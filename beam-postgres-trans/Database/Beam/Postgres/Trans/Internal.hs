{-# OPTIONS_GHC -fno-warn-orphans -fno-warn-partial-type-signatures #-}

{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE UndecidableInstances #-}

module Database.Beam.Postgres.Trans.Internal
  ( PgT(..), PgCtx(..)

  , liftIOWithHandle

  , runBeamPostgres, runBeamPostgresDebug

  , pgRenderSyntax, runPgRowReader, getFields

  , withPgDebug

  , postgresUriSyntax

  , fromPg
  ) where

import           Control.Exception (SomeException(..), throwIO, try)
import           Control.Monad.Base (MonadBase(..))
import           Control.Monad.Free.Church
import           Control.Monad.IO.Class

import           Database.Beam hiding (runDelete, runUpdate, runInsert, insert)
import           Database.Beam.Backend.SQL.BeamExtensions
import           Database.Beam.Backend.SQL.Row ( FromBackendRowF(..), FromBackendRowM(..)
                                               , BeamRowReadError(..), ColumnParseError(..) )
import           Database.Beam.Backend.URI
import           Database.Beam.Schema.Tables

import           Database.Beam.Postgres.Syntax
import           Database.Beam.Postgres.Full
import           Database.Beam.Postgres (Postgres, Pg)
import qualified Database.Beam.Postgres as BeamPg

import qualified Database.PostgreSQL.LibPQ as Pg hiding
  (Connection, escapeStringConn, escapeIdentifier, escapeByteaConn, exec)
import qualified Database.PostgreSQL.Simple as Pg
import qualified Database.PostgreSQL.Simple.FromField as Pg
import qualified Database.PostgreSQL.Simple.Internal as Pg
  ( Field(..)
  , escapeStringConn, escapeIdentifier, escapeByteaConn
  , exec, throwResultError )
import qualified Database.PostgreSQL.Simple.Internal as PgI
import qualified Database.PostgreSQL.Simple.Ok as Pg
import qualified Database.PostgreSQL.Simple.Types as Pg (Query(..))

import           Control.Monad.Except
import           Control.Monad.Reader
import qualified Control.Monad.Fail as Fail

import           Data.ByteString (ByteString)
import           Data.ByteString.Builder (toLazyByteString, byteString)
import qualified Data.ByteString.Lazy as BL
import           Data.IORef
import           Data.Maybe (listToMaybe, fromMaybe)
import           Data.String
import qualified Data.Text as Text
import           Data.Text.Encoding (encodeUtf8)
import           Data.Typeable (cast)
#if !MIN_VERSION_base(4, 11, 0)
import           Data.Semigroup
#endif

import           Foreign.C.Types

import           Network.URI (uriToString)

-- | 'BeamURIOpeners' for the standard @postgresql:@ URI scheme. See the
-- postgres documentation for more details on the formatting. See documentation
-- for 'BeamURIOpeners' for more information on how to use this with beam
postgresUriSyntax :: c Postgres Pg.Connection (PgT IO)
                  -> BeamURIOpeners c
postgresUriSyntax =
    mkUriOpener runBeamPostgres "postgresql:"
        (\uri -> do
            let pgConnStr = fromString (uriToString id uri "")
            hdl <- Pg.connectPostgreSQL pgConnStr
            pure (hdl, Pg.close hdl))

-- * Syntax rendering

pgRenderSyntax ::
  Pg.Connection -> PgSyntax -> IO ByteString
pgRenderSyntax conn (PgSyntax mkQuery) =
  renderBuilder <$> runF mkQuery finish step mempty
  where
    renderBuilder = BL.toStrict . toLazyByteString

    step (EmitBuilder b next) a = next (a <> b)
    step (EmitByteString b next) a = next (a <> byteString b)
    step (EscapeString b next) a = do
      res <- wrapError "EscapeString" (Pg.escapeStringConn conn b)
      next (a <> byteString res)
    step (EscapeBytea b next) a = do
      res <- wrapError "EscapeBytea" (Pg.escapeByteaConn conn b)
      next (a <> byteString res)
    step (EscapeIdentifier b next) a = do
      res <- wrapError "EscapeIdentifier" (Pg.escapeIdentifier conn b)
      next (a <> byteString res)

    finish _ = pure

    wrapError step' go = do
      res <- go
      case res of
        Right res' -> pure res'
        Left res' -> fail (step' <> ": " <> show res')

-- * Run row readers

getFields :: Pg.Result -> IO [Pg.Field]
getFields res = do
  Pg.Col colCount <- Pg.nfields res

  let getField col =
        Pg.Field res (Pg.Col col) <$> Pg.ftype res (Pg.Col col)

  mapM getField [0..colCount - 1]

runPgRowReader ::
  Pg.Connection -> Pg.Row -> Pg.Result -> [Pg.Field] -> FromBackendRowM Postgres a -> IO (Either BeamRowReadError a)
runPgRowReader conn rowIdx res fields (FromBackendRowM readRow) =
  Pg.nfields res >>= \(Pg.Col colCount) ->
  runF readRow finish step 0 colCount fields
  where

    step :: forall x. FromBackendRowF Postgres (CInt -> CInt -> [PgI.Field] -> IO (Either BeamRowReadError x))
         -> CInt -> CInt -> [PgI.Field] -> IO (Either BeamRowReadError x)
    step (ParseOneField _) curCol colCount [] = pure (Left (BeamRowReadError (Just (fromIntegral curCol)) (ColumnNotEnoughColumns (fromIntegral colCount))))
    step (ParseOneField _) curCol colCount _
      | curCol >= colCount = pure (Left (BeamRowReadError (Just (fromIntegral curCol)) (ColumnNotEnoughColumns (fromIntegral colCount))))
    step (ParseOneField (next' :: next -> _)) curCol colCount (field:remainingFields) =
      do fieldValue <- Pg.getvalue' res rowIdx (Pg.Col curCol)
         res' <- Pg.runConversion (Pg.fromField field fieldValue) conn
         case res' of
           Pg.Errors errs ->
             let err = fromMaybe (ColumnErrorInternal "Column parse failed with unknown exception") $
                       listToMaybe $
                       do SomeException e <- errs
                          Just pgErr <- pure (cast e)
                          case pgErr of
                            Pg.ConversionFailed { Pg.errSQLType = sql
                                                , Pg.errHaskellType = hs
                                                , Pg.errMessage = msg } ->
                              pure (ColumnTypeMismatch hs sql msg)
                            Pg.Incompatible { Pg.errSQLType = sql
                                            , Pg.errHaskellType = hs
                                            , Pg.errMessage = msg } ->
                              pure (ColumnTypeMismatch hs sql msg)
                            Pg.UnexpectedNull {} ->
                              pure ColumnUnexpectedNull
             in pure (Left (BeamRowReadError (Just (fromIntegral curCol)) err))
           Pg.Ok x -> next' x (curCol + 1) colCount remainingFields

    step (Alt (FromBackendRowM a) (FromBackendRowM b) next) curCol colCount cols =
      do aRes <- runF a (\x curCol' colCount' cols' -> pure (Right (next x curCol' colCount' cols'))) step curCol colCount cols
         case aRes of
           Right next' -> next'
           Left aErr -> do
             bRes <- runF b (\x curCol' colCount' cols' -> pure (Right (next x curCol' colCount' cols'))) step curCol colCount cols
             case bRes of
               Right next' -> next'
               Left {} -> pure (Left aErr)

    step (FailParseWith err) _ _ _ =
      pure (Left err)

    finish x _ _ _ = pure (Right x)

withPgDebug :: (ByteString -> IO ()) -> Pg.Connection -> PgT m a -> m (Either BeamRowReadError a)
withPgDebug dbg conn (PgT action) = runReaderT (runExceptT action) (PgCtx conn dbg)

-- * Beam Monad class


data PgCtx = PgCtx { pgCtxConn :: Pg.Connection, pgCtxDebug :: ByteString -> IO () }

-- | 'MonadBeam' in which we can run Postgres commands. See the documentation
-- for 'MonadBeam' on examples of how to use.
--
-- @beam-postgres@ also provides functions that let you run queries without
-- 'MonadBeam'. These functions may be more efficient and offer a conduit
-- API. See "Database.Beam.Postgres.Conduit" for more information.
newtype PgT m a = PgT { runPgT :: ExceptT BeamRowReadError (ReaderT PgCtx m) a }
    deriving (Monad, Applicative, Functor)

instance MonadTrans PgT where
  lift = PgT . lift . lift

instance Fail.MonadFail m => Fail.MonadFail (PgT m) where
    fail e = lift (Fail.fail $ "Internal Error with: " <> show e)

instance MonadIO m => MonadIO (PgT m) where
    liftIO = PgT . liftIO

instance MonadBase base m => MonadBase base (PgT m) where
    liftBase = PgT . liftBase

liftIOWithHandle :: MonadIO m => (Pg.Connection -> IO a) -> PgT m a
liftIOWithHandle f = PgT $ do
  conn <- asks pgCtxConn
  liftIO $ f conn

runBeamPostgresDebug :: MonadIO m => (ByteString -> IO ()) -> Pg.Connection -> PgT m a -> m a
runBeamPostgresDebug dbg conn action =
    withPgDebug dbg conn action >>= either (liftIO . throwIO) pure

runBeamPostgres :: MonadIO m => Pg.Connection -> PgT m a -> m a
runBeamPostgres = runBeamPostgresDebug (\_ -> pure ())

instance MonadIO m => MonadBeam Postgres (PgT m) where
  runReturningMany cmd consume =
    PgT $ do
      conn <- asks pgCtxConn
      dbg <- asks pgCtxDebug

      query <- liftIO $ pgRenderSyntax conn (fromPgCommand cmd)
      liftIO $ dbg query

      case pgCommandType cmd of
        PgCommandTypeQuery ->
          go conn query
        PgCommandTypeDataUpdateReturning ->
          go conn query
        _ -> do
          _ <- liftIO $ Pg.execute_ conn (Pg.Query query)
          runPgT $ consume (pure Nothing)
    where
      go conn query = do
        result <- liftIO $ Pg.exec conn query
        status <- liftIO $ Pg.resultStatus result
        case status of
          Pg.TuplesOk -> do
            fields <- liftIO $ getFields result
            Pg.Row rowCount <- liftIO $ Pg.ntuples result

            rowIdxRef <- liftIO $ newIORef 0
            a <- runPgT . consume . PgT $ do
              rowIdx <- liftIO $ readIORef rowIdxRef
              if rowIdx >= rowCount
                then pure Nothing
                else do
                  rowResult <- liftIO $ runPgRowReader conn (Pg.Row rowIdx) result fields fromBackendRow
                  case rowResult of
                    Left err -> do
                      throwError err
                    Right r -> do
                      liftIO $ writeIORef rowIdxRef (rowIdx + 1)
                      pure $ Just r

            pure a
          _ ->
            liftIO $ Pg.throwResultError "runReturningMany" result status

  runReturningOne cmd = PgT $ do
    conn <- asks pgCtxConn
    dbg <- asks pgCtxDebug

    query <- liftIO $ pgRenderSyntax conn (fromPgCommand cmd)
    liftIO $ dbg query

    case pgCommandType cmd of
      PgCommandTypeQuery ->
        go conn query
      PgCommandTypeDataUpdateReturning ->
        go conn query
      _ -> do
        _ <- liftIO $ Pg.execute_ conn (Pg.Query query)
        pure Nothing
    where
      go conn query = do
        result <- liftIO $ Pg.exec conn query
        status <- liftIO $ Pg.resultStatus result
        case status of
          Pg.TuplesOk -> do
            fields <- liftIO $ getFields result
            Pg.Row rowCount <- liftIO $ Pg.ntuples result

            a <-
              if rowCount == 0
              then pure Nothing
              else if rowCount == 1
              then do
                rowResult <- liftIO $ runPgRowReader conn (Pg.Row 0) result fields fromBackendRow
                either throwError (pure . Just) rowResult
              else do
                error $ "runReturningOne: expected 0-1 rows, got " <> show rowCount

            pure a
          _ ->
            liftIO $ Pg.throwResultError "runReturningOne" result status

  runReturningFirst cmd = runReturningMany cmd id

  runReturningList cmd = runReturningMany cmd (loop id)
    where
      loop acc next = do
        mRow <- next
        case mRow of
          Nothing -> pure (acc [])
          Just row -> loop (acc . (:) row) next

instance MonadIO m => MonadBeamInsertReturning Postgres (PgT m) where
    runInsertReturningList i = do
        let insertReturningCmd' = i `returning`
              changeBeamRep (\(Columnar' (QExpr s) :: Columnar' (QExpr Postgres PostgresInaccessible) ty) ->
                Columnar' (QExpr s) :: Columnar' (QExpr Postgres ()) ty)

        -- Make savepoint
        case insertReturningCmd' of
          PgInsertReturningEmpty ->
            pure []
          PgInsertReturning insertReturningCmd ->
            runReturningList (PgCommandSyntax PgCommandTypeDataUpdateReturning insertReturningCmd)

instance MonadIO m => MonadBeamUpdateReturning Postgres (PgT m) where
    runUpdateReturningList u = do
        let updateReturningCmd' = u `returning`
              changeBeamRep (\(Columnar' (QExpr s) :: Columnar' (QExpr Postgres PostgresInaccessible) ty) ->
                Columnar' (QExpr s) :: Columnar' (QExpr Postgres ()) ty)

        case updateReturningCmd' of
          PgUpdateReturningEmpty ->
            pure []
          PgUpdateReturning updateReturningCmd ->
            runReturningList (PgCommandSyntax PgCommandTypeDataUpdateReturning updateReturningCmd)

instance MonadIO m => MonadBeamDeleteReturning Postgres (PgT m) where
    runDeleteReturningList d = do
        let PgDeleteReturning deleteReturningCmd = d `returning`
              changeBeamRep (\(Columnar' (QExpr s) :: Columnar' (QExpr Postgres PostgresInaccessible) ty) ->
                Columnar' (QExpr s) :: Columnar' (QExpr Postgres ()) ty)

        runReturningList (PgCommandSyntax PgCommandTypeDataUpdateReturning deleteReturningCmd)
-- | Lift @beam-postgres@'s 'Pg' into 'PgT'.
fromPg :: MonadIO m => Pg a -> PgT m a
fromPg ma =
  PgT $ do
    PgCtx conn dbg <- ask
    result <- liftIO . try $ BeamPg.runBeamPostgresDebug (dbg . encodeUtf8 . Text.pack) conn ma
    either throwError pure result
