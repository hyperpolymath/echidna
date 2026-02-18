-- SPDX-License-Identifier: PLMP-1.0-or-later
-- Trustfile template - cryptographic and provenance verification

module Trustfile where

import Control.Monad (forM)
import System.Directory (doesFileExist)
import System.Environment (lookupEnv)
import System.Exit (exitFailure, exitSuccess)
import System.Process (readProcessWithExitCode)

policyPath :: FilePath
policyPath = "policy/policy.ncl"

policyHashPath :: FilePath
policyHashPath = "policy/policy.ncl.sha256"

schemaPath :: FilePath
schemaPath = "schema/schema.json"

schemaSigPath :: FilePath
schemaSigPath = "schema/schema.sig"

schemaPubPath :: FilePath
schemaPubPath = "schema/schema.pub"

driverPaths :: [FilePath]
driverPaths = ["drivers/gateway-driver.bin"]

migrationsPath :: FilePath
migrationsPath = "migrations/provenance.json"

migrationsSigPath :: FilePath
migrationsSigPath = "migrations/provenance.sig"

migrationsPubPath :: FilePath
migrationsPubPath = "migrations/provenance.pub"

runCmd :: String -> [String] -> IO Bool
runCmd cmd args = do
  (code, _out, _err) <- readProcessWithExitCode cmd args ""
  pure (code == mempty)

readFirstWord :: FilePath -> IO (Maybe String)
readFirstWord path = do
  exists <- doesFileExist path
  if not exists
    then pure Nothing
    else do
      content <- readFile path
      pure (case words content of
        [] -> Nothing
        (w:_) -> Just w)

verifyPolicyHash :: IO Bool
verifyPolicyHash = do
  expected <- readFirstWord policyHashPath
  case expected of
    Nothing -> pure False
    Just hash -> do
      (code, out, _err) <- readProcessWithExitCode "sha256sum" [policyPath] ""
      if code /= mempty
        then pure False
        else do
          let actual = case words out of
                [] -> ""
                (w:_) -> w
          pure (actual == hash)

verifySchemaSignature :: IO Bool
verifySchemaSignature = do
  filesOk <- and <$> mapM doesFileExist [schemaPath, schemaSigPath, schemaPubPath]
  if not filesOk
    then pure False
    else runCmd "openssl" ["dgst", "-sha256", "-verify", schemaPubPath, "-signature", schemaSigPath, schemaPath]

verifyKyber1024Signatures :: IO Bool
verifyKyber1024Signatures = do
  cmd <- lookupEnv "KYBER_VERIFY_CMD"
  let kyberCmd = maybe "kyber-verify" id cmd
  results <- forM driverPaths $ \path -> do
    let sig = path <> ".sig"
    let pub = path <> ".pub"
    filesOk <- and <$> mapM doesFileExist [path, sig, pub]
    if not filesOk
      then pure False
      else runCmd kyberCmd ["--pub", pub, "--sig", sig, "--file", path]
  pure (and results)

verifyMigrationProvenance :: IO Bool
verifyMigrationProvenance = do
  filesOk <- and <$> mapM doesFileExist [migrationsPath, migrationsSigPath, migrationsPubPath]
  if not filesOk
    then pure False
    else runCmd "openssl" ["dgst", "-sha256", "-verify", migrationsPubPath, "-signature", migrationsSigPath, migrationsPath]

main :: IO ()
main = do
  policyOk <- verifyPolicyHash
  schemaOk <- verifySchemaSignature
  driversOk <- verifyKyber1024Signatures
  migrationsOk <- verifyMigrationProvenance
  if and [policyOk, schemaOk, driversOk, migrationsOk]
    then exitSuccess
    else exitFailure
