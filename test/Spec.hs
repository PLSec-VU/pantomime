module Main
  ( main
  ) where

import Test.Hspec
import Test.HUnit

import System.Directory (listDirectory)
import System.IO.Silently (hSilence)
import System.IO (stdout, stderr)

import GHC
import GHC.Paths (libdir)
import GHC.Plugins (HasDynFlags (..), showGhcExceptionUnsafe)
-- import GHC.Utils.Panic (handleGhcException)
import GHC.Driver.Session (updOptLevel)
import qualified GHC.Data.EnumSet as EnumSet

import Language.Haskell.TH.LanguageExtensions

import Control.Monad (forM_)

import Data.Function ((&))
import Data.List (isSuffixOf)

-- | Plugin setup.
--
-- This ensure the flags and session are set up to test out plugin.
setupPlugin :: Ghc ()
setupPlugin = do
  dflags <- getDynFlags
  setSessionDynFlags $ updOptLevel 1 dflags
    { pluginModNames = mkModuleName "UC" : pluginModNames dflags
    , extensionFlags = extensionFlags dflags 
      & EnumSet.insert TemplateHaskellQuotes
    , generalFlags = generalFlags dflags
      & EnumSet.insert Opt_ExposeAllUnfoldings
      -- & EnumSet.delete Opt_KeepHiFiles
      -- & EnumSet.delete Opt_KeepOFiles
    }

-- | Run the ghc monad.
runGhc' :: Ghc a -> IO a
runGhc' = runGhc $ Just libdir

-- | Compile the given file.
--
-- This will additionally return an error if it occurred during the compilation.
-- FIXME: It seems GHC already catches all thrown errors from the plugin. Can
compile :: FilePath -> Ghc (Either GhcException ())
compile path = do
  -- Compile the given module.
  _ <- compileToCoreModule path

  -- Remove the target after compiling to ensure we don't run it twice.
  target <- guessTarget path Nothing Nothing
  removeTarget $ targetId target

  pure $ Right ()

  -- let handler = pure . Left
  -- operation
  -- handleGhcException handler operation

-- | Fetches the files we consider for tests.
progPaths :: IO [FilePath]
progPaths = do
  let listDirectory' dir = do
        files <- listDirectory dir
        pure $ fmap (dir <>) files
  paths <- listDirectory' "prog/"
  let isSrc = isSuffixOf ".hs"
  pure $ filter isSrc paths

-- -- | Compiles the given files, running them through the plugin.
-- runFiles :: [FilePath] -> IO [Either GhcException ()]
-- runFiles paths = runGhc' $ do
--   setupPlugin
--   forM paths compile

-- -- | Check the result of the compilation.
-- check :: FilePath -> Either GhcException () -> SpecWith ()
-- check path result = do
--   it ("checks " <> "\"" <> path <> "\"") $ do
--     let pprFail = assertFailure . flip showGhcExceptionUnsafe ""
--     either pprFail pure result

check' :: FilePath -> SpecWith ()
check' path = do
  it ("checks " <> "\"" <> path <> "\"") $ do
    -- result <- hSilence [stdout, stderr] . runGhc' $ do
    result <- runGhc' $ do
      setupPlugin
      compile path

    let pprFail = assertFailure . flip showGhcExceptionUnsafe ""
    either pprFail pure result

    -- let pprFail = assertFailure . flip showGhcExceptionUnsafe ""
    -- either pprFail pure result

-- | Performs the plugin in a number of files.
main :: IO ()
main = hspec $ do
  paths <- runIO progPaths
  forM_ paths check'
  -- results <- runIO $ runFiles paths

  -- let results' = zip paths results
  -- forM_ results' $ uncurry check
