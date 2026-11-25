module Main (main) where

import Control.Exception (bracket, evaluate)
import Control.Monad (unless, when)
import Data.Char (isPrint, isSpace)
import Data.List (isInfixOf, isPrefixOf, isSuffixOf, nub)
import Dependent.Plugin.ProofSearch (
    SearchConfig (..),
    defaultSearchConfig,
    parseSearchOptions,
 )
import System.Directory (
    createDirectoryIfMissing,
    doesDirectoryExist,
    doesFileExist,
    getTemporaryDirectory,
    listDirectory,
    removeDirectoryRecursive,
 )
import System.Environment (getEnvironment, getExecutablePath, lookupEnv)
import System.Exit (ExitCode (..), exitFailure)
import System.FilePath (takeDirectory, (</>))
import System.IO (IOMode (ReadMode), hGetContents, hPutStrLn, stderr, withBinaryFile)
import System.Process (CreateProcess (env), proc, readCreateProcessWithExitCode, readProcessWithExitCode)

-- | Resolved compiler executable and extra package databases for subprocess checks.
data TestCompiler = TestCompiler
    { tcGhc :: !FilePath
    , tcPkgDbFlags :: ![String]
    }
    deriving (Show)

{- | Locate the Stage 1/2 GHC under test and the local Cabal package databases
registering @dependent-proof-search@.
-}
discoverTestCompiler :: IO TestCompiler
discoverTestCompiler = do
    exePath <- getExecutablePath
    mbBuildRoot <- findBuildRoot (takeDirectory exePath)
    mbEnvGhc <- lookupEnv "GHC_UNDER_TEST"
    ghcBin <-
        case mbEnvGhc of
            Just g | not (null g) -> pure g
            _ -> do
                mbMapsGhc <- findGhcFromProcMaps
                case (mbMapsGhc, mbBuildRoot) of
                    (Just g, _) -> pure g
                    (Nothing, Just root) -> maybe "ghc" id <$> findGhcInCache root
                    (Nothing, Nothing) -> pure "ghc"

    pkgDbFlags <-
        case mbBuildRoot of
            Just root -> findPackageDbs exePath root
            Nothing -> pure ["-plugin-package", "dependent-proof-search"]
    pure TestCompiler{tcGhc = ghcBin, tcPkgDbFlags = pkgDbFlags}

-- | Discover the host @ghc@ binary on Linux from the linked @libHSbase@/@libHSrts@ path.
findGhcFromProcMaps :: IO (Maybe FilePath)
findGhcFromProcMaps = do
    hasMaps <- doesFileExist "/proc/self/maps"
    if not hasMaps
        then pure Nothing
        else do
            txt <- readFile "/proc/self/maps"
            let soPaths =
                    [ tok
                    | ln <- lines txt
                    , tok <- words ln
                    , "/libHS" `isInfixOf` tok
                    ]
            candidates <- fmap concat (mapM ancestorGhcBins (nub soPaths))
            pure $
                case candidates of
                    (g : _) -> Just g
                    [] -> Nothing
  where
    ancestorGhcBins :: FilePath -> IO [FilePath]
    ancestorGhcBins = go (6 :: Int) . takeDirectory
      where
        go n dir
            | n <= 0 = pure []
            | otherwise = do
                let cand = dir </> "bin" </> "ghc"
                ok <- doesFileExist cand
                rest <-
                    let parent = takeDirectory dir
                     in if parent == dir then pure [] else go (n - 1) parent
                pure (if ok then cand : rest else rest)

-- | Walk upward from the test executable to find Cabal's @--builddir@ root.
findBuildRoot :: FilePath -> IO (Maybe FilePath)
findBuildRoot dir = do
    hasPlan <- doesFileExist (dir </> "cache" </> "plan.json")
    if hasPlan
        then pure (Just dir)
        else do
            let parent = takeDirectory dir
            if parent == dir
                then pure Nothing
                else findBuildRoot parent

{- | Extract the configured @ghc@ executable path from Cabal's @cache/@ files
when @GHC_UNDER_TEST@ is not explicitly set.
-}
findGhcInCache :: FilePath -> IO (Maybe FilePath)
findGhcInCache root = do
    let cacheFiles =
            [ root </> "cache" </> "compiler"
            , root </> "cache" </> "config"
            , root </> "cache" </> "plan.json"
            ]
    paths <- fmap concat (mapM extractPaths cacheFiles)
    existing <- filterExisting paths
    pure $
        case existing of
            (p : _) -> Just p
            [] -> Nothing
  where
    extractPaths :: FilePath -> IO [FilePath]
    extractPaths fp = do
        exists <- doesFileExist fp
        if not exists
            then pure []
            else withBinaryFile fp ReadMode $ \h -> do
                raw <- hGetContents h
                _ <- evaluate (length raw)
                let tokens = concatMap sliceBinGhc (map (dropWhile (/= '/')) (splitPathTokens raw))
                pure [t | t <- tokens, "/ghc" `isSuffixOf` t, "/" `isPrefixOf` t]

    sliceBinGhc :: String -> [String]
    sliceBinGhc s = go "" s
      where
        go _ "" = []
        go revAcc rest
            | "/bin/ghc" `isPrefixOf` rest =
                [reverse revAcc ++ "/bin/ghc", s]
            | otherwise =
                case rest of
                    (c : cs) -> go (c : revAcc) cs

    isDelim :: Char -> Bool
    isDelim c = not (isPrint c) || isSpace c || c `elem` ("\",'()[]{};=:@" :: String)

    splitPathTokens :: String -> [String]
    splitPathTokens "" = []
    splitPathTokens s =
        let (_, rest0) = span isDelim s
         in case rest0 of
                "" -> []
                _ ->
                    let (tok, rest1) = break isDelim rest0
                     in tok : splitPathTokens rest1

    filterExisting :: [FilePath] -> IO [FilePath]
    filterExisting [] = pure []
    filterExisting (p : ps) = do
        ok <- doesFileExist p
        rest <- filterExisting ps
        pure (if ok then p : rest else rest)

-- | Find Cabal's local package database directories containing @.conf@ files.
findPackageDbs :: FilePath -> FilePath -> IO [String]
findPackageDbs exePath root = do
    allPkgDbs <- findConfDirs 8 root
    let matchingFlavour d
            | "/opt/" `isInfixOf` exePath = not ("/noopt/" `isInfixOf` d)
            | "/noopt/" `isInfixOf` exePath = not ("/opt/" `isInfixOf` d)
            | otherwise = True
        chosenDbs = nub (filter matchingFlavour allPkgDbs)
    unitIds <- fmap concat (mapM findPluginUnitIds chosenDbs)
    let pkgSel =
            case unitIds of
                (uid : _) -> ["-plugin-package-id", uid]
                [] -> ["-plugin-package", "dependent-proof-search"]
    pure (["-package-db=" ++ db | db <- chosenDbs] ++ pkgSel)

-- | Extract the registered @id:@ of @dependent-proof-search@ from a package DB directory.
findPluginUnitIds :: FilePath -> IO [String]
findPluginUnitIds dbDir = do
    entries <- listDirectory dbDir
    let confFiles =
            [ dbDir </> e
            | e <- entries
            , "dependent-proof-search" `isPrefixOf` e
            , ".conf" `isSuffixOf` e
            ]
    fmap concat $
        mapM
            ( \fp -> do
                txt <- readFile fp
                pure
                    [ dropWhile isSpace (drop 3 ln)
                    | ln <- lines txt
                    , "id:" `isPrefixOf` ln
                    ]
            )
            confFiles

-- | Bounded-depth search for GHC package database directories (containing @package.cache@).
findConfDirs :: Int -> FilePath -> IO [FilePath]
findConfDirs depth dir
    | depth < 0 = pure []
    | otherwise = do
        exists <- doesDirectoryExist dir
        if not exists
            then pure []
            else do
                entries <- listDirectory dir
                if "package.cache" `elem` entries
                    then pure [dir]
                    else
                        fmap concat $
                            mapM
                                ( \e -> do
                                    let full = dir </> e
                                    isDir <- doesDirectoryExist full
                                    if isDir
                                        then findConfDirs (depth - 1) full
                                        else pure []
                                )
                                entries

-- | Run GHC on a source module written into a temporary directory.
runGhcModule :: TestCompiler -> FilePath -> String -> [String] -> String -> IO (ExitCode, String)
runGhcModule tc workDir modFile extraFlags src = do
    let srcPath = workDir </> modFile
        outDir = workDir </> ("out-" ++ sanitize modFile ++ "-" ++ sanitize (concat extraFlags))
    createDirectoryIfMissing True outDir
    writeFile srcPath src
    curEnv <- getEnvironment
    let cleanEnv = filter (\(k, _) -> k /= "GHC_ENVIRONMENT" && k /= "GHC_PACKAGE_PATH") curEnv
        args =
            ["-package-env=-"]
                ++ tcPkgDbFlags tc
                ++ [ "-fforce-recomp"
                   , "-fno-diagnostics-show-caret"
                   , "-fprint-potential-instances"
                   , "-outputdir"
                   , outDir
                   ]
                ++ extraFlags
                ++ [srcPath]
    (code, out, err) <- readCreateProcessWithExitCode ((proc (tcGhc tc) args){env = Just cleanEnv}) ""
    pure (code, normalizeOutput (out ++ "\n" ++ err))
  where
    sanitize :: String -> String
    sanitize = map (\c -> if c `elem` ("/:=,.- " :: String) then '_' else c)

{- | Collapse line wraps and runs of whitespace so multi-line GHC diagnostics
match reliably across terminal widths.
-}
normalizeOutput :: String -> String
normalizeOutput = unwords . words

-- | Assert a boolean condition, printing diagnostics and exiting on failure.
assertBool :: String -> Bool -> String -> IO ()
assertBool label cond detail =
    unless cond $ do
        hPutStrLn stderr ("FAIL [" ++ label ++ "]:\n" ++ detail)
        exitFailure

-- | Assert that normalized compiler output contains an expected substring.
assertContains :: String -> String -> String -> IO ()
assertContains label needle haystack =
    assertBool
        label
        (normalizeOutput needle `isInfixOf` haystack)
        ("Expected substring:\n  " ++ needle ++ "\nin output:\n  " ++ haystack)

-- | Assert that normalized compiler output does not contain a forbidden substring.
assertNotContains :: String -> String -> String -> IO ()
assertNotContains label needle haystack =
    assertBool
        label
        (not (normalizeOutput needle `isInfixOf` haystack))
        ("Unexpected substring:\n  " ++ needle ++ "\nin output:\n  " ++ haystack)

-- | Shared arithmetic and GADT prelude used across hole-fit test modules.
commonPrelude :: String
commonPrelude =
    unlines
        [ "import Data.Type.Equality ((:~:) (Refl), sym, trans)"
        , "import GHC.Exts (Matchability)"
        , ""
        , "data Nat = Zero | Succ Nat"
        , "  deriving (Eq, Show)"
        , ""
        , "plus :: Nat -> Nat -> Nat"
        , "plus Zero     n = n"
        , "plus (Succ m) n = Succ (plus m n)"
        , ""
        , "cong :: forall {a} {b} {m :: Matchability}."
        , "        forall (f :: a %m -> b) -> forall (x :: a) (y :: a)."
        , "        x :~: y -> f x :~: f y"
        , "cong _ Refl = Refl"
        , ""
        , "plusZero :: foreach (m :: Nat) -> plus m Zero :~: m"
        , "plusZero Zero     = Refl"
        , "plusZero (Succ m) = cong Succ (plusZero m)"
        , ""
        , "plusSuc :: foreach (m :: Nat) (n :: Nat) -> plus m (Succ n) :~: Succ (plus m n)"
        , "plusSuc Zero     _ = Refl"
        , "plusSuc (Succ m) n = cong Succ (plusSuc m n)"
        , ""
        , "data LE (m :: Nat) (n :: Nat) where"
        , "  ZleN :: LE Zero n"
        , "  SleS :: LE m n -> LE (Succ m) (Succ n)"
        , ""
        , "leRefl :: foreach (n :: Nat) -> LE n n"
        , "leRefl Zero     = ZleN"
        , "leRefl (Succ n) = SleS (leRefl n)"
        ]

-- | Unit tests for 'defaultSearchConfig' and 'parseSearchOptions'.
testOptionParsing :: IO ()
testOptionParsing = do
    assertBool
        "defaultSearchConfig"
        ( defaultSearchConfig
            == SearchConfig
                { scDepth = 2
                , scMaxFits = 8
                , scMaxCandidates = 64
                , scAuto = True
                , scCongruence = True
                , scTransitivity = True
                , scSubgoalsInValid = False
                }
        )
        (show defaultSearchConfig)

    let parsed =
            parseSearchOptions
                [ "depth=9:max-fits=4,max-candidates=32"
                , "no-auto,no-congruence:no-transitivity,subgoals-in-valid"
                ]
    assertBool
        "parseSearchOptions clamping & flags"
        ( parsed
            == SearchConfig
                { scDepth = 5
                , scMaxFits = 4
                , scMaxCandidates = 32
                , scAuto = False
                , scCongruence = False
                , scTransitivity = False
                , scSubgoalsInValid = True
                }
        )
        (show parsed)

    let parsedNeg = parseSearchOptions ["depth=-3:auto:congruence:transitivity:no-subgoals-in-valid"]
    assertBool "parseSearchOptions lower clamp" (scDepth parsedNeg == 0 && scAuto parsedNeg) (show parsedNeg)

{- | Test 1 & 2 & 3: Congruence refinements, transitivity refinements, and
depth-1 / depth-2 complete backward-chaining proof synthesis.
-}
testProofSearchAndRefinements :: TestCompiler -> FilePath -> IO ()
testProofSearchAndRefinements tc workDir = do
    let holeSrc =
            unlines
                [ "{-# LANGUAGE DependentTypes, GADTs, StandaloneKindSignatures #-}"
                , "{-# OPTIONS_GHC -fplugin=Dependent.Plugin.ProofSearch -frefinement-level-hole-fits=1 #-}"
                , "module HoleChecks where"
                , commonPrelude
                , "-- 1. Congruence subgoal refinement & depth-2 complete proof with source binder 'n'"
                , "plusAssoc :: foreach (m :: Nat) (n :: Nat) (p :: Nat) -> plus (plus m n) p :~: plus m (plus n p)"
                , "plusAssoc Zero     _ _ = Refl"
                , "plusAssoc (Succ m) n p = _"
                , ""
                , "-- Partial-application congruence: cong (plus m) (_ :: a :~: b) and cong (plus m) eq"
                , "congPartial :: foreach (m :: Nat) (a :: Nat) (b :: Nat) -> a :~: b -> plus m a :~: plus m b"
                , "congPartial m a b eq = _"
                , ""
                , "-- 2 & 3. Commutativity holes: Refl, plusZero m, sym (plusZero m), and trans + cong"
                , "commZZ :: plus Zero Zero :~: plus Zero Zero"
                , "commZZ = _"
                , ""
                , "commRightZero :: foreach (m :: Nat) -> plus m Zero :~: plus Zero m"
                , "commRightZero m = _"
                , ""
                , "commLeftZero :: foreach (m :: Nat) -> plus Zero m :~: plus m Zero"
                , "commLeftZero m = _"
                , ""
                , "plusComm :: foreach (m :: Nat) (k :: Nat) -> plus m k :~: plus k m"
                , "plusComm m Zero     = plusZero m"
                , "plusComm m (Succ k) = _"
                , ""
                , "-- Right-rewrite transitivity refinement: trans (_ :: ...) (symSuc k m)"
                , "symSuc :: foreach (m :: Nat) (n :: Nat) -> Succ (plus m n) :~: plus m (Succ n)"
                , "symSuc m n = sym (plusSuc m n)"
                , ""
                , "rightTransGoal :: foreach (m :: Nat) (k :: Nat) -> Succ (Succ (plus k m)) :~: plus k (Succ m)"
                , "rightTransGoal m k = _"
                , ""
                , "-- Indexed GADT proof synthesis: SleS (leRefl n)"
                , "leMonoSucc :: foreach (n :: Nat) -> LE (Succ n) (Succ n)"
                , "leMonoSucc n = _"
                , ""
                , "-- Local foreach hypothesis applied to constructor Z: eq Z"
                , "data PNat = Z | S PNat"
                , "data Witness (n :: PNat) where"
                , "  WZ :: Witness Z"
                , ""
                , "useHyp :: (foreach (n :: PNat) -> Witness n) -> foreach (m :: PNat) -> Witness m"
                , "useHyp eq Z     = _"
                , "useHyp eq (S k) = eq (S k)"
                ]

    (code, out) <- runGhcModule tc workDir "HoleChecks.hs" ["-fno-code"] holeSrc
    assertBool "HoleChecks exits with hole errors" (code /= ExitSuccess) out

    -- 1. Congruence subgoal refinements (exact source binder names m, n, p)
    assertContains
        "congruence refinement Succ"
        "cong Succ (_ :: plus (plus m n) p :~: plus m (plus n p))"
        out
    assertContains
        "congruence refinement partial plus"
        "cong (plus m) (_ :: a :~: b)"
        out

    -- 2. Transitivity subgoal refinements (left-rewrite and right-rewrite, exact m, k)
    assertContains
        "transitivity left-rewrite refinement"
        "trans (plusSuc m k) (_ :: Succ (plus m k) :~: Succ (plus k m))"
        out
    assertContains
        "transitivity right-rewrite refinement"
        "trans (_ :: Succ (Succ (plus k m)) :~: Succ (plus k m)) (symSuc k m)"
        out

    -- 3. Complete depth-0, depth-1, and depth-2 proofs
    assertContains "complete Refl" "Refl" out
    assertContains "complete plusZero m" "plusZero m" out
    assertContains "complete sym (plusZero m)" "sym (plusZero m)" out
    assertContains "complete cong Succ (plusAssoc m n p)" "cong Succ (plusAssoc m n p)" out
    assertNotContains "no renamed n1 in plusAssoc fit" "plusAssoc m n1 p" out
    assertContains "complete cong (plus m) eq" "cong (plus m) eq" out
    assertContains
        "complete trans + cong"
        "trans (plusSuc m k) (cong Succ (plusComm m k))"
        out
    assertContains "complete GADT SleS (leRefl n)" "SleS (leRefl n)" out
    assertContains "complete local hypothesis eq Z" "eq Z" out

    -- Also test custom user equality GADT (zero Data.Type.Equality imports!)
    let customEqSrc =
            unlines
                [ "{-# LANGUAGE DependentTypes, GADTs #-}"
                , "{-# OPTIONS_GHC -fplugin=Dependent.Plugin.ProofSearch -frefinement-level-hole-fits=1 #-}"
                , "module CustomEqHole where"
                , "import GHC.Exts (Matchability)"
                , ""
                , "data Val = VZ | VS Val"
                , ""
                , "addV :: Val -> Val -> Val"
                , "addV VZ     y = y"
                , "addV (VS x) y = VS (addV x y)"
                , ""
                , "data EqP (x :: a) (y :: a) where"
                , "  EqPRefl :: EqP x x"
                , ""
                , "symEqP :: EqP x y -> EqP y x"
                , "symEqP EqPRefl = EqPRefl"
                , ""
                , "transEqP :: EqP x y -> EqP y z -> EqP x z"
                , "transEqP EqPRefl EqPRefl = EqPRefl"
                , ""
                , "congEqP :: forall {a} {b} {m :: Matchability}."
                , "           forall (f :: a %m -> b) -> forall (x :: a) (y :: a)."
                , "           EqP x y -> EqP (f x) (f y)"
                , "congEqP _ EqPRefl = EqPRefl"
                , ""
                , "addVZero :: foreach (x :: Val) -> EqP (addV x VZ) x"
                , "addVZero VZ     = EqPRefl"
                , "addVZero (VS x) = congEqP VS (addVZero x)"
                , ""
                , "addVAssoc :: foreach (x :: Val) (y :: Val) (z :: Val) -> EqP (addV (addV x y) z) (addV x (addV y z))"
                , "addVAssoc VZ     _ _ = EqPRefl"
                , "addVAssoc (VS x) y z = _"
                , ""
                , "symCustomGoal :: foreach (x :: Val) -> EqP x (addV x VZ)"
                , "symCustomGoal x = _"
                ]
    (cCode, cOut) <- runGhcModule tc workDir "CustomEqHole.hs" ["-fno-code"] customEqSrc
    assertBool "CustomEqHole exits with hole errors" (cCode /= ExitSuccess) cOut
    assertContains
        "custom EqP congruence refinement"
        "congEqP VS (_ :: EqP (addV (addV x y) z) (addV x (addV y z)))"
        cOut
    assertContains
        "custom EqP complete congEqP"
        "congEqP VS (addVAssoc x y z)"
        cOut
    assertContains
        "custom EqP complete symEqP"
        "symEqP (addVZero x)"
        cOut

{- | Test 4: Paste-back soundness check at both @-O0@ and @-O2@ with
@-dcore-lint -dstg-lint -Wall -Werror@, plus runtime execution.
-}
testPasteBackSoundness :: TestCompiler -> FilePath -> IO ()
testPasteBackSoundness tc workDir = do
    let pastedSrc =
            unlines
                [ "{-# LANGUAGE DependentTypes, GADTs, ListTuplePuns #-}"
                , "{-# OPTIONS_GHC -fplugin=Dependent.Plugin.ProofSearch #-}"
                , "module Main (main) where"
                , commonPrelude
                , "plusAssoc :: foreach (m :: Nat) (n :: Nat) (p :: Nat) -> plus (plus m n) p :~: plus m (plus n p)"
                , "plusAssoc Zero     _ _ = Refl"
                , "plusAssoc (Succ m) n p = cong Succ (plusAssoc m n p)"
                , ""
                , "congPartial :: foreach (m :: Nat) (a :: Nat) (b :: Nat) -> a :~: b -> plus m a :~: plus m b"
                , "congPartial m _ _ eq = cong (plus m) eq"
                , ""
                , "commZZ :: plus Zero Zero :~: plus Zero Zero"
                , "commZZ = Refl"
                , ""
                , "commRightZero :: foreach (m :: Nat) -> plus m Zero :~: plus Zero m"
                , "commRightZero m = plusZero m"
                , ""
                , "commLeftZero :: foreach (m :: Nat) -> plus Zero m :~: plus m Zero"
                , "commLeftZero m = sym (plusZero m)"
                , ""
                , "plusComm :: foreach (m :: Nat) (k :: Nat) -> plus m k :~: plus k m"
                , "plusComm m Zero     = plusZero m"
                , "plusComm m (Succ k) = trans (plusSuc m k) (cong Succ (plusComm m k))"
                , ""
                , "leMonoSucc :: foreach (n :: Nat) -> LE (Succ n) (Succ n)"
                , "leMonoSucc n = SleS (leRefl n)"
                , ""
                , "data PNat = Z | S PNat"
                , "data Witness (n :: PNat) where"
                , "  WZ :: Witness Z"
                , "  WS :: Witness n -> Witness (S n)"
                , ""
                , "mkWit :: foreach (n :: PNat) -> Witness n"
                , "mkWit Z     = WZ"
                , "mkWit (S k) = WS (mkWit k)"
                , ""
                , "useHyp :: (foreach (n :: PNat) -> Witness n) -> foreach (m :: PNat) -> Witness m"
                , "useHyp eq Z     = eq Z"
                , "useHyp eq (S k) = eq (S k)"
                , ""
                , "main :: IO ()"
                , "main = do"
                , "  let two = Succ (Succ Zero)"
                , "      one = Succ Zero"
                , "  case (plusAssoc two one two, congPartial two one one Refl, commZZ, commRightZero two, commLeftZero two, plusComm two one) of"
                , "    (Refl, Refl, Refl, Refl, Refl, Refl) -> pure ()"
                , "  case (leMonoSucc two, useHyp mkWit Z, useHyp mkWit (S Z)) of"
                , "    (SleS _, WZ, WS WZ) -> putStrLn \"paste-back: OK\""
                ]

    mapM_
        ( \optFlag -> do
            let binPath = workDir </> ("pasted-" ++ drop 1 optFlag)
            (code, out) <-
                runGhcModule
                    tc
                    workDir
                    "PasteBackMain.hs"
                    [optFlag, "-dcore-lint", "-dstg-lint", "-Wall", "-Werror", "-o", binPath]
                    pastedSrc
            assertBool ("PasteBackMain compiles cleanly at " ++ optFlag) (code == ExitSuccess) out
            (runCode, runOut, runErr) <- readProcessWithExitCode binPath [] ""
            assertBool
                ("PasteBackMain runs cleanly at " ++ optFlag)
                (runCode == ExitSuccess && "paste-back: OK" `isInfixOf` runOut)
                (runOut ++ "\n" ++ runErr)
        )
        ["-O0", "-O2"]

{- | Test 5: Plugin options (@:depth=1@, @:no-congruence@, @:no-transitivity@,
@:no-auto@, @:subgoals-in-valid@).
-}
testPluginOptions :: TestCompiler -> FilePath -> IO ()
testPluginOptions tc workDir = do
    let optSrc =
            unlines
                [ "{-# LANGUAGE DependentTypes, GADTs #-}"
                , "module OptionChecks where"
                , commonPrelude
                , "plusAssoc :: foreach (m :: Nat) (n :: Nat) (p :: Nat) -> plus (plus m n) p :~: plus m (plus n p)"
                , "plusAssoc Zero     _ _ = Refl"
                , "plusAssoc (Succ m) n p = _"
                , ""
                , "usePlusZero :: foreach (m :: Nat) -> plus m Zero :~: m"
                , "usePlusZero m = _"
                , ""
                , "plusCommStep :: foreach (m :: Nat) (k :: Nat) -> plus m (Succ k) :~: Succ (plus k m)"
                , "plusCommStep m k = _"
                ]

    -- A. :depth=1 suppresses depth-2 cong Succ (plusAssoc m n p) while keeping depth-1 plusZero m
    (_, outDepth1) <-
        runGhcModule
            tc
            workDir
            "OptDepth1.hs"
            [ "-fno-code"
            , "-fplugin=Dependent.Plugin.ProofSearch"
            , "-fplugin-opt=Dependent.Plugin.ProofSearch:depth=1"
            ]
            optSrc
    assertContains "depth=1 keeps plusZero m" "plusZero m" outDepth1
    assertNotContains "depth=1 suppresses cong Succ (plusAssoc m n p)" "cong Succ (plusAssoc m n p)" outDepth1

    -- B. :no-congruence suppresses cong Succ refinement & auto fits
    (_, outNoCong) <-
        runGhcModule
            tc
            workDir
            "OptNoCong.hs"
            [ "-fno-code"
            , "-frefinement-level-hole-fits=1"
            , "-fplugin=Dependent.Plugin.ProofSearch"
            , "-fplugin-opt=Dependent.Plugin.ProofSearch:no-congruence"
            ]
            optSrc
    assertNotContains "no-congruence suppresses cong Succ refinement" "cong Succ (_ ::" outNoCong
    assertNotContains "no-congruence suppresses cong Succ auto" "cong Succ (plusAssoc m n p)" outNoCong
    assertContains "no-congruence keeps trans refinement" "trans (plusSuc m k) (_ ::" outNoCong

    -- C. :no-transitivity suppresses trans refinement & auto fits while keeping cong
    (_, outNoTrans) <-
        runGhcModule
            tc
            workDir
            "OptNoTrans.hs"
            [ "-fno-code"
            , "-frefinement-level-hole-fits=1"
            , "-fplugin=Dependent.Plugin.ProofSearch"
            , "-fplugin-opt=Dependent.Plugin.ProofSearch:no-transitivity"
            ]
            optSrc
    assertNotContains "no-transitivity suppresses trans refinement" "trans (plusSuc m k)" outNoTrans
    assertContains "no-transitivity keeps cong Succ auto" "cong Succ (plusAssoc m n p)" outNoTrans

    -- D. :no-auto suppresses complete synthesis while keeping refinement fits
    (_, outNoAuto) <-
        runGhcModule
            tc
            workDir
            "OptNoAuto.hs"
            [ "-fno-code"
            , "-frefinement-level-hole-fits=1"
            , "-fplugin=Dependent.Plugin.ProofSearch"
            , "-fplugin-opt=Dependent.Plugin.ProofSearch:no-auto"
            ]
            optSrc
    assertNotContains "no-auto suppresses cong Succ (plusAssoc m n p)" "cong Succ (plusAssoc m n p)" outNoAuto
    assertContains
        "no-auto keeps cong Succ refinement"
        "cong Succ (_ :: plus (plus m n) p :~: plus m (plus n p))"
        outNoAuto

    -- E. :subgoals-in-valid emits subgoal refinements even without -frefinement-level-hole-fits
    (_, outSubInValid) <-
        runGhcModule
            tc
            workDir
            "OptSubInValid.hs"
            [ "-fno-code"
            , "-fplugin=Dependent.Plugin.ProofSearch"
            , "-fplugin-opt=Dependent.Plugin.ProofSearch:no-auto:subgoals-in-valid"
            ]
            optSrc
    assertContains
        "subgoals-in-valid emits cong Succ refinement"
        "cong Succ (_ :: plus (plus m n) p :~: plus m (plus n p))"
        outSubInValid

main :: IO ()
main = do
    testOptionParsing
    tc <- discoverTestCompiler
    when (null (tcGhc tc)) $ do
        hPutStrLn stderr "Could not locate GHC executable"
        exitFailure
    tmpBase <- getTemporaryDirectory
    let workRoot = tmpBase </> "dependent-proof-search-tests"
    bracket
        (createDirectoryIfMissing True workRoot >> pure workRoot)
        (\d -> removeDirectoryRecursive d)
        $ \workDir -> do
            testProofSearchAndRefinements tc workDir
            testPasteBackSoundness tc workDir
            testPluginOptions tc workDir
            putStrLn "dependent-proof-search-test: OK"
