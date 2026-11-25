{-# LANGUAGE MultiWayIf #-}

{- |
Module      : Dependent.Plugin.ProofSearch
Description : Bounded proof-search hole-fit plugin for Dependent Haskell
License     : BSD-3-Clause
Maintainer  : mpg@mpg.is

GHC hole-fit plugin that performs bounded backward-chaining proof synthesis
and congruence/transitivity subgoal refinement for Dependent Haskell
(@-XDependentTypes@).

See @Note [Bounded backward-chaining proof search in HoleFitPlugin]@.
-}
module Dependent.Plugin.ProofSearch (
    plugin,
    SearchConfig (..),
    defaultSearchConfig,
    parseSearchOptions,
) where

import Control.Monad (foldM, guard)
import Data.Char (isDigit, isSpace, toLower)
import Data.Function (on)
import Data.List (isPrefixOf, nubBy, sortOn, stripPrefix)
import Data.Maybe (catMaybes, isJust, isNothing, mapMaybe)
import Data.Set qualified as Set
import Text.Read (readMaybe)

import GHC.Builtin.Modules (gHC_INTERNAL_ERR, gHC_INTERNAL_UNSAFE_COERCE)
import GHC.Builtin.WiredIn.Types (
    liftedTypeKind,
    manyDataConTy,
    mkListTy,
    unitTy,
    unmatchableDataConTy,
 )
import GHC.Core.Coercion (Role (Nominal), abstractNativeIndices, coercionRole)
import GHC.Core.ConLike (ConLike (PatSynCon, RealDataCon))
import GHC.Core.DataCon (
    DataCon,
    dataConFullSig,
    dataConName,
    dataConOrigArgTys,
    dataConSourceArity,
    dataConWrapperType,
 )
import GHC.Core.PatSyn (patSynName)
import GHC.Core.Predicate (getEqPredTys_maybe)
import GHC.Core.Reduction (Reduction (..))
import GHC.Core.TyCo.Compare (eqType)
import GHC.Core.TyCo.FVs (tyCoVarsOfType, tyCoVarsOfTypeList, tyCoVarsOfTypes)
import GHC.Core.TyCo.Rep (Type (..))
import GHC.Core.TyCo.Subst qualified as Subst
import GHC.Core.TyCo.Tidy (tidyOpenType)
import GHC.Core.TyCon (
    TyCon,
    isAlgTyCon,
    isPromotedDataCon_maybe,
    isTypeFamilyTyCon,
    tyConArity,
    tyConDataCons,
    tyConName,
 )
import GHC.Core.Type (
    PredType,
    coreFullView,
    coreView,
    filterOutInvisibleTypes,
    funTyFlagTyCon,
    isFamFreeTy,
    isTauTy,
    mkForAllTy,
    mkTyConApp,
    mkTyVarTy,
    mkVisFunTyManyU,
    splitTyConApp_maybe,
    typeKind,
 )
import GHC.Core.Unify (BindFlag (..), tcMatchTyX_BM)
import GHC.Data.Bag (emptyBag)
import GHC.Data.FastString (fsLit)
import GHC.Driver.DynFlags (DynFlags, refLevelHoleFits, xopt)
import GHC.Driver.Plugins (
    CommandLineOption,
    Plugin (..),
    defaultPlugin,
    flagRecompile,
 )
import GHC.Driver.Session (FlagSpec (..), getDynFlags, xFlags)
import GHC.Tc.Errors.Hole (
    HoleFitDispConfig (..),
    getHoleFitDispConfig,
    tcCheckHoleFit,
    tcFilterHoleFits,
    withoutUnification,
 )
import GHC.Tc.Errors.Hole.FitTypes (
    HoleFit (..),
    HoleFitCandidate (..),
    TcHoleFit (..),
    TypedHole (..),
 )
import GHC.Tc.Errors.Hole.Plugin (
    CandPlugin,
    FitPlugin,
    HoleFitPlugin (..),
    HoleFitPluginR (..),
 )
import GHC.Tc.Solver (tcRewriteFamilyAxioms)
import GHC.Tc.TyCl.PatSyn (patSynBuilderOcc)
import GHC.Tc.Types (
    TcGblEnv (tcg_mod),
    TcM,
    TcRef,
 )
import GHC.Tc.Types.BasicTypes (TcBinder (..), TcTyThing (AGlobal, ATcId, tct_id))
import GHC.Tc.Types.Constraint (Hole (..), HoleSort (..), Implication (..))
import GHC.Tc.Types.CtLoc (CtLoc, CtLocEnv (ctl_bndrs, ctl_rdr), ctLocEnv)
import GHC.Tc.Types.ErrCtxt (isSigMaybe)
import GHC.Tc.Types.Origin (SkolemInfoAnon (PatSkol, SigSkol))
import GHC.Tc.Utils.Env (tcLookup)
import GHC.Tc.Utils.Monad (
    getGblEnv,
    getLclTypeEnv,
    liftZonkM,
    newSysName,
    newTcRef,
    readTcRef,
    setCtLocM,
    tryTcDiscardingErrs,
    updTcRef,
    writeTcRef,
 )
import GHC.Tc.Utils.TcMType (newOpenFlexiTyVar)
import GHC.Tc.Utils.TcType (TcType, mkPhiTy, tcEqType, tcSplitForAllInvisTyVars, tcSplitPhiTy)
import GHC.Tc.Utils.Unify (
    DeepSubsumptionDepth (..),
    DeepSubsumptionFlag (..),
    getDeepSubsumptionFlag,
 )
import GHC.Tc.Zonk.TcType (zonkTcType)
import GHC.Types.Basic (isTopLevel)
import GHC.Types.Id (Id, idName, idType, isDeadEndId, mkLocalId)
import GHC.Types.Name (
    Name,
    NamedThing (getName, getOccName),
    getSrcLoc,
    isValNameSpace,
    mkTyVarOccFS,
    mkVarOcc,
    mkVarOccFS,
    nameModule_maybe,
    nameOccName,
    occNameFS,
    occNameSpace,
    occNameString,
    sourceTableTermOcc,
 )
import GHC.Types.Name.Env (NameEnv, emptyNameEnv, extendNameEnv, lookupNameEnv)
import GHC.Types.Name.Occurrence (
    OccEnv,
    OccSet,
    elemOccSet,
    emptyOccEnv,
    extendOccEnv,
    isUnderscore,
    lookupOccEnv,
    mkOccSet,
 )
import GHC.Types.Name.Reader (
    LocalRdrEnv,
    localRdrEnvElts,
    lookupLocalRdrOcc,
    pprNameProvenance,
 )
import GHC.Types.Name.Set (NameSet, elemNameSet, mkNameSet)
import GHC.Types.TyThing (TyThing (AConLike, AnId))
import GHC.Types.Unique.Map (listToUniqMap, lookupUniqMap)
import GHC.Types.Var (
    DepFunTyFlag (..),
    ForAllTyFlag (Required),
    TyVar,
    VarBndr (Bndr),
    isGlobalId,
    isInvisibleForAllTyFlag,
    isNonCoVarId,
    isVisibleFunArg,
    mkTyVar,
    setTyVarKind,
    setVarName,
    tyVarKind,
    varType,
 )
import GHC.Types.Var.Env (VarEnv, emptyTidyEnv, lookupVarEnv, mkVarEnv)
import GHC.Types.Var.Set (VarSet, elemVarSet, emptyVarSet, mkVarSet)
import GHC.Unit.Module (Module, moduleName, moduleNameString)
import GHC.Utils.Misc (equalLength)
import GHC.Utils.Outputable (
    SDoc,
    dcolon,
    hang,
    nest,
    parens,
    ppWhen,
    ppr,
    pprPrefixOcc,
    sep,
    showSDocUnsafe,
    text,
    ($$),
    (<+>),
 )

{- Note [Bounded backward-chaining proof search in HoleFitPlugin]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
GHC's `findValidHoleFits` invokes each registered `HoleFitPlugin` inside
`withHoleLclEnv`, where the hole's lexical `LocalRdrEnv`, local `Id` bindings,
and enclosing Given implications (`th_implics`) are active in `TcM`:

1. Two-pass invocation protocol:
   `candPlugin` runs once per expression hole and receives the unscoped list of
   in-scope `HoleFitCandidate` values. When refinement hole fits are active
   (`-frefinement-level-hole-fits=N` with `N >= 0`), GHC calls `fitPlugin`
   twice on that hole: first for `Valid refinement hole fits`, and second for
   `Valid hole fits`. When refinement hole fits are disabled, GHC calls
   `fitPlugin` once for `Valid hole fits`. `PluginState` records the hole's
   candidates in `candPlugin` and increments `psPassIndex` on each `fitPlugin`
   call so the plugin distinguishes `RefinementPass` from `ValidPass`.

2. Type-directed generality:
   The plugin does not reference specific library modules or datatype names.
   Instead, it inspects candidate types directly:
   - Nullary GADT constructors and local bindings solve leaf goals at depth 0.
   - Saturated `foreach` (`DepFunTy`) calls reify type-level runtime indices,
     promoted constructors, and source-table applications into source terms at
     depth 1.
   - Introduction rules, symmetry combinators, and GADT constructors peel
     invisible quantifiers, `foreach` binders, and visible proof subgoals,
     instantiate template variables from the normalized goal via `matchDepResult`,
     and solve remaining proof subgoals recursively at `depth - 1`.
   - Required-type-argument congruence combinators (`forall f -> x ~ y -> f x ~ f y`)
     split normalized equality goals whose endpoints share an outer constructor,
     source-table prefix, or local function spine differing in the final argument.
   - Binary transitivity combinators (`a ~ b -> b ~ c -> a ~ c`) pair with
     in-scope equality lemmas that rewrite the normalized LHS or RHS to a
     distinct intermediate type `mid`.

3. Normalization, solver soundness, and source binder names:
   - Every goal and intermediate rewrite endpoint is pre-normalized with
     `tcRewriteFamilyAxioms` inside `tryTcDiscardingErrs` and `withoutUnification`.
   - Every instantiated candidate or subgoal step is verified with
     `tcCheckHoleFit` inside `withoutUnification`, preserving enclosing
     `th_implics` Givens and `th_relevant_cts` without mutating meta-variables.
   - Tidied local runtime `Id`s (such as `m1` or `n1`) are mapped back to their
     unambiguous source `Name`s in `LocalRdrEnv` (`sourceTermOcc`) in both
     synthesized expressions and subgoal hole annotations, so pasted suggestions
     typecheck verbatim.
   - Recursive calls to an enclosing function require at least one bare
     `TermVarTy` argument in `seStrictSubterms`, preventing non-terminating
     self-applications.
-}

-- | Configuration for bounded proof synthesis and subgoal refinement.
data SearchConfig = SearchConfig
    { scDepth :: !Int
    {- ^ Maximum expression tree depth for complete (@0@-subgoal) proof synthesis
    (clamped to @0..5@, default @2@).
    -}
    , scMaxFits :: !Int
    -- ^ Maximum number of synthesized fits injected per hole pass (default @8@).
    , scMaxCandidates :: !Int
    -- ^ Solver candidate check budget per hole pass (default @64@).
    , scAuto :: !Bool
    -- ^ Enable complete (@0@-hole) backward-chaining proof synthesis (default 'True').
    , scCongruence :: !Bool
    -- ^ Enable congruence subgoal refinements and search steps (default 'True').
    , scTransitivity :: !Bool
    -- ^ Enable transitivity subgoal refinements and search steps (default 'True').
    , scSubgoalsInValid :: !Bool
    {- ^ Emit 1-hole subgoal refinements in @Valid hole fits@ when
    @-frefinement-level-hole-fits@ is unset (default 'False').
    -}
    }
    deriving (Eq, Ord, Read, Show)

{- | Default proof-search configuration: depth @2@, at most @8@ fits and @64@
solver checks per hole pass, with auto, congruence, and transitivity enabled.
-}
defaultSearchConfig :: SearchConfig
defaultSearchConfig =
    SearchConfig
        { scDepth = 2
        , scMaxFits = 8
        , scMaxCandidates = 64
        , scAuto = True
        , scCongruence = True
        , scTransitivity = True
        , scSubgoalsInValid = False
        }

{- | Parse colon- or comma-separated @-fplugin-opt=Dependent.Plugin.ProofSearch:...@
arguments into a 'SearchConfig'.
-}
parseSearchOptions :: [CommandLineOption] -> SearchConfig
parseSearchOptions = foldl applyToken defaultSearchConfig . concatMap splitTokens
  where
    splitTokens :: String -> [String]
    splitTokens s =
        case dropWhile isSep s of
            "" -> []
            s' ->
                let (tok, rest) = break isSep s'
                 in trim tok : splitTokens rest

    isSep :: Char -> Bool
    isSep c = c == ':' || c == ','

    trim :: String -> String
    trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace

    applyToken :: SearchConfig -> String -> SearchConfig
    applyToken cfg raw =
        case map toLower raw of
            "" -> cfg
            "auto" -> cfg{scAuto = True}
            "no-auto" -> cfg{scAuto = False}
            "congruence" -> cfg{scCongruence = True}
            "no-congruence" -> cfg{scCongruence = False}
            "transitivity" -> cfg{scTransitivity = True}
            "no-transitivity" -> cfg{scTransitivity = False}
            "subgoals-in-valid" -> cfg{scSubgoalsInValid = True}
            "no-subgoals-in-valid" -> cfg{scSubgoalsInValid = False}
            tok
                | Just v <- stripPrefix "depth=" tok
                , Just n <- readMaybe v ->
                    cfg{scDepth = max 0 (min 5 n)}
                | Just v <- stripPrefix "max-fits=" tok
                , Just n <- readMaybe v ->
                    cfg{scMaxFits = max 0 n}
                | Just v <- stripPrefix "max-candidates=" tok
                , Just n <- readMaybe v ->
                    cfg{scMaxCandidates = max 0 n}
                | Just v <- stripPrefix "auto=" tok
                , Just b <- parseBool v ->
                    cfg{scAuto = b}
                | Just v <- stripPrefix "congruence=" tok
                , Just b <- parseBool v ->
                    cfg{scCongruence = b}
                | Just v <- stripPrefix "transitivity=" tok
                , Just b <- parseBool v ->
                    cfg{scTransitivity = b}
                | Just v <- stripPrefix "subgoals-in-valid=" tok
                , Just b <- parseBool v ->
                    cfg{scSubgoalsInValid = b}
                | otherwise -> cfg

    parseBool :: String -> Maybe Bool
    parseBool "true" = Just True
    parseBool "1" = Just True
    parseBool "yes" = Just True
    parseBool "false" = Just False
    parseBool "0" = Just False
    parseBool "no" = Just False
    parseBool _ = Nothing

{- | GHC plugin entry point for @-fplugin=Dependent.Plugin.ProofSearch@.
Keeps all non-hole hooks from 'defaultPlugin' unchanged.
-}
plugin :: Plugin
plugin =
    defaultPlugin
        { holeFitPlugin = \opts -> Just (mkProofSearchPlugin (parseSearchOptions opts))
        , pluginRecompile = flagRecompile
        }

-- | Cached type information for a non-local 'Name'.
type CandInfo = (Name, Bool, Type)

-- | Mutable per-module state stored in 'HoleFitPluginR'.
data PluginState = PluginState
    { psCurrentCands :: ![HoleFitCandidate]
    , psPassIndex :: !Int
    , psHasImplicitDepRef :: !(Maybe Bool)
    , psGlobalTypeCache :: !(NameEnv (Maybe CandInfo))
    }

-- | Which 'findValidHoleFits' pass is currently invoking 'fitPlugin'.
data HolePass
    = RefinementPass
    | ValidPass
    deriving (Eq, Show)

{- | Construct the stateful 'HoleFitPluginR' from a 'SearchConfig'.
See Note [Bounded backward-chaining proof search in HoleFitPlugin].
-}
mkProofSearchPlugin :: SearchConfig -> HoleFitPluginR
mkProofSearchPlugin cfg =
    HoleFitPluginR
        { hfPluginInit =
            newTcRef
                PluginState
                    { psCurrentCands = []
                    , psPassIndex = 0
                    , psHasImplicitDepRef = Nothing
                    , psGlobalTypeCache = emptyNameEnv
                    }
        , hfPluginRun = \ref ->
            HoleFitPlugin
                { candPlugin = recordHoleCands ref
                , fitPlugin = runProofSearchPass cfg ref
                }
        , hfPluginStop = \_ -> pure ()
        }

-- | Record the hole's candidate list and reset the per-hole pass index.
recordHoleCands :: TcRef PluginState -> CandPlugin
recordHoleCands ref _hole cands = do
    updTcRef ref (\st -> st{psCurrentCands = cands, psPassIndex = 0})
    pure cands

-- | Is @-XDependentTypes@ enabled in 'DynFlags'?
hasDependentTypesExt :: DynFlags -> Bool
hasDependentTypesExt dflags =
    any (\fs -> flagSpecName fs == "DependentTypes" && xopt (flagSpecFlag fs) dflags) xFlags

{- | Detect whether the host GHC runs an implicit level-1 refinement pass when
@-frefinement-level-hole-fits@ is unset under @-XDependentTypes@.
-}
detectImplicitDepRef :: TcM Bool
detectImplicitDepRef =
    tryTcDiscardingErrs (pure False) $ do
        dflags <- getDynFlags
        if not (hasDependentTypesExt dflags)
            then pure False
            else do
                tvNm <- newSysName (mkTyVarOccFS (fsLit "a"))
                idNm <- newSysName (mkVarOccFS (fsLit "$probe_req"))
                let tv = mkTyVar tvNm liftedTypeKind
                    candTy = mkForAllTy unmatchableDataConTy (Bndr tv Required) (mkListTy (mkTyVarTy tv))
                    probeId = mkLocalId idNm manyDataConTy candTy
                rTv <- newOpenFlexiTyVar
                let hTy = mkVisFunTyManyU (mkTyVarTy rTv) (mkListTy unitTy)
                    dummyHole =
                        TypedHole
                            { th_relevant_cts = emptyBag
                            , th_implics = []
                            , th_hole = Nothing
                            }
                (_, subs) <- tcFilterHoleFits (Just 1) dummyHole (hTy, [rTv]) [IdHFCand probeId]
                pure (null subs)

-- | Run one 'fitPlugin' pass ('RefinementPass' or 'ValidPass') for an expression hole.
runProofSearchPass :: SearchConfig -> TcRef PluginState -> FitPlugin
runProofSearchPass cfg ref typedHole fits
    | Just (Hole{hole_sort = ExprHole _, hole_loc = ctLoc, hole_ty = rawHoleTy}) <- th_hole typedHole = do
        st0 <- readTcRef ref
        hasImpRef <- case psHasImplicitDepRef st0 of
            Just b -> pure b
            Nothing -> do
                b <- detectImplicitDepRef
                updTcRef ref (\s -> s{psHasImplicitDepRef = Just b})
                pure b
        st <- readTcRef ref
        let passIdx = psPassIndex st
            cands = psCurrentCands st
        writeTcRef ref (st{psPassIndex = passIdx + 1})

        dflags <- getDynFlags
        hfdc <- getHoleFitDispConfig
        tcgEnv <- getGblEnv
        let mbRefLvl = refLevelHoleFits dflags
            depExts = hasDependentTypesExt dflags
            effRefLvl =
                case mbRefLvl of
                    Just n -> Just n
                    Nothing | depExts && hasImpRef -> Just 1
                    Nothing -> Nothing
            passKind
                | effRefLvl >= Just 0 && passIdx == 0 = RefinementPass
                | otherwise = ValidPass
            baseFits
                | hasImpRef = [TcHoleFit hf | TcHoleFit hf <- fits]
                | otherwise = fits

        if scMaxFits cfg <= 0 || scMaxCandidates cfg <= 0
            then pure baseFits
            else do
                goalTy <- normalizeGoalTy ctLoc rawHoleTy
                let env = mkScopeEnv (tcg_mod tcgEnv) ctLoc typedHole goalTy cands
                budgetRef <- newTcRef (scMaxCandidates cfg)
                let lookupCand = mkMemoCandLookup ref (isGadtGoalTy goalTy)
                case passKind of
                    RefinementPass
                        | effRefLvl >= Just 1 -> do
                            refFits <- synthesizeSubgoalFits cfg lookupCand budgetRef env hfdc goalTy cands
                            pure (prependDedupFits (scMaxFits cfg) refFits baseFits)
                        | otherwise ->
                            pure baseFits
                    ValidPass -> do
                        autoFits <-
                            if scAuto cfg
                                then synthesizeCompleteFits cfg lookupCand budgetRef env hfdc goalTy cands
                                else pure []
                        extraSubFits <-
                            if scSubgoalsInValid cfg
                                then synthesizeSubgoalFits cfg lookupCand budgetRef env hfdc goalTy cands
                                else pure []
                        pure (prependDedupFits (scMaxFits cfg) (autoFits ++ extraSubFits) baseFits)
    | otherwise = pure fits

-- | Lexical and implication context for a single expression hole.
data ScopeEnv = ScopeEnv
    { seCtLoc :: !CtLoc
    , seHoleNoSelf :: !TypedHole
    , seLocalRdr :: !LocalRdrEnv
    , seHoleTermIds :: ![Id]
    , seAutoLocals :: ![Id]
    , seLocalById :: !(VarEnv Id)
    , seLocalByOcc :: !(OccEnv Id)
    , seInScopeNames :: !NameSet
    , seInScopeValOccs :: !OccSet
    , seStrictSubterms :: !VarSet
    , seHomeMod :: !Module
    , seSelfOccs :: !OccSet
    }

{- | Build the 'ScopeEnv' for a hole from its 'CtLoc', enclosing 'Implication's,
and in-scope 'HoleFitCandidate's.
-}
mkScopeEnv :: Module -> CtLoc -> TypedHole -> TcType -> [HoleFitCandidate] -> ScopeEnv
mkScopeEnv homeMod ctLoc typedHole goalTy cands =
    ScopeEnv
        { seCtLoc = ctLoc
        , seHoleNoSelf = typedHole{th_hole = Nothing}
        , seLocalRdr = lclRdr
        , seHoleTermIds = holeTermIds
        , seAutoLocals = autoLocals
        , seLocalById = mkVarEnv [(v, v) | v <- autoLocals]
        , seLocalByOcc =
            foldl
                (\acc v -> extendOccEnv acc (getOccName v) v)
                emptyOccEnv
                (reverse autoLocals)
        , seInScopeNames = mkNameSet (map getName cands)
        , seInScopeValOccs =
            mkOccSet
                [ getOccName c
                | c <- cands
                , isValNameSpace (occNameSpace (getOccName c))
                ]
        , seStrictSubterms = computeStrictSubterms lclRdr holeTermIds typedHole autoLocals
        , seHomeMod = homeMod
        , seSelfOccs = mkOccSet (sigOccs ++ enclOcc)
        }
  where
    lclEnv = ctLocEnv ctLoc
    lclRdr = ctl_rdr lclEnv
    candLocals =
        [ i
        | IdHFCand i <- cands
        , not (isUnderscore (nameOccName (idName i)))
        ]
    bndrLocals =
        [ b
        | TcIdBndr b _ <- ctl_bndrs lclEnv
        , not (isUnderscore (nameOccName (idName b)))
        ]
    holeTermIds =
        [ v
        | v <- tyCoVarsOfTypeList goalTy
        , isNonCoVarId v
        , not (isGlobalId v)
        , not (isUnderscore (nameOccName (idName v)))
        ]
    autoLocals = nubBy ((==) `on` idName) (candLocals ++ bndrLocals ++ holeTermIds)

    bndrOcc (TcIdBndr b tl) = Just (nameOccName (idName b), tl)
    bndrOcc (TcIdBndr_ExpType nm _ tl) = Just (nameOccName nm, tl)
    bndrOcc (TcTvBndr _ _) = Nothing

    allIdBndrs = mapMaybe bndrOcc (ctl_bndrs lclEnv)
    notTopOccs = [occ | (occ, tl) <- allIdBndrs, not (isTopLevel tl)]
    enclOcc =
        case reverse notTopOccs of
            occ : _ -> [occ]
            [] -> [occ | (occ, _) : _ <- [allIdBndrs]]
    sigOccs =
        [ nameOccName fnNm
        | imp <- th_implics typedHole
        , SigSkol uctxt _ _ <- [ic_info imp]
        , Just fnNm <- [isSigMaybe uctxt]
        ]

-- | Does 'Name' refer to the enclosing function currently being defined?
isSelfName :: ScopeEnv -> Name -> Bool
isSelfName env nm =
    (isNothing (nameModule_maybe nm) || nameModule_maybe nm == Just (seHomeMod env))
        && (nameOccName nm `elemOccSet` seSelfOccs env)

{- | Compute variables introduced as strict structural subterms by enclosing
pattern matches or Given constructor equalities.
-}
computeStrictSubterms :: LocalRdrEnv -> [Id] -> TypedHole -> [Id] -> VarSet
computeStrictSubterms lclRdr holeTermIds typedHole autoLocals
    | not (null eqSubterms) = mkVarSet (eqSubterms ++ aliasedSubterms)
    | otherwise = mkVarSet patFallbackSubterms
  where
    eqSubterms =
        [ v
        | imp <- th_implics typedHole
        , ev <- ic_given imp
        , Just (_, lhs, rhs) <- [getEqPredTys_maybe (varType ev)]
        , v <- subtermsFromEq lhs rhs ++ subtermsFromEq rhs lhs
        ]

    srcOccSet =
        mkOccSet
            [ maybe (getOccName u) nameOccName (sourceTermOccRaw lclRdr holeTermIds u)
            | u <- eqSubterms
            ]

    aliasedSubterms =
        [ v
        | v <- autoLocals
        , let occ = maybe (getOccName v) nameOccName (sourceTermOccRaw lclRdr holeTermIds v)
        , occ `elemOccSet` srcOccSet
        ]

    patFallbackSubterms =
        [ v
        | imp <- th_implics typedHole
        , PatSkol (RealDataCon dc) _ <- [ic_info imp]
        , dataConSourceArity dc > 0
        , let outerIds = mkVarSet [b | TcIdBndr b _ <- ctl_bndrs (ic_env imp)]
        , v <- autoLocals
        , not (v `elemVarSet` outerIds)
        ]

    subtermsFromEq lhs rhs
        | isScrutineeLhs lhs
        , Just (tc, args) <- splitTyConApp_maybe (coreFullView rhs)
        , isJust (isPromotedDataCon_maybe tc) =
            let lhsVars = tyCoVarsOfType lhs
             in [ v
                | v <- concatMap tyCoVarsOfTypeList args
                , isNonCoVarId v
                , not (v `elemVarSet` lhsVars)
                ]
        | otherwise = []

    isScrutineeLhs ty =
        case coreFullView ty of
            TermVarTy _ -> True
            TyVarTy _ -> True
            _ -> False

{- | Resolve a tidied local runtime 'Id' (such as @n1@) back to its unambiguous
source 'Name' in 'LocalRdrEnv'.
See Note [Bounded backward-chaining proof search in HoleFitPlugin].
-}
sourceTermOcc :: ScopeEnv -> Id -> Maybe Name
sourceTermOcc env = sourceTermOccRaw (seLocalRdr env) (seHoleTermIds env)

sourceTermOccRaw :: LocalRdrEnv -> [Id] -> Id -> Maybe Name
sourceTermOccRaw lclRdr holeTermIds v
    | Just nm <- lookupUniqMap rdrByUniq (idName v) =
        Just nm
    | not (null baseStr)
    , baseStr /= occStr
    , isNothing (lookupLocalRdrOcc lclRdr (mkVarOcc occStr))
    , Just nm <- lookupLocalRdrOcc lclRdr (mkVarOcc baseStr)
    , isValNameSpace (occNameSpace (nameOccName nm))
    , not (nameOccName nm `elemOccSet` usedRawOccs) =
        Just nm
    | otherwise =
        Nothing
  where
    valRdrNames =
        [ nm
        | nm <- localRdrEnvElts lclRdr
        , isValNameSpace (occNameSpace (nameOccName nm))
        ]
    rdrByUniq = listToUniqMap [(nm, nm) | nm <- valRdrNames]
    usedRawOccs =
        mkOccSet
            [ nameOccName nm
            | u <- holeTermIds
            , Just nm <- [lookupUniqMap rdrByUniq (idName u)]
            ]
    occStr = occNameString (getOccName v)
    baseStr = reverse (dropWhile isDigit (reverse occStr))

-- | Pretty-print a local runtime 'Id' using its unrenamed source occurrence.
pprSourceTermId :: ScopeEnv -> Id -> SDoc
pprSourceTermId env v =
    maybe
        (pprPrefixOcc (getOccName v))
        (pprPrefixOcc . nameOccName)
        (sourceTermOcc env v)

{- | Replace tidied local runtime 'Id' occurrences inside a 'Type' with their
unrenamed source 'Name's for user-facing hole annotations.
-}
renameSourceIdsInType :: ScopeEnv -> Type -> Type
renameSourceIdsInType env = go
  where
    restore v =
        case sourceTermOcc env v of
            Just srcNm -> setVarName v srcNm
            Nothing -> v

    go (TyVarTy tv) = TyVarTy tv
    go (TermVarTy v) = TermVarTy (restore v)
    go (TermAppTy f arg) = TermAppTy (restore f) (go arg)
    go (AppTy t1 t2) = AppTy (go t1) (go t2)
    go (TyConApp tc tys) = TyConApp tc (map go tys)
    go (FunTy af ma w arg res) = FunTy af (go ma) (go w) (go arg) (go res)
    go (ForAllTy ma bndr inner) = ForAllTy (go ma) bndr (go inner)
    go (DepFunTy fl b body) = DepFunTy fl b (go body)
    go (DepDictTy b body) = DepDictTy b (go body)
    go (ExistsTy fl b body) = ExistsTy fl b (go body)
    go (ClassAppTy c i d o k) = ClassAppTy c (go i) (go d) (go o) (go k)
    go (CastTy ty co) = CastTy (go ty) co
    go (LitTy l) = LitTy l
    go (CoercionTy co) = CoercionTy co

-- | Zonk, tidy open type variables, and restore source 'Id' names for display.
prepareDisplayType :: ScopeEnv -> TcType -> TcM Type
prepareDisplayType env ty = do
    zTy <- liftZonkM (zonkTcType ty)
    pure (renameSourceIdsInType env (tidyOpenType emptyTidyEnv zTy))

-- | Pre-normalize open and closed family redexes in a goal or endpoint type.
normalizeGoalTy :: CtLoc -> TcType -> TcM TcType
normalizeGoalTy ctLoc ty
    | isFamFreeTy ty = pure ty
    | otherwise =
        tryTcDiscardingErrs (pure ty) $
            withoutUnification (tyCoVarsOfType ty) $
                setCtLocM ctLoc $ do
                    Reduction _ normTy <- tcRewriteFamilyAxioms ctLoc ty
                    pure normTy

-- | Is the goal type headed by an indexed GADT?
isGadtGoalTy :: Type -> Bool
isGadtGoalTy ty
    | Just (tc, _) <- splitTyConApp_maybe (coreFullView ty)
    , isAlgTyCon tc
    , let dcs = tyConDataCons tc
    , not (null dcs) =
        any hasEqSpec dcs
    | otherwise = False
  where
    hasEqSpec :: DataCon -> Bool
    hasEqSpec dc =
        case dataConFullSig dc of
            (_, _, eqSpec, _, _, _) -> not (null eqSpec)

-- | Memoized candidate type lookup backed by 'psGlobalTypeCache'.
mkMemoCandLookup :: TcRef PluginState -> Bool -> HoleFitCandidate -> TcM (Maybe CandInfo)
mkMemoCandLookup ref gadtGoal cand =
    case cand of
        IdHFCand i
            | isAllowedCandId i -> pure (Just (idName i, False, idType i))
            | otherwise -> pure Nothing
        _ -> do
            let nm = getName cand
            if not (isValNameSpace (occNameSpace (nameOccName nm)))
                then pure Nothing
                else do
                    st <- readTcRef ref
                    case lookupNameEnv (psGlobalTypeCache st) nm of
                        Just cached -> pure cached
                        Nothing
                            | gadtGoal && skipIrrelevantPrelMod nm -> do
                                updTcRef ref (\s -> s{psGlobalTypeCache = extendNameEnv (psGlobalTypeCache s) nm Nothing})
                                pure Nothing
                            | otherwise -> do
                                res <- tryTcDiscardingErrs (pure Nothing) (lookupGlobalCand nm)
                                updTcRef ref (\s -> s{psGlobalTypeCache = extendNameEnv (psGlobalTypeCache s) nm res})
                                pure res
  where
    -- Skip only compiler IO/Read/Show/Enum modules that cannot define pure GADT
    -- proof constructors or equality combinators, avoiding interface churn.
    skipIrrelevantPrelMod :: Name -> Bool
    skipIrrelevantPrelMod nm
        | Just m <- nameModule_maybe nm
        , let modStr = moduleNameString (moduleName m) =
            any (`isPrefixOf` modStr) ["GHC.Internal.Read", "GHC.Internal.Show", "GHC.Internal.IO", "System.IO", "Text.Read", "Text.Show"]
        | otherwise = False

-- | Look up a non-local 'Name' in the typechecker environment.
lookupGlobalCand :: Name -> TcM (Maybe CandInfo)
lookupGlobalCand nm = do
    thing <- tcLookup nm
    pure $
        case thing of
            ATcId{tct_id = i}
                | isAllowedCandId i -> Just (idName i, False, idType i)
            AGlobal (AnId i)
                | isAllowedCandId i -> Just (idName i, False, idType i)
            AGlobal (AConLike (RealDataCon con)) ->
                Just (dataConName con, True, dataConWrapperType con)
            AGlobal (AConLike (PatSynCon ps))
                | Just (_, t) <- patSynBuilderOcc ps ->
                    Just (patSynName ps, False, t)
            _ -> Nothing

-- | Exclude diverging and unsafe-coercion identifiers from proof synthesis.
isAllowedCandId :: Id -> Bool
isAllowedCandId i =
    not (isDeadEndId i)
        && nameModule_maybe (idName i) `notElem` [Just gHC_INTERNAL_ERR, Just gHC_INTERNAL_UNSAFE_COERCE]

-- | Decrement the per-hole solver check budget, returning 'False' once exhausted.
spendBudget :: TcRef Int -> TcM Bool
spendBudget budgetRef = do
    n <- readTcRef budgetRef
    if n <= 0
        then pure False
        else do
            writeTcRef budgetRef (n - 1)
            pure True

{- | Soundness gate: verify that @candInstTy@ is a subtype of @goalTy@ with all
wanted and relevant constraints solved inside enclosing 'th_implics' Givens,
restoring all flexible unification variables via 'withoutUnification'.
-}
checkSoundFit :: TcRef Int -> ScopeEnv -> Bool -> TcType -> TcType -> TcM Bool
checkSoundFit budgetRef env isDc goalTy candInstTy = do
    okBudget <- spendBudget budgetRef
    if not okBudget
        then pure False
        else tryTcDiscardingErrs (pure False) $
            withoutUnification (tyCoVarsOfTypes [goalTy, candInstTy]) $ do
                baseDs <- getDeepSubsumptionFlag
                let dsFlag =
                        case baseDs of
                            Deep DeepSub -> Deep DeepSub
                            _ | isDc -> Deep TopSub
                            _ -> Shallow
                isJust <$> tcCheckHoleFit dsFlag (seHoleNoSelf env) goalTy candInstTy

{- | Verify that every non-global runtime 'Id' occurring in the chosen types
refers to an in-scope local binding in 'TcLclEnv' with matching type.
-}
checkRuntimeScope :: [Type] -> TcM Bool
checkRuntimeScope tys = do
    lclEnv <- getLclTypeEnv
    let runtimeIds =
            filter (\v -> isNonCoVarId v && not (isGlobalId v)) $
                concatMap tyCoVarsOfTypeList tys
        okId v =
            case lookupNameEnv lclEnv (idName v) of
                Just (ATcId{tct_id = bndr}) ->
                    bndr == v && (varType bndr `eqType` varType v)
                _ -> False
    pure (all okId runtimeIds)

-- | Extract the head 'TyCon' of a result type after stripping invisible binders.
depResHead :: Type -> Maybe TyCon
depResHead ty | Just ty' <- coreView ty = depResHead ty'
depResHead (TyConApp tc _) = Just tc
depResHead (FunTy{ft_af = af, ft_res = r})
    | isVisibleFunArg af = Just (funTyFlagTyCon af)
    | otherwise = depResHead r
depResHead (ForAllTy _ (Bndr _ vis) b)
    | isInvisibleForAllTyFlag vis = depResHead b
depResHead (DepFunTy _ _ b) = depResHead b
depResHead (DepDictTy _ b) = depResHead b
depResHead _ = Nothing

{- | Extract @(tc, lhs, rhs)@ from a binary equality-like or indexed GADT type
whose final two arguments are the endpoints.
-}
splitBinaryRelLike :: Type -> Maybe (TyCon, Type, Type)
splitBinaryRelLike ty
    | Just (tc, args) <- splitTyConApp_maybe (coreFullView ty)
    , isAlgTyCon tc
    , rhs : lhs : _ <- reverse args =
        Just (tc, lhs, rhs)
    | otherwise = Nothing

{- | Extract @(tc, lhs, rhs)@ when @lhs@ and @rhs@ share a common kind (or
belong to an indexed GADT with equality specifications, such as heterogeneous
equality).
-}
splitEqGoalLike :: Type -> Maybe (TyCon, Type, Type)
splitEqGoalLike ty
    | Just (tc, lhs, rhs) <- splitBinaryRelLike ty
    , isGadtGoalTy ty || (typeKind lhs `eqType` typeKind rhs) =
        Just (tc, lhs, rhs)
    | otherwise = Nothing

{- | Match a formal result template against an actual goal type, binding only
template variables in @bindTvs@. Supports repeated GADT indices and higher-order
congruence applications (@f x@ against @TyConApp@ or @TermAppTy@).
-}
matchDepResult :: [TyVar] -> Type -> Type -> Maybe Subst.Subst
matchDepResult bindTvs formalRes actualRes
    | Just s0 <- matchOne Subst.emptySubst formalRes actualRes =
        Just s0
    | Just pairs <- decompPairs formalRes actualRes
    , let cands = mapMaybe (uncurry (matchOne Subst.emptySubst)) pairs
    , not (null cands) =
        let pick s tv =
                case [ty | sub <- cands, Just ty <- [Subst.lookupTyVar sub tv]] of
                    (ty : _) -> Subst.extendTvSubstAndInScope s tv ty
                    [] -> s
            merged = foldl pick Subst.emptySubst bindTvs
            boundAny = null bindTvs || any (isJust . Subst.lookupTyVar merged) bindTvs
         in if boundAny then Just merged else Nothing
    | otherwise = Nothing
  where
    bindFn tv _
        | tv `elem` bindTvs = BindMe
        | otherwise = DontBindMe

    matchOne subst formal actual
        | Just s1 <- tcMatchTyX_BM bindFn subst (typeKind formal) (typeKind actual)
        , Just s2 <- tcMatchTyX_BM bindFn s1 formal actual =
            Just s2
        | AppTy fTmpl xTmpl <- coreFullView formal
        , Just (con, args) <- splitTyConApp_maybe (coreFullView actual)
        , lastA : revPrefix <- reverse args
        , let prefix = mkTyConApp con (reverse revPrefix)
        , Just s1 <- matchOne subst fTmpl prefix
        , Just s2 <- matchOne s1 xTmpl lastA =
            Just s2
        | AppTy fTmpl xTmpl <- coreFullView formal
        , TermAppTy fnId lastA <- coreFullView actual
        , Just s1 <- matchOne subst fTmpl (TermVarTy fnId)
        , Just s2 <- matchOne s1 xTmpl lastA =
            Just s2
        | formal' <- coreFullView formal
        , CastTy actual' co <- coreFullView actual
        , coercionRole co == Nominal =
            matchOne subst formal' actual'
        | Just s <- matchEndpointSubst bindTvs subst formal actual =
            Just s
        | otherwise = Nothing

    decompPairs formal actual
        | Just (tc1, ts1) <- splitTyConApp_maybe (coreFullView formal)
        , Just (tc2, ts2) <- splitTyConApp_maybe (coreFullView actual)
        , tc1 == tc2
        , isAlgTyCon tc1
        , length ts1 == tyConArity tc1
        , ts1 `equalLength` ts2 =
            let vis1 = filterOutInvisibleTypes tc1 ts1
                vis2 = filterOutInvisibleTypes tc2 ts2
             in if not (null vis1) && vis1 `equalLength` vis2
                    then Just (zip vis1 vis2)
                    else Just (zip ts1 ts2)
        | otherwise = Nothing

{- | Match a rewrite lemma's endpoint template strictly against an equality
endpoint, decomposing aligned constructors, applications, and type families.
-}
matchEndpointTemplate :: [TyVar] -> Type -> Type -> Maybe Subst.Subst
matchEndpointTemplate bindTvs = matchEndpointSubst bindTvs Subst.emptySubst

matchEndpointSubst :: [TyVar] -> Subst.Subst -> Type -> Type -> Maybe Subst.Subst
matchEndpointSubst bindTvs = matchSub
  where
    bindSet = mkVarSet bindTvs

    hasBindVar :: Type -> Bool
    hasBindVar ty = any (`elemVarSet` bindSet) (tyCoVarsOfTypeList ty)

    matchSub :: Subst.Subst -> Type -> Type -> Maybe Subst.Subst
    matchSub s t1Raw t2Raw
        | TyVarTy tv <- t1
        , tv `elemVarSet` bindSet = do
            s1 <- matchSub s (tyVarKind tv) (typeKind t2)
            case Subst.lookupTyVar s1 tv of
                Nothing
                    | Subst.substTy s1 (tyVarKind tv) `tcEqType` typeKind t2 ->
                        Just (Subst.extendTvSubstAndInScope s1 tv t2)
                    | otherwise -> Nothing
                Just prev
                    | prev `tcEqType` t2 -> Just s1
                    | otherwise -> Nothing
        | not (hasBindVar t1)
        , t1 `tcEqType` t2 =
            Just s
        | Just (tc1, ts1) <- splitTyConApp_maybe t1
        , Just (tc2, ts2) <- splitTyConApp_maybe t2
        , tc1 == tc2
        , isAlgTyCon tc1 || isTypeFamilyTyCon tc1 || isJust (isPromotedDataCon_maybe tc1)
        , ts1 `equalLength` ts2 =
            foldM (\acc (u1, u2) -> matchSub acc u1 u2) s (zip ts1 ts2)
        | AppTy f1 a1 <- t1
        , AppTy f2 a2 <- t2 = do
            s1 <- matchSub s f1 f2
            matchSub s1 a1 a2
        | TermAppTy f1 a1 <- t1
        , TermAppTy f2 a2 <- t2
        , f1 == f2 =
            matchSub s a1 a2
        | otherwise = Nothing
      where
        t1 = coreFullView t1Raw
        t2 = coreFullView t2Raw

{- | Complete a template 'Subst.Subst', verifying that every bound template
variable is concrete and well-kinded.
-}
completeConcreteSubst :: VarSet -> [TyVar] -> Subst.Subst -> Maybe Subst.Subst
completeConcreteSubst unusedVisDepTvs tvs subst0 = go subst0 tvs
  where
    allTvSet = mkVarSet tvs

    go subst [] = Just subst
    go subst (tv : rest) =
        case Subst.lookupTyVar subst tv of
            Just choice ->
                let expK = Subst.substTy subst (tyVarKind tv)
                    leaksUnbound =
                        any
                            (\v -> v `elemVarSet` allTvSet && not (v `elemVarSet` unusedVisDepTvs))
                            (tyCoVarsOfTypeList choice)
                 in if (expK `tcEqType` typeKind choice) && not leaksUnbound
                        then go (Subst.extendTvSubstAndInScope subst tv choice) rest
                        else Nothing
            Nothing
                | tv `elemVarSet` unusedVisDepTvs ->
                    let k' = Subst.substTy subst (tyVarKind tv)
                        tv' = mkTyVar (getName tv) k'
                     in go (Subst.extendTvSubstAndInScope subst tv (mkTyVarTy tv')) rest
                | otherwise -> Nothing

-- | Reified source term for a type-level value index: @(termDoc, isAtom, canonType)@.
data ReifiedTerm = ReifiedTerm
    { rtDoc :: !SDoc
    , rtIsAtom :: !Bool
    , rtType :: !Type
    , rtIsStrictSubterm :: !Bool
    }

{- | Reify a type-level value argument (runtime 'TermVarTy', promoted 'DataCon'
application, 'SourceTable' call, or 'TermAppTy') into a well-scoped term expression.
-}
reifyValueArg :: ScopeEnv -> Int -> Maybe Type -> Type -> Maybe ReifiedTerm
reifyValueArg env fuel mbExpDom ty0
    | fuel < 0 = Nothing
    | TermVarTy v <- ty = do
        v' <- resolveLocalId v
        let vTy = TermVarTy v'
        guard (matchesDom vTy)
        pure
            ReifiedTerm
                { rtDoc = pprSourceTermId env v'
                , rtIsAtom = True
                , rtType = vTy
                , rtIsStrictSubterm = v' `elemVarSet` seStrictSubterms env
                }
    | Just (tc, args) <- splitTyConApp_maybe ty
    , Just dc <- isPromotedDataCon_maybe tc = do
        let dcNm = dataConName dc
        guard (dcNm `elemNameSet` seInScopeNames env)
        let visArgs = filterOutInvisibleTypes tc args
        if null visArgs
            then do
                guard (matchesDom ty)
                pure
                    ReifiedTerm
                        { rtDoc = pprPrefixOcc dcNm
                        , rtIsAtom = True
                        , rtType = ty
                        , rtIsStrictSubterm = False
                        }
            else do
                guard (fuel > 0)
                subTerms <- traverse (reifyValueArg env (fuel - 1) Nothing) visArgs
                guard (matchesDom ty)
                let doc = pprPrefixOcc dcNm <+> sep (map pprArg subTerms)
                pure
                    ReifiedTerm
                        { rtDoc = doc
                        , rtIsAtom = False
                        , rtType = ty
                        , rtIsStrictSubterm = False
                        }
    | Just (tc, args) <- splitTyConApp_maybe ty
    , Just rawOcc <- sourceTableTermOcc (nameOccName (tyConName tc))
    , isNothing (stripPrefix "#guard:" (occNameString rawOcc)) = do
        guard (rawOcc `elemOccSet` seInScopeValOccs env)
        let visArgs = filterOutInvisibleTypes tc args
        if null visArgs
            then do
                guard (matchesDom ty)
                pure
                    ReifiedTerm
                        { rtDoc = pprPrefixOcc rawOcc
                        , rtIsAtom = True
                        , rtType = ty
                        , rtIsStrictSubterm = False
                        }
            else do
                guard (fuel > 0)
                subTerms <- traverse (reifyValueArg env (fuel - 1) Nothing) visArgs
                -- Prevent unreduced self-calls inside index arguments.
                guard (not (rawOcc `elemOccSet` seSelfOccs env) || any rtIsStrictSubterm subTerms)
                guard (matchesDom ty)
                let doc = pprPrefixOcc rawOcc <+> sep (map pprArg subTerms)
                pure
                    ReifiedTerm
                        { rtDoc = doc
                        , rtIsAtom = False
                        , rtType = ty
                        , rtIsStrictSubterm = False
                        }
    | TermAppTy fnId argTy <- ty = do
        guard (fuel > 0)
        fn' <- resolveLocalId fnId
        subTerm <- reifyValueArg env (fuel - 1) Nothing argTy
        let rebuilt = TermAppTy fn' (rtType subTerm)
        guard (matchesDom rebuilt)
        pure
            ReifiedTerm
                { rtDoc = pprSourceTermId env fn' <+> pprArg subTerm
                , rtIsAtom = False
                , rtType = rebuilt
                , rtIsStrictSubterm = False
                }
    | otherwise = Nothing
  where
    ty = coreFullView ty0

    pprArg :: ReifiedTerm -> SDoc
    pprArg rt
        | rtIsAtom rt = rtDoc rt
        | otherwise = parens (rtDoc rt)

    matchesDom :: Type -> Bool
    matchesDom candTy =
        case mbExpDom of
            Nothing -> True
            Just dom -> typeKind candTy `tcEqType` dom

    resolveLocalId :: Id -> Maybe Id
    resolveLocalId v
        | Just v' <- lookupVarEnv (seLocalById env) v
        , checkDomId v' =
            Just v'
        | Just v' <- lookupOccEnv (seLocalByOcc env) (getOccName v)
        , checkDomId v' =
            Just v'
        | Just srcNm <- sourceTermOcc env v
        , Just v' <- lookupOccEnv (seLocalByOcc env) (nameOccName srcNm)
        , checkDomId v' =
            Just v'
        | otherwise = Nothing

    checkDomId :: Id -> Bool
    checkDomId v' =
        case mbExpDom of
            Nothing -> varType v' `tcEqType` varType v'
            Just dom -> varType v' `tcEqType` dom

{- | Extract all candidate congruence spines @(fType, fDoc, (subLhs, subRhs))@
when normalized @lhs@ and @rhs@ share a constructor, source-table prefix, or
local function spine differing in the final argument.
-}
splitCongSpines :: ScopeEnv -> Type -> Type -> [(Type, SDoc, (Type, Type))]
splitCongSpines env lhs0 rhs0
    | lhs `tcEqType` rhs = []
    | Just (tc1, as1) <- splitTyConApp_maybe lhs
    , Just (tc2, as2) <- splitTyConApp_maybe rhs
    , tc1 == tc2
    , u : revP1 <- reverse as1
    , v : revP2 <- reverse as2
    , revP1 `equalLength` revP2
    , and (zipWith tcEqType revP1 revP2)
    , not (u `tcEqType` v) =
        let prefixTys = reverse revP1
            fTy = mkTyConApp tc1 prefixTys
         in if
                | Just dc <- isPromotedDataCon_maybe tc1
                , let dcNm = dataConName dc
                , dcNm `elemNameSet` seInScopeNames env
                , let visPrefix = filterOutInvisibleTypes tc1 prefixTys
                , Just argTerms <- traverse (reifyValueArg env 2 Nothing) visPrefix ->
                    let doc =
                            case argTerms of
                                [] -> pprPrefixOcc dcNm
                                ts -> parens (pprPrefixOcc dcNm <+> sep (map pprArgTerm ts))
                     in [(fTy, doc, (u, v))]
                | Just rawOcc <- sourceTableTermOcc (nameOccName (tyConName tc1))
                , isNothing (stripPrefix "#guard:" (occNameString rawOcc))
                , rawOcc `elemOccSet` seInScopeValOccs env
                , let visPrefix = filterOutInvisibleTypes tc1 prefixTys
                , Just argTerms <- traverse (reifyValueArg env 2 Nothing) visPrefix ->
                    let doc =
                            case argTerms of
                                [] -> pprPrefixOcc rawOcc
                                ts -> parens (pprPrefixOcc rawOcc <+> sep (map pprArgTerm ts))
                     in [(fTy, doc, (u, v))]
                | otherwise -> []
    | TermAppTy f1 u <- lhs
    , TermAppTy f2 v <- rhs
    , f1 == f2
    , not (u `tcEqType` v)
    , Just fnRt <- reifyValueArg env 1 Nothing (TermVarTy f1) =
        [(rtType fnRt, pprArgTerm fnRt, (u, v))]
    | otherwise = []
  where
    lhs = coreFullView lhs0
    rhs = coreFullView rhs0

    pprArgTerm :: ReifiedTerm -> SDoc
    pprArgTerm rt
        | rtIsAtom rt = rtDoc rt
        | otherwise = parens (rtDoc rt)

-- ---------------------------------------------------------------------------
-- Subgoal Refinement Synthesis (Congruence & Transitivity)
-- ---------------------------------------------------------------------------

-- | Synthesized 1-hole subgoal refinement before formatting.
data SubgoalSpec = SubgoalSpec
    { ssKey :: !String
    , ssHoleFit :: !HoleFit
    , ssPrefixWithHole :: !(SDoc -> Bool -> SDoc)
    , ssSubgoalTy :: !TcType
    }

-- | Synthesize 1-hole congruence and transitivity subgoal refinements for @goalTy@.
synthesizeSubgoalFits ::
    SearchConfig ->
    (HoleFitCandidate -> TcM (Maybe CandInfo)) ->
    TcRef Int ->
    ScopeEnv ->
    HoleFitDispConfig ->
    TcType ->
    [HoleFitCandidate] ->
    TcM [HoleFit]
synthesizeSubgoalFits cfg lookupCand budgetRef env hfdc goalTy cands = do
    congSpecs <-
        if scCongruence cfg
            then findCongSubgoals lookupCand budgetRef env hfdc goalTy cands
            else pure []
    transSpecs <-
        if scTransitivity cfg
            then findTransSubgoals lookupCand budgetRef env hfdc goalTy cands
            else pure []
    pure (map ssHoleFit (congSpecs ++ transSpecs))

{- | Discover 1-subgoal congruence refinements for Required-type-argument or
visible-@foreach@ congruence combinators in scope.
-}
findCongSubgoals ::
    (HoleFitCandidate -> TcM (Maybe CandInfo)) ->
    TcRef Int ->
    ScopeEnv ->
    HoleFitDispConfig ->
    TcType ->
    [HoleFitCandidate] ->
    TcM [SubgoalSpec]
findCongSubgoals lookupCand budgetRef env hfdc goalTy cands
    | Just (_, lhs, rhs) <- splitEqGoalLike goalTy
    , spines@(_ : _) <- splitCongSpines env lhs rhs =
        fmap concat $
            mapM
                (\(fTy, fDoc, _) -> goSpine fTy fDoc [] cands)
                spines
    | otherwise = pure []
  where
    goSpine :: Type -> SDoc -> [SubgoalSpec] -> [HoleFitCandidate] -> TcM [SubgoalSpec]
    goSpine _ _ acc [] = pure (reverse acc)
    goSpine fTy fDoc acc (cand : rest)
        | length acc >= 4 = pure (reverse acc)
        | otherwise =
            tryTcDiscardingErrs (goSpine fTy fDoc acc rest) $ do
                mbInfo <- lookupCongCombinator lookupCand cand
                case mbInfo of
                    Nothing -> goSpine fTy fDoc acc rest
                    Just (nm, candTy, allTvs, reqTv, theta, argTy, resTy)
                        | depResHead resTy /= depResHead goalTy ->
                            goSpine fTy fDoc acc rest
                        | otherwise -> do
                            let sInit = Subst.extendTvSubst Subst.emptySubst reqTv fTy
                            case matchDepResult allTvs resTy goalTy of
                                Nothing -> goSpine fTy fDoc acc rest
                                Just sMatch -> do
                                    let sMerged =
                                            foldl
                                                ( \s tv ->
                                                    case Subst.lookupTyVar sMatch tv of
                                                        Just t -> Subst.extendTvSubstAndInScope s tv t
                                                        Nothing -> s
                                                )
                                                sInit
                                                allTvs
                                    case completeConcreteSubst emptyVarSet allTvs sMerged of
                                        Nothing -> goSpine fTy fDoc acc rest
                                        Just fullS -> do
                                            let choices = [Subst.substTy fullS (mkTyVarTy tv) | tv <- allTvs]
                                            scoped <- checkRuntimeScope choices
                                            if not scoped
                                                then goSpine fTy fDoc acc rest
                                                else do
                                                    let instRes =
                                                            mkPhiTy
                                                                (map (Subst.substTy fullS) theta)
                                                                (Subst.substTy fullS resTy)
                                                        rawSubTy = Subst.substTy fullS argTy
                                                    ok <- checkSoundFit budgetRef env False goalTy instRes
                                                    if not ok
                                                        then goSpine fTy fDoc acc rest
                                                        else do
                                                            subTy <- normalizeGoalTy (seCtLoc env) rawSubTy
                                                            dispSub <- prepareDisplayType env subTy
                                                            dispCand <- prepareDisplayType env candTy
                                                            let prefixDoc = pprPrefixOcc nm <+> fDoc
                                                                holeDoc
                                                                    | showMatches hfdc = parens (text "_" <+> dcolon <+> ppr dispSub)
                                                                    | otherwise = text "_"
                                                                callDoc = prefixDoc <+> holeDoc
                                                                whereDoc =
                                                                    ppWhen (showType hfdc) $
                                                                        nest 2 (text "where" <+> pprPrefixOcc nm <+> dcolon <+> ppr dispCand)
                                                                provDoc =
                                                                    ppWhen (showProv hfdc) $
                                                                        nest 2 (pprCandProvenance cand)
                                                                rDoc = callDoc $$ whereDoc $$ provDoc
                                                                mkComplete subDoc isAtom =
                                                                    prefixDoc <+> if isAtom then subDoc else parens subDoc
                                                                spec =
                                                                    SubgoalSpec
                                                                        { ssKey = normalizeWhitespace (showSDocUnsafe callDoc)
                                                                        , ssHoleFit = RawHoleFit rDoc
                                                                        , ssPrefixWithHole = mkComplete
                                                                        , ssSubgoalTy = subTy
                                                                        }
                                                            goSpine fTy fDoc (spec : acc) rest

{- | Parse a candidate type for a congruence combinator taking a visible
function parameter (@forall f ->@ or @foreach f ->@) and one proof subgoal.
-}
lookupCongCombinator ::
    (HoleFitCandidate -> TcM (Maybe CandInfo)) ->
    HoleFitCandidate ->
    TcM (Maybe (Name, Type, [TyVar], TyVar, [PredType], Type, Type))
lookupCongCombinator lookupCand cand = do
    mb <- lookupCand cand
    case mb of
        Nothing -> pure Nothing
        Just (nm, _, ty0) -> do
            let (invis1B, ty1) = tcSplitForAllInvisTyVars ty0
                invis1 = map snd invis1B
            case coreFullView ty1 of
                ForAllTy _ (Bndr reqTv Required) ty2 -> do
                    let (invis2B, ty3) = tcSplitForAllInvisTyVars ty2
                        invis2 = map snd invis2B
                        (theta, ty4) = tcSplitPhiTy ty3
                    case coreFullView ty4 of
                        FunTy{ft_af = af, ft_arg = argTy, ft_res = resTy}
                            | isVisibleFunArg af && isTauTy resTy ->
                                pure (Just (nm, ty0, invis1 ++ [reqTv] ++ invis2, reqTv, theta, argTy, resTy))
                        _ -> pure Nothing
                DepFunTy DepFunVisible fnBndr ty2 -> do
                    tvNm <- newSysName (mkTyVarOccFS (occNameFS (getOccName fnBndr)))
                    let reqTv = mkTyVar tvNm (varType fnBndr)
                        pairs = [(TermVarTy fnBndr, reqTv)]
                    case abstractNativeIndices pairs ty2 of
                        Nothing -> pure Nothing
                        Just ty2Abs -> do
                            let (invis2B, ty3) = tcSplitForAllInvisTyVars ty2Abs
                                invis2 = map snd invis2B
                                (theta, ty4) = tcSplitPhiTy ty3
                            case coreFullView ty4 of
                                FunTy{ft_af = af, ft_arg = argTy, ft_res = resTy}
                                    | isVisibleFunArg af && isTauTy resTy ->
                                        pure (Just (nm, ty0, invis1 ++ [reqTv] ++ invis2, reqTv, theta, argTy, resTy))
                                _ -> pure Nothing
                _ -> pure Nothing

-- | Direction of a binary transitivity combinator's two arguments.
data TransOrder
    = LeftThenRight
    | RightThenLeft
    deriving (Eq, Show)

{- | Discover 1-lemma transitivity subgoal refinements (rewriting either @lhs@
to @mid@ or @mid@ to @rhs@).
-}
findTransSubgoals ::
    (HoleFitCandidate -> TcM (Maybe CandInfo)) ->
    TcRef Int ->
    ScopeEnv ->
    HoleFitDispConfig ->
    TcType ->
    [HoleFitCandidate] ->
    TcM [SubgoalSpec]
findTransSubgoals lookupCand budgetRef env hfdc goalTy cands
    | Just (eqTc, lhs, rhs) <- splitEqGoalLike goalTy
    , not (lhs `tcEqType` rhs) = do
        mbTrans <- findTransCombinator lookupCand eqTc goalTy cands
        case mbTrans of
            Nothing -> pure []
            Just (transNm, transCand, transTy, order, mkRel) ->
                goLemmas eqTc lhs rhs transNm transCand transTy order mkRel [] cands
    | otherwise = pure []
  where
    goLemmas _ _ _ _ _ _ _ _ acc [] = pure (reverse acc)
    goLemmas eqTc lhs rhs transNm transCand transTy order mkRel acc (cand : rest)
        | length acc >= 4 = pure (reverse acc)
        | otherwise =
            tryTcDiscardingErrs
                (goLemmas eqTc lhs rhs transNm transCand transTy order mkRel acc rest)
                $ do
                    mb <- lookupCand cand
                    case mb of
                        Just (lemNm, isDc, lemTy)
                            | not isDc -> do
                                lhsHits <- tryRewriteLemma True eqTc lhs rhs mkRel lemNm lemTy
                                rhsHits <- tryRewriteLemma False eqTc lhs rhs mkRel lemNm lemTy
                                newSpecs <-
                                    mapM
                                        (mkTransSpec transNm transCand transTy order)
                                        (take 2 (lhsHits ++ rhsHits))
                                goLemmas eqTc lhs rhs transNm transCand transTy order mkRel (reverse newSpecs ++ acc) rest
                        _ ->
                            goLemmas eqTc lhs rhs transNm transCand transTy order mkRel acc rest

    mkTransSpec ::
        Name ->
        HoleFitCandidate ->
        Type ->
        TransOrder ->
        (Bool, SDoc, Bool, TcType) ->
        TcM SubgoalSpec
    mkTransSpec transNm transCand transTy order (isLeftRewrite, lemDoc, lemIsAtom, subTy) = do
        dispSub <- prepareDisplayType env subTy
        dispTrans <- prepareDisplayType env transTy
        let pLem = if lemIsAtom then lemDoc else parens lemDoc
            holeDoc
                | showMatches hfdc = parens (text "_" <+> dcolon <+> ppr dispSub)
                | otherwise = text "_"
            lemIsFirstArg =
                case (order, isLeftRewrite) of
                    (LeftThenRight, True) -> True
                    (LeftThenRight, False) -> False
                    (RightThenLeft, True) -> False
                    (RightThenLeft, False) -> True
            callDoc
                | lemIsFirstArg = pprPrefixOcc transNm <+> pLem <+> holeDoc
                | otherwise = pprPrefixOcc transNm <+> holeDoc <+> pLem
            whereDoc =
                ppWhen (showType hfdc) $
                    nest 2 (text "where" <+> pprPrefixOcc transNm <+> dcolon <+> ppr dispTrans)
            provDoc =
                ppWhen (showProv hfdc) $
                    nest 2 (pprCandProvenance transCand)
            rDoc = callDoc $$ whereDoc $$ provDoc
            mkComplete subDoc subIsAtom =
                let pSub = if subIsAtom then subDoc else parens subDoc
                 in if lemIsFirstArg
                        then pprPrefixOcc transNm <+> pLem <+> pSub
                        else pprPrefixOcc transNm <+> pSub <+> pLem
        pure
            SubgoalSpec
                { ssKey = normalizeWhitespace (showSDocUnsafe callDoc)
                , ssHoleFit = RawHoleFit rDoc
                , ssPrefixWithHole = mkComplete
                , ssSubgoalTy = subTy
                }

    -- Match a value-indexed or local equality lemma against either @lhs@
    -- (@isLeft == True@, producing @mid ~ rhs@) or @rhs@ (@isLeft == False@,
    -- producing @lhs ~ mid@).
    tryRewriteLemma ::
        Bool ->
        TyCon ->
        Type ->
        Type ->
        (Type -> Type -> Type) ->
        Name ->
        Type ->
        TcM [(Bool, SDoc, Bool, TcType)]
    tryRewriteLemma isLeft eqTc lhs rhs mkRel lemNm lemTy = do
        mbP <- peelValueLemma lemTy
        case mbP of
            Nothing -> pure []
            Just (allTvs, valParams, lemTheta, lemResAbs)
                | Just (lemTc, lemLhsTmpl, lemRhsTmpl) <- splitBinaryRelLike lemResAbs
                , lemTc == eqTc -> do
                    let (matchTmpl, targetSide, otherTmpl) =
                            if isLeft
                                then (lemLhsTmpl, lhs, lemRhsTmpl)
                                else (lemRhsTmpl, rhs, lemLhsTmpl)
                        isBareTemplateVar =
                            case coreFullView matchTmpl of
                                TyVarTy tv -> tv `elem` allTvs
                                _ -> False
                    if isBareTemplateVar
                        then pure []
                        else case matchEndpointTemplate allTvs matchTmpl targetSide of
                            Nothing -> pure []
                            Just sMatch ->
                                case resolveValueParams env sMatch valParams of
                                    Nothing -> pure []
                                    Just (sWithArgs, reifiedArgs)
                                        | isSelfName env lemNm
                                        , not (any rtIsStrictSubterm reifiedArgs) ->
                                            pure []
                                        | otherwise ->
                                            case completeConcreteSubst emptyVarSet allTvs sWithArgs of
                                                Nothing -> pure []
                                                Just fullS -> do
                                                    let choices = [Subst.substTy fullS (mkTyVarTy tv) | tv <- allTvs]
                                                    scoped <- checkRuntimeScope choices
                                                    if not scoped
                                                        then pure []
                                                        else do
                                                            let midRaw = Subst.substTy fullS otherTmpl
                                                            mid <- normalizeGoalTy (seCtLoc env) midRaw
                                                            if mid `tcEqType` lhs || mid `tcEqType` rhs
                                                                then pure []
                                                                else do
                                                                    let instLemTy =
                                                                            mkPhiTy
                                                                                (map (Subst.substTy fullS) lemTheta)
                                                                                (Subst.substTy fullS lemResAbs)
                                                                        expLemTy =
                                                                            if isLeft
                                                                                then mkRel lhs mid
                                                                                else mkRel mid rhs
                                                                        subGoalTy =
                                                                            if isLeft
                                                                                then mkRel mid rhs
                                                                                else mkRel lhs mid
                                                                    ok <- checkSoundFit budgetRef env False expLemTy instLemTy
                                                                    if not ok
                                                                        then pure []
                                                                        else do
                                                                            let (lemDoc, isAtom) = renderCall lemNm reifiedArgs
                                                                            pure [(isLeft, lemDoc, isAtom, subGoalTy)]
                | otherwise -> pure []

-- | Discover an in-scope binary transitivity combinator for @eqTc@.
findTransCombinator ::
    (HoleFitCandidate -> TcM (Maybe CandInfo)) ->
    TyCon ->
    TcType ->
    [HoleFitCandidate] ->
    TcM (Maybe (Name, HoleFitCandidate, Type, TransOrder, Type -> Type -> Type))
findTransCombinator _ _ _ [] = pure Nothing
findTransCombinator lookupCand eqTc goalTy (cand : rest) =
    tryTcDiscardingErrs (findTransCombinator lookupCand eqTc goalTy rest) $ do
        mb <- lookupCand cand
        case mb >>= parseTrans of
            Just info -> pure (Just info)
            Nothing -> findTransCombinator lookupCand eqTc goalTy rest
  where
    parseTrans (nm, False, ty0) = do
        let (invisB, ty1) = tcSplitForAllInvisTyVars ty0
            invisTvs = map snd invisB
            (theta, ty2) = tcSplitPhiTy ty1
        guard (null theta)
        FunTy{ft_af = af1, ft_arg = arg1Ty, ft_res = ty3} <- pure (coreFullView ty2)
        guard (isVisibleFunArg af1)
        FunTy{ft_af = af2, ft_arg = arg2Ty, ft_res = resTy} <- pure (coreFullView ty3)
        guard (isVisibleFunArg af2 && isTauTy resTy)
        (tcR, TyVarTy aTv, TyVarTy cTv) <- splitBinaryRelLike resTy
        (tc1, TyVarTy x1, TyVarTy y1) <- splitBinaryRelLike arg1Ty
        (tc2, TyVarTy x2, TyVarTy y2) <- splitBinaryRelLike arg2Ty
        guard (tcR == eqTc && tc1 == eqTc && tc2 == eqTc)
        guard (aTv /= cTv)
        order <-
            if
                | x1 == aTv && y1 == x2 && y2 == cTv && y1 /= aTv && y1 /= cTv ->
                    Just LeftThenRight
                | x2 == aTv && y2 == x1 && y1 == cTv && y2 /= aTv && y2 /= cTv ->
                    Just RightThenLeft
                | otherwise -> Nothing
        sBase <- matchDepResult invisTvs resTy goalTy
        let mkRel l r =
                let s =
                        Subst.extendTvSubstAndInScope
                            (Subst.extendTvSubstAndInScope sBase aTv l)
                            cTv
                            r
                 in Subst.substTy s resTy
        pure (nm, cand, ty0, order, mkRel)
    parseTrans _ = Nothing

-- ---------------------------------------------------------------------------
-- Bounded Backward-Chaining Complete Proof Search
-- ---------------------------------------------------------------------------

-- | Synthesized complete (@0@-subgoal) proof candidate with cost metrics.
data SynthProof = SynthProof
    { spDoc :: !SDoc
    , spIsAtom :: !Bool
    , spDepth :: !Int
    , spSize :: !Int
    }

-- | Visible parameter in a general backward-chaining proof rule telescope.
data RuleParam
    = RuleValDep !TyVar !Type
    | RuleProofSub !Type

-- | Synthesize complete (@0@-subgoal) proofs up to 'scDepth' for @goalTy@.
synthesizeCompleteFits ::
    SearchConfig ->
    (HoleFitCandidate -> TcM (Maybe CandInfo)) ->
    TcRef Int ->
    ScopeEnv ->
    HoleFitDispConfig ->
    TcType ->
    [HoleFitCandidate] ->
    TcM [HoleFit]
synthesizeCompleteFits cfg lookupCand budgetRef env hfdc goalTy cands = do
    proofs <- solveGoal (scDepth cfg) True 0 goalTy
    dispGoal <- prepareDisplayType env goalTy
    let sorted = sortOn (\p -> (spDepth p, spSize p)) proofs
        formatFit p
            | showType hfdc = RawHoleFit (hang (spDoc p) 2 (dcolon <+> ppr dispGoal))
            | otherwise = RawHoleFit (spDoc p)
    pure (map formatFit sorted)
  where
    -- Solve @subGoal@ with expression depth budget @remDepth@.
    -- Depth 0 admits nullary constructors and local bindings.
    -- Depth 1 admits saturated value-indexed calls and depth-1 combinator applications.
    -- Depth >= 2 recursively chains introduction, symmetry, congruence, and
    -- transitivity steps.
    solveGoal :: Int -> Bool -> Int -> TcType -> TcM [SynthProof]
    solveGoal remDepth allowTransBridge callDepth rawSubGoal
        | remDepth < 0 || callDepth > 6 = pure []
        | otherwise = do
            subGoal <- normalizeGoalTy (seCtLoc env) rawSubGoal
            leafHits <- solveAtoms subGoal
            if remDepth == 0
                then pure leafHits
                else do
                    valLemmaHits <- solveValueLemmas subGoal
                    congHits <-
                        if scCongruence cfg
                            then solveCongStep (remDepth - 1) (callDepth + 1) subGoal
                            else pure []
                    transHits <-
                        if scTransitivity cfg && remDepth >= 2 && allowTransBridge
                            then solveTransStep remDepth (callDepth + 1) subGoal
                            else pure []
                    ruleHits <- solveProofRules (remDepth - 1) (callDepth + 1) subGoal
                    pure (leafHits ++ valLemmaHits ++ congHits ++ ruleHits ++ transHits)

    -- Depth-0 atoms: local bindings and nullary GADT constructors.
    solveAtoms :: TcType -> TcM [SynthProof]
    solveAtoms subGoal = do
        lclHits <-
            fmap catMaybes $
                mapM
                    ( \v ->
                        if isSelfName env (idName v) && not (v `elemVarSet` seStrictSubterms env)
                            then pure Nothing
                            else do
                                let vTy = idType v
                                if isJust (depResHead vTy) && isJust (depResHead subGoal) && depResHead vTy /= depResHead subGoal
                                    then pure Nothing
                                    else do
                                        ok <-
                                            if vTy `tcEqType` subGoal
                                                then pure True
                                                else checkSoundFit budgetRef env False subGoal vTy
                                        pure $
                                            if ok
                                                then
                                                    Just
                                                        SynthProof
                                                            { spDoc = pprSourceTermId env v
                                                            , spIsAtom = True
                                                            , spDepth = 0
                                                            , spSize = 1
                                                            }
                                                else Nothing
                    )
                    (seAutoLocals env)
        conHits <-
            case splitTyConApp_maybe (coreFullView subGoal) of
                Just (gtc, _)
                    | isAlgTyCon gtc ->
                        fmap catMaybes $
                            mapM
                                ( \dc ->
                                    let dcNm = dataConName dc
                                     in if not (dcNm `elemNameSet` seInScopeNames env)
                                            || not (null (dataConOrigArgTys dc))
                                            then pure Nothing
                                            else do
                                                ok <- checkSoundFit budgetRef env True subGoal (dataConWrapperType dc)
                                                pure $
                                                    if ok
                                                        then
                                                            Just
                                                                SynthProof
                                                                    { spDoc = pprPrefixOcc dcNm
                                                                    , spIsAtom = True
                                                                    , spDepth = 0
                                                                    , spSize = 1
                                                                    }
                                                        else Nothing
                                )
                                (take 6 (tyConDataCons gtc))
                _ -> pure []
        pure (lclHits ++ conHits)

    -- Depth-1 saturated value-indexed calls (`plusZero m`, `leRefl n`, `eq Z`).
    solveValueLemmas :: TcType -> TcM [SynthProof]
    solveValueLemmas subGoal
        | not (isTauTy subGoal) = pure []
        | Nothing <- depResHead subGoal = pure []
        | otherwise = goVal [] cands
      where
        goVal acc [] = pure (reverse acc)
        goVal acc (cand : rest)
            | length acc >= 4 = pure (reverse acc)
            | otherwise =
                tryTcDiscardingErrs (goVal acc rest) $ do
                    mb <- lookupCand cand
                    case mb of
                        Just (fnNm, isDc, candTy) -> do
                            mbP <- peelValueLemma candTy
                            case mbP of
                                Just (allTvs, valParams@(_ : _), theta, resAbs)
                                    | depResHead resAbs == depResHead subGoal ->
                                        case matchDepResult allTvs resAbs subGoal of
                                            Nothing -> goVal acc rest
                                            Just sMatch ->
                                                case resolveValueParams env sMatch valParams of
                                                    Nothing -> goVal acc rest
                                                    Just (sWithArgs, reifiedArgs)
                                                        | isSelfName env fnNm
                                                        , not (any rtIsStrictSubterm reifiedArgs) ->
                                                            goVal acc rest
                                                        | otherwise -> do
                                                            let unusedDeps =
                                                                    mkVarSet
                                                                        [ tv
                                                                        | (tv, _) <- valParams
                                                                        , isNothing (Subst.lookupTyVar sMatch tv)
                                                                        ]
                                                            case completeConcreteSubst unusedDeps allTvs sWithArgs of
                                                                Nothing -> goVal acc rest
                                                                Just fullS -> do
                                                                    let choices = [Subst.substTy fullS (mkTyVarTy tv) | tv <- allTvs]
                                                                    scoped <- checkRuntimeScope choices
                                                                    if not scoped
                                                                        then goVal acc rest
                                                                        else do
                                                                            let instTy =
                                                                                    mkPhiTy
                                                                                        (map (Subst.substTy fullS) theta)
                                                                                        (Subst.substTy fullS resAbs)
                                                                            ok <- checkSoundFit budgetRef env isDc subGoal instTy
                                                                            if ok
                                                                                then do
                                                                                    let (doc, isAtom) = renderCall fnNm reifiedArgs
                                                                                        prf =
                                                                                            SynthProof
                                                                                                { spDoc = doc
                                                                                                , spIsAtom = isAtom
                                                                                                , spDepth = 1
                                                                                                , spSize = 1 + length reifiedArgs
                                                                                                }
                                                                                    goVal (prf : acc) rest
                                                                                else goVal acc rest
                                _ -> goVal acc rest
                        Nothing -> goVal acc rest

    -- Congruence step (`cong Succ <subproof>`, `cong (plus m) <subproof>`).
    solveCongStep :: Int -> Int -> TcType -> TcM [SynthProof]
    solveCongStep childDepth nextCall subGoal = do
        hfdcDummy <- getHoleFitDispConfig
        specs <- findCongSubgoals lookupCand budgetRef env hfdcDummy subGoal cands
        fmap concat $
            mapM
                ( \spec -> do
                    subProofs <- solveGoal childDepth True nextCall (ssSubgoalTy spec)
                    pure
                        [ SynthProof
                            { spDoc = ssPrefixWithHole spec (spDoc sp) (spIsAtom sp)
                            , spIsAtom = False
                            , spDepth = 1 + spDepth sp
                            , spSize = 2 + spSize sp
                            }
                        | sp <- take 2 subProofs
                        ]
                )
                (take 3 specs)

    -- General 1..2-proof-subgoal rules (`sym`, `SleS`, `congSucc`, custom GADT
    -- constructors, and mixed `foreach` + proof-subgoal combinators).
    solveProofRules :: Int -> Int -> TcType -> TcM [SynthProof]
    solveProofRules childDepth nextCall subGoal
        | not (isTauTy subGoal) = pure []
        | Nothing <- depResHead subGoal = pure []
        | otherwise = goRules [] cands
      where
        goRules acc [] = pure (reverse acc)
        goRules acc (cand : rest)
            | length acc >= 4 = pure (reverse acc)
            | otherwise =
                tryTcDiscardingErrs (goRules acc rest) $ do
                    mb <- lookupCand cand
                    case mb of
                        Just (fnNm, isDc, candTy) -> do
                            mbRule <- peelProofRule candTy
                            case mbRule of
                                Just (allTvs, params, theta, resAbs)
                                    | depResHead resAbs == depResHead subGoal -> do
                                        hits <- instantiateRule fnNm isDc allTvs params theta resAbs
                                        goRules (reverse hits ++ acc) rest
                                _ -> goRules acc rest
                        Nothing -> goRules acc rest

        instantiateRule ::
            Name ->
            Bool ->
            [TyVar] ->
            [RuleParam] ->
            [PredType] ->
            Type ->
            TcM [SynthProof]
        instantiateRule fnNm isDc allTvs params theta resAbs =
            case matchDepResult allTvs resAbs subGoal of
                Nothing -> pure []
                Just sMatch -> do
                    let valDeps = [(tv, dom) | RuleValDep tv dom <- params]
                    case resolveValueParams env sMatch valDeps of
                        Nothing -> pure []
                        Just (sWithArgs, reifiedVals) -> do
                            let unusedDeps =
                                    mkVarSet
                                        [ tv
                                        | (tv, _) <- valDeps
                                        , isNothing (Subst.lookupTyVar sMatch tv)
                                        ]
                            case completeConcreteSubst unusedDeps allTvs sWithArgs of
                                Nothing -> pure []
                                Just fullS -> do
                                    let choices = [Subst.substTy fullS (mkTyVarTy tv) | tv <- allTvs]
                                    scoped <- checkRuntimeScope choices
                                    if not scoped
                                        then pure []
                                        else do
                                            let isSelf = isSelfName env fnNm
                                                hasValSubterm = any rtIsStrictSubterm reifiedVals
                                            if isSelf && not hasValSubterm && isEmptyVarSetSimple (seStrictSubterms env)
                                                then pure []
                                                else do
                                                    let instRes =
                                                            mkPhiTy
                                                                (map (Subst.substTy fullS) theta)
                                                                (Subst.substTy fullS resAbs)
                                                    ok <- checkSoundFit budgetRef env isDc subGoal instRes
                                                    if not ok
                                                        then pure []
                                                        else do
                                                            argChoices <- buildRuleArgs fullS params
                                                            pure
                                                                [ SynthProof
                                                                    { spDoc = pprPrefixOcc fnNm <+> sep argDocs
                                                                    , spIsAtom = False
                                                                    , spDepth = 1 + maxSubDepth
                                                                    , spSize = 1 + totalSize
                                                                    }
                                                                | (argDocs, maxSubDepth, totalSize, usedSubterm) <- take 2 argChoices
                                                                , not isSelf || hasValSubterm || usedSubterm
                                                                ]

        buildRuleArgs :: Subst.Subst -> [RuleParam] -> TcM [([SDoc], Int, Int, Bool)]
        buildRuleArgs _ [] = pure [([], 0, 0, False)]
        buildRuleArgs fullS (p : ps) =
            case p of
                RuleValDep tv dom -> do
                    let rawArg = Subst.substTy fullS (mkTyVarTy tv)
                        instDom = Subst.substTy fullS dom
                    case reifyValueArg env 2 (Just instDom) rawArg of
                        Nothing -> pure []
                        Just rt -> do
                            restArgs <- buildRuleArgs fullS ps
                            let doc = if rtIsAtom rt then rtDoc rt else parens (rtDoc rt)
                            pure
                                [ (doc : ds, md, 1 + sz, usedSub || rtIsStrictSubterm rt)
                                | (ds, md, sz, usedSub) <- restArgs
                                ]
                RuleProofSub subTmpl -> do
                    let subTy = Subst.substTy fullS subTmpl
                    normSubTy <- normalizeGoalTy (seCtLoc env) subTy
                    if normSubTy `tcEqType` subGoal
                        then pure []
                        else do
                            subProofs <- solveGoal childDepth True nextCall normSubTy
                            if null subProofs
                                then pure []
                                else do
                                    restArgs <- buildRuleArgs fullS ps
                                    pure
                                        [ (doc : ds, max (spDepth sp) md, spSize sp + sz, usedSub || subUsesStrictSubterm sp)
                                        | sp <- take 2 subProofs
                                        , let doc = if spIsAtom sp then spDoc sp else parens (spDoc sp)
                                        , (ds, md, sz, usedSub) <- restArgs
                                        ]

    subUsesStrictSubterm :: SynthProof -> Bool
    subUsesStrictSubterm sp =
        let txt = showSDocUnsafe (spDoc sp)
            subStrs =
                [ showSDocUnsafe (pprSourceTermId env v)
                | v <- seAutoLocals env
                , v `elemVarSet` seStrictSubterms env
                ]
         in spIsAtom sp && any (== txt) subStrs

    -- 1-lemma transitivity rewrite bridge (`trans (plusSuc m k) (cong Succ (plusComm m k))`).
    solveTransStep :: Int -> Int -> TcType -> TcM [SynthProof]
    solveTransStep remDepth nextCall subGoal = do
        hfdcDummy <- getHoleFitDispConfig
        specs <- findTransSubgoals lookupCand budgetRef env hfdcDummy subGoal cands
        let contDepth
                | remDepth <= 2 = 2
                | otherwise = remDepth - 1
            nextAllowBridge = remDepth >= 3
        fmap concat $
            mapM
                ( \spec -> do
                    subProofs <- solveGoal contDepth nextAllowBridge nextCall (ssSubgoalTy spec)
                    pure
                        [ SynthProof
                            { spDoc = ssPrefixWithHole spec (spDoc sp) (spIsAtom sp)
                            , spIsAtom = False
                            , spDepth = max 2 (1 + spDepth sp)
                            , spSize = 3 + spSize sp
                            }
                        | sp <- take 2 subProofs
                        ]
                )
                (take 3 specs)

isEmptyVarSetSimple :: VarSet -> Bool
isEmptyVarSetSimple vs = vs == emptyVarSet

{- | Peel a candidate with @0..4@ visible @foreach@ value parameters and zero
visible proof-subgoal arrows into template 'TyVar's.
-}
peelValueLemma :: Type -> TcM (Maybe ([TyVar], [(TyVar, Type)], [PredType], Type))
peelValueLemma = go [] [] [] []
  where
    go invisTvs valParams theta depPairs ty
        | Just ty' <- coreView ty =
            go invisTvs valParams theta depPairs ty'
        | ForAllTy _ (Bndr tv vis) body <- ty
        , isInvisibleForAllTyFlag vis =
            case abstractNativeIndices depPairs (tyVarKind tv) of
                Nothing -> pure Nothing
                Just k' ->
                    let tv' = if k' `eqType` tyVarKind tv then tv else setTyVarKind tv k'
                        body' = if k' `eqType` tyVarKind tv then body else Subst.substTyWith [tv] [mkTyVarTy tv'] body
                     in go (invisTvs ++ [tv']) valParams theta depPairs body'
        | DepFunTy DepFunInvisible bndr body <- ty =
            case abstractNativeIndices depPairs (varType bndr) of
                Nothing -> pure Nothing
                Just dom' -> do
                    nm <- newSysName (mkTyVarOccFS (occNameFS (getOccName bndr)))
                    let tv = mkTyVar nm dom'
                    go (invisTvs ++ [tv]) valParams theta (depPairs ++ [(TermVarTy bndr, tv)]) body
        | FunTy{ft_af = af, ft_arg = predTy, ft_res = body} <- ty
        , not (isVisibleFunArg af) =
            case abstractNativeIndices depPairs predTy of
                Nothing -> pure Nothing
                Just pred' -> go invisTvs valParams (theta ++ [pred']) depPairs body
        | DepFunTy DepFunVisible bndr body <- ty
        , length valParams < 4 =
            case abstractNativeIndices depPairs (varType bndr) of
                Nothing -> pure Nothing
                Just dom' -> do
                    nm <- newSysName (mkTyVarOccFS (occNameFS (getOccName bndr)))
                    let tv = mkTyVar nm dom'
                    go invisTvs (valParams ++ [(tv, dom')]) theta (depPairs ++ [(TermVarTy bndr, tv)]) body
        | isTauTy ty
        , isJust (depResHead ty) =
            case abstractNativeIndices depPairs ty of
                Nothing -> pure Nothing
                Just res' ->
                    pure (Just (invisTvs ++ map fst valParams, valParams, theta, res'))
        | otherwise = pure Nothing

{- | Peel a backward-chaining proof rule with @1..2@ visible proof subgoals and
@0..3@ interleaved @foreach@ value parameters, rejecting degenerate bare-tyvar
combinators such as 'id', '($)', and 'const'.
-}
peelProofRule :: Type -> TcM (Maybe ([TyVar], [RuleParam], [PredType], Type))
peelProofRule = go [] [] (0 :: Int) (0 :: Int) [] []
  where
    go invisTvs params nSub nVal theta depPairs ty
        | Just ty' <- coreView ty =
            go invisTvs params nSub nVal theta depPairs ty'
        | ForAllTy _ (Bndr tv vis) body <- ty
        , isInvisibleForAllTyFlag vis =
            case abstractNativeIndices depPairs (tyVarKind tv) of
                Nothing -> pure Nothing
                Just k' ->
                    let tv' = if k' `eqType` tyVarKind tv then tv else setTyVarKind tv k'
                        body' = if k' `eqType` tyVarKind tv then body else Subst.substTyWith [tv] [mkTyVarTy tv'] body
                     in go (invisTvs ++ [tv']) params nSub nVal theta depPairs body'
        | DepFunTy DepFunInvisible bndr body <- ty =
            case abstractNativeIndices depPairs (varType bndr) of
                Nothing -> pure Nothing
                Just dom' -> do
                    nm <- newSysName (mkTyVarOccFS (occNameFS (getOccName bndr)))
                    let tv = mkTyVar nm dom'
                    go (invisTvs ++ [tv]) params nSub nVal theta (depPairs ++ [(TermVarTy bndr, tv)]) body
        | FunTy{ft_af = af, ft_arg = predTy, ft_res = body} <- ty
        , not (isVisibleFunArg af) =
            case abstractNativeIndices depPairs predTy of
                Nothing -> pure Nothing
                Just pred' -> go invisTvs params nSub nVal (theta ++ [pred']) depPairs body
        | DepFunTy DepFunVisible bndr body <- ty
        , nVal < 3 =
            case abstractNativeIndices depPairs (varType bndr) of
                Nothing -> pure Nothing
                Just dom' -> do
                    nm <- newSysName (mkTyVarOccFS (occNameFS (getOccName bndr)))
                    let tv = mkTyVar nm dom'
                    go
                        (invisTvs ++ [tv])
                        (params ++ [RuleValDep tv dom'])
                        nSub
                        (nVal + 1)
                        theta
                        (depPairs ++ [(TermVarTy bndr, tv)])
                        body
        | FunTy{ft_af = af, ft_arg = argTy, ft_res = body} <- ty
        , isVisibleFunArg af
        , nSub < (2 :: Int) =
            case abstractNativeIndices depPairs argTy of
                Nothing -> pure Nothing
                Just arg'
                    | isJust (depResHead arg') ->
                        go invisTvs (params ++ [RuleProofSub arg']) (nSub + 1) nVal theta depPairs body
                    | otherwise -> pure Nothing
        | nSub >= 1
        , isTauTy ty
        , isJust (depResHead ty) =
            case abstractNativeIndices depPairs ty of
                Nothing -> pure Nothing
                Just res' -> pure (Just (invisTvs, params, theta, res'))
        | otherwise = pure Nothing

-- | Reify all visible @foreach@ value parameters from a partial result 'Subst.Subst'.
resolveValueParams ::
    ScopeEnv ->
    Subst.Subst ->
    [(TyVar, Type)] ->
    Maybe (Subst.Subst, [ReifiedTerm])
resolveValueParams env = go []
  where
    go acc subst [] = Just (subst, reverse acc)
    go acc subst ((tv, dom) : rest) = do
        let instDom = Subst.substTy subst dom
        choice <-
            case Subst.lookupTyVar subst tv of
                Just c -> Just c
                Nothing -> pickDefaultInScope env instDom
        rt <- reifyValueArg env 2 (Just instDom) choice
        let subst' = Subst.extendTvSubstAndInScope subst tv (rtType rt)
        go (rt : acc) subst' rest

    -- If a foreach binder does not occur in the result type, use a local binding
    -- of matching domain when one exists.
    pickDefaultInScope :: ScopeEnv -> Type -> Maybe Type
    pickDefaultInScope sc dom =
        case [TermVarTy v | v <- seAutoLocals sc, varType v `tcEqType` dom] of
            (t : _) -> Just t
            [] -> Nothing

-- | Render a function or local variable applied to zero or more 'ReifiedTerm' arguments.
renderCall :: Name -> [ReifiedTerm] -> (SDoc, Bool)
renderCall nm [] = (pprPrefixOcc nm, True)
renderCall nm args =
    ( pprPrefixOcc nm
        <+> sep [if rtIsAtom a then rtDoc a else parens (rtDoc a) | a <- args]
    , False
    )

-- | Format candidate provenance in the same layout as GHC's built-in hole fits.
pprCandProvenance :: HoleFitCandidate -> SDoc
pprCandProvenance (GreHFCand gre) = parens (pprNameProvenance gre)
pprCandProvenance (NameHFCand nm) = parens (text "bound at" <+> ppr (getSrcLoc nm))
pprCandProvenance (IdHFCand i) = parens (text "bound at" <+> ppr (getSrcLoc i))

{- | Prepend at most @maxInject@ synthesized fits in front of @existingFits@,
deduplicating against both earlier synthesized fits and @existingFits@.
-}
prependDedupFits :: Int -> [HoleFit] -> [HoleFit] -> [HoleFit]
prependDedupFits maxInject synthFits existingFits =
    take maxInject uniqueSynth ++ existingFits
  where
    existingKeys = Set.fromList (map holeFitHeadKey existingFits)
    uniqueSynth = dedup existingKeys synthFits

    dedup _ [] = []
    dedup seen (hf : hfs)
        | key `Set.member` seen = dedup seen hfs
        | otherwise = hf : dedup (Set.insert key seen) hfs
      where
        key = holeFitHeadKey hf

-- | Extract a normalized head-expression key from a 'HoleFit' for deduplication.
holeFitHeadKey :: HoleFit -> String
holeFitHeadKey (TcHoleFit hf)
    | null (hfMatches hf) =
        normalizeWhitespace (showSDocUnsafe (pprPrefixOcc (hfName hf)))
    | otherwise =
        normalizeWhitespace
            ( showSDocUnsafe
                ( ppr (hfName hf)
                    <+> sep [parens (text "_" <+> dcolon <+> ppr m) | m <- hfMatches hf]
                )
            )
holeFitHeadKey (RawHoleFit doc) =
    let exprLines = takeWhile (not . isMetaLine) (lines (showSDocUnsafe doc))
        joined = normalizeWhitespace (unwords exprLines)
     in normalizeWhitespace (stripTopLevelMeta (0 :: Int) joined)
  where
    isMetaLine :: String -> Bool
    isMetaLine ln =
        let stripped = dropWhile isSpace ln
         in "where " `isPrefixOf` stripped
                || ":: " `isPrefixOf` stripped
                || "(imported " `isPrefixOf` stripped
                || "(defined " `isPrefixOf` stripped
                || "(bound " `isPrefixOf` stripped

    stripTopLevelMeta :: Int -> String -> String
    stripTopLevelMeta _ "" = ""
    stripTopLevelMeta depth s
        | depth == 0 && (" where " `isPrefixOf` s || " :: " `isPrefixOf` s) = ""
        | otherwise =
            case s of
                '(' : cs -> '(' : stripTopLevelMeta (depth + 1) cs
                ')' : cs -> ')' : stripTopLevelMeta (max 0 (depth - 1)) cs
                c : cs -> c : stripTopLevelMeta depth cs

-- | Collapse runs of whitespace into single spaces and trim leading/trailing space.
normalizeWhitespace :: String -> String
normalizeWhitespace = unwords . words
