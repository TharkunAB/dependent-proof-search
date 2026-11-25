# dependent-proof-search

`dependent-proof-search` provides a GHC hole-fit plugin (`Dependent.Plugin.ProofSearch`) for bounded backward-chaining proof synthesis and subgoal refinement in Dependent Haskell (`-XDependentTypes`).

## Overview

GHC's built-in hole-fit finder checks individual in-scope identifiers and general `-frefinement-level-hole-fits=N` wrappers. `Dependent.Plugin.ProofSearch` layers type-directed proof search on top of GHC's `HoleFitPlugin` interface without hardcoding library module names or specific equality types:

1. **Complete backward-chaining synthesis**: Synthesizes multi-step proof terms up to a configurable depth (`depth=0..5`) from local bindings, nullary and indexed GADT constructors, saturated `foreach` lemmas, congruence combinators, symmetry combinators, and transitivity rewrite steps.
2. **Congruence subgoal refinements**: Suggests 1-subgoal refinements such as `cong Succ (_ :: lhs :~: rhs)` and `cong (plus m) (_ :: a :~: b)` when normalized equality endpoints share a promoted constructor, function prefix, or local function spine differing in the final argument.
3. **Transitivity subgoal refinements**: Suggests 1-lemma rewrite refinements `trans (lemma args...) (_ :: mid :~: rhs)` and `trans (_ :: lhs :~: mid) (lemma args...)` when an in-scope equality lemma rewrites the normalized left-hand side or right-hand side to a distinct intermediate term.
4. **Solver soundness and source binder names**: Normalizes open family redexes with `tcRewriteFamilyAxioms`, verifies every synthesized proof and subgoal refinement with GHC's constraint solver inside `withoutUnification`, and formats terms and subgoal types with unrenamed source binder names so suggested fits compile verbatim.

## Usage

Enable the plugin in a module:

```haskell
{-# LANGUAGE DependentTypes #-}
{-# OPTIONS_GHC -fplugin=Dependent.Plugin.ProofSearch #-}
```

To inspect 1-hole congruence and transitivity subgoal refinements alongside complete proofs, enable refinement hole fits:

```haskell
{-# LANGUAGE DependentTypes #-}
{-# OPTIONS_GHC -fplugin=Dependent.Plugin.ProofSearch -frefinement-level-hole-fits=1 #-}
```

Example proof holes:

```haskell
import Data.Type.Equality ((:~:) (Refl), sym, trans)
import GHC.Exts (Matchability)

data Nat = Zero | Succ Nat

plus :: Nat -> Nat -> Nat
plus Zero     n = n
plus (Succ m) n = Succ (plus m n)

cong :: forall {a} {b} {m :: Matchability}.
        forall (f :: a %m -> b) -> forall (x :: a) (y :: a).
        x :~: y -> f x :~: f y
cong _ Refl = Refl

plusZero :: foreach (m :: Nat) -> plus m Zero :~: m
plusZero Zero     = Refl
plusZero (Succ m) = cong Succ (plusZero m)

plusSuc :: foreach (m :: Nat) (n :: Nat) -> plus m (Succ n) :~: Succ (plus m n)
plusSuc Zero     _ = Refl
plusSuc (Succ m) n = cong Succ (plusSuc m n)

plusComm :: foreach (m :: Nat) (n :: Nat) -> plus m n :~: plus n m
plusComm m Zero     = _  -- suggests: plusZero m
plusComm m (Succ k) = _  -- suggests: trans (plusSuc m k) (cong Succ (plusComm m k))
                         -- and refinement: trans (plusSuc m k) (_ :: Succ (plus m k) :~: Succ (plus k m))

zeroLeft :: foreach (m :: Nat) -> plus Zero m :~: plus m Zero
zeroLeft m = _           -- suggests: sym (plusZero m)
```

## Plugin Options

Pass colon- or comma-separated options with `-fplugin-opt=Dependent.Plugin.ProofSearch:<option>`:

| Option | Default | Meaning |
| --- | --- | --- |
| `depth=N` | `2` | Maximum expression tree depth (`0..5`) for complete (`0`-subgoal) proof synthesis |
| `max-fits=N` | `8` | Maximum number of synthesized fits injected per hole pass |
| `max-candidates=N` | `64` | Solver candidate check budget per hole pass |
| `auto` / `no-auto` | `auto` | Enable or disable complete (`0`-hole) backward-chaining proof synthesis |
| `congruence` / `no-congruence` | `congruence` | Enable or disable congruence subgoal refinements and search steps |
| `transitivity` / `no-transitivity` | `transitivity` | Enable or disable 1-lemma transitivity subgoal refinements and search steps |
| `subgoals-in-valid` / `no-subgoals-in-valid` | `no-subgoals-in-valid` | Also emit 1-hole subgoal refinements in `Valid hole fits` when `-frefinement-level-hole-fits` is unset |
