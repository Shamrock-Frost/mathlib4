# LeanTrees

Binary and rose tree developments, extracted from a mathlib fork and rebuilt as a
standalone Lean 4 project against current mathlib.

```
lake exe cache get   # optional, but much faster than building mathlib
lake build
```

## Provenance

Everything here comes from the `new-new-tree-stuff` branch of
[Shamrock-Frost/mathlib4](https://github.com/Shamrock-Frost/mathlib4), last touched
on 2024-01-23 (`35b2112c9f`, whose one substantive commit is titled *"WIP refactoring
out non-tree code"*). At that point the branch was pinned to Lean `v4.5.0-rc1`. This
project targets `v4.34.0-rc1`, so roughly two years of mathlib and Lean core churn sit
between the original sources and what builds here.

The branch was genuine work-in-progress. It is preserved as such: proofs that were
unfinished in 2024 are still unfinished, marked `admit`, and listed below. Nothing was
weakened or deleted to make the build pass.

## Layout

| module | contents |
|---|---|
| `LeanTrees/Compat.lean` | small `List`/`Option` additions and the `<*>` / `<*` / `*>` delaborators, which the original patched directly into mathlib files |
| `LeanTrees/Tactic/MonadReassoc.lean` | the `@[reassocM]` attribute, generating `_assoc` continuation variants of monadic equations |
| `LeanTrees/Control/Reverse.lean` | `SeqOpposite`, reversing an applicative's control flow |
| `LeanTrees/Control/Monad/MonadLift.lean` | `LawfulMonadLift` instances for the standard transformers |
| `LeanTrees/Control/Monad/MonadState.lean` | additions to Batteries' lawful-state-monad API |
| `LeanTrees/SetTheory/Tree.lean` | `IsForest` / `IsTree` order classes |
| `LeanTrees/Data/BitVec/Compat.lean` | `BitVec` support for `BinAddr` (see below) |
| `LeanTrees/Data/Tree/ShouldBeMoved.lean` | general-purpose `List` / `Array` / `Option` lemmas the author staged for upstreaming |
| `LeanTrees/Data/Tree/BinAddr.lean` | paths from the root of a binary tree, as a length-indexed `BitVec` |
| `LeanTrees/Data/Tree/BinTree.lean` | binary trees with data at both nodes and leaves |
| `LeanTrees/Data/Tree/RoseTree.lean` | trees with arbitrary finite branching |

## What was left behind

The original branch also carried changes to mathlib proper that are not part of the
tree development and are not reproduced here:

* `Mathlib/Combinatorics/Catalan.lean` and `Mathlib/Tactic/CancelDenoms.lean` —
  refactors of existing mathlib files, only meaningful as a diff against mathlib.
* `Mathlib/Data/BitVec/Lemmas.lean` — a 1259-line `BitVec` and `Nat` bitwise
  development. Nearly all of it has since landed in Lean core, under the `getLsbD`
  spelling. In particular the branch's own `Nat.size'` is exactly core's `Nat.size`,
  with the same `size_le` characterization. `LeanTrees/Data/BitVec/Compat.lean`
  supplies only the genuine remainder: `BitVec.lsb` and `BitVec.dropLast`, the
  `concatRecOn` snoc-recursor, `HEq` forms of the `append` lemmas (core states them
  modulo a `BitVec.cast`, but `BinAddr.ext` needs to compare vectors of
  provably-but-not-definitionally equal widths), and two `Nat` shift facts.

## Deviations from the original

Three deliberate changes, beyond mechanical porting:

* **`MonadState.lean` was rebased onto Batteries' `LawfulMonadStateOf`.** The original
  defined its own class, stating the `get` laws as equations between closed
  computations; Batteries states them with a continuation baked in. The two
  axiomatizations are interderivable, and the bridge is preserved as
  `LawfulMonadStateOf.ofClosed`, which builds Batteries' class from the original's
  laws. `LawfulMonadState`, the `MonadState`-level mirror, was dropped — Batteries
  deliberately provides only the `MonadStateOf` level. `ofLift` (transfer along an
  arbitrary `LawfulMonadLift`) is a `def` rather than an `instance`: as a global
  instance over an arbitrary `MonadLift` it matches every monad pair.
* **`RoseTree.BinTree` was renamed to `AryTree.Bin`.** In the fork, `Data/Tree/RoseTree.lean`
  and `Data/Tree/BinTree.lean` were never imported together, so nobody noticed that
  both defined a root-level `BinTree`. Importing both here exposes the clash; the
  inductive `BinTree` keeps the name.
* **`BinTree.ofRBNode` was deleted.** Batteries moved its red-black tree into
  `Batteries/Recycling/`, a holding area for modules "deprecated due to obsolescence"
  that "will be moved to a separate repository once a suitable deprecation period has
  passed", recommending `Std.TreeMap` instead. `ofRBNode` was a three-line converter
  with no call sites, so dropping it removes the dependency entirely.

`ShouldBeMoved` still depends on `Batteries.Recycling.MonadSatisfying` for `SatisfiesM`.
That one is load-bearing and will need attention if Batteries follows through.

## Unfinished proofs

12 `admit`s across 9 declarations, all inherited from the 2024 branch. No new ones were
introduced during the port.

| module | declaration |
|---|---|
| `ShouldBeMoved` | `Std.Legacy.Range.forM_spec` |
| `ShouldBeMoved` | `Array.extractAlt_eq_extractAlt_upto_min` |
| `ShouldBeMoved` | `Array.extract_mem_extractAlt` |
| `ShouldBeMoved` | `Array.foldlIdx_eq_foldlIdx_toList` |
| `BinTree` | `shape_hasNodeAt` |
| `BinTree` | `shape_eq_iff` |
| `BinTree` | `getStateAt?_eq_getNodeAt?_labelWithState` |
| `RoseTree` | `maxValidPrefixLen_spec` |
| `RoseTree` | `contractEdge` |

`BinAddr`, and every module outside `Data/Tree`, are free of `admit`s.
