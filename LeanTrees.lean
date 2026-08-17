/-
# LeanTrees

Binary/rose tree developments extracted from a 2023–24 mathlib fork branch
(`new-new-tree-stuff` on Shamrock-Frost/mathlib4), rebuilt as a standalone
project against current mathlib.

All modules build against current mathlib. Some proofs inherited from the original
branch are still `admit`ted; see README.md.
-/

import LeanTrees.Compat
import LeanTrees.Tactic.MonadReassoc
import LeanTrees.Control.Reverse
import LeanTrees.Control.Monad.MonadLift
import LeanTrees.Control.Monad.MonadState
import LeanTrees.SetTheory.Tree
import LeanTrees.Data.BitVec.Compat
import LeanTrees.Data.Tree.BinAddr
import LeanTrees.Data.Tree.BinTree
import LeanTrees.Data.Tree.ShouldBeMoved
import LeanTrees.Data.Tree.RoseTree
