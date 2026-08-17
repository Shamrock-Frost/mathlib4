/-
Copyright (c) 2019 mathlib community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/

import Batteries.Data.DList.Basic
import Mathlib.Util.CompileInductive
import Mathlib.Data.FinEnum
import Mathlib.Control.Bitraversable.Instances
import Mathlib.Control.Fold
import Mathlib.Data.Finmap
import LeanTrees.Data.Tree.ShouldBeMoved

/-!
# Rose tree

A tree with an arbitrary (finite) number of children at each node,
storing (potentially) different types of data at the nodes and leaves.
-/

inductive RoseTree.{u, v} (N : Type u) (L : Type v) : Type (max u v)
  | leaf : L → RoseTree N L
  | branch : N → Array (RoseTree N L) → RoseTree N L
  deriving Repr

compile_inductive% RoseTree

namespace RoseTree

universe u₁ u₂ u₃ v₁ v₂ v₃ w₁ w₂ w₃
variable {N : Type u₁} {N' : Type u₂} {N'' : Type u₃}
         {L : Type v₁} {L' : Type v₂} {L'' : Type v₃}
         {ω : Type w₁}

def children : RoseTree N L → Array (RoseTree N L)
  | leaf _ => Array.empty
  | branch _ ts => ts

lemma leaf_inj_iff {x y : L} : @leaf N L x = @leaf N L y ↔ x = y :=
  iff_of_eq (leaf.injEq x y)

lemma branch_inj_iff {x} {ts : Array (RoseTree N L)} {y ts'} :
    branch x ts = branch y ts' ↔ x = y ∧ ts = ts' :=
  iff_of_eq (branch.injEq _ _ _ _)

lemma leaf_ne_branch {x : L} {y : N} {ts} : leaf x ≠ branch y ts := by simp

lemma branch_ne_leaf {y : N} {ts} {x : L} : branch y ts ≠ leaf x :=
  Ne.symm leaf_ne_branch

section getElim
variable {motive : RoseTree N L → Sort w₁}
         (leaf : (x : L) → motive (leaf x))
         (branch : (y : N) → (ts : Array (RoseTree N L))
                 → ((i : Fin ts.size) → motive ts[i]) → motive (branch y ts))

@[induction_eliminator, cases_eliminator]
def getElim : (t : RoseTree N L) → motive t
  | RoseTree.leaf x => leaf x
  | RoseTree.branch y ts => branch y ts (fun i => getElim ts[i])

lemma getElim_leaf {x} : getElim leaf branch (RoseTree.leaf x) = leaf x := by
  rw [getElim]
lemma getElim_branch {y ts} :
    getElim leaf branch (RoseTree.branch y ts)
    = branch y ts (fun i => getElim leaf branch ts[i]) :=
  by rw [getElim]

end getElim

instance [DecidableEq N] [DecidableEq L] : DecidableEq (RoseTree N L) := by
  intro t₁ t₂
  induction t₁ generalizing t₂ with
  | leaf x =>
    match t₂ with
    | leaf x' => exact decidable_of_iff (x = x') leaf_inj_iff.symm
    | branch _ _ => exact Decidable.isFalse leaf_ne_branch
  | branch y ts ih =>
    match t₂ with
    | leaf _ => exact Decidable.isFalse branch_ne_leaf
    | branch y' ts' =>
      -- putting the y = y' inside the ∃ h means we check ts.size = ts'.size,
      -- which is roughly O(1), before y = y' (arbitrarily expensive)
      refine decidable_of_iff (∃ h : ts.size = ts'.size, y = y' ∧
                                 ∀ i : Fin ts.size, ts[i] = ts'[i.cast h])
                              (Iff.trans ?_ branch_inj_iff.symm)
      refine Iff.trans exists_and_left (and_congr_right' ?_)
      refine ⟨?_, (. ▸ ⟨rfl, fun _ => rfl⟩)⟩
      rintro ⟨h, h'⟩
      exact Array.ext h (fun i hi _ => h' ⟨i, hi⟩)

-- it might make more sense to use `Subarray`,
-- but because `Subarray.forIn` is opaque we can't prove anything about it
abbrev Addr := Array ℕ

def bimap (f : N → N') (g : L → L') (t : RoseTree N L) : RoseTree N' L' := by
  induction t with
  | leaf x => exact leaf (g x)
  | branch y ts self => exact branch (f y) (Array.ofFn self)

@[simp] lemma bimap_leaf {f : N → N'} {g : L → L'} {x} :
    bimap f g (leaf x) = leaf (g x) := getElim_leaf _ _

@[simp] lemma bimap_branch {f : N → N'} {g : L → L'} {y ts} :
    bimap f g (branch y ts) = branch (f y) (ts.map (bimap f g)) :=
  Eq.trans (getElim_branch _ _) $ congrArg (branch (f y)) (Array.map_eq_ofFn ts _).symm

section getNodeAt?

def getNodeData : RoseTree N L → N ⊕ L
  | leaf x => Sum.inr x
  | branch y _ => Sum.inl y

def getSubtreeAt? (t : RoseTree N L) (a : Addr) : Option (RoseTree N L) :=
  a.foldlM (fun t i => t.children[i]?) t

@[reducible] def applyAt (f : RoseTree N L → ω) (p : Addr) (t : RoseTree N L) : Option ω :=
  Option.map f (getSubtreeAt? t p)

@[reducible] def getNodeAt? (t : RoseTree N L) (p : Addr) :=
  applyAt getNodeData p t

@[reducible] def getLeafAt? (t : RoseTree N L) (p : Addr) :=
  Option.bind (getNodeAt? t p) Sum.getRight?

@[reducible] def getInnerNodeAt? (t : RoseTree N L) (p : Addr) :=
  Option.bind (getNodeAt? t p) Sum.getLeft?

@[simp] lemma getSubtreeAt?_empty {t : RoseTree N L} :
    t.getSubtreeAt? Array.empty = some t :=
  Eq.trans Array.foldlM_toList.symm (List.foldlM_nil)

-- i would like this to be lower priority than getSubtreeAt?_empty
@[simp] lemma getSubtreeAt?_leaf {x a} :
    getSubtreeAt? (@leaf N L x) a = (Option.guard (fun _ => a.isEmpty) (leaf x)) :=
  eq_ite_iff'.mpr
    ⟨fun h => Eq.trans (congrArg _ (Array.isEmpty_iff.mp h)) getSubtreeAt?_empty,
    fun h => have h' := List.ne_nil_of_length_pos $ Nat.pos_of_ne_zero
                        $ of_decide_eq_false ((Bool.not_eq_true _).mp h)
             Eq.trans Array.foldlM_toList.symm
             $ Eq.trans (congrArg _ (List.cons_head!_tail h').symm)
             $ Eq.trans (List.foldlM_cons) (Option.bind_none _)⟩

@[simp] lemma getSubtreeAt?_singleton {t : RoseTree N L} {i : ℕ} :
    getSubtreeAt? t (Array.singleton i) = t.children[i]? :=
  Eq.trans Array.foldlM_toList.symm
  $ Eq.trans (congrArg (List.foldlM _ _ $ Array.toList .) (Array.singleton_def))
  $ Eq.trans (congrArg _ List.toList_toArray)
  $ Eq.trans (List.foldlM_cons)
  $ Eq.trans (congrArg _ (funext (fun _ => List.foldlM_nil))) $ Eq.trans (bind_pure _)
  $ match t with | leaf _ => rfl | branch _ _ => rfl

lemma getSubtreeAt?_append {t : RoseTree N L} {a₁ a₂ : Addr} :
    t.getSubtreeAt? (a₁ ++ a₂) = (getSubtreeAt? t a₁).bind (getSubtreeAt? . a₂) := by
  simp only [getSubtreeAt?, ← Array.foldlM_toList, Array.toList_append]
  exact List.foldlM_append

lemma getSubtreeAt?_cons {t : RoseTree N L} {i : ℕ} {a : Addr} :
    getSubtreeAt? t (Array.singleton i ++ a)
    = t.children[i]?.bind (getSubtreeAt? . a) :=
  Eq.trans getSubtreeAt?_append (congrArg (Option.bind . _) getSubtreeAt?_singleton)

@[simp] lemma getNodeAt?_empty {t : RoseTree N L} :
    t.getNodeAt? Array.empty = getNodeData t :=
  Eq.trans (congrArg (Option.map _) getSubtreeAt?_empty) (Option.map_some _ _)

@[simp] lemma getNodeAt?_leaf {x a} :
    getNodeAt? (@leaf N L x) a = (Option.guard (fun _ => a.isEmpty) $ Sum.inr x) :=
  Eq.trans (congrArg (Option.map _) getSubtreeAt?_leaf)
           (Option.map'_guard_const _ _ _)

@[simp] lemma getNodeAt?_singleton {t : RoseTree N L} {i : ℕ} :
    getNodeAt? t (Array.singleton i) = t.children[i]?.map getNodeData :=
  congrArg (Option.map _) getSubtreeAt?_singleton

lemma getNodeAt?_getSubtreeAt? (t : RoseTree N L) (p q : Addr) :
    (t.getSubtreeAt? p).bind (getNodeAt? . q) = t.getNodeAt? (p ++ q) :=
  Eq.symm $ Eq.trans (congrArg (Option.map _) getSubtreeAt?_append)
                     (Option.map_bind)

lemma getNodeAt?_cons {t : RoseTree N L} {i : ℕ} {a : Addr} :
    getNodeAt? t (Array.singleton i ++ a)
    = t.children[i]?.bind (getNodeAt? . a) :=
  Eq.trans (congrArg (Option.map _) getSubtreeAt?_cons) (Option.map_bind)

section predicates

variable (t : RoseTree N L) (p : Addr)

def hasNodeAt := ∃ n, n ∈ getNodeAt? t p
def hasLeafAt := ∃ b, Sum.inr b ∈ getNodeAt? t p
def hasInnerNodeAt := ∃ a, Sum.inl a ∈ getNodeAt? t p

lemma hasNodeAt_of_hasLeafAt : hasLeafAt t p → hasNodeAt t p
  | ⟨x, h⟩ => ⟨Sum.inr x, h⟩

lemma hasNodeAt_of_hasInnerNodeAt : hasInnerNodeAt t p → hasNodeAt t p
  | ⟨x, h⟩ => ⟨Sum.inl x, h⟩

lemma hasNodeAt_iff_getNodeAt?_isSome : hasNodeAt t p ↔ (getNodeAt? t p).isSome :=
  Option.isSome_iff_exists.symm

lemma hasNodeAt_iff_getSubtreeAt?_isSome : hasNodeAt t p ↔ (getSubtreeAt? t p).isSome :=
  Iff.trans (hasNodeAt_iff_getNodeAt?_isSome _ _) (Bool.eq_iff_iff.mp Option.isSome_map)

/-- `Option.isSome_bind` used to be stated in this form; it is now a `Bool` equation
phrased with `Option.any`. -/
private theorem isSome_bind_iff {α β} {x : Option α} {f : α → Option β} :
    (x.bind f).isSome ↔ ∃ a, a ∈ x ∧ (f a).isSome := by
  cases x <;> simp

lemma hasLeafAt_iff_getLeafNodeAt?_isSome :
    hasLeafAt t p ↔ (getLeafAt? t p).isSome :=
  Iff.symm
  $ Iff.trans isSome_bind_iff
  $ Iff.trans (exists_congr (fun _ =>
      Iff.trans (and_congr_right' Sum.isSome_getRight?_iff_isRight) and_comm))
    Sum.exists_isRight

lemma hasInnerNodeAt_iff_getInnerNodeAt?_isSome :
    hasInnerNodeAt t p ↔ (getInnerNodeAt? t p).isSome :=
  Iff.symm
  $ Iff.trans isSome_bind_iff
  $ Iff.trans (exists_congr (fun _ =>
      Iff.trans (and_congr_right' Sum.isSome_getLeft?_iff_isLeft) and_comm))
    Sum.exists_isLeft

def getSubtreeAt {t : RoseTree N L} {p} (h : hasNodeAt t p) : RoseTree N L :=
  Option.get (getSubtreeAt? t p)
  $ Iff.mp (hasNodeAt_iff_getSubtreeAt?_isSome _ _) h

def getNodeAt {t : RoseTree N L} {p} (h : hasNodeAt t p) : N ⊕ L :=
  Option.get (getNodeAt? t p)
  $ Iff.mp (hasNodeAt_iff_getNodeAt?_isSome _ _) h

def getLeafAt {t : RoseTree N L} {p} (h : hasLeafAt t p) : L :=
  Option.get (getLeafAt? t p)
  $ Iff.mp (hasLeafAt_iff_getLeafNodeAt?_isSome _ _) h

def getInnerNodeAt {t : RoseTree N L} {p} (h : hasInnerNodeAt t p) : N :=
  Option.get (getInnerNodeAt? t p)
  $ Iff.mp (hasInnerNodeAt_iff_getInnerNodeAt?_isSome _ _) h

instance : Decidable (hasNodeAt t p) :=
  decidable_of_bool _ (hasNodeAt_iff_getNodeAt?_isSome t p).symm
instance : Decidable (hasLeafAt t p) :=
  decidable_of_bool _ (hasLeafAt_iff_getLeafNodeAt?_isSome t p).symm
instance : Decidable (hasInnerNodeAt t p) :=
  decidable_of_bool _ (hasInnerNodeAt_iff_getInnerNodeAt?_isSome t p).symm

lemma hasNodeAt_empty {t : RoseTree N L} : hasNodeAt t Array.empty :=
  (hasNodeAt_iff_getSubtreeAt?_isSome _ _).mpr
  $ Eq.trans (congrArg _ getSubtreeAt?_empty) Option.isSome_some

lemma hasNodeAt_leaf {x p} : hasNodeAt (@leaf N L x) p ↔ p.isEmpty :=
  by rw [hasNodeAt_iff_getSubtreeAt?_isSome, getSubtreeAt?_leaf,
         Option.isSome_guard]

lemma hasNodeAt_push {t : RoseTree N L} {p i} :
    hasNodeAt t (p.push i)
    ↔ hasInnerNodeAt t p ∧ SatisfiesM (fun t => i < t.children.size)
                                      (getSubtreeAt? t p) := by
  simp only [hasNodeAt_iff_getSubtreeAt?_isSome, Array.push_eq_append_singleton,
             getSubtreeAt?_append, isSome_bind_iff, ← Array.singleton_def,
             getSubtreeAt?_singleton,
             Array.isSome_getElem?, hasInnerNodeAt_iff_getInnerNodeAt?_isSome,
             Option.mem_map, exists_exists_and_eq_and]
  conv_rhs =>
    simp only [Option.SatisfiesM_iff_forall_mem, ← forall_and,
               Option.exists_mem_iff_isSome_and_forall_mem, and_assoc]
    rw [← Option.exists_mem_iff_isSome_and_forall_mem]
  refine exists_congr (fun t => and_congr_right (fun ht => ?_))
  rw [Sum.isSome_getLeft?_iff_isLeft, iff_and_self]
  match t with
  | leaf _ => exact Not.elim (Nat.not_lt_zero _)
  | branch _ ts => intro; rfl

end predicates

-- there's probably a clever way to do this if we inductively prove
-- equality of Option (RoseTree N L), but Lean can't automatically prove that
-- `t.bind (fun x => x.children[i]?)` is below `t`
lemma getNodeAt?_faithful ⦃t₁ t₂ : RoseTree N L⦄
    (h : ∀ p, t₁.getNodeAt? p = t₂.getNodeAt? p) : t₁ = t₂ :=
  have h1 := Option.some.inj (h Array.empty)
  have h2 : t₁.children.size = t₂.children.size := by
    have h' i := Bool.eq_iff_iff.mp $ congrArg Option.isSome (h (Array.singleton i))
    simp only [getNodeAt?_singleton, Option.isSome_map, Array.isSome_getElem?] at h'
    exact eq_of_forall_lt_iff h'
  match t₁, t₂ with
  | leaf _, leaf _ => congrArg leaf (Sum.inr.inj h1)
  | branch _ ts₁, branch _ ts₂ =>
    congrArg₂ branch (Sum.inl.inj h1)
    $ Array.ext h2 $ fun i hi₁ hi₂ => getNodeAt?_faithful $ fun a =>
      have h' := Eq.trans getNodeAt?_cons.symm
                $ Eq.trans (h (Array.singleton i ++ a)) getNodeAt?_cons
      by simp only [children, Array.getElem?_eq_getElem, hi₁, hi₂,
                    Option.bind_some] at h'; exact h'

lemma children_bimap {f : N → N'} {g : L → L'} :
    ∀ (t : RoseTree N L), (t.bimap f g).children = t.children.map (.bimap f g)
  | leaf _ => by simp [children, Array.empty]
  | branch _ _ => congrArg children bimap_branch

lemma getSubtreeAt?_bimap {f : N → N'} {g : L → L'} (t : RoseTree N L) (p : Addr) :
    (t.bimap f g).getSubtreeAt? p = (t.getSubtreeAt? p).map (.bimap f g) := by
  simp only [getSubtreeAt?, ← Array.foldlM_toList, List.foldlM_eq_foldl]
  let C := fun x => Prod.fst x = Option.map (RoseTree.bimap f g) (Prod.snd x)
  refine @Eq.substr _ C _ _ (p.toList.prod_mk_foldl _ _ _ _) $
         p.toList.foldlRecOn _ (Option.map_some _ _).symm $
    fun
    | (none, none), _, _, _ => (Option.map_none _).symm
    | (some t₁, some t₂), H, i, _ =>
      Eq.trans (congrArg₂ (. >>= .) H rfl) (?_ : (t₂.bimap f g).children[i]? = _)
  exact Eq.trans (congrArg (.[i]?) (children_bimap t₂)) Array.getElem?_map

-- `getNodeAt?` is a natural transformation `RoseTree → Function.bicompr Option Sum`
lemma getNodeAt?_bimap {f : N → N'} {g : L → L'} (t : RoseTree N L) (p : Addr) :
    (t.bimap f g).getNodeAt? p = (t.getNodeAt? p).map (Sum.map f g) := by
  simp only [getNodeAt?, applyAt, getSubtreeAt?_bimap, Option.map_map]
  match getSubtreeAt? t p with
  | none => exact Eq.trans (Option.map_none _) (Option.map_none _).symm
  | some (leaf _) => simp only [Option.map_some, Function.comp_apply,
                                bimap_leaf, getNodeData, Sum.map_inr]
  | some (branch _ _) => simp only [Option.map_some, Function.comp_apply,
                                    bimap_branch, getNodeData, Sum.map_inl]

end getNodeAt?

section setSubtreeAt?

private def modifyMSubtreeAt.impl {m} [Monad m]
    (f : RoseTree N L → m (RoseTree N L)) (p : Addr)
    (i j : ℕ) (h : j ≤ p.size) (t : RoseTree N L) : m (RoseTree N L) :=
  if h' : i < j
  then match t with
       | leaf x => pure (leaf x)
       | branch y ts =>
          branch y <$> ts.modifyM p[i]
                                  (modifyMSubtreeAt.impl f p (i + 1) j h)
  else f t
termination_by j - i

def modifyMSubtreeAt {m} [Monad m] (f : RoseTree N L → m (RoseTree N L))
    (p : Addr) (t : RoseTree N L) : m (RoseTree N L) :=
  modifyMSubtreeAt.impl f p 0 p.size (le_refl _) t

private lemma modifyMSubtreeAt.impl_eq_modifyMSubtreeAt_extract
    (f : RoseTree N L → Option (RoseTree N L)) (p : Addr)
    (i j : ℕ) (h : j ≤ p.size) (t : RoseTree N L) :
    modifyMSubtreeAt.impl f p i j h t = modifyMSubtreeAt f (p.extract i j) t := by
  simp only [modifyMSubtreeAt, Array.size_extract, min_eq_left h]
  conv_lhs => rw [← Nat.add_zero i]
  generalize 0 = ℓ
  induction t generalizing ℓ with
  | leaf x => simp_rw [modifyMSubtreeAt.impl, lt_tsub_iff_left]
  | branch y ts ih =>
    simp_rw [modifyMSubtreeAt.impl, lt_tsub_iff_left]
    refine dite_congr rfl (fun h' => congrArg _ ?_) (fun _ => rfl)
    rw [Array.getElem_extract]
    simp only [Array.modifyM, Nat.add_assoc]
    refine dite_congr rfl (fun h'' => congrArg (. >>= _) ?_) (fun _ => rfl)
    exact ih ⟨_, h''⟩ (ℓ + 1)

def maxValidPrefixLen (t : RoseTree N L) (p : Addr) :=
  (p.foldlIdxM (fun i t j => t.children[j]?.getDM (Sum.inl i)) t).getLeft?.getD p.size

lemma maxValidPrefixLen_spec (t : RoseTree N L) (p : Addr) :
    maxValidPrefixLen t p
    = (p.findIdx? (fun i => ¬ t.hasNodeAt (p.extract 0 i))).getD p.size := by
  refine congrArg (Option.getD . p.size) ?_

  admit

-- lemma modifyMSubtreeAt_def {m} [Monad m] (f : RoseTree N L → m (RoseTree N L))
--     (p : Addr) (t : RoseTree N L) :
--     modifyMSubtreeAt f p t
--     = let cont := p.foldrM
--       cont.getD id  := _

-- def setSubtreeAt? (t : RoseTree N L) (p : Addr) (t' : RoseTree N L) := sorry

-- def transformAt? (f : RoseTree N L → Option (RoseTree N L)) (p : Addr)
--     (t : RoseTree N L) : Option (RoseTree N L) :=
--   transformAt?.impl f p 0 p.size (le_refl _) t

-- private lemma transformAt?.impl_getSubtreeAt?
--     (f : RoseTree N L → Option (RoseTree N L)) (p q : Addr)
--     (i j : ℕ) (h : j ≤ p.size) (t : RoseTree N L) :
--     (transformAt?.impl f p i j h t).bind (getSubtreeAt? . q)
--     = if p.toList <+: q.toList
--       then ((t.getSubtreeAt? p).bind f).bind (getSubtreeAt? . $ ⟨q.toList.drop p.size⟩)
--       else t.getSubtreeAt? q := by

--   admit

def contractEdge (t : RoseTree N L) (p : Addr)
    (f : N → L → N) (g : N → N → N) : Option (RoseTree N L) := by
  induction t with
  | leaf x => admit
  | branch y ts => admit

end setSubtreeAt?

end RoseTree

@[reducible] def AryTree.{u, v} (k : ℕ) (N : Type u) (L : Type v) :=
  { t : RoseTree N L // ∀ p (h : t.hasInnerNodeAt p),
    (t.getSubtreeAt (t.hasNodeAt_of_hasInnerNodeAt p h)).children.size = k }

/-- The binary case of `AryTree`. Renamed from `BinTree` during extraction: in the
original branch this file and `Data/Tree/BinTree.lean` were never imported together, so
the clash with the inductive `BinTree` there never surfaced. -/
def AryTree.Bin := AryTree 2
