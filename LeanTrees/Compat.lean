/-
Copyright (c) 2023 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
import Mathlib.Control.Applicative
import Mathlib.Control.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Sublists
import Mathlib.Data.Option.Basic

/-!
# Compatibility shims

When this development lived inside mathlib, these declarations were added
directly to `Mathlib.Control.Applicative`, `Mathlib.Data.List.Basic` and
`Mathlib.Data.Option.Basic`. Extracted into a standalone project they live
here instead, so that upstream mathlib is used unmodified.
-/

section Delab
open Lean PrettyPrinter.Delaborator SubExpr

/-- Delaborate `Seq.seq f (fun _ => x)` back to `f <*> x`. -/
@[delab app.Seq.seq]
def delabSeq : Delab := whenPPOption Lean.getPPNotation do
  let #[_, _, _, _, _, thunk] := (← getExpr).getAppArgs | failure
  guard <| thunk.isLambda && !thunk.bindingBody!.hasLooseBVar 0
  let a ← withAppFn <| withAppArg delab
  let b ← withAppArg <| withBindingBody `_ delab
  `($a <*> $b)

/-- Delaborate `SeqLeft.seqLeft f (fun _ => x)` back to `f <* x`. -/
@[delab app.SeqLeft.seqLeft]
def delabSeqLeft : Delab := whenPPOption Lean.getPPNotation do
  let #[_, _, _, _, _, thunk] := (← getExpr).getAppArgs | failure
  guard <| thunk.isLambda && !thunk.bindingBody!.hasLooseBVar 0
  let a ← withAppFn <| withAppArg delab
  let b ← withAppArg <| withBindingBody `_ delab
  `($a <* $b)

/-- Delaborate `SeqRight.seqRight f (fun _ => x)` back to `f *> x`. -/
@[delab app.SeqRight.seqRight]
def delabSeqRight : Delab := whenPPOption Lean.getPPNotation do
  let #[_, _, _, _, _, thunk] := (← getExpr).getAppArgs | failure
  guard <| thunk.isLambda && !thunk.bindingBody!.hasLooseBVar 0
  let a ← withAppFn <| withAppArg delab
  let b ← withAppArg <| withBindingBody `_ delab
  `($a *> $b)

end Delab

namespace List
variable {α β : Type*}

theorem doubleton_eq' [DecidableEq α] {x y : α} :
    ({x, y} : List α) = if x = y then [x] else [x, y] := by
  show List.insert x [y] = _
  by_cases h : x = y
  · subst h; rw [List.insert_of_mem (mem_singleton_self x), if_pos rfl]
  · rw [List.insert_of_not_mem (by simpa using h), if_neg h]

theorem cons_sublist_cons_iff' {xs ys : List α} {x y : α} :
    x :: xs <+ y :: ys ↔ (x = y ∧ xs <+ ys) ∨ x :: xs <+ ys := by
  constructor
  · intro H
    cases H with
    | cons _ h => exact Or.inr h
    | cons_cons _ h => exact Or.inl ⟨rfl, h⟩
  · rintro (⟨rfl, h⟩ | h)
    · exact h.cons_cons _
    · exact h.cons _

theorem pair_sublist_append {a b : α} {xs ys : List α} :
    [a, b] <+ xs ++ ys ↔ [a, b] <+ xs ∨ (a ∈ xs ∧ b ∈ ys) ∨ [a, b] <+ ys := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [cons_sublist_cons_iff', cons_append, mem_append, mem_cons,
               and_or_left, singleton_sublist, ih, or_assoc, or_and_right]
    exact or_congr_right or_left_comm

theorem Sublist.map_inj (f : α → β) (h : Function.Injective f) {xs ys : List α} :
    List.map f xs <+ List.map f ys ↔ xs <+ ys := by
  refine Iff.intro ?_ (Sublist.map f)
  induction ys generalizing xs with
  | nil => simp only [map_nil, sublist_nil, map_eq_nil_iff, imp_self]
  | cons y ys ih =>
    intro H
    cases xs with
    | nil => apply nil_sublist
    | cons x xs =>
      simp only [map_cons, cons_sublist_cons_iff', h.eq_iff] at H ⊢
      refine Or.imp (And.imp_right ?_) ?_ H
      · apply ih
      · rw [← map_cons]; apply ih

end List

namespace Option
variable {α β : Type*}

-- `Option.isSome_map` and `Option.get_map` are now in core; only this helper
-- (used for the `get` side condition) still needs to be provided.
theorem isSome_map' (f : α → β) {o : Option α} : o.isSome → (o.map f).isSome :=
  fun h => isSome_map.trans h

end Option
