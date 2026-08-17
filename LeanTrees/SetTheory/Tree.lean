import Mathlib.Order.RelClasses
import Mathlib.Order.RelIso.Set
import Mathlib.Order.InitialSeg
import Mathlib.Order.Bounds.Basic
import Mathlib.Data.Sum.Order

universe u v

/--
A forest is a poset in which every down set is a WellOrder
-/
class IsForest (α : Type u) extends PartialOrder α where
  toWellFoundedLT : WellFoundedLT α
  downset_trichot : ∀ (x y a : α), x < a → y < a → x < y ∨ x = y ∨ x > y

attribute [instance] IsForest.toWellFoundedLT

/-- Build a `Std.Trichotomous` instance from the usual three-way disjunction.
(`Std.Trichotomous` states trichotomy negatively, as `¬ r a b → ¬ r b a → a = b`.) -/
theorem trichotomous_of_or {α : Sort*} {r : α → α → Prop}
    (h : ∀ a b, r a b ∨ a = b ∨ r b a) : Std.Trichotomous r :=
  ⟨fun a b hab hba => ((h a b).resolve_left hab).resolve_right hba⟩

instance (α : Type u) [IsForest α] (a : α) :
    Std.Trichotomous (α := { x // x < a }) (. < .) :=
  trichotomous_of_or fun x y => by
    rcases IsForest.downset_trichot x.1 y.1 a x.2 y.2 with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr h)

instance {α : Type u} [IsForest α] (a : α) :
    IsWellOrder { x // x < a } (. < .) where

instance {α : Type u} [DecidableEq α] [IsForest α] (a : α) :
    Std.Trichotomous (α := { x // x ≤ a }) (. < .) :=
  trichotomous_of_or <| by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    by_cases h : x = a <;> by_cases h' : y = a
    · subst h; subst h'; exact Or.inr (Or.inl rfl)
    · subst h
      exact Or.inr (Or.inr (lt_of_le_of_ne hy fun hEq => h' (congrArg Subtype.val hEq)))
    · subst h'
      exact Or.inl (lt_of_le_of_ne hx fun hEq => h (congrArg Subtype.val hEq))
    · rcases IsForest.downset_trichot x y a (lt_of_le_of_ne hx h)
          (lt_of_le_of_ne hy h') with H | H | H
      · exact Or.inl H
      · exact Or.inr (Or.inl (Subtype.ext H))
      · exact Or.inr (Or.inr H)

instance {α : Type u} [DecidableEq α] [IsForest α] (a : α) :
    IsWellOrder { x // x ≤ a } (. < .) where

/--
A tree is a forest equipped with a minimum element.
-/
class IsTree (α : Type u) extends IsForest α, OrderBot α

instance {α} [LinearOrder α] [OrderBot α] [WellFoundedLT α] : IsTree α where
  toWellFoundedLT := inferInstance
  downset_trichot x y _ _ _ := lt_trichotomy x y

instance {α : Type u} [IsForest α] : IsTree (WithBot α) where
  toWellFoundedLT := inferInstance
  downset_trichot := by
    intro x y a hx hy
    induction x using WithBot.recBotCoe with
    | bot =>
      induction y using WithBot.recBotCoe with
      | bot => exact Or.inr (Or.inl rfl)
      | coe y => exact Or.inl (WithBot.bot_lt_coe y)
    | coe x =>
      induction y using WithBot.recBotCoe with
      | bot => exact Or.inr (Or.inr (WithBot.bot_lt_coe x))
      | coe y =>
        induction a using WithBot.recBotCoe with
        | bot => exact absurd hx (WithBot.not_lt_bot _)
        | coe a =>
          rw [WithBot.coe_lt_coe] at hx hy
          rcases IsForest.downset_trichot x y a hx hy with H | H | H
          · exact Or.inl (WithBot.coe_lt_coe.mpr H)
          · exact Or.inr (Or.inl (congrArg _ H))
          · exact Or.inr (Or.inr (WithBot.coe_lt_coe.mpr H))

instance {α : Type u} {β : Type v} [IsForest α] [IsForest β]
    : IsForest (α ⊕ β) where
  -- should extract both of these to somewhere else
  toWellFoundedLT := by
    constructor; constructor; rintro (x | x)
    <;> (induction x using WellFounded.induction;
         exact IsForest.toWellFoundedLT.wf)
    <;> constructor
    <;> intro _ h <;> cases h
    <;> apply_assumption
    <;> assumption
  downset_trichot := by
    rintro s t (a | a) hs ht
    · cases hs with
      | inl hs =>
        cases ht with
        | inl ht =>
          rcases IsForest.downset_trichot _ _ a hs ht with H | H | H
          · exact Or.inl (Sum.inl_lt_inl_iff.mpr H)
          · exact Or.inr (Or.inl (congrArg _ H))
          · exact Or.inr (Or.inr (Sum.inl_lt_inl_iff.mpr H))
    · cases hs with
      | inr hs =>
        cases ht with
        | inr ht =>
          rcases IsForest.downset_trichot _ _ a hs ht with H | H | H
          · exact Or.inl (Sum.inr_lt_inr_iff.mpr H)
          · exact Or.inr (Or.inl (congrArg _ H))
          · exact Or.inr (Or.inr (Sum.inr_lt_inr_iff.mpr H))
