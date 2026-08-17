import Batteries.Recycling.MonadSatisfying.Basic
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Control.Monad.Basic
import Mathlib.Control.Fold
import Mathlib.Data.Array.Defs
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Nat.Upto
import Mathlib.Data.List.DropRight
import Mathlib.Data.List.Fold
import Mathlib.Data.List.Indexes
import Mathlib.Data.Part
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Action.Opposite
import Mathlib.Algebra.Group.Action.Pi

@[reducible, always_inline, inline]
def ReaderM.run {ρ α} (x : ReaderM ρ α) (r : ρ) : α := ReaderT.run x r

@[reducible]
protected def ReaderM.mk {ρ α} (f : ρ → α) : ReaderM ρ α := ReaderT.mk f

example {γ : Type*} : γ → γ × γ := ReaderM.run $ joinM Prod.mk

@[reducible, always_inline, inline]
def StateM.run {σ α} (x : StateM σ α) (s : σ) : α × σ := StateT.run x s

@[reducible]
protected def StateM.mk {σ α} (f : σ → α × σ) : StateM σ α := StateT.mk f

lemma eq_ite_iff' {α} {P} [Decidable P] {a b c : α} :
    a = (if P then b else c) ↔ (P → a = b) ∧ (¬P → a = c) := by
  refine Iff.trans eq_comm (Iff.trans ite_eq_iff' (Iff.and ?_ ?_))
  <;> exact Iff.imp Iff.rfl eq_comm

lemma id_map''.{u, v} {F : Type u → Type v} {α : Type u}
    [Functor F] [LawfulFunctor F] : (Functor.map id : F α → F α) = id :=
  funext LawfulFunctor.id_map

theorem SatisfiesM.bind_congr {m α β} [Monad m] [LawfulMonad m] {p : α → Prop}
    {x : m α} (h1 : SatisfiesM p x) {f : α → m β} {g : α → m β}
    (h2 : ∀ (a : α), p a → f a = g a) :
    x >>= f = x >>= g := by
  obtain ⟨y, ⟨⟩⟩ := h1
  rw [seq_bind_eq, seq_bind_eq]
  exact _root_.bind_congr (Subtype.forall.mpr h2)

theorem SatisfiesM.map_congr {m α β} [Monad m] [LawfulMonad m] {p : α → Prop}
    {x : m α} (h1 : SatisfiesM p x) {f : α → β} {g : α → β}
    (h2 : ∀ (a : α), p a → f a = g a) : f <$> x = g <$> x := by
    simp only [map_eq_bind_pure_comp]
    exact h1.bind_congr (congrArg _ $ h2 . .)

lemma fish_eq_backfish' {m α β γ} [Monad m] :
    (fun (p : α → m β) (q : β → m γ) => p >=> q) = (fun p q => q <=< p) := rfl

lemma fish_eq_backfish {m α β γ} [Monad m] (p : α → m β) (q : β → m γ) :
    p >=> q = q <=< p := congrFun (congrFun fish_eq_backfish' p) q

lemma backfish_assoc {m α β γ δ} [Monad m] [LawfulMonad m] (p : γ → m δ)
    (q : β → m γ) (r : α → m β) : p <=< q <=< r = (p <=< q) <=< r :=
  funext $ fun x => bind_assoc (r x) q p

@[simp] lemma fish_apply {m α β γ} [Monad m] {p : α → m β} {q : β → m γ}
    {x} : (p >=> q) x = p x >>= q := rfl

@[simp] lemma backfish_apply {m α β γ} [Monad m] {p : β → m γ} {q : α → m β}
    {x} : (p <=< q) x = p =<< q x := rfl

@[simp] lemma backfish_pure {m α β} [Monad m] [LawfulMonad m] (p : α → m β) :
    p <=< pure = p := fish_pipe p

@[simp] lemma pure_backfish {m α β} [Monad m] [LawfulMonad m] (p : α → m β) :
    pure <=< p = p := fish_pure p

lemma pure_comp_fish {m α β γ} [Monad m] [LawfulMonad m] (p : α → β)
    (q : β → m γ) : pure ∘ p >=> q = q ∘ p := funext $ fun x => pure_bind (p x) q

lemma backfish_pure_comp {m α β γ} [Monad m] [LawfulMonad m] (p : β → m γ)
    (q : α → β) : p <=< pure ∘ q = p ∘ q := funext $ fun x => pure_bind (q x) p

lemma pure_bindLeft {m α} [Monad m] [LawfulMonad m] (x : m α) :
    pure =<< x = x := bind_pure x

lemma bindLeft_pure {m α β} [Monad m] [LawfulMonad m] (f : α → m β) (x : α) :
    f =<< pure x = f x := pure_bind x f

lemma bind_fish {m α β γ} [Monad m] [LawfulMonad m] (x : m α)
    (p : α → m β) (q : β → m γ) : x >>= (p >=> q) = x >>= p >>= q :=
  Eq.symm $ bind_assoc x p q

lemma backfish_bindLeft {m α β γ} [Monad m] [LawfulMonad m] (p : β → m γ)
    (q : α → m β) (x : m α) : (p <=< q) =<< x = p =<< q =<< x := bind_fish x q p

-- should refactor both of these into a general Category thing

namespace EndActions
universe u v
variable {α : Type u} {β : Type v}

scoped instance instEndMonoid : Monoid (α → α) :=
  inferInstanceAs (Monoid (Function.End α))

scoped instance instEndApply : MulAction (α → α) α :=
  inferInstanceAs (MulAction (Function.End α) α)

scoped instance instEndPostcomp : MulAction (β → β) (α → β) :=
  inferInstanceAs (MulAction (Function.End β) (α → β))

scoped instance instEndPrecomp : MulAction (α → α)ᵐᵒᵖ (α → β) where
  smul p q := q ∘ p.unop; one_smul _ := rfl; mul_smul _ _ _ := rfl

end EndActions

namespace EndMActions
universe u v
variable {α : Type v} {β : Type u}
         {m : Type u → Type v} [Monad m] [LawfulMonad m]

scoped instance instEndMMonoid : Monoid (β → m β) where
  -- mul is backwards from `instEndMonoid`, but fish is more common than backfish
  one := pure; mul x y := x >=> y
  mul_assoc := fish_assoc; one_mul := fish_pipe; mul_one := fish_pure

scoped instance instEndMApply : MulAction (β → m β)ᵐᵒᵖ (m β) where
  smul x y := x.unop =<< y
  one_smul := bind_pure; mul_smul x y b := (bind_assoc b y.unop x.unop).symm

scoped instance instEndMPostcomp : MulAction (β → m β)ᵐᵒᵖ (α → m β) where
  smul x y := y >=> x.unop
  one_smul := fish_pure; mul_smul x y b := (fish_assoc b y.unop x.unop).symm

scoped instance instEndMPrecomp {α} : MulAction (β → m β) (β → m α) where
  smul x y := x >=> y; one_smul := fish_pipe; mul_smul := fish_assoc

end EndMActions

-- lemma StateT.SatisfiesM.conjunction.{u}
--     {σ : Type u} {α : Type u} {p q : α → Prop}
--     {x : StateM σ α} :
--     SatisfiesM p x → SatisfiesM q x → SatisfiesM (fun t => p t ∧ q t) x := by
--   simp_rw [SatisfiesM_StateT_eq, SatisfiesM_Id_eq, forall_and,
--            ← and_imp, ← imp_and, imp_self]

-- lemma Part.SatisfiesM.conjunction.{u}
--     {α : Type u} {p q : α → Prop} {x : Part α} :
--     SatisfiesM p x → SatisfiesM q x → SatisfiesM (fun t => p t ∧ q t) x := by
--   rintro ⟨x1, h1⟩ ⟨x2, h2⟩
--   have H  : x.Dom = x1.Dom := (congrArg _ h1).symm
--   have H' : x.Dom = x2.Dom := (congrArg _ h2).symm
--   dsimp only [SatisfiesM]
--   refine ⟨⟨x.Dom, (fun h => ⟨x.get h, ?_, ?_⟩)⟩, rfl⟩
--   . refine Eq.subst ?_ (x1.get (H.mp h)).property; subst h1; rfl
--   . refine Eq.subst ?_ (x2.get (H'.mp h)).property; subst h2; rfl

namespace Std.Legacy.Range

/-
keep going until i ≥ stop
how many iterations?
ℓ is how long it takes until i ≥ stop
ℓ is least s.t. stop ≤ i + ℓ * step
              ↔ stop - i ≤ ℓ * step
              ↔ (stop - i) ⌈/⌉ step ≤ ℓ
so ℓ = (stop - i) ⌈/⌉ step?
-/

-- `Std.Legacy.Range.forM.loop_spec` used to live here; the `fuel`-carrying
-- internal loop of `Std.Range.forM` no longer exists (and the current
-- `Std.Legacy.Range.forM.loop` is not exported), so the statement is gone.
-- Compare `Std.Legacy.Range.forM_eq_forM_range'` in core.

lemma forM_spec {m} [Monad m] [LawfulMonad m] (r : Range) (f : ℕ → m PUnit) :
    forM r f = (List.range' r.start (r.stop - r.start) r.step).foldlM
                  (fun _ => f) ⟨⟩ := by

  admit

end Std.Legacy.Range

namespace Option

lemma mem_bind {α β} {f : α → Option β} {y : β} {o : Option α} :
    y ∈ Option.bind o f ↔ ∃ x ∈ o, f x = some y := by
  cases o
  <;> simp only [bind_none, bind_some, Option.not_mem_none, false_and,
                 exists_false, Option.mem_some_iff, exists_eq_left']
  exact mem_def


def assert {α} (o : Option α) (b : Bool) := o.bind (guard (fun _ => b))
@[simp] lemma assert_true {α} {o : Option α} : o.assert true = o :=
  by cases o <;> rfl
@[simp] lemma assert_false {α} {o : Option α} : o.assert false = none :=
  by cases o <;> rfl

lemma eq_assert_iff {α} {o₁ o₂ : Option α} {b : Bool} :
    o₁ = o₂.assert b ↔ (b = true → o₁ = o₂) ∧ (b = false → o₁ = none) := by
  cases b <;> simp only [assert_true, assert_false, reduceCtorEq,
                         true_implies, false_implies, true_and, and_true]


lemma guard_bind {α β} (x : α) (f : α → Option β) (p) [DecidablePred p] :
    guard p x >>= f = (f x).assert (p x) := by
  by_cases h : p x <;> simp [Option.guard, assert, h]

lemma guard_const_eq_some_assert {α} (p : Prop) [Decidable p] (a : α) :
    guard (fun _ => p) a = (some a).assert p :=
  Eq.trans (Eq.symm (bind_pure _)) (guard_bind _ _ (fun _ => p))

lemma map'_guard_const {α β} (f : α → β) (p : Prop) [Decidable p] (x : α) :
    Option.map f (guard (fun _ => p) x) = guard (fun _ => p) (f x) :=
  by rename Decidable p => i; dsimp only [guard, ite]; cases i <;> rfl

lemma map_guard_const {α β} (f : α → β) (p : Prop) [Decidable p] (x : α) :
    f <$> guard (fun _ => p) x = guard (fun _ => p) (f x) := map'_guard_const f p x

lemma SatisfiesM_iff_forall_mem {α} {p : α → Prop} {o : Option α} :
    SatisfiesM p o ↔ (∀ x ∈ o, p x) := SatisfiesM_Option_eq

lemma exists_mem_iff_isSome_and_forall_mem {α} {p : α → Prop} {o : Option α} :
    (∃ x ∈ o, p x) ↔ o.isSome ∧ (∀ x ∈ o, p x) :=
  Iff.trans ⟨fun ⟨x, h1, h2⟩ => ⟨⟨x, h1⟩,
                fun _ hy => Eq.subst (Option.mem_unique h1 hy) h2⟩,
             fun ⟨⟨x, h1⟩, h2⟩ => ⟨x, h1, h2 x h1⟩⟩
            (and_congr_left' isSome_iff_exists.symm)

-- this is like Part.ext'
lemma ext' {α} {o₁ o₂ : Option α} (H : o₁.isSome = o₂.isSome)
           (H' : ∀ h₁ h₂, o₁.get h₁ = o₂.get h₂) : o₁ = o₂ :=
  match o₁, o₂, H, H' with
  | some _, some _, .refl true, H' => congrArg _ (H' isSome_some isSome_some)
  | none, none, _, _ => rfl


lemma pmap_guard_eq_dite {α β} {p : α → Prop} {q} [DecidablePred p]
    (f : (a : α) → q → β) (a : α) (H : p a → q) :
    .pmap f (guard p a)
      (fun _ h => H (of_decide_eq_true (Option.guard_eq_some_iff.mp h).2))
    = (if h : p a then some (f a (H h)) else none) :=
  by by_cases h : p a <;> simp [guard, h]


lemma getD_mem {α x} (h : isSome x) (y : α) : x.getD y ∈ x :=
  Eq.symm (getD_of_ne_none (ne_none_iff_isSome.mpr h) y)

end Option

namespace Part

lemma ofOption_pure_hom {α} (x : α) : ofOption (pure x) = pure x := coe_some x
lemma pure_comp_ofOption {α} : ofOption ∘ (@pure _ _ α) = pure :=
  funext ofOption_pure_hom

lemma ofOption_bind_hom {α β} (x : Option α) (f : α → Option β) :
    ofOption (x >>= f) = ofOption x >>= ofOption ∘ f :=
  Part.ext $ fun _ => by
    simp only [Part.mem_ofOption, Option.bind_eq_bind, Option.mem_bind,
               Part.bind_eq_bind, Part.mem_bind_iff, Function.comp_apply]; rfl

lemma ofOption_naturality {α β} (x : Option α) (f : α → β) :
    ofOption (f <$> x) = f <$> ofOption x := by
  simp only [map_eq_bind_pure_comp, ofOption_bind_hom, pure_comp_ofOption,
             ← Function.comp_assoc]

end Part

namespace List
universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

namespace decEqNil
scoped instance : DecidablePred (. = ([] : List α)) :=
  fun l => decidable_of_bool l.isEmpty List.isEmpty_iff
end decEqNil


lemma mem_zip_iff {xs : List α} {ys : List β} {x y} :
    (x, y) ∈ zip xs ys ↔ (∃ (i : ℕ) (h1 : i < xs.length) (h2 : i < ys.length),
                          xs[i] = x ∧ ys[i] = y) := by
  refine Iff.trans mem_iff_get $ Iff.trans Fin.exists_iff $ exists_congr ?_
  intro i
  simp_rw [length_zip, lt_min_iff, And.exists, get_eq_getElem, getElem_zip,
           Prod.mk.injEq]



lemma headD_mem_head? {l} (a : α) (h : l ≠ []) : headD l a ∈ head? l := by
  rw [headD_eq_head?_getD]; exact Option.getD_mem (isSome_head?.mpr h) a

lemma ofOption_head?_eq_head (xs : List α) :
    Part.ofOption xs.head? = Part.mk _ xs.head :=
  Eq.trans (Part.ofOption_eq_get _) $ Part.ext' isSome_head?
  $ fun _ _ => Option.get_of_mem _ (head_mem_head? _)

lemma get_zero' {xs : List α} (h : xs ≠ []) :
    get xs ⟨0, length_pos_iff.mpr h⟩ = head xs h :=
  Eq.trans get_eq_getElem (head_eq_getElem h).symm

lemma getLast_reverse' {xs : List α} (h : xs ≠ []) :
    getLast (reverse xs) (reverse_eq_nil_iff.not.mpr h) = head xs h :=
  getLast_reverse _


open Traversable (toList_eq_self length_toList foldl_toList) in
lemma length_eq_foldl (xs : List α) :
    length xs = foldl (fun n _ => n + 1) 0 xs :=
  Eq.trans (congrArg _ toList_eq_self.symm)
  $ Eq.trans length_toList.symm
  $ Eq.trans (congrArg ULift.down (foldl_toList _ _ _))
  $ Eq.trans (congrArg (ULift.down $ foldl _ _ .) toList_eq_self)
  $ Eq.symm (foldl_hom ULift.down (fun _ _ => rfl))

lemma length_eq_foldr (xs : List α) :
    length xs = foldr (fun _ n => n + 1) 0 xs :=
  Eq.trans length_reverse.symm
  $ Eq.trans (length_eq_foldl _) foldl_reverse


lemma head?_SatisfiesM_eq_cons_tail (xs : List α) :
    SatisfiesM (xs = . :: xs.tail) xs.head? :=
  Option.SatisfiesM_iff_forall_mem.mpr (fun _ h => eq_cons_of_mem_head? h)

def uncons? (xs : List α) := xs.head?.map (., xs.tail)
@[simp] lemma uncons?_cons (x : α) (xs : List α) :
    uncons? (x :: xs) = some (x, xs) := rfl
@[simp] lemma uncons?_nil : uncons? ([] : List α) = none := rfl
lemma mem_uncons?_iff (p : α × List α) (xs : List α) :
    p ∈ xs.uncons? ↔ p.fst :: p.snd = xs := by
  cases xs <;> simp [uncons?, Prod.ext_iff, eq_comm]
lemma cons_uncons? (xs : List α) :
    Function.uncurry cons <$> xs.uncons?
    = Option.guard (List.isEmpty . = false) xs :=
  by cases xs <;> rfl

lemma cons_uncons?_SatisfiesM (xs : List α) :
    SatisfiesM (Function.uncurry cons . = xs) xs.uncons? :=
  ((head?_SatisfiesM_eq_cons_tail xs).imp Eq.symm).map_pre

lemma head?_eq_uncons?_map_fst (xs : List α) :
    xs.head? = xs.uncons?.map Prod.fst :=
  Eq.symm $ by cases xs <;> rfl

lemma pair_foldr_eq_foldr_zip {α₁ α₂ β₁ β₂} {l₁ l₂} (H : l₁.length = l₂.length)
    (op₁ : α₁ → β₁ → β₁) (op₂ : α₂ → β₂ → β₂) (b₁ : β₁) (b₂ : β₂) :
    (foldr op₁ b₁ l₁, foldr op₂ b₂ l₂)
    = foldr (fun p q => (op₁ p.1 q.1, op₂ p.2 q.2)) (b₁, b₂) (zip l₁ l₂) :=
  match l₁, l₂ with
  | [], [] => rfl
  | x::_, y::_ =>
    -- `fun p q => (op₁ p.1 q.1, op₂ p.2 q.2)`
    -- `= Function.uncurry Prod.map ∘ Prod.map op₁ op₂`
    show (Function.uncurry Prod.map ∘ Prod.map op₁ op₂) (x, y) (_, _) = _
    from congrArg _ (pair_foldr_eq_foldr_zip (Nat.succ.inj H) op₁ op₂ b₁ b₂)

lemma pair_foldl_eq_foldl_zip {α₁ α₂ β₁ β₂} {l₁ l₂} (H : l₁.length = l₂.length)
    (op₁ : β₁ → α₁ → β₁) (op₂ : β₂ → α₂ → β₂) (b₁ : β₁) (b₂ : β₂) :
    (foldl op₁ b₁ l₁, foldl op₂ b₂ l₂)
    = foldl (fun p q => (op₁ p.1 q.1, op₂ p.2 q.2)) (b₁, b₂) (zip l₁ l₂) := by
  repeat rw [← foldr_reverse]
  simp only [zip, reverse_zipWith H]
  exact pair_foldr_eq_foldr_zip (by simp [H]) _ _ _ _

lemma zip_self_eq_map_dup (xs : List α) : zip xs xs = map (fun t => (t, t)) xs :=
  Eq.trans (congrArg₂ zip (map_id _).symm (map_id _).symm) zip_map'

lemma prod_mk_foldr (f : α → β → β) (g : α → γ → γ) (b0 : β) (c0 : γ) (as : List α) :
    (as.foldr f b0, as.foldr g c0)
    = as.foldr (fun a => Prod.map (f a) (g a)) (b0, c0) :=
  Eq.trans (pair_foldr_eq_foldr_zip rfl _ _ _ _)
  $ Eq.trans (congrArg _ (zip_self_eq_map_dup _)) foldr_map

lemma prod_mk_foldl (f : β → α → β) (g : γ → α → γ) (b0 : β) (c0 : γ) (as : List α) :
    (as.foldl f b0, as.foldl g c0)
    = as.foldl (fun p a => Prod.map (f . a) (g . a) p) (b0, c0) :=
  by rw [← foldr_reverse, ← foldr_reverse, prod_mk_foldr, foldr_reverse]

def foldrRecOn₂ {α₁ α₂ β₁ β₂} {C : β₁ → β₂ → Sort*} {l₁ l₂}
    (H : l₁.length = l₂.length) (op₁ : α₁ → β₁ → β₁) (op₂ : α₂ → β₂ → β₂)
    (b₁ : β₁) (b₂ : β₂) (hb : C b₁ b₂)
    (hl : ∀ b₁ b₂, C b₁ b₂ → ∀ a₁ a₂, (a₁, a₂) ∈ zip l₁ l₂
                           → C (op₁ a₁ b₁) (op₂ a₂ b₂)) :
    C (foldr op₁ b₁ l₁) (foldr op₂ b₂ l₂) :=
  (congrArg (Function.uncurry C) (pair_foldr_eq_foldr_zip H op₁ op₂ b₁ b₂)).mpr
  $ foldrRecOn _ _ hb $ fun b₁₂ hb a₁₂ ha => hl b₁₂.1 b₁₂.2 hb a₁₂.1 a₁₂.2 ha

def foldlRecOn₂ {α₁ α₂ β₁ β₂} {C : β₁ → β₂ → Sort*} {l₁ l₂}
    (H : l₁.length = l₂.length) (op₁ : β₁ → α₁ → β₁) (op₂ : β₂ → α₂ → β₂)
    (b₁ : β₁) (b₂ : β₂) (hb : C b₁ b₂)
    (hl : ∀ b₁ b₂, C b₁ b₂ → ∀ a₁ a₂, (a₁, a₂) ∈ zip l₁ l₂
                           → C (op₁ b₁ a₁) (op₂ b₂ a₂)) :
    C (foldl op₁ b₁ l₁) (foldl op₂ b₂ l₂) :=
  (congrArg (Function.uncurry C) (pair_foldl_eq_foldl_zip H op₁ op₂ b₁ b₂)).mpr
  $ foldlRecOn _ _ hb $ fun b₁₂ hb a₁₂ ha => hl b₁₂.1 b₁₂.2 hb a₁₂.1 a₁₂.2 ha

def foldrRecDiag {α β₁ β₂} {C : β₁ → β₂ → Sort*} {xs}
    (op₁ : α → β₁ → β₁) (op₂ : α → β₂ → β₂) (b₁ : β₁) (b₂ : β₂) (hb : C b₁ b₂)
    (hl : ∀ b₁ b₂, C b₁ b₂ → ∀ a, a ∈ xs → C (op₁ a b₁) (op₂ a b₂)) :
    C (foldr op₁ b₁ xs) (foldr op₂ b₂ xs) := by
  refine foldrRecOn₂ rfl op₁ op₂ b₁ b₂ hb $ fun y₁ y₂ h1 x₁ x₂ h2 => ?_
  refine cast ?_ (hl y₁ y₂ h1 x₁ ?_) <;>
  have h3 := (exists_congr (fun _ => and_congr_right' Prod.ext_iff)).mp
             $ mem_map.mp ((congrArg (_ ∈ .) (zip_self_eq_map_dup xs)).mp h2)
  . refine congrArg (C (op₁ x₁ y₁) $ op₂ . y₂) ?_
    have h4 := exists_eq_left.mp $ h3.imp $ fun _ => And.right; exact h4
  . exact (exists_eq_left (p := (. ∈ xs))).mp $ h3.imp $ fun _ =>
            and_comm.mp ∘ And.imp_right And.left

def foldlRecDiag {α β₁ β₂} {C : β₁ → β₂ → Sort*} {xs}
    (op₁ : β₁ → α → β₁) (op₂ : β₂ → α → β₂) (b₁ : β₁) (b₂ : β₂) (hb : C b₁ b₂)
    (hl : ∀ b₁ b₂, C b₁ b₂ → ∀ a ∈ xs, C (op₁ b₁ a) (op₂ b₂ a)) :
    C (foldl op₁ b₁ xs) (foldl op₂ b₂ xs) := by
  refine foldlRecOn₂ rfl op₁ op₂ b₁ b₂ hb $ fun y₁ y₂ h1 x₁ x₂ h2 => ?_
  refine cast ?_ (hl y₁ y₂ h1 x₁ ?_) <;>
  have h3 := (exists_congr (fun _ => and_congr_right' Prod.ext_iff)).mp
             $ mem_map.mp ((congrArg (_ ∈ .) (zip_self_eq_map_dup xs)).mp h2)
  . refine congrArg (C (op₁ y₁ x₁) $ op₂ y₂ .) ?_
    have h4 := exists_eq_left.mp $ h3.imp $ fun _ => And.right; exact h4
  . exact (exists_eq_left (p := (. ∈ xs))).mp $ h3.imp $ fun _ =>
            and_comm.mp ∘ And.imp_right And.left

lemma foldr_left_act [Monoid α] [MulAction α β] (b : β) (xs : List α) :
    foldr (. * .) 1 xs • b = foldr (. • .) b xs :=
  Eq.trans (Eq.symm $ foldr_hom (. • b) (Eq.symm $ mul_smul . . b))
  $ congrArg (foldr _ . _) (one_smul α b)

open scoped RightActions in
lemma foldl_right_act [Monoid α] [MulAction αᵐᵒᵖ β] (b : β) (xs : List α) :
    b <• foldl (. * .) 1 xs = foldl (. <• .) b xs :=
  Eq.trans (Eq.symm $ foldl_hom (b <• .) (Eq.symm $ op_smul_mul b . .))
  $ congrArg (foldl _ . _) (one_smul αᵐᵒᵖ b)

open scoped RightActions in
lemma foldr_right_act [Monoid α] [MulAction αᵐᵒᵖ β] (b : β) (xs : List α) :
    b <• foldr (. * .) 1 xs = foldl (. <• .) b xs :=
  Eq.trans (congrArg (b <• .) $ Eq.trans (one_mul _).symm
  $ Eq.trans foldl1_eq_foldr1.symm $ mul_one _) $ foldl_right_act _ _

lemma foldl_left_act [Monoid α] [MulAction α β] (b : β) (xs : List α) :
    foldl (. * .) 1 xs • b = foldr (. • .) b xs :=
  Eq.trans (congrArg (. • b) $ Eq.trans (mul_one _).symm
    $ Eq.trans foldl1_eq_foldr1 $ one_mul _) $ foldr_left_act _ _

open scoped EndActions in
lemma foldr_comp_apply (xs : List (β → β)) (f : α → β) (a : α) :
    foldr (fun s t => s ∘ t) f xs a = foldr id (f a) xs :=
  (congrFun . a) $ Eq.trans (foldr_left_act f xs).symm
  $ congrArg (. • f) $ funext (foldr_left_act . xs)

open scoped RightActions EndActions in
lemma foldl_comp_apply (xs : List (α → α)) (f : α → β) (a : α) :
    foldl (fun s t => s ∘ t) f xs a = f (foldr id a xs) :=
  suffices foldl _ f xs = f ∘ (foldr _ . xs) from congrFun this a
  Eq.trans (foldr_right_act _ _).symm $ congrArg (f <• .) $ funext (foldr_comp_apply _ _)

lemma foldr_eq_foldr_comp_map (f : α → β → β) (b : β) (xs : List α) :
    foldr f b xs = foldr (fun s t => s ∘ t) id (map f xs) b :=
  Eq.symm $ Eq.trans (foldr_comp_apply (map f xs) id b) foldr_map

lemma foldl_eq_foldl_comp_map (f : β → α → β) (b : β) (xs : List α) :
    foldl f b xs = foldl (fun s t => t ∘ s) id (map (fun x y => f y x) xs) b :=
  by rw [← foldr_reverse, ← foldr_reverse, ← map_reverse, foldr_eq_foldr_comp_map]

open scoped EndMActions in
lemma foldl_fish_bind {m α β} [Monad m] [LawfulMonad m] (xs : List (β → m β))
    (f : α → m β) (a : m α) :
    a >>= foldl (fun s t => s >=> t) f xs = foldl (. >>= .) (a >>= f) xs :=
  Eq.trans (congrArg (a >>= .) (foldr_right_act _ _).symm)
  $ Eq.trans (LawfulMonad.bind_assoc a f _).symm (foldr_right_act _ xs)

open scoped EndMActions in
lemma foldr_fish_bind {m α β} [Monad m] [LawfulMonad m] (xs : List (α → m α))
    (f : α → m β) (a : m α) :
    a >>= foldr (fun s t => s >=> t) f xs = foldl (. >>= .) a xs >>= f :=
  Eq.trans (congrArg (a >>= .) (foldr_left_act _ _).symm)
  $ Eq.trans (LawfulMonad.bind_assoc a _ f).symm
  $ congrArg (. >>= f) (foldr_right_act a xs)

lemma foldl_backfish_bindLeft {m α β} [Monad m] [LawfulMonad m]
    (xs : List (α → m α)) (f : α → m β) (a : m α) :
    foldl (fun s t => s <=< t) f xs =<< a = f =<< foldr (. =<< .) a xs :=
  Eq.trans (congrArg (. =<< a) foldr_reverse.symm)
  $ Eq.trans (foldr_fish_bind _ _ _) $ congrArg (. >>= f) foldl_reverse

lemma foldr_backfish_bindLeft {m α β} [Monad m] [LawfulMonad m]
    (xs : List (β → m β)) (f : α → m β) (a : m α) :
    foldr (fun s t => s <=< t) f xs =<< a = foldr (. =<< .) (f =<< a) xs :=
  Eq.trans (congrArg (. =<< a) foldl_reverse.symm)
  $ Eq.trans (foldl_fish_bind _ _ _) foldl_reverse

open MulOpposite RightActions EndMActions in
lemma foldr_backfish_pure_backfish {m α β} [Monad m] [LawfulMonad m]
    (xs : List (β → m β)) (f : α → m β) :
    foldr (. <=< .) pure xs <=< f = foldr (. <=< .) f xs :=
  have H (p q : β → m β) : op p * op q = op (p <=< q) := rfl
  Eq.trans (congrArg (. • f) (foldr_map_hom H).symm)
  $ Eq.trans (foldr_left_act f _) foldr_map

open scoped RightActions EndMActions in
lemma fish_foldl_fish_pure {m α β} [Monad m] [LawfulMonad m]
    (xs : List (β → m β)) (f : α → m β) :
    f >=> foldl (. >=> .) pure xs = foldl (. >=> .) f xs :=
  foldl_right_act f xs

open scoped EndMActions in
lemma foldlM_eq_foldl_fish_map {m} [Monad m] [LawfulMonad m]
    (f : β → α → m β) (b : β) (xs : List α) :
    xs.foldlM f b = foldl (. >=> .) pure (map (fun x y => f y x) xs) b :=
  Eq.trans (foldlM_eq_foldl _ _ _) $ Eq.trans foldl_map.symm
  $ Eq.trans (foldl_right_act _ _).symm (pure_bind _ _)

lemma foldrM_eq_foldr_backfish_map {m} [Monad m] [LawfulMonad m]
    (f : α → β → m β) (b : β) (xs : List α) :
    xs.foldrM f b = foldr (. <=< .) pure (map f xs) b :=
  Eq.trans (foldlM_eq_foldl_fish_map _ _ _)
  $ congrFun (Eq.trans (congrArg _ map_reverse) foldl_reverse) b

lemma foldlM_eq_foldl_fish_map' {m} [Monad m] [LawfulMonad m]
    (f : β → α → m β) (xs : List α) :
    xs.foldlM f = foldl (. >=> .) pure (map (fun x y => f y x) xs) :=
  funext (xs.foldlM_eq_foldl_fish_map f)

lemma foldrM_eq_foldr_backfish_map' {m} [Monad m] [LawfulMonad m]
    (f : α → β → m β) (xs : List α) :
    xs.foldrM f = foldr (. <=< .) pure (map f xs) :=
  funext (xs.foldrM_eq_foldr_backfish_map f)

lemma foldrM_homM {m n} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    (f : ∀ {a}, m a → n a) (g₁ : α → β → m β) (g₂ : α → β → n β) (l : List α)
    (init : β) (h1 : ∀ {a} (x : a), f (pure x) = pure x)
    (h2 : ∀ {a b} (x : m a) (y : a → m b), f (x >>= y) = f x >>= (f ∘ y))
    -- equivalent to `f y >>= g₂ x = f (y >>= g₁ x)` under h2
    -- which makes it look more like the condition in foldr_hom
    (H : ∀ x y, f y >>= g₂ x = f y >>= (f ∘ g₁ x)) :
    l.foldrM g₂ init = f (l.foldrM g₁ init) := by
  rw [foldrM_eq_foldr, foldrM_eq_foldr]; conv_lhs => left; exact (h1 init).symm
  exact foldr_hom _ (fun _ _ => Eq.trans (H _ _) (Eq.symm (h2 _ _)))

lemma foldlM_homM {m n} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    (f : ∀ {a}, m a → n a) (g₁ : β → α → m β) (g₂ : β → α → n β) (l : List α)
    (init : β) (h1 : ∀ {a} (x : a), f (pure x) = pure x)
    (h2 : ∀ {a b} (x : m a) (y : a → m b), f (x >>= y) = f x >>= (f ∘ y))
    -- equivalent to `f y >>= g₂ x = f (y >>= g₁ x)` under h2
    -- which makes it look more like the condition in foldr_hom
    (H : ∀ x y, f y >>= (g₂ . x) = f y >>= (f ∘ (g₁ . x))) :
    l.foldlM g₂ init = f (l.foldlM g₁ init) := by
  rw [foldlM_eq_foldl, foldlM_eq_foldl]; conv_lhs => left; exact (h1 init).symm
  exact foldl_hom _ (fun _ _ => Eq.trans (H _ _) (Eq.symm (h2 _ _)))

lemma foldrM_pure_comp {m} [Monad m] [LawfulMonad m]
    (f : α → β → β) (b : β) (xs : List α) :
    xs.foldrM (pure ∘ f .) b = (pure (xs.foldr f b) : m β) :=
  have H1 {a} x : pure (pure x : Id a) = pure x := rfl
  have H2 x y : pure y >>= pure ∘ f x = pure y >>= pure ∘ f x := rfl
  Eq.trans (foldrM_homM _ _ _ _ _ H1 (Eq.symm $ pure_bind . $ pure ∘ .) H2)
  $ congrArg pure foldr_eq_foldrM.symm

lemma foldlM_pure_comp {m} [Monad m] [LawfulMonad m]
    (f : β → α → β) (b : β) (xs : List α) :
    xs.foldlM (pure ∘ f .) b = (pure (xs.foldl f b) : m β) :=
  have H1 {a} x : pure (pure x : Id a) = pure x := rfl
  have H2 x y : pure y >>= pure ∘ (f . x) = (pure y : m β) >>= pure ∘ (f . x) := rfl
  Eq.trans (foldlM_homM _ _ _ _ _ H1 (Eq.symm $ pure_bind . $ pure ∘ .) H2)
  $ congrArg pure foldl_eq_foldlM.symm

lemma foldr_pmap_eq_foldr_attach {α β γ} {p : α → Prop} (f : (a : α) → p a → β)
    (xs : List α) (H : ∀ a ∈ xs, p a) (g : β → γ → γ) (init : γ) :
    (xs.pmap f H).foldr g init
    = xs.attach.foldr (fun x c => g (f x.val (H _ x.property)) c) init :=
  by rw [List.pmap_eq_map_attach H, foldr_map]

lemma foldl_pmap_eq_foldl_attach {α β γ} {p : α → Prop} (f : (a : α) → p a → β)
    (xs : List α) (H : ∀ a ∈ xs, p a) (g : γ → β → γ) (init : γ) :
    (xs.pmap f H).foldl g init
    = xs.attach.foldl (fun c x => g c (f x.val (H _ x.property))) init :=
  by rw [List.pmap_eq_map_attach H, foldl_map]

lemma foldr_pmap_mem_foldrM_Part {α β γ} {p : α → Prop} (f : (a : α) → p a → β)
    (xs : List α) (H : ∀ a ∈ xs, p a) (g : β → γ → γ) (init : γ) :
    (xs.pmap f H).foldr g init
    ∈ xs.foldrM (fun a c => Part.mk (p a) (fun h => g (f a h) c)) init := by
  conv_lhs => rw [← attach_map_subtype_val xs]
  rw [foldr_pmap_eq_foldr_attach, foldrM_eq_foldr, foldr_map]
  apply foldrRecOn₂
  . rfl
  . exact Part.mem_some _
  . intro p b hb a1 _ ha
    refine Part.mem_bind_iff.mpr ⟨b, hb, H _ a1.property, ?_⟩
    obtain ⟨i, _, _, ⟨⟩, ⟨⟩⟩ := mem_zip_iff.mp ha; rfl

lemma foldl_pmap_mem_foldlM_Part {α β γ} {p : α → Prop} (f : (a : α) → p a → β)
    (xs : List α) (H : ∀ a ∈ xs, p a) (g : γ → β → γ) (init : γ) :
    (xs.pmap f H).foldl g init
    ∈ xs.foldlM (fun c a => Part.mk (p a) (fun h => g c (f a h))) init := by
  rw [← foldr_reverse, ← foldrM_reverse, ← pmap_reverse]
  refine foldr_pmap_mem_foldrM_Part f _ ?_ (fun x y => g y x) init
  exact fun a h => H a (mem_reverse.mp h)

lemma foldr_pmap_mem_foldrM_Option {α β γ} {p : α → Prop} [DecidablePred p]
    (f : (a : α) → p a → β) (xs : List α) (H : ∀ a ∈ xs, p a) (g : β → γ → γ)
    (init : γ) :
    (xs.pmap f H).foldr g init
    ∈ xs.foldrM (fun a c => (Option.guard p a).pmap (fun _ h => g (f a h) c)
                              (fun _ h => of_decide_eq_true (Option.guard_eq_some_iff.mp h).2))
                init := by
  refine Part.mem_ofOption.mp ?_
  refine Eq.subst (motive := ((xs.pmap f H).foldr g init ∈ .)) ?_
                  (foldr_pmap_mem_foldrM_Part f xs H g init)
  apply foldrM_homM
  . exact Part.ofOption_pure_hom
  . exact Part.ofOption_bind_hom
  . intro x _
    refine _root_.bind_congr ?_
    intro
    dsimp only [Function.comp_apply]
    refine Part.ext' ?_ ?_
    . simp only [Part.ofOption_dom, Option.isSome_pmap, Option.isSome_guard]
      exact decide_eq_true_iff.symm
    . intro (h1 : p x) _
      simp [Option.guard, h1]

lemma foldl_pmap_mem_foldlM_Option {α β γ} {p : α → Prop} [DecidablePred p]
    (f : (a : α) → p a → β) (xs : List α) (H : ∀ a ∈ xs, p a) (g : γ → β → γ)
    (init : γ) :
    (xs.pmap f H).foldl g init
    ∈ xs.foldlM (fun c a => (Option.guard p a).pmap (fun _ h => g c (f a h))
                              (fun _ h => of_decide_eq_true (Option.guard_eq_some_iff.mp h).2))
                init := by
  rw [← foldr_reverse, ← foldrM_reverse, ← pmap_reverse]
  refine foldr_pmap_mem_foldrM_Option f _ ?_ (fun x y => g y x) init
  exact fun a h => H a (mem_reverse.mp h)

lemma foldr_telescope {α β γ δ ε ζ} (p : α → γ) (q : α → δ) (r : α → ε)
    (g₁ : γ → ζ → β) (g₂ : δ → ζ → ζ) (g₃ : ε → β → ζ) (b : β) (xs : List α)
    (h1 : Pairwise (fun w z => ∀ t, g₃ (r w) (g₁ (p z) t) = t) xs) (h2 : xs ≠ [])
    : xs.foldr (fun x y => g₁ (p x) (g₂ (q x) (g₃ (r x) y))) b
      = g₁ (p (xs.head h2)) (xs.foldr (g₂ ∘ q) (g₃ (r (xs.getLast h2)) b)) :=
  match xs, h1 with
  | [_], _ => rfl
  | _ :: x :: xs, .cons H₁ H₂ =>
    have H₃ := foldr_telescope p q r g₁ g₂ g₃ b _ H₂ (cons_ne_nil x xs)
    congrArg (g₁ (p _) ∘ g₂ (q _))
    $ Eq.trans (congrArg (g₃ (r _)) H₃) (H₁ _ (head_mem _) _)

lemma foldl_telescope {α β γ δ ε ζ} (p : α → γ) (q : α → δ) (r : α → ε)
    (g₁ : β → γ → ζ) (g₂ : ζ → δ → ζ) (g₃ : ζ → ε → β) (b : β) (xs : List α)
    (h1 : Pairwise (fun w z => ∀ t, g₁ (g₃ t (r w)) (p z) = t) xs) (h2 : xs ≠ [])
    : xs.foldl (fun x y => g₃ (g₂ (g₁ x (p y)) (q y)) (r y)) b
      = g₃ (xs.foldl (g₂ . $ q .) (g₁ b (p (xs.head h2)))) (r (xs.getLast h2)) := by
  rw [← foldr_reverse, ← foldr_reverse, ← head_reverse, ← getLast_reverse' h2]
  exact foldr_telescope r q p (flip g₃) (flip g₂) (flip g₁) b _
                        (pairwise_reverse.mpr h1) (reverse_eq_nil_iff.not.mpr h2)

lemma foldr_telescope' {α β γ δ ε ζ} (p : γ) (q : α → δ) (r : ε)
    (g₁ : γ → ζ → β) (g₂ : δ → ζ → ζ) (g₃ : ε → β → ζ) (b : β) (xs : List α)
    (h1 : ∀ t, g₃ r (g₁ p t) = t) (h2 : xs ≠ [])
    : xs.foldr (fun x y => g₁ p (g₂ (q x) (g₃ r y))) b
      = g₁ p (xs.foldr (g₂ ∘ q) (g₃ r b)) :=
  have h3 := pairwise_of_forall_mem_list $ fun _ _ _ _ => h1
  foldr_telescope (fun _ => p) q (fun _ => r) g₁ g₂ g₃ b xs h3 h2

lemma foldl_telescope' {α β γ δ ε ζ} (p : γ) (q : α → δ) (r : ε)
    (g₁ : β → γ → ζ) (g₂ : ζ → δ → ζ) (g₃ : ζ → ε → β) (b : β) (xs : List α)
    (h1 : ∀ t, g₁ (g₃ t r) p = t) (h2 : xs ≠ [])
    : xs.foldl (fun x y => g₃ (g₂ (g₁ x p) (q y)) r) b
      = g₃ (xs.foldl (g₂ . $ q .) (g₁ b p)) r :=
  have h3 := pairwise_of_forall_mem_list $ fun _ _ _ _ => h1
  foldl_telescope (fun _ => p) q (fun _ => r) g₁ g₂ g₃ b xs h3 h2

lemma foldrM_telescope {m α β γ} [Monad m] [LawfulMonad m]
    (p : α → γ → m β) (q : α → γ → m γ) (r : α → β → m γ) (b : β) (xs : List α)
    (h1 : Pairwise (fun w z => r w <=< p z = pure) xs) (h2 : xs ≠ []) :
    xs.foldrM (fun x => p x <=< q x <=< r x) b
    = p (xs.head h2) =<< xs.foldrM q =<< r (xs.getLast h2) b :=
  have h3 {w z} (h : r w <=< p z = pure) t := Eq.trans (backfish_assoc _ _ _)
    $ Eq.trans (congrArg (. <=< _) h) (pure_backfish t)
  show _ = (_ <=< _ <=< _) b by
  rw [foldrM_eq_foldr_backfish_map', foldr_backfish_pure_backfish, foldr_map]
  rw [foldrM_eq_foldr_backfish_map, foldr_map]
  conv in _ <=< _ => rw [← backfish_assoc, ← backfish_assoc]
  rw [foldr_telescope _ _ _ _ _ _ pure _ (h1.imp h3) h2, backfish_pure]; rfl

lemma foldlM_telescope {m α β γ} [Monad m] [LawfulMonad m]
    (p : α → β → m γ) (q : α → γ → m γ) (r : α → γ → m β) (b : β) (xs : List α)
    (h1 : Pairwise (fun w z => r w >=> p z = pure) xs) (h2 : xs ≠ []) :
    xs.foldlM (fun x y => (p y >=> q y >=> r y) x) b
    = p (xs.head h2) b >>= xs.foldlM (fun x y => q y x) >>= r (xs.getLast h2) :=
  have h3 {w z} (h : r w >=> p z = pure) t := Eq.trans (fish_assoc _ _ _)
    $ Eq.trans (congrArg (_ >=> .) h) (fish_pure t)
  show _ = ((_ >=> _) >=> _) b by
  rw [foldlM_eq_foldl_fish_map', fish_foldl_fish_pure, foldl_map]
  rw [foldlM_eq_foldl_fish_map, foldl_map]
  conv in _ >=> _ => rw [← fish_assoc, ← fish_assoc]
  rw [foldl_telescope _ _ _ _ _ _ pure _ (h1.imp h3) h2, fish_pipe]

lemma foldrM_telescope' {m α β γ} [Monad m] [LawfulMonad m]
    (p : γ → m β) (q : α → γ → m γ) (r : β → m γ) (b : β) (xs : List α)
    (h1 : r <=< p = pure) (h2 : xs ≠ []) :
    xs.foldrM (fun x => p <=< q x <=< r) b = p =<< xs.foldrM q =<< r b :=
  have h3 := pairwise_of_forall_mem_list $ fun _ _ _ _ => h1
  foldrM_telescope (fun _ => p) q (fun _ => r) b xs h3 h2

lemma foldlM_telescope' {m α β γ} [Monad m] [LawfulMonad m]
    (p : β → m γ) (q : α → γ → m γ) (r : γ → m β) (b : β) (xs : List α)
    (h1 : r >=> p = pure) (h2 : xs ≠ []) :
    xs.foldlM (fun x y => (p >=> q y >=> r) x) b
    = p b >>= xs.foldlM (fun x y => q y x) >>= r :=
  have h3 := pairwise_of_forall_mem_list $ fun _ _ _ _ => h1
  foldlM_telescope (fun _ => p) q (fun _ => r) b xs h3 h2

-- open scoped decEqNil in
-- lemma scanr_mem_foldrM {α β} (f : α → β → β) (b : β) (xs : List α) :
--     scanr f b xs ∈ foldrM (fun x ys => ys.head?.map (f x . :: ys)) [b] xs :=
--   let F : β × List β → List β := Function.uncurry cons
--   let G x (y : β × List β) := (f x y.1, y.1 :: y.2)
--   have H1 x ys : ys.head?.map (f x . :: ys)
--                = (pure ∘ F <=< pure ∘ G x <=< uncons?) ys := by cases ys <;> rfl
--   have H2 : uncons? <=< pure ∘ F = pure :=
--     Eq.trans (backfish_pure_comp _ _) $ funext $ fun p => uncons?_cons p.1 p.2
--   if h : xs = [] then h ▸ rfl else
--   Eq.trans (congrArg (foldrM . _ _) (funext₂ H1))
--   $ Eq.trans (foldrM_telescope' _ _ _ _ _ H2 h) $ Eq.trans (bind_pure_comp _ _)
--   $ congrArg (F <$> .) (foldrM_pure_comp G (b, []) _)

-- lemma scanr_eq_foldr {α β} (f : α → β → β) (b : β) (xs : List α) :
--     scanr f b xs = foldr (fun x ys => f x (ys.headD b) :: ys) [b] xs :=
--   Option.mem_unique (scanr_mem_foldrM f b xs)
--   $ Eq.trans (foldrM_eq_foldr _ _ _) $ And.right
--   $ foldrRecDiag (C := fun bs bs? => bs ≠ [] ∧ bs? = some bs) _ _ _ _
--                  ⟨cons_ne_nil b [], rfl⟩ (fun _ _ h _ _ => ⟨cons_ne_nil _ _,
--     h.right ▸ Eq.trans (Option.some_bind _ _) (headD_mem_head? b h.left ▸ rfl)⟩)



-- `List.scanr_append`, `List.getElem?_scanr`, `List.getElem_scanr`,
-- `List.getElem_scanl` and `List.getElem?_scanl` are now all in core
-- (`Init.Data.List.Scan.Lemmas`), superseding the `scanr_append`, `get?_scanr`,
-- `get_scanr`, `get_scanl` and `get?_scanl` that used to live here.

lemma scanl_succ_eq_range'_length {α} (s : ℕ) (xs : List α) :
    scanl (fun k _ => k + 1) s xs = range' s (xs.length + 1) := by
  induction xs generalizing s with
  | nil => simp
  | cons _ _ ih => rw [scanl_cons, ih, length_cons]; exact range'_succ.symm

end List

namespace Array
universe u v w
variable {α : Type u} {β : Type v} {γ : Type w} {m : Type v → Type w}
         [Monad m] [LawfulMonad m]

-- `Array.getElem?_map` is now in core with the same statement.

theorem mapIdx_eq_ofFn (a : Array α) (f : ℕ → α → β) :
    a.mapIdx f = Array.ofFn (fun i : Fin a.size => f i a[i]) :=
  Array.ext (Eq.trans Array.size_mapIdx Array.size_ofFn.symm)
  $ fun i h1 h2 =>
    Eq.trans (Array.getElem_mapIdx h1) (Array.getElem_ofFn h2).symm

theorem map_eq_mapIdx (a : Array α) (f : α → β) :
    a.map f = a.mapIdx (fun _ x => f x) :=
  Array.ext (Eq.trans Array.size_map Array.size_mapIdx.symm)
  $ fun i h1 h2 =>
    Eq.trans (Array.getElem_map _ h1) (Array.getElem_mapIdx h2).symm

lemma map_eq_ofFn (a : Array α) (f : α → β) :
    a.map f = Array.ofFn (fun (i : Fin a.size) => f a[i]) :=
  Eq.trans (map_eq_mapIdx _ _) (mapIdx_eq_ofFn a _)

-- `Array.isEmpty_iff` and `Array.push_eq_append_singleton` are now in core.

lemma isSome_getElem? (a : Array α) (i : ℕ) : a[i]?.isSome ↔ i < a.size := by
  simp

private def extractAlt (as : Array α) (start stop : ℕ) :=
  (StateT.run ([start:stop].forM (m := StateT (Array α) Option)
              $ fun i => do _root_.modify (Array.push . (← as[i]?)))
              (mkEmpty (min stop as.size - start))).map Prod.snd

lemma extract_eq_extract_upto_min (as : Array α) (start stop : ℕ) :
    as.extract start stop = as.extract start (min stop as.size) :=
  Array.ext
    (Eq.trans size_extract $ Eq.symm $ Eq.trans size_extract
      $ congrArg (. - start) $ Eq.trans (min_assoc _ _ _)
      $ congrArg (min stop) $ Nat.min_self _)
    (fun _ h1 h2 => Eq.trans (getElem_extract h1) (getElem_extract h2).symm)

lemma extractAlt_eq_extractAlt_upto_min (as : Array α) (start stop : ℕ) :
    as.extractAlt start stop = as.extractAlt start (min stop as.size) := by
  refine congrArg (Option.map _ $ StateT.run . _) (congrFun ?_ _)
  unfold Std.Legacy.Range.forM

  admit

lemma extract_mem_extractAlt (as : Array α) (start stop : ℕ) :
    as.extract start stop ∈ as.extractAlt start stop := by
  rw [extract_eq_extract_upto_min]

  admit

lemma extract_toList (as : Array α) (start stop : ℕ) :
    (as.extract start stop).toList = (as.toList.drop start).take (stop - start) :=
  Eq.trans toList_extract List.extract_eq_take_drop

-- `Array.size_extract` is now in core with the same statement.

lemma extract_isEmpty_of_stop_le_start (as : Array α) (start stop : ℕ)
    (H : stop ≤ start) : (as.extract start stop).isEmpty :=
  decide_eq_true $ Eq.trans size_extract
  $ Nat.sub_eq_zero_of_le $ min_le_of_left_le H

lemma extract_isEmpty_of_size_le_start (as : Array α) (start stop : ℕ)
    (H : as.size ≤ start) : (as.extract start stop).isEmpty :=
  Eq.trans (congrArg _ (extract_eq_extract_upto_min _ _ _))
  $ extract_isEmpty_of_stop_le_start _ _ _ $ min_le_of_right_le H

lemma extract_getElem? (as : Array α) (start stop i : ℕ) :
    (as.extract start stop)[i]? = as[start + i]?.assert (start + i < stop) := by
  rw [Array.getElem?_extract]
  by_cases h : start + i < stop
  . rw [decide_eq_true h, Option.assert_true]
    by_cases h2 : i < min stop as.size - start
    . rw [if_pos h2]
    . rw [if_neg h2, eq_comm, Array.getElem?_eq_none_iff]
      omega
  . rw [decide_eq_false h, Option.assert_false, if_neg]
    omega

-- `Array.get?` and `Array.get` no longer exist, so the `get?`/`get` phrasings
-- `extract_get?` and `extract_get` are gone; `Array.getElem_extract` in core is
-- exactly the old `extract_getElem`.

lemma foldlM_eq_foldlM_upto_min (f : β → α → m β) (init : β) (as : Array α)
    (start stop : ℕ) :
    as.foldlM f init start stop  = as.foldlM f init start (min stop as.size) := by
  simp only [foldlM, min_le_right, dite_true, dite_eq_iff']
  refine ⟨?_, ?_ ∘ Nat.le_of_not_le⟩ <;> intro h <;> congr <;> refine Eq.symm ?_
  <;> simp only [min_eq_left_iff, min_eq_right_iff, h]

lemma foldl_eq_foldl_upto_min (f : β → α → β) (init : β) (as : Array α)
    (start stop : ℕ) :
    as.foldl f init start stop  = as.foldl f init start (min stop as.size) :=
  foldlM_eq_foldlM_upto_min (m:=Id) f init as start stop

lemma foldlM_eq_pure_init_of_stop_le_start (f : β → α → m β) (init : β)
    (as : Array α) (start stop : ℕ) (H : stop ≤ start) :
    as.foldlM f init start stop = pure init := by
  dsimp only [foldlM]; simp (config:={singlePass:=true}) only [foldlM.loop]
  simp only [not_lt.mpr H, dite_false, apply_dite (. = pure init),
             dite_prop_iff_and, implies_true, true_and, and_true]
  intro h h'; exfalso; exact h (le_trans H (le_of_lt h'))

lemma foldl_eq_init_of_stop_le_start (f : β → α → β) (init : β)
    (as : Array α) (start stop : ℕ) (H : stop ≤ start) :
    as.foldl f init start stop = init :=
  foldlM_eq_pure_init_of_stop_le_start (m:=Id) f init as start stop H

lemma foldlM_eq_foldlM_extract (f : β → α → m β) (init : β) (as : Array α)
    (start stop : ℕ) :
    as.foldlM f init start stop = (as.extract start stop).foldlM f init := by
  rw [← foldlM_toList, extract_toList, foldlM_eq_foldlM_upto_min]
  generalize h1 : min stop (size as) = stop'
  suffices h : foldlM f init as start stop'
             = List.foldlM f init ((as.toList.drop start).take (stop' - start)) by
    refine Eq.trans h $ congrArg _ $ List.take_eq_take_iff.mpr ?_
    simp only [List.length_drop, Array.length_toList, ← h1]
    omega
  replace h1 := le_of_eq_of_le h1.symm (min_le_right _ _); clear stop
  rcases Nat.le_total start stop' with h2 | h2
  . generalize H : stop' - start = w
    replace H := Nat.eq_add_of_sub_eq h2 H; clear h2; subst H
    simp only [foldlM, h1, le_refl, dite_true, Nat.sub_zero, Nat.add_sub_cancel]
    induction w generalizing start init with
    | zero =>
      rw [List.take_zero, List.foldlM_nil, foldlM.loop]
      simp only [Nat.zero_add, lt_irrefl, dite_false]
    | succ w ih =>
      have := lt_of_lt_of_le (Nat.lt_succ_self start) (Nat.le_add_left _ w)
      rw [foldlM.loop]
      simp only [Nat.succ_add_eq_add_succ] at h1 ⊢
      replace ih b := ih b (Nat.succ start) h1
      simp only [ih, this, dite_true, List.take_succ_cons, List.foldlM_cons,
                 List.drop_eq_getElem_cons (lt_of_lt_of_le this h1)]
      rfl
  . rw [Nat.sub_eq_zero_of_le h2, List.take_zero, List.foldlM_nil]
    exact foldlM_eq_pure_init_of_stop_le_start _ _ _ _ _ h2

-- `Array.foldl_eq_foldl_extract` is now in core with the same statement.

theorem foldl_induction'
    {as : Array α} (motive : Nat → β → Prop) {init : β} (start stop : ℕ)
    (h0 : motive start init) (h0' : stop < start → motive stop init)
    (h1 : stop ≤ as.size) {f : β → α → β}
    (hf : ∀ i : Fin as.size, ∀ b, start ≤ i → i < stop
                                  → motive i.1 b → motive (i.1 + 1) (f b as[i])) :
    motive stop (as.foldl f init start stop) := by
  by_cases H : stop < start
  . exact (foldl_eq_init_of_stop_le_start _ _ _ _ _ (le_of_lt H)).substr (h0' H)
  rw [not_lt] at H
  rw [foldl_eq_foldl_extract]
  conv => left; exact Eq.symm (Nat.add_sub_cancel' H)
  have := Eq.symm (Eq.trans size_extract
                            (congrArg (. - start) (min_eq_left h1)))

  convert @foldl_induction α β (as.extract start stop) (motive $ start + .) _ h0 f ?_
  intro ⟨i, hi⟩ b h
  rw [← Nat.add_assoc, Fin.getElem_fin, getElem_extract]
  have H := lt_tsub_iff_left.mp $ lt_of_lt_of_eq hi this.symm
  exact hf ⟨_, lt_of_lt_of_le H h1⟩ b (Nat.le_add_right _ _) H h

lemma foldlM_eq_foldl (f : β → α → m β) (init : β) (as : Array α)
    (start : ℕ := 0) (stop : ℕ := as.size) :
    as.foldlM f init start stop
    = as.foldl (fun mb a => do f (← mb) a) (pure init) start stop := by
  rw [foldlM_eq_foldlM_extract, foldl_eq_foldl_extract,
      ← foldlM_toList, ← foldl_toList]
  exact List.foldlM_eq_foldl _ _ _

lemma prod_mk_foldl (f : β → α → β) (g : γ → α → γ) (b0 : β) (c0 : γ)
    (as : Array α) (start stop : ℕ) :
    (as.foldl f b0 start stop, as.foldl g c0 start stop)
    = as.foldl (fun p a => Prod.map (f . a) (g . a) p) (b0, c0) start stop := by
  simp (config := {singlePass := true}) only [foldl_eq_foldl_extract]
  simp only [← foldl_toList, List.prod_mk_foldl]

-- `Array.foldrM_reverse` and `Array.foldr_reverse` are now in core.

@[inline]
unsafe def foldlIdxMUnsafe (f : ℕ → β → α → m β) (init : β) (as : Array α)
    (start := 0) (stop := as.size) : m β :=
  let rec @[specialize] fold (i : USize) (stop : USize) (b : β) : m β := do
    if i == stop then
      pure b
    else
      fold (i+1) stop (← f (USize.toNat i) b (as.uget i lcProof))
  if start < stop then
    if stop ≤ as.size then
      fold (USize.ofNat start) (USize.ofNat stop) init
    else
      pure init
  else
    pure init

/-
should stuff be in terms of StateM?
-/

@[implemented_by foldlIdxMUnsafe]
def foldlIdxM (f : ℕ → β → α → m β) (init : β) (as : Array α)
    (start := 0) (stop := as.size) : m β :=
  let fold (stop : Nat) (h : stop ≤ as.size) :=
    let rec loop (i : Nat) (j : Nat) (b : β) : m β := do
      if hlt : j < stop then
        match i with
        | 0    => pure b
        | i'+1 =>
          have : j < as.size := Nat.lt_of_lt_of_le hlt h
          loop i' (j+1) (← f j b as[j])
      else
        pure b
    loop (stop - start) start init
  if h : stop ≤ as.size then
    fold stop h
  else
    fold as.size (Nat.le_refl _)

@[reducible] def foldlIdx (f : ℕ → β → α → β) (init : β) (as : Array α)
    (start := 0) (stop := as.size) := Id.run $ foldlIdxM f init as start stop

lemma foldlIdxM_eq_foldlIdxM_upto_min (f : ℕ → β → α → m β) (b : β)
    (as : Array α) (i0 i1 : ℕ) :
    as.foldlIdxM f b i0 i1  = as.foldlIdxM f b i0 (min i1 as.size) := by
  simp only [foldlIdxM, min_le_right, dite_true, dite_eq_iff']
  refine ⟨?_, ?_ ∘ Nat.le_of_not_le⟩ <;> intro h <;> congr <;> refine Eq.symm ?_
  <;> simp only [min_eq_left_iff, min_eq_right_iff, h]

lemma foldlIdx_eq_foldlIdx_upto_min (f : ℕ → β → α → β) (b : β)
    (as : Array α) (i0 i1 : ℕ) :
    as.foldlIdx f b i0 i1  = as.foldlIdx f b i0 (min i1 as.size) :=
  foldlIdxM_eq_foldlIdxM_upto_min (m:=Id) f b as i0 i1

-- pulling an `m`-bind out of an `Id`-valued `foldlIdxM.loop`; this used to be
-- true by `rfl` but now needs the monad laws
private lemma foldlIdxM.loop_bind (f : ℕ → β → α → m β) (as : Array α)
    (stop : ℕ) (h : stop ≤ as.size) (i j : ℕ) (mb : m β) :
    foldlIdxM.loop (m := Id) (β := m β)
        (fun n x a => Bind.bind (m := m) x (f n · a)) as stop h i j mb
    = mb >>= foldlIdxM.loop f as stop h i j := by
  induction i generalizing j mb with
  | zero =>
    have h0 : foldlIdxM.loop f as stop h 0 j = (pure : β → m β) := by
      funext b; rw [foldlIdxM.loop]; split <;> rfl
    rw [foldlIdxM.loop, h0, bind_pure]
    split <;> rfl
  | succ i ih =>
    by_cases hlt : j < stop
    . have hj : j < as.size := Nat.lt_of_lt_of_le hlt h
      have h1 : ∀ b : β, foldlIdxM.loop f as stop h (i + 1) j b
          = f j b as[j] >>= foldlIdxM.loop f as stop h i (j + 1) := by
        intro b; rw [foldlIdxM.loop, dif_pos hlt]
      rw [foldlIdxM.loop, dif_pos hlt]
      refine Eq.trans (ih (j + 1) (mb >>= (f j · as[j]))) ?_
      rw [bind_assoc]
      exact (bind_congr h1).symm
    . have h0 : ∀ b : β, foldlIdxM.loop f as stop h (i + 1) j b = pure b := by
        intro b; rw [foldlIdxM.loop, dif_neg hlt]
      rw [foldlIdxM.loop, dif_neg hlt, bind_congr h0, bind_pure]
      rfl

lemma foldlIdxM_eq_foldlIdx (f : ℕ → β → α → m β) b as i0 i1 :
    foldlIdxM f b as i0 i1
    = foldlIdx (fun n mb a => mb >>= (f n . a)) (pure b) as i0 i1 := by
  rw [foldlIdxM_eq_foldlIdxM_upto_min, foldlIdx_eq_foldlIdx_upto_min]
  generalize H : min i1 (size as) = i1'
  replace H := le_of_eq_of_le H.symm (min_le_right _ _); clear i1
  simp only [foldlIdxM, foldlIdx, Id.run, H, dite_true]
  exact (Eq.trans (foldlIdxM.loop_bind f as i1' H _ i0 (pure b))
                  (pure_bind b _)).symm


lemma foldlIdxM_eq_foldlM (f : ℕ → β → α → m β) (init : β) (as : Array α)
    (start stop : ℕ) :
    as.foldlIdxM f init start stop
    = Prod.snd <$>
      as.foldlM (fun p a => Prod.mk (p.fst + 1) <$> Function.uncurry f p a)
                (start, init) start stop := by
  rw [foldlM_eq_foldlM_upto_min, foldlIdxM_eq_foldlIdxM_upto_min]
  generalize h1 : min stop (size as) = stop'
  replace h1 := le_of_eq_of_le h1.symm (min_le_right _ _); clear stop
  -- simp only [foldlIdxM, min_le_right, dite_true]
  simp only [foldlIdxM, foldlM, Id.run, h1, le_refl, dite_true]
  rcases Nat.le_total start stop' with h2 | h2
  . generalize H : stop' - start = w
    replace H := Nat.eq_add_of_sub_eq h2 H; clear h2; subst H
    induction w generalizing start init with
    | zero =>
      simp only [Nat.zero_add, foldlM.loop, foldlIdxM.loop, lt_irrefl,
                 dite_false, map_pure, Id.run_pure]
    | succ w ih =>
      have H := lt_of_lt_of_le (Nat.lt_succ_self start) (Nat.le_add_left _ w)
      rw [foldlM.loop, foldlIdxM.loop]
      simp only [Nat.succ_add_eq_add_succ] at h1 ⊢
      simp only [H, dite_true, ih, h1, map_bind, seq_bind_eq,
                 Function.uncurry_apply_pair, Function.comp_apply]
  . rw [Nat.sub_eq_zero_of_le h2, foldlIdxM.loop, foldlM.loop]
    simp only [not_lt.mpr h2, dite_false, map_pure]

lemma foldlIdx_eq_foldl (f : ℕ → β → α → β) (init : β) (as : Array α)
    (start stop : ℕ) :
    as.foldlIdx f init start stop
    = (as.foldl (fun p a => (p.fst + 1, f p.fst p.snd a))
                (start, init) start stop).snd :=
  foldlIdxM_eq_foldlM (m := Id) f init as start stop

lemma foldlIdxM_eq_foldl (f : ℕ → β → α → m β) (init : β) (as : Array α)
    (start stop : ℕ) :
    as.foldlIdxM f init start stop
    = (as.foldl (fun p a => (p.fst + 1, p.snd >>= (f p.fst . a)))
                (start, pure init) start stop).snd := by
  refine Eq.trans (foldlIdxM_eq_foldlM f init as start stop) ?_
  -- morally Function.uncurry (Functor.map ∘ Prod.mk) is sequence
  have (x : ℕ × m β) :=
    Eq.trans (congrArg (Prod.snd <$> .)
            $ congrFun (Function.uncurry_def (Functor.map ∘ Prod.mk)) x)
    $ Eq.trans (comp_map _ _ _).symm (id_map _)
  refine Eq.trans (congrArg (Prod.snd <$> .) ?_) (this _); clear this
  rw [foldlM_eq_foldlM_extract, foldlM_eq_foldl, ← foldl_eq_foldl_extract, ← map_pure]
  let C (x : m (ℕ × β) × (ℕ × m β)) :=
    x.fst = Function.uncurry (Functor.map ∘ Prod.mk) x.snd
  refine @Eq.substr _ C _ _ (Array.prod_mk_foldl _ _ _ _ _ _ _) ?_
  rw [foldl_eq_foldl_upto_min]
  apply foldl_induction' (fun _ => C)
  . rfl
  . intro; rfl
  . exact min_le_right _ _
  . intro i ⟨x, y, z⟩ _ _ H
    dsimp only [C, Function.uncurry_apply_pair, Prod.map_apply, Function.comp_apply] at H ⊢
    rw [H, map_bind, seq_bind_eq]
    rfl

lemma foldlIdx_eq_foldlIdx_toList (f : ℕ → β → α → β) (init : β)
    (as : Array α) (start stop : ℕ) :
    as.foldlIdx f init start stop
    = ((as.toList.take stop).drop start).foldlIdx f init start := by
  -- `List.foldlIdxSpec` and `List.enumFrom` are gone from `Mathlib.Data.List.Indexes`,
  -- so the WIP skeleton that used to live here no longer applies.

  admit

end Array

namespace Sum

lemma exists_isLeft {α β} {P : α ⊕ β → Prop} :
    (∃ x, x.isLeft ∧ P x) ↔ (∃ a, P (Sum.inl a)) :=
  Iff.trans (exists_congr $ fun _ =>
    Iff.trans (and_congr_left' isLeft_iff) exists_and_right.symm)
  $ Iff.trans exists_swap $ exists_congr $ fun _ => exists_eq_left

lemma exists_isRight {α β} {P : α ⊕ β → Prop} :
    (∃ x, x.isRight ∧ P x) ↔ (∃ a, P (Sum.inr a)) :=
  Iff.trans (exists_congr $ fun _ =>
    Iff.trans (and_congr_left' isRight_iff) exists_and_right.symm)
  $ Iff.trans exists_swap (exists_congr (fun _ => exists_eq_left))

end Sum
