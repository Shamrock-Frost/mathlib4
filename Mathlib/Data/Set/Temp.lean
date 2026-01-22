import Mathlib.Data.Set.Lattice.Image
import Mathlib.Data.Set.Disjoint

noncomputable section

open Classical Function Set

universe u v

variable {α : Type u} {β : Type v} (f : α → β) (g : β → α)

def ring : ℕ → Set α
  | 0     => (range g)ᶜ
  | n + 1 => g '' (f '' ring n)

def rings : Set α := ⋃ n, ring f g n

def inner_map : α → α := Set.piecewise (rings f g) (g ∘ f) id

lemma ring_succ {x : α} (n : ℕ) : x ∈ ring f g n → g (f x) ∈ ring f g (n + 1) :=
  mem_image_of_mem g ∘ mem_image_of_mem f

lemma comp_fixes_rings : (g ∘ f) '' rings f g ⊆ rings f g := by
  rw [image_comp, rings, image_iUnion, image_iUnion]
  exact sSup_le_sSup (range_comp_subset_range Nat.succ (ring f g))

lemma range_piecewise (s) (p q : α → β) : range (piecewise s p q) = p '' s ∪ q '' sᶜ := by
  simp_rw [← range_restrict, ← restrict_piecewise p q, ← restrict_piecewise_compl p q,
    range_restrict, image_union_image_compl_eq_range]

lemma piecewise_inj (s : Set α) {p q : α → β} (hp : p.Injective) (hq : q.Injective)
    (hpq : Disjoint (p '' s) (q '' sᶜ)) : Function.Injective (piecewise s p q) := by
  intro x y
  simp only [piecewise, ite_eq_iff, eq_ite_iff, and_or_left, and_assoc, or_imp]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro ⟨h1, h2, h3⟩
  · exact hp h3
  · exact absurd h3.symm (hpq.ne_of_mem (mem_image_of_mem _ h1) (mem_image_of_mem _ h2))
  · exact absurd h3      (hpq.ne_of_mem (mem_image_of_mem _ h2) (mem_image_of_mem _ h1))
  · exact hq h3

lemma inner_map_range_subset_range : range (inner_map f g) ⊆ range g := by
  rw [inner_map, range_piecewise, image_id, image_comp]
  refine union_subset (image_subset_range g _) ?_
  refine subset_of_eq_of_subset (compl_iUnion _) ?_
  exact  subset_of_subset_of_eq (iInter_subset _ 0) (compl_compl _)

lemma inner_map_range_eq_range : range (inner_map f g) = range g := by
  refine subset_antisymm (inner_map_range_subset_range _ _) ?_
  intro x hx
  by_cases hx' : x ∈ rings f g
  · obtain ⟨_, ⟨n, rfl⟩, h2⟩ := hx'
    cases n with
    | zero => exact absurd hx (mem_compl h2)
    | succ n =>
      obtain ⟨_, ⟨z, h, rfl⟩, rfl⟩ := h2
      exact mem_range.mpr ⟨z, ite_eq_left_iff.mpr (absurd (mem_iUnion_of_mem n h))⟩
  · exact mem_range.mpr ⟨x, ite_eq_right_iff.mpr hx'.elim⟩

lemma inner_map_inj (hf : Injective f) (hg : Injective g) : Injective (inner_map f g) :=
  piecewise_inj _ (hg.comp hf) injective_id <|
    image_id _ ▸ disjoint_compl_right_iff_subset.mpr (comp_fixes_rings f g)

variable [Nonempty β]

def sb_map : α → β := invFun g ∘ inner_map f g

lemma sb_map_inj (hf : Injective f) (hg : Injective g) : Injective <| sb_map f g := by
  rw [sb_map, InjOn.injective_iff _ _ (inner_map_range_subset_range f g)]
  · exact inner_map_inj f g hf hg
  · exact Injective.injOn_range (Function.invFun_comp hg ▸ injective_id)

lemma sb_map_surj (hg : Injective g) : Surjective <| sb_map f g := by
  rw [sb_map, ← Set.surjOn_univ, Set.surjOn_comp_iff, image_univ, inner_map_range_eq_range]
  exact ((Function.leftInverse_invFun hg).leftInvOn univ).surjOn (mapsTo_range g univ)

theorem schroeder_bernstein {f : α → β} {g : β → α} (hf : Injective f) (hg : Injective g) :
    ∃ h : α → β, Bijective h := ⟨sb_map f g, sb_map_inj f g hf hg, sb_map_surj f g hg⟩

end
