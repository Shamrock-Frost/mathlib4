import Mathlib.GroupTheory.Index
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Order.Atoms
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace Subgroup

open QuotientGroup

variable {G : Type*} [Group G] {H : Subgroup G}

lemma eq_of_le_of_index_eq_of_nz {K : Subgroup G} (h1 : H ≤ K) (h2 : H.index = K.index)
    (h3 : K.index ≠ 0) : H = K :=
  le_antisymm h1 <| relIndex_eq_one.mp <| (Nat.mul_eq_right h3).mp <|
    Eq.trans (relIndex_mul_index h1) h2

lemma prime_index_is_coatom (h1 : H.index.Prime) : IsCoatom H :=
  ⟨mt (congr_arg _) (ne_of_ne_of_eq h1.ne_one index_top.symm), fun _ h2 =>
    index_eq_one.mp <| ((Nat.dvd_prime h1).mp (index_dvd_of_le h2.le)).resolve_right <| fun h3 =>
      h2.ne <| eq_of_le_of_index_eq_of_nz h2.le h3.symm <| ne_of_eq_of_ne h3 h1.ne_zero⟩

theorem sup_normal_of_prime_index {p} (hp : p.Prime) [H.Normal] (hH : H.index = p)
    (K : Subgroup G) : K ≤ H ∨ (⊤ = H ⊔ K ∧ (H ⊓ K).relIndex K = p) := by
  refine or_iff_not_imp_left.mpr ?_
  intro hK
  have := Eq.symm <| And.right (prime_index_is_coatom (hH ▸ hp)) _ <|
      lt_iff_le_and_ne.mpr ⟨le_sup_left, (hK <| le_of_sup_eq' <| Eq.symm · )⟩
  refine ⟨this, (Nat.card_congr ?_).trans <| H.relIndex_top_right.trans hH⟩
  refine Equiv.trans (quotientEquivOfEq (inf_subgroupOf_right H K)) ?_
  refine Equiv.trans (quotientInfEquivProdNormalQuotient K H).toEquiv (MulEquiv.toEquiv ?_)

  replace this := (sup_comm _ _).trans this.symm
  refine QuotientGroup.congr (H.subgroupOf _) (H.subgroupOf _) (MulEquiv.subgroupCongr this) ?_
  ext ⟨x⟩
  simp only [mem_map, mem_subgroupOf, MonoidHom.coe_coe, Subtype.ext_iff,
    MulEquiv.subgroupCongr_apply, Subtype.exists, this, mem_top, exists_const, exists_eq_right]


end Subgroup
