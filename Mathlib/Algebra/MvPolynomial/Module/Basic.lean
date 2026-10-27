/-
Copyright (c) 2024 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
module

public import Mathlib.Algebra.MvPolynomial.Module.AEval
public import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Multivariate polynomial modules

In this file we define the multivariate polynomial module of an `R`-module `M`, with variables
indexed by an arbitrary (possibly infinite) type `σ`. Mathematically this is the module
$M[X_i : i ∈ σ]$ over $R[X_i : i ∈ σ]$.

This is the multivariate analogue of `PolynomialModule`; see the docstring there for why this is
a separate type rather than `MvPolynomial σ M` or `(σ →₀ ℕ) →₀ M`.

## Main definitions

* `MvPolynomialModule σ R M`: the `MvPolynomial σ R`-module `M[X_i : i ∈ σ]`.
* `MvPolynomialModule.single R a m`: the monomial `m X^a`.
* `MvPolynomialModule.equivPolynomialSelf`: `MvPolynomialModule σ R R ≃ MvPolynomial σ R`
  as `MvPolynomial σ R`-modules.
* `MvPolynomialModule.map`: the map `M[X] → M'[X]` induced by a linear map `M → M'`.
* `MvPolynomialModule.eval`: evaluation at a point `T : σ → R`.
* `MvPolynomialModule.comp`: substitution of polynomials `P : σ → MvPolynomial τ R` for the
  variables.
-/

@[expose] public noncomputable section

open MvPolynomial

/-- The `MvPolynomial σ R`-module `M[X_i : i ∈ σ]` for an `R`-module `M`.
This is isomorphic (as an `R`-module) to `MvPolynomial σ M` when `M` is a ring.

We require all the module instances `Module S (MvPolynomialModule σ R M)` to factor through `R`
except `Module (MvPolynomial σ R) (MvPolynomialModule σ R M)`.
This is also the reason why `R` is included in the alias, or else there would be two different
instances of `Module (MvPolynomial σ R) (MvPolynomialModule σ (MvPolynomial σ R))`. -/
@[nolint unusedArguments]
structure MvPolynomialModule (σ R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M] where
  /-- Construct an element of `M[X_i : i ∈ σ]` from its coefficients `(σ →₀ ℕ) →₀ M`. -/
  ofCoeff (R) ::
  /-- The coefficients `(σ →₀ ℕ) →₀ M` of an element of `M[X_i : i ∈ σ]`. -/
  coeff : (σ →₀ ℕ) →₀ M

variable {ι σ τ R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {S : Type*} [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M]

namespace MvPolynomialModule

variable {x y : MvPolynomialModule σ R M}

lemma coeff_ofCoeff (x : (σ →₀ ℕ) →₀ M) : (ofCoeff R x).coeff = x := rfl
lemma ofCoeff_coeff (x : MvPolynomialModule σ R M) : ofCoeff R x.coeff = x := rfl

variable (σ R M) in
/-- `MvPolynomialModule.coeff` as an equiv. -/
@[simps! apply symm_apply]
def coeffEquiv : MvPolynomialModule σ R M ≃ ((σ →₀ ℕ) →₀ M) where
  toFun := coeff
  invFun := ofCoeff R
  left_inv _ := rfl
  right_inv _ := rfl

lemma «forall» {P : MvPolynomialModule σ R M → Prop} : (∀ p, P p) ↔ ∀ q, P (ofCoeff R q) :=
  (coeffEquiv σ R M).forall_congr_left

lemma «exists» {P : MvPolynomialModule σ R M → Prop} : (∃ p, P p) ↔ ∃ q, P (ofCoeff R q) :=
  (coeffEquiv σ R M).exists_congr_left

lemma coeff_injective : (coeff : MvPolynomialModule σ R M → (σ →₀ ℕ) →₀ M).Injective :=
  (coeffEquiv σ R M).injective

lemma ofCoeff_injective : (ofCoeff R : ((σ →₀ ℕ) →₀ M) → MvPolynomialModule σ R M).Injective :=
  (coeffEquiv σ R M).symm.injective

@[simp]
lemma coeff_inj : x.coeff = y.coeff ↔ x = y := coeff_injective.eq_iff

lemma ofCoeff_inj {x y : (σ →₀ ℕ) →₀ M} : ofCoeff R x = ofCoeff R y ↔ x = y :=
  ofCoeff_injective.eq_iff

@[ext] alias ⟨ext, _⟩ := coeff_inj

instance instInhabited : Inhabited (MvPolynomialModule σ R M) := fast_instance%
  (coeffEquiv σ R M).inhabited

instance instNontrivial [Nontrivial M] : Nontrivial (MvPolynomialModule σ R M) :=
  (coeffEquiv σ R M).nontrivial

instance instUnique [Subsingleton M] : Unique (MvPolynomialModule σ R M) := fast_instance%
  (coeffEquiv σ R M).unique

instance instDecidableEq [DecidableEq σ] [DecidableEq M] :
    DecidableEq (MvPolynomialModule σ R M) :=
  (coeffEquiv σ R M).decidableEq

instance instAddCommMonoid : AddCommMonoid (MvPolynomialModule σ R M) := fast_instance%
  (coeffEquiv σ R M).addCommMonoid

instance instAddCommGroup {M : Type*} [AddCommGroup M] [Module R M] :
    AddCommGroup (MvPolynomialModule σ R M) := fast_instance%
  (coeffEquiv σ R M).addCommGroup

/-- `MvPolynomialModule.coeff` as an `AddEquiv`. -/
@[simps! apply symm_apply]
def coeffAddEquiv : MvPolynomialModule σ R M ≃+ ((σ →₀ ℕ) →₀ M) := (coeffEquiv σ R M).addEquiv

@[simp] lemma coeff_zero : coeff (0 : MvPolynomialModule σ R M) = 0 := rfl
@[simp] lemma ofCoeff_zero : (ofCoeff R 0 : MvPolynomialModule σ R M) = 0 := rfl
@[simp] lemma coeff_eq_zero : coeff x = 0 ↔ x = 0 := coeff_inj
@[simp] lemma ofCoeff_eq_zero {x : (σ →₀ ℕ) →₀ M} : ofCoeff R x = 0 ↔ x = 0 := ofCoeff_inj

@[simp] lemma coeff_add (x y : MvPolynomialModule σ R M) : coeff (x + y) = coeff x + coeff y :=
  rfl

@[simp] lemma ofCoeff_add (x y : (σ →₀ ℕ) →₀ M) :
    ofCoeff R (x + y) = ofCoeff R x + ofCoeff R y := rfl

@[simp]
lemma coeff_sum (s : Finset ι) (f : ι → MvPolynomialModule σ R M) :
    coeff (∑ i ∈ s, f i) = ∑ i ∈ s, coeff (f i) := map_sum coeffAddEquiv ..

@[simp]
lemma ofCoeff_sum (s : Finset ι) (f : ι → (σ →₀ ℕ) →₀ M) :
    ofCoeff R (∑ i ∈ s, f i) = ∑ i ∈ s, ofCoeff R (f i) := map_sum coeffAddEquiv.symm ..

variable (R) in
/-- `single R a m` is the monomial `m X^a`. -/
def single (a : σ →₀ ℕ) (m : M) : MvPolynomialModule σ R M := .ofCoeff R <| .single a m

@[simp] lemma coeff_single (a : σ →₀ ℕ) (m : M) : (single R a m).coeff = .single a m := rfl
@[simp] lemma ofCoeff_single (a : σ →₀ ℕ) (m : M) : ofCoeff R (.single a m) = single R a m := rfl

@[simp] lemma single_zero (a : σ →₀ ℕ) : single R a (0 : M) = 0 := by
  simp [single, -ofCoeff_single]

@[simp]
lemma single_eq_zero {a : σ →₀ ℕ} {m : M} : single R a m = 0 ↔ m = 0 := by
  rw [← coeff_eq_zero, coeff_single, Finsupp.single_eq_zero]

@[simp]
lemma single_add (a : σ →₀ ℕ) (m₁ m₂ : M) :
    single R a (m₁ + m₂) = single R a m₁ + single R a m₂ := by ext; simp

/-- This is required to have the `IsScalarTower S R M` instance to avoid diamonds. -/
instance : Module S (MvPolynomialModule σ R M) := coeffAddEquiv.module _

instance : IsScalarTower S R (MvPolynomialModule σ R M) := coeffAddEquiv.isScalarTower _ _

omit [Algebra S R] [IsScalarTower S R M] in
@[simp] lemma coeff_smul (s : S) (x : MvPolynomialModule σ R M) : (s • x).coeff = s • x.coeff :=
  rfl

variable (R S) in
/-- `MvPolynomialModule.coeff` as a linear equiv. -/
@[simps! apply symm_apply]
def coeffLinearEquiv : MvPolynomialModule σ R M ≃ₗ[S] (σ →₀ ℕ) →₀ M :=
  (coeffAddEquiv (M := M)).linearEquiv S

variable (R) in
/-- `MvPolynomialModule.single` as a linear map. -/
def lsingle (a : σ →₀ ℕ) : M →ₗ[R] MvPolynomialModule σ R M :=
  (coeffLinearEquiv R R).symm.toLinearMap ∘ₗ Finsupp.lsingle a

@[simp] lemma lsingle_apply (a : σ →₀ ℕ) (m : M) : lsingle R a m = single R a m := rfl

theorem single_smul (a : σ →₀ ℕ) (r : R) (m : M) : single R a (r • m) = r • single R a m :=
  (lsingle R a).map_smul r m

@[elab_as_elim]
lemma induction_linear {p : MvPolynomialModule σ R M → Prop} (x : MvPolynomialModule σ R M)
    (zero : p 0) (add : ∀ x y : MvPolynomialModule σ R M, p x → p y → p (x + y))
    (single : ∀ a m, p (single R a m)) : p x :=
  Finsupp.induction_linear (motive := (p <| ofCoeff R ·)) x.coeff zero (fun _ _ ↦ add _ _)
    (fun _ _ ↦ single _ _)

/-- Two `R`-linear maps from `MvPolynomialModule σ R M` which are equal after pre-composition
with every `lsingle R a` are equal. -/
@[ext high]
theorem hom_ext {M' : Type*} [AddCommMonoid M'] [Module R M']
    {f g : MvPolynomialModule σ R M →ₗ[R] M'}
    (h : ∀ a, f ∘ₗ lsingle R a = g ∘ₗ lsingle R a) : f = g := by
  simpa [← DFunLike.coe_fn_eq, funext_iff, MvPolynomialModule.forall] using Finsupp.lhom_ext'
    (φ := f.comp (coeffLinearEquiv R R).symm.toLinearMap)
    (ψ := g.comp (coeffLinearEquiv R R (M := M)).symm.toLinearMap) h

/-! ### The `MvPolynomial σ R`-module structure -/

variable (σ R M) in
/-- Multiplication by the variable `X i`, as an `R`-linear endomorphism of
`MvPolynomialModule σ R M`. -/
def mulX (i : σ) : MvPolynomialModule σ R M →ₗ[R] MvPolynomialModule σ R M :=
  (coeffLinearEquiv R R).symm.toLinearMap ∘ₗ Finsupp.lmapDomain M R (· + Finsupp.single i 1) ∘ₗ
    (coeffLinearEquiv R R).toLinearMap

lemma mulX_single (i : σ) (a : σ →₀ ℕ) (m : M) :
    mulX σ R M i (single R a m) = single R (a + Finsupp.single i 1) m := by
  simp [mulX, single, -ofCoeff_single]

lemma commute_mulX : Pairwise fun i j ↦ Commute (mulX σ R M i) (mulX σ R M j) := by
  intro i j _
  refine hom_ext fun a ↦ LinearMap.ext fun m ↦ ?_
  simp [Module.End.mul_apply, mulX_single, add_right_comm]

instance polynomialModule : Module (MvPolynomial σ R) (MvPolynomialModule σ R M) :=
  inferInstanceAs <| Module (MvPolynomial σ R) <| Module.MvAEval' (mulX σ R M) commute_mulX

instance isScalarTower' : IsScalarTower S (MvPolynomial σ R) (MvPolynomialModule σ R M) := by
  have : IsScalarTower R (MvPolynomial σ R) (MvPolynomialModule σ R M) :=
    inferInstanceAs <| IsScalarTower R (MvPolynomial σ R) <|
      Module.MvAEval' (mulX σ R M) commute_mulX
  constructor
  intro x y z
  rw [← @IsScalarTower.algebraMap_smul S R, ← @IsScalarTower.algebraMap_smul S R, smul_assoc]

lemma X_smul (i : σ) (x : MvPolynomialModule σ R M) :
    (X i : MvPolynomial σ R) • x = mulX σ R M i x :=
  Module.MvAEval'.X_smul_of (Φ := mulX σ R M) (h := commute_mulX) i x

@[simp]
lemma C_smul (r : R) (x : MvPolynomialModule σ R M) : (C r : MvPolynomial σ R) • x = r • x :=
  Module.MvAEval.C_smul (M := MvPolynomialModule σ R M) _ r x

lemma X_smul_single (i : σ) (a : σ →₀ ℕ) (m : M) :
    (X i : MvPolynomial σ R) • single R a m = single R (a + Finsupp.single i 1) m := by
  rw [X_smul, mulX_single]

lemma X_pow_smul_single (i : σ) (e : ℕ) (a : σ →₀ ℕ) (m : M) :
    (X i ^ e : MvPolynomial σ R) • single R a m = single R (a + Finsupp.single i e) m := by
  induction e generalizing a with
  | zero => simp
  | succ e ih =>
    rw [pow_succ', mul_smul, ih, X_smul_single, add_assoc, ← Finsupp.single_add]

@[simp]
theorem monomial_smul_single (a : σ →₀ ℕ) (r : R) (b : σ →₀ ℕ) (m : M) :
    monomial a r • single R b m = single R (a + b) (r • m) := by
  induction a using Finsupp.induction generalizing b with
  | zero => simp [single_smul]
  | single_add i e a _ _ ih =>
    rw [monomial_single_add, mul_smul, ih, X_pow_smul_single, add_comm _ a, add_right_comm]

@[simp]
theorem monomial_smul_apply (b : σ →₀ ℕ) (r : R) (g : MvPolynomialModule σ R M) (a : σ →₀ ℕ) :
    (monomial b r • g).coeff a = if b ≤ a then r • g.coeff (a - b) else 0 := by
  classical
  induction g using induction_linear with
  | zero => simp
  | add p q hp hq => simp [smul_add, hp, hq, ite_add_ite]
  | single c m =>
    simp only [monomial_smul_single, coeff_single, Finsupp.single_apply]
    by_cases h : b ≤ a
    · obtain ⟨d, rfl⟩ := exists_add_of_le h
      simp [smul_ite]
    · have : b + c ≠ a := by rintro rfl; exact h le_self_add
      simp [h, this]

@[simp]
theorem smul_single_apply (b : σ →₀ ℕ) (f : MvPolynomial σ R) (m : M) (a : σ →₀ ℕ) :
    (f • single R b m).coeff a = if b ≤ a then f.coeff (a - b) • m else 0 := by
  induction f using MvPolynomial.induction_on' with
  | monomial c r =>
    classical
    rw [monomial_smul_single, coeff_single, Finsupp.single_apply, MvPolynomial.coeff_monomial]
    by_cases h : b ≤ a
    · obtain ⟨d, rfl⟩ := exists_add_of_le h
      simp [add_comm c b, ite_smul]
    · have : c + b ≠ a := by rintro rfl; exact h le_add_self
      simp [h, this]
  | add p q hp hq => simp [add_smul, hp, hq, ite_add_ite]

theorem smul_apply [DecidableEq σ] (f : MvPolynomial σ R) (g : MvPolynomialModule σ R M)
    (a : σ →₀ ℕ) :
    (f • g).coeff a = ∑ x ∈ Finset.antidiagonal a, f.coeff x.1 • g.coeff x.2 := by
  induction f using MvPolynomial.induction_on' with
  | monomial b r =>
    simp only [monomial_smul_apply, MvPolynomial.coeff_monomial, ite_smul, zero_smul]
    split_ifs with h
    · rw [Finset.sum_eq_single (b, a - b) (fun x hx hne ↦ ?_) (fun hn ↦ ?_)]
      · simp
      · rw [Finset.mem_antidiagonal] at hx
        have : b ≠ x.1 := fun hb ↦ hne <| Prod.ext hb.symm <| by
          rw [← hx, ← hb, add_tsub_cancel_left]
        simp [this]
      · exact (hn (by simp [Finset.mem_antidiagonal, add_tsub_cancel_of_le h])).elim
    · refine (Finset.sum_eq_zero fun x hx ↦ ?_).symm
      rw [Finset.mem_antidiagonal] at hx
      have : b ≠ x.1 := by rintro rfl; exact h (hx ▸ le_self_add)
      simp [this]
  | add p q hp hq => simp [add_smul, hp, hq, ← Finset.sum_add_distrib]

/-! ### Comparison with `MvPolynomial` -/

/-- `MvPolynomialModule σ R R` is isomorphic to `MvPolynomial σ R` as an
`MvPolynomial σ R`-module. -/
def equivPolynomialSelf : MvPolynomialModule σ R R ≃ₗ[MvPolynomial σ R] MvPolynomial σ R where
  toAddEquiv := coeffAddEquiv.trans AddMonoidAlgebra.coeffAddEquiv.symm
  map_smul' f x := by
    induction x using induction_linear with
    | zero => simp
    | add _ _ hp hq => simp_all [smul_add, mul_add]
    | single a r =>
      ext b
      change (f • single R a r).coeff b = (f * monomial a r).coeff b
      rw [smul_single_apply, MvPolynomial.coeff_mul_monomial', smul_eq_mul]

/-- `MvPolynomialModule σ R S` is isomorphic to `MvPolynomial σ S` as an `R`-module. -/
def equivPolynomial {S : Type*} [CommSemiring S] [Algebra R S] :
    MvPolynomialModule σ R S ≃ₗ[R] MvPolynomial σ S where
  toAddEquiv := coeffAddEquiv.trans AddMonoidAlgebra.coeffAddEquiv.symm
  map_smul' _ _ := rfl

@[simp]
lemma equivPolynomialSelf_apply_eq (p : MvPolynomialModule σ R R) :
    equivPolynomialSelf p = equivPolynomial p := rfl

@[simp]
lemma equivPolynomial_single {S : Type*} [CommSemiring S] [Algebra R S] (a : σ →₀ ℕ) (x : S) :
    equivPolynomial (single R a x) = monomial a x := rfl

@[simp]
lemma equivPolynomial_symm_monomial {S : Type*} [CommSemiring S] [Algebra R S]
    (a : σ →₀ ℕ) (x : S) : equivPolynomial.symm (monomial a x) = single R a x := rfl

/-! ### Functoriality, evaluation and substitution -/

variable (R' : Type*) {M' : Type*} [CommSemiring R'] [AddCommMonoid M'] [Module R' M']
variable [Module R M']

/-- The image of a polynomial under a linear map. -/
def map (f : M →ₗ[R] M') : MvPolynomialModule σ R M →ₗ[R] MvPolynomialModule σ R' M' :=
  (coeffLinearEquiv ..).symm.toLinearMap ∘ₗ (Finsupp.mapRange.linearMap f) ∘ₗ
    (coeffLinearEquiv ..).toLinearMap

@[simp]
theorem map_single (f : M →ₗ[R] M') (a : σ →₀ ℕ) (m : M) :
    map R' f (single R a m) = single R' a (f m) := by simp [map]

variable [Algebra R R'] [IsScalarTower R R' M']

theorem map_smul (f : M →ₗ[R] M') (p : MvPolynomial σ R) (q : MvPolynomialModule σ R M) :
    map R' f (p • q) = p.map (algebraMap R R') • map R' f q := by
  induction q using induction_linear with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add f g e₁ e₂ => rw [smul_add, map_add, e₁, e₂, map_add, smul_add]
  | single a m =>
    induction p using MvPolynomial.induction_on' with
    | add _ _ e₁ e₂ => simp only [add_smul, map_add, e₁, e₂]
    | monomial => rw [monomial_smul_single, map_single, MvPolynomial.map_monomial, map_single,
        monomial_smul_single, f.map_smul, algebraMap_smul]

/-- Evaluate `p : MvPolynomialModule σ R M` at a point `T : σ → R`. -/
@[simps! -isSimp]
def eval (T : σ → R) : MvPolynomialModule σ R M →ₗ[R] M where
  toFun p := p.coeff.sum fun a m ↦ (a.prod fun i e ↦ T i ^ e) • m
  map_add' _ _ := Finsupp.sum_add_index' (fun _ ↦ smul_zero _) fun _ _ _ ↦ smul_add _ _ _
  map_smul' s p := by
    rw [coeff_smul, Finsupp.sum_smul_index' fun _ ↦ smul_zero _, RingHom.id_apply,
      Finsupp.smul_sum]
    simp_rw [smul_comm s]

@[simp]
theorem eval_single (T : σ → R) (a : σ →₀ ℕ) (m : M) :
    eval T (single R a m) = (a.prod fun i e ↦ T i ^ e) • m :=
  Finsupp.sum_single_index (smul_zero _)

@[simp]
theorem eval_smul (p : MvPolynomial σ R) (q : MvPolynomialModule σ R M) (T : σ → R) :
    eval T (p • q) = p.eval T • eval T q := by
  induction q using induction_linear with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add f g e₁ e₂ => rw [smul_add, map_add, e₁, e₂, map_add, smul_add]
  | single b m =>
    induction p using MvPolynomial.induction_on' with
    | add _ _ e₁ e₂ => rw [add_smul, map_add, MvPolynomial.eval_add, e₁, e₂, add_smul]
    | monomial a r =>
      rw [monomial_smul_single, eval_single, MvPolynomial.eval_monomial, eval_single,
        Finsupp.prod_add_index' (fun _ ↦ pow_zero _) (fun _ _ _ ↦ pow_add _ _ _)]
      simp only [smul_smul]
      ring_nf

@[simp]
theorem eval_map (f : M →ₗ[R] M') (q : MvPolynomialModule σ R M) (T : σ → R) :
    eval (algebraMap R R' ∘ T) (map R' f q) = f (eval T q) := by
  induction q using induction_linear with
  | zero => simp_rw [map_zero]
  | add f g e₁ e₂ => simp_rw [map_add, e₁, e₂]
  | single a m =>
    simp only [map_single, eval_single, f.map_smul, Function.comp_apply, ← map_pow,
      ← map_finsuppProd, algebraMap_smul]

@[simp]
theorem eval_map' (f : M →ₗ[R] M) (q : MvPolynomialModule σ R M) (T : σ → R) :
    eval T (map R f q) = f (eval T q) :=
  eval_map R f q T

/-- `comp P q` substitutes the family `P : σ → MvPolynomial τ R` for the variables of
`q : MvPolynomialModule σ R M`, i.e. it is `q(X i ↦ P i)`. See `MvPolynomial.bind₁`. -/
@[simps!]
def comp (P : σ → MvPolynomial τ R) :
    MvPolynomialModule σ R M →ₗ[R] MvPolynomialModule τ R M :=
  (eval P).restrictScalars R ∘ₗ map (MvPolynomial τ R) (lsingle R 0)

theorem comp_single (P : σ → MvPolynomial τ R) (a : σ →₀ ℕ) (m : M) :
    comp P (single R a m) = (a.prod fun i e ↦ P i ^ e) • single R 0 m := by
  rw [comp_apply, map_single, eval_single, lsingle_apply]

theorem comp_eval (P : σ → MvPolynomial τ R) (q : MvPolynomialModule σ R M) (T : τ → R) :
    eval T (comp P q) = eval (fun i ↦ (P i).eval T) q := by
  induction q using induction_linear with
  | zero => simp_rw [map_zero]
  | add _ _ e₁ e₂ => simp_rw [map_add, e₁, e₂]
  | single a m =>
    rw [comp_single, eval_smul, eval_single, eval_single, Finsupp.prod_zero_index, one_smul,
      map_finsuppProd]
    simp only [map_pow]

theorem comp_smul (P : σ → MvPolynomial τ R) (p : MvPolynomial σ R)
    (q : MvPolynomialModule σ R M) : comp P (p • q) = bind₁ P p • comp P q := by
  rw [comp_apply, map_smul, eval_smul, bind₁, aeval_def, MvPolynomial.eval_map, comp_apply]

end MvPolynomialModule
