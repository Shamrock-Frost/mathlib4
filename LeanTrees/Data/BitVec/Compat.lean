/-
Copyright (c) 2023 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
import Mathlib.Data.BitVec
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Bitwise

/-!
# `BitVec` support for `BinAddr`

The original development carried a large `Mathlib/Data/BitVec/Lemmas.lean` of its own.
Nearly all of it has since landed in Lean core, but under the `getLsbD` spelling and
without the `HEq` variants that `BinAddr` needs in order to state facts about vectors
of provably-but-not-definitionally equal widths.

This module supplies only the remainder:

* `BitVec.lsb` and `BitVec.dropLast`, the two operations core still lacks. Note that
  `concat` appends at the *least* significant end, so `dropLast` is a right shift
  rather than a `setWidth`.
* `concatRecOn`, the recursor that lets `BitVec` be consumed like a snoc-list.
* `HEq` forms of the `append` lemmas, whose `Eq` forms in core are stated modulo a
  `BitVec.cast`.
* two `Nat` shift facts. The original development defined its own `Nat.size'`; that is
  just core's `Nat.size`, so only the shift lemmas below are still missing.
-/

namespace Nat

/-- Shifting right by `n - k` is shifting left by `k` and then right by `n`. -/
theorem shiftRight_sub (m : ℕ) {n k : ℕ} (h : k ≤ n) :
    m >>> (n - k) = (m <<< k) >>> n := by
  simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  refine Eq.symm (Eq.trans (congrArg _ (Eq.trans ?_ (Nat.pow_add 2 (n - k) k))) ?_)
  · exact congrArg _ (Nat.sub_add_cancel h).symm
  · exact Nat.mul_div_mul_right _ _ (Nat.two_pow_pos k)

/-- A right shift shrinks the bit width by the shift amount. Stated with truncated
subtraction, so no hypothesis relating `v` and `w` is needed. -/
theorem shiftRight_lt_two_pow_sub {n w v : ℕ} (h : n < 2 ^ w) : n >>> v < 2 ^ (w - v) := by
  rw [Nat.shiftRight_eq_div_pow]
  refine Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_le h ?_)
  rw [← Nat.pow_add]
  exact Nat.pow_le_pow_right (by omega) (by omega)

/-- Shifting right and then left again clears the low `w` bits. -/
theorem shiftRight_shiftLeft_eq (n w : ℕ) : (n >>> w) <<< w = Nat.ldiff n (2 ^ w - 1) := by
  refine eq_of_testBit_eq fun i => ?_
  rw [testBit_shiftLeft, testBit_shiftRight, testBit_ldiff, testBit_two_pow_sub_one]
  rcases Nat.lt_or_ge i w with h | h
  · simp [Nat.not_le.mpr h, h]
  · have hi : w + (i - w) = i := by omega
    simp [Nat.not_lt.mpr h, h, hi]

end Nat

namespace BitVec

universe u

variable {w v u' : ℕ}

/-- The `Nat.size` of a bitvector's value is bounded by its width. -/
theorem toNat_size_le (xs : BitVec w) : Nat.size xs.toNat ≤ w := Nat.size_le.mpr xs.isLt

/-- Proof irrelevance across distinct propositions, in `HEq` form. -/
theorem heq_prop {p q : Prop} (hp : p) (hq : q) : HEq hp hq := proof_irrel_heq hp hq

/-- The least significant bit. -/
@[inline] protected def lsb (xs : BitVec w) : Bool := xs.getLsbD 0

@[simp] theorem lsb_eq_getLsbD (xs : BitVec w) : xs.lsb = xs.getLsbD 0 := rfl

/-- Drop the least significant bit. Inverse to `concat`. -/
def dropLast (xs : BitVec (w + 1)) : BitVec w := (xs >>> 1).setWidth w

@[simp] theorem getLsbD_dropLast (xs : BitVec (w + 1)) (i : ℕ) :
    (dropLast xs).getLsbD i = xs.getLsbD (i + 1) := by
  rcases Nat.lt_or_ge i w with h | h
  · rw [dropLast, getLsbD_setWidth, decide_eq_true h, Bool.true_and, getLsbD_ushiftRight]
    congr 1
    omega
  · rw [dropLast, getLsbD_setWidth]
    rw [decide_eq_false (Nat.not_lt.mpr h), Bool.false_and]
    exact (getLsbD_of_ge xs (i + 1) (Nat.succ_le_succ h)).symm

@[simp] theorem lsb_concat (xs : BitVec w) (b : Bool) : (xs.concat b).lsb = b := by
  simp [BitVec.lsb]

@[simp] theorem dropLast_concat (xs : BitVec w) (b : Bool) :
    dropLast (xs.concat b) = xs := by
  refine eq_of_getLsbD_eq fun i _ => ?_
  simp

@[simp] theorem dropLast_concat_lsb (xs : BitVec (w + 1)) :
    (dropLast xs).concat xs.lsb = xs := by
  refine eq_of_getLsbD_eq fun i _ => ?_
  rw [getLsbD_concat]
  split
  · subst ‹i = 0›; rfl
  · rw [getLsbD_dropLast]
    congr 1
    omega

theorem cast_heq : ∀ (h : w = v) (xs : BitVec w), HEq (BitVec.cast h xs) xs
  | rfl, _ => HEq.refl _

/-- Recursion on a `BitVec` viewed as a snoc-list, peeling off the least significant
bit at each step. -/
@[elab_as_elim]
def concatRecOn {motive : ∀ {w}, BitVec w → Sort*}
    (nil : motive BitVec.nil)
    (concat : ∀ {w} (xs : BitVec w) (x : Bool), motive xs → motive (xs.concat x)) :
    ∀ {w} (x : BitVec w), motive x
  | 0, x => _root_.cast (congrArg motive (eq_nil x).symm) nil
  | _ + 1, x => _root_.cast (congrArg motive <| dropLast_concat_lsb x)
      <| concat x.dropLast x.lsb <| concatRecOn nil concat x.dropLast

@[simp] theorem concatRecOn_nil {motive : ∀ {w}, BitVec w → Sort*}
    (nil : motive BitVec.nil)
    (concat : ∀ {w} (xs : BitVec w) (x : Bool), motive xs → motive (xs.concat x)) :
    concatRecOn nil concat BitVec.nil = nil := rfl

@[simp] theorem concatRecOn_concat {motive : ∀ {w}, BitVec w → Sort*}
    (nil : motive BitVec.nil)
    (concat : ∀ {w} (xs : BitVec w) (x : Bool), motive xs → motive (xs.concat x))
    (v : BitVec w) (b : Bool) :
    concatRecOn nil concat (v.concat b) = concat v b (concatRecOn nil concat v) :=
  cast_eq_iff_heq.mpr <| by
    congr <;> first
      | exact dropLast_concat v b
      | exact lsb_concat v b

@[simp] theorem reverse_reverse (xs : BitVec w) : reverse (reverse xs) = xs := by
  refine eq_of_getLsbD_eq fun i hi => ?_
  rw [getLsbD_reverse, getMsbD_reverse]

/-!
### `HEq` forms of the `append` lemmas

Core states these modulo a `BitVec.cast`; `BinAddr` needs them as `HEq`s so that they
can be composed with `BinAddr.ext`.
-/

/-- Additive form of `toNat_append`: the two halves occupy disjoint bit ranges, so the
bitwise `or` in core's statement is an addition. -/
theorem toNat_append' {m n : ℕ} (x : BitVec m) (y : BitVec n) :
    (x ++ y).toNat = x.toNat * 2 ^ n + y.toNat := by
  rw [toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]

theorem append_nil_heq (xs : BitVec w) : HEq (xs ++ BitVec.nil) xs := by
  refine HEq.trans (cast_heq (Nat.add_zero w) (xs ++ BitVec.nil)).symm
    (heq_of_eq (eq_of_getLsbD_eq fun i _ => ?_))
  rw [getLsbD_cast, getLsbD_append]
  simp

theorem nil_append_heq (xs : BitVec w) : HEq (BitVec.nil ++ xs) xs := by
  refine HEq.trans (cast_heq (Nat.zero_add w) (BitVec.nil ++ xs)).symm
    (heq_of_eq (eq_of_getLsbD_eq fun i hi => ?_))
  rw [getLsbD_cast, getLsbD_append]
  simp [hi]

theorem append_assoc_heq (xs : BitVec w) (ys : BitVec v) (zs : BitVec u') :
    HEq (xs ++ ys ++ zs) (xs ++ (ys ++ zs)) :=
  HEq.trans (heq_of_eq append_assoc) (cast_heq _ _)

theorem append_concat_heq (b : Bool) (xs : BitVec w) (ys : BitVec v) :
    HEq (xs ++ ys.concat b) ((xs ++ ys).concat b) := by
  refine HEq.trans (cast_heq (Nat.add_succ w v) (xs ++ ys.concat b)).symm
    (heq_of_eq (eq_of_getLsbD_eq fun i _ => ?_))
  simp only [getLsbD_cast, getLsbD_append, getLsbD_concat]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega)

theorem reverse_concat (b : Bool) (xs : BitVec w) :
    reverse (xs.concat b) = cons b (reverse xs) := by
  refine eq_of_getLsbD_eq fun i hi => ?_
  simp only [getLsbD_reverse, getMsbD_concat, getLsbD_cons]
  rcases Nat.lt_or_ge i w with h | h
  · simp [h, Nat.ne_of_lt h]
  · have hw : i = w := by omega
    subst hw
    simp

theorem reverse_cons (b : Bool) (xs : BitVec w) :
    reverse (cons b xs) = (reverse xs).concat b := by
  have h := reverse_concat b (reverse xs)
  rw [reverse_reverse] at h
  rw [← h, reverse_reverse]

theorem reverse_append_heq (xs : BitVec w) (ys : BitVec v) :
    HEq (reverse (xs ++ ys)) (reverse ys ++ reverse xs) := by
  refine HEq.trans (cast_heq (Nat.add_comm w v) (reverse (xs ++ ys))).symm
    (heq_of_eq (eq_of_getLsbD_eq fun i _ => ?_))
  simp only [getLsbD_cast, getLsbD_reverse, getLsbD_append, getMsbD_append]
  split_ifs <;> first | rfl | (exfalso; omega)

end BitVec
