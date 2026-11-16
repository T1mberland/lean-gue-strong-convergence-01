import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic

/-!
# Strictly upper-triangular word matrices and their geometric inverses

This file formalizes §2.1 of the linearization handoff: for a (possibly
noncommutative) ring `R`, a family of "generators" `x : I → R`, and a word
`w : List I`, the **shift matrix** `shiftMatrix x w` is the strictly
upper-triangular `(length w + 1) × (length w + 1)` matrix whose only nonzero
entries are

`(shiftMatrix x w) i (i+1) = x (w[i])`.

Its powers are computed exactly by `shiftMatrix_pow_apply`, its nilpotence
`(shiftMatrix x w) ^ (length w + 1) = 0` follows, the finite geometric series
`∑_{i ≤ length w} (shiftMatrix x w)^i` is the explicit two-sided inverse of
`1 - shiftMatrix x w`, and the ordered-word extraction identity
`shiftMatrix_pow_extract` recovers `x (w[0]) * ... * x (w[k-1])` in the top-right
corner.

No commutativity of `R` is used, and the word order is preserved by working with
`List.prod` rather than `Finset.prod`.
-/

namespace GUEStrongConvergence

open Matrix

variable {R : Type*} [Ring R] {I : Type*}

/-- The strictly upper-triangular "shift" matrix of a word `w`: its only nonzero
entries are `(shiftMatrix x w) i (i+1) = x (w[i])`. -/
def shiftMatrix (x : I → R) (w : List I) :
    Matrix (Fin (w.length + 1)) (Fin (w.length + 1)) R :=
  Matrix.of fun i j => if h : (i : ℕ) + 1 = (j : ℕ) then x (w[i.1]'(by omega)) else 0

/-- Entrywise description of `shiftMatrix`. -/
theorem shiftMatrix_apply (x : I → R) (w : List I)
    (i j : Fin (w.length + 1)) :
    shiftMatrix x w i j =
      (if h : (i : ℕ) + 1 = (j : ℕ) then x (w[i.1]'(by omega)) else 0) := rfl

/-- The ordered word product `x (w[0]) * x (w[1]) * ... * x (w[k-1])`, using the
noncommutative `List.prod` (not `Finset.prod`). -/
def wordProd (x : I → R) (w : List I) : R := (w.map x).prod

theorem wordProd_append (x : I → R) (l₁ l₂ : List I) :
    wordProd x (l₁ ++ l₂) = wordProd x l₁ * wordProd x l₂ := by
  simp [wordProd, List.prod_append]

theorem wordProd_singleton (x : I → R) (a : I) : wordProd x [a] = x a := by
  simp [wordProd]

theorem wordProd_nil (x : I → R) : wordProd x [] = 1 := by
  simp [wordProd]

/-- **Exact power formula.** The `(i,j)` entry of `(shiftMatrix x w)^n` is nonzero
only when `j = i + n`, and then it is the product of the `n` consecutive letters
of `w` starting at position `i`. -/
theorem shiftMatrix_pow_apply (x : I → R) (w : List I) (n : ℕ)
    (i j : Fin (w.length + 1)) :
    ((shiftMatrix x w) ^ n) i j =
      (if _h : (i : ℕ) + n = (j : ℕ) then wordProd x ((w.drop i.1).take n) else 0) := by
  induction n generalizing i j with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    by_cases h : (i : ℕ) + 0 = (j : ℕ)
    · rw [dite_eq_left h]
      have hij : i = j := by omega
      subst hij
      simp [wordProd]
    · rw [dite_eq_right h]
      have hij : i ≠ j := by omega
      simp [hij]
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply]
    by_cases hcase : (i : ℕ) + (n + 1) = (j : ℕ)
    · rw [dite_eq_left hcase]
      set l0 : Fin (w.length + 1) := ⟨i.1 + n, by omega⟩ with hl0
      rw [Finset.sum_eq_single l0]
      · rw [ih, dite_eq_left (by simp [l0])]
        rw [shiftMatrix_apply, dite_eq_left (by simp [l0]; omega)]
        have hdrop : (w.drop i.1).take (n + 1)
            = (w.drop i.1).take n ++ [w[i.1 + n]'(by omega)] :=
          List.take_succ_drop (by omega)
        rw [hdrop, wordProd_append, wordProd_singleton]
      · intro l _ hlne
        rw [ih]
        by_cases hln : (i : ℕ) + n = (l : ℕ)
        · rw [dite_eq_left hln]
          have : l = l0 := by
            apply Fin.ext
            simp only [l0]
            omega
          exact absurd this hlne
        · rw [dite_eq_right hln, zero_mul]
      · intro hmem
        exact absurd (Finset.mem_univ l0) hmem
    · rw [dite_eq_right hcase]
      apply Finset.sum_eq_zero
      intro l _
      rw [ih]
      by_cases hln : (i : ℕ) + n = (l : ℕ)
      · rw [dite_eq_left hln, shiftMatrix_apply, dite_eq_right (by omega)]
        exact mul_zero _
      · rw [dite_eq_right hln, zero_mul]

/-- **Nilpotence.** `shiftMatrix x w` to the power `length w + 1` is zero: each
multiplication of a nonzero block strictly increases the block index, which cannot
happen `length w + 1` times among `length w + 1` positions. -/
theorem shiftMatrix_pow_length_eq_zero (x : I → R) (w : List I) :
    (shiftMatrix x w) ^ (w.length + 1) = 0 := by
  ext i j
  rw [shiftMatrix_pow_apply]
  split_ifs with h
  · exfalso; omega
  · rfl

/-- **Ordered-word extraction.** The `(0, length w)` entry of `(shiftMatrix x w)^(length w)`
is exactly the ordered word product `x (w[0]) * ... * x (w[k-1])`. -/
theorem shiftMatrix_pow_extract (x : I → R) (w : List I) :
    ((shiftMatrix x w) ^ w.length) ⟨0, by omega⟩ ⟨w.length, by omega⟩ = wordProd x w := by
  rw [shiftMatrix_pow_apply]
  rw [dite_eq_left (by omega : (0 : ℕ) + w.length = w.length)]
  simp [wordProd]

/-- **Explicit two-sided inverse (left order).** The finite geometric series
`∑_{i ≤ length w} (shiftMatrix x w)^i` is a right inverse of `1 - shiftMatrix x w`. -/
theorem one_sub_shiftMatrix_mul_geomSum (x : I → R) (w : List I) :
    (1 - shiftMatrix x w) *
        (∑ i ∈ Finset.range (w.length + 1), (shiftMatrix x w) ^ i) = 1 := by
  rw [mul_neg_geom_sum, shiftMatrix_pow_length_eq_zero, sub_zero]

/-- **Explicit two-sided inverse (right order).** The same geometric series is a
left inverse of `1 - shiftMatrix x w`. -/
theorem geomSum_mul_one_sub_shiftMatrix (x : I → R) (w : List I) :
    (∑ i ∈ Finset.range (w.length + 1), (shiftMatrix x w) ^ i) *
        (1 - shiftMatrix x w) = 1 := by
  rw [geom_sum_mul_neg, shiftMatrix_pow_length_eq_zero, sub_zero]

/-- The `(0, length w)` entry of the geometric inverse of `1 - shiftMatrix x w`
is the ordered word product. -/
theorem geomSum_apply_zero_length (x : I → R) (w : List I) :
    (∑ i ∈ Finset.range (w.length + 1), (shiftMatrix x w) ^ i)
        ⟨0, by omega⟩ ⟨w.length, by omega⟩ = wordProd x w := by
  rw [Matrix.sum_apply, Finset.sum_eq_single w.length]
  · rw [shiftMatrix_pow_apply]
    rw [dite_eq_left (by omega : (0 : ℕ) + w.length = w.length)]
    simp [wordProd]
  · intro k _ hk
    rw [shiftMatrix_pow_apply]
    by_cases h : (0 : ℕ) + k = w.length
    · exfalso; omega
    · rw [dite_eq_right h]
  · intro hmem
    exact absurd (Finset.mem_range.mpr (by omega)) hmem

end GUEStrongConvergence
