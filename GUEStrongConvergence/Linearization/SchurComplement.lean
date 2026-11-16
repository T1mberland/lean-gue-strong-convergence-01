import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Tactic

/-!
# Schur-complement invertibility for block matrices over a ring

This is the algebraic heart of the linearization trick, stated in the maximal
generality we need: `R` is an arbitrary (possibly noncommutative) unital ring,
and the matrices have entries in `R`.  No commutativity of `R`, and in particular
no commutation between the matrix coefficients and the formal indeterminates, is
used.

The main result is `isUnit_fromBlocks_iff`:

Given a block matrix
```
M = !![A, B; C, D]
```
with `D` invertible (two-sided inverse `D'`), the matrix `M` is invertible if and
only if its Schur complement `A - B ⬝ D' ⬝ C` is invertible.

The proof is constructive: block-unitriangular conjugation transforms `M` into
the block-diagonal matrix `!![A - B ⬝ D' ⬝ C, 0; 0, D]`, and a block-diagonal
matrix is invertible iff both of its diagonal blocks are.

None of the statements below confuse formal inverse notation (`D'`) with an
existence statement: the two-sided inverse condition is carried explicitly as
hypotheses `D * D' = 1` and `D' * D = 1`.
-/

namespace GUEStrongConvergence

open Matrix

variable {R : Type*} [Ring R]
variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- The upper block-unitriangular matrix `!![1, -B ⬝ D'; 0, 1]`.  Its two-sided
inverse is `!![1, B ⬝ D'; 0, 1]` (see `upperBlockUnit_inv`,
`upperBlockUnit_inv'`). -/
def upperBlockUnit (B : Matrix n m R) (D' : Matrix m m R) : Matrix (n ⊕ m) (n ⊕ m) R :=
  fromBlocks 1 (-(B * D')) 0 1

/-- The lower block-unitriangular matrix `!![1, 0; -D' ⬝ C, 1]`.  Its two-sided
inverse is `!![1, 0; D' ⬝ C, 1]` (see `lowerBlockUnit_inv`,
`lowerBlockUnit_inv'`). -/
def lowerBlockUnit (C : Matrix m n R) (D' : Matrix m m R) : Matrix (n ⊕ m) (n ⊕ m) R :=
  fromBlocks 1 0 (-(D' * C)) 1

theorem upperBlockUnit_inv (B : Matrix n m R) (D' : Matrix m m R) :
    upperBlockUnit B D' * fromBlocks 1 (B * D') 0 1 = 1 := by
  rw [upperBlockUnit, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

theorem upperBlockUnit_inv' (B : Matrix n m R) (D' : Matrix m m R) :
    fromBlocks 1 (B * D') 0 1 * upperBlockUnit B D' = 1 := by
  rw [upperBlockUnit, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

theorem lowerBlockUnit_inv (C : Matrix m n R) (D' : Matrix m m R) :
    lowerBlockUnit C D' * fromBlocks 1 0 (D' * C) 1 = 1 := by
  rw [lowerBlockUnit, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

theorem lowerBlockUnit_inv' (C : Matrix m n R) (D' : Matrix m m R) :
    fromBlocks 1 0 (D' * C) 1 * lowerBlockUnit C D' = 1 := by
  rw [lowerBlockUnit, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

/-- Conjugating `!![A, B; C, D]` by the two block-unitriangular matrices produces
the block-diagonal matrix `!![A - B ⬝ D' ⬝ C, 0; 0, D]`. -/
theorem upperBlockUnit_mul_mul_lowerBlockUnit
    (A : Matrix n n R) (B : Matrix n m R) (C : Matrix m n R) (D : Matrix m m R)
    (D' : Matrix m m R) (hDD' : D * D' = 1) (hD'D : D' * D = 1) :
    upperBlockUnit B D' * fromBlocks A B C D * lowerBlockUnit C D' =
      fromBlocks (A - B * D' * C) 0 0 D := by
  have hBD : B * D' * D = B := by rw [Matrix.mul_assoc, hD'D, Matrix.mul_one]
  have hCD : D * (D' * C) = C := by rw [← Matrix.mul_assoc, hDD', Matrix.one_mul]
  rw [upperBlockUnit, lowerBlockUnit, fromBlocks_multiply, fromBlocks_multiply,
    fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : B + -(B * D') * D = 0 := by rw [Matrix.neg_mul, hBD, add_neg_cancel]
    have h2 : -(B * D') * C = -(B * D' * C) := by rw [Matrix.neg_mul]
    simp only [Matrix.one_mul, Matrix.mul_one]
    rw [h1, h2]
    simp [sub_eq_add_neg]
  · have h1 : B + -(B * D') * D = 0 := by rw [Matrix.neg_mul, hBD, add_neg_cancel]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, zero_add]
    exact h1
  · have h3 : D * -(D' * C) = -C := by rw [Matrix.mul_neg, hCD]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, zero_add]
    rw [h3, add_neg_cancel]
  · simp

/-- A block-diagonal matrix is invertible if and only if both diagonal blocks
are invertible. -/
theorem isUnit_fromBlocks_diagonal_iff (S : Matrix n n R) (D : Matrix m m R) :
    IsUnit (fromBlocks S 0 0 D) ↔ IsUnit S ∧ IsUnit D := by
  have h₁₁ : ∀ (W : Matrix (n ⊕ m) (n ⊕ m) R),
      (fromBlocks S 0 0 D * W).toBlocks₁₁ = S * W.toBlocks₁₁ := by
    intro W
    rw [← fromBlocks_toBlocks W, fromBlocks_multiply]
    simp
  have h₁₁' : ∀ (W : Matrix (n ⊕ m) (n ⊕ m) R),
      (W * fromBlocks S 0 0 D).toBlocks₁₁ = W.toBlocks₁₁ * S := by
    intro W
    rw [← fromBlocks_toBlocks W, fromBlocks_multiply]
    simp
  have h₂₂ : ∀ (W : Matrix (n ⊕ m) (n ⊕ m) R),
      (fromBlocks S 0 0 D * W).toBlocks₂₂ = D * W.toBlocks₂₂ := by
    intro W
    rw [← fromBlocks_toBlocks W, fromBlocks_multiply]
    simp
  have h₂₂' : ∀ (W : Matrix (n ⊕ m) (n ⊕ m) R),
      (W * fromBlocks S 0 0 D).toBlocks₂₂ = W.toBlocks₂₂ * D := by
    intro W
    rw [← fromBlocks_toBlocks W, fromBlocks_multiply]
    simp
  have hone₁₁ : (1 : Matrix (n ⊕ m) (n ⊕ m) R).toBlocks₁₁ = 1 := by
    ext i j
    simp [Matrix.toBlocks₁₁, Matrix.one_apply]
  have hone₂₂ : (1 : Matrix (n ⊕ m) (n ⊕ m) R).toBlocks₂₂ = 1 := by
    ext i j
    simp [Matrix.toBlocks₂₂, Matrix.one_apply]
  constructor
  · intro h
    obtain ⟨W, hW1, hW2⟩ := isUnit_iff_exists.mp h
    have h1 := congrArg Matrix.toBlocks₁₁ hW1
    rw [h₁₁ W, hone₁₁] at h1
    have h2 := congrArg Matrix.toBlocks₁₁ hW2
    rw [h₁₁' W, hone₁₁] at h2
    have h3 := congrArg Matrix.toBlocks₂₂ hW1
    rw [h₂₂ W, hone₂₂] at h3
    have h4 := congrArg Matrix.toBlocks₂₂ hW2
    rw [h₂₂' W, hone₂₂] at h4
    exact ⟨isUnit_iff_exists.mpr ⟨W.toBlocks₁₁, h1, h2⟩,
      isUnit_iff_exists.mpr ⟨W.toBlocks₂₂, h3, h4⟩⟩
  · rintro ⟨hS, hD⟩
    obtain ⟨S', hS1, hS2⟩ := isUnit_iff_exists.mp hS
    obtain ⟨D', hD1, hD2⟩ := isUnit_iff_exists.mp hD
    refine isUnit_iff_exists.mpr ⟨fromBlocks S' 0 0 D', ?_, ?_⟩
    · rw [fromBlocks_multiply, hS1, hD1]; simp [fromBlocks_one]
    · rw [fromBlocks_multiply, hS2, hD2]; simp [fromBlocks_one]

/-- **Schur-complement invertibility.**  For a block matrix `!![A, B; C, D]` whose
`(2,2)`-block `D` has the explicit two-sided inverse `D'`, invertibility of the
whole matrix is equivalent to invertibility of the Schur complement
`A - B ⬝ D' ⬝ C`. -/
theorem isUnit_fromBlocks_iff
    (A : Matrix n n R) (B : Matrix n m R) (C : Matrix m n R) (D : Matrix m m R)
    (D' : Matrix m m R) (hDD' : D * D' = 1) (hD'D : D' * D = 1) :
    IsUnit (fromBlocks A B C D) ↔ IsUnit (A - B * D' * C) := by
  have hU : IsUnit (upperBlockUnit B D') :=
    isUnit_iff_exists.mpr ⟨_, upperBlockUnit_inv B D', upperBlockUnit_inv' B D'⟩
  have hV : IsUnit (lowerBlockUnit C D') :=
    isUnit_iff_exists.mpr ⟨_, lowerBlockUnit_inv C D', lowerBlockUnit_inv' C D'⟩
  have hU' : IsUnit (fromBlocks 1 (B * D') 0 1) :=
    isUnit_iff_exists.mpr ⟨_, upperBlockUnit_inv' B D', upperBlockUnit_inv B D'⟩
  have hV' : IsUnit (fromBlocks 1 0 (D' * C) 1) :=
    isUnit_iff_exists.mpr ⟨_, lowerBlockUnit_inv' C D', lowerBlockUnit_inv C D'⟩
  have hD : IsUnit D := isUnit_iff_exists.mpr ⟨D', hDD', hD'D⟩
  have hconj := upperBlockUnit_mul_mul_lowerBlockUnit A B C D D' hDD' hD'D
  have key : IsUnit (fromBlocks A B C D) ↔ IsUnit (fromBlocks (A - B * D' * C) 0 0 D) := by
    constructor
    · intro hM
      have : IsUnit (upperBlockUnit B D' * fromBlocks A B C D * lowerBlockUnit C D') :=
        (hU.mul hM).mul hV
      rwa [hconj] at this
    · intro hbd
      have hseq : fromBlocks A B C D
          = fromBlocks 1 (B * D') 0 1 * (fromBlocks (A - B * D' * C) 0 0 D)
              * fromBlocks 1 0 (D' * C) 1 := by
        have h := hconj
        calc fromBlocks A B C D
            = (fromBlocks 1 (B * D') 0 1 * upperBlockUnit B D')
                * fromBlocks A B C D
                * (lowerBlockUnit C D' * fromBlocks 1 0 (D' * C) 1) := by
              rw [upperBlockUnit_inv', lowerBlockUnit_inv, one_mul, mul_one]
          _ = fromBlocks 1 (B * D') 0 1
                * (upperBlockUnit B D' * fromBlocks A B C D * lowerBlockUnit C D')
                * fromBlocks 1 0 (D' * C) 1 := by
              simp only [Matrix.mul_assoc]
          _ = fromBlocks 1 (B * D') 0 1 * (fromBlocks (A - B * D' * C) 0 0 D)
                * fromBlocks 1 0 (D' * C) 1 := by
              rw [h]
      rw [hseq]
      exact (hU'.mul hbd).mul hV'
  rw [key, isUnit_fromBlocks_diagonal_iff, and_iff_left hD]

end GUEStrongConvergence
