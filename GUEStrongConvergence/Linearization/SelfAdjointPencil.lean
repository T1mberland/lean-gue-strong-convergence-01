import GUEStrongConvergence.Linearization.SchurComplement
import GUEStrongConvergence.Linearization.WordRealization
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic

set_option linter.unusedSectionVars false

/-!
# The self-adjoint affine pencil `ℒ_z`

This file formalizes §2.2–2.4 of the linearization handoff at the level of an
arbitrary `*`-ring `M`.  Given the block-diagonal `Q = linQMat x wds` with explicit
inverse `Q^{-1} = linQinvMat x wds`, the block row `u = linU wds coeff`, the block
column `v = linV x wds`, it builds

* `penB = !![0, Q*; Q, 0]` with explicit two-sided inverse
  `penBinv = !![0, Q^{-1}; (Q*)^{-1}, 0]`   (`penB_mul_penBinv`, `penBinv_mul_penB`),
* the off-diagonal block `E = (-u, -v*)` (`penE`) and its adjoint `E*` (`penEconj`),

and proves the Schur-complement identity
`E B^{-1} E* = q + q*` with `q = u Q^{-1} v` (`penE_mul_penBinv_mul_penEconj`).

Together with `SchurComplement.isUnit_fromBlocks_iff` this yields the central
invertibility equivalence `zI - P invertible ↔ ℒ_z invertible` once the pencil is
assembled (`pencil_isUnit_iff`).
-/

namespace GUEStrongConvergence

open Matrix

variable {M : Type*} [Ring M] [StarRing M] {I κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The block index type `Σ k, Fin (length (wds k) + 1)`. -/
abbrev BlkIdx (wds : κ → List I) : Type _ := Σ k, Fin ((wds k).length + 1)

/-- The self-adjoint off-diagonal block `B = !![0, Q*; Q, 0]`. -/
def penB (x : I → M) (wds : κ → List I) :
    Matrix (BlkIdx wds ⊕ BlkIdx wds) (BlkIdx wds ⊕ BlkIdx wds) M :=
  fromBlocks 0 (linQMat x wds)ᴴ (linQMat x wds) 0

/-- The explicit inverse `B^{-1} = !![0, Q^{-1}; (Q*)^{-1}, 0]`. -/
def penBinv (x : I → M) (wds : κ → List I) :
    Matrix (BlkIdx wds ⊕ BlkIdx wds) (BlkIdx wds ⊕ BlkIdx wds) M :=
  fromBlocks 0 (linQinvMat x wds) (linQinvMat x wds)ᴴ 0

/-- `B` is a left inverse of `B^{-1}`. -/
theorem penB_mul_penBinv (x : I → M) (wds : κ → List I) :
    penB x wds * penBinv x wds = 1 := by
  rw [penB, penBinv, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_zero, zero_add, ← Matrix.conjTranspose_mul, linQinvMat_mul_linQ,
      Matrix.conjTranspose_one]
  · rw [Matrix.zero_mul, Matrix.mul_zero, add_zero]
  · rw [Matrix.zero_mul, Matrix.mul_zero, add_zero]
  · rw [Matrix.mul_zero, add_zero, linQ_mul_linQinvMat]

/-- `B` is a right inverse of `B^{-1}`. -/
theorem penBinv_mul_penB (x : I → M) (wds : κ → List I) :
    penBinv x wds * penB x wds = 1 := by
  rw [penB, penBinv, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_zero, zero_add, linQinvMat_mul_linQ]
  · rw [Matrix.zero_mul, Matrix.mul_zero, add_zero]
  · rw [Matrix.mul_zero, Matrix.zero_mul, zero_add]
  · rw [Matrix.mul_zero, add_zero, ← Matrix.conjTranspose_mul, linQ_mul_linQinvMat,
      Matrix.conjTranspose_one]

omit [Fintype κ] in
/-- `B` is self-adjoint. -/
theorem penB_conjTranspose (x : I → M) (wds : κ → List I) :
    (penB x wds)ᴴ = penB x wds := by
  rw [penB, fromBlocks_conjTranspose]
  simp

/-- The off-diagonal block `E = (-u, -v*)`. -/
def penE (x : I → M) (wds : κ → List I) (coeff : κ → M) :
    Matrix (Fin 1) (BlkIdx wds ⊕ BlkIdx wds) M :=
  Matrix.of fun _ p => match p with
    | Sum.inl b => -linU wds coeff 0 b
    | Sum.inr b => -((linV x wds)ᴴ) 0 b

/-- The adjoint `E* = (-u*, -v)` of `E`. -/
def penEconj (x : I → M) (wds : κ → List I) (coeff : κ → M) :
    Matrix (BlkIdx wds ⊕ BlkIdx wds) (Fin 1) M :=
  Matrix.of fun p _ => match p with
    | Sum.inl b => -((linU wds coeff)ᴴ) b 0
    | Sum.inr b => -(linV x wds) b 0

omit [Fintype κ] [DecidableEq κ] in
/-- The adjoint of `penE` is `penEconj`. -/
theorem penE_conjTranspose (x : I → M) (wds : κ → List I) (coeff : κ → M) :
    (penE x wds coeff)ᴴ = penEconj x wds coeff := by
  ext p j
  rcases p with b | b <;>
    · fin_cases j
      simp [penE, penEconj, Matrix.conjTranspose_apply]

omit [Fintype κ] [DecidableEq κ] in
/-- The adjoint of `penEconj` is `penE`. -/
theorem penEconj_conjTranspose (x : I → M) (wds : κ → List I) (coeff : κ → M) :
    (penEconj x wds coeff)ᴴ = penE x wds coeff := by
  rw [← penE_conjTranspose x wds coeff, Matrix.conjTranspose_conjTranspose]

section Entries

variable (x : I → M) (wds : κ → List I) (coeff : κ → M)

@[simp] theorem penBinv_apply_inl_inl (a b : BlkIdx wds) :
    penBinv x wds (Sum.inl a) (Sum.inl b) = 0 := by
  simp [penBinv]

@[simp] theorem penBinv_apply_inl_inr (a b : BlkIdx wds) :
    penBinv x wds (Sum.inl a) (Sum.inr b) = linQinvMat x wds a b := by
  simp [penBinv]

@[simp] theorem penBinv_apply_inr_inl (a b : BlkIdx wds) :
    penBinv x wds (Sum.inr a) (Sum.inl b) = (linQinvMat x wds)ᴴ a b := by
  simp [penBinv]

@[simp] theorem penBinv_apply_inr_inr (a b : BlkIdx wds) :
    penBinv x wds (Sum.inr a) (Sum.inr b) = 0 := by
  simp [penBinv]

@[simp] theorem penE_apply_inl (b : BlkIdx wds) (j : Fin 1) :
    penE x wds coeff j (Sum.inl b) = -linU wds coeff 0 b := by
  simp [penE]

@[simp] theorem penE_apply_inr (b : BlkIdx wds) (j : Fin 1) :
    penE x wds coeff j (Sum.inr b) = -((linV x wds)ᴴ) 0 b := by
  simp [penE]

@[simp] theorem penEconj_apply_inl (b : BlkIdx wds) (j : Fin 1) :
    penEconj x wds coeff (Sum.inl b) j = -((linU wds coeff)ᴴ) b 0 := by
  simp [penEconj]

@[simp] theorem penEconj_apply_inr (b : BlkIdx wds) (j : Fin 1) :
    penEconj x wds coeff (Sum.inr b) j = -(linV x wds) b 0 := by
  simp [penEconj]

/-- `B^{-1} E*` in block form. -/
theorem penBinv_mul_penEconj_eq :
    penBinv x wds * penEconj x wds coeff
      = Matrix.of fun p _ => match p with
          | Sum.inl a => -((linQinvMat x wds) * linV x wds) a 0
          | Sum.inr a => -(((linQinvMat x wds)ᴴ) * (linU wds coeff)ᴴ) a 0 := by
  ext p j
  rcases p with a | a <;> fin_cases j
  · rw [Matrix.mul_apply, Fintype.sum_sum_type]
    simp only [Matrix.of_apply, penBinv_apply_inl_inl, penBinv_apply_inl_inr,
      penEconj_apply_inl, penEconj_apply_inr, zero_mul, Finset.sum_const_zero,
      Finset.sum_neg_distrib, mul_neg, neg_zero, zero_add, ← Matrix.mul_apply]
  · rw [Matrix.mul_apply, Fintype.sum_sum_type]
    simp only [Matrix.of_apply, penBinv_apply_inr_inl, penBinv_apply_inr_inr,
      penEconj_apply_inl, penEconj_apply_inr, zero_mul, Finset.sum_const_zero,
      Finset.sum_neg_distrib, mul_neg, neg_zero, add_zero, ← Matrix.mul_apply]

/-- **Key identity.** `E B^{-1} E* = q + q*`. -/
theorem penE_mul_penBinv_mul_penEconj :
    penE x wds coeff * penBinv x wds * penEconj x wds coeff
      = (linU wds coeff * linQinvMat x wds * linV x wds)
        + (linU wds coeff * linQinvMat x wds * linV x wds)ᴴ := by
  ext i j
  fin_cases i; fin_cases j
  rw [Matrix.mul_assoc, penBinv_mul_penEconj_eq, Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [Matrix.of_apply, penE_apply_inl, penE_apply_inr, neg_mul, mul_neg, neg_neg,
    ← Matrix.mul_apply]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.add_apply]
  simp only [Matrix.mul_assoc]
  rfl

end Entries

section Pencil

variable (x : I → M) (wds : κ → List I) (coeff : κ → M)

/-- The assembled affine pencil
`ℒ(A0) = !![A0, -u, -v*; -u*, 0, Q*; -v, Q, 0]`, where `A0` plays the role of
`z I - C`.  The discarded row/column group is `B = !![0, Q*; Q, 0]`. -/
def penL (A0 : Matrix (Fin 1) (Fin 1) M) :
    Matrix ((Fin 1) ⊕ (BlkIdx wds ⊕ BlkIdx wds))
      ((Fin 1) ⊕ (BlkIdx wds ⊕ BlkIdx wds)) M :=
  fromBlocks A0 (penE x wds coeff) (penEconj x wds coeff) (penB x wds)

/-- The Schur complement of the pencil with respect to the invertible block `B` is
`A0 - (q + q*)`. -/
theorem penL_schur (A0 : Matrix (Fin 1) (Fin 1) M) :
    upperBlockUnit (penE x wds coeff) (penBinv x wds) * penL x wds coeff A0 *
        lowerBlockUnit (penEconj x wds coeff) (penBinv x wds)
      = fromBlocks (A0 - ((linU wds coeff * linQinvMat x wds * linV x wds)
            + (linU wds coeff * linQinvMat x wds * linV x wds)ᴴ)) 0 0 (penB x wds) := by
  rw [penL, upperBlockUnit_mul_mul_lowerBlockUnit _ _ _ _ _
      (penB_mul_penBinv x wds) (penBinv_mul_penB x wds), penE_mul_penBinv_mul_penEconj]

/-- **Invertibility equivalence.** The pencil `ℒ(A0)` is invertible if and only if
its Schur complement `A0 - (q + q*)` is invertible. -/
theorem penL_isUnit_iff (A0 : Matrix (Fin 1) (Fin 1) M) :
    IsUnit (penL x wds coeff A0) ↔
      IsUnit (A0 - ((linU wds coeff * linQinvMat x wds * linV x wds)
        + (linU wds coeff * linQinvMat x wds * linV x wds)ᴴ)) := by
  rw [penL, isUnit_fromBlocks_iff A0 (penE x wds coeff) (penEconj x wds coeff)
    (penB x wds) (penBinv x wds) (penB_mul_penBinv x wds) (penBinv_mul_penB x wds),
    penE_mul_penBinv_mul_penEconj]

/-- The pencil is self-adjoint whenever its top-left block `A0` is. -/
theorem penL_conjTranspose (A0 : Matrix (Fin 1) (Fin 1) M) :
    (penL x wds coeff A0)ᴴ = penL x wds coeff A0ᴴ := by
  unfold penL
  rw [fromBlocks_conjTranspose, penE_conjTranspose x wds coeff,
    penEconj_conjTranspose x wds coeff, penB_conjTranspose]

/-- The pencil depends affinely on its top-left block: the difference of two
pencils is supported on the `(1,1)` block. -/
theorem penL_sub (A0 A0' : Matrix (Fin 1) (Fin 1) M) :
    penL x wds coeff A0 - penL x wds coeff A0' = fromBlocks (A0 - A0') 0 0 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    · simp [penL, fromBlocks, Matrix.sub_apply]

/-- The projection `Π_D = diag(1_D, 0, 0)` in the block ring, the fixed orthogonal
projection used in the parameter-continuity estimate (§2.4). -/
def penPi (wds : κ → List I) :
    Matrix ((Fin 1) ⊕ (BlkIdx wds ⊕ BlkIdx wds))
      ((Fin 1) ⊕ (BlkIdx wds ⊕ BlkIdx wds)) M :=
  fromBlocks 1 0 0 0

/-- `Π_D` is idempotent. -/
theorem penPi_mul_self (wds : κ → List I) :
    penPi (M := M) wds * penPi (M := M) wds = penPi (M := M) wds := by
  rw [penPi, fromBlocks_multiply, fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

/-- `Π_D` is self-adjoint. -/
theorem penPi_conjTranspose (wds : κ → List I) :
    (penPi (M := M) wds)ᴴ = penPi (M := M) wds := by
  rw [penPi, fromBlocks_conjTranspose]
  simp

/-- **§2.4 algebraic identity.** The pencil depends on the scalar `z` only through
its `(1,1)` block, so the difference of the pencils at `z` and `z'` is exactly
`(z - z') Π_D`.  This is the algebraic content of the parameter-continuity estimate. -/
theorem penL_sub_smul (z z' : M) :
    penL x wds coeff (z • 1) - penL x wds coeff (z' • 1)
      = (z - z') • penPi (M := M) wds := by
  rw [penL_sub, penPi]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    · simp [fromBlocks, Matrix.sub_apply, Matrix.smul_apply, sub_mul]

section NormEstimate

variable [Norm M]
  [SeminormedAddCommGroup (Matrix ((Fin 1) ⊕ (BlkIdx wds ⊕ BlkIdx wds))
    ((Fin 1) ⊕ (BlkIdx wds ⊕ BlkIdx wds)) M)]

/-- **§2.4 parametric-continuity estimate (reduction form).** Assuming the block
matrix norm is submultiplicative for the `M`-action (`hsmul`) and the projection
`Π_D` has norm at most one (`hPi`) — both standard properties of the genuine
C\*-operator norm — the pencil is Lipschitz in the scalar parameter:
`‖ℒ_z - ℒ_{z'}‖ ≤ ‖z - z'‖`.  When `z, z'` are real scalars embedded isometrically as
`z • 1`, `z' • 1`, the right-hand side is `|z - z'|`. -/
theorem penL_norm_diff_le
    (hsmul : ∀ (a : M) (A : Matrix ((Fin 1) ⊕ (BlkIdx wds ⊕ BlkIdx wds))
        ((Fin 1) ⊕ (BlkIdx wds ⊕ BlkIdx wds)) M), ‖a • A‖ ≤ ‖a‖ * ‖A‖)
    (hPi : ‖penPi (M := M) wds‖ ≤ 1) (z z' : M) (hznn : 0 ≤ ‖z - z'‖) :
    ‖penL x wds coeff (z • 1) - penL x wds coeff (z' • 1)‖ ≤ ‖z - z'‖ := by
  rw [penL_sub_smul]
  calc ‖(z - z') • penPi (M := M) wds‖
      ≤ ‖z - z'‖ * ‖penPi (M := M) wds‖ := hsmul _ _
    _ ≤ ‖z - z'‖ * 1 := mul_le_mul_of_nonneg_left hPi hznn
    _ = ‖z - z'‖ := mul_one _

end NormEstimate

end Pencil

end GUEStrongConvergence
