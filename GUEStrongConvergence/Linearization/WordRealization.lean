import GUEStrongConvergence.Linearization.NilpotentShift
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic

/-!
# Finite direct sum of word realizations

This file formalizes the block-diagonal assembly of §2.1 of the linearization
handoff.  For a finite index type `κ`, a family of words `wds : κ → List I` and a
family of "coefficients" `coeff : κ → M` in a (possibly noncommutative) ring `M`,
it builds the block-diagonal matrix `Q = blockDiagonal' linQ` and its explicit
two-sided inverse `Q^{-1} = blockDiagonal' linQinv`, together with the block row
`linU` and block column `linV` such that

`linU * Q^{-1} * linV = ∑ k, coeff k * wordProd x (wds k)`.

This is the algebraic core of the word realization `u Q(X)^{-1} v = q(X)`: the
right-hand side is precisely `q` evaluated at `x`, with `coeff k` playing the role
of the half-coefficient `C_w / 2`.

Everything is stated over an arbitrary ring `M`; matrix-coefficient polynomials
are recovered later by taking `M = Matrix D D S` and `x i = Matrix.scalar D (gen i)`.
-/

namespace GUEStrongConvergence

open Matrix

variable {M : Type*} [Ring M] {I κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The block matrix `Q_k = 1 - shiftMatrix x (wds k)` associated with word `k`. -/
def linQ (x : I → M) (wds : κ → List I) (k : κ) :
    Matrix (Fin ((wds k).length + 1)) (Fin ((wds k).length + 1)) M :=
  1 - shiftMatrix x (wds k)

/-- The explicit inverse `Q_k^{-1} = ∑_{i ≤ length} (shiftMatrix x (wds k))^i`. -/
def linQinv (x : I → M) (wds : κ → List I) (k : κ) :
    Matrix (Fin ((wds k).length + 1)) (Fin ((wds k).length + 1)) M :=
  ∑ i ∈ Finset.range ((wds k).length + 1), (shiftMatrix x (wds k)) ^ i

/-- The direct sum `Q = ⊕_k Q_k`. -/
def linQMat (x : I → M) (wds : κ → List I) :
    Matrix (Σ k, Fin ((wds k).length + 1)) (Σ k, Fin ((wds k).length + 1)) M :=
  blockDiagonal' (linQ x wds)

/-- The direct sum `Q^{-1} = ⊕_k Q_k^{-1}`. -/
def linQinvMat (x : I → M) (wds : κ → List I) :
    Matrix (Σ k, Fin ((wds k).length + 1)) (Σ k, Fin ((wds k).length + 1)) M :=
  blockDiagonal' (linQinv x wds)

/-- `Q` is a left inverse of `Q^{-1}`. -/
theorem linQ_mul_linQinvMat (x : I → M) (wds : κ → List I) :
    linQMat x wds * linQinvMat x wds = 1 := by
  rw [linQMat, linQinvMat, ← blockDiagonal'_one, ← blockDiagonal'_mul, blockDiagonal'_inj]
  funext k
  exact one_sub_shiftMatrix_mul_geomSum x (wds k)

/-- `Q^{-1}` is a left inverse of `Q`. -/
theorem linQinvMat_mul_linQ (x : I → M) (wds : κ → List I) :
    linQinvMat x wds * linQMat x wds = 1 := by
  rw [linQMat, linQinvMat, ← blockDiagonal'_one, ← blockDiagonal'_mul, blockDiagonal'_inj]
  funext k
  exact geomSum_mul_one_sub_shiftMatrix x (wds k)

/-- The block row `u`: the coefficient `coeff k` sits in the first block position
of the block labelled `k`, and zeros elsewhere. -/
def linU (wds : κ → List I) (coeff : κ → M) :
    Matrix (Fin 1) (Σ k, Fin ((wds k).length + 1)) M :=
  Matrix.of fun _ p => if _h : (p.2 : ℕ) = 0 then coeff p.1 else 0

/-- The block column `v`: the unit sits in the last block position of the block
labelled `k`, and zeros elsewhere.  (The generator family `x` is passed only to fix
the ring `M` for type inference; it is not used.) -/
def linV (_x : I → M) (wds : κ → List I) :
    Matrix (Σ k, Fin ((wds k).length + 1)) (Fin 1) M :=
  Matrix.of fun p _ => if _h : (p.2 : ℕ) = (wds p.1).length then 1 else 0

/-- The product of the block-diagonal inverse with the block column `v` selects,
in each block, the last entry of the corresponding `Q_k^{-1}`. -/
theorem linQinvMat_mul_linV (x : I → M) (wds : κ → List I) (k : κ)
    (i : Fin ((wds k).length + 1)) :
    (linQinvMat x wds * linV x wds) ⟨k, i⟩ 0
      = (linQinv x wds k) i ⟨(wds k).length, by omega⟩ := by
  rw [linQinvMat, Matrix.mul_apply]
  rw [Finset.sum_eq_single (⟨k, ⟨(wds k).length, by omega⟩⟩ :
        Σ k, Fin ((wds k).length + 1))]
  · rw [blockDiagonal'_apply_eq]
    rw [linV, Matrix.of_apply, dite_eq_left (by simp)]
    rw [mul_one]
  · rintro ⟨k', i'⟩ _ hq
    rw [blockDiagonal'_apply']
    by_cases hk : k = k'
    · rw [dite_eq_left hk]
      by_cases hi : (i' : ℕ) = (wds k').length
      · exfalso
        exact hq (by subst hk; exact Sigma.ext rfl (heq_of_eq (Fin.ext hi)))
      · rw [linV, Matrix.of_apply, dite_eq_right (by simpa using hi), mul_zero]
    · rw [dite_eq_right hk, zero_mul]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-- **Word realization.** The assembled block row, block-diagonal inverse and
block column multiply back to the finite combination `∑ k, coeff k * wordProd x (wds k)`. -/
theorem linU_mul_linQinvMat_mul_linV (x : I → M) (wds : κ → List I) (coeff : κ → M) :
    (linU wds coeff * linQinvMat x wds * linV x wds) 0 0
      = ∑ k, coeff k * wordProd x (wds k) := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_eq_single (0 : Fin ((wds k).length + 1))]
  · rw [linQinvMat_mul_linV x wds k 0]
    rw [linU, Matrix.of_apply, dite_eq_left (by simp)]
    rw [linQinv]
    exact congrArg (fun r => coeff k * r) (geomSum_apply_zero_length x (wds k))
  · intro i _ hi
    rw [linU, Matrix.of_apply, dite_eq_right (by simpa using hi), zero_mul]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

end GUEStrongConvergence
