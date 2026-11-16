/-
# Closing the GUE trace-word variance bound from the pairing expansion

This file isolates the final arithmetic step of the `O(N⁻²)` variance bound for a fixed GUE trace
word, conditional on the two-trace pairing expansion (the remaining combinatorial transport).

Let `Wick N = gueTwoTraceWick N w w.reverse` be the unnormalized two-trace second moment, `S N` the
single-walk label-weighted sum and `A N` the cross-pairing contribution.  The two-walk slot
reindexing produces the expansion

`gueTwoTraceWick N w w.reverse = N^{-k} * (S N ^ 2 + A N)`

(block-diagonal pairings contribute exactly `S N ^ 2`, the cross pairings `A N`), and the mean
squared has the matching block form `‖E tr_N W‖² = (N^{-(k+2)} (S N)²).re`.

Under these hypotheses and the cross-pairing bound `‖A N‖ ≤ B N^k` (which follows from
`twoWalkLoopCount_cross_le`), the exact variance identity gives

`∫ ‖tr_N W − E tr_N W‖² = N^{-(k+2)} * Re (A N) ≤ B / N²`.
-/
import GUEStrongConvergence.Probability.GUEWordSecondMoment

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Matrix ENNReal Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

namespace GUEStrongConvergence

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- **Conditional variance bound**: given the two-trace pairing expansion with the block-diagonal
part `(S N)^2` and the cross part `A N`, the mean formula `‖E tr_N W‖² = Re(N^{-(k+2)} (S N)²)`,
and the cross bound `‖A N‖ ≤ B N^k`, the variance of `tr_N W` is at most `B / N²`. -/
theorem variance_bound_of_wick_expansion (w : List ι) (k : ℕ) (S : ℕ → ℂ) (A : ℕ → ℂ) (B : ℝ)
    (hWick : ∀ N : ℕ, gueTwoTraceWick N w w.reverse =
      ((N : ℂ)⁻¹) ^ k * (((S N) ^ 2) + A N))
    (hmean : ∀ N : ℕ,
      Complex.normSq (∫ y, gueNormTrace w y
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) =
          ((((N : ℂ)⁻¹) ^ (k + 2) * (S N) ^ 2)).re)
    (hA : ∀ N : ℕ, 1 ≤ N → ‖A N‖ ≤ B * (N : ℝ) ^ k) :
    ∀ N : ℕ, 1 ≤ N →
      ∫ x : EuclideanSpace ℝ (GUECoord ι N),
          ‖gueNormTrace w x - ∫ y, gueNormTrace w y
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))‖ ^ 2
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) ≤ B / (N : ℝ) ^ 2 := by
  intro N hN
  rw [integral_sq_sub_integral_gueNormTrace, hWick N, hmean N]
  -- combine the two inverse powers of `N`
  have hpow : (((N : ℂ)⁻¹) ^ 2 * (((N : ℂ)⁻¹) ^ k * ((S N) ^ 2 + A N))) =
      ((N : ℂ)⁻¹) ^ (k + 2) * ((S N) ^ 2 + A N) := by
    rw [← mul_assoc, ← pow_add, Nat.add_comm 2 k]
  rw [hpow]
  -- the block-diagonal `S²` cancels
  have hsub : ((((N : ℂ)⁻¹) ^ (k + 2) * ((S N) ^ 2 + A N)).re -
      ((((N : ℂ)⁻¹) ^ (k + 2) * (S N) ^ 2)).re) =
      ((((N : ℂ)⁻¹) ^ (k + 2) * A N).re) := by
    rw [← Complex.sub_re]
    congr 1
    ring
  rw [hsub]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hnorm : ‖((N : ℂ)⁻¹)‖ = ((N : ℝ)⁻¹) := by
    rw [norm_inv, Complex.norm_natCast]
  have hnp : ‖(((N : ℂ)⁻¹) ^ (k + 2))‖ = ((N : ℝ)⁻¹) ^ (k + 2) := by
    rw [norm_pow, hnorm]
  have hp : ((N : ℝ)⁻¹) ^ (k + 2) * (N : ℝ) ^ k = ((N : ℝ) ^ 2)⁻¹ := by
    rw [inv_pow, show (N : ℝ) ^ (k + 2) = (N : ℝ) ^ k * (N : ℝ) ^ 2 by rw [pow_add]]
    field_simp
  calc ((((N : ℂ)⁻¹) ^ (k + 2) * A N).re)
      ≤ |((((N : ℂ)⁻¹) ^ (k + 2) * A N).re)| := le_abs_self _
    _ ≤ ‖(((N : ℂ)⁻¹) ^ (k + 2) * A N)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖(((N : ℂ)⁻¹) ^ (k + 2))‖ * ‖A N‖ := norm_mul_le _ _
    _ = ((N : ℝ)⁻¹) ^ (k + 2) * ‖A N‖ := by rw [hnp]
    _ ≤ ((N : ℝ)⁻¹) ^ (k + 2) * (B * (N : ℝ) ^ k) := by
        exact mul_le_mul_of_nonneg_left (hA N hN) (by positivity)
    _ = B / (N : ℝ) ^ 2 := by
        rw [div_eq_mul_inv, ← hp]
        ring

end

end GUEStrongConvergence
