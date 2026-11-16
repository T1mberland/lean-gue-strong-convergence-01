/-
# The sharp `O(N⁻²)` comparison with the limit Dyson solution

This file re-runs the stability argument of `DysonLimit` with the **sharp** approximate-Dyson
defect of `SharpTwoPoint.approximate_dyson_entry_le_sharp` (whose right-hand side carries an
extra factor `1/N`).  The result is

`frob (g_N(z) − g(z)) ≤ C(A,d) (im z)⁻⁵ / N²`,

the `O(N⁻²)` averaged-resolvent comparison, which is the input for the smooth-trace comparison
(Lemma M) and hence for the almost-sure spectral inclusion.
-/
import GUEStrongConvergence.Probability.DysonLimit
import GUEStrongConvergence.Probability.SharpTwoPoint

open MeasureTheory ProbabilityTheory Matrix Filter
open FreeProbability FreeProbability.Fock
open scoped Matrix.Norms.Frobenius ComplexOrder ENNReal NNReal Topology

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace GUEStrongConvergence

variable {ι d : Type*} {N : ℕ} [Fintype ι] [Fintype d] [DecidableEq d] [DecidableEq ι]

noncomputable local instance : PartialOrder (WordSpace ι →L[ℂ] WordSpace ι) :=
  CStarAlgebra.spectralOrder _
noncomputable local instance : StarOrderedRing (WordSpace ι →L[ℂ] WordSpace ι) :=
  CStarAlgebra.spectralOrderedRing _

noncomputable section

/-- **Sharp comparison of the finite-`N` mean with the limit Cauchy transform.**
The `O(N⁻²)` approximate-Dyson defect and the stability of the Dyson map give
`frob (g_N(z) - g(z)) ≤ 2 d (im z)⁻¹ · (d · K_sharp)`, where `K_sharp` is the sharp defect
constant; since `gueScale(N)² = 1/N` this is `O(N⁻²)`. -/
theorem frob_gueResolventMean_sub_limit_le_sharp (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (hN : 0 < N)
    (hη : 2 * (Fintype.card d : ℝ) ^ 2 * (∑ i, (frob (A i)) ^ 2) ≤ (z.im) ^ 2) :
    frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
      ≤ 2 * (Fintype.card d : ℝ) * (z.im)⁻¹ *
          ((Fintype.card d : ℝ) *
            (2 * (Fintype.card d : ℝ) ^ 2 * Real.sqrt (Fintype.card d : ℝ) *
              (∑ i, (frob (A i)) ^ 2) *
              (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4 / (N : ℝ)))) := by
  classical
  set g : Matrix d d ℂ := operatorMatrixPencilCauchy A₀ A z with hg
  set gN : Matrix d d ℂ := gueResolventMean (N := N) A₀ A z with hgN
  set K : ℝ := 2 * (Fintype.card d : ℝ) ^ 2 * Real.sqrt (Fintype.card d : ℝ) *
      (∑ i, (frob (A i)) ^ 2) *
      (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4 / (N : ℝ)) with hK
  set D : Matrix d d ℂ := (z • (1 : Matrix d d ℂ) - A₀ - ∑ i, A i * gN * A i) * gN - 1 with hD
  have hDeq : D = (z • (1 : Matrix d d ℂ) - A₀) * gN - 1
      - ∑ i, A i * (gN * A i * gN) := by
    rw [hD, Matrix.sub_mul]
    rw [show (∑ i, A i * gN * A i) * gN = ∑ i, A i * (gN * A i * gN) from by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      noncomm_ring]
    abel
  have hD_dyson : (z • (1 : Matrix d d ℂ) - A₀ - ∑ i, A i * gN * A i) * gN = 1 + D := by
    rw [hD]
    abel
  have hDbound : frob D ≤ (Fintype.card d : ℝ) * K := by
    refine frob_le_card_mul_of_entry_le D (fun u v => ?_) (by positivity)
    rw [hDeq, hK]
    exact approximate_dyson_entry_le_sharp A₀ A hA₀ hA z hz hN u v
  have hstab := dyson_stability A₀ A z hz g gN D
    (by rw [hg]; exact limit_dyson_equation A₀ A hA₀ hA z (ne_of_gt hz))
    hD_dyson
    (by
      rw [hg]
      simpa [abs_of_pos hz] using frob_operatorMatrixPencilCauchy_le A₀ A hA₀ hA z (ne_of_gt hz))
    (by rw [hgN]; exact frob_gueResolventMean_le A₀ A hA₀ hA z hz hN)
    (by positivity) hη
  calc frob (gN - g) ≤ 2 * (Fintype.card d : ℝ) * (z.im)⁻¹ * frob D := hstab
    _ ≤ 2 * (Fintype.card d : ℝ) * (z.im)⁻¹ * ((Fintype.card d : ℝ) * K) := by
        refine mul_le_mul_of_nonneg_left hDbound ?_
        positivity
    _ = 2 * (Fintype.card d : ℝ) * (z.im)⁻¹ *
          ((Fintype.card d : ℝ) *
            (2 * (Fintype.card d : ℝ) ^ 2 * Real.sqrt (Fintype.card d : ℝ) *
              (∑ i, (frob (A i)) ^ 2) *
              (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4 / (N : ℝ)))) := by
        rw [hK]

end

end GUEStrongConvergence
