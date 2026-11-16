/-
# Almost-sure convergence of the first normalized GUE trace

The exact second moment is `N⁻²`, so Chebyshev and the first Borel--Cantelli lemma
prove almost-sure convergence. No independence between dimensions is needed for this
step. The general coupling statement below is useful for any realization with the
specified Gaussian block marginals; the canonical common space is instantiated separately.

The summable-deviations lemma is reused from the pinned free-probability dependency.
-/
import GUEStrongConvergence.Probability.TraceMoments
import GUEStrongConvergence.Probability.CommonSpace
import FreeProbability.RandomMatrix.AlmostSureFromTails
import Mathlib.Analysis.PSeries

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace GUEStrongConvergence

noncomputable section

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

/-- Summability of the dimension-dependent second-moment bound. -/
lemma summable_gueTrace_bound (ε : ℝ) :
    Summable (fun N : ℕ => ε⁻¹ ^ 2 * (N : ℝ)⁻¹ ^ 2) := by
  have h : Summable (fun N : ℕ => ((N : ℝ) ^ 2)⁻¹) :=
    (Real.summable_nat_pow_inv (p := 2)).mpr (by norm_num)
  exact (h.mul_left (ε⁻¹ ^ 2)).congr (fun N => by simp only [inv_pow])

/-- First-word trace convergence for any coupling with the correct Gaussian block laws.
The hypotheses specify only the finite-dimensional input laws, not a convergence conclusion. -/
theorem ae_tendsto_gueNormalizedTrace_of_measurePreserving (μ : Measure Ω)
    (X : (N : ℕ) → Ω → EuclideanSpace ℝ (GUECoord ι N))
    (hX : ∀ N, MeasurePreserving (X N) μ (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
    (i : ι) :
    ∀ᵐ ω ∂μ, Tendsto (fun N => gueNormalizedTrace (X N ω) i) atTop (𝓝 0) := by
  apply FreeProbability.ae_tendsto_zero_of_summable_deviations
  intro ε hε
  have hbound (N : ℕ) : μ {ω | ε ≤ |gueNormalizedTrace (X N ω) i|} ≤
      ENNReal.ofReal (ε⁻¹ ^ 2 * (N : ℝ)⁻¹ ^ 2) := by
    have hmeas : MeasurableSet {x : EuclideanSpace ℝ (GUECoord ι N) |
        ε ≤ |gueNormalizedTrace x i|} :=
      by simpa only [Real.norm_eq_abs] using
        measurableSet_le measurable_const (measurable_gueNormalizedTrace i).norm
    calc
      μ {ω | ε ≤ |gueNormalizedTrace (X N ω) i|} =
          stdGaussian (EuclideanSpace ℝ (GUECoord ι N)) {x | ε ≤ |gueNormalizedTrace x i|} :=
        (hX N).measure_preimage hmeas.nullMeasurableSet
      _ ≤ _ := measure_gueNormalizedTrace_deviation_le i hε
  exact ne_top_of_le_ne_top (summable_gueTrace_bound ε).tsum_ofReal_ne_top
    (ENNReal.tsum_le_tsum hbound)

/-- One full-measure event works simultaneously for every matrix label. -/
theorem ae_all_tendsto_gueNormalizedTrace_of_measurePreserving (μ : Measure Ω)
    (X : (N : ℕ) → Ω → EuclideanSpace ℝ (GUECoord ι N))
    (hX : ∀ N, MeasurePreserving (X N) μ (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) :
    ∀ᵐ ω ∂μ, ∀ i : ι,
      Tendsto (fun N => gueNormalizedTrace (X N ω) i) atTop (𝓝 0) := by
  exact ae_all_iff.mpr (fun i => ae_tendsto_gueNormalizedTrace_of_measurePreserving μ X hX i)

/-- **Unconditional almost-sure first moment on the canonical common GUE space.**
One event of probability one works for every matrix label. -/
theorem ae_all_tendsto_gueNormalizedTrace :
    ∀ᵐ x : CommonSpace ι ∂commonGaussianMeasure ι, ∀ i : ι,
      Tendsto (fun N => gueNormalizedTrace (x N) i) atTop (𝓝 0) :=
  ae_all_tendsto_gueNormalizedTrace_of_measurePreserving (commonGaussianMeasure ι)
    (fun N x => x N) (fun N => measurePreserving_eval_commonGaussian N)

/-- Matrix-trace formulation of the same unconditional simultaneous first moment limit. -/
theorem ae_all_tendsto_normalizedTrace_gueMatrixOn :
    ∀ᵐ x : CommonSpace ι ∂commonGaussianMeasure ι, ∀ i : ι,
      Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * Matrix.trace (gueMatrixOn x N i)) atTop (𝓝 0) := by
  filter_upwards [ae_all_tendsto_gueNormalizedTrace (ι := ι)] with x hx
  intro i
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp (hx i)
  simpa only [Function.comp_def, Complex.ofReal_zero, gueNormalizedTrace_eq_matrix_trace,
    gueMatrixOn] using h

end

end GUEStrongConvergence
