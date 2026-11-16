/-
# Simultaneous almost-sure limits of all two-letter GUE traces

On a single probability-one event, for every pair of labels `i,j`,
`tr_N(G_i G_j) → δ_ij`. The variance estimate used here is computed from Wick's
formula, not supplied as a hypothesis. All dimensions use the same common space.
-/
import GUEStrongConvergence.Probability.MixedTraceVariance

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace GUEStrongConvergence

noncomputable section

variable {ι : Type*} {N : ℕ} [Fintype ι] [DecidableEq ι]

/-- Uniform summable Chebyshev bound for all pairs of labels. -/
theorem measure_gueNormalizedMixedTrace_deviation_le (i j : ι) {ε : ℝ} (hε : 0 < ε) :
    stdGaussian (EuclideanSpace ℝ (GUECoord ι N))
      {x | ε ≤ |gueNormalizedMixedTrace x i j - if i = j then 1 else 0|} ≤
        ENNReal.ofReal (ε⁻¹ ^ 2 * gueSquareTraceVarianceBound N) := by
  have hInt := (integrable_gueNormalizedMixedTrace_centered_sq (N := N) i j).const_mul (ε⁻¹ ^ 2)
  have hmeasure := hInt.measure_le_integral
    (ae_of_all _ (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
    (s := {x | ε ≤ |gueNormalizedMixedTrace x i j - if i = j then 1 else 0|}) ?_
  · refine hmeasure.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      (integral_gueNormalizedMixedTrace_centered_sq_le i j) (sq_nonneg _)
  · intro x hx
    change ε ≤ |gueNormalizedMixedTrace x i j - if i = j then 1 else 0| at hx
    have hs : ε ^ 2 ≤ (gueNormalizedMixedTrace x i j - if i = j then 1 else 0) ^ 2 := by
      nlinarith [sq_abs (gueNormalizedMixedTrace x i j - if i = j then 1 else 0),
        abs_nonneg (gueNormalizedMixedTrace x i j - if i = j then 1 else 0)]
    have he : ε ≠ 0 := ne_of_gt hε
    calc
      1 = ε⁻¹ ^ 2 * ε ^ 2 := by field_simp
      _ ≤ ε⁻¹ ^ 2 * (gueNormalizedMixedTrace x i j - if i = j then 1 else 0) ^ 2 :=
        mul_le_mul_of_nonneg_left hs (sq_nonneg _)

/-- Centered mixed traces converge to zero almost surely, with no asymptotic hypothesis. -/
theorem ae_tendsto_gueNormalizedMixedTrace_sub_delta (i j : ι) :
    ∀ᵐ x : CommonSpace ι ∂commonGaussianMeasure ι,
      Tendsto (fun N => gueNormalizedMixedTrace (x N) i j - if i = j then 1 else 0)
        atTop (𝓝 0) := by
  apply FreeProbability.ae_tendsto_zero_of_summable_deviations
  intro ε hε
  have hbound (N : ℕ) : commonGaussianMeasure ι
      {x | ε ≤ |gueNormalizedMixedTrace (x N) i j - if i = j then 1 else 0|} ≤
        ENNReal.ofReal (ε⁻¹ ^ 2 * gueSquareTraceVarianceBound N) := by
    have hmeas : MeasurableSet {y : EuclideanSpace ℝ (GUECoord ι N) |
        ε ≤ |gueNormalizedMixedTrace y i j - if i = j then 1 else 0|} := by
      simpa only [Real.norm_eq_abs, Pi.sub_apply] using measurableSet_le measurable_const
        ((measurable_gueNormalizedMixedTrace i j).sub measurable_const).norm
    calc
      commonGaussianMeasure ι
          {x | ε ≤ |gueNormalizedMixedTrace (x N) i j - if i = j then 1 else 0|} =
          stdGaussian (EuclideanSpace ℝ (GUECoord ι N))
            {y | ε ≤ |gueNormalizedMixedTrace y i j - if i = j then 1 else 0|} :=
        (measurePreserving_eval_commonGaussian (ι := ι) N).measure_preimage hmeas.nullMeasurableSet
      _ ≤ _ := measure_gueNormalizedMixedTrace_deviation_le i j hε
  exact ne_top_of_le_ne_top (summable_gueSquareTrace_deviation_bound ε).tsum_ofReal_ne_top
    (ENNReal.tsum_le_tsum hbound)

/-- One full-measure event works for all ordered pairs of matrix labels. -/
theorem ae_all_tendsto_gueNormalizedMixedTrace :
    ∀ᵐ x : CommonSpace ι ∂commonGaussianMeasure ι, ∀ i j : ι,
      Tendsto (fun N => gueNormalizedMixedTrace (x N) i j)
        atTop (𝓝 (if i = j then 1 else 0)) := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  filter_upwards [ae_tendsto_gueNormalizedMixedTrace_sub_delta (ι := ι) i j] with x hx
  have h := hx.add_const (if i = j then (1:ℝ) else 0)
  simpa only [sub_add_cancel, zero_add] using h

/-- **Unconditional simultaneous almost-sure two-letter matrix trace limits.** -/
theorem ae_all_tendsto_normalizedMixedTrace_gueMatrixOn :
    ∀ᵐ x : CommonSpace ι ∂commonGaussianMeasure ι, ∀ i j : ι,
      Tendsto (fun N : ℕ => (N : ℂ)⁻¹ *
        Matrix.trace (gueMatrixOn x N i * gueMatrixOn x N j))
        atTop (𝓝 (if i = j then 1 else 0)) := by
  filter_upwards [ae_all_tendsto_gueNormalizedMixedTrace (ι := ι)] with x hx
  intro i j
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp (hx i j)
  by_cases hij : i = j <;>
    simpa only [Function.comp_def, hij, ite_true, ite_false, Complex.ofReal_one,
      Complex.ofReal_zero, gueNormalizedMixedTrace_eq_matrix_trace, gueMatrixOn] using h

/-- A single full-measure event carries both the first and all mixed second word limits. -/
theorem ae_all_tendsto_first_second_word_traces :
    ∀ᵐ x : CommonSpace ι ∂commonGaussianMeasure ι,
      (∀ i : ι, Tendsto (fun N : ℕ => (N : ℂ)⁻¹ *
        Matrix.trace (gueMatrixOn x N i)) atTop (𝓝 0)) ∧
      (∀ i j : ι, Tendsto (fun N : ℕ => (N : ℂ)⁻¹ *
        Matrix.trace (gueMatrixOn x N i * gueMatrixOn x N j))
          atTop (𝓝 (if i = j then 1 else 0))) := by
  filter_upwards [ae_all_tendsto_normalizedTrace_gueMatrixOn (ι := ι),
    ae_all_tendsto_normalizedMixedTrace_gueMatrixOn (ι := ι)] with x hfirst hsecond
  exact ⟨hfirst, hsecond⟩

end

end GUEStrongConvergence
