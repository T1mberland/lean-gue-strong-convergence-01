/-
# Almost-sure second normalized GUE trace

The computed centered second moment is `2/N²` for positive dimensions. The
zero-dimensional convention contributes only a single summable term. Chebyshev
and Borel--Cantelli therefore prove convergence to one, simultaneously for every
matrix label on the concrete common probability space.
-/
import GUEStrongConvergence.Probability.GaussianSquareSum
import GUEStrongConvergence.Probability.TraceConvergence

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace GUEStrongConvergence

noncomputable section

/-- The exact variance, including the single exceptional zero dimension. -/
def gueSquareTraceVarianceBound (N : ℕ) : ℝ :=
  if N = 0 then 1 else 2 * (N : ℝ)⁻¹ ^ 2

lemma summable_gueSquareTraceVarianceBound : Summable gueSquareTraceVarianceBound := by
  have h0 : Summable (fun N : ℕ => if N = 0 then (1:ℝ) else 0) :=
    (hasSum_ite_eq (0:ℕ) (1:ℝ)).summable
  have h1 : Summable (fun N : ℕ => (N : ℝ)⁻¹ ^ 2) := by
    simpa only [inv_one, one_pow, one_mul] using summable_gueTrace_bound 1
  exact (h0.add (h1.mul_left 2)).congr (fun N => by
    by_cases hN : N = 0 <;> simp [gueSquareTraceVarianceBound, hN])

lemma summable_gueSquareTrace_deviation_bound (ε : ℝ) :
    Summable (fun N : ℕ => ε⁻¹ ^ 2 * gueSquareTraceVarianceBound N) :=
  summable_gueSquareTraceVarianceBound.mul_left _

variable {ι : Type*} {N : ℕ} [Fintype ι] [DecidableEq ι]

/-- A summable dimension-explicit deviation bound for `tr_N(G²)`. -/
theorem measure_gueNormalizedSquareTrace_deviation_le (i : ι) {ε : ℝ} (hε : 0 < ε) :
    stdGaussian (EuclideanSpace ℝ (GUECoord ι N))
      {x | ε ≤ |gueNormalizedSquareTrace x i - 1|} ≤
        ENNReal.ofReal (ε⁻¹ ^ 2 * gueSquareTraceVarianceBound N) := by
  have hInt := (integrable_gueNormalizedSquareTrace_centered_sq (N := N) i).const_mul (ε⁻¹ ^ 2)
  have h := hInt.measure_le_integral
    (ae_of_all _ (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
    (s := {x | ε ≤ |gueNormalizedSquareTrace x i - 1|}) ?_
  · simpa only [integral_const_mul, integral_gueNormalizedSquareTrace_centered_sq,
      gueSquareTraceVarianceBound] using h
  · intro x hx
    change ε ≤ |gueNormalizedSquareTrace x i - 1| at hx
    have hs : ε ^ 2 ≤ (gueNormalizedSquareTrace x i - 1) ^ 2 := by
      nlinarith [sq_abs (gueNormalizedSquareTrace x i - 1),
        abs_nonneg (gueNormalizedSquareTrace x i - 1)]
    have he : ε ≠ 0 := ne_of_gt hε
    calc
      1 = ε⁻¹ ^ 2 * ε ^ 2 := by field_simp
      _ ≤ ε⁻¹ ^ 2 * (gueNormalizedSquareTrace x i - 1) ^ 2 :=
        mul_le_mul_of_nonneg_left hs (sq_nonneg _)

/-- The centered second trace tends to zero almost surely on the concrete common space. -/
theorem ae_tendsto_gueNormalizedSquareTrace_sub_one (i : ι) :
    ∀ᵐ x : CommonSpace ι ∂commonGaussianMeasure ι,
      Tendsto (fun N => gueNormalizedSquareTrace (x N) i - 1) atTop (𝓝 0) := by
  apply FreeProbability.ae_tendsto_zero_of_summable_deviations
  intro ε hε
  have hbound (N : ℕ) :
      commonGaussianMeasure ι {x | ε ≤ |gueNormalizedSquareTrace (x N) i - 1|} ≤
        ENNReal.ofReal (ε⁻¹ ^ 2 * gueSquareTraceVarianceBound N) := by
    have hmeas : MeasurableSet {y : EuclideanSpace ℝ (GUECoord ι N) |
        ε ≤ |gueNormalizedSquareTrace y i - 1|} := by
      simpa only [Real.norm_eq_abs, Pi.sub_apply] using measurableSet_le measurable_const
        ((measurable_gueNormalizedSquareTrace i).sub measurable_const).norm
    calc
      commonGaussianMeasure ι {x | ε ≤ |gueNormalizedSquareTrace (x N) i - 1|} =
          stdGaussian (EuclideanSpace ℝ (GUECoord ι N))
            {y | ε ≤ |gueNormalizedSquareTrace y i - 1|} :=
        (measurePreserving_eval_commonGaussian (ι := ι) N).measure_preimage hmeas.nullMeasurableSet
      _ ≤ _ := measure_gueNormalizedSquareTrace_deviation_le i hε
  exact ne_top_of_le_ne_top (summable_gueSquareTrace_deviation_bound ε).tsum_ofReal_ne_top
    (ENNReal.tsum_le_tsum hbound)

/-- One probability-one event carries the second normalized trace limit for every label. -/
theorem ae_all_tendsto_gueNormalizedSquareTrace :
    ∀ᵐ x : CommonSpace ι ∂commonGaussianMeasure ι, ∀ i : ι,
      Tendsto (fun N => gueNormalizedSquareTrace (x N) i) atTop (𝓝 1) := by
  apply ae_all_iff.mpr
  intro i
  filter_upwards [ae_tendsto_gueNormalizedSquareTrace_sub_one (ι := ι) i] with x hx
  have h := hx.add_const 1
  simpa only [sub_add_cancel, zero_add] using h

/-- **Unconditional second-word matrix trace limit on the common GUE space.** -/
theorem ae_all_tendsto_normalizedSquareTrace_gueMatrixOn :
    ∀ᵐ x : CommonSpace ι ∂commonGaussianMeasure ι, ∀ i : ι,
      Tendsto (fun N : ℕ => (N : ℂ)⁻¹ *
        Matrix.trace (gueMatrixOn x N i * gueMatrixOn x N i)) atTop (𝓝 1) := by
  filter_upwards [ae_all_tendsto_gueNormalizedSquareTrace (ι := ι)] with x hx
  intro i
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp (hx i)
  simpa only [Function.comp_def, Complex.ofReal_one, gueNormalizedSquareTrace_eq_matrix_trace,
    gueMatrixOn] using h

end

end GUEStrongConvergence
