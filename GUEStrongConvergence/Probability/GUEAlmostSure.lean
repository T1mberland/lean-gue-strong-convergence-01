/-
# Almost-sure convergence from summable variances (Borel–Cantelli)

This file provides the Borel–Cantelli step of the strong-convergence program for a sequence of
complex random variables whose centered second moments are summable.  It is the abstract template
used for the fixed GUE trace words once the `O(N⁻²)` variance bound is available.

Main results:

* `ae_tendsto_zero_of_summable_integral_norm_sq`: if `∑_N ∫ ‖F N‖² < ∞`, then
  `F N → 0` almost surely (Borel–Cantelli applied to `∑_N ‖F N‖²`).
* `ae_tendsto_of_tendsto_deviation`: if `F N − m N → 0` almost surely and `m N → L`, then
  `F N → L` almost surely.
* `summable_integral_norm_sq_of_bound`: a bound `∫ ‖F N‖² ≤ B / N²` for `N ≥ 1` gives summability
  of the second moments (comparison with the convergent `p`-series `∑ N^{-2}`).
-/
import GUEStrongConvergence.Probability.GUEWordSecondMoment
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.PSeries

open MeasureTheory ProbabilityTheory Filter ENNReal
open scoped RealInnerProductSpace Matrix ENNReal Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

namespace GUEStrongConvergence

noncomputable section

/-- Borel–Cantelli: summability of the integrals of `‖F N‖` gives almost-sure summability of the
norms. -/
theorem ae_summable_norm_of_summable_integral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (F : ℕ → Ω → ℝ) (hF : ∀ i, Integrable (F i) μ)
    (hs : Summable (fun i => ∫ x, ‖F i x‖ ∂μ)) :
    ∀ᵐ x ∂μ, Summable (fun i => ‖F i x‖) := by
  have he (i : ℕ) : ∫⁻ x, ‖F i x‖ₑ ∂μ = ‖∫ x, ‖F i x‖ ∂μ‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hF i).norm]
    simp only [coe_nnreal_eq, coe_nnnorm, Real.norm_eq_abs]
    rw [abs_of_nonneg (integral_nonneg (fun x => abs_nonneg (F i x)))]
  have hsum : ∑' i, ∫⁻ x, ‖F i x‖ₑ ∂μ ≠ ∞ := by
    rw [funext he]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_coe.1 hs.abs)
  have hm (i : ℕ) : AEMeasurable (fun x => ‖F i x‖ₑ) μ := (hF i).1.enorm
  rw [← lintegral_tsum hm] at hsum
  refine (ae_lt_top' (AEMeasurable.tsum hm) hsum).mono ?_
  intro x hx
  change Summable (fun i => (‖F i x‖₊ : ℝ))
  rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
  exact hx.ne

/-- **Borel–Cantelli for summable squared norms**: summable second moments give almost-sure
convergence to zero. -/
theorem ae_tendsto_zero_of_summable_integral_norm_sq {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] (μ : Measure Ω) (F : ℕ → Ω → E)
    (hF : ∀ N, Integrable (fun ω => ‖F N ω‖ ^ 2) μ)
    (hs : Summable (fun N => ∫ ω, ‖F N ω‖ ^ 2 ∂μ)) :
    ∀ᵐ ω ∂μ, Tendsto (fun N => F N ω) atTop (𝓝 0) := by
  have hsn : Summable (fun N => ∫ ω, ‖‖F N ω‖ ^ 2‖ ∂μ) := by
    simpa only [Real.norm_eq_abs, abs_sq] using hs
  have hae := ae_summable_norm_of_summable_integral (fun N ω => ‖F N ω‖ ^ 2) hF hsn
  filter_upwards [hae] with ω hω
  have ht := hω.tendsto_atTop_zero
  simp only [Real.norm_eq_abs, abs_sq] at ht
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp ht
  change Tendsto (fun N => Real.sqrt (‖F N ω‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) at hroot
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using hroot

/-- **Deviations plus mean limit**: if `F N − m N → 0` almost surely and `m N → L`, then
`F N → L` almost surely. -/
theorem ae_tendsto_of_tendsto_deviation {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (F : ℕ → Ω → ℂ) (m : ℕ → ℂ) (L : ℂ)
    (hF : ∀ N, Integrable (fun ω => ‖F N ω - m N‖ ^ 2) μ)
    (hs : Summable (fun N => ∫ ω, ‖F N ω - m N‖ ^ 2 ∂μ))
    (hm : Tendsto m atTop (𝓝 L)) :
    ∀ᵐ ω ∂μ, Tendsto (fun N => F N ω) atTop (𝓝 L) := by
  have hdev := ae_tendsto_zero_of_summable_integral_norm_sq μ
    (fun N ω => F N ω - m N) hF hs
  filter_upwards [hdev] with ω hω
  have h1 : Tendsto (fun N => (F N ω - m N) + m N) atTop (𝓝 (0 + L)) := hω.add hm
  simpa [sub_add_cancel] using h1

/-- A `B / N²` second-moment bound (for `N ≥ 1`) gives summability of the second moments. -/
theorem summable_integral_norm_sq_of_bound {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] (μ : Measure Ω) (F : ℕ → Ω → E) (B : ℝ)
    (h : ∀ N : ℕ, 1 ≤ N → ∫ ω, ‖F N ω‖ ^ 2 ∂μ ≤ B / (N : ℝ) ^ 2) :
    Summable (fun N => ∫ ω, ‖F N ω‖ ^ 2 ∂μ) := by
  have hbase : Summable (fun N : ℕ => B / (N : ℝ) ^ 2) := by
    have := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num : 1 < (2 : ℕ))
    simpa only [div_eq_mul_inv, one_mul] using this.mul_left B
  rw [← summable_nat_add_iff 1]
  have hshift : Summable (fun N : ℕ => B / ((N : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr hbase
    simpa [Nat.cast_add, Nat.cast_one] using this
  refine hshift.of_nonneg_of_le (fun N => ?_) (fun N => ?_)
  · exact integral_nonneg (fun ω => by positivity)
  · have hN : 1 ≤ N + 1 := by omega
    have hb := h (N + 1) hN
    simpa [Nat.cast_add, Nat.cast_one] using hb

end

end GUEStrongConvergence
