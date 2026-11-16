/-
# Variance tensorization for finite product measures

This module develops the product-measure variance decomposition and the two-factor
Efron--Stein/tensorization inequality, with exact section variances and all integrability
side conditions.  It is the analytic prerequisite for the finite-product Gaussian Poincaré
inequality.

For probability measures `μ` on `α` and `ν` on `β` and `F : α × β → ℝ` in `L²(μ ⊗ ν)`:

* `variance_prod_eq_integral_variance_fst_add_variance_meanFst` is the **exact law of total
  variance for a product**:
  `Var_{μ⊗ν}(F) = ∫ y, Var_μ(F(·,y)) dν(y) + Var_ν(y ↦ ∫ x, F(x,y) dμ(x))`.
* `variance_prod_le_integral_variance_fst_add_integral_variance_snd` is the **two-factor
  tensorization / Efron--Stein inequality**:
  `Var_{μ⊗ν}(F) ≤ ∫ y, Var_μ(F(·,y)) dν(y) + ∫ x, Var_ν(F(x,·)) dμ(x)`.

No conditional expectation is used: the decomposition is proved by Fubini directly, and the
inequality follows from the exact decomposition plus convexity of the variance, itself obtained
from the two-point identity and Cauchy--Schwarz.
-/
import GUEStrongConvergence.Probability.PolynomialPoincare
import Mathlib.MeasureTheory.Integral.Prod
open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory ENNReal NNReal Topology

namespace GUEStrongConvergence

noncomputable section

/-! ## A scalar Cauchy--Schwarz inequality -/

/-- For a probability measure, `(∫ f)² ≤ ∫ f²` for `f ∈ L²`. -/
theorem sq_integral_le_integral_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {f : α → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ ∫ x, f x ^ 2 ∂μ := by
  have hvar : variance f μ = ∫ x, f x ^ 2 ∂μ - (∫ x, f x ∂μ) ^ 2 :=
    variance_eq_sub hf
  have hnonneg : 0 ≤ variance f μ := variance_nonneg f μ
  linarith

/-! ## Section notation -/

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- The `x`-section of a function on a product, as a function of `x` at fixed `y`. -/
def sectionFst (F : α × β → ℝ) (y : β) : α → ℝ := fun x => F (x, y)

/-- The `y`-section of a function on a product, as a function of `y` at fixed `x`. -/
def sectionSnd (F : α × β → ℝ) (x : α) : β → ℝ := fun y => F (x, y)

/-- The mean of the `x`-section. -/
def meanFst (F : α × β → ℝ) (y : β) : ℝ := ∫ x, F (x, y) ∂μ

/-- The mean of the `y`-section. -/
def meanSnd (F : α × β → ℝ) (x : α) : ℝ := ∫ y, F (x, y) ∂ν

/-! ## Integrability of sections and section means -/

/-- Almost every `x`-section of an `L²` function is `L²`. -/
theorem ae_memLp_sectionFst {F : α × β → ℝ} (hF : MemLp F 2 (μ.prod ν)) :
    ∀ᵐ y ∂ν, MemLp (sectionFst F y) 2 μ := by
  have h1 : ∀ᵐ y ∂ν, Integrable (fun x => F (x, y)) μ :=
    (hF.integrable (by norm_num)).prod_left_ae
  have h2 : ∀ᵐ y ∂ν, Integrable (fun x => F (x, y) ^ 2) μ :=
    hF.integrable_sq.prod_left_ae
  filter_upwards [h1, h2] with y hy hy2
  exact (memLp_two_iff_integrable_sq hy.aestronglyMeasurable).mpr hy2

/-- Almost every `y`-section of an `L²` function is `L²`. -/
theorem ae_memLp_sectionSnd {F : α × β → ℝ} (hF : MemLp F 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, MemLp (sectionSnd F x) 2 ν := by
  have h1 : ∀ᵐ x ∂μ, Integrable (fun y => F (x, y)) ν :=
    (hF.integrable (by norm_num)).prod_right_ae
  have h2 : ∀ᵐ x ∂μ, Integrable (fun y => F (x, y) ^ 2) ν :=
    hF.integrable_sq.prod_right_ae
  filter_upwards [h1, h2] with x hx hx2
  exact (memLp_two_iff_integrable_sq hx.aestronglyMeasurable).mpr hx2

/-- The mean of the `x`-section is integrable. -/
theorem integrable_meanFst {F : α × β → ℝ} (hF : MemLp F 2 (μ.prod ν)) :
    Integrable (meanFst (μ := μ) F) ν :=
  (hF.integrable (by norm_num)).integral_prod_right

/-- The mean of the `y`-section is integrable. -/
theorem integrable_meanSnd {F : α × β → ℝ} (hF : MemLp F 2 (μ.prod ν)) :
    Integrable (meanSnd (ν := ν) F) μ :=
  (hF.integrable (by norm_num)).integral_prod_left

/-- The square of the mean of the `x`-section is integrable. -/
theorem integrable_meanFst_sq {F : α × β → ℝ} (hF : MemLp F 2 (μ.prod ν)) :
    Integrable (fun y => (meanFst (μ := μ) F y) ^ 2) ν := by
  have hK : Integrable (fun y => ∫ x, F (x, y) ^ 2 ∂μ) ν :=
    hF.integrable_sq.integral_prod_right
  have hmeas : AEStronglyMeasurable (fun y => (meanFst (μ := μ) F y) ^ 2) ν :=
    (integrable_meanFst hF).aestronglyMeasurable.pow 2
  refine hK.mono' hmeas ?_
  filter_upwards [ae_memLp_sectionFst hF] with y hy
  have hsq := sq_integral_le_integral_sq hy
  have hK0 : (0:ℝ) ≤ ∫ x, F (x, y) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (meanFst (μ := μ) F y))]
  exact hsq

/-- The square of the mean of the `y`-section is integrable. -/
theorem integrable_meanSnd_sq {F : α × β → ℝ} (hF : MemLp F 2 (μ.prod ν)) :
    Integrable (fun x => (meanSnd (ν := ν) F x) ^ 2) μ := by
  have hK : Integrable (fun x => ∫ y, F (x, y) ^ 2 ∂ν) μ :=
    hF.integrable_sq.integral_prod_left
  have hmeas : AEStronglyMeasurable (fun x => (meanSnd (ν := ν) F x) ^ 2) μ :=
    (integrable_meanSnd hF).aestronglyMeasurable.pow 2
  refine hK.mono' hmeas ?_
  filter_upwards [ae_memLp_sectionSnd hF] with x hx
  have hsq := sq_integral_le_integral_sq hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (meanSnd (ν := ν) F x))]
  exact hsq

/-- The mean of the `x`-section is `L²`. -/
theorem memLp_meanFst {F : α × β → ℝ} (hF : MemLp F 2 (μ.prod ν)) :
    MemLp (meanFst (μ := μ) F) 2 ν :=
  (memLp_two_iff_integrable_sq (integrable_meanFst hF).aestronglyMeasurable).mpr
    (integrable_meanFst_sq hF)

/-- The mean of the `y`-section is `L²`. -/
theorem memLp_meanSnd {F : α × β → ℝ} (hF : MemLp F 2 (μ.prod ν)) :
    MemLp (meanSnd (ν := ν) F) 2 μ :=
  (memLp_two_iff_integrable_sq (integrable_meanSnd hF).aestronglyMeasurable).mpr
    (integrable_meanSnd_sq hF)


/-! ## Exact variance decomposition for a product -/

/-- **Exact law of total variance for a product measure.**
For `F ∈ L²(μ ⊗ ν)`,
`Var_{μ⊗ν}(F) = ∫ y, Var_μ(F(·,y)) dν(y) + Var_ν(y ↦ ∫ x, F(x,y) dμ(x))`.
This is the exact conditional-variance decomposition, proved directly by Fubini. -/
theorem variance_prod_eq_integral_variance_fst_add_variance_meanFst
    {F : α × β → ℝ} (hF : MemLp F 2 (μ.prod ν)) :
    variance F (μ.prod ν)
      = (∫ y, variance (sectionFst F y) μ ∂ν)
        + variance (meanFst (μ := μ) F) ν := by
  have hF_int : Integrable F (μ.prod ν) := hF.integrable (by norm_num)
  have hF2_int : Integrable (fun z : α × β => F z ^ 2) (μ.prod ν) := hF.integrable_sq
  have hsec : ∀ᵐ y ∂ν, MemLp (sectionFst F y) 2 μ := ae_memLp_sectionFst hF
  have hG : MemLp (meanFst (μ := μ) F) 2 ν := memLp_meanFst hF
  have hK : Integrable (fun y => ∫ x, F (x, y) ^ 2 ∂μ) ν :=
    hF2_int.integral_prod_right
  have hG2 : Integrable (fun y => (meanFst (μ := μ) F y) ^ 2) ν :=
    integrable_meanFst_sq hF
  -- the first summand in the decomposition
  have hA : (∫ y, variance (sectionFst F y) μ ∂ν)
      = (∫ y, (∫ x, F (x, y) ^ 2 ∂μ) ∂ν)
        - ∫ y, (meanFst (μ := μ) F y) ^ 2 ∂ν := by
    have hcongr : (∫ y, variance (sectionFst F y) μ ∂ν)
        = ∫ y, ((∫ x, F (x, y) ^ 2 ∂μ)
            - (meanFst (μ := μ) F y) ^ 2) ∂ν := by
      refine integral_congr_ae ?_
      filter_upwards [hsec] with y hy
      rw [variance_eq_sub hy]
      simp only [sectionFst, meanFst, Pi.pow_apply]
    rw [hcongr]
    exact integral_sub hK hG2
  have hK_eq : (∫ y, (∫ x, F (x, y) ^ 2 ∂μ) ∂ν)
      = ∫ z : α × β, F z ^ 2 ∂(μ.prod ν) :=
    (integral_prod_symm (fun z : α × β => F z ^ 2) hF2_int).symm
  have hAeq : (∫ y, variance (sectionFst F y) μ ∂ν)
      = (∫ z : α × β, F z ^ 2 ∂(μ.prod ν))
        - ∫ y, (meanFst (μ := μ) F y) ^ 2 ∂ν := by
    rw [hA, hK_eq]
  have hB : variance (meanFst (μ := μ) F) ν
      = (∫ y, (meanFst (μ := μ) F y) ^ 2 ∂ν)
        - (∫ y, meanFst (μ := μ) F y ∂ν) ^ 2 :=
    variance_eq_sub hG
  have hGeq : (∫ y, meanFst (μ := μ) F y ∂ν)
      = ∫ z : α × β, F z ∂(μ.prod ν) :=
    (integral_prod_symm F hF_int).symm
  rw [variance_eq_sub hF, hAeq, hB, hGeq]
  simp only [Pi.pow_apply]
  ring



/-! ## The two-point identity -/

/-- Two-point form of the variance: `2 Var[X; μ] = ∫∫ (X x - X y)²`. -/
theorem two_mul_variance_eq_integral_prod_sq_sub {γ : Type*} [MeasurableSpace γ]
    {μ : Measure γ} [IsProbabilityMeasure μ] {f : γ → ℝ} (hf : MemLp f 2 μ) :
    2 * variance f μ
      = ∫ z : γ × γ, (f z.1 - f z.2) ^ 2 ∂(μ.prod μ) := by
  rw [integral_prod_sq_sub μ (hf.integrable (by norm_num)) hf.integrable_sq,
    variance_eq_sub hf]
  simp only [Pi.pow_apply]
  ring

/-! ## Integrability of the cross-square kernel -/

/-- The projection `(x, (y, y')) ↦ (x, y)` is measure preserving for a product of
probability measures. -/
theorem measurePreserving_projFst3 :
    MeasurePreserving (fun p : α × (β × β) => (p.1, p.2.1))
      (μ.prod (ν.prod ν)) (μ.prod ν) := by
  have h := (MeasurePreserving.id μ).prod
    (measurePreserving_fst (μ := ν) (ν := ν))
  convert h using 1
  ext p <;> rfl

/-- The projection `(x, (y, y')) ↦ (x, y')` is measure preserving for a product of
probability measures. -/
theorem measurePreserving_projSnd3 :
    MeasurePreserving (fun p : α × (β × β) => (p.1, p.2.2))
      (μ.prod (ν.prod ν)) (μ.prod ν) := by
  have h := (MeasurePreserving.id μ).prod
    (measurePreserving_snd (μ := ν) (ν := ν))
  convert h using 1
  ext p <;> rfl

/-- The squared difference of two `x`-sections, as a function on `α × (β × β)`. -/
def crossSq (F : α × β → ℝ) (p : α × (β × β)) : ℝ :=
  (F (p.1, p.2.1) - F (p.1, p.2.2)) ^ 2

theorem measurable_crossSq {F : α × β → ℝ} (hF : AEStronglyMeasurable F (μ.prod ν)) :
    AEStronglyMeasurable (crossSq F) (μ.prod (ν.prod ν)) := by
  have h1 : AEStronglyMeasurable (fun p : α × (β × β) => F (p.1, p.2.1))
      (μ.prod (ν.prod ν)) :=
    hF.comp_measurePreserving measurePreserving_projFst3
  have h2 : AEStronglyMeasurable (fun p : α × (β × β) => F (p.1, p.2.2))
      (μ.prod (ν.prod ν)) :=
    hF.comp_measurePreserving measurePreserving_projSnd3
  exact (h1.sub h2).pow 2

/-- The cross-square kernel is integrable for `F ∈ L²(μ ⊗ ν)`, by domination with
`2F(x,y)² + 2F(x,y')²`. -/
theorem integrable_crossSq {F : α × β → ℝ} (hF : MemLp F 2 (μ.prod ν)) :
    Integrable (crossSq F) (μ.prod (ν.prod ν)) := by
  have hU : Integrable (fun p : α × (β × β) =>
      2 * F (p.1, p.2.1) ^ 2 + 2 * F (p.1, p.2.2) ^ 2)
      (μ.prod (ν.prod ν)) :=
    ((hF.comp_measurePreserving measurePreserving_projFst3).integrable_sq.const_mul 2).add
      ((hF.comp_measurePreserving measurePreserving_projSnd3).integrable_sq.const_mul 2)
  refine hU.mono' (measurable_crossSq hF.aestronglyMeasurable) ?_
  filter_upwards with p
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h : (F (p.1, p.2.1) - F (p.1, p.2.2)) ^ 2
      ≤ 2 * F (p.1, p.2.1) ^ 2 + 2 * F (p.1, p.2.2) ^ 2 := by
    nlinarith [sq_nonneg (F (p.1, p.2.1) + F (p.1, p.2.2))]
  exact h


/-- If `g ∈ L²(ν)`, then `(y,y') ↦ (g y - g y')²` is integrable on `ν ⊗ ν`. -/
theorem integrable_sq_sub_prod {g : β → ℝ} (hg : MemLp g 2 ν) :
    Integrable (fun z : β × β => (g z.1 - g z.2) ^ 2) (ν.prod ν) := by
  have hU : Integrable (fun z : β × β => 2 * g z.1 ^ 2 + 2 * g z.2 ^ 2)
      (ν.prod ν) :=
    ((hg.comp_measurePreserving (measurePreserving_fst (μ := ν) (ν := ν))).integrable_sq.const_mul 2).add
      ((hg.comp_measurePreserving (measurePreserving_snd (μ := ν) (ν := ν))).integrable_sq.const_mul 2)
  refine hU.mono' ?_ ?_
  · have h1 : AEStronglyMeasurable (fun z : β × β => g z.1) (ν.prod ν) :=
      hg.aestronglyMeasurable.comp_measurePreserving (measurePreserving_fst (μ := ν) (ν := ν))
    have h2 : AEStronglyMeasurable (fun z : β × β => g z.2) (ν.prod ν) :=
      hg.aestronglyMeasurable.comp_measurePreserving (measurePreserving_snd (μ := ν) (ν := ν))
    exact (h1.sub h2).pow 2
  · filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (g z.1 + g z.2)]

/-- **Variance of the conditional mean is at most the mean conditional variance.**
For `F ∈ L²(μ ⊗ ν)`, the variance of `y ↦ ∫ x, F(x,y) dμ(x)` is at most
`∫ x, Var_ν(F(x,·)) dμ(x)`.  This is the convexity of the variance, proved with the two-point
identity and Cauchy--Schwarz. -/
theorem variance_meanFst_le_integral_variance_snd {F : α × β → ℝ}
    (hF : MemLp F 2 (μ.prod ν)) :
    variance (meanFst (μ := μ) F) ν ≤ ∫ x, variance (sectionSnd F x) ν ∂μ := by
  have hG : MemLp (meanFst (μ := μ) F) 2 ν := memLp_meanFst hF
  have hLHS_int : Integrable
      (fun z : β × β => (meanFst (μ := μ) F z.1 - meanFst (μ := μ) F z.2) ^ 2)
      (ν.prod ν) := integrable_sq_sub_prod hG
  have hRHS_int : Integrable (fun z : β × β => ∫ x, crossSq F (x, z) ∂μ) (ν.prod ν) :=
    (integrable_crossSq hF).integral_prod_right
  have hsec1 : ∀ᵐ z ∂(ν.prod ν), MemLp (sectionFst F z.1) 2 μ :=
    (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := ν)).ae (ae_memLp_sectionFst hF)
  have hsec2 : ∀ᵐ z ∂(ν.prod ν), MemLp (sectionFst F z.2) 2 μ :=
    (Measure.quasiMeasurePreserving_snd (μ := ν) (ν := ν)).ae (ae_memLp_sectionFst hF)
  have hpoint : ∀ᵐ z ∂(ν.prod ν),
      (meanFst (μ := μ) F z.1 - meanFst (μ := μ) F z.2) ^ 2
        ≤ ∫ x, crossSq F (x, z) ∂μ := by
    filter_upwards [hsec1, hsec2] with z h1 h2
    have hz : MemLp (fun x => F (x, z.1) - F (x, z.2)) 2 μ := h1.sub h2
    have hsub : (∫ x, (F (x, z.1) - F (x, z.2)) ∂μ)
        = meanFst (μ := μ) F z.1 - meanFst (μ := μ) F z.2 := by
      simp only [meanFst]
      exact integral_sub (h1.integrable (by norm_num)) (h2.integrable (by norm_num))
    rw [← hsub]
    simpa [crossSq] using sq_integral_le_integral_sq hz
  have hmono : (∫ z : β × β,
        (meanFst (μ := μ) F z.1 - meanFst (μ := μ) F z.2) ^ 2 ∂(ν.prod ν))
      ≤ ∫ z : β × β, (∫ x, crossSq F (x, z) ∂μ) ∂(ν.prod ν) :=
    integral_mono_ae hLHS_int hRHS_int hpoint
  have hswap := integral_integral_swap (μ := μ) (ν := ν.prod ν)
    (f := fun x (z : β × β) => crossSq F (x, z)) (integrable_crossSq hF)
  have hinner : (∫ z : β × β, (∫ x, crossSq F (x, z) ∂μ) ∂(ν.prod ν))
      = ∫ x, 2 * variance (sectionSnd F x) ν ∂μ := by
    have hsec : ∀ᵐ x ∂μ, MemLp (sectionSnd F x) 2 ν := ae_memLp_sectionSnd hF
    have hcongr : ∀ᵐ x ∂μ,
        (∫ z : β × β, crossSq F (x, z) ∂(ν.prod ν))
          = 2 * variance (sectionSnd F x) ν := by
      filter_upwards [hsec] with x hx
      have h := two_mul_variance_eq_integral_prod_sq_sub (μ := ν) hx
      simpa [crossSq, sectionSnd] using h.symm
    calc (∫ z : β × β, (∫ x, crossSq F (x, z) ∂μ) ∂(ν.prod ν))
        = ∫ x, (∫ z : β × β, crossSq F (x, z) ∂(ν.prod ν)) ∂μ := hswap.symm
      _ = ∫ x, 2 * variance (sectionSnd F x) ν ∂μ := integral_congr_ae hcongr
  have htwo := two_mul_variance_eq_integral_prod_sq_sub hG
  rw [← htwo, hinner] at hmono
  rw [integral_const_mul] at hmono
  linarith


/-- **Two-factor variance tensorization / Efron--Stein inequality.**
For `F ∈ L²(μ ⊗ ν)`,
`Var_{μ⊗ν}(F) ≤ ∫ y, Var_μ(F(·,y)) dν(y) + ∫ x, Var_ν(F(x,·)) dμ(x)`.
This follows from the exact product decomposition and convexity of the variance. -/
theorem variance_prod_le_integral_variance_fst_add_integral_variance_snd
    {F : α × β → ℝ} (hF : MemLp F 2 (μ.prod ν)) :
    variance F (μ.prod ν)
      ≤ (∫ y, variance (sectionFst F y) μ ∂ν)
        + ∫ x, variance (sectionSnd F x) ν ∂μ := by
  have hdec := variance_prod_eq_integral_variance_fst_add_variance_meanFst hF
  have hmean := variance_meanFst_le_integral_variance_snd hF
  rw [hdec]
  linarith


/-- The section variances of an `L²` function are integrable. -/
theorem integrable_variance_sectionFst {F : α × β → ℝ} (hF : MemLp F 2 (μ.prod ν)) :
    Integrable (fun y => variance (sectionFst F y) μ) ν := by
  have hsec : ∀ᵐ y ∂ν, MemLp (sectionFst F y) 2 μ := ae_memLp_sectionFst hF
  have hK : Integrable (fun y => ∫ x, F (x, y) ^ 2 ∂μ) ν :=
    hF.integrable_sq.integral_prod_right
  have hG2 : Integrable (fun y => (meanFst (μ := μ) F y) ^ 2) ν :=
    integrable_meanFst_sq hF
  refine (hK.sub hG2).congr ?_
  filter_upwards [hsec] with y hy
  rw [variance_eq_sub hy]
  simp only [sectionFst, meanFst, Pi.sub_apply, Pi.pow_apply]

/-- The section variances in the second factor of an `L²` function are integrable. -/
theorem integrable_variance_sectionSnd {F : α × β → ℝ} (hF : MemLp F 2 (μ.prod ν)) :
    Integrable (fun x => variance (sectionSnd F x) ν) μ := by
  have hsec : ∀ᵐ x ∂μ, MemLp (sectionSnd F x) 2 ν := ae_memLp_sectionSnd hF
  have hK : Integrable (fun x => ∫ y, F (x, y) ^ 2 ∂ν) μ :=
    hF.integrable_sq.integral_prod_left
  have hH2 : Integrable (fun x => (meanSnd (ν := ν) F x) ^ 2) μ :=
    integrable_meanSnd_sq hF
  refine (hK.sub hH2).congr ?_
  filter_upwards [hsec] with x hx
  rw [variance_eq_sub hx]
  simp only [sectionSnd, meanSnd, Pi.sub_apply, Pi.pow_apply]


/-- **Two-factor Gaussian Poincaré inequality.**
For `F ∈ L²(γ ⊗ γ)` whose coordinate sections are differentiable and of polynomial growth, with
partial derivatives `Fx` and `Fy` also `L²`,
`Var_{γ⊗γ}(F) ≤ ∫∫ (∂_x F)² + ∫∫ (∂_y F)²`,
i.e. the tensorized coordinate gradient bound in the two-coordinate case. -/
theorem gaussian_poincare_prod_two
    {F Fx Fy : ℝ × ℝ → ℝ}
    (hF : MemLp F 2 ((gaussianReal 0 1).prod (gaussianReal 0 1)))
    (hFx_mem : MemLp Fx 2 ((gaussianReal 0 1).prod (gaussianReal 0 1)))
    (hFy_mem : MemLp Fy 2 ((gaussianReal 0 1).prod (gaussianReal 0 1)))
    (hderivx : ∀ᵐ y ∂(gaussianReal 0 1),
      ∀ x, HasDerivAt (fun x => F (x, y)) (Fx (x, y)) x)
    (hderivy : ∀ᵐ x ∂(gaussianReal 0 1),
      ∀ y, HasDerivAt (fun y => F (x, y)) (Fy (x, y)) y)
    (hpolyx : ∀ᵐ y ∂(gaussianReal 0 1),
      PolyGrowth (fun x => F (x, y)) ∧ PolyGrowth (fun x => Fx (x, y)))
    (hpolyy : ∀ᵐ x ∂(gaussianReal 0 1),
      PolyGrowth (fun y => F (x, y)) ∧ PolyGrowth (fun y => Fy (x, y))) :
    variance F ((gaussianReal 0 1).prod (gaussianReal 0 1))
      ≤ (∫ y, ∫ x, (Fx (x, y)) ^ 2 ∂(gaussianReal 0 1) ∂(gaussianReal 0 1))
        + ∫ x, ∫ y, (Fy (x, y)) ^ 2 ∂(gaussianReal 0 1) ∂(gaussianReal 0 1) := by
  have hten := variance_prod_le_integral_variance_fst_add_integral_variance_snd
    (μ := gaussianReal 0 1) (ν := gaussianReal 0 1) hF
  have hA : (∫ y, variance (sectionFst F y) (gaussianReal 0 1) ∂(gaussianReal 0 1))
      ≤ ∫ y, (∫ x, (Fx (x, y)) ^ 2 ∂(gaussianReal 0 1)) ∂(gaussianReal 0 1) := by
    refine integral_mono_ae (integrable_variance_sectionFst hF)
      hFx_mem.integrable_sq.integral_prod_right ?_
    filter_upwards [hderivx, hpolyx, ae_memLp_sectionFst hF] with y hd hp hmem
    have hpoin := gaussian_poincare_variance_poly (f := fun x => F (x, y))
      (f' := fun x => Fx (x, y)) hd hp.1 hp.2
    have hv : variance (sectionFst F y) (gaussianReal 0 1)
        = (∫ x, F (x, y) ^ 2 ∂(gaussianReal 0 1))
          - (∫ x, F (x, y) ∂(gaussianReal 0 1)) ^ 2 := by
      rw [variance_eq_sub hmem]
      simp only [sectionFst, Pi.pow_apply]
    rw [← hv] at hpoin
    simpa [sectionFst] using hpoin
  have hB : (∫ x, variance (sectionSnd F x) (gaussianReal 0 1) ∂(gaussianReal 0 1))
      ≤ ∫ x, (∫ y, (Fy (x, y)) ^ 2 ∂(gaussianReal 0 1)) ∂(gaussianReal 0 1) := by
    refine integral_mono_ae (integrable_variance_sectionSnd hF)
      hFy_mem.integrable_sq.integral_prod_left ?_
    filter_upwards [hderivy, hpolyy, ae_memLp_sectionSnd hF] with x hd hp hmem
    have hpoin := gaussian_poincare_variance_poly (f := fun y => F (x, y))
      (f' := fun y => Fy (x, y)) hd hp.1 hp.2
    have hv : variance (sectionSnd F x) (gaussianReal 0 1)
        = (∫ y, F (x, y) ^ 2 ∂(gaussianReal 0 1))
          - (∫ y, F (x, y) ∂(gaussianReal 0 1)) ^ 2 := by
      rw [variance_eq_sub hmem]
      simp only [sectionSnd, Pi.pow_apply]
    rw [← hv] at hpoin
    simpa [sectionSnd] using hpoin
  linarith

end

end GUEStrongConvergence
