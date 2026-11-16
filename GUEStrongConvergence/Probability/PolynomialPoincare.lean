/-
# Gaussian Poincaré inequality for polynomially growing functions

This module discharges the analytic hypotheses of
`GUEStrongConvergence.gaussian_poincare` for functions of polynomial growth, and derives the
variance form of the inequality from the genuine Poincaré inequality rather than assuming it.

The main new analytic input is a **two-sided polynomial tail bound** for the moving tail
`gueTail g x = ∫ t in Ioi x, g t * ρ t`: for polynomially growing `g` with mean zero
(`∫ g ρ = 0`) there are constants `M, N` with

  `|gueTail g x| ≤ M * (1 + |x|)^N * ρ x`   for every `x`.

The mean-zero hypothesis is essential: without it the Stein kernel
`h x = -√(2π) exp(x²/2) gueTail g x` does not decay on the negative half-line (for `g = 1` it
blows up like `exp(x²/2)`), and the Stein-kernel Poincaré proof cannot be closed.
-/
import GUEStrongConvergence.Probability.Variance
open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace ENNReal NNReal Topology

namespace GUEStrongConvergence

noncomputable section

/-! ## The polynomial-growth class -/

/-- `f` has polynomial growth: `|f x| ≤ C (1 + |x|)^k` for some `C ≥ 0` and `k`. -/
def PolyGrowth (f : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ k : ℕ, ∀ x, |f x| ≤ C * (1 + |x|) ^ k

theorem polyGrowth_const (c : ℝ) : PolyGrowth (fun _ : ℝ => c) := by
  refine ⟨|c|, abs_nonneg _, 0, fun x => ?_⟩
  simp

theorem polyGrowth_id : PolyGrowth (fun x : ℝ => x) := by
  refine ⟨1, zero_le_one, 1, fun x => ?_⟩
  rw [pow_one, one_mul]
  nlinarith [abs_nonneg x, le_abs_self x]

theorem polyGrowth_neg {f : ℝ → ℝ} (hf : PolyGrowth f) : PolyGrowth (fun x => -f x) := by
  obtain ⟨C, hC0, k, hC⟩ := hf
  exact ⟨C, hC0, k, fun x => by simpa using hC x⟩

theorem polyGrowth_add {f g : ℝ → ℝ} (hf : PolyGrowth f) (hg : PolyGrowth g) :
    PolyGrowth (fun x => f x + g x) := by
  obtain ⟨Cf, hCf0, kf, hCf⟩ := hf
  obtain ⟨Cg, hCg0, kg, hCg⟩ := hg
  refine ⟨Cf + Cg, by linarith, max kf kg, fun x => ?_⟩
  have hb1 : (1:ℝ) ≤ 1 + |x| := by linarith [abs_nonneg x]
  have hfk : (1 + |x|) ^ kf ≤ (1 + |x|) ^ max kf kg :=
    pow_le_pow_right₀ hb1 (le_max_left _ _)
  have hgk : (1 + |x|) ^ kg ≤ (1 + |x|) ^ max kf kg :=
    pow_le_pow_right₀ hb1 (le_max_right _ _)
  have h1 : |f x| ≤ Cf * (1 + |x|) ^ max kf kg :=
    (hCf x).trans (mul_le_mul_of_nonneg_left hfk hCf0)
  have h2 : |g x| ≤ Cg * (1 + |x|) ^ max kf kg :=
    (hCg x).trans (mul_le_mul_of_nonneg_left hgk hCg0)
  calc |f x + g x| ≤ |f x| + |g x| := abs_add_le _ _
    _ ≤ Cf * (1 + |x|) ^ max kf kg + Cg * (1 + |x|) ^ max kf kg := add_le_add h1 h2
    _ = (Cf + Cg) * (1 + |x|) ^ max kf kg := by ring

theorem polyGrowth_sub {f g : ℝ → ℝ} (hf : PolyGrowth f) (hg : PolyGrowth g) :
    PolyGrowth (fun x => f x - g x) := by
  simpa [sub_eq_add_neg] using polyGrowth_add hf (polyGrowth_neg hg)

theorem polyGrowth_mul {f g : ℝ → ℝ} (hf : PolyGrowth f) (hg : PolyGrowth g) :
    PolyGrowth (fun x => f x * g x) := by
  obtain ⟨Cf, hCf0, kf, hCf⟩ := hf
  obtain ⟨Cg, hCg0, kg, hCg⟩ := hg
  refine ⟨Cf * Cg, mul_nonneg hCf0 hCg0, kf + kg, fun x => ?_⟩
  have hb : (0:ℝ) ≤ 1 + |x| := by positivity
  calc |f x * g x| = |f x| * |g x| := abs_mul _ _
    _ ≤ (Cf * (1 + |x|) ^ kf) * (Cg * (1 + |x|) ^ kg) :=
        mul_le_mul (hCf x) (hCg x) (abs_nonneg _) (by positivity)
    _ = Cf * Cg * (1 + |x|) ^ (kf + kg) := by rw [pow_add]; ring

theorem polyGrowth_const_mul {f : ℝ → ℝ} (c : ℝ) (hf : PolyGrowth f) :
    PolyGrowth (fun x => c * f x) := by
  simpa [mul_comm] using polyGrowth_mul (polyGrowth_const c) hf

theorem polyGrowth_pow {f : ℝ → ℝ} (hf : PolyGrowth f) (n : ℕ) :
    PolyGrowth (fun x => f x ^ n) := by
  induction n with
  | zero => simpa using polyGrowth_const (1:ℝ)
  | succ n ih =>
      simpa [pow_succ] using polyGrowth_mul ih hf

/-! ## Density-weighted polynomial bounds -/

/-- `F` is a.e. strongly measurable and dominated by a polynomial multiple of the standard
Gaussian density. -/
def PDFPolyGrowth (F : ℝ → ℝ) : Prop :=
  AEStronglyMeasurable F (volume : Measure ℝ) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x, |F x| ≤ C * (1 + |x|) ^ N * gaussianPDFReal 0 1 x

theorem pdfPolyGrowth_of_polyGrowth_mul_pdf {q : ℝ → ℝ} (hq : PolyGrowth q)
    (hqm : AEStronglyMeasurable q (volume : Measure ℝ)) :
    PDFPolyGrowth (fun x => q x * gaussianPDFReal 0 1 x) := by
  obtain ⟨C, hC0, k, hC⟩ := hq
  refine ⟨hqm.mul (by fun_prop), C, hC0, k, fun x => ?_⟩
  rw [abs_mul, abs_of_nonneg (gaussianPDFReal_nonneg 0 1 x)]
  calc |q x| * gaussianPDFReal 0 1 x
      ≤ (C * (1 + |x|) ^ k) * gaussianPDFReal 0 1 x :=
        mul_le_mul_of_nonneg_right (hC x) (gaussianPDFReal_nonneg 0 1 x)
    _ = C * (1 + |x|) ^ k * gaussianPDFReal 0 1 x := by ring

theorem pdfPolyGrowth_mul_polyGrowth {F q : ℝ → ℝ} (hF : PDFPolyGrowth F)
    (hq : PolyGrowth q) (hqm : AEStronglyMeasurable q (volume : Measure ℝ)) :
    PDFPolyGrowth (fun x => q x * F x) := by
  obtain ⟨hFm, C, hC0, N, hC⟩ := hF
  obtain ⟨D, hD0, k, hD⟩ := hq
  refine ⟨hqm.mul hFm, D * C, mul_nonneg hD0 hC0, k + N, fun x => ?_⟩
  have hρ : (0:ℝ) ≤ gaussianPDFReal 0 1 x := gaussianPDFReal_nonneg 0 1 x
  have hb : (0:ℝ) ≤ 1 + |x| := by positivity
  calc |q x * F x| = |q x| * |F x| := abs_mul _ _
    _ ≤ (D * (1 + |x|) ^ k) * (C * (1 + |x|) ^ N * gaussianPDFReal 0 1 x) :=
        mul_le_mul (hD x) (hC x) (abs_nonneg _) (by positivity)
    _ = D * C * (1 + |x|) ^ (k + N) * gaussianPDFReal 0 1 x := by
        rw [pow_add]; ring

theorem pdfPolyGrowth_add {F G : ℝ → ℝ} (hF : PDFPolyGrowth F) (hG : PDFPolyGrowth G) :
    PDFPolyGrowth (fun x => F x + G x) := by
  obtain ⟨hFm, CF, hCF0, NF, hCF⟩ := hF
  obtain ⟨hGm, CG, hCG0, NG, hCG⟩ := hG
  refine ⟨hFm.add hGm, CF + CG, by linarith, max NF NG, fun x => ?_⟩
  have hb1 : (1:ℝ) ≤ 1 + |x| := by linarith [abs_nonneg x]
  have hρ : (0:ℝ) ≤ gaussianPDFReal 0 1 x := gaussianPDFReal_nonneg 0 1 x
  have h1 : |F x| ≤ CF * (1 + |x|) ^ max NF NG * gaussianPDFReal 0 1 x := by
    refine (hCF x).trans ?_
    have := pow_le_pow_right₀ hb1 (le_max_left NF NG)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hCF0) hρ
  have h2 : |G x| ≤ CG * (1 + |x|) ^ max NF NG * gaussianPDFReal 0 1 x := by
    refine (hCG x).trans ?_
    have := pow_le_pow_right₀ hb1 (le_max_right NF NG)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hCG0) hρ
  calc |F x + G x| ≤ |F x| + |G x| := abs_add_le _ _
    _ ≤ CF * (1 + |x|) ^ max NF NG * gaussianPDFReal 0 1 x
          + CG * (1 + |x|) ^ max NF NG * gaussianPDFReal 0 1 x := add_le_add h1 h2
    _ = (CF + CG) * (1 + |x|) ^ max NF NG * gaussianPDFReal 0 1 x := by ring

theorem pdfPolyGrowth_const_mul (c : ℝ) {F : ℝ → ℝ} (hF : PDFPolyGrowth F) :
    PDFPolyGrowth (fun x => c * F x) := by
  obtain ⟨hFm, C, hC0, N, hC⟩ := hF
  refine ⟨hFm.const_mul c, |c| * C, mul_nonneg (abs_nonneg c) hC0, N, fun x => ?_⟩
  calc |c * F x| = |c| * |F x| := abs_mul _ _
    _ ≤ |c| * (C * (1 + |x|) ^ N * gaussianPDFReal 0 1 x) :=
        mul_le_mul_of_nonneg_left (hC x) (abs_nonneg c)
    _ = |c| * C * (1 + |x|) ^ N * gaussianPDFReal 0 1 x := by ring

/-- A density-polynomial majorant makes a function Lebesgue integrable. -/
theorem integrable_of_pdfPolyGrowth {F : ℝ → ℝ} (hF : PDFPolyGrowth F) : Integrable F := by
  obtain ⟨hFm, C, hC0, N, hC⟩ := hF
  have hdom : Integrable (fun x : ℝ => C * ((1 + |x|) ^ N * gaussianPDFReal 0 1 x)) :=
    (integrable_one_add_abs_pow_mul_gaussianPDFReal N).const_mul C
  refine hdom.mono' hFm ?_
  filter_upwards with x
  rw [Real.norm_eq_abs]
  calc |F x| ≤ C * (1 + |x|) ^ N * gaussianPDFReal 0 1 x := hC x
    _ = C * ((1 + |x|) ^ N * gaussianPDFReal 0 1 x) := by ring

theorem integrable_mul_gaussianPDFReal_of_polyGrowth {f : ℝ → ℝ} (hf : PolyGrowth f)
    (hfm : AEStronglyMeasurable f (volume : Measure ℝ)) :
    Integrable (fun x => f x * gaussianPDFReal 0 1 x) :=
  integrable_of_pdfPolyGrowth (pdfPolyGrowth_of_polyGrowth_mul_pdf hf hfm)

/-! ## Transfer to the Gaussian measure -/

theorem integrable_gaussianReal_iff_integrable_mul_gaussianPDFReal {F : ℝ → ℝ} :
    Integrable F (gaussianReal 0 1) ↔
      Integrable (fun x => F x * gaussianPDFReal 0 1 x) (volume : Measure ℝ) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1:ℝ≥0) ≠ 0)]
  rw [integrable_withDensity_iff (measurable_gaussianPDF (μ := 0) (v := 1))
    (by filter_upwards with t using gaussianPDF_lt_top (μ := 0) (v := 1) (x := t))]
  refine integrable_congr (ae_of_all _ fun x => ?_)
  simp only [toReal_gaussianPDF]

theorem integrable_gaussianReal_of_polyGrowth {F : ℝ → ℝ} (hF : PolyGrowth F)
    (hFm : AEStronglyMeasurable F (volume : Measure ℝ)) : Integrable F (gaussianReal 0 1) := by
  refine integrable_gaussianReal_iff_integrable_mul_gaussianPDFReal.mpr ?_
  exact integrable_of_pdfPolyGrowth
    (pdfPolyGrowth_of_polyGrowth_mul_pdf hF hFm)

theorem memLp_two_of_polyGrowth {F : ℝ → ℝ} (hF : PolyGrowth F)
    (hFm : AEStronglyMeasurable F (volume : Measure ℝ)) : MemLp F 2 (gaussianReal 0 1) := by
  have hFmγ : AEStronglyMeasurable F (gaussianReal 0 1) :=
    hFm.mono_ac (gaussianReal_absolutelyContinuous 0 (by norm_num : (1:ℝ≥0) ≠ 0))
  refine (memLp_two_iff_integrable_sq hFmγ).mpr ?_
  exact integrable_gaussianReal_of_polyGrowth (polyGrowth_pow hF 2) (hFm.pow 2)

/-! ## Decay of polynomial multiples of the density -/

theorem tendsto_mul_gaussianPDFReal_of_polyGrowth {F : ℝ → ℝ} (hF : PolyGrowth F) :
    Tendsto (fun x => F x * gaussianPDFReal 0 1 x) atTop (𝓝 0) := by
  obtain ⟨C, hC0, k, hC⟩ := hF
  have hmaj : Tendsto (fun x : ℝ => C * ((1 + |x|) ^ k * gaussianPDFReal 0 1 x))
      atTop (𝓝 0) := by
    simpa using (tendsto_one_add_abs_pow_mul_gaussianPDFReal k).const_mul C
  refine squeeze_zero_norm' (a := fun x => C * ((1 + |x|) ^ k * gaussianPDFReal 0 1 x)) ?_ hmaj
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussianPDFReal_nonneg 0 1 x)]
  calc |F x| * gaussianPDFReal 0 1 x
      ≤ (C * (1 + |x|) ^ k) * gaussianPDFReal 0 1 x :=
        mul_le_mul_of_nonneg_right (hC x) (gaussianPDFReal_nonneg 0 1 x)
    _ = C * ((1 + |x|) ^ k * gaussianPDFReal 0 1 x) := by ring

theorem tendsto_mul_gaussianPDFReal_of_polyGrowth_atBot {F : ℝ → ℝ} (hF : PolyGrowth F) :
    Tendsto (fun x => F x * gaussianPDFReal 0 1 x) atBot (𝓝 0) := by
  obtain ⟨C, hC0, k, hC⟩ := hF
  have hmaj : Tendsto (fun x : ℝ => C * ((1 + |x|) ^ k * gaussianPDFReal 0 1 x))
      atBot (𝓝 0) := by
    simpa using (tendsto_one_add_abs_pow_mul_gaussianPDFReal_atBot k).const_mul C
  refine squeeze_zero_norm' (a := fun x => C * ((1 + |x|) ^ k * gaussianPDFReal 0 1 x)) ?_ hmaj
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussianPDFReal_nonneg 0 1 x)]
  calc |F x| * gaussianPDFReal 0 1 x
      ≤ (C * (1 + |x|) ^ k) * gaussianPDFReal 0 1 x :=
        mul_le_mul_of_nonneg_right (hC x) (gaussianPDFReal_nonneg 0 1 x)
    _ = C * ((1 + |x|) ^ k * gaussianPDFReal 0 1 x) := by ring


/-! ## A two-sided tail bound for polynomially growing mean-zero functions -/

/-- Reflection `x ↦ g (-x)`. -/
def gaussReflect (g : ℝ → ℝ) : ℝ → ℝ := fun x => g (-x)

theorem measurable_gaussReflect {g : ℝ → ℝ} (hg : Measurable g) :
    Measurable (gaussReflect g) :=
  hg.comp measurable_neg

theorem polyGrowth_gaussReflect {g : ℝ → ℝ} (hg : PolyGrowth g) :
    PolyGrowth (gaussReflect g) := by
  obtain ⟨C, hC0, k, hC⟩ := hg
  refine ⟨C, hC0, k, fun x => ?_⟩
  simpa [gaussReflect] using hC (-x)

/-- `1 + a^(2k) ≤ 2 (1+a)^(2k)` for `a ≥ 0`. -/
theorem one_add_pow_even_le_two_mul (a : ℝ) (ha : 0 ≤ a) (k : ℕ) :
    1 + a ^ (2 * k) ≤ 2 * (1 + a) ^ (2 * k) := by
  have hbase : (1:ℝ) ≤ 1 + a := by linarith
  have h1 : (1:ℝ) ≤ (1 + a) ^ (2 * k) := one_le_pow₀ hbase
  have h2 : a ^ (2 * k) ≤ (1 + a) ^ (2 * k) :=
    pow_le_pow_left₀ ha (by linarith : a ≤ 1 + a) (2 * k)
  nlinarith

/-- The Gaussian density is minimised at `|x| = 1` on the interval `[-1,1]`. -/
theorem gaussianPDFReal_one_le_of_abs_le_one {x : ℝ} (hx : |x| ≤ 1) :
    gaussianPDFReal 0 1 1 ≤ gaussianPDFReal 0 1 x := by
  have hx2 : x ^ 2 ≤ 1 := by
    have h := pow_le_pow_left₀ (abs_nonneg x) hx 2
    simpa [sq_abs] using h
  have hexp : Real.exp (-((1:ℝ) - 0) ^ 2 / (2 * ((1:ℝ≥0):ℝ)))
      ≤ Real.exp (-(x - 0) ^ 2 / (2 * ((1:ℝ≥0):ℝ))) := by
    apply Real.exp_le_exp.mpr
    norm_num
    nlinarith
  have hsqrt : Real.sqrt (2 * Real.pi * ((1:ℝ≥0):ℝ)) = Real.sqrt (2 * Real.pi) := by
    norm_num
  unfold gaussianPDFReal
  rw [hsqrt]
  exact mul_le_mul_of_nonneg_left hexp (by positivity)

/-- Change of variables `x ↦ -x` leaves `∫ g ρ` unchanged. -/
theorem integral_gaussReflect_mul_gaussianPDFReal {g : ℝ → ℝ} (hg : Measurable g) :
    ∫ x, gaussReflect g x * gaussianPDFReal 0 1 x
      = ∫ x, g x * gaussianPDFReal 0 1 x := by
  have hmap : Measure.map (fun x : ℝ => -x) (volume : Measure ℝ) = volume :=
    Measure.map_neg_eq_self (volume : Measure ℝ)
  have hf : AEStronglyMeasurable (fun y : ℝ => g y * gaussianPDFReal 0 1 y)
      (Measure.map (fun x : ℝ => -x) (volume : Measure ℝ)) :=
    ((hg.mul (by fun_prop : Measurable (fun y : ℝ => gaussianPDFReal 0 1 y))).aestronglyMeasurable)
  have h := integral_map (μ := (volume : Measure ℝ)) (φ := fun x : ℝ => -x)
    (f := fun y : ℝ => g y * gaussianPDFReal 0 1 y) measurable_neg.aemeasurable hf
  rw [hmap] at h
  simp_rw [gaussianPDFReal_neg] at h
  simpa [gaussReflect] using h.symm

/-- On the negative half-line the tail of `g` is minus the reflected tail. -/
theorem gueTail_eq_neg_gueTail_gaussReflect {g : ℝ → ℝ} (hg : Measurable g)
    (hgr : PolyGrowth g) (hzero : ∫ x, g x * gaussianPDFReal 0 1 x = 0)
    (x : ℝ) :
    gueTail g x = -gueTail (gaussReflect g) (-x) := by
  have hIntg : Integrable (fun t : ℝ => g t * gaussianPDFReal 0 1 t) :=
    integrable_mul_gaussianPDFReal_of_polyGrowth hgr hg.aestronglyMeasurable
  have hIntG : Integrable (fun s : ℝ => gaussReflect g s * gaussianPDFReal 0 1 s) :=
    integrable_mul_gaussianPDFReal_of_polyGrowth (polyGrowth_gaussReflect hgr)
      (measurable_gaussReflect hg).aestronglyMeasurable
  have hzeroG : ∫ s, gaussReflect g s * gaussianPDFReal 0 1 s = 0 := by
    rw [integral_gaussReflect_mul_gaussianPDFReal hg, hzero]
  have hcomp : ∫ s in Set.Iic (-x), gaussReflect g s * gaussianPDFReal 0 1 s
      = gueTail g x := by
    have h := integral_comp_neg_Iic (-x)
      (fun t : ℝ => g t * gaussianPDFReal 0 1 t)
    rw [neg_neg] at h
    rw [show gueTail g x = ∫ t in Set.Ioi x, g t * gaussianPDFReal 0 1 t from rfl]
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Iic (fun s _ => ?_)
    simp only [gaussReflect, gaussianPDFReal_neg]
  have hsplit := integral_add_compl (μ := (volume : Measure ℝ))
    (s := Set.Iic (-x)) measurableSet_Iic hIntG
  rw [Set.compl_Iic] at hsplit
  rw [hcomp, hzeroG] at hsplit
  have htail : ∫ s in Set.Ioi (-x), gaussReflect g s * gaussianPDFReal 0 1 s
      = gueTail (gaussReflect g) (-x) := rfl
  rw [htail] at hsplit
  linarith

/-- Right-tail polynomial decay for polynomially growing `g` (no mean-zero needed). -/
theorem exists_abs_gueTail_le_poly_mul_gaussianPDFReal_of_one_le {g : ℝ → ℝ}
    (hg : Measurable g) (hgr : PolyGrowth g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x : ℝ, 1 ≤ x →
      |gueTail g x| ≤ C * (1 + |x|) ^ N * gaussianPDFReal 0 1 x := by
  obtain ⟨C, hC0, k, hC⟩ := hgr
  obtain ⟨Ck, hCk0, hCk⟩ := exists_integral_Ioi_pow_mul_gaussianPDFReal_le (2 * k)
  have hbig : Integrable (fun t : ℝ => C * ((1 + t) ^ k * gaussianPDFReal 0 1 t)) := by
    have hbase : Integrable (fun t : ℝ => (1 + |t|) ^ k * gaussianPDFReal 0 1 t) :=
      integrable_one_add_abs_pow_mul_gaussianPDFReal k
    refine (hbase.const_mul C).mono' ?_ ?_
    · exact (by fun_prop : Measurable (fun t : ℝ => C * ((1 + t) ^ k *
        gaussianPDFReal 0 1 t))).aestronglyMeasurable
    · filter_upwards with t
      have hρ : (0:ℝ) ≤ gaussianPDFReal 0 1 t := gaussianPDFReal_nonneg 0 1 t
      have hle : |1 + t| ≤ 1 + |t| := by
        simpa using abs_add_le (1:ℝ) t
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hC0,
        abs_of_nonneg hρ, abs_pow]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hle k) hρ) hC0
  refine ⟨C * 2 ^ (k + 1) * (2 + Ck) * 2,
    mul_nonneg (mul_nonneg (mul_nonneg hC0 (pow_nonneg (by norm_num) _)) (by linarith))
      (by norm_num), 2 * k, fun x hx => ?_⟩
  have hdecay := abs_gueTail_le_mul_gaussianPDFReal hg (by fun_prop : Measurable
    (fun t : ℝ => gaussianPDFReal 0 1 t)) hC0 hCk0 hC hbig hCk hx
  have hx0 : (0:ℝ) ≤ x := by linarith
  have hpow : 1 + x ^ (2 * k) ≤ 2 * (1 + |x|) ^ (2 * k) := by
    have := one_add_pow_even_le_two_mul x hx0 k
    rwa [abs_of_nonneg hx0]
  have hρ : (0:ℝ) ≤ gaussianPDFReal 0 1 x := gaussianPDFReal_nonneg 0 1 x
  have hconst : (0:ℝ) ≤ C * 2 ^ (k + 1) * (2 + Ck) :=
    mul_nonneg (mul_nonneg hC0 (pow_nonneg (by norm_num) _)) (by linarith)
  calc |gueTail g x|
      ≤ C * 2 ^ (k + 1) * (2 + Ck) * ((1 + x ^ (2 * k)) *
          gaussianPDFReal 0 1 x) := hdecay
    _ ≤ C * 2 ^ (k + 1) * (2 + Ck) * (2 * (1 + |x|) ^ (2 * k) *
          gaussianPDFReal 0 1 x) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hpow hρ) hconst
    _ = C * 2 ^ (k + 1) * (2 + Ck) * 2 * (1 + |x|) ^ (2 * k) *
          gaussianPDFReal 0 1 x := by ring

/-- Left-tail polynomial decay for polynomially growing mean-zero `g`. -/
theorem exists_abs_gueTail_le_poly_mul_gaussianPDFReal_of_le_neg_one {g : ℝ → ℝ}
    (hg : Measurable g) (hgr : PolyGrowth g)
    (hzero : ∫ x, g x * gaussianPDFReal 0 1 x = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x : ℝ, x ≤ -1 →
      |gueTail g x| ≤ C * (1 + |x|) ^ N * gaussianPDFReal 0 1 x := by
  obtain ⟨C, hC0, N, hC⟩ :=
    exists_abs_gueTail_le_poly_mul_gaussianPDFReal_of_one_le
      (measurable_gaussReflect hg) (polyGrowth_gaussReflect hgr)
  refine ⟨C, hC0, N, fun x hx => ?_⟩
  have hxpos : 1 ≤ -x := by linarith
  have h := hC (-x) hxpos
  rw [gueTail_eq_neg_gueTail_gaussReflect hg hgr hzero x]
  simpa [abs_neg, gaussianPDFReal_neg] using h

/-- **Two-sided polynomial tail bound** for polynomially growing mean-zero `g`:
`|gueTail g x| ≤ M (1+|x|)^N ρ x` for every `x`.  Mean zero is essential for the left tail. -/
theorem exists_abs_gueTail_le_poly_mul_gaussianPDFReal {g : ℝ → ℝ}
    (hg : Measurable g) (hgr : PolyGrowth g)
    (hzero : ∫ x, g x * gaussianPDFReal 0 1 x = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∃ N : ℕ, ∀ x : ℝ,
      |gueTail g x| ≤ M * (1 + |x|) ^ N * gaussianPDFReal 0 1 x := by
  obtain ⟨Cr, hCr0, Nr, hCr⟩ :=
    exists_abs_gueTail_le_poly_mul_gaussianPDFReal_of_one_le hg hgr
  obtain ⟨Cl, hCl0, Nl, hCl⟩ :=
    exists_abs_gueTail_le_poly_mul_gaussianPDFReal_of_le_neg_one hg hgr hzero
  have hAbs : PolyGrowth (fun t : ℝ => |g t|) := by
    obtain ⟨C, hC0, k, hC⟩ := hgr
    exact ⟨C, hC0, k, fun x => by simpa using hC x⟩
  have hTotal : Integrable (fun t : ℝ => |g t| * gaussianPDFReal 0 1 t) :=
    integrable_mul_gaussianPDFReal_of_polyGrowth hAbs hg.norm.aestronglyMeasurable
  set total : ℝ := ∫ t, |g t| * gaussianPDFReal 0 1 t with htotal
  have htotal0 : 0 ≤ total := integral_nonneg (fun t =>
    mul_nonneg (abs_nonneg _) (gaussianPDFReal_nonneg 0 1 t))
  have hρ1pos : 0 < gaussianPDFReal 0 1 1 :=
    gaussianPDFReal_pos 0 1 1 (by norm_num : (1:ℝ≥0) ≠ 0)
  set M0 : ℝ := total / gaussianPDFReal 0 1 1 with hM0
  have hM00 : 0 ≤ M0 := div_nonneg htotal0 hρ1pos.le
  refine ⟨max (max Cr Cl) M0, ?_, max Nr Nl, fun x => ?_⟩
  · exact le_trans (le_trans hCr0 (le_max_left Cr Cl)) (le_max_left (max Cr Cl) M0)
  · have hN := max Nr Nl
    have hb : (1:ℝ) ≤ 1 + |x| := by linarith [abs_nonneg x]
    have hpowR : (1 + |x|) ^ Nr ≤ (1 + |x|) ^ max Nr Nl :=
      pow_le_pow_right₀ hb (le_max_left _ _)
    have hpowL : (1 + |x|) ^ Nl ≤ (1 + |x|) ^ max Nr Nl :=
      pow_le_pow_right₀ hb (le_max_right _ _)
    have hMr : Cr ≤ max (max Cr Cl) M0 := le_trans (le_max_left _ _) (le_max_left _ _)
    have hMl : Cl ≤ max (max Cr Cl) M0 := le_trans (le_max_right _ _) (le_max_left _ _)
    have hM0le : M0 ≤ max (max Cr Cl) M0 := le_max_right _ _
    have hρ : (0:ℝ) ≤ gaussianPDFReal 0 1 x := gaussianPDFReal_nonneg 0 1 x
    have hpow1 : (1:ℝ) ≤ (1 + |x|) ^ max Nr Nl := one_le_pow₀ hb
    by_cases hx1 : 1 ≤ x
    · have h := hCr x hx1
      have hstep : Cr * (1 + |x|) ^ Nr * gaussianPDFReal 0 1 x
          ≤ max (max Cr Cl) M0 * (1 + |x|) ^ max Nr Nl * gaussianPDFReal 0 1 x := by
        have h1 : Cr * (1 + |x|) ^ Nr ≤ max (max Cr Cl) M0 * (1 + |x|) ^ max Nr Nl :=
          mul_le_mul hMr hpowR (by positivity) (le_trans hCr0 hMr)
        exact mul_le_mul_of_nonneg_right h1 hρ
      exact h.trans hstep
    · by_cases hx2 : x ≤ -1
      · have h := hCl x hx2
        have hstep : Cl * (1 + |x|) ^ Nl * gaussianPDFReal 0 1 x
            ≤ max (max Cr Cl) M0 * (1 + |x|) ^ max Nr Nl * gaussianPDFReal 0 1 x := by
          have h1 : Cl * (1 + |x|) ^ Nl ≤ max (max Cr Cl) M0 * (1 + |x|) ^ max Nr Nl :=
            mul_le_mul hMl hpowL (by positivity) (le_trans hCl0 hMl)
          exact mul_le_mul_of_nonneg_right h1 hρ
        exact h.trans hstep
      · have hxlt : x < 1 := not_le.mp hx1
        have hxgt : -1 < x := not_le.mp hx2
        have habs : |x| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith
        have hmass := abs_gueTail_le hTotal x
        have hρle : gaussianPDFReal 0 1 1 ≤ gaussianPDFReal 0 1 x :=
          gaussianPDFReal_one_le_of_abs_le_one habs
        have hmiddle : |gueTail g x| ≤ M0 * gaussianPDFReal 0 1 x := by
          calc |gueTail g x| ≤ total := hmass
            _ = M0 * gaussianPDFReal 0 1 1 := by rw [hM0]; field_simp
            _ ≤ M0 * gaussianPDFReal 0 1 x := mul_le_mul_of_nonneg_left hρle hM00
        have hstep : M0 * gaussianPDFReal 0 1 x
            ≤ max (max Cr Cl) M0 * (1 + |x|) ^ max Nr Nl * gaussianPDFReal 0 1 x := by
          have h1 : M0 ≤ max (max Cr Cl) M0 * (1 + |x|) ^ max Nr Nl := by
            calc M0 = M0 * 1 := by ring
              _ ≤ max (max Cr Cl) M0 * (1 + |x|) ^ max Nr Nl :=
                  mul_le_mul hM0le hpow1 (by norm_num) (le_trans hM00 hM0le)
          exact mul_le_mul_of_nonneg_right h1 hρ
        exact hmiddle.trans hstep


/-- The mean of `f` against the standard Gaussian density is zero. -/
def GaussianMeanZero (f : ℝ → ℝ) : Prop :=
  ∫ x, f x * gaussianPDFReal 0 1 x = 0

theorem gaussianMeanZero_iff_integral_gaussianReal {f : ℝ → ℝ} :
    GaussianMeanZero f ↔ ∫ x, f x ∂(gaussianReal 0 1) = 0 := by
  unfold GaussianMeanZero
  rw [integral_gaussianReal_eq_integral_smul (μ := 0) (v := 1) (by norm_num)]
  simp only [smul_eq_mul]
  have hcomm : (fun x => gaussianPDFReal 0 1 x * f x)
      = fun x => f x * gaussianPDFReal 0 1 x := by
    funext x
    ring
  rw [hcomm]

/-- If `f` has a derivative `f'` everywhere then `f'` is Borel measurable. -/
theorem measurable_deriv_of_hasDerivAt {f f' : ℝ → ℝ}
    (hderiv : ∀ x, HasDerivAt f (f' x) x) : Measurable f' := by
  have h : f' = deriv f := funext fun x => (hderiv x).deriv.symm
  rw [h]
  exact measurable_deriv f

/-- **Gaussian Poincaré inequality for polynomially growing mean-zero functions.** -/
theorem gaussian_poincare_poly {f f' : ℝ → ℝ}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf : PolyGrowth f) (hf' : PolyGrowth f')
    (hmean : GaussianMeanZero f) :
    ∫ x, f x ^ 2 ∂(gaussianReal 0 1) ≤ ∫ x, (f' x) ^ 2 ∂(gaussianReal 0 1) := by
  have hfcont : Continuous f := by
    have hdiff : Differentiable ℝ f := fun x => (hderiv x).differentiableAt
    exact hdiff.continuous
  have hfm : Measurable f := hfcont.measurable
  have hf'meas : Measurable f' := measurable_deriv_of_hasDerivAt hderiv
  obtain ⟨M, hM0, N, hT⟩ := exists_abs_gueTail_le_poly_mul_gaussianPDFReal hfm hf hmean
  let h : ℝ → ℝ := fun x => -Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail f x
  let h' : ℝ → ℝ := fun x => f x + x * h x
  have hTm : AEStronglyMeasurable (fun x : ℝ => gueTail f x) (volume : Measure ℝ) :=
    aestronglyMeasurable_gueTail hfm
  have hhm : AEStronglyMeasurable
      (fun x : ℝ => -Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail f x)
      (volume : Measure ℝ) := by
    have hfac : AEStronglyMeasurable
        (fun x : ℝ => -Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2)) (volume : Measure ℝ) := by
      fun_prop
    have hmul := hfac.mul hTm
    refine hmul.congr ?_
    filter_upwards with x
    simp only [Pi.mul_apply]
  have hh_poly : PolyGrowth h := by
    refine ⟨M, hM0, N, fun x => ?_⟩
    have hρ : (0:ℝ) ≤ gaussianPDFReal 0 1 x := gaussianPDFReal_nonneg 0 1 x
    have hexp0 : (0:ℝ) ≤ Real.exp (x ^ 2 / 2) := (Real.exp_pos _).le
    have hsqrt0 : (0:ℝ) ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
    have hkey := sqrt_two_pi_mul_exp_mul_gaussianPDFReal x
    have hb := hT x
    calc |h x|
        = Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * |gueTail f x| := by
          simp only [h, abs_mul, abs_neg, abs_of_nonneg hsqrt0, abs_of_nonneg hexp0]
      _ ≤ Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
            (M * (1 + |x|) ^ N * gaussianPDFReal 0 1 x) := by
          exact mul_le_mul_of_nonneg_left hb (mul_nonneg hsqrt0 hexp0)
      _ = M * (1 + |x|) ^ N *
            (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gaussianPDFReal 0 1 x) := by ring
      _ = M * (1 + |x|) ^ N := by rw [hkey]; ring
  have h'_poly : PolyGrowth h' := by
    simpa [h'] using polyGrowth_add hf (polyGrowth_mul polyGrowth_id hh_poly)
  have h'hm : AEStronglyMeasurable (fun x : ℝ => f x + x * h x) (volume : Measure ℝ) := by
    have hmul := hfm.aestronglyMeasurable.add
      (measurable_id.aestronglyMeasurable.mul hhm)
    refine hmul.congr ?_
    filter_upwards with x
    simp only [Pi.add_apply, Pi.mul_apply, id, h]
  have hcont : ∀ x, ContinuousAt (fun t => f t * gaussianPDFReal 0 1 t) x := fun x =>
    hfcont.continuousAt.mul (hasDerivAt_gaussianPDFReal_one x).continuousAt
  have hintU : IntegrableOn (fun t => f t * gaussianPDFReal 0 1 t) Set.univ :=
    (integrable_mul_gaussianPDFReal_of_polyGrowth hf hfm.aestronglyMeasurable).integrableOn
  have hf'ρ : Integrable (fun x => f' x * gaussianPDFReal 0 1 x) :=
    integrable_mul_gaussianPDFReal_of_polyGrowth hf' hf'meas.aestronglyMeasurable
  have hIBPg : Integrable (fun x => gaussianPDFReal 0 1 x * f' x) :=
    hf'ρ.congr (ae_of_all _ fun x => by ring)
  have hxf : PolyGrowth (fun x => x * f x) := polyGrowth_mul polyGrowth_id hf
  have hxfg : Integrable (fun x => (x * f x) * gaussianPDFReal 0 1 x) :=
    integrable_mul_gaussianPDFReal_of_polyGrowth hxf
      (measurable_id.aestronglyMeasurable.mul hfm.aestronglyMeasurable)
  have hIBPxg : Integrable (fun x => x * (gaussianPDFReal 0 1 x * f x)) :=
    hxfg.congr (ae_of_all _ fun x => by ring)
  have hbotg : Tendsto (fun x => gaussianPDFReal 0 1 x * f x) atBot (𝓝 0) := by
    simpa [mul_comm] using tendsto_mul_gaussianPDFReal_of_polyGrowth_atBot hf
  have htopg : Tendsto (fun x => gaussianPDFReal 0 1 x * f x) atTop (𝓝 0) := by
    simpa [mul_comm] using tendsto_mul_gaussianPDFReal_of_polyGrowth hf
  -- the combined integrability condition for the Stein identity
  have t1 : PDFPolyGrowth (fun x => (f' x * h x) * gaussianPDFReal 0 1 x) :=
    pdfPolyGrowth_of_polyGrowth_mul_pdf (polyGrowth_mul hf' hh_poly)
      (hf'meas.aestronglyMeasurable.mul hhm)
  have t2 : PDFPolyGrowth (fun x => (f x * (f x + x * h x)) * gaussianPDFReal 0 1 x) :=
    pdfPolyGrowth_of_polyGrowth_mul_pdf (polyGrowth_mul hf h'_poly)
      (hfm.aestronglyMeasurable.mul h'hm)
  have hFPDF : PDFPolyGrowth
      (fun x => gaussianPDFReal 0 1 x * (f' x * h x + f x * (f x + x * h x))) := by
    have hsum := pdfPolyGrowth_add t1 t2
    have heq : (fun x => (f' x * h x) * gaussianPDFReal 0 1 x
          + (f x * (f x + x * h x)) * gaussianPDFReal 0 1 x)
        = fun x => gaussianPDFReal 0 1 x * (f' x * h x + f x * (f x + x * h x)) := by
      funext x
      ring
    rwa [heq] at hsum
  have hIBPgh : Integrable
      (fun x => gaussianPDFReal 0 1 x * (f' x * h x + f x * (f x + x * h x))) :=
    integrable_of_pdfPolyGrowth hFPDF
  have hxfh : PolyGrowth (fun x => x * (f x * h x)) :=
    polyGrowth_mul polyGrowth_id (polyGrowth_mul hf hh_poly)
  have hxgh_vol : Integrable (fun x => (x * (f x * h x)) * gaussianPDFReal 0 1 x) :=
    integrable_mul_gaussianPDFReal_of_polyGrowth hxfh
      (measurable_id.aestronglyMeasurable.mul
        (hfm.aestronglyMeasurable.mul hhm))
  have hIBPxgh : Integrable
      (fun x => x * (gaussianPDFReal 0 1 x * (f x * h x))) :=
    hxgh_vol.congr (ae_of_all _ fun x => by ring)
  have hfh_poly : PolyGrowth (fun x => f x * h x) := polyGrowth_mul hf hh_poly
  have hbotgh : Tendsto
      (fun x => gaussianPDFReal 0 1 x * (f x * h x)) atBot (𝓝 0) := by
    simpa [mul_comm] using tendsto_mul_gaussianPDFReal_of_polyGrowth_atBot hfh_poly
  have htopgh : Tendsto
      (fun x => gaussianPDFReal 0 1 x * (f x * h x)) atTop (𝓝 0) := by
    simpa [mul_comm] using tendsto_mul_gaussianPDFReal_of_polyGrowth hfh_poly
  have hgh' : Integrable (fun x => f x * (f x + x * h x)) (gaussianReal 0 1) :=
    integrable_gaussianReal_of_polyGrowth (polyGrowth_mul hf h'_poly)
      (hfm.aestronglyMeasurable.mul h'hm)
  have hgh : Integrable (fun x => f' x * h x) (gaussianReal 0 1) :=
    integrable_gaussianReal_of_polyGrowth (polyGrowth_mul hf' hh_poly)
      (hf'meas.aestronglyMeasurable.mul hhm)
  have hxgh : Integrable (fun x => x * (f x * h x)) (gaussianReal 0 1) :=
    integrable_gaussianReal_of_polyGrowth hxfh
      (measurable_id.aestronglyMeasurable.mul
        (hfm.aestronglyMeasurable.mul hhm))
  have hLp1 : MemLp f' 2 (gaussianReal 0 1) :=
    memLp_two_of_polyGrowth hf' hf'meas.aestronglyMeasurable
  have hLp2 : MemLp h 2 (gaussianReal 0 1) :=
    memLp_two_of_polyGrowth hh_poly hhm
  have hh2x_poly : PolyGrowth (fun x => (h x) ^ 2 * x) :=
    polyGrowth_mul (polyGrowth_pow hh_poly 2) polyGrowth_id
  have hbot_h : Tendsto (fun x => (h x) ^ 2 * (x * gaussianPDFReal 0 1 x)) atBot (𝓝 0) := by
    have := tendsto_mul_gaussianPDFReal_of_polyGrowth_atBot hh2x_poly
    simpa [mul_assoc, mul_comm, mul_left_comm] using this
  have htop_h : Tendsto (fun x => (h x) ^ 2 * (x * gaussianPDFReal 0 1 x)) atTop (𝓝 0) := by
    have := tendsto_mul_gaussianPDFReal_of_polyGrowth hh2x_poly
    simpa [mul_assoc, mul_comm, mul_left_comm] using this
  have hsq : Integrable
      (fun x => (f x + x * h x) ^ 2 * gaussianPDFReal 0 1 x) := by
    have hp : PolyGrowth (fun x => (h' x) ^ 2) := by
      simpa [h'] using polyGrowth_pow h'_poly 2
    simpa [h'] using integrable_of_pdfPolyGrowth
      (pdfPolyGrowth_of_polyGrowth_mul_pdf hp (h'hm.pow 2))
  have hh : Integrable
      (fun x => (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail f x) ^ 2 *
        gaussianPDFReal 0 1 x) := by
    simpa [h] using integrable_of_pdfPolyGrowth
      (pdfPolyGrowth_of_polyGrowth_mul_pdf (polyGrowth_pow hh_poly 2) (hhm.pow 2))
  have hx2 : Integrable
      (fun x => x ^ 2 * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
        gueTail f x) ^ 2 * gaussianPDFReal 0 1 x) := by
    have hp : PolyGrowth (fun x => x ^ 2 * (h x) ^ 2) :=
      polyGrowth_mul (polyGrowth_pow polyGrowth_id 2) (polyGrowth_pow hh_poly 2)
    simpa [h, mul_assoc] using integrable_of_pdfPolyGrowth
      (pdfPolyGrowth_of_polyGrowth_mul_pdf hp
        ((by fun_prop : AEStronglyMeasurable (fun x : ℝ => x ^ 2) volume).mul (hhm.pow 2)))
  have hcross : Integrable
      (fun x => x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail f x) *
        (f x + x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail f x)) *
        gaussianPDFReal 0 1 x) := by
    have hp : PolyGrowth (fun x => x * h x * h' x) :=
      polyGrowth_mul (polyGrowth_mul polyGrowth_id hh_poly) h'_poly
    simpa [h, h', mul_assoc] using integrable_of_pdfPolyGrowth
      (pdfPolyGrowth_of_polyGrowth_mul_pdf hp
        ((measurable_id.aestronglyMeasurable.mul hhm).mul h'hm))
  simpa [h, h'] using gaussian_poincare (f := f) (f' := f')
    hderiv hfm hcont hintU hIBPg hIBPxg hbotg htopg
    (by simpa [h] using hIBPgh) (by simpa [h] using hIBPxgh)
    (by simpa [h] using hbotgh) (by simpa [h] using htopgh)
    (by simpa [h, h'] using hgh') (by simpa [h] using hgh)
    (by simpa [h] using hxgh) hLp1 (by simpa [h] using hLp2)
    (by simpa [h] using hbot_h) (by simpa [h] using htop_h)
    (by simpa [h, h'] using hsq) (by simpa [h] using hh)
    (by simpa [h] using hx2) (by simpa [h, h'] using hcross)

/-- Total mass of the standard Gaussian density is one. -/
theorem integral_gaussianPDFReal_zero_one : ∫ x : ℝ, gaussianPDFReal 0 1 x = 1 := by
  have h := integral_gaussianReal_eq_integral_smul (μ := 0) (v := 1) (by norm_num)
    (f := fun _ : ℝ => (1:ℝ))
  simp only [smul_eq_mul, mul_one] at h
  rw [integral_const, MeasureTheory.probReal_univ] at h
  simpa using h.symm

/-- The Stein kernel of a polynomially growing mean-zero function has polynomial growth.  In
particular it is bounded by a polynomial (no exponential factor survives, because the Gaussian
density cancels `exp(x²/2)`). -/
theorem exists_abs_gaussianSteinKernel_le {g : ℝ → ℝ} (hg : Measurable g)
    (hgr : PolyGrowth g) (hzero : ∫ x, g x * gaussianPDFReal 0 1 x = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∃ N : ℕ, ∀ x : ℝ,
      |(-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x)|
        ≤ M * (1 + |x|) ^ N := by
  obtain ⟨M, hM0, N, hT⟩ := exists_abs_gueTail_le_poly_mul_gaussianPDFReal hg hgr hzero
  refine ⟨M, hM0, N, fun x => ?_⟩
  have hexp0 : (0:ℝ) ≤ Real.exp (x ^ 2 / 2) := (Real.exp_pos _).le
  have hsqrt0 : (0:ℝ) ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
  have hkey := sqrt_two_pi_mul_exp_mul_gaussianPDFReal x
  have hb := hT x
  calc |(-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x)|
      = Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * |gueTail g x| := by
        simp only [abs_mul, abs_neg, abs_of_nonneg hsqrt0, abs_of_nonneg hexp0]
    _ ≤ Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
          (M * (1 + |x|) ^ N * gaussianPDFReal 0 1 x) :=
        mul_le_mul_of_nonneg_left hb (mul_nonneg hsqrt0 hexp0)
    _ = M * (1 + |x|) ^ N *
          (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gaussianPDFReal 0 1 x) := by ring
    _ = M * (1 + |x|) ^ N := by rw [hkey]; ring

/-- The Stein kernel of a polynomially growing mean-zero function is square integrable for the
standard Gaussian measure (the `hLp2` hypothesis of `gaussian_poincare`). -/
theorem memLp_gaussianSteinKernel_of_polyGrowth {g : ℝ → ℝ} (hg : Measurable g)
    (hgr : PolyGrowth g) (hzero : ∫ x, g x * gaussianPDFReal 0 1 x = 0) :
    MemLp (fun x => -Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) 2
      (gaussianReal 0 1) := by
  obtain ⟨M, hM0, N, hM⟩ := exists_abs_gaussianSteinKernel_le hg hgr hzero
  have hpoly : PolyGrowth
      (fun x => -Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) :=
    ⟨M, hM0, N, hM⟩
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => -Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x)
      (volume : Measure ℝ) := by
    have hfac : AEStronglyMeasurable
        (fun x : ℝ => -Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2)) (volume : Measure ℝ) := by
      fun_prop
    have hmul := hfac.mul (aestronglyMeasurable_gueTail hg)
    refine hmul.congr ?_
    filter_upwards with x
    simp only [Pi.mul_apply]
  exact memLp_two_of_polyGrowth hpoly hmeas

/-- The constant function `1` is **not** mean zero, so it does not satisfy the hypothesis of
`gaussian_poincare_poly`: this is exactly the case in which the Stein kernel fails to decay on
the negative half-line. -/
theorem not_gaussianMeanZero_const_one : ¬ GaussianMeanZero (fun _ : ℝ => (1:ℝ)) := by
  unfold GaussianMeanZero
  have h : (fun x : ℝ => (fun _ : ℝ => (1:ℝ)) x * gaussianPDFReal 0 1 x)
      = fun x => gaussianPDFReal 0 1 x := by
    funext x
    simp
  rw [h, integral_gaussianPDFReal_zero_one]
  norm_num

/-- **Variance form of the Gaussian Poincaré inequality for polynomially growing functions.**
This is derived from the genuine mean-zero Poincaré inequality applied to `f - ∫ f`: no
centered Poincaré inequality is assumed. -/
theorem gaussian_poincare_variance_poly {f f' : ℝ → ℝ}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf : PolyGrowth f) (hf' : PolyGrowth f') :
    ∫ x, f x ^ 2 ∂(gaussianReal 0 1) - (∫ x, f x ∂(gaussianReal 0 1)) ^ 2
      ≤ ∫ x, (f' x) ^ 2 ∂(gaussianReal 0 1) := by
  set c : ℝ := ∫ x, f x ∂(gaussianReal 0 1) with hcdef
  have hfcont : Continuous f := by
    have hdiff : Differentiable ℝ f := fun x => (hderiv x).differentiableAt
    exact hdiff.continuous
  have hfm : Measurable f := hfcont.measurable
  have hf_int : Integrable f (gaussianReal 0 1) :=
    integrable_gaussianReal_of_polyGrowth hf hfm.aestronglyMeasurable
  have hf2_int : Integrable (fun x => f x ^ 2) (gaussianReal 0 1) :=
    integrable_gaussianReal_of_polyGrowth (polyGrowth_pow hf 2)
      (hfm.aestronglyMeasurable.pow 2)
  have hfρ_int : Integrable (fun x => f x * gaussianPDFReal 0 1 x) :=
    integrable_mul_gaussianPDFReal_of_polyGrowth hf hfm.aestronglyMeasurable
  have hc_eq : c = ∫ x, f x * gaussianPDFReal 0 1 x := by
    change ∫ x, f x ∂(gaussianReal 0 1) = ∫ x, f x * gaussianPDFReal 0 1 x
    have h := integral_gaussianReal_eq_integral_smul (μ := 0) (v := 1) (by norm_num)
      (f := f)
    simp only [smul_eq_mul] at h
    rw [h]
    congr 1
    funext x
    ring
  have hmean_g : GaussianMeanZero (fun x => f x - c) := by
    unfold GaussianMeanZero
    have hρ_int : Integrable (fun x : ℝ => gaussianPDFReal 0 1 x) := by
      simpa using integrable_gaussianPDFReal_mul_pow 0
    have hsplit : ∫ x, (f x - c) * gaussianPDFReal 0 1 x
        = (∫ x, f x * gaussianPDFReal 0 1 x)
          - c * ∫ x, gaussianPDFReal 0 1 x := by
      have h1 : ∫ x, (f x * gaussianPDFReal 0 1 x
            - c * gaussianPDFReal 0 1 x)
          = (∫ x, f x * gaussianPDFReal 0 1 x)
            - ∫ x, c * gaussianPDFReal 0 1 x :=
        integral_sub hfρ_int (hρ_int.const_mul c)
      have h2 : ∫ x, c * gaussianPDFReal 0 1 x
          = c * ∫ x, gaussianPDFReal 0 1 x :=
        integral_const_mul c (fun x => gaussianPDFReal 0 1 x)
      calc ∫ x, (f x - c) * gaussianPDFReal 0 1 x
          = ∫ x, (f x * gaussianPDFReal 0 1 x
              - c * gaussianPDFReal 0 1 x) := by
              refine integral_congr_ae (ae_of_all _ fun x => ?_)
              ring
        _ = (∫ x, f x * gaussianPDFReal 0 1 x)
              - ∫ x, c * gaussianPDFReal 0 1 x := h1
        _ = (∫ x, f x * gaussianPDFReal 0 1 x)
              - c * ∫ x, gaussianPDFReal 0 1 x := by rw [h2]
    rw [hsplit]
    have hcρ : c * ∫ x, gaussianPDFReal 0 1 x = c := by
      rw [integral_gaussianPDFReal_zero_one]
      ring
    rw [hcρ, hc_eq]
    exact sub_self _
  have hg_poly : PolyGrowth (fun x => f x - c) :=
    polyGrowth_sub hf (polyGrowth_const c)
  have hderiv_g : ∀ x, HasDerivAt (fun y => f y - c) (f' x) x := fun x =>
    (hderiv x).sub_const c
  have hpoin := gaussian_poincare_poly hderiv_g hg_poly hf' hmean_g
  have hkey : ∫ x, (f x - c) ^ 2 ∂(gaussianReal 0 1)
      = ∫ x, f x ^ 2 ∂(gaussianReal 0 1) - c ^ 2 := by
    have hc_int : Integrable (fun x => c * f x) (gaussianReal 0 1) := hf_int.const_mul c
    have hconst_int : Integrable (fun _ : ℝ => c ^ 2) (gaussianReal 0 1) := integrable_const _
    have hlin_int : Integrable (fun x => 2 * c * f x) (gaussianReal 0 1) :=
      hf_int.const_mul (2 * c)
    calc ∫ x, (f x - c) ^ 2 ∂(gaussianReal 0 1)
        = ∫ x, (f x ^ 2 - 2 * c * f x + c ^ 2) ∂(gaussianReal 0 1) := by
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          ring
      _ = ∫ x, ((f x ^ 2 - 2 * c * f x) + c ^ 2) ∂(gaussianReal 0 1) := rfl
      _ = (∫ x, (f x ^ 2 - 2 * c * f x) ∂(gaussianReal 0 1))
            + ∫ _x : ℝ, c ^ 2 ∂(gaussianReal 0 1) :=
          integral_add (hf2_int.sub hlin_int) hconst_int
      _ = ((∫ x, f x ^ 2 ∂(gaussianReal 0 1))
            - ∫ x, 2 * c * f x ∂(gaussianReal 0 1))
            + ∫ _x : ℝ, c ^ 2 ∂(gaussianReal 0 1) := by
          rw [integral_sub hf2_int hlin_int]
      _ = ((∫ x, f x ^ 2 ∂(gaussianReal 0 1)) - 2 * c * c)
            + c ^ 2 := by
          rw [integral_const_mul, integral_const, MeasureTheory.probReal_univ, one_smul,
            ← hcdef]
      _ = ∫ x, f x ^ 2 ∂(gaussianReal 0 1) - c ^ 2 := by ring
  rw [← hkey]
  exact hpoin
end

end GUEStrongConvergence
