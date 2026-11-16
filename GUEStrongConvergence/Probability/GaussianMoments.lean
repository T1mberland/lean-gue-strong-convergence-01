/-
# Gaussian moments, Mills bounds and the Gaussian Poincaré inequality

This module builds the analytic machinery for the Gaussian Poincaré inequality:

* decay and integrability of `x ↦ x^n * ρ x` (`ρ = gaussianPDFReal 0 1`);
* **Mills bounds** on both tails, including the general polynomial-tail family
  `∫ t in Ioi x, t^j ρ t ≤ C_j (1 + x^j) ρ x` (via the integration-by-parts identity
  `integral_Ioi_pow_mul_gaussianPDFReal`) and the branch-free majorant
  `(1+t)^k ≤ 2^(k+1)(1+t^(2k))`;
* tail **Cauchy–Schwarz** on both half-lines and the pointwise bounds
  `|g x · T x| ≤ √(g² x ρ x / x) √(∫ t in Ioi x, g² ρ)` for the tail `T = gueTail g`;
* the two **`x²`-weighted Tonelli chains** relating `∫⁻ ofReal(x²) · (tail mass)` to
  `∫⁻ ofReal((|t|+1)³) · g²ρ`;
* integrability of `h²ρ`, `x²h²ρ`, `h'²ρ` and `x h h'ρ` for the Stein kernel
  `h = -√(2π) e^{x²/2} T`, and the decay of `h²xρ` and `ρgh` at both infinities;
* the **Stein identity** `∫ g² dγ = -∫ g' h dγ`;
* the **contraction identity** `∫ g² dγ = ∫ h'² dγ + ∫ h² dγ`;
* and the **Gaussian Poincaré inequality**
  `gaussian_poincare : ∫ f² dγ ≤ ∫ (f')² dγ`.

The hypotheses of the final theorems are stated explicitly (integrability, decay and `L²`
conditions), all of which are available for `f` of polynomial growth from the lemmas above.
-/
import GUEStrongConvergence.Probability.GaussianIBP
open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace ENNReal NNReal Topology

namespace GUEStrongConvergence

noncomputable section

theorem sqDivTwoTendsto : Tendsto (fun s : ℝ => s ^ 2 / 2) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ tendsto_id
  filter_upwards [eventually_ge_atTop (2:ℝ)] with s hs
  have hs0 : (0:ℝ) ≤ s := by linarith
  have h2 : s * 2 ≤ s * s := mul_le_mul_of_nonneg_left hs hs0
  show s ≤ s ^ 2 / 2
  nlinarith [h2]

theorem expDecay : Tendsto (fun s : ℝ => Real.exp (-(s ^ 2 / 2))) atTop (𝓝 0) := by
  have h : Tendsto (fun s : ℝ => -(s ^ 2 / 2)) atTop atBot :=
    (tendsto_neg_atBot_iff (f := fun x : ℝ => x ^ 2 / 2) (l := atTop)).mpr sqDivTwoTendsto
  have := Real.tendsto_exp_atBot.comp h
  simpa [Function.comp_def] using this

/-- The Gaussian density integrates any polynomial power against Lebesgue measure. -/
theorem integrable_gaussianPDFReal_mul_pow (n : ℕ) :
    Integrable (fun x : ℝ => gaussianPDFReal 0 1 x * x ^ n) := by
  have hn : (-1 : ℝ) < (n : ℝ) := by
    have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith
  have hbase : Integrable (fun x : ℝ => x ^ (n : ℝ) * Real.exp (-(1/2 : ℝ) * x ^ 2)) :=
    integrable_rpow_mul_exp_neg_mul_sq (b := (1/2 : ℝ)) (s := (n : ℝ)) (by norm_num) hn
  have h1 : Integrable (fun x : ℝ => x ^ n * Real.exp (-(1/2 : ℝ) * x ^ 2)) := by
    refine hbase.congr (ae_of_all _ fun x => ?_)
    show x ^ (n : ℝ) * Real.exp (-(1/2 : ℝ) * x ^ 2)
      = x ^ n * Real.exp (-(1/2 : ℝ) * x ^ 2)
    rw [Real.rpow_natCast]
  refine h1.const_mul (√(2 * Real.pi * (1:ℝ≥0)))⁻¹ |>.congr (ae_of_all _ fun x => ?_)
  show (√(2 * Real.pi * (1:ℝ≥0)))⁻¹ * (x ^ n * Real.exp (-(1/2 : ℝ) * x ^ 2))
    = gaussianPDFReal 0 1 x * x ^ n
  rw [gaussianPDFReal,
    show (-(x - 0) ^ 2 / (2 * ((1:ℝ≥0):ℝ))) = (-(1/2 : ℝ) * x ^ 2) from by
      push_cast; ring]
  ring



theorem tendsto_pow_mul_exp_neg_half (n : ℕ) :
    Tendsto (fun x : ℝ => x ^ n * Real.exp (-(x / 2))) atTop (𝓝 0) := by
  have h2 : Tendsto (fun x : ℝ => x / 2) atTop atTop :=
    tendsto_id.atTop_div_const (by norm_num : (0:ℝ) < 2)
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp h2
  have h3 := h.const_mul ((2:ℝ)^n)
  simp only [mul_zero] at h3
  refine h3.congr' (Filter.Eventually.of_forall (fun x => ?_))
  show 2 ^ n * ((x / 2) ^ n * Real.exp (-(x / 2))) = x ^ n * Real.exp (-(x / 2))
  rw [← mul_assoc, ← mul_pow]
  congr 1
  ring

/-- The Gaussian density times any power decays at `+∞`. -/
theorem tendsto_gaussianPDFReal_mul_pow_atTop (n : ℕ) :
    Tendsto (fun x : ℝ => gaussianPDFReal 0 1 x * x ^ n) atTop (𝓝 0) := by
  have hc : Tendsto (fun x : ℝ => (√(2 * Real.pi * (1:ℝ≥0)))⁻¹ *
      (x ^ n * Real.exp (-(x / 2)))) atTop (𝓝 0) := by
    simpa using (tendsto_pow_mul_exp_neg_half n).const_mul ((√(2 * Real.pi * (1:ℝ≥0)))⁻¹)
  refine squeeze_zero_norm' ?_ hc
  filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
  have hx0 : (0:ℝ) ≤ x := by linarith
  have hρ : gaussianPDFReal 0 1 x = (√(2 * Real.pi * (1:ℝ≥0)))⁻¹ * Real.exp (-(x ^ 2 / 2)) := by
    rw [gaussianPDFReal, show (-(x - 0) ^ 2 / (2 * ((1:ℝ≥0):ℝ))) = (-(x ^ 2 / 2)) from by
      push_cast; ring]
  have hexp : Real.exp (-(x ^ 2 / 2)) ≤ Real.exp (-(x / 2)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hnn : (0:ℝ) ≤ Real.exp (-(x / 2)) := (Real.exp_pos _).le
  rw [hρ, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_assoc]
  have hxp : (0:ℝ) ≤ x ^ n := by positivity
  have : (√(2 * Real.pi * (1:ℝ≥0)))⁻¹ * (Real.exp (-(x ^ 2 / 2)) * x ^ n)
      ≤ (√(2 * Real.pi * (1:ℝ≥0)))⁻¹ * (Real.exp (-(x / 2)) * x ^ n) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_right hexp hxp
  calc (√(2 * Real.pi * (1:ℝ≥0)))⁻¹ * (Real.exp (-(x ^ 2 / 2)) * x ^ n)
      ≤ (√(2 * Real.pi * (1:ℝ≥0)))⁻¹ * (Real.exp (-(x / 2)) * x ^ n) := this
    _ = (√(2 * Real.pi * (1:ℝ≥0)))⁻¹ * (x ^ n * Real.exp (-(x / 2))) := by ring

/-- Derivative of `s ↦ -exp (-(s^2/2))`. -/
theorem hasDerivAt_neg_exp_neg_sq_div_two (t : ℝ) :
    HasDerivAt (fun s : ℝ => -Real.exp (-(s ^ 2 / 2)))
      (Real.exp (-(t ^ 2 / 2)) * t) t := by
  have h1 : HasDerivAt (fun s : ℝ => -(s ^ 2 / 2)) (-t) t := by
    have h := (hasDerivAt_pow 2 t).const_mul (-(1/2) : ℝ)
    convert h using 1
    · funext s
      ring
    · simp
  have h2 := h1.exp
  have h3 := h2.neg
  convert h3 using 1
  ring

theorem integrableOn_exp_neg_sq_div_two_mul (x : ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp (-(t ^ 2 / 2)) * t) (Set.Ioi x) := by
  have hbase : Integrable (fun t : ℝ => t * Real.exp (-(1/2 : ℝ) * t ^ 2)) :=
    integrable_mul_exp_neg_mul_sq (by norm_num)
  refine hbase.integrableOn.congr_fun (fun t _ => ?_) measurableSet_Ioi
  show t * Real.exp (-(1/2 : ℝ) * t ^ 2) = Real.exp (-(t ^ 2 / 2)) * t
  rw [show (-(1/2 : ℝ) * t ^ 2) = (-(t ^ 2 / 2)) from by ring, mul_comm]

theorem integrableOn_exp_neg_sq_div_two (x : ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp (-(t ^ 2 / 2))) (Set.Ioi x) := by
  have hbase : Integrable (fun t : ℝ => Real.exp (-(1/2 : ℝ) * t ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  refine hbase.integrableOn.congr_fun (fun t _ => ?_) measurableSet_Ioi
  show Real.exp (-(1/2 : ℝ) * t ^ 2) = Real.exp (-(t ^ 2 / 2))
  rw [show (-(1/2 : ℝ) * t ^ 2) = (-(t ^ 2 / 2)) from by ring]

/-- The improper integral of `t * exp (-(t^2/2))` on `(x, +∞)` equals `exp (-(x^2/2))`. -/
theorem integral_Ioi_exp_neg_sq_div_two_mul (x : ℝ) :
    ∫ t in Set.Ioi x, Real.exp (-(t ^ 2 / 2)) * t = Real.exp (-(x ^ 2 / 2)) := by
  have hF : Tendsto (fun s : ℝ => -Real.exp (-(s ^ 2 / 2))) atTop (𝓝 0) := by
    simpa using expDecay.neg
  have := integral_Ioi_of_hasDerivAt_of_tendsto' (a := x)
    (f := fun s : ℝ => -Real.exp (-(s ^ 2 / 2)))
    (f' := fun t => Real.exp (-(t ^ 2 / 2)) * t) (m := 0)
    (fun t _ => hasDerivAt_neg_exp_neg_sq_div_two t)
    (integrableOn_exp_neg_sq_div_two_mul x) hF
  simpa using this

/-- **Mills-ratio bound**: the Gaussian tail is at most `exp (-(x^2/2)) / x` for `x > 0`. -/
theorem integral_Ioi_exp_neg_sq_div_two_le {x : ℝ} (hx : 0 < x) :
    ∫ t in Set.Ioi x, Real.exp (-(t ^ 2 / 2)) ≤ Real.exp (-(x ^ 2 / 2)) / x := by
  have hInt : IntegrableOn (fun t : ℝ => Real.exp (-(t ^ 2 / 2))) (Set.Ioi x) :=
    integrableOn_exp_neg_sq_div_two x
  have hInt2 : IntegrableOn (fun t : ℝ => t / x * Real.exp (-(t ^ 2 / 2))) (Set.Ioi x) := by
    have h2 : IntegrableOn (fun t : ℝ => 1 / x * (Real.exp (-(t ^ 2 / 2)) * t)) (Set.Ioi x) :=
      (integrableOn_exp_neg_sq_div_two_mul x).const_mul (1 / x)
    refine h2.congr_fun (fun t _ => ?_) measurableSet_Ioi
    show 1 / x * (Real.exp (-(t ^ 2 / 2)) * t) = t / x * Real.exp (-(t ^ 2 / 2))
    ring
  calc ∫ t in Set.Ioi x, Real.exp (-(t ^ 2 / 2))
      ≤ ∫ t in Set.Ioi x, t / x * Real.exp (-(t ^ 2 / 2)) := by
        refine setIntegral_mono_on hInt hInt2 measurableSet_Ioi ?_
        intro t ht
        have ht' : x < t := ht
        have h1 : (1:ℝ) ≤ t / x := (le_div_iff₀ hx).mpr (by linarith)
        have h2 : (0:ℝ) ≤ Real.exp (-(t ^ 2 / 2)) := (Real.exp_pos _).le
        calc Real.exp (-(t ^ 2 / 2)) = 1 * Real.exp (-(t ^ 2 / 2)) := by ring
          _ ≤ t / x * Real.exp (-(t ^ 2 / 2)) := by
              exact mul_le_mul_of_nonneg_right h1 h2
    _ = Real.exp (-(x ^ 2 / 2)) / x := by
        rw [show (fun t : ℝ => t / x * Real.exp (-(t ^ 2 / 2)))
            = fun t => (1 / x) * (Real.exp (-(t ^ 2 / 2)) * t) from by
          funext t; ring]
        rw [integral_const_mul, integral_Ioi_exp_neg_sq_div_two_mul]
        ring

/-- **Mills-ratio bound for the standard Gaussian density**: for `x > 0`,
`∫ t in Ioi x, ρ t ≤ ρ x / x`. -/
theorem integral_Ioi_gaussianPDFReal_le {x : ℝ} (hx : 0 < x) :
    ∫ t in Set.Ioi x, gaussianPDFReal 0 1 t ≤ gaussianPDFReal 0 1 x / x := by
  have hc : ∀ t : ℝ, gaussianPDFReal 0 1 t
      = (√(2 * Real.pi * (1:ℝ≥0)))⁻¹ * Real.exp (-(t ^ 2 / 2)) := by
    intro t
    rw [gaussianPDFReal,
      show (-(t - 0) ^ 2 / (2 * ((1:ℝ≥0):ℝ))) = (-(t ^ 2 / 2)) from by push_cast; ring]
  simp only [hc]
  rw [integral_const_mul]
  have h := integral_Ioi_exp_neg_sq_div_two_le hx
  have hcpos : (0:ℝ) < (√(2 * Real.pi * (1:ℝ≥0)))⁻¹ := by
    have : (0:ℝ) < √(2 * Real.pi * (1:ℝ≥0)) := Real.sqrt_pos.mpr (by positivity)
    positivity
  calc (√(2 * Real.pi * (1:ℝ≥0)))⁻¹ * ∫ t in Set.Ioi x, Real.exp (-(t ^ 2 / 2))
      ≤ (√(2 * Real.pi * (1:ℝ≥0)))⁻¹ * (Real.exp (-(x ^ 2 / 2)) / x) :=
        mul_le_mul_of_nonneg_left h hcpos.le
    _ = (√(2 * Real.pi * (1:ℝ≥0)))⁻¹ * Real.exp (-(x ^ 2 / 2)) / x := by ring

lemma gaussianPDFReal_neg (x : ℝ) : gaussianPDFReal 0 1 (-x) = gaussianPDFReal 0 1 x := by
  simp only [gaussianPDFReal, sub_zero]
  norm_num

/-- The Gaussian density times any power decays at `-∞`. -/
theorem tendsto_gaussianPDFReal_mul_pow_atBot (n : ℕ) :
    Tendsto (fun x : ℝ => gaussianPDFReal 0 1 x * x ^ n) atBot (𝓝 0) := by
  have h := (tendsto_gaussianPDFReal_mul_pow_atTop n).comp
    (tendsto_neg_atBot_atTop (G := ℝ))
  have h' : Tendsto (fun x : ℝ => (-1 : ℝ) ^ n * (gaussianPDFReal 0 1 x * x ^ n))
      atBot (𝓝 0) := by
    refine h.congr' (Filter.Eventually.of_forall (fun x => ?_))
    show gaussianPDFReal 0 1 (-x) * (-x) ^ n
      = (-1 : ℝ) ^ n * (gaussianPDFReal 0 1 x * x ^ n)
    rw [gaussianPDFReal_neg, neg_pow]
    ring
  have hone : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  have h2 := h'.const_mul ((-1 : ℝ) ^ n)
  simp only [mul_zero] at h2
  refine h2.congr' (Filter.Eventually.of_forall (fun x => ?_))
  show (-1 : ℝ) ^ n * ((-1 : ℝ) ^ n * (gaussianPDFReal 0 1 x * x ^ n))
    = gaussianPDFReal 0 1 x * x ^ n
  rw [← mul_assoc, hone, one_mul]

/-- **Wick recursion for the standard normal**: `E[X^{n+2}] = (n+1) E[X^n]`, obtained by
applying the Gaussian integration by parts to `f = x^{n+1}` with the integrability and decay
lemmas of this file. -/
theorem integral_gaussianPDFReal_mul_pow_succ (n : ℕ) :
    ∫ x : ℝ, gaussianPDFReal 0 1 x * x ^ (n + 2)
      = (n + 1) * ∫ x : ℝ, gaussianPDFReal 0 1 x * x ^ n := by
  have hderiv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y ^ (n + 1)) ((n + 1 : ℝ) * x ^ n) x := by
    intro x
    have h := hasDerivAt_pow (n + 1) x
    convert h using 1
    push_cast
    ring
  have hff' : Integrable (fun x : ℝ => gaussianPDFReal 0 1 x • ((n + 1 : ℝ) * x ^ n)) := by
    refine (integrable_gaussianPDFReal_mul_pow n).const_mul ((n + 1 : ℝ)) |>.congr
      (ae_of_all _ fun x => ?_)
    show (n + 1 : ℝ) * (gaussianPDFReal 0 1 x * x ^ n)
      = gaussianPDFReal 0 1 x • ((n + 1 : ℝ) * x ^ n)
    rw [smul_eq_mul]
    ring
  have hxf : Integrable (fun x : ℝ => x • (gaussianPDFReal 0 1 x • x ^ (n + 1))) := by
    refine (integrable_gaussianPDFReal_mul_pow (n + 2)).congr (ae_of_all _ fun x => ?_)
    show gaussianPDFReal 0 1 x * x ^ (n + 2) = x • (gaussianPDFReal 0 1 x • x ^ (n + 1))
    rw [smul_smul]
    ring
  have hbot : Tendsto (fun x : ℝ => gaussianPDFReal 0 1 x • x ^ (n + 1)) atBot (𝓝 0) := by
    refine (tendsto_gaussianPDFReal_mul_pow_atBot (n + 1)).congr'
      (Filter.Eventually.of_forall (fun x => ?_))
    show gaussianPDFReal 0 1 x * x ^ (n + 1) = gaussianPDFReal 0 1 x • x ^ (n + 1)
    rw [smul_eq_mul]
  have htop : Tendsto (fun x : ℝ => gaussianPDFReal 0 1 x • x ^ (n + 1)) atTop (𝓝 0) := by
    refine (tendsto_gaussianPDFReal_mul_pow_atTop (n + 1)).congr'
      (Filter.Eventually.of_forall (fun x => ?_))
    show gaussianPDFReal 0 1 x * x ^ (n + 1) = gaussianPDFReal 0 1 x • x ^ (n + 1)
    rw [smul_eq_mul]
  have hIBP := gaussian_integration_by_parts_density (f := fun y : ℝ => y ^ (n + 1))
    (f' := fun x : ℝ => (n + 1 : ℝ) * x ^ n) hderiv hff' hxf hbot htop
  calc ∫ x : ℝ, gaussianPDFReal 0 1 x * x ^ (n + 2)
      = ∫ x : ℝ, x • (gaussianPDFReal 0 1 x • x ^ (n + 1)) := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        show gaussianPDFReal 0 1 x * x ^ (n + 2) = x • (gaussianPDFReal 0 1 x • x ^ (n + 1))
        rw [smul_smul]
        ring
    _ = ∫ x : ℝ, gaussianPDFReal 0 1 x • ((n + 1 : ℝ) * x ^ n) := hIBP
    _ = (n + 1) * ∫ x : ℝ, gaussianPDFReal 0 1 x * x ^ n := by
        rw [← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        show gaussianPDFReal 0 1 x • ((n + 1 : ℝ) * x ^ n)
          = (n + 1 : ℝ) * (gaussianPDFReal 0 1 x * x ^ n)
        rw [smul_eq_mul]
        ring

/-- Integration by parts identity for the Stein kernel: for `h` with `h^2 * (x * ρ) -> 0` at ±∞,

`∫ (h x)^2 * (x * ρ x - x^2 * ρ x) = -2 ∫ x * h x * h' x * ρ x`. -/
theorem integral_sq_mul_deriv_gaussianPDF (h h' : ℝ → ℝ)
    (hderiv : ∀ x, HasDerivAt h (h' x) x)
    (hInt : Integrable ((fun y : ℝ => h y ^ 2) *
      fun x : ℝ => gaussianPDFReal 0 1 x - x ^ 2 * gaussianPDFReal 0 1 x))
    (hInt2 : Integrable ((fun x : ℝ => 2 * (h x * h' x)) *
      fun x : ℝ => x * gaussianPDFReal 0 1 x))
    (hbot : Tendsto (fun x => h x ^ 2 * (x * gaussianPDFReal 0 1 x)) atBot (𝓝 0))
    (htop : Tendsto (fun x => h x ^ 2 * (x * gaussianPDFReal 0 1 x)) atTop (𝓝 0)) :
    ∫ x, h x ^ 2 * (gaussianPDFReal 0 1 x - x ^ 2 * gaussianPDFReal 0 1 x)
      = -2 * ∫ x, x * h x * h' x * gaussianPDFReal 0 1 x := by
  have hv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y * gaussianPDFReal 0 1 y)
      (gaussianPDFReal 0 1 x - x ^ 2 * gaussianPDFReal 0 1 x) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => y * gaussianPDFReal 0 1 y)
        (1 * gaussianPDFReal 0 1 x + x * (-x * gaussianPDFReal 0 1 x)) x :=
      (hasDerivAt_id x).mul (hasDerivAt_gaussianPDFReal_one x)
    convert h1 using 1
    ring
  have hu' : ∀ x : ℝ, HasDerivAt (fun y : ℝ => h y ^ 2) (2 * (h x * h' x)) x := by
    intro x
    have h2 : HasDerivAt (fun y : ℝ => h y * h y) (h' x * h x + h x * h' x) x :=
      (hderiv x).mul (hderiv x)
    have hfun : (fun y : ℝ => h y ^ 2) = fun y : ℝ => h y * h y := by
      funext y
      ring
    rw [hfun]
    convert h2 using 1
    ring
  have hu : ∀ x : ℝ, HasDerivAt (fun y : ℝ => h y ^ 2) (2 * (h x * h' x)) x := hu'
  have hIBP := integral_mul_deriv_eq_deriv_mul
    (u := fun y => h y ^ 2) (v := fun y => y * gaussianPDFReal 0 1 y)
    (u' := fun x => 2 * (h x * h' x))
    (v' := fun x => gaussianPDFReal 0 1 x - x ^ 2 * gaussianPDFReal 0 1 x)
    (fun x _ => hu x) (fun x _ => hv x) hInt hInt2 hbot htop
  rw [hIBP]
  have hzero : (0:ℝ) - 0 = 0 := by ring
  rw [hzero, zero_sub]
  rw [show (∫ x, 2 * (h x * h' x) * (x * gaussianPDFReal 0 1 x))
      = 2 * ∫ x, x * h x * h' x * gaussianPDFReal 0 1 x from by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    ring]
  ring_nf

/-- **Contraction step of the Gaussian Poincare inequality.** For a Stein kernel
`h' - x * h = g` (with the boundary and integrability hypotheses needed for the integration by
parts), `∫ g^2 ρ = ∫ h'^2 ρ + ∫ h^2 ρ`, hence `∫ h^2 ρ ≤ ∫ g^2 ρ`. -/
theorem integral_sq_eq_integral_deriv_sq_add {h h' g : ℝ → ℝ}
    (hderiv : ∀ x, HasDerivAt h (h' x) x)
    (hg : ∀ x, g x = h' x - x * h x)
    (hIBP1 : Integrable ((fun y : ℝ => h y ^ 2) *
      fun x : ℝ => gaussianPDFReal 0 1 x - x ^ 2 * gaussianPDFReal 0 1 x))
    (hIBP2 : Integrable ((fun x : ℝ => 2 * (h x * h' x)) *
      fun x : ℝ => x * gaussianPDFReal 0 1 x))
    (hIBPbot : Tendsto (fun x => h x ^ 2 * (x * gaussianPDFReal 0 1 x)) atBot (𝓝 0))
    (hIBPtop : Tendsto (fun x => h x ^ 2 * (x * gaussianPDFReal 0 1 x)) atTop (𝓝 0))
    (hsq : Integrable (fun x => (h' x) ^ 2 * gaussianPDFReal 0 1 x))
    (hh : Integrable (fun x => (h x) ^ 2 * gaussianPDFReal 0 1 x))
    (hx2 : Integrable (fun x => x ^ 2 * (h x) ^ 2 * gaussianPDFReal 0 1 x))
    (hcross : Integrable (fun x => x * h x * h' x * gaussianPDFReal 0 1 x)) :
    ∫ x, g x ^ 2 * gaussianPDFReal 0 1 x
      = (∫ x, (h' x) ^ 2 * gaussianPDFReal 0 1 x)
        + ∫ x, (h x) ^ 2 * gaussianPDFReal 0 1 x := by
  set A := ∫ x, (h' x) ^ 2 * gaussianPDFReal 0 1 x with hA
  set B := ∫ x, x * h x * h' x * gaussianPDFReal 0 1 x with hB
  set C := ∫ x, x ^ 2 * (h x) ^ 2 * gaussianPDFReal 0 1 x with hC
  set D := ∫ x, (h x) ^ 2 * gaussianPDFReal 0 1 x with hD
  have hBint : Integrable (fun x => 2 * (x * h x * h' x * gaussianPDFReal 0 1 x)) :=
    hcross.const_mul 2
  -- expansion of the left-hand side
  have e1 : ∫ x, g x ^ 2 * gaussianPDFReal 0 1 x = A - 2 * B + C := by
    calc ∫ x, g x ^ 2 * gaussianPDFReal 0 1 x
        = ∫ x, (((fun y : ℝ => (h' y) ^ 2 * gaussianPDFReal 0 1 y)
              - (fun y : ℝ => 2 * (y * h y * h' y * gaussianPDFReal 0 1 y)))
            + (fun y : ℝ => y ^ 2 * (h y) ^ 2 * gaussianPDFReal 0 1 y)) x := by
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          show g x ^ 2 * gaussianPDFReal 0 1 x
            = ((h' x) ^ 2 * gaussianPDFReal 0 1 x
                - 2 * (x * h x * h' x * gaussianPDFReal 0 1 x))
              + x ^ 2 * (h x) ^ 2 * gaussianPDFReal 0 1 x
          rw [hg x]
          ring
      _ = (∫ x, ((fun y : ℝ => (h' y) ^ 2 * gaussianPDFReal 0 1 y)
              - (fun y : ℝ => 2 * (y * h y * h' y * gaussianPDFReal 0 1 y))) x)
            + ∫ x, x ^ 2 * (h x) ^ 2 * gaussianPDFReal 0 1 x :=
          integral_add (hsq.sub hBint) hx2
      _ = ((∫ x, (h' x) ^ 2 * gaussianPDFReal 0 1 x)
              - ∫ x, 2 * (x * h x * h' x * gaussianPDFReal 0 1 x))
            + ∫ x, x ^ 2 * (h x) ^ 2 * gaussianPDFReal 0 1 x := by
          simp only [Pi.sub_apply]
          rw [integral_sub hsq hBint]
      _ = A - 2 * B + C := by
          rw [integral_const_mul, ← hA, ← hB, ← hC]
  -- the IBP identity gives  -2 B = D - C
  have hkey := integral_sq_mul_deriv_gaussianPDF h h' hderiv hIBP1 hIBP2 hIBPbot hIBPtop
  have hid : ∫ x, h x ^ 2 * (gaussianPDFReal 0 1 x - x ^ 2 * gaussianPDFReal 0 1 x) = D - C := by
    have hsub := integral_sub hh hx2
    rw [← hsub]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    ring
  have e2 : -2 * B = D - C := by
    rw [← hkey, hid]
  have e2' : 2 * B = C - D := by linarith
  calc ∫ x, g x ^ 2 * gaussianPDFReal 0 1 x
      = A - 2 * B + C := e1
    _ = A - (C - D) + C := by rw [e2']
    _ = A + D := by ring
    _ = (∫ x, (h' x) ^ 2 * gaussianPDFReal 0 1 x)
        + ∫ x, (h x) ^ 2 * gaussianPDFReal 0 1 x := by
        rw [hA, hD]

/-- **Stein step of the Gaussian Poincare inequality.** If `h` solves the Stein equation
`g = h' - x * h`, then `∫ g^2 dγ = -∫ g' * h dγ`. -/
theorem integral_sq_eq_neg_integral_deriv_mul {g g' h h' : ℝ → ℝ}
    (hderivg : ∀ x, HasDerivAt g (g' x) x)
    (hderivh : ∀ x, HasDerivAt h (h' x) x)
    (hIBPg : Integrable (fun x => gaussianPDFReal 0 1 x • g' x))
    (hIBPxg : Integrable (fun x => x • (gaussianPDFReal 0 1 x • g x)))
    (hbotg : Tendsto (fun x => gaussianPDFReal 0 1 x • g x) atBot (𝓝 0))
    (htopg : Tendsto (fun x => gaussianPDFReal 0 1 x • g x) atTop (𝓝 0))
    (hIBPgh : Integrable (fun x => gaussianPDFReal 0 1 x • (g' x * h x + g x * h' x)))
    (hIBPxgh : Integrable (fun x => x • (gaussianPDFReal 0 1 x • (g x * h x))))
    (hbotgh : Tendsto (fun x => gaussianPDFReal 0 1 x • (g x * h x)) atBot (𝓝 0))
    (htopgh : Tendsto (fun x => gaussianPDFReal 0 1 x • (g x * h x)) atTop (𝓝 0))
    (hg : ∀ x, g x = h' x - x * h x)
    (hgh' : Integrable (fun x => g x * h' x) (gaussianReal 0 1))
    (hgh : Integrable (fun x => g' x * h x) (gaussianReal 0 1))
    (hxgh : Integrable (fun x => x * (g x * h x)) (gaussianReal 0 1)) :
    ∫ x, g x ^ 2 ∂(gaussianReal 0 1) = -∫ x, g' x * h x ∂(gaussianReal 0 1) := by
  -- IBP applied to g
  have h1 : ∫ x, x • g x ∂(gaussianReal 0 1) = ∫ x, g' x ∂(gaussianReal 0 1) :=
    gaussian_integration_by_parts_algebra hderivg hIBPg hIBPxg hbotg htopg
  -- IBP applied to g * h
  have hderivgh : ∀ x, HasDerivAt (fun y => g y * h y) (g' x * h x + g x * h' x) x :=
    fun x => (hderivg x).mul (hderivh x)
  have h2 : ∫ x, x • (g x * h x) ∂(gaussianReal 0 1)
      = ∫ x, (g' x * h x + g x * h' x) ∂(gaussianReal 0 1) :=
    gaussian_integration_by_parts_algebra hderivgh hIBPgh hIBPxgh hbotgh htopgh
  -- pointwise identity
  have hpt : ∀ x, g x ^ 2 = g x * h' x - x • (g x * h x) := by
    intro x
    have hxg : g x = h' x - x * h x := hg x
    rw [hxg, smul_eq_mul]
    ring
  have hint1 : Integrable (fun x => g x * h' x) (gaussianReal 0 1) := hgh'
  have hint2 : Integrable (fun x => x • (g x * h x)) (gaussianReal 0 1) := by
    refine hxgh.congr (ae_of_all _ fun x => ?_)
    simp only [smul_eq_mul]
  calc ∫ x, g x ^ 2 ∂(gaussianReal 0 1)
      = ∫ x, (g x * h' x - x • (g x * h x)) ∂(gaussianReal 0 1) := by
        refine integral_congr_ae (ae_of_all _ fun x => hpt x)
    _ = (∫ x, g x * h' x ∂(gaussianReal 0 1))
        - ∫ x, x • (g x * h x) ∂(gaussianReal 0 1) := by
        refine integral_sub hint1 hint2
    _ = (∫ x, g x * h' x ∂(gaussianReal 0 1))
        - ∫ x, (g' x * h x + g x * h' x) ∂(gaussianReal 0 1) := by
        rw [h2]
    _ = (∫ x, g x * h' x ∂(gaussianReal 0 1))
        - ((∫ x, g' x * h x ∂(gaussianReal 0 1))
          + ∫ x, g x * h' x ∂(gaussianReal 0 1)) := by
        have hcomb : (∫ x, ((fun y : ℝ => g' y * h y) + (fun y : ℝ => g y * h' y)) x
              ∂(gaussianReal 0 1))
            = (∫ x, g' x * h x ∂(gaussianReal 0 1)) + ∫ x, g x * h' x ∂(gaussianReal 0 1) :=
          integral_add hgh hgh'
        have hs : (∫ x, (g' x * h x + g x * h' x) ∂(gaussianReal 0 1))
            = ∫ x, ((fun y : ℝ => g' y * h y) + (fun y : ℝ => g y * h' y)) x
              ∂(gaussianReal 0 1) := rfl
        rw [hs, hcomb]
    _ = -∫ x, g' x * h x ∂(gaussianReal 0 1) := by ring

/-- Derivative of the moving tail: for `x > 0`, `y ↦ ∫ t in Ioi y, f t` has derivative `-f x`. -/
theorem hasDerivAt_integral_Ioi {f : ℝ → ℝ} {x : ℝ} (hx : 0 < x)
    (hint : IntegrableOn f (Set.Ioi 0)) (hmeas : AEStronglyMeasurable f (volume : Measure ℝ))
    (hc : ContinuousAt f x) :
    HasDerivAt (fun y => ∫ t in Set.Ioi y, f t) (-(f x)) x := by
  have hI : HasDerivAt (fun y => ∫ t in (0:ℝ)..y, f t) (f x) x := by
    refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ hc
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_of_lt hx)).mpr
        (hint.mono_set Set.Ioc_subset_Ioi_self)
    · exact hmeas.stronglyMeasurableAtFilter
  have hC : HasDerivAt (fun _ : ℝ => ∫ t in Set.Ioi 0, f t) 0 x := hasDerivAt_const x _
  have hsplit : ∀ᶠ y in 𝓝 x, ∫ t in Set.Ioi y, f t
      = (∫ t in Set.Ioi 0, f t) - ∫ t in (0:ℝ)..y, f t := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    have hy0 : (0:ℝ) ≤ y := le_of_lt hy
    have hun : Set.Ioi (0:ℝ) = Set.Ioc 0 y ∪ Set.Ioi y := by
      ext t
      simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
      constructor
      · intro ht
        by_cases h : t ≤ y
        · exact Or.inl ⟨ht, h⟩
        · exact Or.inr (lt_of_not_ge h)
      · rintro (⟨ht, _⟩ | ht)
        · exact ht
        · linarith
    have hI1 : IntegrableOn f (Set.Ioc 0 y) := hint.mono_set Set.Ioc_subset_Ioi_self
    have hI2 : IntegrableOn f (Set.Ioi y) := hint.mono_set (Set.Ioi_subset_Ioi (le_of_lt hy))
    rw [hun, setIntegral_union (by rw [Set.disjoint_left]; intro t ht ht'; exact absurd ht.2 (not_le.mpr ht')) measurableSet_Ioi hI1 hI2,
      intervalIntegral.integral_of_le hy0]
    ring
  simpa using (hC.sub hI).congr_of_eventuallyEq hsplit

/-- Derivative of the moving lower tail: for `x < 0`, `y ↦ ∫ t in Iic y, f t` has derivative
`f x`. -/
theorem hasDerivAt_integral_Iic {f : ℝ → ℝ} {x : ℝ} (hx : x < 0)
    (hint : IntegrableOn f (Set.Iic 0)) (hmeas : AEStronglyMeasurable f (volume : Measure ℝ))
    (hc : ContinuousAt f x) :
    HasDerivAt (fun y => ∫ t in Set.Iic y, f t) (f x) x := by
  have hI : HasDerivAt (fun y => ∫ t in y..(0:ℝ), f t) (-(f x)) x := by
    refine intervalIntegral.integral_hasDerivAt_left ?_ ?_ hc
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_of_lt hx)).mpr
        (hint.mono_set (by
          intro t ht
          exact ht.2))
    · exact hmeas.stronglyMeasurableAtFilter
  have hC : HasDerivAt (fun _ : ℝ => ∫ t in Set.Iic 0, f t) 0 x := hasDerivAt_const x _
  have hsplit : ∀ᶠ y in 𝓝 x, ∫ t in Set.Iic y, f t
      = (∫ t in Set.Iic 0, f t) - ∫ t in y..(0:ℝ), f t := by
    filter_upwards [Iic_mem_nhds (a := (0:ℝ)) hx] with y hy
    have hy0 : y ≤ (0:ℝ) := hy
    have hun : Set.Iic (0:ℝ) = Set.Iic y ∪ Set.Ioc y 0 := by
      ext t
      simp only [Set.mem_Iic, Set.mem_union, Set.mem_Ioc]
      constructor
      · intro ht
        by_cases h : t ≤ y
        · exact Or.inl h
        · exact Or.inr ⟨lt_of_not_ge h, ht⟩
      · rintro (h | ⟨_, h⟩)
        · exact le_trans h hy0
        · exact h
    have hI1 : IntegrableOn f (Set.Iic y) := hint.mono_set (by
      intro t ht
      exact le_trans ht hy0)
    have hI2 : IntegrableOn f (Set.Ioc y 0) := hint.mono_set (by
      intro t ht
      exact Set.mem_Iic.mpr ht.2)
    rw [hun, setIntegral_union (by
        rw [Set.disjoint_left]
        intro t ht ht'
        exact absurd ht'.1 (not_lt.mpr ht)) measurableSet_Ioc hI1 hI2,
      intervalIntegral.integral_of_le hy0]
    ring
  simpa using (hC.sub hI).congr_of_eventuallyEq hsplit

/-- Derivative of `x ↦ exp (x^2/2)`. -/
lemma hasDerivAt_exp_sq_div_two (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (y ^ 2 / 2)) (x * Real.exp (x ^ 2 / 2)) x := by
  have h2 := ((hasDerivAt_pow 2 x).div_const 2).exp
  convert h2 using 1
  ring_nf

/-- The normalising identity `√(2π) * exp (x²/2) * ρ x = 1`. -/
lemma sqrt_two_pi_mul_exp_mul_gaussianPDFReal (x : ℝ) :
    Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gaussianPDFReal 0 1 x = 1 := by
  have hpos : (0:ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  rw [gaussianPDFReal]
  have h1 : ((2:ℝ) * Real.pi * ((1:ℝ≥0):ℝ)) = 2 * Real.pi := by push_cast; ring
  have h2 : (-(x - 0) ^ 2 / (2 * ((1:ℝ≥0):ℝ))) = (-(x ^ 2 / 2)) := by push_cast; ring
  rw [h1, h2]
  field_simp
  rw [← Real.exp_add]
  norm_num

/-- **Right branch of the Stein kernel solves the Stein equation**: for `x > 0`,
`h x = -√(2π) exp(x²/2) ∫ t in Ioi x, g t * ρ t` satisfies `h' x = x * h x + g x`. -/
theorem hasDerivAt_steinKernel_right {g : ℝ → ℝ} {x : ℝ} (hx : 0 < x)
    (hint : IntegrableOn (fun t => g t * gaussianPDFReal 0 1 t) (Set.Ioi 0))
    (hmeas : AEStronglyMeasurable (fun t => g t * gaussianPDFReal 0 1 t)
      (volume : Measure ℝ))
    (hc : ContinuousAt (fun t => g t * gaussianPDFReal 0 1 t) x) :
    HasDerivAt
      (fun y => -Real.sqrt (2 * Real.pi) * Real.exp (y ^ 2 / 2) *
        ∫ t in Set.Ioi y, g t * gaussianPDFReal 0 1 t)
      (g x + x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
        ∫ t in Set.Ioi x, g t * gaussianPDFReal 0 1 t)) x := by
  have hT := hasDerivAt_integral_Ioi hx hint hmeas hc
  have hE := hasDerivAt_exp_sq_div_two x
  have hprod := hE.mul hT
  have hfinal := hprod.const_mul (-Real.sqrt (2 * Real.pi))
  have hval : Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
      (g x * gaussianPDFReal 0 1 x) = g x := by
    rw [show Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
        (g x * gaussianPDFReal 0 1 x)
        = (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
          gaussianPDFReal 0 1 x) * g x by ring]
    rw [sqrt_two_pi_mul_exp_mul_gaussianPDFReal, one_mul]
  convert hfinal using 1
  · funext y
    simp only [Pi.mul_apply]
    ring
  · rw [show -Real.sqrt (2 * Real.pi) *
        ((x * Real.exp (x ^ 2 / 2) * ∫ t in Set.Ioi x, g t * gaussianPDFReal 0 1 t)
          + Real.exp (x ^ 2 / 2) * -(g x * gaussianPDFReal 0 1 x))
        = (-(Real.sqrt (2 * Real.pi) * x * Real.exp (x ^ 2 / 2)
              * ∫ t in Set.Ioi x, g t * gaussianPDFReal 0 1 t))
          + (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2)
              * (g x * gaussianPDFReal 0 1 x)) from by ring]
    rw [hval]
    ring

/-- **Left branch of the Stein kernel solves the Stein equation**: for `x < 0`,
`h x = √(2π) exp(x²/2) ∫ t in Iic x, g t * ρ t` satisfies `h' x = x * h x + g x`. -/
theorem hasDerivAt_steinKernel_left {g : ℝ → ℝ} {x : ℝ} (hx : x < 0)
    (hint : IntegrableOn (fun t => g t * gaussianPDFReal 0 1 t) (Set.Iic 0))
    (hmeas : AEStronglyMeasurable (fun t => g t * gaussianPDFReal 0 1 t)
      (volume : Measure ℝ))
    (hc : ContinuousAt (fun t => g t * gaussianPDFReal 0 1 t) x) :
    HasDerivAt
      (fun y => Real.sqrt (2 * Real.pi) * Real.exp (y ^ 2 / 2) *
        ∫ t in Set.Iic y, g t * gaussianPDFReal 0 1 t)
      (g x + x * (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
        ∫ t in Set.Iic x, g t * gaussianPDFReal 0 1 t)) x := by
  have hT := hasDerivAt_integral_Iic hx hint hmeas hc
  have hE := hasDerivAt_exp_sq_div_two x
  have hprod := hE.mul hT
  have hfinal := hprod.const_mul (Real.sqrt (2 * Real.pi))
  have hval : Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
      (g x * gaussianPDFReal 0 1 x) = g x := by
    rw [show Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
        (g x * gaussianPDFReal 0 1 x)
        = (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
          gaussianPDFReal 0 1 x) * g x by ring]
    rw [sqrt_two_pi_mul_exp_mul_gaussianPDFReal, one_mul]
  convert hfinal using 1
  · funext y
    simp only [Pi.mul_apply]
    ring
  · rw [show Real.sqrt (2 * Real.pi) *
        ((x * Real.exp (x ^ 2 / 2) * ∫ t in Set.Iic x, g t * gaussianPDFReal 0 1 t)
          + Real.exp (x ^ 2 / 2) * (g x * gaussianPDFReal 0 1 x))
        = (x * (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2)
              * ∫ t in Set.Iic x, g t * gaussianPDFReal 0 1 t))
          + (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2)
              * (g x * gaussianPDFReal 0 1 x)) from by ring]
    rw [hval]
    ring

/-- **Cauchy–Schwarz step of the Gaussian Poincare inequality**: `∫g² = -∫g'h`, `∫h² ≤ ∫g²`
and `g', h ∈ L²` imply `∫g² ≤ ∫g'²`. -/
theorem integral_sq_le_integral_deriv_sq {g g' h : ℝ → ℝ}
    (hstein : ∫ x, g x ^ 2 ∂(gaussianReal 0 1) = -∫ x, g' x * h x ∂(gaussianReal 0 1))
    (hcontr : ∫ x, (h x) ^ 2 ∂(gaussianReal 0 1) ≤ ∫ x, g x ^ 2 ∂(gaussianReal 0 1))
    (hg2 : 0 ≤ ∫ x, g x ^ 2 ∂(gaussianReal 0 1))
    (hLp1 : MemLp g' 2 (gaussianReal 0 1)) (hLp2 : MemLp h 2 (gaussianReal 0 1)) :
    ∫ x, g x ^ 2 ∂(gaussianReal 0 1) ≤ ∫ x, (g' x) ^ 2 ∂(gaussianReal 0 1) := by
  set S := ∫ x, g x ^ 2 ∂(gaussianReal 0 1) with hS
  set D := ∫ x, (g' x) ^ 2 ∂(gaussianReal 0 1) with hD
  have hD0 : 0 ≤ D := integral_nonneg (fun x => sq_nonneg _)
  have hMS : 0 ≤ S := hg2
  by_cases hS0 : S = 0
  · rw [hS0]; exact hD0
  have hSpos : 0 < S := lt_of_le_of_ne hMS (Ne.symm hS0)
  -- Cauchy–Schwarz
  have hholder : (2:ℝ).HolderConjugate 2 := ⟨by norm_num, by norm_num, by norm_num⟩
  have hLp1' : MemLp g' (ENNReal.ofReal 2) (gaussianReal 0 1) := by simpa using hLp1
  have hLp2' : MemLp h (ENNReal.ofReal 2) (gaussianReal 0 1) := by simpa using hLp2
  have hCS := integral_mul_norm_le_Lp_mul_Lq (p := (2:ℝ)) (q := (2:ℝ))
    (μ := gaussianReal 0 1) hholder hLp1' hLp2'
  have hnorm1 : (∫ x, ‖g' x‖ ^ (2:ℝ) ∂(gaussianReal 0 1)) = D := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show ‖g' x‖ ^ (2:ℝ) = (g' x) ^ 2
    rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  have hnorm2 : (∫ x, ‖h x‖ ^ (2:ℝ) ∂(gaussianReal 0 1))
      = ∫ x, (h x) ^ 2 ∂(gaussianReal 0 1) := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show ‖h x‖ ^ (2:ℝ) = (h x) ^ 2
    rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [hnorm1, hnorm2] at hCS
  -- monotonicity ∫ g' h ≤ ∫ ‖g'‖ ‖h‖
  have hInt1 : Integrable (fun x => g' x * h x) (gaussianReal 0 1) := by
    have := MemLp.mul (p := 2) (q := 2) (r := 1) hLp1 hLp2
    exact memLp_one_iff_integrable.mp this
  have hInt2 : Integrable (fun x => ‖g' x‖ * ‖h x‖) (gaussianReal 0 1) := by
    have h1 : MemLp (fun x => ‖g' x‖) 2 (gaussianReal 0 1) := hLp1.norm
    have h2 : MemLp (fun x => ‖h x‖) 2 (gaussianReal 0 1) := hLp2.norm
    have := MemLp.mul (p := 2) (q := 2) (r := 1) h1 h2
    exact memLp_one_iff_integrable.mp this
  have hneg : -∫ x, g' x * h x ∂(gaussianReal 0 1)
      ≤ ∫ x, ‖g' x‖ * ‖h x‖ ∂(gaussianReal 0 1) := by
    rw [← integral_neg]
    refine integral_mono hInt1.neg hInt2 (fun x => ?_)
    have : ‖g' x‖ * ‖h x‖ = |g' x * h x| := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    rw [this]
    exact neg_le_abs _
  -- chain
  have hchain : S ≤ Real.sqrt D * Real.sqrt S := by
    have h1 : ∫ x, g x ^ 2 ∂(gaussianReal 0 1)
        ≤ Real.sqrt D * Real.sqrt (∫ x, (h x) ^ 2 ∂(gaussianReal 0 1)) := by
      calc ∫ x, g x ^ 2 ∂(gaussianReal 0 1)
          = -∫ x, g' x * h x ∂(gaussianReal 0 1) := hstein
        _ ≤ ∫ x, ‖g' x‖ * ‖h x‖ ∂(gaussianReal 0 1) := hneg
        _ ≤ Real.sqrt D * Real.sqrt (∫ x, (h x) ^ 2 ∂(gaussianReal 0 1)) := by
            rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
            exact hCS
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg D))
    exact Real.sqrt_le_sqrt hcontr
  -- divide by √S
  have hsq : Real.sqrt S * Real.sqrt S ≤ Real.sqrt D * Real.sqrt S := by
    rw [Real.mul_self_sqrt hMS]
    exact hchain
  have hdiv : Real.sqrt S ≤ Real.sqrt D := le_of_mul_le_mul_right hsq (Real.sqrt_pos.mpr hSpos)
  calc S = Real.sqrt S * Real.sqrt S := (Real.mul_self_sqrt hMS).symm
    _ ≤ Real.sqrt D * Real.sqrt D :=
        mul_le_mul hdiv hdiv (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = D := Real.mul_self_sqrt hD0

/-- **Derivative of the moving tail at every point**: for `f` integrable on a left neighbourhood
of `x` and continuous at `x`, `y ↦ ∫ t in Ioi y, f t` has derivative `-f x` at `x`.

(The base point of the split is `x - 1`, so no case analysis at `0` is needed — this is what
makes the one-sided Stein kernel unnecessary.) -/
theorem hasDerivAt_integral_Ioi' {f : ℝ → ℝ} {x : ℝ}
    (hint : IntegrableOn f (Set.Ioi (x - 1)))
    (hmeas : AEStronglyMeasurable f (volume : Measure ℝ)) (hc : ContinuousAt f x) :
    HasDerivAt (fun y => ∫ t in Set.Ioi y, f t) (-(f x)) x := by
  have hbase : x - 1 < x := by linarith
  have hI : HasDerivAt (fun y => ∫ t in (x - 1)..y, f t) (f x) x := by
    refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ hc
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_of_lt hbase)).mpr
        (hint.mono_set Set.Ioc_subset_Ioi_self)
    · exact hmeas.stronglyMeasurableAtFilter
  have hC : HasDerivAt (fun _ : ℝ => ∫ t in Set.Ioi (x - 1), f t) 0 x := hasDerivAt_const x _
  have hsplit : ∀ᶠ y in 𝓝 x, ∫ t in Set.Ioi y, f t
      = (∫ t in Set.Ioi (x - 1), f t) - ∫ t in (x - 1)..y, f t := by
    filter_upwards [Ici_mem_nhds hbase] with y hy
    have hun : Set.Ioi (x - 1) = Set.Ioc (x - 1) y ∪ Set.Ioi y := by
      ext t
      simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
      constructor
      · intro ht
        by_cases h : t ≤ y
        · exact Or.inl ⟨ht, h⟩
        · exact Or.inr (lt_of_not_ge h)
      · rintro (⟨ht, _⟩ | ht)
        · exact ht
        · exact lt_of_le_of_lt hy ht
    have hI1 : IntegrableOn f (Set.Ioc (x - 1) y) := hint.mono_set Set.Ioc_subset_Ioi_self
    have hI2 : IntegrableOn f (Set.Ioi y) := hint.mono_set (Set.Ioi_subset_Ioi hy)
    rw [hun, setIntegral_union (by
        rw [Set.disjoint_left]
        intro t ht ht'
        exact absurd ht.2 (not_le.mpr ht')) measurableSet_Ioi hI1 hI2,
      intervalIntegral.integral_of_le hy]
    ring
  simpa using (hC.sub hI).congr_of_eventuallyEq hsplit

/-- **The Stein kernel solves the Stein equation at every point**: for `x : ℝ`,

`h x := -√(2π) exp(x²/2) ∫ t in Ioi x, g t * ρ t`  satisfies  `h' x = x * h x + g x`,

i.e. `h' - x h = g`. (No case split at `0` is needed: the same formula decays at both ends.) -/
theorem hasDerivAt_steinKernel {g : ℝ → ℝ} {x : ℝ}
    (hint : IntegrableOn (fun t => g t * gaussianPDFReal 0 1 t) (Set.Ioi (x - 1)))
    (hmeas : AEStronglyMeasurable (fun t => g t * gaussianPDFReal 0 1 t)
      (volume : Measure ℝ))
    (hc : ContinuousAt (fun t => g t * gaussianPDFReal 0 1 t) x) :
    HasDerivAt
      (fun y => -Real.sqrt (2 * Real.pi) * Real.exp (y ^ 2 / 2) *
        ∫ t in Set.Ioi y, g t * gaussianPDFReal 0 1 t)
      (g x + x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
        ∫ t in Set.Ioi x, g t * gaussianPDFReal 0 1 t)) x := by
  have hT := hasDerivAt_integral_Ioi' hint hmeas hc
  have hE := hasDerivAt_exp_sq_div_two x
  have hprod := hE.mul hT
  have hfinal := hprod.const_mul (-Real.sqrt (2 * Real.pi))
  have hval : Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
      (g x * gaussianPDFReal 0 1 x) = g x := by
    rw [show Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
        (g x * gaussianPDFReal 0 1 x)
        = (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
          gaussianPDFReal 0 1 x) * g x by ring]
    rw [sqrt_two_pi_mul_exp_mul_gaussianPDFReal, one_mul]
  convert hfinal using 1
  · funext y
    simp only [Pi.mul_apply]
    ring
  · rw [show -Real.sqrt (2 * Real.pi) *
        ((x * Real.exp (x ^ 2 / 2) * ∫ t in Set.Ioi x, g t * gaussianPDFReal 0 1 t)
          + Real.exp (x ^ 2 / 2) * -(g x * gaussianPDFReal 0 1 x))
        = (-(Real.sqrt (2 * Real.pi) * x * Real.exp (x ^ 2 / 2)
              * ∫ t in Set.Ioi x, g t * gaussianPDFReal 0 1 t))
          + (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2)
              * (g x * gaussianPDFReal 0 1 x)) from by ring]
    rw [hval]
    ring

/-- The density times the Stein kernel is minus the tail integral:
`ρ x * h x = -∫ t in Ioi x, g t * ρ t`. -/
theorem gaussianPDFReal_mul_steinKernel (g : ℝ → ℝ) (x : ℝ) :
    gaussianPDFReal 0 1 x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
      ∫ t in Set.Ioi x, g t * gaussianPDFReal 0 1 t)
      = -∫ t in Set.Ioi x, g t * gaussianPDFReal 0 1 t := by
  have hkey := sqrt_two_pi_mul_exp_mul_gaussianPDFReal x
  linear_combination (-(∫ t in Set.Ioi x, g t * gaussianPDFReal 0 1 t)) * hkey

/-- The moving tail tends to `0` at `+∞`. -/
theorem tendsto_integral_Ioi_id_zero (f : ℝ → ℝ) :
    Tendsto (fun x => ∫ t in Set.Ioi x, f t) atTop (𝓝 0) :=
  MeasureTheory.tendsto_integral_Ioi_zero (f := f) tendsto_id

/-- The moving tail tends to the total integral at `-∞`. -/
theorem tendsto_integral_Ioi_id_atBot {f : ℝ → ℝ} (hf : Integrable f) :
    Tendsto (fun x => ∫ t in Set.Ioi x, f t) atBot (𝓝 (∫ t, f t)) := by
  have h := MeasureTheory.tendsto_integral_Iic_zero (μ := volume) (f := f) (l := atBot)
    (a := fun x : ℝ => x) tendsto_id
  have hid : ∀ x, ∫ t in Set.Ioi x, f t = (∫ t, f t) - ∫ t in Set.Iic x, f t := by
    intro x
    have hdisj : Disjoint (Set.Iic x) (Set.Ioi x) := by
      rw [Set.disjoint_left]
      intro t ht ht'
      have h1 : t ≤ x := ht
      have h2 : x < t := ht'
      linarith
    have hu : Set.Iic x ∪ Set.Ioi x = (Set.univ : Set ℝ) := by
      ext t
      simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ioi, Set.mem_univ, iff_true]
      by_cases h : t ≤ x
      · exact Or.inl h
      · exact Or.inr (lt_of_not_ge h)
    have hsum := setIntegral_union hdisj measurableSet_Ioi hf.integrableOn hf.integrableOn
    rw [hu, setIntegral_univ] at hsum
    linarith [hsum]
  have h2 : Tendsto (fun x => (∫ t, f t) - ∫ t in Set.Iic x, f t) atBot (𝓝 ((∫ t, f t) - 0)) :=
    tendsto_const_nhds.sub h
  rw [sub_zero] at h2
  exact Tendsto.congr' (Filter.Eventually.of_forall (fun x => (hid x).symm)) h2

/-- On a probability space, `L²` functions are integrable. -/
theorem integrable_of_memLp_two {f : ℝ → ℝ} (hf : MemLp f 2 (gaussianReal 0 1)) :
    Integrable f (gaussianReal 0 1) := by
  have h1 : MemLp f 1 (gaussianReal 0 1) := hf.mono_exponent (p := 1) (by norm_num)
  exact memLp_one_iff_integrable.mp h1

/-- The product of two `L²` functions is integrable. -/
theorem integrable_mul_of_memLp_two {f g : ℝ → ℝ}
    (hf : MemLp f 2 (gaussianReal 0 1)) (hg : MemLp g 2 (gaussianReal 0 1)) :
    Integrable (fun x => f x * g x) (gaussianReal 0 1) :=
  memLp_one_iff_integrable.mp (MemLp.mul (p := 2) (q := 2) (r := 1) hf hg)

/-- `∫ t in Iic x, t * exp (-(t^2/2)) = -exp (-(x^2/2))`. -/
theorem integral_Iic_exp_neg_sq_div_two_mul (x : ℝ) :
    ∫ t in Set.Iic x, Real.exp (-(t ^ 2 / 2)) * t = -Real.exp (-(x ^ 2 / 2)) := by
  have hderiv : ∀ t ∈ Set.Iic x,
      HasDerivAt (fun s : ℝ => -Real.exp (-(s ^ 2 / 2)))
        (Real.exp (-(t ^ 2 / 2)) * t) t := fun t _ => hasDerivAt_neg_exp_neg_sq_div_two t
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-(t ^ 2 / 2)) * t) (Set.Iic x) := by
    have hbase : Integrable (fun t : ℝ => t * Real.exp (-(1/2 : ℝ) * t ^ 2)) :=
      integrable_mul_exp_neg_mul_sq (by norm_num)
    refine hbase.integrableOn.congr_fun (fun t _ => ?_) measurableSet_Iic
    show t * Real.exp (-(1/2 : ℝ) * t ^ 2) = Real.exp (-(t ^ 2 / 2)) * t
    rw [show (-(1/2 : ℝ) * t ^ 2) = (-(t ^ 2 / 2)) from by ring, mul_comm]
  have hlim : Tendsto (fun s : ℝ => -Real.exp (-(s ^ 2 / 2))) atBot (𝓝 0) := by
    have h2 : Tendsto (fun s : ℝ => -Real.exp (-((-s) ^ 2 / 2))) atBot (𝓝 0) := by
      simpa [Function.comp_def] using expDecay.neg.comp (tendsto_neg_atBot_atTop (G := ℝ))
    refine h2.congr' (Filter.Eventually.of_forall (fun s => ?_))
    show -Real.exp (-((-s) ^ 2 / 2)) = -Real.exp (-(s ^ 2 / 2))
    ring_nf
  have := integral_Iic_of_hasDerivAt_of_tendsto' (a := x)
    (f := fun s : ℝ => -Real.exp (-(s ^ 2 / 2)))
    (f' := fun t => Real.exp (-(t ^ 2 / 2)) * t) (m := 0) hderiv hint hlim
  simpa using this

/-- **Mills-ratio bound for the left tail**: for `x < 0`,
`∫ t in Iic x, exp (-(t^2/2)) ≤ exp (-(x^2/2)) / (-x)`. -/
theorem integral_Iic_exp_neg_sq_div_two_le {x : ℝ} (hx : x < 0) :
    ∫ t in Set.Iic x, Real.exp (-(t ^ 2 / 2)) ≤ Real.exp (-(x ^ 2 / 2)) / (-x) := by
  have hInt : IntegrableOn (fun t : ℝ => Real.exp (-(t ^ 2 / 2))) (Set.Iic x) := by
    have hbase : Integrable (fun t : ℝ => Real.exp (-(1/2 : ℝ) * t ^ 2)) :=
      integrable_exp_neg_mul_sq (by norm_num)
    refine hbase.integrableOn.congr_fun (fun t _ => ?_) measurableSet_Iic
    show Real.exp (-(1/2 : ℝ) * t ^ 2) = Real.exp (-(t ^ 2 / 2))
    rw [show (-(1/2 : ℝ) * t ^ 2) = (-(t ^ 2 / 2)) from by ring]
  have hInt2 : IntegrableOn (fun t : ℝ => t / x * Real.exp (-(t ^ 2 / 2))) (Set.Iic x) := by
    have h2 : IntegrableOn (fun t : ℝ => 1 / x * (Real.exp (-(t ^ 2 / 2)) * t)) (Set.Iic x) := by
      have hbase : Integrable (fun t : ℝ => t * Real.exp (-(1/2 : ℝ) * t ^ 2)) :=
        integrable_mul_exp_neg_mul_sq (by norm_num)
      refine ((hbase.const_mul (1 / x)).integrableOn).congr_fun (fun t _ => ?_) measurableSet_Iic
      show 1 / x * (t * Real.exp (-(1/2 : ℝ) * t ^ 2))
        = 1 / x * (Real.exp (-(t ^ 2 / 2)) * t)
      rw [show (-(1/2 : ℝ) * t ^ 2) = (-(t ^ 2 / 2)) from by ring]
      ring
    refine h2.congr_fun (fun t _ => ?_) measurableSet_Iic
    show 1 / x * (Real.exp (-(t ^ 2 / 2)) * t) = t / x * Real.exp (-(t ^ 2 / 2))
    ring
  calc ∫ t in Set.Iic x, Real.exp (-(t ^ 2 / 2))
      ≤ ∫ t in Set.Iic x, t / x * Real.exp (-(t ^ 2 / 2)) := by
        refine setIntegral_mono_on hInt hInt2 measurableSet_Iic ?_
        intro t ht
        have ht' : t ≤ x := ht
        have h1 : (1:ℝ) ≤ t / x := by
          rw [le_div_iff_of_neg hx]
          linarith
        have h2 : (0:ℝ) ≤ Real.exp (-(t ^ 2 / 2)) := (Real.exp_pos _).le
        calc Real.exp (-(t ^ 2 / 2)) = 1 * Real.exp (-(t ^ 2 / 2)) := by ring
          _ ≤ t / x * Real.exp (-(t ^ 2 / 2)) := mul_le_mul_of_nonneg_right h1 h2
    _ = Real.exp (-(x ^ 2 / 2)) / (-x) := by
        rw [show (fun t : ℝ => t / x * Real.exp (-(t ^ 2 / 2)))
            = fun t => (1 / x) * (Real.exp (-(t ^ 2 / 2)) * t) from by
          funext t; ring]
        rw [integral_const_mul, integral_Iic_exp_neg_sq_div_two_mul]
        field_simp

/-- **Cauchy–Schwarz for a finite measure**: `(∫ g)² ≤ (∫ 1) * ∫ g²`. -/
theorem sq_integral_le_integral_one_mul (ν : Measure ℝ) [IsFiniteMeasure ν] {g : ℝ → ℝ}
    (hg : MemLp g 2 ν) :
    (∫ t, g t ∂ν) ^ 2 ≤ (∫ _t, (1:ℝ) ∂ν) * ∫ t, (g t) ^ 2 ∂ν := by
  have hholder : (2:ℝ).HolderConjugate 2 := ⟨by norm_num, by norm_num, by norm_num⟩
  have h1 : MemLp g (ENNReal.ofReal 2) ν := by simpa using hg
  have h2 : MemLp (fun _ : ℝ => (1:ℝ)) (ENNReal.ofReal 2) ν := by
    simpa using memLp_const (μ := ν) (1:ℝ)
  have hCS := integral_mul_norm_le_Lp_mul_Lq (p := (2:ℝ)) (q := (2:ℝ)) (μ := ν) hholder h1 h2
  have e1 : (∫ t, ‖g t‖ * ‖(1:ℝ)‖ ∂ν) = ∫ t, |g t| ∂ν := by
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp [Real.norm_eq_abs]
  have e2 : (∫ t, ‖g t‖ ^ (2:ℝ) ∂ν) = ∫ t, (g t) ^ 2 ∂ν := by
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    show ‖g t‖ ^ (2:ℝ) = (g t) ^ 2
    rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  have e3 : (∫ t, ‖(1:ℝ)‖ ^ (2:ℝ) ∂ν) = ∫ _t, (1:ℝ) ∂ν := by
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    norm_num
  rw [e1, e2, e3] at hCS
  have hB : (0:ℝ) ≤ ∫ t, (g t) ^ 2 ∂ν := integral_nonneg (fun t => sq_nonneg _)
  have hC : (0:ℝ) ≤ ∫ _t, (1:ℝ) ∂ν := integral_nonneg (fun t => zero_le_one)
  have h1' : |∫ t, g t ∂ν|
      ≤ Real.sqrt (∫ t, (g t) ^ 2 ∂ν) * Real.sqrt (∫ _t, (1:ℝ) ∂ν) := by
    refine le_trans (abs_integral_le_integral_abs) ?_
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    exact hCS
  have h3 := sq_le_sq' (abs_le.mp h1').1 (abs_le.mp h1').2
  rw [mul_pow, Real.sq_sqrt hB, Real.sq_sqrt hC, mul_comm] at h3
  exact h3

/-- Densities on a measurable set: `∫ t in s, f t ∂γ = ∫ t in s, ρ t * f t`. -/
theorem setIntegral_gaussianReal_eq_setIntegral_mul {f : ℝ → ℝ} {s : Set ℝ}
    (hs : MeasurableSet s) :
    ∫ t in s, f t ∂(gaussianReal 0 1) = ∫ t in s, gaussianPDFReal 0 1 t * f t := by
  have hv : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  have h1 : gaussianReal 0 1 = volume.withDensity (gaussianPDF 0 1) :=
    gaussianReal_of_var_ne_zero 0 hv
  rw [h1, restrict_withDensity hs (gaussianPDF 0 1),
    integral_withDensity_eq_integral_toReal_smul (measurable_gaussianPDF (μ := 0) (v := 1))
      (by filter_upwards with t using gaussianPDF_lt_top (μ := 0) (v := 1) (x := t))]
  refine setIntegral_congr_fun hs (fun t _ => ?_)
  rw [toReal_gaussianPDF, smul_eq_mul]

/-- **Weighted Cauchy–Schwarz for the Gaussian tail**:
`(∫ t in Ioi x, g t * ρ t)² ≤ (∫ t in Ioi x, ρ t) * ∫ t in Ioi x, (g t)² * ρ t`. -/
theorem sq_integral_Ioi_mul_gaussianPDFReal_le {g : ℝ → ℝ} {x : ℝ}
    (hg : MemLp g 2 (gaussianReal 0 1)) :
    (∫ t in Set.Ioi x, g t * gaussianPDFReal 0 1 t) ^ 2
      ≤ (∫ t in Set.Ioi x, gaussianPDFReal 0 1 t)
        * ∫ t in Set.Ioi x, (g t) ^ 2 * gaussianPDFReal 0 1 t := by
  have hgν : MemLp g 2 ((gaussianReal 0 1).restrict (Set.Ioi x)) := hg.restrict _
  have hCS := sq_integral_le_integral_one_mul ((gaussianReal 0 1).restrict (Set.Ioi x)) hgν
  have e1 : (∫ t, g t ∂((gaussianReal 0 1).restrict (Set.Ioi x)))
      = ∫ t in Set.Ioi x, g t * gaussianPDFReal 0 1 t := by
    rw [setIntegral_gaussianReal_eq_setIntegral_mul measurableSet_Ioi]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    ring
  have e2 : (∫ _t, (1:ℝ) ∂((gaussianReal 0 1).restrict (Set.Ioi x)))
      = ∫ t in Set.Ioi x, gaussianPDFReal 0 1 t := by
    rw [setIntegral_gaussianReal_eq_setIntegral_mul measurableSet_Ioi]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    ring
  have e3 : (∫ t, (g t) ^ 2 ∂((gaussianReal 0 1).restrict (Set.Ioi x)))
      = ∫ t in Set.Ioi x, (g t) ^ 2 * gaussianPDFReal 0 1 t := by
    rw [setIntegral_gaussianReal_eq_setIntegral_mul measurableSet_Ioi]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    ring
  rw [e1, e2, e3] at hCS
  exact hCS

/-- **Weighted Cauchy–Schwarz on an arbitrary measurable set**:
`(∫ t in s, g t * ρ t)² ≤ (∫ t in s, ρ t) * ∫ t in s, (g t)² * ρ t`. -/
theorem sq_setIntegral_mul_gaussianPDFReal_le {g : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (hg : MemLp g 2 (gaussianReal 0 1)) :
    (∫ t in s, g t * gaussianPDFReal 0 1 t) ^ 2
      ≤ (∫ t in s, gaussianPDFReal 0 1 t) * ∫ t in s, (g t) ^ 2 * gaussianPDFReal 0 1 t := by
  have hgν : MemLp g 2 ((gaussianReal 0 1).restrict s) := hg.restrict _
  have hCS := sq_integral_le_integral_one_mul ((gaussianReal 0 1).restrict s) hgν
  have e1 : (∫ t, g t ∂((gaussianReal 0 1).restrict s))
      = ∫ t in s, g t * gaussianPDFReal 0 1 t := by
    rw [setIntegral_gaussianReal_eq_setIntegral_mul hs]
    refine setIntegral_congr_fun hs (fun t _ => ?_)
    ring
  have e2 : (∫ _t, (1:ℝ) ∂((gaussianReal 0 1).restrict s))
      = ∫ t in s, gaussianPDFReal 0 1 t := by
    rw [setIntegral_gaussianReal_eq_setIntegral_mul hs]
    refine setIntegral_congr_fun hs (fun t _ => ?_)
    ring
  have e3 : (∫ t, (g t) ^ 2 ∂((gaussianReal 0 1).restrict s))
      = ∫ t in s, (g t) ^ 2 * gaussianPDFReal 0 1 t := by
    rw [setIntegral_gaussianReal_eq_setIntegral_mul hs]
    refine setIntegral_congr_fun hs (fun t _ => ?_)
    ring
  rw [e1, e2, e3] at hCS
  exact hCS

/-- For a centred `g`, the upper tail of `g ρ` is minus the lower tail. -/
theorem integral_Ioi_mul_eq_neg_integral_Iic_mul {g : ℝ → ℝ} {x : ℝ}
    (hint : IntegrableOn (fun t => g t * gaussianPDFReal 0 1 t) (Set.univ))
    (hzero : ∫ t, g t * gaussianPDFReal 0 1 t = 0) :
    ∫ t in Set.Ioi x, g t * gaussianPDFReal 0 1 t
      = -∫ t in Set.Iic x, g t * gaussianPDFReal 0 1 t := by
  have hdisj : Disjoint (Set.Iic x) (Set.Ioi x) := by
    rw [Set.disjoint_left]
    intro t ht ht'
    have h1 : t ≤ x := ht
    have h2 : x < t := ht'
    linarith
  have hu : Set.Iic x ∪ Set.Ioi x = (Set.univ : Set ℝ) := by
    ext t
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ioi, Set.mem_univ, iff_true]
    by_cases h : t ≤ x
    · exact Or.inl h
    · exact Or.inr (lt_of_not_ge h)
  have hsum := setIntegral_union hdisj measurableSet_Ioi (hint.mono_set (Set.subset_univ _))
    (hint.mono_set (Set.subset_univ _))
  rw [hu, setIntegral_univ, hzero] at hsum
  linarith

/-- **Left-tail version** of the weighted Cauchy–Schwarz, for centred `g`. -/
theorem sq_integral_Ioi_mul_gaussianPDFReal_le_left {g : ℝ → ℝ} {x : ℝ}
    (hg : MemLp g 2 (gaussianReal 0 1))
    (hint : IntegrableOn (fun t => g t * gaussianPDFReal 0 1 t) (Set.univ))
    (hzero : ∫ t, g t * gaussianPDFReal 0 1 t = 0) :
    (∫ t in Set.Ioi x, g t * gaussianPDFReal 0 1 t) ^ 2
      ≤ (∫ t in Set.Iic x, gaussianPDFReal 0 1 t)
        * ∫ t in Set.Iic x, (g t) ^ 2 * gaussianPDFReal 0 1 t := by
  have hid := integral_Ioi_mul_eq_neg_integral_Iic_mul (x := x) hint hzero
  have hCS := sq_setIntegral_mul_gaussianPDFReal_le (s := Set.Iic x) measurableSet_Iic hg
  rw [hid]
  have : (-∫ t in Set.Iic x, g t * gaussianPDFReal 0 1 t) ^ 2
      = (∫ t in Set.Iic x, g t * gaussianPDFReal 0 1 t) ^ 2 := by ring
  rw [this]
  exact hCS

/-- **Weight estimate for the right tail**: for `x > 0`,
`√(2π) exp (x²/2) * ∫ t in Ioi x, ρ t ≤ 1/x`. -/
theorem weight_tail_Ioi_le {x : ℝ} (hx : 0 < x) :
    Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * (∫ t in Set.Ioi x, gaussianPDFReal 0 1 t)
      ≤ 1 / x := by
  have hmills := integral_Ioi_gaussianPDFReal_le hx
  have hpos : (0:ℝ) < Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) := by
    have h1 : (0:ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    positivity
  calc Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
        (∫ t in Set.Ioi x, gaussianPDFReal 0 1 t)
      ≤ Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
          (gaussianPDFReal 0 1 x / x) := mul_le_mul_of_nonneg_left hmills hpos.le
    _ = (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gaussianPDFReal 0 1 x) / x := by ring
    _ = 1 / x := by rw [sqrt_two_pi_mul_exp_mul_gaussianPDFReal]

/-- **Uniform bound near zero**: for `0 < x ≤ 1`,
`√(2π) exp (x²/2) * ∫ t in Ioi x, ρ t ≤ √(2π) * exp (1/2)`. -/
theorem weight_tail_Ioi_le_const {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * (∫ t in Set.Ioi x, gaussianPDFReal 0 1 t)
      ≤ Real.sqrt (2 * Real.pi) * Real.exp (1 / 2) := by
  have hmass : (∫ t in Set.Ioi x, gaussianPDFReal 0 1 t) ≤ 1 := by
    have h1 : (∫ t in Set.Ioi x, gaussianPDFReal 0 1 t) ≤ ∫ t, gaussianPDFReal 0 1 t := by
      refine setIntegral_le_integral ?_ ?_
      · exact (integrable_gaussianPDFReal_mul_pow 0).congr (ae_of_all _ fun t => by ring)
      · exact ae_of_all _ (fun t => gaussianPDFReal_nonneg 0 1 t)
    have h2 : (∫ t, gaussianPDFReal 0 1 t) = 1 := by
      have := integral_gaussianReal_eq_integral_smul (μ := 0) (v := 1)
        (f := fun t : ℝ => (1:ℝ)) (by norm_num : (1:ℝ≥0) ≠ 0)
      simpa using this.symm
    linarith [h1, h2]
  have hexp : Real.exp (x ^ 2 / 2) ≤ Real.exp (1 / 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hpos : (0:ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hmass0 : (0:ℝ) ≤ ∫ t in Set.Ioi x, gaussianPDFReal 0 1 t :=
    setIntegral_nonneg measurableSet_Ioi (fun t _ => gaussianPDFReal_nonneg 0 1 t)
  calc Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
        (∫ t in Set.Ioi x, gaussianPDFReal 0 1 t)
      ≤ Real.sqrt (2 * Real.pi) * Real.exp (1 / 2) * 1 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hexp hpos.le) hmass hmass0
        exact mul_nonneg hpos.le (Real.exp_pos _).le
    _ = Real.sqrt (2 * Real.pi) * Real.exp (1 / 2) := by ring

/-- **Weight estimate for the left tail**: for `x < 0`,
`√(2π) exp (x²/2) * ∫ t in Iic x, ρ t ≤ 1/(-x)`. -/
theorem weight_tail_Iic_le {x : ℝ} (hx : x < 0) :
    Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * (∫ t in Set.Iic x, gaussianPDFReal 0 1 t)
      ≤ 1 / (-x) := by
  have hmills := integral_Iic_exp_neg_sq_div_two_le hx
  -- ∫ ρ = (√(2π))⁻¹ ∫ exp (-(t²/2)) on the tail
  have hρexp : (∫ t in Set.Iic x, gaussianPDFReal 0 1 t)
      = (Real.sqrt (2 * Real.pi))⁻¹ * ∫ t in Set.Iic x, Real.exp (-(t ^ 2 / 2)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Iic (fun t _ => ?_)
    rw [gaussianPDFReal,
      show (2 * Real.pi * ((1:ℝ≥0):ℝ)) = 2 * Real.pi from by push_cast; ring,
      show (-(t - 0) ^ 2 / (2 * ((1:ℝ≥0):ℝ))) = (-(t ^ 2 / 2)) from by push_cast; ring]
  have hspos : (0:ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hexp : (0:ℝ) < Real.exp (x ^ 2 / 2) := Real.exp_pos _
  rw [hρexp]
  have hc : Real.sqrt (2 * Real.pi) * (Real.sqrt (2 * Real.pi))⁻¹ = 1 :=
    mul_inv_cancel₀ hspos.ne'
  have hcomb : Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
      ((Real.sqrt (2 * Real.pi))⁻¹ * ∫ t in Set.Iic x, Real.exp (-(t ^ 2 / 2)))
      = Real.exp (x ^ 2 / 2) * ∫ t in Set.Iic x, Real.exp (-(t ^ 2 / 2)) := by
    linear_combination (Real.exp (x ^ 2 / 2) * ∫ t in Set.Iic x, Real.exp (-(t ^ 2 / 2))) * hc
  rw [hcomb]
  refine le_trans (mul_le_mul_of_nonneg_left hmills hexp.le) (le_of_eq ?_)
  rw [← mul_div_assoc, ← Real.exp_add]
  have hx0 : (x ^ 2 / 2) + (-(x ^ 2 / 2)) = 0 := by ring
  rw [hx0, Real.exp_zero]

/-- Uniform bound near zero for the left tail: for `-1 ≤ x < 0`,
`√(2π) exp (x²/2) * ∫ t in Iic x, ρ t ≤ √(2π) exp (1/2)`. -/
theorem weight_tail_Iic_le_const {x : ℝ} (hx0 : x < 0) (hx1 : -1 ≤ x) :
    Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * (∫ t in Set.Iic x, gaussianPDFReal 0 1 t)
      ≤ Real.sqrt (2 * Real.pi) * Real.exp (1 / 2) := by
  have hmass : (∫ t in Set.Iic x, gaussianPDFReal 0 1 t) ≤ 1 := by
    have h1 : (∫ t in Set.Iic x, gaussianPDFReal 0 1 t) ≤ ∫ t, gaussianPDFReal 0 1 t := by
      refine setIntegral_le_integral ?_ ?_
      · exact (integrable_gaussianPDFReal_mul_pow 0).congr (ae_of_all _ fun t => by ring)
      · exact ae_of_all _ (fun t => gaussianPDFReal_nonneg 0 1 t)
    have h2 : (∫ t, gaussianPDFReal 0 1 t) = 1 := by
      have := integral_gaussianReal_eq_integral_smul (μ := 0) (v := 1)
        (f := fun t : ℝ => (1:ℝ)) (by norm_num : (1:ℝ≥0) ≠ 0)
      simpa using this.symm
    linarith [h1, h2]
  have hexp : Real.exp (x ^ 2 / 2) ≤ Real.exp (1 / 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hpos : (0:ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hmass0 : (0:ℝ) ≤ ∫ t in Set.Iic x, gaussianPDFReal 0 1 t :=
    setIntegral_nonneg measurableSet_Iic (fun t _ => gaussianPDFReal_nonneg 0 1 t)
  calc Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
        (∫ t in Set.Iic x, gaussianPDFReal 0 1 t)
      ≤ Real.sqrt (2 * Real.pi) * Real.exp (1 / 2) * 1 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hexp hpos.le) hmass hmass0
        exact mul_nonneg hpos.le (Real.exp_pos _).le
    _ = Real.sqrt (2 * Real.pi) * Real.exp (1 / 2) := by ring

/-- Global weight bound for the right tail, with the constant `max 1 (√(2π) exp (1/2))`. -/
theorem weight_tail_Ioi_le_global {x : ℝ} (hx : 0 < x) :
    Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * (∫ t in Set.Ioi x, gaussianPDFReal 0 1 t)
      ≤ max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2)) := by
  by_cases h1 : x ≤ 1
  · refine (weight_tail_Ioi_le_const hx h1).trans ?_
    exact le_max_right _ _
  · push_neg at h1
    refine (weight_tail_Ioi_le hx).trans ?_
    rw [one_div]
    have h2 : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1.le
    exact h2.trans (le_max_left _ _)

/-- Global weight bound for the left tail, with the constant `max 1 (√(2π) exp (1/2))`. -/
theorem weight_tail_Iic_le_global {x : ℝ} (hx : x < 0) :
    Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * (∫ t in Set.Iic x, gaussianPDFReal 0 1 t)
      ≤ max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2)) := by
  by_cases h1 : -1 ≤ x
  · refine (weight_tail_Iic_le_const hx h1).trans ?_
    exact le_max_right _ _
  · push_neg at h1
    refine (weight_tail_Iic_le hx).trans ?_
    rw [one_div]
    have h2 : (-x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    exact h2.trans (le_max_left _ _)

/-- The tail integral of `g ρ`. -/
def gueTail (g : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in Set.Ioi x, g t * gaussianPDFReal 0 1 t

/-- **Pointwise bound for the Stein kernel on the right half-line**:
`h x² * ρ x ≤ C * ∫ t in Ioi x, (g t)² * ρ t` with `C = max 1 (√(2π) e^{1/2})`. -/
theorem steinKernel_sq_mul_le_right {g : ℝ → ℝ} (hg : MemLp g 2 (gaussianReal 0 1)) {x : ℝ}
    (hx : 0 < x) :
    (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
        gaussianPDFReal 0 1 x
      ≤ max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2)) *
        ∫ t in Set.Ioi x, (g t) ^ 2 * gaussianPDFReal 0 1 t := by
  have hT := sq_integral_Ioi_mul_gaussianPDFReal_le (g := g) (x := x) hg
  have hnorm : Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gaussianPDFReal 0 1 x = 1 :=
    sqrt_two_pi_mul_exp_mul_gaussianPDFReal x
  have hw := weight_tail_Ioi_le_global hx
  have hmass0 : (0:ℝ) ≤ ∫ t in Set.Ioi x, gaussianPDFReal 0 1 t :=
    setIntegral_nonneg measurableSet_Ioi (fun t _ => gaussianPDFReal_nonneg 0 1 t)
  have hG0 : (0:ℝ) ≤ ∫ t in Set.Ioi x, (g t) ^ 2 * gaussianPDFReal 0 1 t :=
    setIntegral_nonneg measurableSet_Ioi (fun t _ => mul_nonneg (sq_nonneg _) (gaussianPDFReal_nonneg 0 1 t))
  have hexp : (0:ℝ) < Real.exp (x ^ 2 / 2) := Real.exp_pos _
  have hspos : (0:ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  -- h² ρ = √(2π) e^{x²/2} T²
  have hkey : (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
      gaussianPDFReal 0 1 x
      = Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * (gueTail g x) ^ 2 := by
    have h1 : Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gaussianPDFReal 0 1 x = 1 := hnorm
    linear_combination (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * (gueTail g x) ^ 2) * h1
  rw [hkey]
  -- combine: T² ≤ mass * G, weight ≤ C
  have hstep : Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * (gueTail g x) ^ 2
      ≤ Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
        ((∫ t in Set.Ioi x, gaussianPDFReal 0 1 t) *
          ∫ t in Set.Ioi x, (g t) ^ 2 * gaussianPDFReal 0 1 t) := by
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hspos.le hexp.le)
    simpa [gueTail] using hT
  refine hstep.trans ?_
  have hw' : Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
      (∫ t in Set.Ioi x, gaussianPDFReal 0 1 t) ≤
        max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2)) := hw
  calc Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
        ((∫ t in Set.Ioi x, gaussianPDFReal 0 1 t) *
          ∫ t in Set.Ioi x, (g t) ^ 2 * gaussianPDFReal 0 1 t)
      = (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
          (∫ t in Set.Ioi x, gaussianPDFReal 0 1 t)) *
          ∫ t in Set.Ioi x, (g t) ^ 2 * gaussianPDFReal 0 1 t := by ring
    _ ≤ max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2)) *
          ∫ t in Set.Ioi x, (g t) ^ 2 * gaussianPDFReal 0 1 t :=
        mul_le_mul_of_nonneg_right hw' hG0

/-- **Pointwise bound for the Stein kernel on the left half-line** (centred `g`):
`h x² * ρ x ≤ C * ∫ t in Iic x, (g t)² * ρ t`. -/
theorem steinKernel_sq_mul_le_left {g : ℝ → ℝ} (hg : MemLp g 2 (gaussianReal 0 1)) {x : ℝ}
    (hint : IntegrableOn (fun t => g t * gaussianPDFReal 0 1 t) (Set.univ))
    (hzero : ∫ t, g t * gaussianPDFReal 0 1 t = 0) (hx : x < 0) :
    (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
        gaussianPDFReal 0 1 x
      ≤ max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2)) *
        ∫ t in Set.Iic x, (g t) ^ 2 * gaussianPDFReal 0 1 t := by
  have hT := sq_integral_Ioi_mul_gaussianPDFReal_le_left (g := g) (x := x) hg hint hzero
  have hnorm : Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gaussianPDFReal 0 1 x = 1 :=
    sqrt_two_pi_mul_exp_mul_gaussianPDFReal x
  have hw := weight_tail_Iic_le_global hx
  have hG0 : (0:ℝ) ≤ ∫ t in Set.Iic x, (g t) ^ 2 * gaussianPDFReal 0 1 t :=
    setIntegral_nonneg measurableSet_Iic (fun t _ => mul_nonneg (sq_nonneg _) (gaussianPDFReal_nonneg 0 1 t))
  have hexp : (0:ℝ) < Real.exp (x ^ 2 / 2) := Real.exp_pos _
  have hspos : (0:ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hkey : (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
      gaussianPDFReal 0 1 x
      = Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * (gueTail g x) ^ 2 := by
    linear_combination (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * (gueTail g x) ^ 2) * hnorm
  rw [hkey]
  have hstep : Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * (gueTail g x) ^ 2
      ≤ Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
        ((∫ t in Set.Iic x, gaussianPDFReal 0 1 t) *
          ∫ t in Set.Iic x, (g t) ^ 2 * gaussianPDFReal 0 1 t) := by
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hspos.le hexp.le)
    simpa [gueTail] using hT
  refine hstep.trans ?_
  calc Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
        ((∫ t in Set.Iic x, gaussianPDFReal 0 1 t) *
          ∫ t in Set.Iic x, (g t) ^ 2 * gaussianPDFReal 0 1 t)
      = (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
          (∫ t in Set.Iic x, gaussianPDFReal 0 1 t)) *
          ∫ t in Set.Iic x, (g t) ^ 2 * gaussianPDFReal 0 1 t := by ring
    _ ≤ max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2)) *
          ∫ t in Set.Iic x, (g t) ^ 2 * gaussianPDFReal 0 1 t :=
        mul_le_mul_of_nonneg_right hw hG0

/-- The tail integral of a nonnegative function is antitone. -/
theorem antitone_lintegral_Ioi {F : ℝ → ℝ≥0∞} : Antitone fun x => ∫⁻ t in Set.Ioi x, F t := by
  intro x y hxy
  exact lintegral_mono_set (Set.Ioi_subset_Ioi hxy)

/-- **Monotone integral reduction**: for antitone `G`, `∫⁻ x in Ioi 0, G x ≤ ∑' k, G k`. -/
theorem lintegral_Ioi_zero_le_tsum {G : ℝ → ℝ≥0∞} (hanti : Antitone G) :
    ∫⁻ x in Set.Ioi (0:ℝ), G x ≤ ∑' k : ℕ, G k := by
  set H : ℝ → ℝ≥0∞ := fun x => ∑' k : ℕ,
    (Set.Icc (k:ℝ) ((k:ℝ) + 1)).indicator (fun _ => G k) x with hH
  have hpt : ∀ x ∈ Set.Ioi (0:ℝ), G x ≤ H x := by
    intro x hx
    have hx' : (0:ℝ) < x := hx
    have hkx : x ∈ Set.Icc ((⌊x⌋₊ : ℝ)) ((⌊x⌋₊ : ℝ) + 1) := by
      refine ⟨Nat.floor_le (le_of_lt hx'), ?_⟩
      have h := Nat.lt_floor_add_one x
      push_cast
      linarith
    calc G x ≤ G ⌊x⌋₊ := hanti (Nat.floor_le (le_of_lt hx'))
      _ = (Set.Icc (⌊x⌋₊ : ℝ) ((⌊x⌋₊ : ℝ) + 1)).indicator (fun _ => G ⌊x⌋₊) x :=
          (Set.indicator_of_mem hkx (fun _ => G ⌊x⌋₊)).symm
      _ ≤ ∑' k : ℕ, (Set.Icc (k:ℝ) ((k:ℝ) + 1)).indicator (fun _ => G k) x :=
          ENNReal.le_tsum (f := fun k : ℕ =>
            (Set.Icc (k:ℝ) ((k:ℝ) + 1)).indicator (fun _ => G k) x) ⌊x⌋₊
  have h1 : ∫⁻ x in Set.Ioi (0:ℝ), G x ≤ ∫⁻ x in Set.Ioi (0:ℝ), H x := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hpt x hx
  refine h1.trans ?_
  rw [lintegral_tsum (fun k => (measurable_const.indicator measurableSet_Icc).aemeasurable)]
  refine ENNReal.tsum_le_tsum (fun k => ?_)
  have hterm : ∫⁻ x in Set.Ioi (0:ℝ),
      (Set.Icc (k:ℝ) ((k:ℝ) + 1)).indicator (fun _ => G k) x
      = ∫⁻ x, (Set.Ioi (0:ℝ) ∩ Set.Icc (k:ℝ) ((k:ℝ) + 1)).indicator (fun _ => G k) x := by
    rw [← lintegral_indicator measurableSet_Ioi]
    congr 1
    funext x
    simp only [Set.indicator, Set.mem_inter_iff]
    by_cases h1 : x ∈ Set.Ioi (0:ℝ) <;> by_cases h2 : x ∈ Set.Icc (k:ℝ) ((k:ℝ) + 1) <;>
      simp [h1, h2]
  rw [hterm, lintegral_indicator_const (measurableSet_Ioi.inter measurableSet_Icc)]
  refine mul_le_of_le_one_right' ?_
  calc (volume : Measure ℝ) (Set.Ioi (0:ℝ) ∩ Set.Icc (k:ℝ) ((k:ℝ) + 1))
      ≤ volume (Set.Icc (k:ℝ) ((k:ℝ) + 1)) := measure_mono (Set.inter_subset_right)
    _ = 1 := by
        rw [Real.volume_Icc]
        norm_num

/-- The number of natural numbers below `t` is at most `t + 1`. -/
theorem tsum_Ioi_indicator_one_le (t : ℝ) :
    (∑' k : ℕ, (Set.Ioi (k:ℝ)).indicator (fun _ => (1:ℝ≥0∞)) t) ≤ ENNReal.ofReal t + 1 := by
  have hzero : ∀ k : ℕ, ⌊t⌋₊ + 1 ≤ k → (Set.Ioi (k:ℝ)).indicator (fun _ => (1:ℝ≥0∞)) t = 0 := by
    intro k hk
    refine Set.indicator_of_notMem ?_ _
    simp only [Set.mem_Ioi, not_lt]
    have h2 : (⌊t⌋₊ : ℝ) + 1 ≤ (k:ℝ) := by exact_mod_cast hk
    linarith [Nat.lt_floor_add_one t]
  have hbound : (∑' k : ℕ, (Set.Ioi (k:ℝ)).indicator (fun _ => (1:ℝ≥0∞)) t)
      ≤ (⌊t⌋₊ : ℝ≥0∞) + 1 := by
    rw [tsum_eq_sum (s := Finset.range (⌊t⌋₊ + 1)) (fun k hk => hzero k (by simpa using hk))]
    calc ∑ k ∈ Finset.range (⌊t⌋₊ + 1), (Set.Ioi (k:ℝ)).indicator (fun _ => (1:ℝ≥0∞)) t
        ≤ ∑ _k ∈ Finset.range (⌊t⌋₊ + 1), (1:ℝ≥0∞) := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          by_cases h : (k:ℝ) < t
          · rw [Set.indicator_of_mem (by simpa using h)]
          · rw [Set.indicator_of_notMem (by simpa using h)]
            exact zero_le_one
      _ = (⌊t⌋₊ : ℝ≥0∞) + 1 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
          push_cast
          ring
  refine hbound.trans ?_
  have hof : ENNReal.ofReal ((⌊t⌋₊ : ℝ)) ≤ ENNReal.ofReal t := by
    rcases le_or_gt (0:ℝ) t with h | h
    · exact ENNReal.ofReal_le_ofReal (Nat.floor_le h)
    · have h0 : ⌊t⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith : t < 1)
      rw [h0, ENNReal.ofReal_of_nonpos (le_of_lt h)]
      simp
  calc (⌊t⌋₊ : ℝ≥0∞) + 1 = ENNReal.ofReal ((⌊t⌋₊ : ℝ)) + 1 := by
        rw [ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal t + 1 := by
        have h := add_le_add_right hof (1 : ℝ≥0∞)
        simpa [add_comm] using h

/-- **Combined tail bound**: `∫⁻ x in Ioi 0, ∫⁻ t in Ioi x, F t ≤ ∫⁻ t, (ofReal t + 1) * F t`. -/
theorem lintegral_Ioi_lintegral_Ioi_le {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x in Set.Ioi (0:ℝ), ∫⁻ t in Set.Ioi x, F t
      ≤ ∫⁻ t, (ENNReal.ofReal t + 1) * F t := by
  have h1 := lintegral_Ioi_zero_le_tsum (G := fun x => ∫⁻ t in Set.Ioi x, F t)
    (antitone_lintegral_Ioi (F := F))
  refine h1.trans ?_
  have hind : ∀ k : ℕ, ∫⁻ t in Set.Ioi (k:ℝ), F t
      = ∫⁻ t, (Set.Ioi (k:ℝ)).indicator F t :=
        fun k => (lintegral_indicator measurableSet_Ioi (f := F) (s := Set.Ioi (k:ℝ))).symm
  simp_rw [hind]
  rw [← lintegral_tsum (fun k => (hF.indicator measurableSet_Ioi).aemeasurable)]
  refine lintegral_mono (fun t => ?_)
  have hpt : ∀ k : ℕ, (Set.Ioi (k:ℝ)).indicator F t
      = F t * (Set.Ioi (k:ℝ)).indicator (fun _ => (1:ℝ≥0∞)) t := by
    intro k
    by_cases h : t ∈ Set.Ioi (k:ℝ)
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, mul_one]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]
  simp_rw [hpt]
  rw [ENNReal.tsum_mul_left]
  rw [mul_comm]
  exact mul_le_mul_left (tsum_Ioi_indicator_one_le t) (F t)

/-- Mirror counting bound: the number of natural numbers `k` with `t ≤ -k` is at most `-t + 1`. -/
theorem tsum_Iic_indicator_one_le (t : ℝ) :
    (∑' k : ℕ, (Set.Iic (-(k:ℝ))).indicator (fun _ => (1:ℝ≥0∞)) t)
      ≤ ENNReal.ofReal (-t) + 1 := by
  have hzero : ∀ k : ℕ, ⌊-t⌋₊ + 1 ≤ k →
      (Set.Iic (-(k:ℝ))).indicator (fun _ => (1:ℝ≥0∞)) t = 0 := by
    intro k hk
    refine Set.indicator_of_notMem ?_ _
    simp only [Set.mem_Iic, not_le]
    have h2 : (⌊-t⌋₊ : ℝ) + 1 ≤ (k:ℝ) := by exact_mod_cast hk
    linarith [Nat.lt_floor_add_one (-t)]
  have hbound : (∑' k : ℕ, (Set.Iic (-(k:ℝ))).indicator (fun _ => (1:ℝ≥0∞)) t)
      ≤ (⌊-t⌋₊ : ℝ≥0∞) + 1 := by
    rw [tsum_eq_sum (s := Finset.range (⌊-t⌋₊ + 1)) (fun k hk => hzero k (by simpa using hk))]
    calc ∑ k ∈ Finset.range (⌊-t⌋₊ + 1), (Set.Iic (-(k:ℝ))).indicator (fun _ => (1:ℝ≥0∞)) t
        ≤ ∑ _k ∈ Finset.range (⌊-t⌋₊ + 1), (1:ℝ≥0∞) := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          by_cases h : t ∈ Set.Iic (-(k:ℝ))
          · rw [Set.indicator_of_mem h]
          · rw [Set.indicator_of_notMem h]
            exact zero_le_one
      _ = (⌊-t⌋₊ : ℝ≥0∞) + 1 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
          push_cast
          ring
  refine hbound.trans ?_
  have hof : ENNReal.ofReal ((⌊-t⌋₊ : ℝ)) ≤ ENNReal.ofReal (-t) := by
    rcases le_or_gt (0:ℝ) (-t) with h | h
    · exact ENNReal.ofReal_le_ofReal (Nat.floor_le h)
    · have h0 : ⌊-t⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith : -t < 1)
      rw [h0, ENNReal.ofReal_of_nonpos (le_of_lt h)]
      simp
  calc (⌊-t⌋₊ : ℝ≥0∞) + 1 = ENNReal.ofReal ((⌊-t⌋₊ : ℝ)) + 1 := by
        rw [ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (-t) + 1 := by
        have h := add_le_add_right hof (1 : ℝ≥0∞)
        simpa [add_comm] using h

/-- The lower-tail integral of a nonnegative function is monotone. -/
theorem monotone_lintegral_Iic {F : ℝ → ℝ≥0∞} : Monotone fun x => ∫⁻ t in Set.Iic x, F t := by
  intro x y hxy
  exact lintegral_mono_set (fun t ht => le_trans ht hxy)

/-- **Mirror monotone reduction**: for monotone `G`, `∫⁻ x in Iic 0, G x ≤ ∑' k, G (-k)`. -/
theorem lintegral_Iic_zero_le_tsum {G : ℝ → ℝ≥0∞} (hmono : Monotone G) :
    ∫⁻ x in Set.Iic (0:ℝ), G x ≤ ∑' k : ℕ, G (-(k:ℝ)) := by
  have hpt : ∀ x ∈ Set.Iic (0:ℝ),
      G x ≤ ∑' k : ℕ,
        (Set.Icc (-(k:ℝ) - 1) (-(k:ℝ))).indicator (fun _ => G (-(k:ℝ))) x := by
    intro x hx
    have hx' : x ≤ 0 := hx
    have hneg : (0:ℝ) ≤ -x := by linarith
    have hfl : (⌊-x⌋₊ : ℝ) ≤ -x := Nat.floor_le hneg
    have hxk : x ∈ Set.Icc (-(⌊-x⌋₊ : ℝ) - 1) (-(⌊-x⌋₊ : ℝ)) := by
      refine ⟨by linarith [Nat.lt_floor_add_one (-x)], by linarith⟩
    calc G x ≤ G (-(⌊-x⌋₊ : ℝ)) := hmono (by linarith)
      _ = (Set.Icc (-(⌊-x⌋₊ : ℝ) - 1) (-(⌊-x⌋₊ : ℝ))).indicator
            (fun _ => G (-(⌊-x⌋₊ : ℝ))) x := (Set.indicator_of_mem hxk (fun _ => G (-(⌊-x⌋₊ : ℝ)))).symm
      _ ≤ ∑' k : ℕ, (Set.Icc (-(k:ℝ) - 1) (-(k:ℝ))).indicator (fun _ => G (-(k:ℝ))) x :=
          ENNReal.le_tsum (f := fun k : ℕ =>
            (Set.Icc (-(k:ℝ) - 1) (-(k:ℝ))).indicator (fun _ => G (-(k:ℝ))) x) ⌊-x⌋₊
  have h1 : ∫⁻ x in Set.Iic (0:ℝ), G x
      ≤ ∫⁻ x in Set.Iic (0:ℝ), (fun x => ∑' k : ℕ,
        (Set.Icc (-(k:ℝ) - 1) (-(k:ℝ))).indicator (fun _ => G (-(k:ℝ))) x) x := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
    exact hpt x hx
  refine h1.trans ?_
  have hmeas : ∀ k : ℕ, Measurable
      ((Set.Icc (-(k:ℝ) - 1) (-(k:ℝ))).indicator (fun _ => G (-(k:ℝ)))) :=
    fun k => measurable_const.indicator measurableSet_Icc
  rw [lintegral_tsum (fun k => (hmeas k).aemeasurable)]
  refine ENNReal.tsum_le_tsum (fun k => ?_)
  rw [← lintegral_indicator measurableSet_Iic]
  have hstep : ∫⁻ a, (Set.Iic (0:ℝ)).indicator
        ((Set.Icc (-(k:ℝ) - 1) (-(k:ℝ))).indicator (fun _ => G (-(k:ℝ)))) a
      ≤ ∫⁻ a, (Set.Icc (-(k:ℝ) - 1) (-(k:ℝ))).indicator (fun _ => G (-(k:ℝ))) a := by
    refine lintegral_mono (fun a => ?_)
    by_cases h : a ∈ Set.Iic (0:ℝ)
    · rw [Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h]
      exact bot_le
  have h2 : ∫⁻ a, (Set.Icc (-(k:ℝ) - 1) (-(k:ℝ))).indicator (fun _ => G (-(k:ℝ))) a
      = G (-(k:ℝ)) := by
    rw [lintegral_indicator_const measurableSet_Icc (G (-(k:ℝ)))]
    have hv : volume (Set.Icc (-(k:ℝ) - 1) (-(k:ℝ))) = 1 := by
      rw [Real.volume_Icc, show (-(k:ℝ)) - (-(k:ℝ) - 1) = 1 from by ring, ENNReal.ofReal_one]
    rw [hv, mul_one]
  exact hstep.trans (le_of_eq h2)

/-- **Mirror combined tail bound**:
`∫⁻ x in Iic 0, ∫⁻ t in Iic x, F t ≤ ∫⁻ t, (ofReal (-t) + 1) * F t`. -/
theorem lintegral_Iic_lintegral_Iic_le {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x in Set.Iic (0:ℝ), ∫⁻ t in Set.Iic x, F t
      ≤ ∫⁻ t, (ENNReal.ofReal (-t) + 1) * F t := by
  have h1 := lintegral_Iic_zero_le_tsum (G := fun x => ∫⁻ t in Set.Iic x, F t)
    (monotone_lintegral_Iic (F := F))
  refine h1.trans ?_
  have hind : ∀ k : ℕ, ∫⁻ t in Set.Iic (-(k:ℝ)), F t
      = ∫⁻ t, (Set.Iic (-(k:ℝ))).indicator F t :=
    fun k => (lintegral_indicator measurableSet_Iic (f := F) (s := Set.Iic (-(k:ℝ)))).symm
  simp_rw [hind]
  rw [← lintegral_tsum (fun k => (hF.indicator measurableSet_Iic).aemeasurable)]
  refine lintegral_mono (fun t => ?_)
  have hpt : ∀ k : ℕ, (Set.Iic (-(k:ℝ))).indicator F t
      = F t * (Set.Iic (-(k:ℝ))).indicator (fun _ => (1:ℝ≥0∞)) t := by
    intro k
    by_cases h : t ∈ Set.Iic (-(k:ℝ))
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, mul_one]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]
  simp_rw [hpt]
  rw [ENNReal.tsum_mul_left, mul_comm]
  exact mul_le_mul_left (tsum_Iic_indicator_one_le t) (F t)

/-- `ofReal t + 1 ≤ ofReal (t² + 2)`. -/
theorem ofReal_add_one_le_sq_add_two (t : ℝ) :
    ENNReal.ofReal t + 1 ≤ ENNReal.ofReal (t ^ 2 + 2) := by
  rcases le_or_gt 0 t with h | h
  · rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add h zero_le_one]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg t])
  · rw [ENNReal.ofReal_of_nonpos (le_of_lt h), zero_add, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg t])

/-- Bridge between a real set-integral of a nonnegative function and its lintegral. -/
theorem ofReal_setIntegral_eq_lintegral {f : ℝ → ℝ} {s : Set ℝ}
    (hfi : IntegrableOn f s) (h0 : 0 ≤ᵐ[(volume.restrict s)] f) :
    ENNReal.ofReal (∫ t in s, f t) = ∫⁻ t in s, ENNReal.ofReal (f t) :=
  ofReal_integral_eq_lintegral_ofReal hfi h0

/-- Pointwise-nonnegative version. -/
theorem ofReal_setIntegral_eq_lintegral' {f : ℝ → ℝ} {s : Set ℝ}
    (hfi : IntegrableOn f s) (h0 : ∀ t, 0 ≤ f t) :
    ENNReal.ofReal (∫ t in s, f t) = ∫⁻ t in s, ENNReal.ofReal (f t) :=
  ofReal_setIntegral_eq_lintegral hfi (ae_of_all _ h0)

/-- Right-half finiteness of the squared Stein kernel. -/
theorem lintegral_steinKernel_sq_right_le {g : ℝ → ℝ} (hg : MemLp g 2 (gaussianReal 0 1))
    (hgm : Measurable g)
    (hint2 : ∀ x : ℝ, IntegrableOn (fun t => (g t) ^ 2 * gaussianPDFReal 0 1 t) (Set.Ioi x)) :
    ∫⁻ x in Set.Ioi (0:ℝ),
        ENNReal.ofReal ((Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
          gaussianPDFReal 0 1 x)
      ≤ ENNReal.ofReal (max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2))) *
        ∫⁻ t, ENNReal.ofReal ((t ^ 2 + 2) * ((g t) ^ 2 * gaussianPDFReal 0 1 t)) := by
  set F : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal ((g t) ^ 2 * gaussianPDFReal 0 1 t) with hFdef
  set C : ℝ := max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2)) with hCdef
  have hC0 : (0:ℝ) ≤ C := le_trans zero_le_one (le_max_left _ _)
  have hpt : ∀ x ∈ Set.Ioi (0:ℝ),
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
        gaussianPDFReal 0 1 x)
      ≤ ENNReal.ofReal C * ∫⁻ t in Set.Ioi x, F t := by
    intro x hx
    have hnn : ∀ t : ℝ, (0:ℝ) ≤ (g t) ^ 2 * gaussianPDFReal 0 1 t :=
      fun t => mul_nonneg (sq_nonneg _) (gaussianPDFReal_nonneg 0 1 t)
    have hbr := ofReal_setIntegral_eq_lintegral' (hint2 x) hnn
    have hb := steinKernel_sq_mul_le_right (g := g) hg hx
    rw [← hbr, ← ENNReal.ofReal_mul hC0]
    exact ENNReal.ofReal_le_ofReal hb
  have h1 : ∫⁻ x in Set.Ioi (0:ℝ),
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
        gaussianPDFReal 0 1 x)
      ≤ ∫⁻ x in Set.Ioi (0:ℝ), ENNReal.ofReal C * ∫⁻ t in Set.Ioi x, F t := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hpt x hx
  refine h1.trans ?_
  · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine mul_le_mul_right ?_ (ENNReal.ofReal C)
    refine (lintegral_Ioi_lintegral_Ioi_le (F := F) ?_).trans ?_
    · -- measurability of F
      show Measurable F
      fun_prop
    · refine lintegral_mono (fun t => ?_)
      rw [ENNReal.ofReal_mul (by positivity)]
      exact mul_le_mul_left (ofReal_add_one_le_sq_add_two t) (F t)

/-- `ofReal (-t) + 1 ≤ ofReal (t² + 2)`. -/
theorem ofReal_neg_add_one_le_sq_add_two (t : ℝ) :
    ENNReal.ofReal (-t) + 1 ≤ ENNReal.ofReal (t ^ 2 + 2) := by
  have h := ofReal_add_one_le_sq_add_two (-t)
  rwa [neg_sq] at h

/-- Left-half finiteness of the squared Stein kernel. -/
theorem lintegral_steinKernel_sq_left_le {g : ℝ → ℝ} (hg : MemLp g 2 (gaussianReal 0 1))
    (hgm : Measurable g)
    (hint : IntegrableOn (fun t => g t * gaussianPDFReal 0 1 t) (Set.univ))
    (hzero : ∫ t, g t * gaussianPDFReal 0 1 t = 0)
    (hint2 : ∀ x : ℝ, IntegrableOn (fun t => (g t) ^ 2 * gaussianPDFReal 0 1 t) (Set.Iic x)) :
    ∫⁻ x in Set.Iio (0:ℝ),
        ENNReal.ofReal ((Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
          gaussianPDFReal 0 1 x)
      ≤ ENNReal.ofReal (max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2))) *
        ∫⁻ t, ENNReal.ofReal ((t ^ 2 + 2) * ((g t) ^ 2 * gaussianPDFReal 0 1 t)) := by
  set F : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal ((g t) ^ 2 * gaussianPDFReal 0 1 t) with hFdef
  set C : ℝ := max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2)) with hCdef
  have hC0 : (0:ℝ) ≤ C := le_trans zero_le_one (le_max_left _ _)
  have hpt : ∀ x ∈ Set.Iio (0:ℝ),
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
        gaussianPDFReal 0 1 x)
      ≤ ENNReal.ofReal C * ∫⁻ t in Set.Iic x, F t := by
    intro x hx
    have hnn : ∀ t : ℝ, (0:ℝ) ≤ (g t) ^ 2 * gaussianPDFReal 0 1 t :=
      fun t => mul_nonneg (sq_nonneg _) (gaussianPDFReal_nonneg 0 1 t)
    have hbr := ofReal_setIntegral_eq_lintegral' (hint2 x) hnn
    have hb := steinKernel_sq_mul_le_left (g := g) hg hint hzero hx
    rw [← hbr, ← ENNReal.ofReal_mul hC0]
    exact ENNReal.ofReal_le_ofReal hb
  set G : ℝ → ℝ≥0∞ := fun x => ∫⁻ t in Set.Iic x, F t with hGdef
  have h1 : ∫⁻ x in Set.Iio (0:ℝ),
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
        gaussianPDFReal 0 1 x)
      ≤ ∫⁻ x in Set.Iio (0:ℝ), ENNReal.ofReal C * G x := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
    exact hpt x hx
  refine h1.trans ?_
  calc ∫⁻ x in Set.Iio (0:ℝ), ENNReal.ofReal C * G x
      ≤ ∫⁻ x in Set.Iic (0:ℝ), ENNReal.ofReal C * G x :=
        lintegral_mono_set (Set.Iio_subset_Iic (le_refl (0:ℝ)))
    _ = ENNReal.ofReal C * ∫⁻ x in Set.Iic (0:ℝ), G x := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal C * ∫⁻ t, ENNReal.ofReal ((t ^ 2 + 2) * ((g t) ^ 2 * gaussianPDFReal 0 1 t)) := by
        refine mul_le_mul_right ?_ (ENNReal.ofReal C)
        refine (lintegral_Iic_lintegral_Iic_le (F := F) ?_).trans ?_
        · show Measurable F
          fun_prop
        · refine lintegral_mono (fun t => ?_)
          rw [ENNReal.ofReal_mul (by positivity)]
          exact mul_le_mul_left (ofReal_neg_add_one_le_sq_add_two t) (F t)

/-- The endpoint `0` is negligible for the lintegral on `Iic 0`. -/
theorem lintegral_Iic_zero_eq_Iio {f : ℝ → ℝ≥0∞} :
    ∫⁻ x in Set.Iic (0:ℝ), f x = ∫⁻ x in Set.Iio (0:ℝ), f x := by
  have hae : Set.Iic (0:ℝ) =ᵐ[volume] Set.Iio (0:ℝ) := by
    refine (ae_eq_set).mpr ⟨?_, ?_⟩
    · -- (Iic 0) \ (Iio 0) = {0}
      have hset : Set.Iic (0:ℝ) \ Set.Iio (0:ℝ) = {(0:ℝ)} := by
        ext x
        simp only [Set.mem_diff, Set.mem_Iic, Set.mem_Iio, Set.mem_singleton_iff]
        constructor
        · rintro ⟨h1, h2⟩
          push_neg at h2
          linarith
        · rintro rfl
          exact ⟨le_refl 0, by norm_num⟩
      rw [hset]
      simp
    · -- (Iio 0) \ (Iic 0) = ∅
      have hset : Set.Iio (0:ℝ) \ Set.Iic (0:ℝ) = ∅ := by
        ext x
        simp only [Set.mem_diff, Set.mem_Iio, Set.mem_Iic, Set.mem_empty_iff_false, not_le]
        constructor
        · rintro ⟨h1, h2⟩
          linarith
        · intro h
          exact absurd h (by simp)
      rw [hset]
      simp
  rw [Measure.restrict_congr_set hae]

/-- Split of a lintegral over `ℝ` into `Iic 0` and `Ioi 0`. -/
theorem lintegral_eq_Iic_add_Ioi (f : ℝ → ℝ≥0∞) :
    ∫⁻ x, f x = (∫⁻ x in Set.Iic (0:ℝ), f x) + (∫⁻ x in Set.Ioi (0:ℝ), f x) := by
  have h := lintegral_add_compl (μ := volume) f (measurableSet_Iic (a := (0:ℝ)))
  rw [Set.compl_Iic] at h
  simpa using h.symm

/-- **Finiteness of the squared Stein kernel** against the Gaussian density. -/
theorem lintegral_steinKernel_sq_le {g : ℝ → ℝ} (hg : MemLp g 2 (gaussianReal 0 1))
    (hgm : Measurable g)
    (hint : IntegrableOn (fun t => g t * gaussianPDFReal 0 1 t) (Set.univ))
    (hzero : ∫ t, g t * gaussianPDFReal 0 1 t = 0)
    (hintR : ∀ x : ℝ, IntegrableOn (fun t => (g t) ^ 2 * gaussianPDFReal 0 1 t) (Set.Ioi x))
    (hintL : ∀ x : ℝ, IntegrableOn (fun t => (g t) ^ 2 * gaussianPDFReal 0 1 t) (Set.Iic x)) :
    ∫⁻ x, ENNReal.ofReal ((Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
        gaussianPDFReal 0 1 x)
      ≤ 2 * ENNReal.ofReal (max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2))) *
        ∫⁻ t, ENNReal.ofReal ((t ^ 2 + 2) * ((g t) ^ 2 * gaussianPDFReal 0 1 t)) := by
  have hL := lintegral_steinKernel_sq_left_le (g := g) hg hgm hint hzero hintL
  have hR := lintegral_steinKernel_sq_right_le (g := g) hg hgm hintR
  rw [lintegral_eq_Iic_add_Ioi (fun x => ENNReal.ofReal
    ((Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 * gaussianPDFReal 0 1 x))]
  rw [lintegral_Iic_zero_eq_Iio (f := fun x => ENNReal.ofReal
    ((Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 * gaussianPDFReal 0 1 x))]
  exact (add_le_add hL hR).trans_eq (by ring)

/-- The tail integral is a.e. strongly measurable in the cut-off point. -/
theorem aestronglyMeasurable_gueTail {g : ℝ → ℝ} (hgm : Measurable g) :
    AEStronglyMeasurable (gueTail g) (volume : Measure ℝ) := by
  have hj : StronglyMeasurable (Function.uncurry fun (x : ℝ) (t : ℝ) =>
      (Set.Ioi x).indicator (fun t => g t * gaussianPDFReal 0 1 t) t) := by
    refine Measurable.stronglyMeasurable ?_
    show Measurable (fun p : ℝ × ℝ =>
      if p.1 < p.2 then g p.2 * gaussianPDFReal 0 1 p.2 else 0)
    have hs : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} :=
      measurableSet_lt measurable_fst measurable_snd
    have h1 : Measurable fun p : ℝ × ℝ => g p.2 * gaussianPDFReal 0 1 p.2 :=
      (hgm.comp measurable_snd).mul (by fun_prop : Measurable fun p : ℝ × ℝ => gaussianPDFReal 0 1 p.2)
    exact Measurable.ite hs h1 measurable_const
  have h := hj.integral_prod_right (ν := (volume : Measure ℝ))
  have h2 := h.aestronglyMeasurable (μ := volume)
  have hfun : (fun x : ℝ => ∫ (y : ℝ),
      (Set.Ioi x).indicator (fun t => g t * gaussianPDFReal 0 1 t) y)
      = fun x => gueTail g x := by
    funext y
    exact integral_indicator (μ := volume) (measurableSet_Ioi (a := y))
      (f := fun t => g t * gaussianPDFReal 0 1 t)
  rw [hfun] at h2
  exact h2

/-- **Integrability of the squared Stein kernel** against the Gaussian density. -/
theorem integrable_steinKernel_sq {g : ℝ → ℝ} (hg : MemLp g 2 (gaussianReal 0 1))
    (hgm : Measurable g)
    (hint : IntegrableOn (fun t => g t * gaussianPDFReal 0 1 t) (Set.univ))
    (hzero : ∫ t, g t * gaussianPDFReal 0 1 t = 0)
    (hintR : ∀ x : ℝ, IntegrableOn (fun t => (g t) ^ 2 * gaussianPDFReal 0 1 t) (Set.Ioi x))
    (hintL : ∀ x : ℝ, IntegrableOn (fun t => (g t) ^ 2 * gaussianPDFReal 0 1 t) (Set.Iic x))
    (hW : Integrable (fun t => (t ^ 2 + 2) * ((g t) ^ 2 * gaussianPDFReal 0 1 t))) :
    Integrable (fun x => (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
      gaussianPDFReal 0 1 x) := by
  have hb := lintegral_steinKernel_sq_le (g := g) hg hgm hint hzero hintR hintL
  have hWfin : ∫⁻ t, ENNReal.ofReal ((t ^ 2 + 2) * ((g t) ^ 2 * gaussianPDFReal 0 1 t)) < ⊤ := by
    rw [← hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun t =>
      mul_nonneg (by positivity) (mul_nonneg (sq_nonneg _) (gaussianPDFReal_nonneg 0 1 t))))]
    exact hW.2
  have hlt : ∫⁻ x, ENNReal.ofReal ((Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
      gaussianPDFReal 0 1 x) < ⊤ :=
    lt_of_le_of_lt hb (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) hWfin.ne))
  refine ⟨?_, ?_⟩
  · have hT := aestronglyMeasurable_gueTail hgm
    have h1 : AEStronglyMeasurable
        (fun x : ℝ => Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) volume :=
      (by fun_prop : AEStronglyMeasurable
        (fun x : ℝ => Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2)) volume).mul hT
    exact h1.pow 2 |>.mul (by fun_prop)
  · rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun x =>
      mul_nonneg (sq_nonneg _) (gaussianPDFReal_nonneg 0 1 x)))]
    exact hlt

/-- The Stein kernel in its natural sign convention. -/
def steinG (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  -Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x

/-- `h² ρ` is integrable for the Stein kernel (transferred from `integrable_steinKernel_sq`). -/
theorem integrable_steinG_sq {g : ℝ → ℝ} (hg : MemLp g 2 (gaussianReal 0 1))
    (hgm : Measurable g)
    (hint : IntegrableOn (fun t => g t * gaussianPDFReal 0 1 t) (Set.univ))
    (hzero : ∫ t, g t * gaussianPDFReal 0 1 t = 0)
    (hintR : ∀ x : ℝ, IntegrableOn (fun t => (g t) ^ 2 * gaussianPDFReal 0 1 t) (Set.Ioi x))
    (hintL : ∀ x : ℝ, IntegrableOn (fun t => (g t) ^ 2 * gaussianPDFReal 0 1 t) (Set.Iic x))
    (hW : Integrable (fun t => (t ^ 2 + 2) * ((g t) ^ 2 * gaussianPDFReal 0 1 t))) :
    Integrable (fun x => (steinG g x) ^ 2 * gaussianPDFReal 0 1 x) := by
  have h := integrable_steinKernel_sq (g := g) hg hgm hint hzero hintR hintL hW
  refine h.congr (ae_of_all _ (fun x => ?_))
  simp only [steinG]
  ring

/-- The Stein kernel is `L²` for the Gaussian measure (the `hLp2` hypothesis). -/
theorem memLp_steinG_two {g : ℝ → ℝ} (hg : MemLp g 2 (gaussianReal 0 1))
    (hgm : Measurable g)
    (hint : IntegrableOn (fun t => g t * gaussianPDFReal 0 1 t) (Set.univ))
    (hzero : ∫ t, g t * gaussianPDFReal 0 1 t = 0)
    (hintR : ∀ x : ℝ, IntegrableOn (fun t => (g t) ^ 2 * gaussianPDFReal 0 1 t) (Set.Ioi x))
    (hintL : ∀ x : ℝ, IntegrableOn (fun t => (g t) ^ 2 * gaussianPDFReal 0 1 t) (Set.Iic x))
    (hW : Integrable (fun t => (t ^ 2 + 2) * ((g t) ^ 2 * gaussianPDFReal 0 1 t))) :
    MemLp (steinG g) 2 (gaussianReal 0 1) := by
  have hsq : Integrable (fun x => (steinG g x) ^ 2 * gaussianPDFReal 0 1 x) :=
    integrable_steinG_sq hg hgm hint hzero hintR hintL hW
  have hγ : Integrable (fun x => (steinG g x) ^ 2) (gaussianReal 0 1) := by
    have hd : gaussianReal 0 1 = volume.withDensity (gaussianPDF 0 1) :=
      gaussianReal_of_var_ne_zero 0 (by norm_num : (1:ℝ≥0) ≠ 0)
    rw [hd, integrable_withDensity_iff (measurable_gaussianPDF (μ := 0) (v := 1))
      (by filter_upwards with t using gaussianPDF_lt_top (μ := 0) (v := 1) (x := t))]
    refine hsq.congr (ae_of_all _ (fun x => ?_))
    simp only [toReal_gaussianPDF]
  refine (memLp_two_iff_integrable_sq ?_).mpr hγ
  show AEStronglyMeasurable (steinG g) (gaussianReal 0 1)
  have h1 : StronglyMeasurable (fun x => gueTail g x) := by
    have hj : StronglyMeasurable (Function.uncurry fun (x : ℝ) (t : ℝ) =>
        (Set.Ioi x).indicator (fun t => g t * gaussianPDFReal 0 1 t) t) := by
      refine Measurable.stronglyMeasurable ?_
      show Measurable (fun p : ℝ × ℝ =>
        if p.1 < p.2 then g p.2 * gaussianPDFReal 0 1 p.2 else 0)
      have hs : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} :=
        measurableSet_lt measurable_fst measurable_snd
      have h1' : Measurable fun p : ℝ × ℝ => g p.2 * gaussianPDFReal 0 1 p.2 :=
        (hgm.comp measurable_snd).mul (by fun_prop : Measurable fun p : ℝ × ℝ => gaussianPDFReal 0 1 p.2)
      exact Measurable.ite hs h1' measurable_const
    have h2 := hj.integral_prod_right (ν := (volume : Measure ℝ))
    have hfun : (fun x : ℝ => ∫ (y : ℝ),
        (Set.Ioi x).indicator (fun t => g t * gaussianPDFReal 0 1 t) y) = fun x => gueTail g x := by
      funext y
      exact integral_indicator (μ := volume) (measurableSet_Ioi (a := y))
        (f := fun t => g t * gaussianPDFReal 0 1 t)
    rw [hfun] at h2
    exact h2
  exact ((by fun_prop : StronglyMeasurable
    (fun x : ℝ => -Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2)))).mul h1 |>.aestronglyMeasurable

/-- Density-weighted integrability from `L²(γ)` (on a probability space `L² ⊆ L¹`). -/
theorem integrable_mul_gaussianPDFReal_of_memLp {f : ℝ → ℝ} (hf : MemLp f 2 (gaussianReal 0 1)) :
    Integrable (fun x => f x * gaussianPDFReal 0 1 x) := by
  have h1 : Integrable f (gaussianReal 0 1) := integrable_of_memLp_two hf
  have hd : gaussianReal 0 1 = volume.withDensity (gaussianPDF 0 1) :=
    gaussianReal_of_var_ne_zero 0 (by norm_num : (1:ℝ≥0) ≠ 0)
  rw [hd] at h1
  rw [integrable_withDensity_iff (measurable_gaussianPDF (μ := 0) (v := 1))
    (by filter_upwards with t using gaussianPDF_lt_top (μ := 0) (v := 1) (x := t))] at h1
  refine h1.congr (ae_of_all _ (fun x => ?_))
  simp only [toReal_gaussianPDF]

/-- Moments of every order are finite for the Gaussian measure. -/
theorem integrable_pow_gaussianReal (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (gaussianReal 0 1) := by
  have h := integrable_gaussianPDFReal_mul_pow n
  have hd : gaussianReal 0 1 = volume.withDensity (gaussianPDF 0 1) :=
    gaussianReal_of_var_ne_zero 0 (by norm_num : (1:ℝ≥0) ≠ 0)
  rw [hd]
  rw [integrable_withDensity_iff (measurable_gaussianPDF (μ := 0) (v := 1))
    (by filter_upwards with t using gaussianPDF_lt_top (μ := 0) (v := 1) (x := t))]
  refine h.congr (ae_of_all _ (fun x => ?_))
  simp only [toReal_gaussianPDF]
  ring

/-- `(1 + a)^m ≤ 2^m * (1 + a^m)` for `a ≥ 0`. -/
theorem one_add_pow_le_two_pow_mul (a : ℝ) (ha : 0 ≤ a) (m : ℕ) :
    (1 + a) ^ m ≤ 2 ^ m * (1 + a ^ m) := by
  induction m with
  | zero => norm_num
  | succ n ih =>
      have h2 : (0:ℝ) < 1 + a := by linarith
      have hstep : (1 + a) ^ (n + 1) ≤ 2 ^ n * (1 + a ^ n) * (1 + a) := by
        rw [pow_succ]
        exact mul_le_mul_of_nonneg_right ih (by linarith)
      have hkey : (1 + a ^ n) * (1 + a) ≤ 2 * (1 + a ^ (n + 1)) := by
        have hsucc := pow_succ a n
        rcases le_or_gt a 1 with h1 | h1
        · have h2 : a ^ n ≤ 1 := pow_le_one₀ ha h1
          nlinarith [hsucc, h2, h1, ha, pow_nonneg ha n]
        · have h2 : 1 ≤ a ^ n := one_le_pow₀ h1.le
          nlinarith [hsucc, h2, h1.le, ha, pow_nonneg ha n]
      calc (1 + a) ^ (n + 1) ≤ 2 ^ n * (1 + a ^ n) * (1 + a) := hstep
        _ = 2 ^ n * ((1 + a ^ n) * (1 + a)) := by ring
        _ ≤ 2 ^ n * (2 * (1 + a ^ (n + 1))) := by
            exact mul_le_mul_of_nonneg_left hkey (by positivity)
        _ = 2 ^ (n + 1) * (1 + a ^ (n + 1)) := by ring

/-- Any power of `|x|` up to order `m` is dominated by `1 + x^m` for `x ≥ 1`. -/
theorem abs_pow_le_one_add {x : ℝ} {n m : ℕ} (hx : 1 ≤ |x|) (hn : n ≤ m) :
    |x| ^ n ≤ 1 + |x| ^ m := by
  have h1 : |x| ^ n ≤ |x| ^ m := pow_le_pow_right₀ (by linarith) hn
  have h2 : (0:ℝ) ≤ |x| ^ n := by positivity
  linarith

/-- Polynomial growth makes `x ↦ x * g x` square-integrable for the Gaussian measure. -/
theorem memLp_id_mul_of_poly {g : ℝ → ℝ} (hgm : Measurable g)
    (hgr : ∃ C : ℝ, 0 ≤ C ∧ ∃ k : ℕ, ∀ x, |g x| ≤ C * (1 + |x|) ^ k) :
    MemLp (fun x => x * g x) 2 (gaussianReal 0 1) := by
  obtain ⟨C, hC0, k, hC⟩ := hgr
  set K : ℝ := 4 * C ^ 2 * 2 ^ (2 * k) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  set P : ℝ → ℝ := fun x => 1 + x ^ 2 + x ^ (2 * k + 4) with hP
  have hP0 : ∀ x, 0 ≤ P x := by
    intro x
    rw [hP]
    have hp2 : (0:ℝ) ≤ x ^ (2 * k + 4) := by
      have hsq : x ^ (2 * k + 4) = (x ^ (k + 2)) ^ 2 := by rw [← pow_mul]; ring_nf
      rw [hsq]; positivity
    nlinarith [sq_nonneg x, hp2]
  have hmaj : Integrable (fun x : ℝ => K * P x) (gaussianReal 0 1) := by
    have h1 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) := integrable_pow_gaussianReal 2
    have h2 : Integrable (fun x : ℝ => (1:ℝ)) (gaussianReal 0 1) := integrable_const 1
    have h3 : Integrable (fun x : ℝ => x ^ (2 * k + 4)) (gaussianReal 0 1) :=
      integrable_pow_gaussianReal _
    have h4 : Integrable (fun x : ℝ => 1 + x ^ 2 + x ^ (2 * k + 4)) (gaussianReal 0 1) := by
      have h := (h2.add h1).add h3
      exact h.congr (ae_of_all _ (fun x => by simp only [Pi.add_apply]))
    have h5 : Integrable (fun x : ℝ => K * (1 + x ^ 2 + x ^ (2 * k + 4))) (gaussianReal 0 1) :=
      h4.const_mul K
    exact h5
  refine (memLp_two_iff_integrable_sq ((measurable_id.mul hgm).aestronglyMeasurable)).mpr ?_
  refine hmaj.mono' ?_ ?_
  · exact ((measurable_id.mul hgm).pow_const 2).aestronglyMeasurable
  · filter_upwards with x
    have hb1 : |g x| ≤ C * 2 ^ k * (1 + |x| ^ k) := by
      have h := hC x
      have hb : (1 + |x|) ^ k ≤ 2 ^ k * (1 + |x| ^ k) :=
        one_add_pow_le_two_pow_mul |x| (abs_nonneg x) k
      calc |g x| ≤ C * (1 + |x|) ^ k := h
        _ ≤ C * (2 ^ k * (1 + |x| ^ k)) := mul_le_mul_of_nonneg_left hb hC0
        _ = C * 2 ^ k * (1 + |x| ^ k) := by ring
    have hb2 : (g x) ^ 2 ≤ (C * 2 ^ k) ^ 2 * (1 + |x| ^ k) ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg (g x)) hb1 2
      rw [mul_pow] at h
      simpa [sq_abs] using h
    have hp2 : (0:ℝ) ≤ x ^ (2 * k + 4) := by
      have hsq : x ^ (2 * k + 4) = (x ^ (k + 2)) ^ 2 := by rw [← pow_mul]; ring_nf
      rw [hsq]; positivity
    have hp12 : (0:ℝ) ≤ x ^ (2 * k + 2) := by
      have hsq : x ^ (2 * k + 2) = (x ^ (k + 1)) ^ 2 := by rw [← pow_mul]; ring_nf
      rw [hsq]; positivity
    have hxk : |x| ^ k ≤ 1 + x ^ (2 * k + 2) := by
      rcases le_or_gt 1 |x| with h1 | h1
      · have habs : |x| ^ (2 * k + 2) = x ^ (2 * k + 2) := by
          have hs1 : |x| ^ (2 * k + 2) = (|x| ^ (k + 1)) ^ 2 := by rw [← pow_mul]; ring_nf
          have hs2 : x ^ (2 * k + 2) = (x ^ (k + 1)) ^ 2 := by rw [← pow_mul]; ring_nf
          rw [hs1, hs2, ← abs_pow, sq_abs]
        have h := abs_pow_le_one_add (x := x) h1 (n := k) (m := 2 * k + 2) (by omega)
        rw [habs] at h
        linarith
      · have h2 : |x| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg x) h1.le
        linarith
    have hx2k : |x| ^ (2 * k) ≤ 1 + x ^ (2 * k + 2) := by
      rcases le_or_gt 1 |x| with h1 | h1
      · have habs : |x| ^ (2 * k + 2) = x ^ (2 * k + 2) := by
          have hs1 : |x| ^ (2 * k + 2) = (|x| ^ (k + 1)) ^ 2 := by rw [← pow_mul]; ring_nf
          have hs2 : x ^ (2 * k + 2) = (x ^ (k + 1)) ^ 2 := by rw [← pow_mul]; ring_nf
          rw [hs1, hs2, ← abs_pow, sq_abs]
        have h := abs_pow_le_one_add (x := x) h1 (n := 2 * k) (m := 2 * k + 2) (by omega)
        rw [habs] at h
        linarith
      · have h2 : |x| ^ (2 * k) ≤ 1 := pow_le_one₀ (abs_nonneg x) h1.le
        linarith
    have hb3 : (1 + |x| ^ k) ^ 2 ≤ 4 * (1 + x ^ (2 * k + 2)) := by
      have hpow : (|x| ^ k) ^ 2 = |x| ^ (2 * k) := by rw [← pow_mul, mul_comm]
      nlinarith [hxk, hx2k, hpow, hp12]
    -- final: x^2 * (g x)^2 ≤ K * P x
    show ‖((id x * g x) : ℝ) ^ 2‖ ≤ K * P x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      show ((id x * g x) : ℝ) ^ 2 = x ^ 2 * (g x) ^ 2 by simp only [id]; ring,
      hP, hK]
    have hx2nn : (0:ℝ) ≤ x ^ 2 := sq_nonneg x
    have hCk : (0:ℝ) ≤ (C * 2 ^ k) ^ 2 * (1 + |x| ^ k) ^ 2 := by positivity
    have step1 : x ^ 2 * (g x) ^ 2 ≤ x ^ 2 * ((C * 2 ^ k) ^ 2 * (1 + |x| ^ k) ^ 2) :=
      mul_le_mul_of_nonneg_left hb2 hx2nn
    have step2 : x ^ 2 * ((C * 2 ^ k) ^ 2 * (1 + |x| ^ k) ^ 2)
        ≤ x ^ 2 * ((C * 2 ^ k) ^ 2 * (4 * (1 + x ^ (2 * k + 2)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb3 (by positivity)) hx2nn
    have step3 : x ^ 2 * ((C * 2 ^ k) ^ 2 * (4 * (1 + x ^ (2 * k + 2))))
        ≤ 4 * C ^ 2 * 2 ^ (2 * k) * (1 + x ^ 2 + x ^ (2 * k + 4)) := by
      have hC2 : (C * 2 ^ k) ^ 2 = C ^ 2 * 2 ^ (2 * k) := by rw [mul_pow, ← pow_mul, mul_comm k 2]
      rw [hC2]
      have hpadd : x ^ 2 * x ^ (2 * k + 2) = x ^ (2 * k + 4) := by
        rw [← pow_add]; ring_nf
      nlinarith [hx2nn, hp12, hp2, sq_nonneg C, pow_nonneg (by norm_num : (0:ℝ) ≤ 2) (2 * k), hpadd]
    exact step1.trans (step2.trans step3)

/-- `x * (ρ x * g x)` is integrable for polynomially growing `g`. -/
theorem integrable_id_mul_gaussianPDFReal_mul_of_poly {g : ℝ → ℝ} (hgm : Measurable g)
    (hgr : ∃ C : ℝ, 0 ≤ C ∧ ∃ k : ℕ, ∀ x, |g x| ≤ C * (1 + |x|) ^ k) :
    Integrable (fun x => x * (gaussianPDFReal 0 1 x * g x)) := by
  have h := integrable_mul_gaussianPDFReal_of_memLp (memLp_id_mul_of_poly hgm hgr)
  refine h.congr (ae_of_all _ (fun x => ?_))
  ring

/-- The tail integral is bounded by the total mass of `|g| ρ`. -/
theorem abs_gueTail_le {g : ℝ → ℝ} (hg1 : Integrable (fun t => |g t| * gaussianPDFReal 0 1 t))
    (x : ℝ) : |gueTail g x| ≤ ∫ t, |g t| * gaussianPDFReal 0 1 t := by
  have h1 : |gueTail g x| ≤ ∫ t in Set.Ioi x, |g t| * gaussianPDFReal 0 1 t := by
    have h := abs_integral_le_integral_abs
      (μ := volume.restrict (Set.Ioi x)) (f := fun t => g t * gaussianPDFReal 0 1 t)
    simpa [gueTail, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (gaussianPDFReal_nonneg 0 1 _)] using h
  refine h1.trans ?_
  exact setIntegral_le_integral hg1 (ae_of_all _ (fun t =>
    mul_nonneg (abs_nonneg _) (gaussianPDFReal_nonneg 0 1 t)))

/-- `x g ρ T` is integrable when `g` grows polynomially and `|g| ρ` is integrable. -/
theorem integrable_id_mul_mul_gueTail {g : ℝ → ℝ} (hgm : Measurable g)
    (hgr : ∃ C : ℝ, 0 ≤ C ∧ ∃ k : ℕ, ∀ x, |g x| ≤ C * (1 + |x|) ^ k)
    (hg1 : Integrable (fun t => |g t| * gaussianPDFReal 0 1 t))
    (hxgr : Integrable (fun x => x * (gaussianPDFReal 0 1 x * g x))) :
    Integrable (fun x => x * (g x * gaussianPDFReal 0 1 x * gueTail g x)) := by
  set M : ℝ := ∫ t, |g t| * gaussianPDFReal 0 1 t with hM
  have hM0 : 0 ≤ M := integral_nonneg (fun t => mul_nonneg (abs_nonneg _)
    (gaussianPDFReal_nonneg 0 1 t))
  have hdom : Integrable (fun x => M * |x * (gaussianPDFReal 0 1 x * g x)|) :=
    hxgr.norm.const_mul M
  refine hdom.mono' ?_ ?_
  · have hT := aestronglyMeasurable_gueTail hgm
    have hgρ : AEStronglyMeasurable (fun x : ℝ => gaussianPDFReal 0 1 x) volume := by fun_prop
    have hxg : AEStronglyMeasurable (fun x : ℝ => x * (gaussianPDFReal 0 1 x * g x)) volume := by
      fun_prop
    have := hxg.mul hT
    refine this.congr ?_
    filter_upwards with x
    simp only [Pi.mul_apply]
    ring
  · filter_upwards with x
    have hb := abs_gueTail_le hg1 x
    have h1 : |x * (g x * gaussianPDFReal 0 1 x * gueTail g x)|
        = |x * (gaussianPDFReal 0 1 x * g x)| * |gueTail g x| := by
      rw [show x * (g x * gaussianPDFReal 0 1 x * gueTail g x)
        = (x * (gaussianPDFReal 0 1 x * g x)) * gueTail g x from by ring, abs_mul]
    rw [Real.norm_eq_abs, h1, mul_comm]
    exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)

/-- **Weighted monotone reduction**: for antitone `G` and monotone `w`,
`∫⁻ x in Ioi 0, w x * G x ≤ ∑' k, w (k+1) * G k`. -/
theorem lintegral_Ioi_zero_weighted {G : ℝ → ℝ≥0∞} (hanti : Antitone G)
    {w : ℝ → ℝ≥0∞} (hwmono : Monotone w) :
    ∫⁻ x in Set.Ioi (0:ℝ), w x * G x ≤ ∑' k : ℕ, w ((k:ℝ) + 1) * G k := by
  have hpt : ∀ x ∈ Set.Ioi (0:ℝ),
      w x * G x ≤ ∑' k : ℕ,
        (Set.Icc (k:ℝ) ((k:ℝ) + 1)).indicator (fun _ => w ((k:ℝ) + 1) * G k) x := by
    intro x hx
    have hx' : (0:ℝ) < x := hx
    have hkx : x ∈ Set.Icc ((⌊x⌋₊ : ℝ)) ((⌊x⌋₊ : ℝ) + 1) := by
      refine ⟨Nat.floor_le (le_of_lt hx'), ?_⟩
      have h := Nat.lt_floor_add_one x
      push_cast
      linarith
    have hfl := Nat.lt_floor_add_one x
    push_cast at hfl
    have hw1 : w x ≤ w ((⌊x⌋₊ : ℝ) + 1) := hwmono (le_of_lt hfl)
    have hG1 : G x ≤ G ⌊x⌋₊ := hanti (Nat.floor_le (le_of_lt hx'))
    calc w x * G x ≤ w ((⌊x⌋₊ : ℝ) + 1) * G ⌊x⌋₊ :=
          mul_le_mul hw1 hG1 bot_le bot_le
      _ = (Set.Icc ((⌊x⌋₊ : ℝ)) ((⌊x⌋₊ : ℝ) + 1)).indicator
            (fun _ => w ((⌊x⌋₊ : ℝ) + 1) * G ⌊x⌋₊) x :=
          (Set.indicator_of_mem hkx (fun _ => w ((⌊x⌋₊ : ℝ) + 1) * G ⌊x⌋₊)).symm
      _ ≤ ∑' k : ℕ, (Set.Icc (k:ℝ) ((k:ℝ) + 1)).indicator
            (fun _ => w ((k:ℝ) + 1) * G k) x :=
          ENNReal.le_tsum (f := fun k : ℕ =>
            (Set.Icc (k:ℝ) ((k:ℝ) + 1)).indicator (fun _ => w ((k:ℝ) + 1) * G k) x) ⌊x⌋₊
  have h1 : ∫⁻ x in Set.Ioi (0:ℝ), w x * G x
      ≤ ∫⁻ x in Set.Ioi (0:ℝ), (fun x => ∑' k : ℕ,
        (Set.Icc (k:ℝ) ((k:ℝ) + 1)).indicator (fun _ => w ((k:ℝ) + 1) * G k) x) x := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hpt x hx
  refine h1.trans ?_
  rw [lintegral_tsum (fun k => (measurable_const.indicator measurableSet_Icc).aemeasurable)]
  refine ENNReal.tsum_le_tsum (fun k => ?_)
  have hterm : ∫⁻ x in Set.Ioi (0:ℝ),
      (Set.Icc (k:ℝ) ((k:ℝ) + 1)).indicator (fun _ => w ((k:ℝ) + 1) * G k) x
      = ∫⁻ x, (Set.Ioi (0:ℝ) ∩ Set.Icc (k:ℝ) ((k:ℝ) + 1)).indicator
          (fun _ => w ((k:ℝ) + 1) * G k) x := by
    rw [← lintegral_indicator measurableSet_Ioi]
    congr 1
    funext x
    simp only [Set.indicator, Set.mem_inter_iff]
    by_cases h1 : x ∈ Set.Ioi (0:ℝ) <;> by_cases h2 : x ∈ Set.Icc (k:ℝ) ((k:ℝ) + 1) <;>
      simp [h1, h2]
  rw [hterm, lintegral_indicator_const (measurableSet_Ioi.inter measurableSet_Icc)]
  refine mul_le_of_le_one_right' ?_
  calc (volume : Measure ℝ) (Set.Ioi (0:ℝ) ∩ Set.Icc (k:ℝ) ((k:ℝ) + 1))
      ≤ volume (Set.Icc (k:ℝ) ((k:ℝ) + 1)) := measure_mono (Set.inter_subset_right)
    _ = 1 := by
        rw [Real.volume_Icc]
        norm_num

/-- **Weighted counting bound**: `∑' k, (k+1)² 1_{t > k} ≤ (t+1)³`. -/
theorem tsum_Ioi_indicator_sq_le {t : ℝ} (ht : 0 ≤ t) :
    (∑' k : ℕ, ((k : ℝ≥0∞) + 1) ^ 2 * (Set.Ioi (k:ℝ)).indicator (fun _ => (1:ℝ≥0∞)) t)
      ≤ ENNReal.ofReal ((t + 1) ^ 3) := by
  have hzero : ∀ k : ℕ, ⌊t⌋₊ + 1 ≤ k →
      ((k : ℝ≥0∞) + 1) ^ 2 * (Set.Ioi (k:ℝ)).indicator (fun _ => (1:ℝ≥0∞)) t = 0 := by
    intro k hk
    have hkt : ¬ ((k:ℝ) < t) := by
      have h2 : (⌊t⌋₊ : ℝ) + 1 ≤ (k:ℝ) := by exact_mod_cast hk
      linarith [Nat.lt_floor_add_one t]
    simp only [Set.indicator, Set.mem_Ioi, hkt, if_false, mul_zero]
  rw [tsum_eq_sum (s := Finset.range (⌊t⌋₊ + 1)) (fun k hk => hzero k (by simpa using hk))]
  have hterm : ∀ k ∈ Finset.range (⌊t⌋₊ + 1),
      ((k : ℝ≥0∞) + 1) ^ 2 * (Set.Ioi (k:ℝ)).indicator (fun _ => (1:ℝ≥0∞)) t
        ≤ ((⌊t⌋₊ : ℝ≥0∞) + 1) ^ 2 := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hind : (Set.Ioi (k:ℝ)).indicator (fun _ => (1:ℝ≥0∞)) t ≤ 1 := by
      by_cases h : t ∈ Set.Ioi (k:ℝ)
      · rw [Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h]
        exact bot_le
    calc ((k : ℝ≥0∞) + 1) ^ 2 * (Set.Ioi (k:ℝ)).indicator (fun _ => (1:ℝ≥0∞)) t
        ≤ ((k : ℝ≥0∞) + 1) ^ 2 * 1 := mul_le_mul_right hind _
      _ = ((k : ℝ≥0∞) + 1) ^ 2 := mul_one _
      _ ≤ ((⌊t⌋₊ : ℝ≥0∞) + 1) ^ 2 := by
          have hk' : (k : ℝ≥0∞) ≤ (⌊t⌋₊ : ℝ≥0∞) := by exact_mod_cast Nat.le_of_lt_succ hk
          have hk'' : (k : ℝ≥0∞) + 1 ≤ (⌊t⌋₊ : ℝ≥0∞) + 1 := by
            rw [add_comm (k : ℝ≥0∞) 1, add_comm ((⌊t⌋₊ : ℝ≥0∞)) 1]
            exact add_le_add_right hk' 1
          exact pow_le_pow_left₀ bot_le hk'' 2
  have hsum : ∑ k ∈ Finset.range (⌊t⌋₊ + 1),
      ((k : ℝ≥0∞) + 1) ^ 2 * (Set.Ioi (k:ℝ)).indicator (fun _ => (1:ℝ≥0∞)) t
      ≤ ((⌊t⌋₊ : ℝ≥0∞) + 1) ^ 3 := by
    calc ∑ k ∈ Finset.range (⌊t⌋₊ + 1),
          ((k : ℝ≥0∞) + 1) ^ 2 * (Set.Ioi (k:ℝ)).indicator (fun _ => (1:ℝ≥0∞)) t
        ≤ ∑ _k ∈ Finset.range (⌊t⌋₊ + 1), ((⌊t⌋₊ : ℝ≥0∞) + 1) ^ 2 :=
          Finset.sum_le_sum (fun k hk => hterm k hk)
      _ = ((⌊t⌋₊ + 1 : ℕ) : ℝ≥0∞) * ((⌊t⌋₊ : ℝ≥0∞) + 1) ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ((⌊t⌋₊ : ℝ≥0∞) + 1) ^ 3 := by
          rw [Nat.cast_add, Nat.cast_one]
          ring
  refine hsum.trans ?_
  have hcast : ((⌊t⌋₊ : ℝ≥0∞) + 1) = ENNReal.ofReal ((⌊t⌋₊ : ℝ) + 1) := by
    rw [ENNReal.ofReal_add (Nat.cast_nonneg _) (by norm_num), ENNReal.ofReal_natCast,
      ENNReal.ofReal_one]
  rw [hcast, ← ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ (⌊t⌋₊ : ℝ) + 1)]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (⌊t⌋₊ : ℝ) + 1)
    (by linarith [Nat.floor_le ht]) 3)

/-- **Weighted monotone reduction (half-line weights)**. -/
theorem lintegral_Ioi_zero_weighted' {G : ℝ → ℝ≥0∞} (hanti : Antitone G)
    {w : ℝ → ℝ≥0∞} (hwmono : ∀ x y : ℝ, 0 ≤ x → x ≤ y → w x ≤ w y) :
    ∫⁻ x in Set.Ioi (0:ℝ), w x * G x ≤ ∑' k : ℕ, w ((k:ℝ) + 1) * G k := by
  have hpt : ∀ x ∈ Set.Ioi (0:ℝ),
      w x * G x ≤ ∑' k : ℕ,
        (Set.Icc (k:ℝ) ((k:ℝ) + 1)).indicator (fun _ => w ((k:ℝ) + 1) * G k) x := by
    intro x hx
    have hx' : (0:ℝ) < x := hx
    have hkx : x ∈ Set.Icc ((⌊x⌋₊ : ℝ)) ((⌊x⌋₊ : ℝ) + 1) := by
      refine ⟨Nat.floor_le (le_of_lt hx'), ?_⟩
      have h := Nat.lt_floor_add_one x
      push_cast
      linarith
    have hfl := Nat.lt_floor_add_one x
    push_cast at hfl
    have hw1 : w x ≤ w ((⌊x⌋₊ : ℝ) + 1) := hwmono x _ (le_of_lt hx') (le_of_lt hfl)
    have hG1 : G x ≤ G ⌊x⌋₊ := hanti (Nat.floor_le (le_of_lt hx'))
    calc w x * G x ≤ w ((⌊x⌋₊ : ℝ) + 1) * G ⌊x⌋₊ := mul_le_mul hw1 hG1 bot_le bot_le
      _ = (Set.Icc ((⌊x⌋₊ : ℝ)) ((⌊x⌋₊ : ℝ) + 1)).indicator
            (fun _ => w ((⌊x⌋₊ : ℝ) + 1) * G ⌊x⌋₊) x :=
          (Set.indicator_of_mem hkx (fun _ => w ((⌊x⌋₊ : ℝ) + 1) * G ⌊x⌋₊)).symm
      _ ≤ ∑' k : ℕ, (Set.Icc (k:ℝ) ((k:ℝ) + 1)).indicator
            (fun _ => w ((k:ℝ) + 1) * G k) x :=
          ENNReal.le_tsum (f := fun k : ℕ =>
            (Set.Icc (k:ℝ) ((k:ℝ) + 1)).indicator (fun _ => w ((k:ℝ) + 1) * G k) x) ⌊x⌋₊
  have h1 : ∫⁻ x in Set.Ioi (0:ℝ), w x * G x
      ≤ ∫⁻ x in Set.Ioi (0:ℝ), (fun x => ∑' k : ℕ,
        (Set.Icc (k:ℝ) ((k:ℝ) + 1)).indicator (fun _ => w ((k:ℝ) + 1) * G k) x) x := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hpt x hx
  refine h1.trans ?_
  rw [lintegral_tsum (fun k => (measurable_const.indicator measurableSet_Icc).aemeasurable)]
  refine ENNReal.tsum_le_tsum (fun k => ?_)
  have hterm : ∫⁻ x in Set.Ioi (0:ℝ),
      (Set.Icc (k:ℝ) ((k:ℝ) + 1)).indicator (fun _ => w ((k:ℝ) + 1) * G k) x
      = ∫⁻ x, (Set.Ioi (0:ℝ) ∩ Set.Icc (k:ℝ) ((k:ℝ) + 1)).indicator
          (fun _ => w ((k:ℝ) + 1) * G k) x := by
    rw [← lintegral_indicator measurableSet_Ioi]
    congr 1
    funext x
    simp only [Set.indicator, Set.mem_inter_iff]
    by_cases h1 : x ∈ Set.Ioi (0:ℝ) <;> by_cases h2 : x ∈ Set.Icc (k:ℝ) ((k:ℝ) + 1) <;>
      simp [h1, h2]
  rw [hterm, lintegral_indicator_const (measurableSet_Ioi.inter measurableSet_Icc)]
  refine mul_le_of_le_one_right' ?_
  calc (volume : Measure ℝ) (Set.Ioi (0:ℝ) ∩ Set.Icc (k:ℝ) ((k:ℝ) + 1))
      ≤ volume (Set.Icc (k:ℝ) ((k:ℝ) + 1)) := measure_mono (Set.inter_subset_right)
    _ = 1 := by
        rw [Real.volume_Icc]
        norm_num

/-- Factoring a constant out of an indicator: `c * 1_s * F = (c * 1_s) * F` pointwise. -/
theorem const_mul_indicator_eq (c : ℝ≥0∞) (F : ℝ → ℝ≥0∞) (s : Set ℝ) (t : ℝ) :
    c * s.indicator F t = (c * s.indicator (fun _ => (1:ℝ≥0∞)) t) * F t := by
  by_cases h : t ∈ s
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, mul_one]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
    simp only [mul_zero, zero_mul]

/-- **`x²`-weighted Tonelli bound**: `∫⁻ x in Ioi 0, x² (∫⁻ t in Ioi x, F t)
≤ ∫⁻ t, (t+1)³ F t`. -/
theorem lintegral_Ioi_sq_lintegral_Ioi_le {F : ℝ → ℝ≥0∞} (hF : AEMeasurable F volume) :
    ∫⁻ x in Set.Ioi (0:ℝ), ENNReal.ofReal (x ^ 2) * (∫⁻ t in Set.Ioi x, F t)
      ≤ ∫⁻ t, ENNReal.ofReal ((t + 1) ^ 3) * F t := by
  have hanti : Antitone fun x : ℝ => ∫⁻ t in Set.Ioi x, F t := antitone_lintegral_Ioi (F := F)
  have hwmono : ∀ x y : ℝ, 0 ≤ x → x ≤ y → ENNReal.ofReal (x ^ 2) ≤ ENNReal.ofReal (y ^ 2) := by
    intro x y hx hxy
    apply ENNReal.ofReal_le_ofReal
    nlinarith
  refine (lintegral_Ioi_zero_weighted' hanti hwmono).trans ?_
  have hind : ∀ k : ℕ, ENNReal.ofReal (((k:ℝ) + 1) ^ 2) * (∫⁻ t in Set.Ioi (k:ℝ), F t)
      = ∫⁻ t, ENNReal.ofReal (((k:ℝ) + 1) ^ 2) * (Set.Ioi (k:ℝ)).indicator F t := by
    intro k
    rw [← lintegral_indicator measurableSet_Ioi]
    exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
  simp_rw [hind]
  have hswap : (∑' k : ℕ, ∫⁻ t,
      ENNReal.ofReal (((k:ℝ) + 1) ^ 2) * (Set.Ioi (k:ℝ)).indicator F t)
      = ∫⁻ t, ∑' k : ℕ,
        ENNReal.ofReal (((k:ℝ) + 1) ^ 2) * (Set.Ioi (k:ℝ)).indicator F t := by
    rw [lintegral_tsum]
    intro k
    exact AEMeasurable.const_mul (hF.indicator measurableSet_Ioi) _
  rw [hswap]
  refine lintegral_mono (fun t => ?_)
  have hpt : ∀ k : ℕ, ENNReal.ofReal (((k:ℝ) + 1) ^ 2) * (Set.Ioi (k:ℝ)).indicator F t
      = (ENNReal.ofReal (((k:ℝ) + 1) ^ 2)
          * (Set.Ioi (k:ℝ)).indicator (fun _ => (1:ℝ≥0∞)) t) * F t :=
    fun k => const_mul_indicator_eq _ F _ t
  simp_rw [hpt]
  rw [ENNReal.tsum_mul_right]
  have hmain : (∑' k : ℕ, ENNReal.ofReal (((k:ℝ) + 1) ^ 2)
      * (Set.Ioi (k:ℝ)).indicator (fun _ => (1:ℝ≥0∞)) t) ≤ ENNReal.ofReal ((t + 1) ^ 3) := by
    have hcast : ∀ k : ℕ, ENNReal.ofReal (((k:ℝ) + 1) ^ 2) = ((k : ℝ≥0∞) + 1) ^ 2 := by
      intro k
      have h1 : ENNReal.ofReal ((k:ℝ) + 1) = (k : ℝ≥0∞) + 1 := by
        rw [ENNReal.ofReal_add (Nat.cast_nonneg k) (by norm_num), ENNReal.ofReal_natCast,
          ENNReal.ofReal_one]
      rw [ENNReal.ofReal_pow (by positivity), h1]
    simp_rw [hcast]
    by_cases ht : 0 ≤ t
    · exact tsum_Ioi_indicator_sq_le ht
    · push_neg at ht
      have hnil : ∀ k : ℕ, (Set.Ioi (k:ℝ)).indicator (fun _ => (1:ℝ≥0∞)) t = 0 := by
        intro k
        refine Set.indicator_of_notMem ?_ _
        simp only [Set.mem_Ioi, not_lt]
        have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
        linarith
      simp only [hnil, mul_zero, tsum_zero]
      exact bot_le
  exact mul_le_mul_left hmain (F t)

/-- **Mirror weighted reduction**: for monotone `G` and a weight that is antitone on the negative
half-line, `∫⁻ x in Iic 0, w x * G x ≤ ∑' k, w (-(k+1)) * G (-k)`. -/
theorem lintegral_Iic_zero_weighted {G : ℝ → ℝ≥0∞} (hmono : Monotone G)
    {w : ℝ → ℝ≥0∞} (hwanti : ∀ x y : ℝ, x ≤ y → y ≤ 0 → w y ≤ w x) :
    ∫⁻ x in Set.Iic (0:ℝ), w x * G x ≤ ∑' k : ℕ, w (-((k:ℝ) + 1)) * G (-(k:ℝ)) := by
  have hpt : ∀ x ∈ Set.Iic (0:ℝ),
      w x * G x ≤ ∑' k : ℕ,
        (Set.Icc (-((k:ℝ) + 1)) (-(k:ℝ))).indicator (fun _ => w (-((k:ℝ) + 1)) * G (-(k:ℝ))) x := by
    intro x hx
    have hx' : x ≤ 0 := hx
    have hneg : (0:ℝ) ≤ -x := by linarith
    have hfl : (⌊-x⌋₊ : ℝ) ≤ -x := Nat.floor_le hneg
    have hxk : x ∈ Set.Icc (-((⌊-x⌋₊ : ℝ) + 1)) (-(⌊-x⌋₊ : ℝ)) := by
      refine ⟨?_, ?_⟩
      · have h := Nat.lt_floor_add_one (-x)
        push_cast at h
        linarith
      · push_cast
        linarith
    have hstep : -((⌊-x⌋₊ : ℝ) + 1) ≤ x := by
      have h := Nat.lt_floor_add_one (-x)
      push_cast at h
      linarith
    have hw1 : w x ≤ w (-((⌊-x⌋₊ : ℝ) + 1)) := hwanti _ x hstep hx'
    have hG1 : G x ≤ G (-(⌊-x⌋₊ : ℝ)) := hmono (by linarith)
    calc w x * G x ≤ w (-((⌊-x⌋₊ : ℝ) + 1)) * G (-(⌊-x⌋₊ : ℝ)) :=
          mul_le_mul hw1 hG1 bot_le bot_le
      _ = (Set.Icc (-((⌊-x⌋₊ : ℝ) + 1)) (-(⌊-x⌋₊ : ℝ))).indicator
            (fun _ => w (-((⌊-x⌋₊ : ℝ) + 1)) * G (-(⌊-x⌋₊ : ℝ))) x :=
          (Set.indicator_of_mem hxk (fun _ => w (-((⌊-x⌋₊ : ℝ) + 1)) * G (-(⌊-x⌋₊ : ℝ)))).symm
      _ ≤ ∑' k : ℕ, (Set.Icc (-((k:ℝ) + 1)) (-(k:ℝ))).indicator
            (fun _ => w (-((k:ℝ) + 1)) * G (-(k:ℝ))) x :=
          ENNReal.le_tsum (f := fun k : ℕ =>
            (Set.Icc (-((k:ℝ) + 1)) (-(k:ℝ))).indicator
              (fun _ => w (-((k:ℝ) + 1)) * G (-(k:ℝ))) x) ⌊-x⌋₊
  have h1 : ∫⁻ x in Set.Iic (0:ℝ), w x * G x
      ≤ ∫⁻ x in Set.Iic (0:ℝ), (fun x => ∑' k : ℕ,
        (Set.Icc (-((k:ℝ) + 1)) (-(k:ℝ))).indicator
          (fun _ => w (-((k:ℝ) + 1)) * G (-(k:ℝ))) x) x := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
    exact hpt x hx
  refine h1.trans ?_
  rw [lintegral_tsum (fun k => (measurable_const.indicator measurableSet_Icc).aemeasurable)]
  refine ENNReal.tsum_le_tsum (fun k => ?_)
  have hterm : ∫⁻ x in Set.Iic (0:ℝ),
      (Set.Icc (-((k:ℝ) + 1)) (-(k:ℝ))).indicator
        (fun _ => w (-((k:ℝ) + 1)) * G (-(k:ℝ))) x
      = ∫⁻ x, (Set.Iic (0:ℝ) ∩ Set.Icc (-((k:ℝ) + 1)) (-(k:ℝ))).indicator
          (fun _ => w (-((k:ℝ) + 1)) * G (-(k:ℝ))) x := by
    rw [← lintegral_indicator measurableSet_Iic]
    congr 1
    funext x
    simp only [Set.indicator, Set.mem_inter_iff]
    by_cases h1 : x ∈ Set.Iic (0:ℝ) <;>
      by_cases h2 : x ∈ Set.Icc (-((k:ℝ) + 1)) (-(k:ℝ)) <;> simp [h1, h2]
  rw [hterm, lintegral_indicator_const (measurableSet_Iic.inter measurableSet_Icc)]
  refine mul_le_of_le_one_right' ?_
  calc (volume : Measure ℝ) (Set.Iic (0:ℝ) ∩ Set.Icc (-((k:ℝ) + 1)) (-(k:ℝ)))
      ≤ volume (Set.Icc (-((k:ℝ) + 1)) (-(k:ℝ))) := measure_mono (Set.inter_subset_right)
    _ = 1 := by
        rw [Real.volume_Icc]
        have : (-(k:ℝ)) - (-((k:ℝ) + 1)) = 1 := by ring
        rw [this, ENNReal.ofReal_one]

/-- **Mirror weighted counting bound**: `∑' k, (k+1)² 1_{t ≤ -k} ≤ (-t+1)³`. -/
theorem tsum_Iic_indicator_sq_le {t : ℝ} (ht : t ≤ 0) :
    (∑' k : ℕ, ((k : ℝ≥0∞) + 1) ^ 2 * (Set.Iic (-(k:ℝ))).indicator (fun _ => (1:ℝ≥0∞)) t)
      ≤ ENNReal.ofReal ((-t + 1) ^ 3) := by
  have hzero : ∀ k : ℕ, ⌊-t⌋₊ + 1 ≤ k →
      ((k : ℝ≥0∞) + 1) ^ 2 * (Set.Iic (-(k:ℝ))).indicator (fun _ => (1:ℝ≥0∞)) t = 0 := by
    intro k hk
    have hkt : ¬ (t ≤ -(k:ℝ)) := by
      have h2 : (⌊-t⌋₊ : ℝ) + 1 ≤ (k:ℝ) := by exact_mod_cast hk
      have h3 := Nat.lt_floor_add_one (-t)
      push_cast at h3
      linarith
    simp only [Set.indicator, Set.mem_Iic, hkt, if_false, mul_zero]
  rw [tsum_eq_sum (s := Finset.range (⌊-t⌋₊ + 1)) (fun k hk => hzero k (by simpa using hk))]
  have hterm : ∀ k ∈ Finset.range (⌊-t⌋₊ + 1),
      ((k : ℝ≥0∞) + 1) ^ 2 * (Set.Iic (-(k:ℝ))).indicator (fun _ => (1:ℝ≥0∞)) t
        ≤ ((⌊-t⌋₊ : ℝ≥0∞) + 1) ^ 2 := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hind : (Set.Iic (-(k:ℝ))).indicator (fun _ => (1:ℝ≥0∞)) t ≤ 1 := by
      by_cases h : t ∈ Set.Iic (-(k:ℝ))
      · rw [Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h]
        exact bot_le
    calc ((k : ℝ≥0∞) + 1) ^ 2 * (Set.Iic (-(k:ℝ))).indicator (fun _ => (1:ℝ≥0∞)) t
        ≤ ((k : ℝ≥0∞) + 1) ^ 2 * 1 := mul_le_mul_right hind _
      _ = ((k : ℝ≥0∞) + 1) ^ 2 := mul_one _
      _ ≤ ((⌊-t⌋₊ : ℝ≥0∞) + 1) ^ 2 := by
          have hk' : (k : ℝ≥0∞) ≤ (⌊-t⌋₊ : ℝ≥0∞) := by exact_mod_cast Nat.le_of_lt_succ hk
          have hk'' : (k : ℝ≥0∞) + 1 ≤ (⌊-t⌋₊ : ℝ≥0∞) + 1 := by
            rw [add_comm (k : ℝ≥0∞) 1, add_comm ((⌊-t⌋₊ : ℝ≥0∞)) 1]
            exact add_le_add_right hk' 1
          exact pow_le_pow_left₀ bot_le hk'' 2
  have hsum : ∑ k ∈ Finset.range (⌊-t⌋₊ + 1),
      ((k : ℝ≥0∞) + 1) ^ 2 * (Set.Iic (-(k:ℝ))).indicator (fun _ => (1:ℝ≥0∞)) t
      ≤ ((⌊-t⌋₊ : ℝ≥0∞) + 1) ^ 3 := by
    calc ∑ k ∈ Finset.range (⌊-t⌋₊ + 1),
          ((k : ℝ≥0∞) + 1) ^ 2 * (Set.Iic (-(k:ℝ))).indicator (fun _ => (1:ℝ≥0∞)) t
        ≤ ∑ _k ∈ Finset.range (⌊-t⌋₊ + 1), ((⌊-t⌋₊ : ℝ≥0∞) + 1) ^ 2 :=
          Finset.sum_le_sum (fun k hk => hterm k hk)
      _ = ((⌊-t⌋₊ + 1 : ℕ) : ℝ≥0∞) * ((⌊-t⌋₊ : ℝ≥0∞) + 1) ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ((⌊-t⌋₊ : ℝ≥0∞) + 1) ^ 3 := by
          rw [Nat.cast_add, Nat.cast_one]
          ring
  refine hsum.trans ?_
  have hcast : ((⌊-t⌋₊ : ℝ≥0∞) + 1) = ENNReal.ofReal ((⌊-t⌋₊ : ℝ) + 1) := by
    rw [ENNReal.ofReal_add (Nat.cast_nonneg _) (by norm_num), ENNReal.ofReal_natCast,
      ENNReal.ofReal_one]
  rw [hcast, ← ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ (⌊-t⌋₊ : ℝ) + 1)]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (⌊-t⌋₊ : ℝ) + 1)
    (by linarith [Nat.floor_le (by linarith : (0:ℝ) ≤ -t)]) 3)

/-- **Mirror `x²`-weighted Tonelli bound**. -/
theorem lintegral_Iic_sq_lintegral_Iic_le {F : ℝ → ℝ≥0∞} (hF : AEMeasurable F volume) :
    ∫⁻ x in Set.Iic (0:ℝ), ENNReal.ofReal (x ^ 2) * (∫⁻ t in Set.Iic x, F t)
      ≤ ∫⁻ t, ENNReal.ofReal ((-t + 1) ^ 3) * F t := by
  have hmono : Monotone fun x : ℝ => ∫⁻ t in Set.Iic x, F t := monotone_lintegral_Iic (F := F)
  have hwanti : ∀ x y : ℝ, x ≤ y → y ≤ 0 → ENNReal.ofReal (y ^ 2) ≤ ENNReal.ofReal (x ^ 2) := by
    intro x y hxy hy
    apply ENNReal.ofReal_le_ofReal
    have h1 : 0 ≤ x ^ 2 := sq_nonneg x
    nlinarith [sq_nonneg x, sq_nonneg y, hy, hxy]
  refine (lintegral_Iic_zero_weighted hmono hwanti).trans ?_
  -- w (-(k+1)) = ofReal ((k+1)^2)
  have hw : ∀ k : ℕ, ENNReal.ofReal ((-((k:ℝ) + 1)) ^ 2) = ENNReal.ofReal (((k:ℝ) + 1) ^ 2) := by
    intro k
    rw [show (-((k:ℝ) + 1)) ^ 2 = ((k:ℝ) + 1) ^ 2 from by ring]
  simp_rw [hw]
  have hind : ∀ k : ℕ, ENNReal.ofReal (((k:ℝ) + 1) ^ 2) * (∫⁻ t in Set.Iic (-(k:ℝ)), F t)
      = ∫⁻ t, ENNReal.ofReal (((k:ℝ) + 1) ^ 2) * (Set.Iic (-(k:ℝ))).indicator F t := by
    intro k
    rw [← lintegral_indicator measurableSet_Iic]
    exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
  simp_rw [hind]
  have hswap : (∑' k : ℕ, ∫⁻ t,
      ENNReal.ofReal (((k:ℝ) + 1) ^ 2) * (Set.Iic (-(k:ℝ))).indicator F t)
      = ∫⁻ t, ∑' k : ℕ,
        ENNReal.ofReal (((k:ℝ) + 1) ^ 2) * (Set.Iic (-(k:ℝ))).indicator F t := by
    rw [lintegral_tsum]
    intro k
    exact AEMeasurable.const_mul (hF.indicator measurableSet_Iic) _
  rw [hswap]
  refine lintegral_mono (fun t => ?_)
  have hpt : ∀ k : ℕ, ENNReal.ofReal (((k:ℝ) + 1) ^ 2) * (Set.Iic (-(k:ℝ))).indicator F t
      = (ENNReal.ofReal (((k:ℝ) + 1) ^ 2)
          * (Set.Iic (-(k:ℝ))).indicator (fun _ => (1:ℝ≥0∞)) t) * F t :=
    fun k => const_mul_indicator_eq _ F _ t
  simp_rw [hpt]
  rw [ENNReal.tsum_mul_right]
  have hcast : ∀ k : ℕ, ENNReal.ofReal (((k:ℝ) + 1) ^ 2) = ((k : ℝ≥0∞) + 1) ^ 2 := by
    intro k
    have h1 : ENNReal.ofReal ((k:ℝ) + 1) = (k : ℝ≥0∞) + 1 := by
      rw [ENNReal.ofReal_add (Nat.cast_nonneg k) (by norm_num), ENNReal.ofReal_natCast,
        ENNReal.ofReal_one]
    rw [ENNReal.ofReal_pow (by positivity), h1]
  have hmain : (∑' k : ℕ, ENNReal.ofReal (((k:ℝ) + 1) ^ 2)
      * (Set.Iic (-(k:ℝ))).indicator (fun _ => (1:ℝ≥0∞)) t)
      ≤ ENNReal.ofReal ((-t + 1) ^ 3) := by
    simp_rw [hcast]
    by_cases ht : t ≤ 0
    · exact tsum_Iic_indicator_sq_le ht
    · push_neg at ht
      have hnil : ∀ k : ℕ, (Set.Iic (-(k:ℝ))).indicator (fun _ => (1:ℝ≥0∞)) t = 0 := by
        intro k
        refine Set.indicator_of_notMem ?_ _
        simp only [Set.mem_Iic, not_le]
        have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
        linarith
      simp only [hnil, mul_zero, tsum_zero]
      exact bot_le
  exact mul_le_mul_left hmain (F t)

/-- Pointwise bound for `x² h² ρ` on the right half-line. -/
theorem ofReal_sq_mul_steinKernel_sq_le_right {g : ℝ → ℝ} (hg : MemLp g 2 (gaussianReal 0 1))
    {x : ℝ} (hx : 0 < x) :
    ENNReal.ofReal (x ^ 2 * ((Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
        gaussianPDFReal 0 1 x))
      ≤ ENNReal.ofReal (max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2))) *
        (ENNReal.ofReal (x ^ 2) * ENNReal.ofReal (∫ t in Set.Ioi x,
          (g t) ^ 2 * gaussianPDFReal 0 1 t)) := by
  have hb := steinKernel_sq_mul_le_right (g := g) hg hx
  have hx2 : (0:ℝ) ≤ x ^ 2 := sq_nonneg x
  have hG0 : (0:ℝ) ≤ ∫ t in Set.Ioi x, (g t) ^ 2 * gaussianPDFReal 0 1 t :=
    setIntegral_nonneg measurableSet_Ioi (fun t _ =>
      mul_nonneg (sq_nonneg _) (gaussianPDFReal_nonneg 0 1 t))
  have hC0 : (0:ℝ) ≤ max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2)) :=
    le_trans zero_le_one (le_max_left _ _)
  have hreal : x ^ 2 * ((Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
        gaussianPDFReal 0 1 x)
      ≤ max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2)) *
        (x ^ 2 * ∫ t in Set.Ioi x, (g t) ^ 2 * gaussianPDFReal 0 1 t) := by
    have h1 : x ^ 2 * ((Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
        gaussianPDFReal 0 1 x)
        ≤ x ^ 2 * (max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2)) *
          ∫ t in Set.Ioi x, (g t) ^ 2 * gaussianPDFReal 0 1 t) :=
      mul_le_mul_of_nonneg_left hb hx2
    calc x ^ 2 * ((Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
          gaussianPDFReal 0 1 x)
        ≤ x ^ 2 * (max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2)) *
            ∫ t in Set.Ioi x, (g t) ^ 2 * gaussianPDFReal 0 1 t) := h1
      _ = max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2)) *
            (x ^ 2 * ∫ t in Set.Ioi x, (g t) ^ 2 * gaussianPDFReal 0 1 t) := by ring
  calc ENNReal.ofReal (x ^ 2 * ((Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
        gaussianPDFReal 0 1 x))
      ≤ ENNReal.ofReal (max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2)) *
          (x ^ 2 * ∫ t in Set.Ioi x, (g t) ^ 2 * gaussianPDFReal 0 1 t)) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2))) *
          (ENNReal.ofReal (x ^ 2) * ENNReal.ofReal (∫ t in Set.Ioi x,
            (g t) ^ 2 * gaussianPDFReal 0 1 t)) := by
        rw [ENNReal.ofReal_mul hC0, ENNReal.ofReal_mul hx2]

/-- Pointwise bound for `x² h² ρ` on the left half-line. -/
theorem ofReal_sq_mul_steinKernel_sq_le_left {g : ℝ → ℝ} (hg : MemLp g 2 (gaussianReal 0 1))
    (hint : IntegrableOn (fun t => g t * gaussianPDFReal 0 1 t) (Set.univ))
    (hzero : ∫ t, g t * gaussianPDFReal 0 1 t = 0) {x : ℝ} (hx : x < 0) :
    ENNReal.ofReal (x ^ 2 * ((Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
        gaussianPDFReal 0 1 x))
      ≤ ENNReal.ofReal (max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2))) *
        (ENNReal.ofReal (x ^ 2) * ENNReal.ofReal (∫ t in Set.Iic x,
          (g t) ^ 2 * gaussianPDFReal 0 1 t)) := by
  have hb := steinKernel_sq_mul_le_left (g := g) hg hint hzero hx
  have hx2 : (0:ℝ) ≤ x ^ 2 := sq_nonneg x
  have hC0 : (0:ℝ) ≤ max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2)) :=
    le_trans zero_le_one (le_max_left _ _)
  have hreal : x ^ 2 * ((Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
        gaussianPDFReal 0 1 x)
      ≤ max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2)) *
        (x ^ 2 * ∫ t in Set.Iic x, (g t) ^ 2 * gaussianPDFReal 0 1 t) := by
    have h1 : x ^ 2 * ((Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
        gaussianPDFReal 0 1 x)
        ≤ x ^ 2 * (max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2)) *
          ∫ t in Set.Iic x, (g t) ^ 2 * gaussianPDFReal 0 1 t) :=
      mul_le_mul_of_nonneg_left hb hx2
    calc x ^ 2 * ((Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
          gaussianPDFReal 0 1 x)
        ≤ x ^ 2 * (max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2)) *
            ∫ t in Set.Iic x, (g t) ^ 2 * gaussianPDFReal 0 1 t) := h1
      _ = max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2)) *
            (x ^ 2 * ∫ t in Set.Iic x, (g t) ^ 2 * gaussianPDFReal 0 1 t) := by ring
  calc ENNReal.ofReal (x ^ 2 * ((Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
        gaussianPDFReal 0 1 x))
      ≤ ENNReal.ofReal (max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2)) *
          (x ^ 2 * ∫ t in Set.Iic x, (g t) ^ 2 * gaussianPDFReal 0 1 t)) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2))) *
          (ENNReal.ofReal (x ^ 2) * ENNReal.ofReal (∫ t in Set.Iic x,
            (g t) ^ 2 * gaussianPDFReal 0 1 t)) := by
        rw [ENNReal.ofReal_mul hC0, ENNReal.ofReal_mul hx2]

/-- Right half of the `x² h² ρ` finiteness bound. -/
theorem lintegral_sq_mul_steinKernel_sq_right_le {g : ℝ → ℝ} (hg : MemLp g 2 (gaussianReal 0 1))
    (hgm : Measurable g)
    (hint2 : ∀ x : ℝ, IntegrableOn (fun t => (g t) ^ 2 * gaussianPDFReal 0 1 t) (Set.Ioi x))
    (hFmeas : AEMeasurable (fun t => ENNReal.ofReal ((g t) ^ 2 * gaussianPDFReal 0 1 t)) volume) :
    ∫⁻ x in Set.Ioi (0:ℝ),
        ENNReal.ofReal (x ^ 2 * ((Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
          gaussianPDFReal 0 1 x))
      ≤ ENNReal.ofReal (max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2))) *
        ∫⁻ t, ENNReal.ofReal ((t + 1) ^ 3)
          * ENNReal.ofReal ((g t) ^ 2 * gaussianPDFReal 0 1 t) := by
  set F : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal ((g t) ^ 2 * gaussianPDFReal 0 1 t) with hFdef
  have hnn : ∀ t : ℝ, (0:ℝ) ≤ (g t) ^ 2 * gaussianPDFReal 0 1 t :=
    fun t => mul_nonneg (sq_nonneg _) (gaussianPDFReal_nonneg 0 1 t)
  have hpt : ∀ x ∈ Set.Ioi (0:ℝ),
      ENNReal.ofReal (x ^ 2 * ((Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
        gaussianPDFReal 0 1 x))
      ≤ ENNReal.ofReal (max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2))) *
        (ENNReal.ofReal (x ^ 2) * ∫⁻ t in Set.Ioi x, F t) := by
    intro x hx
    have hb := ofReal_sq_mul_steinKernel_sq_le_right (g := g) hg hx
    rw [ofReal_setIntegral_eq_lintegral' (hint2 x) hnn] at hb
    exact hb
  have h1 : ∫⁻ x in Set.Ioi (0:ℝ),
      ENNReal.ofReal (x ^ 2 * ((Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
        gaussianPDFReal 0 1 x))
      ≤ ∫⁻ x in Set.Ioi (0:ℝ), ENNReal.ofReal (max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2))) *
        (ENNReal.ofReal (x ^ 2) * ∫⁻ t in Set.Ioi x, F t) := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hpt x hx
  refine h1.trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hmeas : AEMeasurable F volume := hFmeas
  have hton := lintegral_Ioi_sq_lintegral_Ioi_le (F := F) hmeas
  exact mul_le_mul_right hton
    (ENNReal.ofReal (max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2))))

/-- Left half of the `x² h² ρ` finiteness bound. -/
theorem lintegral_sq_mul_steinKernel_sq_left_le {g : ℝ → ℝ} (hg : MemLp g 2 (gaussianReal 0 1))
    (hint : IntegrableOn (fun t => g t * gaussianPDFReal 0 1 t) (Set.univ))
    (hzero : ∫ t, g t * gaussianPDFReal 0 1 t = 0)
    (hint2 : ∀ x : ℝ, IntegrableOn (fun t => (g t) ^ 2 * gaussianPDFReal 0 1 t) (Set.Iic x))
    (hFmeas : AEMeasurable (fun t => ENNReal.ofReal ((g t) ^ 2 * gaussianPDFReal 0 1 t)) volume) :
    ∫⁻ x in Set.Iio (0:ℝ),
        ENNReal.ofReal (x ^ 2 * ((Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
          gaussianPDFReal 0 1 x))
      ≤ ENNReal.ofReal (max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2))) *
        ∫⁻ t, ENNReal.ofReal ((-t + 1) ^ 3)
          * ENNReal.ofReal ((g t) ^ 2 * gaussianPDFReal 0 1 t) := by
  set F : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal ((g t) ^ 2 * gaussianPDFReal 0 1 t) with hFdef
  have hnn : ∀ t : ℝ, (0:ℝ) ≤ (g t) ^ 2 * gaussianPDFReal 0 1 t :=
    fun t => mul_nonneg (sq_nonneg _) (gaussianPDFReal_nonneg 0 1 t)
  have hpt : ∀ x ∈ Set.Iio (0:ℝ),
      ENNReal.ofReal (x ^ 2 * ((Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
        gaussianPDFReal 0 1 x))
      ≤ ENNReal.ofReal (max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2))) *
        (ENNReal.ofReal (x ^ 2) * ∫⁻ t in Set.Iic x, F t) := by
    intro x hx
    have hx' : x < 0 := hx
    have hb := ofReal_sq_mul_steinKernel_sq_le_left (g := g) hg hint hzero hx'
    rw [ofReal_setIntegral_eq_lintegral' (hint2 x) hnn] at hb
    exact hb
  have h1 : ∫⁻ x in Set.Iio (0:ℝ),
      ENNReal.ofReal (x ^ 2 * ((Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
        gaussianPDFReal 0 1 x))
      ≤ ∫⁻ x in Set.Iio (0:ℝ), ENNReal.ofReal (max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2))) *
        (ENNReal.ofReal (x ^ 2) * ∫⁻ t in Set.Iic x, F t) := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
    exact hpt x hx
  have h2 : ∫⁻ x in Set.Iio (0:ℝ), ENNReal.ofReal (max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2))) *
        (ENNReal.ofReal (x ^ 2) * ∫⁻ t in Set.Iic x, F t)
      ≤ ∫⁻ x in Set.Iic (0:ℝ), ENNReal.ofReal (max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2))) *
        (ENNReal.ofReal (x ^ 2) * ∫⁻ t in Set.Iic x, F t) :=
    lintegral_mono_set (Set.Iio_subset_Iic (le_refl (0:ℝ)))
  refine (h1.trans h2).trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hton := lintegral_Iic_sq_lintegral_Iic_le (F := F) hFmeas
  exact mul_le_mul_right hton
    (ENNReal.ofReal (max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2))))

/-- `(t+1)³ ≤ (|t|+1)³` and `(-t+1)³ ≤ (|t|+1)³` in the ofReal sense. -/
theorem ofReal_cube_add_one_le (t : ℝ) :
    ENNReal.ofReal ((t + 1) ^ 3) ≤ ENNReal.ofReal ((|t| + 1) ^ 3) := by
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : t + 1 ≤ |t| + 1 := by
    nlinarith [le_abs_self t]
  have h0 : (0:ℝ) ≤ |t| + 1 := by positivity
  rcases le_or_gt 0 (t + 1) with h | h
  · exact pow_le_pow_left₀ h h1 3
  · have hneg : (t + 1) ^ 3 ≤ 0 := by
      rw [show (t + 1) ^ 3 = (t + 1) * (t + 1) ^ 2 by ring]
      exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt h) (sq_nonneg _)
    have hpos : (0:ℝ) ≤ (|t| + 1) ^ 3 := by positivity
    linarith

/-- `ofReal ((-t+1)³) ≤ ofReal ((|t|+1)³)`. -/
theorem ofReal_cube_neg_add_one_le (t : ℝ) :
    ENNReal.ofReal ((-t + 1) ^ 3) ≤ ENNReal.ofReal ((|t| + 1) ^ 3) := by
  have h := ofReal_cube_add_one_le (-t)
  rwa [abs_neg] at h

/-- **Finiteness of `∫⁻ x² h² ρ`** (both half-lines combined). -/
theorem lintegral_sq_mul_steinKernel_sq_le {g : ℝ → ℝ} (hg : MemLp g 2 (gaussianReal 0 1))
    (hgm : Measurable g)
    (hint : IntegrableOn (fun t => g t * gaussianPDFReal 0 1 t) (Set.univ))
    (hzero : ∫ t, g t * gaussianPDFReal 0 1 t = 0)
    (hintR : ∀ x : ℝ, IntegrableOn (fun t => (g t) ^ 2 * gaussianPDFReal 0 1 t) (Set.Ioi x))
    (hintL : ∀ x : ℝ, IntegrableOn (fun t => (g t) ^ 2 * gaussianPDFReal 0 1 t) (Set.Iic x))
    (hFmeas : AEMeasurable (fun t => ENNReal.ofReal ((g t) ^ 2 * gaussianPDFReal 0 1 t)) volume) :
    ∫⁻ x, ENNReal.ofReal (x ^ 2 * ((Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
        gaussianPDFReal 0 1 x))
      ≤ 2 * ENNReal.ofReal (max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2))) *
        ∫⁻ t, ENNReal.ofReal ((|t| + 1) ^ 3)
          * ENNReal.ofReal ((g t) ^ 2 * gaussianPDFReal 0 1 t) := by
  set F : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal ((g t) ^ 2 * gaussianPDFReal 0 1 t) with hFdef
  set Ff : ℝ → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (x ^ 2 * ((Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
      gaussianPDFReal 0 1 x)) with hFfdef
  have hR := lintegral_sq_mul_steinKernel_sq_right_le (g := g) hg hgm hintR hFmeas
  have hL := lintegral_sq_mul_steinKernel_sq_left_le (g := g) hg hint hzero hintL hFmeas
  -- unify the weights
  have hwR : ∫⁻ t, ENNReal.ofReal ((t + 1) ^ 3) * F t
      ≤ ∫⁻ t, ENNReal.ofReal ((|t| + 1) ^ 3) * F t := by
    refine lintegral_mono (fun t => ?_)
    exact mul_le_mul_left (ofReal_cube_add_one_le t) (F t)
  have hwL : ∫⁻ t, ENNReal.ofReal ((-t + 1) ^ 3) * F t
      ≤ ∫⁻ t, ENNReal.ofReal ((|t| + 1) ^ 3) * F t := by
    refine lintegral_mono (fun t => ?_)
    exact mul_le_mul_left (ofReal_cube_neg_add_one_le t) (F t)
  have hsplit : ∫⁻ x, Ff x = (∫⁻ x in Set.Iio (0:ℝ), Ff x) + (∫⁻ x in Set.Ici (0:ℝ), Ff x) := by
    have h := lintegral_add_compl (μ := volume) Ff (measurableSet_Ici (a := (0:ℝ)))
    rw [Set.compl_Ici] at h
    simpa [add_comm] using h.symm
  have hpt0 : ∫⁻ x in Set.Ici (0:ℝ), Ff x = ∫⁻ x in Set.Ioi (0:ℝ), Ff x := by
    have hsub : Set.Ioi (0:ℝ) ⊆ Set.Ici (0:ℝ) := Set.Ioi_subset_Ici_self
    have hae : Set.Ici (0:ℝ) =ᵐ[volume] Set.Ioi (0:ℝ) := by
      refine ae_eq_set.mpr ⟨?_, ?_⟩
      · have hset : Set.Ici (0:ℝ) \ Set.Ioi (0:ℝ) = {(0:ℝ)} := by
          ext x
          simp only [Set.mem_diff, Set.mem_Ici, Set.mem_Ioi, Set.mem_singleton_iff]
          constructor
          · rintro ⟨h1, h2⟩
            push_neg at h2
            linarith
          · rintro rfl
            exact ⟨le_refl 0, by norm_num⟩
        rw [hset]
        simp
      · rw [Set.sdiff_eq_empty.mpr hsub]
        simp
    rw [Measure.restrict_congr_set hae]
  rw [hsplit, hpt0]
  have hstep : (∫⁻ x in Set.Iio (0:ℝ), Ff x) + (∫⁻ x in Set.Ioi (0:ℝ), Ff x)
      ≤ (ENNReal.ofReal (max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2))) *
          ∫⁻ t, ENNReal.ofReal ((|t| + 1) ^ 3) * F t) +
        (ENNReal.ofReal (max 1 (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2))) *
          ∫⁻ t, ENNReal.ofReal ((|t| + 1) ^ 3) * F t) :=
    add_le_add (hL.trans (mul_le_mul_right hwL _)) (hR.trans (mul_le_mul_right hwR _))
  refine hstep.trans_eq ?_
  ring

/-- **Integrability of `x² h² ρ`**. -/
theorem integrable_sq_mul_steinKernel_sq {g : ℝ → ℝ} (hg : MemLp g 2 (gaussianReal 0 1))
    (hgm : Measurable g)
    (hint : IntegrableOn (fun t => g t * gaussianPDFReal 0 1 t) (Set.univ))
    (hzero : ∫ t, g t * gaussianPDFReal 0 1 t = 0)
    (hintR : ∀ x : ℝ, IntegrableOn (fun t => (g t) ^ 2 * gaussianPDFReal 0 1 t) (Set.Ioi x))
    (hintL : ∀ x : ℝ, IntegrableOn (fun t => (g t) ^ 2 * gaussianPDFReal 0 1 t) (Set.Iic x))
    (hFmeas : AEMeasurable (fun t => ENNReal.ofReal ((g t) ^ 2 * gaussianPDFReal 0 1 t)) volume)
    (hW : Integrable (fun t => (|t| + 1) ^ 3 * ((g t) ^ 2 * gaussianPDFReal 0 1 t))) :
    Integrable (fun x => x ^ 2 * ((Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
      gaussianPDFReal 0 1 x)) := by
  have hb := lintegral_sq_mul_steinKernel_sq_le (g := g) hg hgm hint hzero hintR hintL hFmeas
  have hWfin : ∫⁻ t, ENNReal.ofReal ((|t| + 1) ^ 3) * ENNReal.ofReal ((g t) ^ 2 * gaussianPDFReal 0 1 t)
      < ⊤ := by
    have hsplit_eq : (∫⁻ t, ENNReal.ofReal ((|t| + 1) ^ 3)
        * ENNReal.ofReal ((g t) ^ 2 * gaussianPDFReal 0 1 t))
        = ∫⁻ t, ENNReal.ofReal ((|t| + 1) ^ 3 * ((g t) ^ 2 * gaussianPDFReal 0 1 t)) := by
      refine lintegral_congr_ae (ae_of_all _ (fun t => ?_))
      exact (ENNReal.ofReal_mul (by positivity)).symm
    rw [hsplit_eq, ← hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun t =>
      mul_nonneg (by positivity) (mul_nonneg (sq_nonneg _) (gaussianPDFReal_nonneg 0 1 t))))]
    exact hW.2
  have hlt : ∫⁻ x, ENNReal.ofReal (x ^ 2 *
      ((Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
      gaussianPDFReal 0 1 x)) < ⊤ :=
    lt_of_le_of_lt hb (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) hWfin.ne))
  refine ⟨?_, ?_⟩
  · have hT := aestronglyMeasurable_gueTail hgm
    have h1 : AEStronglyMeasurable
        (fun x : ℝ => Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) volume :=
      (by fun_prop : AEStronglyMeasurable
        (fun x : ℝ => Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2)) volume).mul hT
    have h2 := h1.pow 2
    have h3 : AEStronglyMeasurable (fun x : ℝ => gaussianPDFReal 0 1 x) volume := by fun_prop
    have h4 := (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x ^ 2) volume).mul (h2.mul h3)
    refine h4.congr ?_
    filter_upwards with x
    simp only [Pi.mul_apply, Pi.pow_apply]
  · rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun x =>
      mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (gaussianPDFReal_nonneg 0 1 x))))]
    exact hlt

/-- `g² ρ` is integrable for `g ∈ L²(γ)`. -/
theorem integrable_sq_mul_gaussianPDFReal_of_memLp {g : ℝ → ℝ} (hg : MemLp g 2 (gaussianReal 0 1))
    (hgm : Measurable g) :
    Integrable (fun t => (g t) ^ 2 * gaussianPDFReal 0 1 t) := by
  have h1 : Integrable (fun t => (g t) ^ 2) (gaussianReal 0 1) :=
    (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).mp hg
  have hd : gaussianReal 0 1 = volume.withDensity (gaussianPDF 0 1) :=
    gaussianReal_of_var_ne_zero 0 (by norm_num : (1:ℝ≥0) ≠ 0)
  rw [hd] at h1
  rw [integrable_withDensity_iff (measurable_gaussianPDF (μ := 0) (v := 1))
    (by filter_upwards with t using gaussianPDF_lt_top (μ := 0) (v := 1) (x := t))] at h1
  refine h1.congr (ae_of_all _ (fun x => ?_))
  simp only [toReal_gaussianPDF]

/-- **Integrability of `h'² ρ`** (`hsq`), by domination with `2g²ρ + 2x²h²ρ`. -/
theorem integrable_steinKernel_deriv_sq {g : ℝ → ℝ} (hgm : Measurable g)
    (hmeas : AEStronglyMeasurable (fun x : ℝ => (g x + x * (-Real.sqrt (2 * Real.pi) *
      Real.exp (x ^ 2 / 2) * gueTail g x)) ^ 2 * gaussianPDFReal 0 1 x) volume)
    (hx2 : Integrable (fun x => x ^ 2 * ((Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
      gaussianPDFReal 0 1 x)))
    (hg2 : Integrable (fun x => (g x) ^ 2 * gaussianPDFReal 0 1 x)) :
    Integrable (fun x => (g x + x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
      gueTail g x)) ^ 2 * gaussianPDFReal 0 1 x) := by
  have hmaj : Integrable (fun x => 2 * ((g x) ^ 2 * gaussianPDFReal 0 1 x)
      + 2 * (x ^ 2 * ((Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
          gaussianPDFReal 0 1 x))) :=
    (hg2.const_mul 2).add (hx2.const_mul 2)
  refine hmaj.mono' hmeas ?_
  · filter_upwards with x
    have hρ := gaussianPDFReal_nonneg 0 1 x
    have hsquare : (g x + x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x)) ^ 2
        ≤ 2 * (g x) ^ 2 + 2 * (x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x)) ^ 2 := by
      nlinarith [sq_nonneg (g x - x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x)),
        sq_nonneg (g x + x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x))]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc (g x + x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x)) ^ 2 *
          gaussianPDFReal 0 1 x
        ≤ (2 * (g x) ^ 2 + 2 * (x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x)) ^ 2) *
            gaussianPDFReal 0 1 x := by
          exact mul_le_mul_of_nonneg_right hsquare hρ
      _ = 2 * ((g x) ^ 2 * gaussianPDFReal 0 1 x)
            + 2 * (x ^ 2 * ((Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
                gaussianPDFReal 0 1 x)) := by ring

/-- **Integrability of `x h h' ρ`** (the `hcross` hypothesis). -/
theorem integrable_steinKernel_cross {g : ℝ → ℝ}
    (hmeas : AEStronglyMeasurable (fun x : ℝ => x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
      gueTail g x) * (g x + x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x)) *
      gaussianPDFReal 0 1 x) volume)
    (hxhg : Integrable (fun x => x * (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) *
      g x * gaussianPDFReal 0 1 x))
    (hx2 : Integrable (fun x => x ^ 2 * ((Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
      gaussianPDFReal 0 1 x))) :
    Integrable (fun x => x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) *
      (g x + x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x)) *
      gaussianPDFReal 0 1 x) := by
  have hmaj : Integrable (fun x => |x * (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) *
      g x * gaussianPDFReal 0 1 x| + x ^ 2 * ((Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
      gueTail g x) ^ 2 * gaussianPDFReal 0 1 x)) :=
    hxhg.norm.add hx2
  refine hmaj.mono' hmeas ?_
  · filter_upwards with x
    rw [Real.norm_eq_abs]
    have hsplit : x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) *
          (g x + x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x)) *
          gaussianPDFReal 0 1 x
        = -(x * (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) * g x *
              gaussianPDFReal 0 1 x)
          + x ^ 2 * ((Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
              gaussianPDFReal 0 1 x) := by ring
    rw [hsplit]
    have h2 : (0:ℝ) ≤ x ^ 2 * ((Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
        gaussianPDFReal 0 1 x) :=
      mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (gaussianPDFReal_nonneg 0 1 x))
    have h3 := abs_add_le (-(x * (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) * g x *
        gaussianPDFReal 0 1 x))
      (x ^ 2 * ((Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
        gaussianPDFReal 0 1 x))
    rw [abs_neg, abs_of_nonneg h2] at h3
    exact h3

/-- `∫ t in Ioi x, t * ρ t = ρ x`. -/
theorem integral_Ioi_id_mul_gaussianPDFReal (x : ℝ) :
    ∫ t in Set.Ioi x, t * gaussianPDFReal 0 1 t = gaussianPDFReal 0 1 x := by
  have h := integral_Ioi_exp_neg_sq_div_two_mul x
  have hpt : ∀ t : ℝ, t * gaussianPDFReal 0 1 t
      = (Real.sqrt (2 * Real.pi))⁻¹ * (Real.exp (-(t ^ 2 / 2)) * t) := by
    intro t
    rw [gaussianPDFReal]
    have h1 : ((2:ℝ) * Real.pi * ((1:ℝ≥0):ℝ)) = 2 * Real.pi := by push_cast; ring
    have h2 : (-(t - 0) ^ 2 / (2 * ((1:ℝ≥0):ℝ))) = (-(t ^ 2 / 2)) := by push_cast; ring
    rw [h1, h2]
    ring
  calc ∫ t in Set.Ioi x, t * gaussianPDFReal 0 1 t
      = ∫ t in Set.Ioi x, (Real.sqrt (2 * Real.pi))⁻¹ * (Real.exp (-(t ^ 2 / 2)) * t) := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => hpt t)
    _ = (Real.sqrt (2 * Real.pi))⁻¹ * ∫ t in Set.Ioi x, (Real.exp (-(t ^ 2 / 2)) * t) := by
        rw [integral_const_mul]
    _ = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2 / 2)) := by rw [h]
    _ = gaussianPDFReal 0 1 x := by
        rw [gaussianPDFReal]
        have h1 : ((2:ℝ) * Real.pi * ((1:ℝ≥0):ℝ)) = 2 * Real.pi := by push_cast; ring
        have h2 : (-(x - 0) ^ 2 / (2 * ((1:ℝ≥0):ℝ))) = (-(x ^ 2 / 2)) := by push_cast; ring
        rw [h1, h2]

/-- **Decay of `h² x ρ` at `+∞`.** -/
theorem tendsto_steinKernel_sq_mul_id_atTop {g : ℝ → ℝ} (hg : MemLp g 2 (gaussianReal 0 1)) :
    Tendsto (fun x => (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
      (x * gaussianPDFReal 0 1 x)) atTop (𝓝 0) := by
  have hG : Tendsto (fun x => ∫ t in Set.Ioi x, (g t) ^ 2 * gaussianPDFReal 0 1 t) atTop (𝓝 0) :=
    tendsto_integral_Ioi_id_zero _
  refine squeeze_zero_norm' ?_ hG
  filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _)
    (mul_nonneg (le_of_lt hx0) (gaussianPDFReal_nonneg 0 1 x)))]
  -- weight bound: √(2π) e^{x²/2} x · (tail mass of ρ) ≤ 1
  have hw : Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * x *
      (∫ t in Set.Ioi x, gaussianPDFReal 0 1 t) ≤ 1 := by
    have h1 := weight_tail_Ioi_le hx0
    have h2 : Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * x *
        (∫ t in Set.Ioi x, gaussianPDFReal 0 1 t)
        = x * (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
            (∫ t in Set.Ioi x, gaussianPDFReal 0 1 t)) := by ring
    rw [h2]
    have h3 : x * (1 / x) = 1 := by field_simp
    calc x * (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
          (∫ t in Set.Ioi x, gaussianPDFReal 0 1 t))
        ≤ x * (1 / x) := by
          exact mul_le_mul_of_nonneg_left h1 (le_of_lt hx0)
      _ = 1 := h3
  have hT := sq_integral_Ioi_mul_gaussianPDFReal_le (g := g) (x := x) hg
  have hmass0 : (0:ℝ) ≤ ∫ t in Set.Ioi x, gaussianPDFReal 0 1 t :=
    setIntegral_nonneg measurableSet_Ioi (fun t _ => gaussianPDFReal_nonneg 0 1 t)
  have hG0 : (0:ℝ) ≤ ∫ t in Set.Ioi x, (g t) ^ 2 * gaussianPDFReal 0 1 t :=
    setIntegral_nonneg measurableSet_Ioi (fun t _ =>
      mul_nonneg (sq_nonneg _) (gaussianPDFReal_nonneg 0 1 t))
  have hkey : (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
      (x * gaussianPDFReal 0 1 x)
      ≤ Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * x *
          ((∫ t in Set.Ioi x, gaussianPDFReal 0 1 t) *
            ∫ t in Set.Ioi x, (g t) ^ 2 * gaussianPDFReal 0 1 t) := by
    have hnorm : Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gaussianPDFReal 0 1 x = 1 :=
      sqrt_two_pi_mul_exp_mul_gaussianPDFReal x
    have hsq : (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
        (x * gaussianPDFReal 0 1 x)
        = x * (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2)) * (gueTail g x) ^ 2 := by
      have h1 : Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gaussianPDFReal 0 1 x = 1 := hnorm
      linear_combination (x * (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2)) *
        (gueTail g x) ^ 2) * h1
    rw [hsq]
    calc x * (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2)) * (gueTail g x) ^ 2
        ≤ x * (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2)) *
            ((∫ t in Set.Ioi x, gaussianPDFReal 0 1 t) *
              ∫ t in Set.Ioi x, (g t) ^ 2 * gaussianPDFReal 0 1 t) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          simpa [gueTail] using hT
      _ = Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * x *
            ((∫ t in Set.Ioi x, gaussianPDFReal 0 1 t) *
              ∫ t in Set.Ioi x, (g t) ^ 2 * gaussianPDFReal 0 1 t) := by ring
  refine hkey.trans ?_
  calc Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * x *
        ((∫ t in Set.Ioi x, gaussianPDFReal 0 1 t) *
          ∫ t in Set.Ioi x, (g t) ^ 2 * gaussianPDFReal 0 1 t)
      = (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * x *
          (∫ t in Set.Ioi x, gaussianPDFReal 0 1 t)) *
          ∫ t in Set.Ioi x, (g t) ^ 2 * gaussianPDFReal 0 1 t := by ring
    _ ≤ 1 * ∫ t in Set.Ioi x, (g t) ^ 2 * gaussianPDFReal 0 1 t :=
        mul_le_mul_of_nonneg_right hw hG0
    _ = ∫ t in Set.Ioi x, (g t) ^ 2 * gaussianPDFReal 0 1 t := one_mul _

/-- **Decay of `h² x ρ` at `-∞`** (no-abs route). -/
theorem tendsto_steinKernel_sq_mul_id_atBot {g : ℝ → ℝ} (hg : MemLp g 2 (gaussianReal 0 1))
    (hint : IntegrableOn (fun t => g t * gaussianPDFReal 0 1 t) (Set.univ))
    (hzero : ∫ t, g t * gaussianPDFReal 0 1 t = 0) :
    Tendsto (fun x => (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
      (x * gaussianPDFReal 0 1 x)) atBot (𝓝 0) := by
  have hG : Tendsto (fun x => ∫ t in Set.Iic x, (g t) ^ 2 * gaussianPDFReal 0 1 t) atBot (𝓝 0) := by
    have h := MeasureTheory.tendsto_integral_Iic_zero (μ := volume)
      (f := fun t => (g t) ^ 2 * gaussianPDFReal 0 1 t) (l := atBot)
      (a := fun x : ℝ => x) tendsto_id
    simpa using h
  refine squeeze_zero_norm' ?_ hG
  filter_upwards [eventually_le_atBot (-1:ℝ)] with x hx
  have hx0 : x < 0 := lt_of_le_of_lt hx (by norm_num)
  have hT : ∫ t in Set.Ioi x, g t * gaussianPDFReal 0 1 t
      = -∫ t in Set.Iic x, g t * gaussianPDFReal 0 1 t :=
    integral_Ioi_mul_eq_neg_integral_Iic_mul (x := x) hint hzero
  rw [Real.norm_eq_abs]
  show |(Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * (∫ t in Set.Ioi x, g t * gaussianPDFReal 0 1 t)) ^ 2 *
    (x * gaussianPDFReal 0 1 x)| ≤ _
  -- the expression equals -(√e·(-x)·T²) with T = ∫_{t<x} g ρ
  set Tt : ℝ := ∫ t in Set.Iic x, g t * gaussianPDFReal 0 1 t with hTt
  have hval : (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * (∫ t in Set.Ioi x, g t * gaussianPDFReal 0 1 t)) ^ 2 *
      (x * gaussianPDFReal 0 1 x)
      = -(Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * (-x) * Tt ^ 2) := by
    rw [hT]
    have hnorm : Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gaussianPDFReal 0 1 x = 1 :=
      sqrt_two_pi_mul_exp_mul_gaussianPDFReal x
    have hfac : (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * -Tt) ^ 2 *
          (x * gaussianPDFReal 0 1 x)
        = (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * x) *
          (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gaussianPDFReal 0 1 x) * Tt ^ 2 := by ring
    rw [hfac, hnorm]
    ring
  rw [hval, abs_neg, abs_of_nonneg (mul_nonneg (mul_nonneg (by positivity) (by linarith))
    (sq_nonneg _))]
  -- bound -h²xρ = √e(-x)T² by the tail mass of g² ρ
  have hT2 : Tt ^ 2 ≤ (∫ t in Set.Iic x, gaussianPDFReal 0 1 t) *
      ∫ t in Set.Iic x, (g t) ^ 2 * gaussianPDFReal 0 1 t := by
    have h := sq_integral_Ioi_mul_gaussianPDFReal_le_left (g := g) hg hint hzero (x := x)
    have hT' : ∫ t in Set.Ioi x, g t * gaussianPDFReal 0 1 t = -Tt := hT
    rw [hT'] at h
    have hsq : (-Tt) ^ 2 = Tt ^ 2 := by ring
    rwa [hsq] at h
  have hw : Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * (-x) *
      (∫ t in Set.Iic x, gaussianPDFReal 0 1 t) ≤ 1 := by
    have h1 := weight_tail_Iic_le hx0
    have h2 : Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * (-x) *
        (∫ t in Set.Iic x, gaussianPDFReal 0 1 t)
        = (-x) * (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
            (∫ t in Set.Iic x, gaussianPDFReal 0 1 t)) := by ring
    rw [h2]
    calc (-x) * (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
          (∫ t in Set.Iic x, gaussianPDFReal 0 1 t))
        ≤ (-x) * (1 / (-x)) := by
          apply mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = 1 := by
          rw [one_div]
          exact mul_inv_cancel₀ (by linarith)
  have hG0 : (0:ℝ) ≤ ∫ t in Set.Iic x, (g t) ^ 2 * gaussianPDFReal 0 1 t :=
    setIntegral_nonneg measurableSet_Iic (fun t _ =>
      mul_nonneg (sq_nonneg _) (gaussianPDFReal_nonneg 0 1 t))
  calc Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * (-x) * Tt ^ 2
      ≤ Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * (-x) *
          ((∫ t in Set.Iic x, gaussianPDFReal 0 1 t) *
            ∫ t in Set.Iic x, (g t) ^ 2 * gaussianPDFReal 0 1 t) :=
        mul_le_mul_of_nonneg_left hT2 (mul_nonneg (mul_nonneg
          (Real.sqrt_pos.mpr (by positivity)).le (Real.exp_pos _).le) (by linarith))
    _ = (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * (-x) *
          (∫ t in Set.Iic x, gaussianPDFReal 0 1 t)) *
          ∫ t in Set.Iic x, (g t) ^ 2 * gaussianPDFReal 0 1 t := by ring
    _ ≤ 1 * ∫ t in Set.Iic x, (g t) ^ 2 * gaussianPDFReal 0 1 t :=
        mul_le_mul_of_nonneg_right hw hG0
    _ = ∫ t in Set.Iic x, (g t) ^ 2 * gaussianPDFReal 0 1 t := one_mul _

/-- `(1+|t|)^k ρ t → 0` at `+∞`. -/
theorem tendsto_one_add_abs_pow_mul_gaussianPDFReal (k : ℕ) :
    Tendsto (fun x : ℝ => (1 + |x|) ^ k * gaussianPDFReal 0 1 x) atTop (𝓝 0) := by
  have hρ : Tendsto (fun x : ℝ => gaussianPDFReal 0 1 x * x ^ k) atTop (𝓝 0) :=
    tendsto_gaussianPDFReal_mul_pow_atTop k
  have h1 : Tendsto (fun x : ℝ => gaussianPDFReal 0 1 x * |x| ^ k) atTop (𝓝 0) := by
    have h2 : (fun x : ℝ => |gaussianPDFReal 0 1 x * x ^ k|)
        = fun x => gaussianPDFReal 0 1 x * |x| ^ k := by
      funext x
      rw [abs_mul, abs_of_nonneg (gaussianPDFReal_nonneg 0 1 x), abs_pow]
    rw [← h2]
    simpa using hρ.abs
  have hmaj : Tendsto (fun x : ℝ => 2 ^ k * ((gaussianPDFReal 0 1 x * |x| ^ k) +
      gaussianPDFReal 0 1 x)) atTop (𝓝 0) := by
    have hρz : Tendsto (fun x : ℝ => gaussianPDFReal 0 1 x) atTop (𝓝 0) := by
      have := tendsto_gaussianPDFReal_mul_pow_atTop 0
      simpa using this
    have hsum : Tendsto (fun x : ℝ => gaussianPDFReal 0 1 x * |x| ^ k + gaussianPDFReal 0 1 x)
        atTop (𝓝 0) := by
      have := h1.add hρz
      simpa using this
    have := hsum.const_mul (2 ^ k)
    simpa using this
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (gaussianPDFReal_nonneg 0 1 x))]
  have hb : (1 + |x|) ^ k ≤ 2 ^ k * (1 + |x| ^ k) := one_add_pow_le_two_pow_mul |x| (abs_nonneg x) k
  have hρ0 : (0:ℝ) ≤ gaussianPDFReal 0 1 x := gaussianPDFReal_nonneg 0 1 x
  nlinarith [hb, hρ0, mul_nonneg (by positivity : (0:ℝ) ≤ gaussianPDFReal 0 1 x) (by positivity : (0:ℝ) ≤ 1 + |x| ^ k)]

/-- Dominated convergence helper: a nonnegative function dominated by a polynomial multiple of `ρ`. -/
theorem tendsto_abs_sq_mul_gaussianPDFReal_div_atTop {g : ℝ → ℝ}
    (hgr : ∃ C : ℝ, 0 ≤ C ∧ ∃ k : ℕ, ∀ x, |g x| ≤ C * (1 + |x|) ^ k) :
    Tendsto (fun x : ℝ => (g x) ^ 2 * gaussianPDFReal 0 1 x / x) atTop (𝓝 0) := by
  obtain ⟨C, hC0, k, hC⟩ := hgr
  have hmaj : Tendsto (fun x : ℝ => C ^ 2 * ((1 + |x|) ^ (2 * k) * gaussianPDFReal 0 1 x))
      atTop (𝓝 0) := by
    have h := (tendsto_one_add_abs_pow_mul_gaussianPDFReal (2 * k)).const_mul (C ^ 2)
    simpa using h
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
  have hx0 : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hρ0 : (0:ℝ) ≤ gaussianPDFReal 0 1 x := gaussianPDFReal_nonneg 0 1 x
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mul_nonneg (sq_nonneg _) hρ0) hx0.le)]
  have h1 : (g x) ^ 2 ≤ C ^ 2 * (1 + |x|) ^ (2 * k) := by
    have h3 := pow_le_pow_left₀ (abs_nonneg (g x)) (hC x) 2
    have h4 : (C * (1 + |x|) ^ k) ^ 2 = C ^ 2 * (1 + |x|) ^ (2 * k) := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm k 2]
    rw [h4] at h3
    have h2 : (g x) ^ 2 = |g x| ^ 2 := (sq_abs (g x)).symm
    rw [h2]
    exact h3
  rw [div_le_iff₀ hx0]
  calc (g x) ^ 2 * gaussianPDFReal 0 1 x
      ≤ C ^ 2 * (1 + |x|) ^ (2 * k) * gaussianPDFReal 0 1 x :=
        mul_le_mul_of_nonneg_right h1 hρ0
    _ = C ^ 2 * ((1 + |x|) ^ (2 * k) * gaussianPDFReal 0 1 x) := by ring
    _ ≤ C ^ 2 * ((1 + |x|) ^ (2 * k) * gaussianPDFReal 0 1 x) * x := by
        have hA : (0:ℝ) ≤ C ^ 2 * ((1 + |x|) ^ (2 * k) * gaussianPDFReal 0 1 x) :=
          mul_nonneg (sq_nonneg C) (mul_nonneg (by positivity) hρ0)
        nlinarith [hA, hx]

/-- **Pointwise Cauchy–Schwarz bound for `|g x · T x|`.** -/
theorem abs_mul_gueTail_le {g : ℝ → ℝ} (hg : MemLp g 2 (gaussianReal 0 1)) {x : ℝ} (hx : 0 < x) :
    |g x * gueTail g x| ≤ Real.sqrt ((g x) ^ 2 * gaussianPDFReal 0 1 x / x) *
      Real.sqrt (∫ t in Set.Ioi x, (g t) ^ 2 * gaussianPDFReal 0 1 t) := by
  have hT := sq_integral_Ioi_mul_gaussianPDFReal_le (g := g) (x := x) hg
  have hmass := integral_Ioi_gaussianPDFReal_le hx
  have hρ0 : (0:ℝ) ≤ gaussianPDFReal 0 1 x := gaussianPDFReal_nonneg 0 1 x
  have hG0 : (0:ℝ) ≤ ∫ t in Set.Ioi x, (g t) ^ 2 * gaussianPDFReal 0 1 t :=
    setIntegral_nonneg measurableSet_Ioi (fun t _ =>
      mul_nonneg (sq_nonneg _) (gaussianPDFReal_nonneg 0 1 t))
  have h1 : (gueTail g x) ^ 2 ≤ (gaussianPDFReal 0 1 x / x) *
      ∫ t in Set.Ioi x, (g t) ^ 2 * gaussianPDFReal 0 1 t :=
    hT.trans (mul_le_mul_of_nonneg_right hmass hG0)
  have h2 : |gueTail g x| ≤ Real.sqrt ((gaussianPDFReal 0 1 x / x) *
      ∫ t in Set.Ioi x, (g t) ^ 2 * gaussianPDFReal 0 1 t) := by
    have hs := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq_eq_abs] at hs
  have h3 : |g x| * |gueTail g x| ≤ |g x| * Real.sqrt ((gaussianPDFReal 0 1 x / x) *
      ∫ t in Set.Ioi x, (g t) ^ 2 * gaussianPDFReal 0 1 t) :=
    mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  have h4 : |g x| * Real.sqrt ((gaussianPDFReal 0 1 x / x) *
        ∫ t in Set.Ioi x, (g t) ^ 2 * gaussianPDFReal 0 1 t)
      = Real.sqrt ((g x) ^ 2 * gaussianPDFReal 0 1 x / x) *
        Real.sqrt (∫ t in Set.Ioi x, (g t) ^ 2 * gaussianPDFReal 0 1 t) := by
    have e1 : Real.sqrt ((g x) ^ 2 * gaussianPDFReal 0 1 x / x)
        = Real.sqrt ((g x) ^ 2) * Real.sqrt (gaussianPDFReal 0 1 x / x) := by
      rw [show (g x) ^ 2 * gaussianPDFReal 0 1 x / x
          = (g x) ^ 2 * (gaussianPDFReal 0 1 x / x) by ring,
        Real.sqrt_mul (sq_nonneg (g x))]
    have e2 : |g x| = Real.sqrt ((g x) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    have hρx : (0:ℝ) ≤ gaussianPDFReal 0 1 x / x := div_nonneg hρ0 hx.le
    rw [e2, e1, Real.sqrt_mul hρx]
    ring
  rw [abs_mul]
  exact h3.trans_eq h4

/-- **Decay of `ρ x * (g x * h x)` at `+∞`.** -/
theorem tendsto_gaussianPDFReal_mul_g_mul_steinKernel_atTop {g : ℝ → ℝ}
    (hg : MemLp g 2 (gaussianReal 0 1))
    (hgr : ∃ C : ℝ, 0 ≤ C ∧ ∃ k : ℕ, ∀ x, |g x| ≤ C * (1 + |x|) ^ k) :
    Tendsto (fun x => gaussianPDFReal 0 1 x * (g x * (-Real.sqrt (2 * Real.pi) *
      Real.exp (x ^ 2 / 2) * gueTail g x))) atTop (𝓝 0) := by
  have hfun : (fun x => gaussianPDFReal 0 1 x * (g x * (-Real.sqrt (2 * Real.pi) *
      Real.exp (x ^ 2 / 2) * gueTail g x))) = fun x => -(g x * gueTail g x) := by
    funext x
    have h := gaussianPDFReal_mul_steinKernel g x
    calc gaussianPDFReal 0 1 x * (g x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
          gueTail g x))
        = g x * (gaussianPDFReal 0 1 x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
            ∫ t in Set.Ioi x, g t * gaussianPDFReal 0 1 t)) := by
          simp only [gueTail]
          ring
      _ = g x * (-∫ t in Set.Ioi x, g t * gaussianPDFReal 0 1 t) := by rw [h]
      _ = g x * (-gueTail g x) := by simp only [gueTail]
      _ = -(g x * gueTail g x) := by ring
  rw [hfun]
  have hmain : Tendsto (fun x => g x * gueTail g x) atTop (𝓝 0) := by
    have hsq : Tendsto (fun x : ℝ => Real.sqrt ((g x) ^ 2 * gaussianPDFReal 0 1 x / x))
        atTop (𝓝 0) := by
      have := (tendsto_abs_sq_mul_gaussianPDFReal_div_atTop hgr).sqrt
      simpa using this
    have hG : Tendsto (fun x : ℝ => Real.sqrt (∫ t in Set.Ioi x, (g t) ^ 2 *
        gaussianPDFReal 0 1 t)) atTop (𝓝 0) := by
      have := (tendsto_integral_Ioi_id_zero
        (fun t => (g t) ^ 2 * gaussianPDFReal 0 1 t)).sqrt
      simpa using this
    have hmaj : Tendsto (fun x : ℝ => Real.sqrt ((g x) ^ 2 * gaussianPDFReal 0 1 x / x) *
        Real.sqrt (∫ t in Set.Ioi x, (g t) ^ 2 * gaussianPDFReal 0 1 t)) atTop (𝓝 0) := by
      have := hsq.mul hG
      simpa using this
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    rw [Real.norm_eq_abs]
    exact abs_mul_gueTail_le hg hx
  simpa using hmain.neg

/-- Left-tail Mills bound: `∫ t in Iic x, ρ t ≤ ρ x / (-x)` for `x < 0`. -/
theorem integral_Iic_gaussianPDFReal_le {x : ℝ} (hx : x < 0) :
    ∫ t in Set.Iic x, gaussianPDFReal 0 1 t ≤ gaussianPDFReal 0 1 x / (-x) := by
  have h := weight_tail_Iic_le hx
  have hnorm := sqrt_two_pi_mul_exp_mul_gaussianPDFReal x
  have hpos : (0:ℝ) < Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) := by positivity
  have hx' : (0:ℝ) < -x := by linarith
  have hinv : gaussianPDFReal 0 1 x = 1 / (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2)) := by
    rw [eq_div_iff hpos.ne']
    linarith [hnorm]
  rw [hinv]
  have hden : (0:ℝ) < Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * (-x) := by positivity
  rw [show (1 / (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2))) / (-x)
      = 1 / (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * (-x)) by
    rw [div_div]]
  rw [le_div_iff₀ hden]
  have hmul := mul_le_mul_of_nonneg_right h hx'.le
  rw [one_div, inv_mul_cancel₀ hx'.ne'] at hmul
  calc (∫ t in Set.Iic x, gaussianPDFReal 0 1 t) * (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * (-x))
      = (Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
          ∫ t in Set.Iic x, gaussianPDFReal 0 1 t) * (-x) := by ring
    _ ≤ 1 := hmul

/-- Pointwise Cauchy–Schwarz bound for `|g x · T x|` on the left half-line. -/
theorem abs_mul_gueTail_le_atBot {g : ℝ → ℝ} (hg : MemLp g 2 (gaussianReal 0 1))
    (hint : IntegrableOn (fun t => g t * gaussianPDFReal 0 1 t) (Set.univ))
    (hzero : ∫ t, g t * gaussianPDFReal 0 1 t = 0) {x : ℝ} (hx : x < 0) :
    |g x * gueTail g x| ≤ Real.sqrt ((g x) ^ 2 * gaussianPDFReal 0 1 x / (-x)) *
      Real.sqrt (∫ t in Set.Iic x, (g t) ^ 2 * gaussianPDFReal 0 1 t) := by
  have hT := sq_integral_Ioi_mul_gaussianPDFReal_le_left (g := g) hg hint hzero (x := x)
  have hmass := integral_Iic_gaussianPDFReal_le hx
  have hρ0 : (0:ℝ) ≤ gaussianPDFReal 0 1 x := gaussianPDFReal_nonneg 0 1 x
  have hG0 : (0:ℝ) ≤ ∫ t in Set.Iic x, (g t) ^ 2 * gaussianPDFReal 0 1 t :=
    setIntegral_nonneg measurableSet_Iic (fun t _ =>
      mul_nonneg (sq_nonneg _) (gaussianPDFReal_nonneg 0 1 t))
  have hnx : (0:ℝ) < -x := by linarith
  have h1 : (gueTail g x) ^ 2 ≤ (gaussianPDFReal 0 1 x / (-x)) *
      ∫ t in Set.Iic x, (g t) ^ 2 * gaussianPDFReal 0 1 t :=
    hT.trans (mul_le_mul_of_nonneg_right hmass hG0)
  have h2 : |gueTail g x| ≤ Real.sqrt ((gaussianPDFReal 0 1 x / (-x)) *
      ∫ t in Set.Iic x, (g t) ^ 2 * gaussianPDFReal 0 1 t) := by
    have hs := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq_eq_abs] at hs
  have h3 : |g x| * |gueTail g x| ≤ |g x| * Real.sqrt ((gaussianPDFReal 0 1 x / (-x)) *
      ∫ t in Set.Iic x, (g t) ^ 2 * gaussianPDFReal 0 1 t) :=
    mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  have h4 : |g x| * Real.sqrt ((gaussianPDFReal 0 1 x / (-x)) *
        ∫ t in Set.Iic x, (g t) ^ 2 * gaussianPDFReal 0 1 t)
      = Real.sqrt ((g x) ^ 2 * gaussianPDFReal 0 1 x / (-x)) *
        Real.sqrt (∫ t in Set.Iic x, (g t) ^ 2 * gaussianPDFReal 0 1 t) := by
    have e1 : Real.sqrt ((g x) ^ 2 * gaussianPDFReal 0 1 x / (-x))
        = Real.sqrt ((g x) ^ 2) * Real.sqrt (gaussianPDFReal 0 1 x / (-x)) := by
      rw [show (g x) ^ 2 * gaussianPDFReal 0 1 x / (-x)
          = (g x) ^ 2 * (gaussianPDFReal 0 1 x / (-x)) by ring,
        Real.sqrt_mul (sq_nonneg (g x))]
    have e2 : |g x| = Real.sqrt ((g x) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    have hρx : (0:ℝ) ≤ gaussianPDFReal 0 1 x / (-x) := div_nonneg hρ0 hnx.le
    rw [e2, e1, Real.sqrt_mul hρx]
    ring
  rw [abs_mul]
  exact h3.trans_eq h4

/-- `(1+|t|)^k ρ t → 0` at `-∞`. -/
theorem tendsto_one_add_abs_pow_mul_gaussianPDFReal_atBot (k : ℕ) :
    Tendsto (fun x : ℝ => (1 + |x|) ^ k * gaussianPDFReal 0 1 x) atBot (𝓝 0) := by
  have hρ : Tendsto (fun x : ℝ => gaussianPDFReal 0 1 x * x ^ k) atBot (𝓝 0) :=
    tendsto_gaussianPDFReal_mul_pow_atBot k
  have h1 : Tendsto (fun x : ℝ => gaussianPDFReal 0 1 x * |x| ^ k) atBot (𝓝 0) := by
    have h2 : (fun x : ℝ => |gaussianPDFReal 0 1 x * x ^ k|)
        = fun x => gaussianPDFReal 0 1 x * |x| ^ k := by
      funext x
      rw [abs_mul, abs_of_nonneg (gaussianPDFReal_nonneg 0 1 x), abs_pow]
    rw [← h2]
    simpa using hρ.abs
  have hρz : Tendsto (fun x : ℝ => gaussianPDFReal 0 1 x) atBot (𝓝 0) := by
    have := tendsto_gaussianPDFReal_mul_pow_atBot 0
    simpa using this
  have hmaj : Tendsto (fun x : ℝ => 2 ^ k * ((gaussianPDFReal 0 1 x * |x| ^ k) +
      gaussianPDFReal 0 1 x)) atBot (𝓝 0) := by
    have hsum : Tendsto (fun x : ℝ => gaussianPDFReal 0 1 x * |x| ^ k + gaussianPDFReal 0 1 x)
        atBot (𝓝 0) := by
      have := h1.add hρz
      simpa using this
    have := hsum.const_mul (2 ^ k)
    simpa using this
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (gaussianPDFReal_nonneg 0 1 x))]
  have hb : (1 + |x|) ^ k ≤ 2 ^ k * (1 + |x| ^ k) := one_add_pow_le_two_pow_mul |x| (abs_nonneg x) k
  have hρ0 : (0:ℝ) ≤ gaussianPDFReal 0 1 x := gaussianPDFReal_nonneg 0 1 x
  nlinarith [hb, hρ0,
    mul_nonneg (by positivity : (0:ℝ) ≤ gaussianPDFReal 0 1 x) (by positivity : (0:ℝ) ≤ 1 + |x| ^ k)]

/-- `g²ρ/(-x) → 0` at `-∞` for `g` of polynomial growth. -/
theorem tendsto_abs_sq_mul_gaussianPDFReal_div_neg_atBot {g : ℝ → ℝ}
    (hgr : ∃ C : ℝ, 0 ≤ C ∧ ∃ k : ℕ, ∀ x, |g x| ≤ C * (1 + |x|) ^ k) :
    Tendsto (fun x : ℝ => (g x) ^ 2 * gaussianPDFReal 0 1 x / (-x)) atBot (𝓝 0) := by
  obtain ⟨C, hC0, k, hC⟩ := hgr
  have hmaj : Tendsto (fun x : ℝ => C ^ 2 * ((1 + |x|) ^ (2 * k) * gaussianPDFReal 0 1 x))
      atBot (𝓝 0) := by
    have h := (tendsto_one_add_abs_pow_mul_gaussianPDFReal_atBot (2 * k)).const_mul (C ^ 2)
    simpa using h
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_le_atBot (-1:ℝ)] with x hx
  have hx0 : (0:ℝ) < -x := by linarith
  have hρ0 : (0:ℝ) ≤ gaussianPDFReal 0 1 x := gaussianPDFReal_nonneg 0 1 x
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mul_nonneg (sq_nonneg _) hρ0) hx0.le)]
  have h1 : (g x) ^ 2 ≤ C ^ 2 * (1 + |x|) ^ (2 * k) := by
    have h3 := pow_le_pow_left₀ (abs_nonneg (g x)) (hC x) 2
    have h4 : (C * (1 + |x|) ^ k) ^ 2 = C ^ 2 * (1 + |x|) ^ (2 * k) := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm k 2]
    rw [h4] at h3
    have h2 : (g x) ^ 2 = |g x| ^ 2 := (sq_abs (g x)).symm
    rw [h2]
    exact h3
  rw [div_le_iff₀ hx0]
  calc (g x) ^ 2 * gaussianPDFReal 0 1 x
      ≤ C ^ 2 * (1 + |x|) ^ (2 * k) * gaussianPDFReal 0 1 x :=
        mul_le_mul_of_nonneg_right h1 hρ0
    _ = C ^ 2 * ((1 + |x|) ^ (2 * k) * gaussianPDFReal 0 1 x) := by ring
    _ ≤ C ^ 2 * ((1 + |x|) ^ (2 * k) * gaussianPDFReal 0 1 x) * (-x) := by
        have hA : (0:ℝ) ≤ C ^ 2 * ((1 + |x|) ^ (2 * k) * gaussianPDFReal 0 1 x) :=
          mul_nonneg (sq_nonneg C) (mul_nonneg (by positivity) hρ0)
        nlinarith [hA, hx0]

/-- **Decay of `ρ x * (g x * h x)` at `-∞`.** -/
theorem tendsto_gaussianPDFReal_mul_g_mul_steinKernel_atBot {g : ℝ → ℝ}
    (hg : MemLp g 2 (gaussianReal 0 1))
    (hint : IntegrableOn (fun t => g t * gaussianPDFReal 0 1 t) (Set.univ))
    (hzero : ∫ t, g t * gaussianPDFReal 0 1 t = 0)
    (hgr : ∃ C : ℝ, 0 ≤ C ∧ ∃ k : ℕ, ∀ x, |g x| ≤ C * (1 + |x|) ^ k) :
    Tendsto (fun x => gaussianPDFReal 0 1 x * (g x * (-Real.sqrt (2 * Real.pi) *
      Real.exp (x ^ 2 / 2) * gueTail g x))) atBot (𝓝 0) := by
  have hfun : (fun x => gaussianPDFReal 0 1 x * (g x * (-Real.sqrt (2 * Real.pi) *
      Real.exp (x ^ 2 / 2) * gueTail g x))) = fun x => -(g x * gueTail g x) := by
    funext x
    have h := gaussianPDFReal_mul_steinKernel g x
    calc gaussianPDFReal 0 1 x * (g x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
          gueTail g x))
        = g x * (gaussianPDFReal 0 1 x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
            ∫ t in Set.Ioi x, g t * gaussianPDFReal 0 1 t)) := by
          simp only [gueTail]
          ring
      _ = g x * (-∫ t in Set.Ioi x, g t * gaussianPDFReal 0 1 t) := by rw [h]
      _ = g x * (-gueTail g x) := by simp only [gueTail]
      _ = -(g x * gueTail g x) := by ring
  rw [hfun]
  have hmain : Tendsto (fun x => g x * gueTail g x) atBot (𝓝 0) := by
    have hsq : Tendsto (fun x : ℝ => Real.sqrt ((g x) ^ 2 * gaussianPDFReal 0 1 x / (-x)))
        atBot (𝓝 0) := by
      have := (tendsto_abs_sq_mul_gaussianPDFReal_div_neg_atBot hgr).sqrt
      simpa using this
    have hG : Tendsto (fun x : ℝ => Real.sqrt (∫ t in Set.Iic x, (g t) ^ 2 *
        gaussianPDFReal 0 1 t)) atBot (𝓝 0) := by
      have h := (MeasureTheory.tendsto_integral_Iic_zero (μ := volume)
        (f := fun t => (g t) ^ 2 * gaussianPDFReal 0 1 t) (l := atBot)
        (a := fun x : ℝ => x) tendsto_id).sqrt
      simpa using h
    have hmaj : Tendsto (fun x : ℝ => Real.sqrt ((g x) ^ 2 * gaussianPDFReal 0 1 x / (-x)) *
        Real.sqrt (∫ t in Set.Iic x, (g t) ^ 2 * gaussianPDFReal 0 1 t)) atBot (𝓝 0) := by
      have := hsq.mul hG
      simpa using this
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards [eventually_lt_atBot (0:ℝ)] with x hx
    rw [Real.norm_eq_abs]
    exact abs_mul_gueTail_le_atBot hg hint hzero hx
  simpa using hmain.neg

/-- **Contraction identity for the Stein kernel**, `∫ g² dγ = ∫ h'² dγ + ∫ h² dγ`, with
`h = -√(2π) e^{x²/2} T` and `h' = g + x h` written out explicitly. -/
theorem integral_sq_eq_integral_deriv_steinKernel_sq_add {g : ℝ → ℝ}
    (hcont : ∀ x, ContinuousAt (fun t => g t * gaussianPDFReal 0 1 t) x)
    (hintU : IntegrableOn (fun t => g t * gaussianPDFReal 0 1 t) (Set.univ))
    (hbot : Tendsto (fun x => (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
      (x * gaussianPDFReal 0 1 x)) atBot (𝓝 0))
    (htop : Tendsto (fun x => (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
      (x * gaussianPDFReal 0 1 x)) atTop (𝓝 0))
    (hsq : Integrable (fun x => (g x + x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
      gueTail g x)) ^ 2 * gaussianPDFReal 0 1 x))
    (hh : Integrable (fun x => (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
      gaussianPDFReal 0 1 x))
    (hx2 : Integrable (fun x => x ^ 2 * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
      gueTail g x) ^ 2 * gaussianPDFReal 0 1 x))
    (hcross : Integrable (fun x => x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
      gueTail g x) * (g x + x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x)) *
      gaussianPDFReal 0 1 x)) :
    ∫ x, g x ^ 2 * gaussianPDFReal 0 1 x
      = (∫ x, (g x + x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x)) ^ 2 *
          gaussianPDFReal 0 1 x)
        + ∫ x, (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
          gaussianPDFReal 0 1 x := by
  have hderiv : ∀ x, HasDerivAt (fun y => -Real.sqrt (2 * Real.pi) * Real.exp (y ^ 2 / 2) *
      gueTail g y) (g x + x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x)) x := by
    intro x
    have h := hasDerivAt_steinKernel (g := g) (x := x)
      (hintU.mono_set (Set.subset_univ _))
      (by simpa using hintU.aestronglyMeasurable) (hcont x)
    simpa only [gueTail] using h
  have hg : ∀ x, g x = (g x + x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x)) -
      x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) := by
    intro x
    ring
  have hIBP1 : Integrable ((fun y : ℝ => (-Real.sqrt (2 * Real.pi) * Real.exp (y ^ 2 / 2) *
        gueTail g y) ^ 2) *
      fun x : ℝ => gaussianPDFReal 0 1 x - x ^ 2 * gaussianPDFReal 0 1 x) := by
    refine (hh.sub hx2).congr (ae_of_all _ fun x => ?_)
    simp only [Pi.mul_apply, Pi.sub_apply]
    ring
  have hIBP2 : Integrable ((fun x : ℝ => 2 * ((-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
        gueTail g x) * (g x + x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x)))) *
      fun x : ℝ => x * gaussianPDFReal 0 1 x) := by
    refine (hcross.const_mul 2).congr (ae_of_all _ fun x => ?_)
    simp only [Pi.mul_apply]
    ring
  exact integral_sq_eq_integral_deriv_sq_add
    (h := fun y => -Real.sqrt (2 * Real.pi) * Real.exp (y ^ 2 / 2) * gueTail g y)
    (h' := fun x => g x + x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x))
    (g := g) hderiv hg hIBP1 hIBP2 hbot htop hsq hh hx2 hcross

/-- **Variance bound from the Stein identity**: if `∫ g² dγ = -∫ g' h dγ` and `h` is the Stein
kernel with the contraction estimates, then `∫ g² dγ ≤ ∫ (g')² dγ`. -/
theorem poincare_steinKernel_sq_bound {g g' : ℝ → ℝ}
    (hstein : ∫ x, g x ^ 2 ∂(gaussianReal 0 1) = -∫ x, g' x *
      (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ∂(gaussianReal 0 1))
    (hLp1 : MemLp g' 2 (gaussianReal 0 1))
    (hLp2 : MemLp (fun x => -Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) 2
      (gaussianReal 0 1))
    (hcont : ∀ x, ContinuousAt (fun t => g t * gaussianPDFReal 0 1 t) x)
    (hintU : IntegrableOn (fun t => g t * gaussianPDFReal 0 1 t) (Set.univ))
    (hbot : Tendsto (fun x => (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
      (x * gaussianPDFReal 0 1 x)) atBot (𝓝 0))
    (htop : Tendsto (fun x => (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
      (x * gaussianPDFReal 0 1 x)) atTop (𝓝 0))
    (hsq : Integrable (fun x => (g x + x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
      gueTail g x)) ^ 2 * gaussianPDFReal 0 1 x))
    (hh : Integrable (fun x => (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
      gaussianPDFReal 0 1 x))
    (hx2 : Integrable (fun x => x ^ 2 * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
      gueTail g x) ^ 2 * gaussianPDFReal 0 1 x))
    (hcross : Integrable (fun x => x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
      gueTail g x) * (g x + x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x)) *
      gaussianPDFReal 0 1 x)) :
    ∫ x, g x ^ 2 ∂(gaussianReal 0 1) ≤ ∫ x, (g' x) ^ 2 ∂(gaussianReal 0 1) := by
  have hcid := integral_sq_eq_integral_deriv_steinKernel_sq_add (g := g) hcont hintU hbot htop
    hsq hh hx2 hcross
  -- S = ∫ h'² + ∫ h²  with ∫ h'² ≥ 0, hence ∫ h² ≤ S
  have hnn : (0:ℝ) ≤ ∫ x, (g x + x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
      gueTail g x)) ^ 2 * gaussianPDFReal 0 1 x :=
    integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (gaussianPDFReal_nonneg 0 1 x))
  have hcontr : ∫ x, (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 *
      gaussianPDFReal 0 1 x ≤ ∫ x, g x ^ 2 * gaussianPDFReal 0 1 x := by
    rw [hcid]
    linarith
  have hcontr' : ∫ x, (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ^ 2 ∂
      (gaussianReal 0 1) ≤ ∫ x, g x ^ 2 ∂(gaussianReal 0 1) := by
    rw [integral_gaussianReal_eq_integral_smul (μ := 0) (v := 1) (by norm_num),
      integral_gaussianReal_eq_integral_smul (μ := 0) (v := 1) (by norm_num)]
    simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hcontr
  have hstein' : ∫ x, g x ^ 2 ∂(gaussianReal 0 1) = -∫ x, g' x *
      (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ∂(gaussianReal 0 1) := hstein
  have hhg2 : 0 ≤ ∫ x, g x ^ 2 ∂(gaussianReal 0 1) := integral_nonneg (fun x => sq_nonneg _)
  exact integral_sq_le_integral_deriv_sq (g := g) (g' := g')
    (h := fun x => -Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x)
    hstein' hcontr' hhg2 hLp1 hLp2

/-- The Stein identity `∫ g² dγ = -∫ g' h dγ` for the Stein kernel `h = -√(2π)e^{x²/2}T`. -/
theorem integral_sq_eq_neg_integral_deriv_steinKernel {g g' : ℝ → ℝ}
    (hderivg : ∀ x, HasDerivAt g (g' x) x)
    (hgm : Measurable g)
    (hcont : ∀ x, ContinuousAt (fun t => g t * gaussianPDFReal 0 1 t) x)
    (hintU : IntegrableOn (fun t => g t * gaussianPDFReal 0 1 t) (Set.univ))
    (hIBPg : Integrable (fun x => gaussianPDFReal 0 1 x * g' x))
    (hIBPxg : Integrable (fun x => x * (gaussianPDFReal 0 1 x * g x)))
    (hbotg : Tendsto (fun x => gaussianPDFReal 0 1 x * g x) atBot (𝓝 0))
    (htopg : Tendsto (fun x => gaussianPDFReal 0 1 x * g x) atTop (𝓝 0))
    (hIBPgh : Integrable (fun x => gaussianPDFReal 0 1 x *
      (g' x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) +
        g x * (g x + x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x)))))
    (hIBPxgh : Integrable (fun x => x * (gaussianPDFReal 0 1 x *
      (g x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x)))))
    (hbotgh : Tendsto (fun x => gaussianPDFReal 0 1 x *
      (g x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x))) atBot (𝓝 0))
    (htopgh : Tendsto (fun x => gaussianPDFReal 0 1 x *
      (g x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x))) atTop (𝓝 0))
    (hgh' : Integrable (fun x => g x *
      (g x + x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x))) (gaussianReal 0 1))
    (hgh : Integrable (fun x => g' x *
      (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x)) (gaussianReal 0 1))
    (hxgh : Integrable (fun x => x * (g x *
      (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x))) (gaussianReal 0 1)) :
    ∫ x, g x ^ 2 ∂(gaussianReal 0 1) = -∫ x, g' x *
      (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) ∂(gaussianReal 0 1) := by
  have hderivh : ∀ x, HasDerivAt (fun y => -Real.sqrt (2 * Real.pi) * Real.exp (y ^ 2 / 2) *
      gueTail g y) (g x + x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x)) x := by
    intro x
    have h := hasDerivAt_steinKernel (g := g) (x := x)
      (hintU.mono_set (Set.subset_univ _))
      (by simpa using hintU.aestronglyMeasurable) (hcont x)
    simpa only [gueTail] using h
  have hg : ∀ x, g x = (g x + x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x)) -
      x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x) := fun x => by ring
  exact integral_sq_eq_neg_integral_deriv_mul (g := g) (g' := g')
    (h := fun y => -Real.sqrt (2 * Real.pi) * Real.exp (y ^ 2 / 2) * gueTail g y)
    (h' := fun x => g x + x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail g x))
    hderivg hderivh hIBPg hIBPxg hbotg htopg hIBPgh hIBPxgh hbotgh htopgh hg hgh' hgh hxgh

/-- **Gaussian Poincaré inequality**: `∫ f² dγ ≤ ∫ (f')² dγ`. -/
theorem gaussian_poincare {f f' : ℝ → ℝ}
    (hderivg : ∀ x, HasDerivAt f (f' x) x)
    (hgm : Measurable f)
    (hcont : ∀ x, ContinuousAt (fun t => f t * gaussianPDFReal 0 1 t) x)
    (hintU : IntegrableOn (fun t => f t * gaussianPDFReal 0 1 t) (Set.univ))
    (hIBPg : Integrable (fun x => gaussianPDFReal 0 1 x * f' x))
    (hIBPxg : Integrable (fun x => x * (gaussianPDFReal 0 1 x * f x)))
    (hbotg : Tendsto (fun x => gaussianPDFReal 0 1 x * f x) atBot (𝓝 0))
    (htopg : Tendsto (fun x => gaussianPDFReal 0 1 x * f x) atTop (𝓝 0))
    (hIBPgh : Integrable (fun x => gaussianPDFReal 0 1 x *
      (f' x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail f x) +
        f x * (f x + x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail f x)))))
    (hIBPxgh : Integrable (fun x => x * (gaussianPDFReal 0 1 x *
      (f x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail f x)))))
    (hbotgh : Tendsto (fun x => gaussianPDFReal 0 1 x *
      (f x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail f x))) atBot (𝓝 0))
    (htopgh : Tendsto (fun x => gaussianPDFReal 0 1 x *
      (f x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail f x))) atTop (𝓝 0))
    (hgh' : Integrable (fun x => f x *
      (f x + x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail f x))) (gaussianReal 0 1))
    (hgh : Integrable (fun x => f' x *
      (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail f x)) (gaussianReal 0 1))
    (hxgh : Integrable (fun x => x * (f x *
      (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail f x))) (gaussianReal 0 1))
    (hLp1 : MemLp f' 2 (gaussianReal 0 1))
    (hLp2 : MemLp (fun x => -Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail f x) 2
      (gaussianReal 0 1))
    (hbot_h : Tendsto (fun x => (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail f x) ^ 2 *
      (x * gaussianPDFReal 0 1 x)) atBot (𝓝 0))
    (htop_h : Tendsto (fun x => (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail f x) ^ 2 *
      (x * gaussianPDFReal 0 1 x)) atTop (𝓝 0))
    (hsq : Integrable (fun x => (f x + x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
      gueTail f x)) ^ 2 * gaussianPDFReal 0 1 x))
    (hh : Integrable (fun x => (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail f x) ^ 2 *
      gaussianPDFReal 0 1 x))
    (hx2 : Integrable (fun x => x ^ 2 * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
      gueTail f x) ^ 2 * gaussianPDFReal 0 1 x))
    (hcross : Integrable (fun x => x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) *
      gueTail f x) * (f x + x * (-Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2) * gueTail f x)) *
      gaussianPDFReal 0 1 x)) :
    ∫ x, f x ^ 2 ∂(gaussianReal 0 1) ≤ ∫ x, (f' x) ^ 2 ∂(gaussianReal 0 1) := by
  have hstein := integral_sq_eq_neg_integral_deriv_steinKernel (g := f) (g' := f')
    hderivg hgm hcont hintU hIBPg hIBPxg hbotg htopg hIBPgh hIBPxgh hbotgh htopgh hgh' hgh hxgh
  exact poincare_steinKernel_sq_bound (g := f) (g' := f') hstein hLp1 hLp2 hcont hintU
    hbot_h htop_h hsq hh hx2 hcross

/-- `g' * h ∈ L¹(γ)` for `g', h ∈ L²(γ)`. -/
theorem integrable_mul_of_memLp_two_gaussian {a b : ℝ → ℝ}
    (ha : MemLp a 2 (gaussianReal 0 1)) (hb : MemLp b 2 (gaussianReal 0 1)) :
    Integrable (fun x => a x * b x) (gaussianReal 0 1) := by
  have h := ha.integrable_mul hb
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only [Pi.mul_apply]

/-- `∫ t in Ioi x, t^2 ρ t = x ρ x + ∫ t in Ioi x, ρ t`. -/
theorem integral_Ioi_sq_mul_gaussianPDFReal (x : ℝ) :
    ∫ t in Set.Ioi x, t ^ 2 * gaussianPDFReal 0 1 t
      = x * gaussianPDFReal 0 1 x + ∫ t in Set.Ioi x, gaussianPDFReal 0 1 t := by
  -- d/dt (-t ρ t) = -ρ t + t^2 ρ t
  have hderiv : ∀ t ∈ Set.Ioi x,
      HasDerivAt (fun s : ℝ => -(s * gaussianPDFReal 0 1 s))
        (t ^ 2 * gaussianPDFReal 0 1 t - gaussianPDFReal 0 1 t) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
    have h2 := hasDerivAt_gaussianPDFReal_one t
    have h3 := (h1.mul h2).neg
    have e : -(1 * gaussianPDFReal 0 1 t + t * (-t * gaussianPDFReal 0 1 t))
        = t ^ 2 * gaussianPDFReal 0 1 t - gaussianPDFReal 0 1 t := by ring
    rwa [e] at h3
  have hint : IntegrableOn (fun t : ℝ => t ^ 2 * gaussianPDFReal 0 1 t -
      gaussianPDFReal 0 1 t) (Set.Ioi x) :=
    (((integrable_gaussianPDFReal_mul_pow 2).integrableOn).sub
      ((integrable_gaussianPDFReal_mul_pow 0).integrableOn : IntegrableOn
        (fun t => gaussianPDFReal 0 1 t * t ^ 0) (Set.Ioi x))).congr_fun
      (fun t _ => by simp only [Pi.sub_apply, Pi.mul_apply]; ring) measurableSet_Ioi
  have hlim : Tendsto (fun s : ℝ => -(s * gaussianPDFReal 0 1 s)) atTop (𝓝 0) := by
    have h := tendsto_gaussianPDFReal_mul_pow_atTop 1
    have h' := h.neg
    simpa [mul_comm] using h'
  have hcont : ContinuousWithinAt (fun s : ℝ => -(s * gaussianPDFReal 0 1 s)) (Set.Ici x) x :=
    ((continuousAt_id.mul (hasDerivAt_gaussianPDFReal_one x).continuousAt).neg).continuousWithinAt
  have main := integral_Ioi_of_hasDerivAt_of_tendsto (a := x) hcont hderiv hint hlim
  -- main : ∫ t in Ioi x, (t^2 ρ t - ρ t) = -x ρ x  (limit value)
  have hsplit : ∫ t in Set.Ioi x, (t ^ 2 * gaussianPDFReal 0 1 t - gaussianPDFReal 0 1 t)
      = (∫ t in Set.Ioi x, t ^ 2 * gaussianPDFReal 0 1 t)
        - ∫ t in Set.Ioi x, gaussianPDFReal 0 1 t := by
    refine integral_sub (μ := volume.restrict (Set.Ioi x)) (f := fun t => t ^ 2 * gaussianPDFReal 0 1 t)
      (g := fun t => gaussianPDFReal 0 1 t) ?_ ?_
    · exact ((integrable_gaussianPDFReal_mul_pow 2)).integrableOn.congr_fun
        (fun t _ => by simp only [Pi.mul_apply]; ring) measurableSet_Ioi
    · exact ((integrable_gaussianPDFReal_mul_pow 0)).integrableOn.congr_fun
        (fun t _ => by simp only [Pi.mul_apply, pow_zero, mul_one]) measurableSet_Ioi
  rw [hsplit] at main
  linarith [main]

/-- `∫ t in Ioi x, t² ρ t ≤ (1 + x) ρ x` for `x ≥ 1`. -/
theorem integral_Ioi_sq_mul_gaussianPDFReal_le {x : ℝ} (hx : 1 ≤ x) :
    ∫ t in Set.Ioi x, t ^ 2 * gaussianPDFReal 0 1 t ≤ (1 + x) * gaussianPDFReal 0 1 x := by
  have hx0 : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hid := integral_Ioi_sq_mul_gaussianPDFReal x
  have hmass := integral_Ioi_gaussianPDFReal_le hx0
  have hρ0 : (0:ℝ) ≤ gaussianPDFReal 0 1 x := gaussianPDFReal_nonneg 0 1 x
  rw [hid]
  calc x * gaussianPDFReal 0 1 x + ∫ t in Set.Ioi x, gaussianPDFReal 0 1 t
      ≤ x * gaussianPDFReal 0 1 x + gaussianPDFReal 0 1 x / x := by linarith
    _ = (x + 1 / x) * gaussianPDFReal 0 1 x := by ring
    _ ≤ (1 + x) * gaussianPDFReal 0 1 x := by
        have h1 : 1 / x ≤ 1 := by
          rw [div_le_one hx0]
          exact hx
        have h2 : x + 1 / x ≤ 1 + x := by linarith
        exact mul_le_mul_of_nonneg_right h2 hρ0

/-- **General polynomial-tail integration by parts**:
`∫ t in Ioi x, t^j ρ t = x^{j-1} ρ x + (j-1) ∫ t in Ioi x, t^{j-2} ρ t` for `j ≥ 1`. -/
theorem integral_Ioi_pow_mul_gaussianPDFReal (j : ℕ) (hj : 1 ≤ j) (x : ℝ) :
    ∫ t in Set.Ioi x, t ^ j * gaussianPDFReal 0 1 t
      = x ^ (j - 1) * gaussianPDFReal 0 1 x
        + ((j : ℝ) - 1) * ∫ t in Set.Ioi x, t ^ (j - 2) * gaussianPDFReal 0 1 t := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hderiv : ∀ t ∈ Set.Ioi x,
      HasDerivAt (fun s : ℝ => -(s ^ k * gaussianPDFReal 0 1 s))
        (t ^ (k + 1) * gaussianPDFReal 0 1 t - (k : ℝ) * (t ^ (k - 1) * gaussianPDFReal 0 1 t)) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => s ^ k) ((k : ℝ) * t ^ (k - 1)) t := by
      simpa using hasDerivAt_pow k t
    have h2 := hasDerivAt_gaussianPDFReal_one t
    have h3 := (h1.mul h2).neg
    have e : -((k : ℝ) * t ^ (k - 1) * gaussianPDFReal 0 1 t + t ^ k * (-t * gaussianPDFReal 0 1 t))
        = t ^ (k + 1) * gaussianPDFReal 0 1 t - (k : ℝ) * (t ^ (k - 1) * gaussianPDFReal 0 1 t) := by
      rw [show t ^ (k + 1) = t ^ k * t by ring]
      ring
    rwa [e] at h3
  have hint : IntegrableOn (fun t : ℝ => t ^ (k + 1) * gaussianPDFReal 0 1 t -
      (k : ℝ) * (t ^ (k - 1) * gaussianPDFReal 0 1 t)) (Set.Ioi x) := by
    refine (((integrable_gaussianPDFReal_mul_pow (k + 1)).integrableOn).sub
      (((integrable_gaussianPDFReal_mul_pow (k - 1)).const_mul (k : ℝ)).integrableOn)).congr_fun ?_
      measurableSet_Ioi
    intro t _
    simp only [Pi.sub_apply, Pi.mul_apply]
    ring
  have hlim : Tendsto (fun s : ℝ => -(s ^ k * gaussianPDFReal 0 1 s)) atTop (𝓝 0) := by
    have h := (tendsto_gaussianPDFReal_mul_pow_atTop k).neg
    simpa [mul_comm] using h
  have hcont : ContinuousWithinAt (fun s : ℝ => -(s ^ k * gaussianPDFReal 0 1 s)) (Set.Ici x) x :=
    ((continuousAt_id.pow k).mul (hasDerivAt_gaussianPDFReal_one x).continuousAt).neg.continuousWithinAt
  have main := integral_Ioi_of_hasDerivAt_of_tendsto (a := x) hcont hderiv hint hlim
  have hA : IntegrableOn (fun t : ℝ => t ^ (k + 1) * gaussianPDFReal 0 1 t) (Set.Ioi x) :=
    ((integrable_gaussianPDFReal_mul_pow (k + 1)).integrableOn).congr_fun
      (fun t _ => by simp only [Pi.mul_apply]; ring) measurableSet_Ioi
  have hB : IntegrableOn (fun t : ℝ => (k : ℝ) * (t ^ (k - 1) * gaussianPDFReal 0 1 t))
      (Set.Ioi x) :=
    (((integrable_gaussianPDFReal_mul_pow (k - 1)).const_mul (k : ℝ)).integrableOn).congr_fun
      (fun t _ => by simp only [Pi.mul_apply]; ring) measurableSet_Ioi
  have hsplit : ∫ t in Set.Ioi x, (t ^ (k + 1) * gaussianPDFReal 0 1 t -
      (k : ℝ) * (t ^ (k - 1) * gaussianPDFReal 0 1 t))
      = (∫ t in Set.Ioi x, t ^ (k + 1) * gaussianPDFReal 0 1 t)
        - (k : ℝ) * ∫ t in Set.Ioi x, t ^ (k - 1) * gaussianPDFReal 0 1 t := by
    rw [integral_sub hA hB, integral_const_mul]
  rw [hsplit] at main
  have hfin := main
  have hzero : (0:ℝ) - (-(x ^ k * gaussianPDFReal 0 1 x)) = x ^ k * gaussianPDFReal 0 1 x := by ring
  rw [hzero] at hfin
  have hidx : k + 1 - 1 = k := by omega
  have hidx2 : (k + 1 : ℕ) - 2 = k - 1 := by omega
  rw [hidx, hidx2, Nat.cast_add, Nat.cast_one]
  linarith [hfin]

/-- **Polynomial-tail Mills bound** (existential constant):
`∫ t in Ioi x, t^j ρ t ≤ C_j (1 + x^j) ρ x` for all `x ≥ 1`. -/
theorem exists_integral_Ioi_pow_mul_gaussianPDFReal_le (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      ∫ t in Set.Ioi x, t ^ j * gaussianPDFReal 0 1 t
        ≤ C * ((1 + x ^ j) * gaussianPDFReal 0 1 x) := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases j with _ | _ | k
    · -- j = 0
      refine ⟨4, by norm_num, fun x hx => ?_⟩
      have hx0 : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx
      have hρ0 : (0:ℝ) ≤ gaussianPDFReal 0 1 x := gaussianPDFReal_nonneg 0 1 x
      have h := integral_Ioi_gaussianPDFReal_le hx0
      have h2 : gaussianPDFReal 0 1 x / x ≤ gaussianPDFReal 0 1 x := by
        rw [div_le_iff₀ hx0]
        nlinarith [hρ0, hx]
      have h3 : ∫ t in Set.Ioi x, gaussianPDFReal 0 1 t ≤ gaussianPDFReal 0 1 x := h.trans h2
      have hgoal : ∫ t in Set.Ioi x, t ^ 0 * gaussianPDFReal 0 1 t
          = ∫ t in Set.Ioi x, gaussianPDFReal 0 1 t := by
        congr 1
        ext t
        simp only [pow_zero, one_mul]
      rw [hgoal]
      nlinarith [h3, hρ0]
    · -- j = 1
      refine ⟨4, by norm_num, fun x hx => ?_⟩
      have hx0 : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx
      have hρ0 : (0:ℝ) ≤ gaussianPDFReal 0 1 x := gaussianPDFReal_nonneg 0 1 x
      rw [show (fun t : ℝ => t ^ (0 + 1) * gaussianPDFReal 0 1 t)
          = fun t => t * gaussianPDFReal 0 1 t by ext t; ring_nf]
      rw [integral_Ioi_id_mul_gaussianPDFReal]
      have hx1 : (0:ℝ) ≤ x := le_trans zero_le_one hx
      have hprod : gaussianPDFReal 0 1 x ≤ (1 + x) * gaussianPDFReal 0 1 x := by
        have hxρ : (0:ℝ) ≤ x * gaussianPDFReal 0 1 x := mul_nonneg hx1 hρ0
        nlinarith [hxρ]
      have hx1' : x ^ (0 + 1) = x := by ring
      rw [hx1']
      linarith [hprod]
    · -- j = k + 2
      obtain ⟨Ck, hCk0, hCk⟩ := ih k (by omega)
      refine ⟨2 + ((k : ℝ) + 1) * Ck, by positivity, fun x hx => ?_⟩
      have hx0 : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx
      have hρ0 : (0:ℝ) ≤ gaussianPDFReal 0 1 x := gaussianPDFReal_nonneg 0 1 x
      have hid := integral_Ioi_pow_mul_gaussianPDFReal (k + 2) (by omega) x
      have hidx : k + 2 - 1 = k + 1 := by omega
      have hidx2 : k + 2 - 2 = k := by omega
      rw [hid, hidx, hidx2]
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
      have hrec := hCk x hx
      have hxk : (0:ℝ) ≤ x ^ k := pow_nonneg (by linarith) k
      have hxk1 : (0:ℝ) ≤ x ^ (k + 1) := pow_nonneg (by linarith) (k + 1)
      have hxk2 : (0:ℝ) ≤ x ^ (k + 2) := pow_nonneg (by linarith) (k + 2)
      have hk : (0:ℝ) ≤ (k : ℝ) + 1 := by positivity
      have h1 : x ^ (k + 1) * gaussianPDFReal 0 1 x
          ≤ (1 + x ^ (k + 2)) * gaussianPDFReal 0 1 x := by
        have hxle : x ^ (k + 1) ≤ 1 + x ^ (k + 2) := by
          have e : x ^ (k + 2) = x ^ (k + 1) * x := by ring
          have h' : x ^ (k + 1) * 1 ≤ x ^ (k + 1) * x :=
            mul_le_mul_of_nonneg_left hx hxk1
          rw [e]
          linarith
        nlinarith [hxle, hρ0]
      have h2 : ((k : ℝ) + 1) * (Ck * ((1 + x ^ k) * gaussianPDFReal 0 1 x))
          ≤ (((k : ℝ) + 1) * Ck) * ((1 + x ^ (k + 2)) * gaussianPDFReal 0 1 x) := by
        have hA : (1 + x ^ k) * gaussianPDFReal 0 1 x
            ≤ (1 + x ^ (k + 2)) * gaussianPDFReal 0 1 x := by
          have hxle : x ^ k ≤ x ^ (k + 2) := by
            have e : x ^ (k + 2) = x ^ k * (x * x) := by ring
            have hxx : (1:ℝ) ≤ x * x := by nlinarith [hx]
            have h' : x ^ k * 1 ≤ x ^ k * (x * x) := mul_le_mul_of_nonneg_left hxx hxk
            rw [e]
            linarith
          nlinarith [hxle, hρ0]
        have hC : (0:ℝ) ≤ ((k : ℝ) + 1) * Ck := by positivity
        calc ((k : ℝ) + 1) * (Ck * ((1 + x ^ k) * gaussianPDFReal 0 1 x))
            = (((k : ℝ) + 1) * Ck) * ((1 + x ^ k) * gaussianPDFReal 0 1 x) := by ring
          _ ≤ (((k : ℝ) + 1) * Ck) * ((1 + x ^ (k + 2)) * gaussianPDFReal 0 1 x) :=
              mul_le_mul_of_nonneg_left hA hC
      have hsum : x ^ (k + 1) * gaussianPDFReal 0 1 x +
          ((k : ℝ) + 1) * (Ck * ((1 + x ^ k) * gaussianPDFReal 0 1 x))
          ≤ (2 + ((k : ℝ) + 1) * Ck) * ((1 + x ^ (k + 2)) * gaussianPDFReal 0 1 x) := by
        have hB : (0:ℝ) ≤ (1 + x ^ (k + 2)) * gaussianPDFReal 0 1 x := by positivity
        nlinarith [h1, h2, hB]
      have hmul : ((k : ℝ) + 1) * ∫ t in Set.Ioi x, t ^ k * gaussianPDFReal 0 1 t
          ≤ ((k : ℝ) + 1) * (Ck * ((1 + x ^ k) * gaussianPDFReal 0 1 x)) :=
        mul_le_mul_of_nonneg_left hrec hk
      linarith [hmul, hsum]

/-- Branch-free majorant: `(1 + t)^k ≤ 2^(k+1) (1 + t^(2k))` for all `t : ℝ`. -/
theorem one_add_pow_le_two_pow_mul_one_add_even (t : ℝ) (k : ℕ) :
    (1 + t) ^ k ≤ 2 ^ (k + 1) * (1 + t ^ (2 * k)) := by
  have h1 : (1 + t) ^ k ≤ |1 + t| ^ k := by
    calc (1 + t) ^ k ≤ |(1 + t) ^ k| := le_abs_self _
      _ = |1 + t| ^ k := by rw [abs_pow]
  have h2 : |1 + t| ≤ 1 + |t| := by
    have h3 : |1 + t| ≤ |(1:ℝ)| + |t| := abs_add_le 1 t
    simpa using h3
  have h3 : |1 + t| ^ k ≤ (1 + |t|) ^ k :=
    pow_le_pow_left₀ (abs_nonneg _) h2 k
  have h4 : (1 + |t|) ^ k ≤ 2 ^ k * (1 + |t| ^ k) :=
    one_add_pow_le_two_pow_mul |t| (abs_nonneg t) k
  have h5 : |t| ^ k ≤ 1 + t ^ (2 * k) := by
    by_cases ht1 : (1:ℝ) ≤ |t|
    · have h6 : |t| ^ k ≤ |t| ^ (2 * k) := pow_le_pow_right₀ ht1 (by omega)
      have h7 : |t| ^ (2 * k) = t ^ (2 * k) := by
        rw [← abs_pow]
        exact abs_of_nonneg (by rw [show 2 * k = k + k by ring, pow_add]; exact mul_self_nonneg _)
      linarith
    · push_neg at ht1
      have h6 : |t| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg t) ht1.le
      have h7 : (0:ℝ) ≤ t ^ (2 * k) := by rw [show 2 * k = k + k by ring, pow_add]; exact mul_self_nonneg _
      linarith
  have h6 : (0:ℝ) ≤ 1 + t ^ (2 * k) := by
    have h : (0:ℝ) ≤ t ^ (2 * k) := by
      rw [show 2 * k = k + k by ring, pow_add]
      exact mul_self_nonneg _
    linarith
  have h7 : (0:ℝ) ≤ 2 ^ k := pow_nonneg (by norm_num) k
  have h8 : (1 + |t|) ^ k ≤ 2 ^ k * (2 + t ^ (2 * k)) := by
    have := h4
    nlinarith [h5, h7]
  have h9 : 2 ^ k * (2 + t ^ (2 * k)) = 2 ^ (k + 1) + 2 ^ k * t ^ (2 * k) := by ring
  rw [h9] at h8
  have h10 : 2 ^ (k + 1) * (1 + t ^ (2 * k)) = 2 ^ (k + 1) + 2 ^ (k + 1) * t ^ (2 * k) := by ring
  rw [h10]
  have h11 : (0:ℝ) ≤ t ^ (2 * k) := by rw [show 2 * k = k + k by ring, pow_add]; exact mul_self_nonneg _
  have h12 : (0:ℝ) ≤ 2 ^ k := pow_nonneg (by norm_num) k
  have h13 : 2 ^ (k + 1) = 2 ^ k * 2 := by ring
  nlinarith [h1, h3, h8, h11, h12]

/-- **Decay rate of the tail `T`** (with the majorant's integrability as a hypothesis). -/
theorem abs_gueTail_le_mul_gaussianPDFReal {g : ℝ → ℝ} {C Ck : ℝ} {k : ℕ}
    (hgm : Measurable g)
    (hρm : Measurable (fun t : ℝ => gaussianPDFReal 0 1 t))
    (hC0 : 0 ≤ C) (hCk0 : 0 ≤ Ck)
    (hC : ∀ x : ℝ, |g x| ≤ C * (1 + |x|) ^ k)
    (hbig : Integrable (fun t : ℝ => C * ((1 + t) ^ k * gaussianPDFReal 0 1 t)))
    (hCk : ∀ x : ℝ, 1 ≤ x → ∫ t in Set.Ioi x, t ^ (2 * k) * gaussianPDFReal 0 1 t
      ≤ Ck * ((1 + x ^ (2 * k)) * gaussianPDFReal 0 1 x))
    {x : ℝ} (hx : 1 ≤ x) :
    |gueTail g x| ≤ C * 2 ^ (k + 1) * (2 + Ck) * ((1 + x ^ (2 * k)) * gaussianPDFReal 0 1 x) := by
  have hx0 : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hρ0 : (0:ℝ) ≤ gaussianPDFReal 0 1 x := gaussianPDFReal_nonneg 0 1 x
  -- step 1: |T| ≤ ∫_{t>x} |g| ρ
  have step1 : |gueTail g x| ≤ ∫ t in Set.Ioi x, |g t| * gaussianPDFReal 0 1 t := by
    have hT : gueTail g x = ∫ t in Set.Ioi x, g t * gaussianPDFReal 0 1 t := rfl
    rw [hT]
    have hae : ∫ t in Set.Ioi x, |g t * gaussianPDFReal 0 1 t|
        = ∫ t in Set.Ioi x, |g t| * gaussianPDFReal 0 1 t :=
      setIntegral_congr_fun measurableSet_Ioi (fun t _ => by
        rw [abs_mul, abs_of_nonneg (gaussianPDFReal_nonneg 0 1 t)])
    rw [← hae]
    exact abs_integral_le_integral_abs
  -- step 2: |g| ≤ C (1+t)^k on the half-line
  have hle : ∀ t ∈ Set.Ioi x, |g t| * gaussianPDFReal 0 1 t
      ≤ C * ((1 + t) ^ k * gaussianPDFReal 0 1 t) := by
    intro t ht
    have ht0 : (0:ℝ) ≤ t := by linarith [le_trans hx (le_of_lt ht)]
    have h1 : |g t| ≤ C * (1 + t) ^ k := by
      have h := hC t
      rwa [abs_of_nonneg ht0] at h
    have hρt : (0:ℝ) ≤ gaussianPDFReal 0 1 t := gaussianPDFReal_nonneg 0 1 t
    calc |g t| * gaussianPDFReal 0 1 t
        ≤ C * (1 + t) ^ k * gaussianPDFReal 0 1 t := mul_le_mul_of_nonneg_right h1 hρt
      _ = C * ((1 + t) ^ k * gaussianPDFReal 0 1 t) := by ring
  -- the minorant is integrable
  have hmin : IntegrableOn (fun t : ℝ => |g t| * gaussianPDFReal 0 1 t) (Set.Ioi x) := by
    refine hbig.integrableOn.mono' ?_ ?_
    · have hm : Measurable (fun t : ℝ => |g t| * gaussianPDFReal 0 1 t) :=
        hgm.norm.mul hρm
      exact hm.aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hρt : (0:ℝ) ≤ gaussianPDFReal 0 1 t := gaussianPDFReal_nonneg 0 1 t
      have ht0 : (0:ℝ) ≤ t := by linarith [le_trans hx (le_of_lt ht)]
      have h1 : |g t| ≤ C * (1 + t) ^ k := by
        have h := hC t
        rwa [abs_of_nonneg ht0] at h
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) hρt)]
      exact hle t ht
  have step2 : ∫ t in Set.Ioi x, |g t| * gaussianPDFReal 0 1 t
      ≤ ∫ t in Set.Ioi x, C * ((1 + t) ^ k * gaussianPDFReal 0 1 t) :=
    setIntegral_mono_on hmin hbig.integrableOn measurableSet_Ioi hle
  -- step 3: evaluate the majorant integral by the branch-free bound
  have h2k : IntegrableOn (fun t : ℝ => (1 + t ^ (2 * k)) * gaussianPDFReal 0 1 t)
      (Set.Ioi x) := by
    refine (((integrable_gaussianPDFReal_mul_pow 0).add
      (integrable_gaussianPDFReal_mul_pow (2 * k))).integrableOn).congr_fun ?_ measurableSet_Ioi
    intro t _
    simp only [Pi.add_apply, Pi.mul_apply, pow_zero, mul_one]
    ring
  have hbig2 : IntegrableOn (fun t : ℝ => C * 2 ^ (k + 1) *
      ((1 + t ^ (2 * k)) * gaussianPDFReal 0 1 t)) (Set.Ioi x) := by
    refine Integrable.integrableOn ?_
    have hb := ((integrable_gaussianPDFReal_mul_pow 0).add
      (integrable_gaussianPDFReal_mul_pow (2 * k))).const_mul (C * 2 ^ (k + 1))
    refine hb.congr (ae_of_all _ fun t => ?_)
    simp only [Pi.add_apply, Pi.mul_apply, pow_zero, mul_one]
    ring
  have step3 : ∫ t in Set.Ioi x, C * ((1 + t) ^ k * gaussianPDFReal 0 1 t)
      ≤ ∫ t in Set.Ioi x, C * 2 ^ (k + 1) *
          ((1 + t ^ (2 * k)) * gaussianPDFReal 0 1 t) := by
    refine setIntegral_mono_on hbig.integrableOn hbig2 measurableSet_Ioi (fun t ht => ?_)
    have hρt : (0:ℝ) ≤ gaussianPDFReal 0 1 t := gaussianPDFReal_nonneg 0 1 t
    have hb := one_add_pow_le_two_pow_mul_one_add_even t k
    calc C * ((1 + t) ^ k * gaussianPDFReal 0 1 t)
        ≤ C * ((2 ^ (k + 1) * (1 + t ^ (2 * k))) * gaussianPDFReal 0 1 t) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb hρt) hC0
      _ = C * 2 ^ (k + 1) * ((1 + t ^ (2 * k)) * gaussianPDFReal 0 1 t) := by ring
  -- step 4: split the majorant integral
  have e3 : ∫ t in Set.Ioi x, (1 + t ^ (2 * k)) * gaussianPDFReal 0 1 t
      = (∫ t in Set.Ioi x, gaussianPDFReal 0 1 t)
        + ∫ t in Set.Ioi x, t ^ (2 * k) * gaussianPDFReal 0 1 t := by
    have hf : IntegrableOn (fun t : ℝ => gaussianPDFReal 0 1 t) (Set.Ioi x) :=
      ((integrable_gaussianPDFReal_mul_pow 0).integrableOn).congr_fun
        (fun t _ => by simp only [Pi.mul_apply]; ring) measurableSet_Ioi
    have hg : IntegrableOn (fun t : ℝ => t ^ (2 * k) * gaussianPDFReal 0 1 t) (Set.Ioi x) :=
      ((integrable_gaussianPDFReal_mul_pow (2 * k)).integrableOn).congr_fun
        (fun t _ => by simp only [Pi.mul_apply]; ring) measurableSet_Ioi
    have key : ∫ t in Set.Ioi x, ((fun t : ℝ => gaussianPDFReal 0 1 t) t
          + (fun t : ℝ => t ^ (2 * k) * gaussianPDFReal 0 1 t) t)
        = (∫ t in Set.Ioi x, gaussianPDFReal 0 1 t)
          + ∫ t in Set.Ioi x, t ^ (2 * k) * gaussianPDFReal 0 1 t :=
      integral_add hf hg
    rw [← key]
    congr 1
    ext t
    simp only
    ring
  have e1 : ∫ t in Set.Ioi x, C * 2 ^ (k + 1) * ((1 + t ^ (2 * k)) * gaussianPDFReal 0 1 t)
      = C * 2 ^ (k + 1) * ∫ t in Set.Ioi x, ((1 + t ^ (2 * k)) * gaussianPDFReal 0 1 t) :=
    integral_const_mul (C * 2 ^ (k + 1))
      (fun t : ℝ => (1 + t ^ (2 * k)) * gaussianPDFReal 0 1 t)
  have hsplit : ∫ t in Set.Ioi x, C * 2 ^ (k + 1) * ((1 + t ^ (2 * k)) * gaussianPDFReal 0 1 t)
      = C * 2 ^ (k + 1) * ((∫ t in Set.Ioi x, gaussianPDFReal 0 1 t)
          + ∫ t in Set.Ioi x, t ^ (2 * k) * gaussianPDFReal 0 1 t) := by
    rw [e1, e3]
  -- step 5: bound the two tails
  have hmass : ∫ t in Set.Ioi x, gaussianPDFReal 0 1 t ≤ gaussianPDFReal 0 1 x := by
    refine (integral_Ioi_gaussianPDFReal_le hx0).trans ?_
    rw [div_le_iff₀ hx0]
    nlinarith [hρ0, hx]
  have htail := hCk x hx
  have hB : (0:ℝ) ≤ (1 + x ^ (2 * k)) * gaussianPDFReal 0 1 x := by positivity
  have hsum : (∫ t in Set.Ioi x, gaussianPDFReal 0 1 t)
      + ∫ t in Set.Ioi x, t ^ (2 * k) * gaussianPDFReal 0 1 t
      ≤ (2 + Ck) * ((1 + x ^ (2 * k)) * gaussianPDFReal 0 1 x) := by
    have h1 : ∫ t in Set.Ioi x, gaussianPDFReal 0 1 t
        ≤ (1 + x ^ (2 * k)) * gaussianPDFReal 0 1 x := by
      have hxk : (0:ℝ) ≤ x ^ (2 * k) := by
        rw [show 2 * k = k + k by ring, pow_add]
        exact mul_self_nonneg _
      have h2 : gaussianPDFReal 0 1 x ≤ (1 + x ^ (2 * k)) * gaussianPDFReal 0 1 x := by
        nlinarith [hρ0, hxk]
      linarith [hmass, h2]
    have h2 : (1 + Ck) * ((1 + x ^ (2 * k)) * gaussianPDFReal 0 1 x)
        ≤ (2 + Ck) * ((1 + x ^ (2 * k)) * gaussianPDFReal 0 1 x) :=
      mul_le_mul_of_nonneg_right (by linarith) hB
    have e : (1 + x ^ (2 * k)) * gaussianPDFReal 0 1 x
          + Ck * ((1 + x ^ (2 * k)) * gaussianPDFReal 0 1 x)
        = (1 + Ck) * ((1 + x ^ (2 * k)) * gaussianPDFReal 0 1 x) := by ring
    calc (∫ t in Set.Ioi x, gaussianPDFReal 0 1 t)
          + ∫ t in Set.Ioi x, t ^ (2 * k) * gaussianPDFReal 0 1 t
        ≤ (1 + x ^ (2 * k)) * gaussianPDFReal 0 1 x
            + Ck * ((1 + x ^ (2 * k)) * gaussianPDFReal 0 1 x) := add_le_add h1 htail
      _ = (1 + Ck) * ((1 + x ^ (2 * k)) * gaussianPDFReal 0 1 x) := e
      _ ≤ (2 + Ck) * ((1 + x ^ (2 * k)) * gaussianPDFReal 0 1 x) := h2
  calc |gueTail g x| ≤ ∫ t in Set.Ioi x, C * ((1 + t) ^ k * gaussianPDFReal 0 1 t) :=
        step1.trans step2
    _ ≤ ∫ t in Set.Ioi x, C * 2 ^ (k + 1) *
          ((1 + t ^ (2 * k)) * gaussianPDFReal 0 1 t) := step3
    _ = C * 2 ^ (k + 1) * ((∫ t in Set.Ioi x, gaussianPDFReal 0 1 t)
          + ∫ t in Set.Ioi x, t ^ (2 * k) * gaussianPDFReal 0 1 t) := hsplit
    _ ≤ C * 2 ^ (k + 1) * (2 + Ck) * ((1 + x ^ (2 * k)) * gaussianPDFReal 0 1 x) := by
        have hC2 : (0:ℝ) ≤ C * 2 ^ (k + 1) := by positivity
        have hstep := mul_le_mul_of_nonneg_left hsum hC2
        have e4 : C * 2 ^ (k + 1) * ((2 + Ck) * ((1 + x ^ (2 * k)) * gaussianPDFReal 0 1 x))
            = C * 2 ^ (k + 1) * (2 + Ck) * ((1 + x ^ (2 * k)) * gaussianPDFReal 0 1 x) := by ring
        exact hstep.trans (le_of_eq e4)

/-- `(1 + |x|)^n * ρ x` is Lebesgue-integrable. -/
theorem integrable_one_add_abs_pow_mul_gaussianPDFReal (n : ℕ) :
    Integrable (fun x : ℝ => (1 + |x|) ^ n * gaussianPDFReal 0 1 x) := by
  have hmaj : Integrable (fun x : ℝ => 2 ^ (n + 1) * (1 + x ^ (2 * n)) * gaussianPDFReal 0 1 x) := by
    have hb := ((integrable_gaussianPDFReal_mul_pow 0).add
      (integrable_gaussianPDFReal_mul_pow (2 * n))).const_mul (2 ^ (n + 1))
    refine hb.congr (ae_of_all _ fun x => ?_)
    simp only [Pi.add_apply, Pi.mul_apply, pow_zero, one_mul]
    ring
  refine hmaj.mono' ?_ ?_
  · have hpoly : Measurable (fun x : ℝ => (1 + |x|) ^ n) :=
      (continuous_const.add continuous_abs).pow n |>.measurable
    exact (hpoly.mul (by fun_prop : Measurable (fun x : ℝ => gaussianPDFReal 0 1 x))).aestronglyMeasurable
  · filter_upwards with x
    have hρ : (0:ℝ) ≤ gaussianPDFReal 0 1 x := gaussianPDFReal_nonneg 0 1 x
    have hb := one_add_pow_le_two_pow_mul_one_add_even |x| n
    have hxx : (0:ℝ) ≤ x ^ (2 * n) := by
      rw [show 2 * n = n + n by ring, pow_add]
      exact mul_self_nonneg _
    have habs : |x| ^ (2 * n) = x ^ (2 * n) := by
      rw [← abs_pow]
      exact abs_of_nonneg hxx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) hρ)]
    rw [habs] at hb
    calc (1 + |x|) ^ n * gaussianPDFReal 0 1 x
        ≤ (2 ^ (n + 1) * (1 + x ^ (2 * n))) * gaussianPDFReal 0 1 x :=
          mul_le_mul_of_nonneg_right hb hρ
      _ = 2 ^ (n + 1) * (1 + x ^ (2 * n)) * gaussianPDFReal 0 1 x := by ring

/-- `x · g · T` is Lebesgue-integrable when `|T| ≤ M ρ` and `g` has polynomial growth. -/
theorem integrable_id_mul_g_mul_gueTail {g : ℝ → ℝ} {C M : ℝ} {k : ℕ}
    (hgm : Measurable g) (hTm : Measurable (fun x : ℝ => gueTail g x))
    (hC0 : 0 ≤ C) (hC : ∀ x : ℝ, |g x| ≤ C * (1 + |x|) ^ k)
    (hM0 : 0 ≤ M) (hM : ∀ x : ℝ, |gueTail g x| ≤ M * gaussianPDFReal 0 1 x) :
    Integrable (fun x => x * (g x * gueTail g x)) := by
  have hmaj : Integrable (fun x : ℝ => C * M * ((1 + |x|) ^ (k + 1) * gaussianPDFReal 0 1 x)) :=
    (integrable_one_add_abs_pow_mul_gaussianPDFReal (k + 1)).const_mul (C * M)
  refine hmaj.mono' ?_ ?_
  · exact (measurable_id.mul (hgm.mul hTm)).aestronglyMeasurable
  · filter_upwards with x
    have hρ : (0:ℝ) ≤ gaussianPDFReal 0 1 x := gaussianPDFReal_nonneg 0 1 x
    have habs : (0:ℝ) ≤ |x| := abs_nonneg x
    have h1 : |g x| ≤ C * (1 + |x|) ^ k := hC x
    have h2 : |gueTail g x| ≤ M * gaussianPDFReal 0 1 x := hM x
    have hxk : (0:ℝ) ≤ (1 + |x|) ^ k := by positivity
    have hnn : (0:ℝ) ≤ |x| * |g x| * |gueTail g x| := by positivity
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have hstep1 : |x| ≤ 1 + |x| := by linarith [abs_nonneg x]
    have hxk : (0:ℝ) ≤ (1 + |x|) ^ k := by positivity
    have hbig1 : (0:ℝ) ≤ 1 + |x| := by linarith [abs_nonneg x]
    calc |x| * (|g x| * |gueTail g x|)
        = |x| * |g x| * |gueTail g x| := by ring
      _ ≤ (1 + |x|) * (C * (1 + |x|) ^ k) * (M * gaussianPDFReal 0 1 x) := by
          apply mul_le_mul
          · exact mul_le_mul hstep1 h1 (abs_nonneg _) hbig1
          · exact h2
          · positivity
          · positivity
      _ = C * M * ((1 + |x|) ^ (k + 1) * gaussianPDFReal 0 1 x) := by
          rw [pow_succ]
          ring

end

end GUEStrongConvergence
