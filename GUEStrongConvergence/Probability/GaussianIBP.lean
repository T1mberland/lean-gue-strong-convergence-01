/-
# Gaussian integration by parts on the real line (Part II, checkpoint P1)

For the standard Gaussian measure `gaussianReal 0 1` on `ℝ`, this file proves the
integration-by-parts identity (equation (2.1) of the Part II handoff)

`∫ x, x * f x ∂(gaussianReal 0 1) = ∫ x, deriv f x ∂(gaussianReal 0 1)`

for every differentiable `f` whose derivative is recorded in `f'`, under the natural
integrability and decay hypotheses:

* `f' * ρ` and `x ↦ x * f x * ρ x` are integrable, where `ρ = gaussianPDFReal 0 1` is the
  Gaussian density;
* `x ↦ f x * ρ x` tends to `0` at `±∞`.

The proof rewrites both sides as integrals against the density (Mathlib's
`integral_gaussianReal_eq_integral_smul`), notes `ρ' x = -x * ρ x`
(`hasDerivAt_gaussianPDFReal_one`), and applies the integration-by-parts identity on
`(-∞, ∞)` (`MeasureTheory.integral_mul_deriv_eq_deriv_mul`).
-/
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace ENNReal NNReal Topology

namespace GUEStrongConvergence

noncomputable section

/-- The Gaussian density `gaussianPDFReal 0 1` is the normalised exponential
`(√(2π))⁻¹ * exp(-x²/2)`. -/
lemma gaussianPDFReal_zero_one (x : ℝ) :
    gaussianPDFReal 0 1 x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2) := by
  simp [gaussianPDFReal, NNReal.coe_one, sq]

/-- The logarithmic derivative of the Gaussian density: `ρ' x = -x * ρ x`. -/
theorem hasDerivAt_gaussianPDFReal_one (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have h1 : HasDerivAt (fun y : ℝ => -(y - 0) ^ 2 / (2 * 1)) (-(2 * (x - 0)) / (2 * 1)) x := by
    have := ((((hasDerivAt_id x).sub_const 0).pow 2).neg).div_const (2 * 1)
    simpa using this
  have h2 : HasDerivAt (fun y : ℝ => Real.exp (-(y - 0) ^ 2 / (2 * 1)))
      (Real.exp (-(x - 0) ^ 2 / (2 * 1)) * (-(2 * (x - 0)) / (2 * 1))) x := h1.exp
  have h3 := h2.const_mul ((Real.sqrt (2 * Real.pi))⁻¹)
  convert h3 using 1
  · ext y
    simp [gaussianPDFReal, NNReal.coe_one]
  · simp [gaussianPDFReal, NNReal.coe_one]
    ring

/-- `deriv` form of `hasDerivAt_gaussianPDFReal_one`. -/
theorem deriv_gaussianPDFReal_one (x : ℝ) :
    deriv (gaussianPDFReal 0 1) x = -x * gaussianPDFReal 0 1 x :=
  (hasDerivAt_gaussianPDFReal_one x).deriv

/-- **Gaussian integration by parts** (Part II, (2.1)):
`∫ x, x * f x ∂(gaussianReal 0 1) = ∫ x, f' x ∂(gaussianReal 0 1)` whenever `f'` is the
derivative of `f`, the products `f' * ρ` and `x * f * ρ` are integrable, and `f * ρ → 0` at
`±∞`. -/
theorem gaussian_integration_by_parts {f f' : ℝ → ℝ}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hff' : Integrable (fun x => f' x * gaussianPDFReal 0 1 x))
    (hxf : Integrable (fun x => x * f x * gaussianPDFReal 0 1 x))
    (hbot : Tendsto (fun x => f x * gaussianPDFReal 0 1 x) atBot (𝓝 0))
    (htop : Tendsto (fun x => f x * gaussianPDFReal 0 1 x) atTop (𝓝 0)) :
    ∫ x, x * f x ∂(gaussianReal 0 1) = ∫ x, f' x ∂(gaussianReal 0 1) := by
  have hρ : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  have hL : ∫ x, x * f x ∂(gaussianReal 0 1)
      = ∫ x, gaussianPDFReal 0 1 x * (x * f x) := by
    rw [integral_gaussianReal_eq_integral_smul (μ := 0) (v := 1) hρ]
    simp [smul_eq_mul]
  have hR : ∫ x, f' x ∂(gaussianReal 0 1) = ∫ x, gaussianPDFReal 0 1 x * f' x := by
    rw [integral_gaussianReal_eq_integral_smul (μ := 0) (v := 1) hρ]
    simp [smul_eq_mul]
  rw [hL, hR]
  have hneg : Integrable (fun x => -(f x * (-x * gaussianPDFReal 0 1 x))) := by
    refine hxf.congr (ae_of_all _ fun x => ?_)
    ring
  have hρ' : Integrable (fun x => f x * (-x * gaussianPDFReal 0 1 x)) := by
    simpa using hneg.neg
  have hff'2 : Integrable (f' * gaussianPDFReal 0 1) := hff'
  have hIBP := integral_mul_deriv_eq_deriv_mul
    (u := f) (v := gaussianPDFReal 0 1) (u' := f')
    (v' := fun x => -x * gaussianPDFReal 0 1 x)
    (fun x _ => hderiv x) (fun x _ => hasDerivAt_gaussianPDFReal_one x)
    hρ' hff'2 hbot htop
  calc ∫ x, gaussianPDFReal 0 1 x * (x * f x)
      = ∫ x, -(f x * (-x * gaussianPDFReal 0 1 x)) := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        ring
    _ = -(∫ x, f x * (-x * gaussianPDFReal 0 1 x)) := integral_neg _
    _ = -(0 - 0 - ∫ x, f' x * gaussianPDFReal 0 1 x) := by rw [hIBP]
    _ = ∫ x, gaussianPDFReal 0 1 x * f' x := by
        rw [show (∫ x, gaussianPDFReal 0 1 x * f' x)
            = ∫ x, f' x * gaussianPDFReal 0 1 x from
          integral_congr_ae (ae_of_all _ fun x => by ring)]
        ring


/-- Density form of the 1-D Gaussian IBP. -/
theorem gaussian_integration_by_parts_density
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] {f f' : ℝ → A}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hff' : Integrable (fun x => gaussianPDFReal 0 1 x • f' x))
    (hxf : Integrable (fun x => x • (gaussianPDFReal 0 1 x • f x)))
    (hbot : Tendsto (fun x => gaussianPDFReal 0 1 x • f x) atBot (𝓝 0))
    (htop : Tendsto (fun x => gaussianPDFReal 0 1 x • f x) atTop (𝓝 0)) :
    ∫ x, x • (gaussianPDFReal 0 1 x • f x) = ∫ x, gaussianPDFReal 0 1 x • f' x := by
  have hsm : (∫ x, x • (gaussianPDFReal 0 1 x • f x))
      = ∫ x, (x * gaussianPDFReal 0 1 x) • f x := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show x • (gaussianPDFReal 0 1 x • f x) = (x * gaussianPDFReal 0 1 x) • f x
    rw [smul_smul]
  rw [hsm]
  have hv : ∀ x, HasDerivAt (fun y : ℝ => gaussianPDFReal 0 1 y • (1 : A))
      ((-x * gaussianPDFReal 0 1 x) • (1 : A)) x :=
    fun x => (hasDerivAt_gaussianPDFReal_one x).smul_const 1
  have huv' : Integrable (f * fun x => (-x * gaussianPDFReal 0 1 x) • (1 : A)) := by
    refine hxf.neg.congr (ae_of_all _ fun x => ?_)
    simp only [Pi.mul_apply, Pi.neg_apply]
    rw [Algebra.mul_smul_comm, mul_one, smul_smul,
      show (-x * gaussianPDFReal 0 1 x) = -(x * gaussianPDFReal 0 1 x) by ring, neg_smul]
  have hu'v : Integrable (f' * fun x => gaussianPDFReal 0 1 x • (1 : A)) := by
    refine hff'.congr (ae_of_all _ fun x => ?_)
    simp only [Pi.mul_apply]
    rw [Algebra.mul_smul_comm, mul_one]
  have hbot' : Tendsto (f * fun x => gaussianPDFReal 0 1 x • (1 : A)) atBot (𝓝 0) := by
    refine hbot.congr' ?_
    filter_upwards with x
    simp only [Pi.mul_apply]
    rw [Algebra.mul_smul_comm, mul_one]
  have htop' : Tendsto (f * fun x => gaussianPDFReal 0 1 x • (1 : A)) atTop (𝓝 0) := by
    refine htop.congr' ?_
    filter_upwards with x
    simp only [Pi.mul_apply]
    rw [Algebra.mul_smul_comm, mul_one]
  have hIBP := integral_mul_deriv_eq_deriv_mul
    (u := f) (v := fun y => gaussianPDFReal 0 1 y • (1 : A))
    (u' := f') (v' := fun x => (-x * gaussianPDFReal 0 1 x) • (1 : A))
    (fun x _ => hderiv x) (fun x _ => hv x) huv' hu'v hbot' htop'
  have h1 : (∫ x, (x * gaussianPDFReal 0 1 x) • f x)
      = -∫ x, (-x * gaussianPDFReal 0 1 x) • f x := by
    rw [← integral_neg]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show (x * gaussianPDFReal 0 1 x) • f x = -((-x * gaussianPDFReal 0 1 x) • f x)
    have hx : (-x * gaussianPDFReal 0 1 x) = -(x * gaussianPDFReal 0 1 x) := by ring
    rw [hx, neg_smul, neg_neg]
  have hbridge : (∫ x, (-x * gaussianPDFReal 0 1 x) • f x)
      = ∫ x, f x * ((-x * gaussianPDFReal 0 1 x) • (1 : A)) := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show (-x * gaussianPDFReal 0 1 x) • f x = f x * ((-x * gaussianPDFReal 0 1 x) • (1 : A))
    rw [Algebra.mul_smul_comm, mul_one]
  calc ∫ x, (x * gaussianPDFReal 0 1 x) • f x
      = -∫ x, (-x * gaussianPDFReal 0 1 x) • f x := h1
    _ = -(∫ x, f x * ((-x * gaussianPDFReal 0 1 x) • (1 : A))) := by rw [hbridge]
    _ = -(0 - 0 - ∫ x, f' x * (gaussianPDFReal 0 1 x • (1 : A))) := by rw [hIBP]
    _ = ∫ x, gaussianPDFReal 0 1 x • f' x := by
        rw [show (∫ x, f' x * (gaussianPDFReal 0 1 x • (1 : A)))
            = ∫ x, gaussianPDFReal 0 1 x • f' x from by
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          show f' x * (gaussianPDFReal 0 1 x • (1 : A)) = gaussianPDFReal 0 1 x • f' x
          rw [Algebra.mul_smul_comm, mul_one]]
        abel

/-- **Gaussian integration by parts, algebra-valued form** (the form needed for matrix-valued
observables such as resolvents): for a complete normed `ℝ`-algebra `A` and `f : ℝ → A` with
derivative `f'`,

`∫ x, x • f x ∂(gaussianReal 0 1) = ∫ x, f' x ∂(gaussianReal 0 1)`,

under integrability of `x ↦ ρ x • f' x` and `x ↦ x • (ρ x • f x)`, and decay of
`x ↦ ρ x • f x` at `±∞`, where `ρ = gaussianPDFReal 0 1`. -/
theorem gaussian_integration_by_parts_algebra
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] {f f' : ℝ → A}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hff' : Integrable (fun x => gaussianPDFReal 0 1 x • f' x))
    (hxf : Integrable (fun x => x • (gaussianPDFReal 0 1 x • f x)))
    (hbot : Tendsto (fun x => gaussianPDFReal 0 1 x • f x) atBot (𝓝 0))
    (htop : Tendsto (fun x => gaussianPDFReal 0 1 x • f x) atTop (𝓝 0)) :
    ∫ x, x • f x ∂(gaussianReal 0 1) = ∫ x, f' x ∂(gaussianReal 0 1) := by
  have hρ : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  have hL : ∫ x, x • f x ∂(gaussianReal 0 1)
      = ∫ x, x • (gaussianPDFReal 0 1 x • f x) := by
    rw [integral_gaussianReal_eq_integral_smul (μ := 0) (v := 1) (f := fun x => x • f x) hρ]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show gaussianPDFReal 0 1 x • x • f x = x • (gaussianPDFReal 0 1 x • f x)
    rw [smul_smul, smul_smul, mul_comm]
  have hR : ∫ x, f' x ∂(gaussianReal 0 1) = ∫ x, gaussianPDFReal 0 1 x • f' x := by
    rw [integral_gaussianReal_eq_integral_smul (μ := 0) (v := 1) (f := f') hρ]
  rw [hL, hR]
  exact gaussian_integration_by_parts_density hderiv hff' hxf hbot htop

/-- Second logarithmic derivative of the Gaussian density: differentiating `ρ' = -x ρ` gives
`ρ'' x = (x² - 1) ρ x`. This is the coefficient appearing in the second-order (Laplacian) term of
the HT05 master equation. -/
theorem hasDerivAt_deriv_gaussianPDFReal_one (x : ℝ) :
    HasDerivAt (fun y => -y * gaussianPDFReal 0 1 y)
      ((x ^ 2 - 1) * gaussianPDFReal 0 1 x) x := by
  have h := (hasDerivAt_id x).mul (hasDerivAt_gaussianPDFReal_one x)
  have h2 : HasDerivAt (fun y => -(y * gaussianPDFReal 0 1 y))
      (-(1 * gaussianPDFReal 0 1 x + x * (-x * gaussianPDFReal 0 1 x))) x := h.neg
  rw [show (-(1 * gaussianPDFReal 0 1 x + x * (-x * gaussianPDFReal 0 1 x)))
      = (x ^ 2 - 1) * gaussianPDFReal 0 1 x by ring] at h2
  convert h2 using 1
  ext y
  ring

/-- `deriv` form of `hasDerivAt_deriv_gaussianPDFReal_one`. -/
theorem deriv_deriv_gaussianPDFReal_one (x : ℝ) :
    deriv (fun y => deriv (gaussianPDFReal 0 1) y) x = (x ^ 2 - 1) * gaussianPDFReal 0 1 x := by
  have hfun : (fun y => deriv (gaussianPDFReal 0 1) y) = fun y => -y * gaussianPDFReal 0 1 y := by
    funext y
    exact deriv_gaussianPDFReal_one y
  rw [hfun]
  exact (hasDerivAt_deriv_gaussianPDFReal_one x).deriv

/-- Density form of the second-order Gaussian IBP. -/
theorem gaussian_second_order_integration_by_parts_density
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] {f f' f'' : ℝ → A}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hderiv' : ∀ x, HasDerivAt f' (f'' x) x)
    (hxf' : Integrable (fun x => x • (gaussianPDFReal 0 1 x • f' x)))
    (hff'' : Integrable (fun x => gaussianPDFReal 0 1 x • f'' x))
    (hx2f : Integrable (fun x => ((x ^ 2 - 1) * gaussianPDFReal 0 1 x) • f x))
    (hbot' : Tendsto (fun x => gaussianPDFReal 0 1 x • f' x) atBot (𝓝 0))
    (htop' : Tendsto (fun x => gaussianPDFReal 0 1 x • f' x) atTop (𝓝 0))
    (hbot2 : Tendsto (fun x => (-x * gaussianPDFReal 0 1 x) • f x) atBot (𝓝 0))
    (htop2 : Tendsto (fun x => (-x * gaussianPDFReal 0 1 x) • f x) atTop (𝓝 0)) :
    ∫ x, ((x ^ 2 - 1) * gaussianPDFReal 0 1 x) • f x
      = ∫ x, gaussianPDFReal 0 1 x • f'' x := by
  -- first order IBP applied to f' gives the right-hand side
  have hR : ∫ x, (x * gaussianPDFReal 0 1 x) • f' x
      = ∫ x, gaussianPDFReal 0 1 x • f'' x := by
    rw [show (fun x => (x * gaussianPDFReal 0 1 x) • f' x)
        = fun x => x • (gaussianPDFReal 0 1 x • f' x) from by
      funext x; rw [smul_smul]]
    exact gaussian_integration_by_parts_density hderiv' hff'' hxf' hbot' htop'
  rw [← hR]
  -- IBP with v = -(x * ρ)
  have hv : ∀ x, HasDerivAt (fun y : ℝ => (-y * gaussianPDFReal 0 1 y) • (1 : A))
      (((x ^ 2 - 1) * gaussianPDFReal 0 1 x) • (1 : A)) x :=
    fun x => (hasDerivAt_deriv_gaussianPDFReal_one x).smul_const 1
  have huv' : Integrable (f * fun x => ((x ^ 2 - 1) * gaussianPDFReal 0 1 x) • (1 : A)) := by
    refine hx2f.congr (ae_of_all _ fun x => ?_)
    simp only [Pi.mul_apply]
    rw [Algebra.mul_smul_comm, mul_one]
  have hu'v : Integrable (f' * fun x => (-x * gaussianPDFReal 0 1 x) • (1 : A)) := by
    refine hxf'.neg.congr (ae_of_all _ fun x => ?_)
    simp only [Pi.mul_apply, Pi.neg_apply]
    have hxr : (-x * gaussianPDFReal 0 1 x) = -(x * gaussianPDFReal 0 1 x) := by ring
    rw [Algebra.mul_smul_comm, mul_one, smul_smul, hxr, neg_smul]
  have hbot2' : Tendsto (f * fun x => (-x * gaussianPDFReal 0 1 x) • (1 : A)) atBot (𝓝 0) := by
    refine hbot2.congr' ?_
    filter_upwards with x
    simp only [Pi.mul_apply]
    rw [Algebra.mul_smul_comm, mul_one]
  have htop2' : Tendsto (f * fun x => (-x * gaussianPDFReal 0 1 x) • (1 : A)) atTop (𝓝 0) := by
    refine htop2.congr' ?_
    filter_upwards with x
    simp only [Pi.mul_apply]
    rw [Algebra.mul_smul_comm, mul_one]
  have hIBP := integral_mul_deriv_eq_deriv_mul
    (u := f) (v := fun y => (-y * gaussianPDFReal 0 1 y) • (1 : A))
    (u' := f') (v' := fun x => ((x ^ 2 - 1) * gaussianPDFReal 0 1 x) • (1 : A))
    (fun x _ => hderiv x) (fun x _ => hv x) huv' hu'v hbot2' htop2'
  have hbridge : (∫ x, ((x ^ 2 - 1) * gaussianPDFReal 0 1 x) • f x)
      = ∫ x, f x * (((x ^ 2 - 1) * gaussianPDFReal 0 1 x) • (1 : A)) := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show ((x ^ 2 - 1) * gaussianPDFReal 0 1 x) • f x
      = f x * (((x ^ 2 - 1) * gaussianPDFReal 0 1 x) • (1 : A))
    rw [Algebra.mul_smul_comm, mul_one]
  have hkey : (-∫ x, f' x * ((-x * gaussianPDFReal 0 1 x) • (1 : A)))
      = ∫ x, (x * gaussianPDFReal 0 1 x) • f' x := by
    rw [← integral_neg]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show -(f' x * ((-x * gaussianPDFReal 0 1 x) • (1 : A))) = (x * gaussianPDFReal 0 1 x) • f' x
    have hxr : (-x * gaussianPDFReal 0 1 x) = -(x * gaussianPDFReal 0 1 x) := by ring
    rw [Algebra.mul_smul_comm, mul_one, hxr, neg_smul, neg_neg]
  rw [hbridge, hIBP]
  simp only [neg_zero, zero_sub]
  exact hkey

end

end GUEStrongConvergence
