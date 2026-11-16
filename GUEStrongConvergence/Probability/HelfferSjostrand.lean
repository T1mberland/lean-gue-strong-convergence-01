/-
# The Helffer--Sjöstrand almost-analytic extension and Cauchy--Pompeiu

This file builds the Cauchy--Pompeiu (Helffer--Sjöstrand) representation of a smooth compactly
supported function as a `∂̄` double integral, using Mathlib's rectangle Cauchy--Pompeiu theorem
`Complex.integral_boundary_rect_of_hasFDerivAt_real_off_countable`, whose hypotheses only require
*real* differentiability on the closed rectangle.  This is what makes the real axis admissible as a
boundary of the contour, and it removes the "real-axis crossing" obstruction for the
spectral-exclusion argument.

## Main results (all unconditional)

* `almostAnalyticExt f` — the first-order almost-analytic extension
  `z ↦ f (Re z) + i (Im z) f' (Re z)`; `almostAnalyticExt_ofReal` (agrees with `f` on `ℝ`);
* `hasFDerivAt_almostAnalyticExt` — its real Fréchet derivative, with
  `fderiv_almostAnalyticExt_one`, `fderiv_almostAnalyticExt_I`, and hence
  `dbar_almostAnalyticExt`:
  `I • fderiv (ext f) z 1 - fderiv (ext f) z I = -(Im z) · f'' (Re z)`;
  `norm_dbar_almostAnalyticExt_le` records the resulting estimate `≤ |Im z| · ‖f''‖`;
* `yCut` — the `ContDiffBump` cutoff, and `almostAnalyticExtCut f`
  (`z ↦ (f x + i y f' x) ρ y`), which is smooth, compactly supported, agrees with `f` on `ℝ`
  (`almostAnalyticExtCut_ofReal`), and whose `∂̄` vanishes identically near the real axis:
  `dbar_almostAnalyticExtCut` and the bound `norm_dbar_almostAnalyticExtCut_le`
  (`‖∂̄‖ ≤ |Im z| · ‖f''‖` for `|Im z| < 1`).  This linear vanishing is what beats the
  `|Im z|⁻⁵` blow-up of the sharp resolvent comparison near the real axis;
* `rectBoundary` — the oriented boundary functional
  `∫ f(x+c i) - ∫ f(x+d i) + i ∫ f(b+y i) - i ∫ f(a+y i)`, with additivity under vertical and
  horizontal cuts (`rectBoundary_add_vert`, `rectBoundary_add_horiz`) and translation covariance
  (`rectBoundary_comp_sub`);
* `rectBoundary_eq_doubleIntegral` — **Cauchy–Pompeiu on a rectangle**: the boundary functional
  equals the `∂̄` double integral of `I • fderiv g z 1 - fderiv g z I` (which is `2 i ∂̄g`);
* `rectBoundary_quot_eq` — Cauchy–Pompeiu for the weight `(z - lam)⁻¹` on a rectangle avoiding
  `lam`, with integrand `pompeiuIntegrand F lam z = (I • fderiv F z 1 - fderiv F z I) (z - lam)⁻¹`;
* `rectBoundary_sub_hole_eq` — **the rectangle with a rectangular hole**: the boundary functional of
  a big rectangle minus that of a square hole centred at `lam` equals the `∂̄` integral over the
  four surrounding rectangles.  This is the real-axis-crossing device: the hole is centred on the
  (possibly real) point `lam`, and only real differentiability is used;
* `hasDerivAt_inv_add_mul_I`, `hasDerivAt_add_mul_I_inv` — explicit real antiderivatives of
  `t ↦ (t + i a)⁻¹` and `t ↦ (a + i t)⁻¹` (for `a ≠ 0`);
* `rectBoundary_inv_sub_eq_two_pi_I` — **the residue computation**: for every `ε > 0`,
  `∮_{∂([lam.re-ε,lam.re+ε] × [lam.im-ε,lam.im+ε])} dz/(z - lam) = 2π i`.
  This pins the normalization: with `∂̄F = (F_x + i F_y)/2` and
  `I • fderiv F z 1 - fderiv F z I = i F_x - F_y = 2 i ∂̄F`, the representation is
  `f λ = -(1/π) ∫∫ ∂̄F(z)/(z-λ) = (i/2π) ∫∫ (i F_x - F_y)/(z-λ)`
  (the constant `1/π` in front of the *real* integrand is off by `i/2`).

## Main theorem (verified, no `sorry`)

`pompeiu_plane`:
`f lam = (i / 2π) * ∫ x, ∫ y, pompeiuIntegrand (almostAnalyticExtCut f) (lam : ℂ) (x + iy)`
for `f : ℝ → ℝ` of class `C²` with compact support and every real `lam`.  The proof assembles

* `tendsto_boundary_hole` — `rectBoundary (F / (· - lam))` over the shrinking square tends to
  `2π i F lam` (residue `rectBoundary_inv_sub_eq_two_pi_I` plus the `O(ε)` Lipschitz remainder
  `norm_rectBoundary_hole_le`);
* `tendsto_area_hole` — the sum of the four slab integrals tends to the integral over the big
  rectangle (the hole integral is `≤ M · 4ε²` by `norm_setIntegral_le_of_norm_le_const`, and
  `bigRectSet = holeSurround ∪ holeSet` by `bigRectSet_eq_holeSurround_union`, with
  `setIntegral_holeSurround_eq` splitting the integral over the four slabs);
* the master identity `rectBoundary_sub_hole_eq` at a rectangle whose boundary avoids the support,
  where the boundary functional vanishes (`hbnd0`), and the identification of the rectangle
  integral with the plane integral (`setIntegral_prod` plus the support bound
  `notMem_tsupport_almostAnalyticExtCut_of_lt_abs_im`).

The remaining deliverables (trace/operator form and the smooth Lemma M for the GUE pencil) are
*not* in this file.
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open MeasureTheory Set Filter Topology intervalIntegral
open Complex
open scoped Real Topology NNReal ENNReal Interval

namespace GUEStrongConvergence

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

/-! ## The almost-analytic extension -/

/-- The first-order (Helffer--Sjöstrand) almost-analytic extension of `f : ℝ → ℝ`:
`z ↦ f (Re z) + i (Im z) f' (Re z)`.  It agrees with `f` on the real axis and its `∂̄` vanishes
linearly on the real axis. -/
def almostAnalyticExt (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  (f z.re : ℂ) + I * (z.im : ℂ) * ((deriv f z.re : ℝ) : ℂ)

@[simp]
lemma almostAnalyticExt_ofReal (f : ℝ → ℝ) (x : ℝ) :
    almostAnalyticExt f (x : ℂ) = (f x : ℂ) := by
  simp [almostAnalyticExt]

lemma almostAnalyticExt_apply (f : ℝ → ℝ) (z : ℂ) :
    almostAnalyticExt f z = (f z.re : ℂ) + I * (z.im : ℂ) * ((deriv f z.re : ℝ) : ℂ) := rfl

/-! ## The real Fréchet derivative of the extension -/

/-- The explicit real Fréchet derivative of `z ↦ (g (Re z) : ℂ)`. -/
lemma hasFDerivAt_ofReal_comp_re {g : ℝ → ℝ} {g' : ℝ} {z : ℂ} (hg : HasDerivAt g g' z.re) :
    HasFDerivAt (fun w : ℂ => (g w.re : ℂ))
      (ContinuousLinearMap.smulRight Complex.reCLM (g' : ℂ)) z := by
  have h : HasFDerivAt ((fun y : ℝ => g y) ∘ Complex.reCLM) (g' • Complex.reCLM) z :=
    hg.comp_hasFDerivAt z (ContinuousLinearMap.hasFDerivAt Complex.reCLM)
  have h2 : HasFDerivAt (fun w : ℂ => ((g w.re : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (g' • Complex.reCLM)) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z h
  convert h2 using 1
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, Complex.ofRealCLM_apply, Complex.reCLM_apply,
    Complex.ofReal_mul, Complex.real_smul, smul_eq_mul]
  ring

/-- The explicit real Fréchet derivative of `z ↦ (Im z : ℂ)`. -/
lemma hasFDerivAt_ofReal_comp_im (z : ℂ) :
    HasFDerivAt (fun w : ℂ => (w.im : ℂ))
      (ContinuousLinearMap.smulRight Complex.imCLM (1 : ℂ)) z := by
  have h2 : HasFDerivAt (fun w : ℂ => ((w.im : ℝ) : ℂ))
      (Complex.ofRealCLM.comp Complex.imCLM) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z (ContinuousLinearMap.hasFDerivAt Complex.imCLM)
  convert h2 using 1
  ext v
  simp [ContinuousLinearMap.smulRight_apply]

/-- **Real Fréchet derivative of the almost-analytic extension.** -/
theorem hasFDerivAt_almostAnalyticExt {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (z : ℂ) :
    HasFDerivAt (almostAnalyticExt f)
      (ContinuousLinearMap.smulRight Complex.reCLM
          (((deriv f z.re : ℝ) : ℂ) + I * (z.im : ℂ) * ((deriv (deriv f) z.re : ℝ) : ℂ)) +
        ContinuousLinearMap.smulRight Complex.imCLM (I * ((deriv f z.re : ℝ) : ℂ))) z := by
  have hf' : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hfd : Differentiable ℝ (deriv f) :=
    hf.differentiable_deriv_two
  have h1 : HasFDerivAt (fun z : ℂ => (f z.re : ℂ))
      (ContinuousLinearMap.smulRight Complex.reCLM ((deriv f z.re : ℝ) : ℂ)) z :=
    hasFDerivAt_ofReal_comp_re (hf'.differentiableAt.hasDerivAt)
  have h2 : HasFDerivAt (fun z : ℂ => ((z.im : ℝ) : ℂ))
      (ContinuousLinearMap.smulRight Complex.imCLM (1 : ℂ)) z :=
    hasFDerivAt_ofReal_comp_im z
  have h3 : HasFDerivAt (fun z : ℂ => ((deriv f z.re : ℝ) : ℂ))
      (ContinuousLinearMap.smulRight Complex.reCLM ((deriv (deriv f) z.re : ℝ) : ℂ)) z :=
    hasFDerivAt_ofReal_comp_re (hfd.differentiableAt.hasDerivAt)
  have h4 : HasFDerivAt (fun z : ℂ => ((z.im : ℝ) : ℂ) * ((deriv f z.re : ℝ) : ℂ))
      ((((z.im : ℝ) : ℂ)) • ContinuousLinearMap.smulRight Complex.reCLM
          ((deriv (deriv f) z.re : ℝ) : ℂ)
        + (((deriv f z.re : ℝ) : ℂ)) • ContinuousLinearMap.smulRight Complex.imCLM (1 : ℂ)) z :=
    h2.mul h3
  have h5 : HasFDerivAt (fun z : ℂ => I * (((z.im : ℝ) : ℂ) * ((deriv f z.re : ℝ) : ℂ)))
      (I • ((((z.im : ℝ) : ℂ)) • ContinuousLinearMap.smulRight Complex.reCLM
          ((deriv (deriv f) z.re : ℝ) : ℂ)
        + (((deriv f z.re : ℝ) : ℂ)) • ContinuousLinearMap.smulRight Complex.imCLM (1 : ℂ))) z :=
    h4.const_smul I
  have h6 : HasFDerivAt (fun z : ℂ => (f z.re : ℂ)
      + I * (((z.im : ℝ) : ℂ) * ((deriv f z.re : ℝ) : ℂ)))
      (ContinuousLinearMap.smulRight Complex.reCLM ((deriv f z.re : ℝ) : ℂ)
        + I • ((((z.im : ℝ) : ℂ)) • ContinuousLinearMap.smulRight Complex.reCLM
            ((deriv (deriv f) z.re : ℝ) : ℂ)
          + (((deriv f z.re : ℝ) : ℂ)) • ContinuousLinearMap.smulRight Complex.imCLM (1 : ℂ))) z :=
    h1.add h5
  convert h6 using 1
  · funext w
    simp only [almostAnalyticExt_apply]
    ring
  · ext v
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, Complex.reCLM_apply, Complex.imCLM_apply,
      Complex.real_smul, smul_eq_mul]
    ring

/-- The value of the derivative of the extension in the real direction. -/
lemma fderiv_almostAnalyticExt_one {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (z : ℂ) :
    fderiv ℝ (almostAnalyticExt f) z 1 =
      ((deriv f z.re : ℝ) : ℂ) + I * (z.im : ℂ) * ((deriv (deriv f) z.re : ℝ) : ℂ) := by
  rw [(hasFDerivAt_almostAnalyticExt hf z).fderiv]
  simp [ContinuousLinearMap.smulRight_apply]

/-- The value of the derivative of the extension in the imaginary direction. -/
lemma fderiv_almostAnalyticExt_I {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (z : ℂ) :
    fderiv ℝ (almostAnalyticExt f) z I = I * ((deriv f z.re : ℝ) : ℂ) := by
  rw [(hasFDerivAt_almostAnalyticExt hf z).fderiv]
  simp [ContinuousLinearMap.smulRight_apply]

/-- **The `∂̄` of the almost-analytic extension vanishes linearly on the real axis.** -/
theorem dbar_almostAnalyticExt {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (z : ℂ) :
    I • fderiv ℝ (almostAnalyticExt f) z 1 - fderiv ℝ (almostAnalyticExt f) z I =
      -((z.im : ℂ) * ((deriv (deriv f) z.re : ℝ) : ℂ)) := by
  rw [fderiv_almostAnalyticExt_one hf, fderiv_almostAnalyticExt_I hf]
  have hI : I * I = (-1 : ℂ) := Complex.I_mul_I
  calc I * (((deriv f z.re : ℝ) : ℂ) + I * (z.im : ℂ) * ((deriv (deriv f) z.re : ℝ) : ℂ))
        - I * ((deriv f z.re : ℝ) : ℂ)
      = I * I * ((z.im : ℂ) * ((deriv (deriv f) z.re : ℝ) : ℂ)) := by ring
    _ = -((z.im : ℂ) * ((deriv (deriv f) z.re : ℝ) : ℂ)) := by rw [hI]; ring

/-- Pointwise bound on the `∂̄` term: it is controlled by `|Im z|` times a bound on `f''`. -/
theorem norm_dbar_almostAnalyticExt_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (z : ℂ) {M : ℝ}
    (hM : ∀ x, ‖deriv (deriv f) x‖ ≤ M) :
    ‖I • fderiv ℝ (almostAnalyticExt f) z 1 - fderiv ℝ (almostAnalyticExt f) z I‖
      ≤ |z.im| * M := by
  rw [dbar_almostAnalyticExt hf z, norm_neg, norm_mul, Complex.norm_real, Complex.norm_real]
  have h := hM z.re
  rw [Real.norm_eq_abs] at h
  exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

/-! ## Cut-off extension with compact support -/

/-- The standard smooth bump on `ℝ` used as the vertical cut-off. -/
def yBump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

/-- A smooth cut-off in the imaginary direction which is `1` on `[-1,1]` and supported in `[-2,2]`. -/
def yCut : ℝ → ℝ := yBump.toFun

lemma yCut_one_of_mem {y : ℝ} (hy : |y| ≤ 1) : yCut y = 1 := by
  have h : y ∈ Metric.closedBall (0 : ℝ) yBump.rIn := by
    simpa [yBump, Real.closedBall_zero_eq_Icc, abs_le] using hy
  simpa [yCut] using ContDiffBump.one_of_mem_closedBall (f := yBump) h

lemma yCut_zero_of_two_le {y : ℝ} (hy : 2 ≤ |y|) : yCut y = 0 := by
  have h : yBump.rOut ≤ dist y (0 : ℝ) := by
    simpa [yBump, Real.dist_eq] using hy
  simpa [yCut] using ContDiffBump.zero_of_le_dist (f := yBump) h

lemma contDiff_yCut (n : ℕ∞) : ContDiff ℝ n yCut := by
  simpa [yCut] using ContDiffBump.contDiff (f := yBump) (n := n)

lemma hasCompactSupport_yCut : HasCompactSupport yCut := by
  simpa [yCut] using ContDiffBump.hasCompactSupport (f := yBump)

lemma yCut_nonneg (y : ℝ) : 0 ≤ yCut y := by
  simpa [yCut] using ContDiffBump.nonneg (f := yBump) (x := y)

/-- The cut-off almost-analytic extension `z ↦ (f x + i y f' x) ρ y`.  It is smooth, compactly
supported, agrees with `f` on the real axis, and its `∂̄` vanishes on a neighbourhood of the real
axis. -/
def almostAnalyticExtCut (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  almostAnalyticExt f z * (yCut z.im : ℂ)

lemma almostAnalyticExtCut_ofReal (f : ℝ → ℝ) (x : ℝ) :
    almostAnalyticExtCut f (x : ℂ) = (f x : ℂ) := by
  rw [almostAnalyticExtCut, almostAnalyticExt_ofReal, Complex.ofReal_im,
    yCut_one_of_mem (by norm_num : |(0 : ℝ)| ≤ 1)]
  simp

/-- The support of the cut-off extension is contained in a compact product set. -/
lemma support_almostAnalyticExtCut_subset {f : ℝ → ℝ} :
    Function.support (almostAnalyticExtCut f) ⊆
      (fun p : ℝ × ℝ => ((p.1 : ℂ) + (p.2 : ℂ) * I)) '' (tsupport f ×ˢ tsupport yCut) := by
  intro z hz
  have hzre : z.re ∈ tsupport f := by
    by_contra h
    have hf0 : f z.re = 0 := by
      by_contra h'
      exact h (subset_tsupport f h')
    have hd0 : deriv f z.re = 0 := deriv_of_notMem_tsupport h
    apply hz
    simp [almostAnalyticExtCut, almostAnalyticExt, hf0, hd0]
  have hzim : z.im ∈ tsupport yCut := by
    by_contra h
    have h0 : yCut z.im = 0 := by
      by_contra h'
      exact h (subset_tsupport yCut h')
    apply hz
    simp [almostAnalyticExtCut, h0]
  exact ⟨(z.re, z.im), ⟨hzre, hzim⟩, by simp⟩

lemma hasCompactSupport_almostAnalyticExtCut {f : ℝ → ℝ} (hfc : HasCompactSupport f) :
    HasCompactSupport (almostAnalyticExtCut f) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (K := (fun p : ℝ × ℝ => ((p.1 : ℂ) + (p.2 : ℂ) * I)) '' (tsupport f ×ˢ tsupport yCut))
  · have h1 : IsCompact (tsupport yCut) := hasCompactSupport_yCut
    have h2 : IsCompact (tsupport f) := hfc
    exact (h2.prod h1).image (by fun_prop)
  · exact support_almostAnalyticExtCut_subset

/-- The real Fréchet derivative of `z ↦ (g (Im z) : ℂ)`. -/
lemma hasFDerivAt_ofReal_comp_im' {g : ℝ → ℝ} {g' : ℝ} {z : ℂ} (hg : HasDerivAt g g' z.im) :
    HasFDerivAt (fun w : ℂ => (g w.im : ℂ))
      (ContinuousLinearMap.smulRight Complex.imCLM (g' : ℂ)) z := by
  have h : HasFDerivAt ((fun y : ℝ => g y) ∘ Complex.imCLM) (g' • Complex.imCLM) z :=
    hg.comp_hasFDerivAt z (ContinuousLinearMap.hasFDerivAt Complex.imCLM)
  have h2 : HasFDerivAt (fun w : ℂ => ((g w.im : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (g' • Complex.imCLM)) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z h
  convert h2 using 1
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, Complex.ofRealCLM_apply, Complex.imCLM_apply,
    Complex.ofReal_mul, Complex.real_smul, smul_eq_mul]
  ring

/-- **The `∂̄` of the cut-off extension:** the extension term with the second derivative is damped
by `ρ`, and the extra term coming from `ρ'` is supported away from the real axis. -/
theorem dbar_almostAnalyticExtCut {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {ρ : ℝ → ℝ}
    (hρ : Differentiable ℝ ρ) (z : ℂ) :
    I • fderiv ℝ (fun w => almostAnalyticExt f w * (ρ w.im : ℂ)) z 1
        - fderiv ℝ (fun w => almostAnalyticExt f w * (ρ w.im : ℂ)) z I =
      (ρ z.im : ℂ) * (-((z.im : ℂ) * ((deriv (deriv f) z.re : ℝ) : ℂ)))
        - ((deriv ρ z.im : ℝ) : ℂ) * almostAnalyticExt f z := by
  have hA := hasFDerivAt_almostAnalyticExt hf z
  have hr : HasFDerivAt (fun w : ℂ => (ρ w.im : ℂ))
      (ContinuousLinearMap.smulRight Complex.imCLM ((deriv ρ z.im : ℝ) : ℂ)) z :=
    hasFDerivAt_ofReal_comp_im' (hρ.differentiableAt.hasDerivAt)
  have hG : HasFDerivAt (fun w => almostAnalyticExt f w * (ρ w.im : ℂ))
      (almostAnalyticExt f z • ContinuousLinearMap.smulRight Complex.imCLM ((deriv ρ z.im : ℝ) : ℂ)
        + ((ρ z.im : ℝ) : ℂ) • fderiv ℝ (almostAnalyticExt f) z) z := by
    have h := hA.mul hr
    rw [hA.fderiv]
    exact h
  have key : I • fderiv ℝ (fun w => almostAnalyticExt f w * (ρ w.im : ℂ)) z 1
        - fderiv ℝ (fun w => almostAnalyticExt f w * (ρ w.im : ℂ)) z I
      = (ρ z.im : ℂ) * (I • (fderiv ℝ (almostAnalyticExt f) z) 1
          - (fderiv ℝ (almostAnalyticExt f) z) I)
        - ((deriv ρ z.im : ℝ) : ℂ) * almostAnalyticExt f z := by
    rw [hG.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, Complex.imCLM_apply]
    simp [Complex.one_im, Complex.I_im]
    ring
  rw [key, dbar_almostAnalyticExt hf z]

/-- **Linear vanishing of the `∂̄` term on the real axis.**  On the strip `|Im z| < 1` the extra
term involving `ρ'` is absent, so the `∂̄` term of the cut-off extension is bounded by `|Im z|`
times a bound on `f''`.  This is the estimate that beats the `|Im z|⁻⁵` blow-up of the sharp
resolvent comparison near the real axis. -/
theorem norm_dbar_almostAnalyticExtCut_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {z : ℂ}
    (hz : |z.im| < 1) {M : ℝ} (hM : ∀ x, ‖deriv (deriv f) x‖ ≤ M) :
    ‖I • fderiv ℝ (almostAnalyticExtCut f) z 1 - fderiv ℝ (almostAnalyticExtCut f) z I‖
      ≤ |z.im| * M := by
  have hρd : Differentiable ℝ yCut := (contDiff_yCut 1).differentiable (by norm_num)
  have hmem : z.im ∈ Metric.ball (0 : ℝ) yBump.rIn := by
    have h1 : yBump.rIn = 1 := rfl
    rw [h1, Real.ball_zero_eq_Ioo]
    exact abs_lt.mp hz
  have hρ1 : yCut =ᶠ[𝓝 z.im] 1 := by
    simpa [yCut] using ContDiffBump.eventuallyEq_one_of_mem_ball (f := yBump) hmem
  have hderiv : deriv yCut z.im = 0 := by
    rw [Filter.EventuallyEq.deriv_eq hρ1]
    simp
  change ‖I • (fderiv ℝ (fun w : ℂ => almostAnalyticExt f w * (yCut w.im : ℂ)) z) 1
      - (fderiv ℝ (fun w : ℂ => almostAnalyticExt f w * (yCut w.im : ℂ)) z) I‖ ≤ |z.im| * M
  rw [dbar_almostAnalyticExtCut hf hρd z, hderiv]
  simp only [Complex.ofReal_zero, zero_mul, sub_zero, norm_mul, norm_neg, Complex.norm_real,
    Real.norm_eq_abs]
  have hb : |deriv (deriv f) z.re| ≤ M := by
    have := hM z.re
    rwa [Real.norm_eq_abs] at this
  have hρle : |yCut z.im| ≤ 1 := by
    rw [abs_of_nonneg (yCut_nonneg z.im)]
    simpa [yCut] using ContDiffBump.le_one (f := yBump) (x := z.im)
  calc |yCut z.im| * (|z.im| * |deriv (deriv f) z.re|)
      ≤ 1 * (|z.im| * M) := by gcongr
    _ = |z.im| * M := by ring

/-! ## The oriented rectangle boundary functional and its additivity -/

/-- The oriented boundary functional of the rectangle `[a,b] × [c,d]`, written in the exact shape
used by `Complex.integral_boundary_rect_of_differentiableOn_real`. -/
def rectBoundary (g : ℂ → ℂ) (a b c d : ℝ) : ℂ :=
  (∫ x : ℝ in a..b, g ((x : ℂ) + (c : ℂ) * I)) - (∫ x : ℝ in a..b, g ((x : ℂ) + (d : ℂ) * I))
    + I * (∫ y : ℝ in c..d, g ((b : ℂ) + (y : ℂ) * I))
    - I * (∫ y : ℝ in c..d, g ((a : ℂ) + (y : ℂ) * I))

/-- **Cauchy–Pompeiu on a rectangle** in boundary-functional form.  On the right-hand side the
integrand is `i ∂_x g - ∂_y g`, which is `2i ∂̄g`; only *real* differentiability is required, so the
real axis can be a boundary edge. -/
theorem rectBoundary_eq_doubleIntegral {g : ℂ → ℂ} {a b c d : ℝ}
    (hdiff : DifferentiableOn ℝ g ([[a, b]] ×ℂ [[c, d]]))
    (hint : IntegrableOn (fun z => I • fderiv ℝ g z 1 - fderiv ℝ g z I)
      ([[a, b]] ×ℂ [[c, d]])) :
    rectBoundary g a b c d =
      ∫ x : ℝ in a..b, ∫ y : ℝ in c..d,
        (I • fderiv ℝ g ((x : ℂ) + (y : ℂ) * I) 1 - fderiv ℝ g ((x : ℂ) + (y : ℂ) * I) I) := by
  have h := Complex.integral_boundary_rect_of_differentiableOn_real g ⟨a, c⟩ ⟨b, d⟩ hdiff hint
  simpa [rectBoundary] using h

/-- Additivity of the boundary functional under a vertical cut. -/
lemma rectBoundary_add_vert {g : ℂ → ℂ} {a b c d m : ℝ}
    (h1 : IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + (c : ℂ) * I)) volume a m)
    (h2 : IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + (c : ℂ) * I)) volume m b)
    (h3 : IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + (d : ℂ) * I)) volume a m)
    (h4 : IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + (d : ℂ) * I)) volume m b) :
    rectBoundary g a b c d = rectBoundary g a m c d + rectBoundary g m b c d := by
  unfold rectBoundary
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2,
    ← intervalIntegral.integral_add_adjacent_intervals h3 h4]
  ring

/-- Additivity of the boundary functional under a horizontal cut. -/
lemma rectBoundary_add_horiz {g : ℂ → ℂ} {a b c d m : ℝ}
    (h1 : IntervalIntegrable (fun y : ℝ => g ((a : ℂ) + (y : ℂ) * I)) volume c m)
    (h2 : IntervalIntegrable (fun y : ℝ => g ((a : ℂ) + (y : ℂ) * I)) volume m d)
    (h3 : IntervalIntegrable (fun y : ℝ => g ((b : ℂ) + (y : ℂ) * I)) volume c m)
    (h4 : IntervalIntegrable (fun y : ℝ => g ((b : ℂ) + (y : ℂ) * I)) volume m d) :
    rectBoundary g a b c d = rectBoundary g a b c m + rectBoundary g a b m d := by
  unfold rectBoundary
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2,
    ← intervalIntegral.integral_add_adjacent_intervals h3 h4]
  ring

/-- The real Fréchet derivative of `z ↦ (z - λ)⁻¹`. -/
lemma fderiv_inv_sub (z lam : ℂ) (hz : z ≠ lam) :
    fderiv ℝ (fun w : ℂ => (w - lam)⁻¹) z = (-((z - lam)⁻¹) ^ 2) • (1 : ℂ →L[ℝ] ℂ) := by
  have hderiv : HasDerivAt (fun w : ℂ => (w - lam)⁻¹) (-((z - lam)⁻¹) ^ 2) z := by
    have h0 : HasDerivAt (fun w : ℂ => w - lam) 1 z := (hasDerivAt_id z).sub_const lam
    have h1 := h0.inv (sub_ne_zero.mpr hz)
    convert h1 using 1
    field_simp
  exact hderiv.complexToReal_fderiv.fderiv

/-- **The `∂̄` of `F / (· - λ)` away from `λ`:** the weight is holomorphic, so the `∂̄` term is
multiplied by `(z - λ)⁻¹`. -/
lemma dbar_div_sub {F : ℂ → ℂ} {lam z : ℂ} (hz : z ≠ lam) (hF : DifferentiableAt ℝ F z) :
    I • fderiv ℝ (fun w => F w / (w - lam)) z 1 - fderiv ℝ (fun w => F w / (w - lam)) z I
      = (I • fderiv ℝ F z 1 - fderiv ℝ F z I) * (z - lam)⁻¹ := by
  have hderiv : HasDerivAt (fun w : ℂ => (w - lam)⁻¹) (-((z - lam)⁻¹) ^ 2) z := by
    have h0 : HasDerivAt (fun w : ℂ => w - lam) 1 z := (hasDerivAt_id z).sub_const lam
    have h1 := h0.inv (sub_ne_zero.mpr hz)
    convert h1 using 1
    field_simp
  have hw : HasFDerivAt (fun w : ℂ => (w - lam)⁻¹) ((-((z - lam)⁻¹) ^ 2) • (1 : ℂ →L[ℝ] ℂ)) z :=
    hderiv.complexToReal_fderiv
  have hG : HasFDerivAt (fun w => F w * (w - lam)⁻¹)
      (F z • ((-((z - lam)⁻¹) ^ 2) • (1 : ℂ →L[ℝ] ℂ)) + (z - lam)⁻¹ • fderiv ℝ F z) z :=
    hF.hasFDerivAt.mul hw
  rw [show (fun w => F w / (w - lam)) = fun w => F w * (w - lam)⁻¹ from rfl, hG.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, one_apply_eq_self]
  ring

/-! ## Cauchy–Pompeiu on a rectangle with a rectangular hole -/

/-- The `∂̄`-integrand of the Cauchy–Pompeiu formula for the weight `(z - lam)⁻¹`. -/
def pompeiuIntegrand (F : ℂ → ℂ) (lam z : ℂ) : ℂ :=
  (I • fderiv ℝ F z 1 - fderiv ℝ F z I) * (z - lam)⁻¹

/-- Continuity of the `∂̄` integrand on any set avoiding `lam`. -/
lemma continuousOn_pompeiuIntegrand {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) {lam : ℂ} {s : Set ℂ}
    (hs : ∀ z ∈ s, z ≠ lam) : ContinuousOn (pompeiuIntegrand F lam) s := by
  have hfd : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by norm_num)
  have hfd1 : Continuous (fun z : ℂ => fderiv ℝ F z 1) := hfd.clm_apply continuous_const
  have hfdI : Continuous (fun z : ℂ => fderiv ℝ F z I) := hfd.clm_apply continuous_const
  have h1 : ContinuousOn (fun z : ℂ => I • fderiv ℝ F z 1 - fderiv ℝ F z I) s :=
    ((continuous_const.mul hfd1).sub hfdI).continuousOn
  exact h1.mul (ContinuousOn.inv₀ (by fun_prop) (fun z hz => sub_ne_zero.mpr (hs z hz)))

/-- **Cauchy–Pompeiu on a rectangle** for the weight `(z - lam)⁻¹`, for a rectangle that avoids
`lam`. -/
theorem rectBoundary_quot_eq {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) {lam : ℂ} {a b c d : ℝ}
    (havoid : ∀ z ∈ [[a, b]] ×ℂ [[c, d]], z ≠ lam) :
    rectBoundary (fun z => F z / (z - lam)) a b c d =
      ∫ x : ℝ in a..b, ∫ y : ℝ in c..d, pompeiuIntegrand F lam ((x : ℂ) + (y : ℂ) * I) := by
  change rectBoundary (fun z => F z * (z - lam)⁻¹) a b c d =
      ∫ x : ℝ in a..b, ∫ y : ℝ in c..d, pompeiuIntegrand F lam ((x : ℂ) + (y : ℂ) * I)
  have hdiff : DifferentiableOn ℝ (fun z => F z * (z - lam)⁻¹) ([[a, b]] ×ℂ [[c, d]]) := by
    have h1 : DifferentiableOn ℝ F ([[a, b]] ×ℂ [[c, d]]) :=
      (hF.differentiable (by norm_num)).differentiableOn
    have h2 : DifferentiableOn ℝ (fun z : ℂ => (z - lam)⁻¹) ([[a, b]] ×ℂ [[c, d]]) :=
      DifferentiableOn.inv (by fun_prop) (fun z hz => sub_ne_zero.mpr (havoid z hz))
    exact h1.mul h2
  have hQ : IntegrableOn (fun z => pompeiuIntegrand F lam z) ([[a, b]] ×ℂ [[c, d]]) :=
    (continuousOn_pompeiuIntegrand hF havoid).integrableOn_compact
      (isCompact_Icc.reProdIm isCompact_Icc)
  have heq : ∀ z ∈ [[a, b]] ×ℂ [[c, d]],
      I • fderiv ℝ (fun z => F z * (z - lam)⁻¹) z 1
        - fderiv ℝ (fun z => F z * (z - lam)⁻¹) z I = pompeiuIntegrand F lam z := by
    intro z hz
    have h := dbar_div_sub (F := F) (havoid z hz) (hF.differentiable (by norm_num)).differentiableAt
    simpa [pompeiuIntegrand, div_eq_mul_inv, smul_eq_mul] using h
  have hint : IntegrableOn (fun z => I • fderiv ℝ (fun z => F z * (z - lam)⁻¹) z 1
      - fderiv ℝ (fun z => F z * (z - lam)⁻¹) z I) ([[a, b]] ×ℂ [[c, d]]) := by
    refine hQ.congr_fun_ae ?_
    have hmeas : MeasurableSet ([[a, b]] ×ℂ [[c, d]]) :=
      (isCompact_Icc.reProdIm isCompact_Icc).isClosed.measurableSet
    filter_upwards [ae_restrict_mem hmeas] with z hz
    exact (heq z hz).symm
  rw [rectBoundary_eq_doubleIntegral hdiff hint]
  refine intervalIntegral.integral_congr fun x hx => intervalIntegral.integral_congr fun y hy => ?_
  have hz : ((x : ℂ) + (y : ℂ) * I) ∈ [[a, b]] ×ℂ [[c, d]] := by
    refine ⟨?_, ?_⟩
    · simpa using hx
    · simpa using hy
  exact heq _ hz

lemma ne_of_im_ne {x c : ℝ} {lam : ℂ} (h : c ≠ lam.im) : ((x : ℂ) + (c : ℂ) * I) ≠ lam := by
  intro hc
  exact h (by simpa using congrArg Complex.im hc)

lemma ne_of_re_ne {x c : ℝ} {lam : ℂ} (h : x ≠ lam.re) : ((x : ℂ) + (c : ℂ) * I) ≠ lam := by
  intro hc
  exact h (by simpa using congrArg Complex.re hc)

/-- The edge functions of the quotiented weight are interval integrable on segments that avoid
`lam`. -/
lemma intervalIntegrable_quot_segment {F : ℂ → ℂ} (hF : Continuous F) {lam : ℂ} {c : ℝ} {a b : ℝ}
    (h : ∀ x ∈ Set.uIcc a b, ((x : ℂ) + (c : ℂ) * I) ≠ lam) :
    IntervalIntegrable (fun x : ℝ => F ((x : ℂ) + (c : ℂ) * I) /
      (((x : ℂ) + (c : ℂ) * I) - lam)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  refine ContinuousOn.div (hF.comp_continuousOn (by fun_prop)) (by fun_prop) ?_
  intro x hx
  exact sub_ne_zero.mpr (h x hx)

/-- Interval integrability of the horizontal edge functions. -/
lemma intervalIntegrable_quot_segment_horiz {F : ℂ → ℂ} (hF : Continuous F) {lam : ℂ} {c : ℝ}
    {a b : ℝ} (h : c ≠ lam.re) :
    IntervalIntegrable (fun y : ℝ => F ((c : ℂ) + (y : ℂ) * I) /
      (((c : ℂ) + (y : ℂ) * I) - lam)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  refine ContinuousOn.div (hF.comp_continuousOn (by fun_prop)) (by fun_prop) ?_
  intro y _
  exact sub_ne_zero.mpr (ne_of_re_ne h)

/-- **Cauchy–Pompeiu on a rectangle with a rectangular hole.**  The boundary functional of the big
rectangle minus that of the hole equals the `∂̄` integral over the four rectangles surrounding the
hole.  This is the real-axis-crossing device: the hole is centred at `lam`. -/
theorem rectBoundary_sub_hole_eq {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) {a b c d : ℝ} {lam : ℂ}
    {ε : ℝ} (hε : 0 < ε) (ha : a < lam.re - ε) (hb : lam.re + ε < b)
    (hc : c < lam.im - ε) (hd : lam.im + ε < d) :
    rectBoundary (fun z => F z / (z - lam)) a b c d
      - rectBoundary (fun z => F z / (z - lam)) (lam.re - ε) (lam.re + ε)
          (lam.im - ε) (lam.im + ε)
      = (∫ x : ℝ in a..lam.re - ε, ∫ y : ℝ in c..d,
            pompeiuIntegrand F lam ((x : ℂ) + (y : ℂ) * I))
        + (∫ x : ℝ in lam.re + ε..b, ∫ y : ℝ in c..d,
            pompeiuIntegrand F lam ((x : ℂ) + (y : ℂ) * I))
        + (∫ x : ℝ in lam.re - ε..lam.re + ε, ∫ y : ℝ in lam.im + ε..d,
            pompeiuIntegrand F lam ((x : ℂ) + (y : ℂ) * I))
        + (∫ x : ℝ in lam.re - ε..lam.re + ε, ∫ y : ℝ in c..lam.im - ε,
            pompeiuIntegrand F lam ((x : ℂ) + (y : ℂ) * I)) := by
  have hFc : Continuous F := hF.continuous
  have hcne : c ≠ lam.im := by linarith
  have hdne : d ≠ lam.im := by linarith
  have hane : a ≠ lam.re := by linarith
  have hbne : b ≠ lam.re := by linarith
  have hm1ne : lam.re - ε ≠ lam.re := by linarith
  have hm2ne : lam.re + ε ≠ lam.re := by linarith
  -- Step 1: vertical split at `lam.re - ε`.
  have hs1 : rectBoundary (fun z => F z / (z - lam)) a b c d
      = rectBoundary (fun z => F z / (z - lam)) a (lam.re - ε) c d
        + rectBoundary (fun z => F z / (z - lam)) (lam.re - ε) b c d := by
    refine rectBoundary_add_vert ?_ ?_ ?_ ?_
    · exact intervalIntegrable_quot_segment hFc (fun x _ => ne_of_im_ne hcne)
    · exact intervalIntegrable_quot_segment hFc (fun x _ => ne_of_im_ne hcne)
    · exact intervalIntegrable_quot_segment hFc (fun x _ => ne_of_im_ne hdne)
    · exact intervalIntegrable_quot_segment hFc (fun x _ => ne_of_im_ne hdne)
  -- Step 2: vertical split at `lam.re + ε`.
  have hs2 : rectBoundary (fun z => F z / (z - lam)) (lam.re - ε) b c d
      = rectBoundary (fun z => F z / (z - lam)) (lam.re - ε) (lam.re + ε) c d
        + rectBoundary (fun z => F z / (z - lam)) (lam.re + ε) b c d := by
    refine rectBoundary_add_vert ?_ ?_ ?_ ?_
    · exact intervalIntegrable_quot_segment hFc (fun x _ => ne_of_im_ne hcne)
    · exact intervalIntegrable_quot_segment hFc (fun x _ => ne_of_im_ne hcne)
    · exact intervalIntegrable_quot_segment hFc (fun x _ => ne_of_im_ne hdne)
    · exact intervalIntegrable_quot_segment hFc (fun x _ => ne_of_im_ne hdne)
  -- Step 3: horizontal split of the middle strip.
  have hs3 : rectBoundary (fun z => F z / (z - lam)) (lam.re - ε) (lam.re + ε) c d
      = rectBoundary (fun z => F z / (z - lam)) (lam.re - ε) (lam.re + ε) c (lam.im - ε)
        + rectBoundary (fun z => F z / (z - lam)) (lam.re - ε) (lam.re + ε)
            (lam.im - ε) (lam.im + ε)
        + rectBoundary (fun z => F z / (z - lam)) (lam.re - ε) (lam.re + ε) (lam.im + ε) d := by
    have h1 : rectBoundary (fun z => F z / (z - lam)) (lam.re - ε) (lam.re + ε) c d
        = rectBoundary (fun z => F z / (z - lam)) (lam.re - ε) (lam.re + ε) c (lam.im - ε)
          + rectBoundary (fun z => F z / (z - lam)) (lam.re - ε) (lam.re + ε) (lam.im - ε) d :=
      rectBoundary_add_horiz (m := lam.im - ε)
        (intervalIntegrable_quot_segment_horiz hFc hm1ne)
        (intervalIntegrable_quot_segment_horiz hFc hm1ne)
        (intervalIntegrable_quot_segment_horiz hFc hm2ne)
        (intervalIntegrable_quot_segment_horiz hFc hm2ne)
    have h2 : rectBoundary (fun z => F z / (z - lam)) (lam.re - ε) (lam.re + ε) (lam.im - ε) d
        = rectBoundary (fun z => F z / (z - lam)) (lam.re - ε) (lam.re + ε)
            (lam.im - ε) (lam.im + ε)
          + rectBoundary (fun z => F z / (z - lam)) (lam.re - ε) (lam.re + ε) (lam.im + ε) d :=
      rectBoundary_add_horiz (m := lam.im + ε)
        (intervalIntegrable_quot_segment_horiz hFc hm1ne)
        (intervalIntegrable_quot_segment_horiz hFc hm1ne)
        (intervalIntegrable_quot_segment_horiz hFc hm2ne)
        (intervalIntegrable_quot_segment_horiz hFc hm2ne)
    rw [h1, h2]
    abel
  -- avoid conditions for the four pieces
  have hL : ∀ z ∈ [[a, lam.re - ε]] ×ℂ [[c, d]], z ≠ lam := by
    intro z hz
    have h1 : z.re ≤ lam.re - ε :=
      (Set.mem_Icc.mp (by simpa [Set.uIcc_of_le (le_of_lt ha)] using hz.1)).2
    intro hc
    rw [hc] at h1
    linarith
  have hRt : ∀ z ∈ [[lam.re + ε, b]] ×ℂ [[c, d]], z ≠ lam := by
    intro z hz
    have h1 : lam.re + ε ≤ z.re :=
      (Set.mem_Icc.mp (by simpa [Set.uIcc_of_le (le_of_lt hb)] using hz.1)).1
    intro hc
    rw [hc] at h1
    linarith
  have hC : ∀ z ∈ [[lam.re - ε, lam.re + ε]] ×ℂ [[lam.im + ε, d]], z ≠ lam := by
    intro z hz
    have h2 : lam.im + ε ≤ z.im :=
      (Set.mem_Icc.mp (by simpa [Set.uIcc_of_le (le_of_lt hd)] using hz.2)).1
    intro hc
    rw [hc] at h2
    linarith
  have hD : ∀ z ∈ [[lam.re - ε, lam.re + ε]] ×ℂ [[c, lam.im - ε]], z ≠ lam := by
    intro z hz
    have h2 : z.im ≤ lam.im - ε :=
      (Set.mem_Icc.mp (by simpa [Set.uIcc_of_le (le_of_lt hc)] using hz.2)).2
    intro hc
    rw [hc] at h2
    linarith
  rw [hs1, hs2, hs3,
    rectBoundary_quot_eq hF hL, rectBoundary_quot_eq hF hRt,
    rectBoundary_quot_eq hF hC, rectBoundary_quot_eq hF hD]
  abel


/-! ## The residue of `(z - lam)⁻¹` on a square: `∮ dz/(z - lam) = 2πi` -/

/-- Antiderivative of `t ↦ (t + i a)⁻¹` for `a ≠ 0`. -/
lemma hasDerivAt_inv_add_mul_I (a t : ℝ) (ha : a ≠ 0) :
    HasDerivAt (fun s : ℝ => ((1 / 2 : ℝ) : ℂ) * (Real.log (s ^ 2 + a ^ 2) : ℂ)
        - I * (Real.arctan (s / a) : ℂ)) (((t : ℂ) + (a : ℂ) * I)⁻¹) t := by
  have hpos : (0 : ℝ) < t ^ 2 + a ^ 2 := by
    have h : 0 < a ^ 2 := sq_pos_of_ne_zero ha
    nlinarith [sq_nonneg t]
  have hlog : HasDerivAt (fun s : ℝ => Real.log (s ^ 2 + a ^ 2))
      ((2 * t) / (t ^ 2 + a ^ 2)) t := by
    have h1 : HasDerivAt (fun s : ℝ => s ^ 2 + a ^ 2) (2 * t) t := by
      simpa using ((hasDerivAt_id (x := t)).pow 2).const_add (a ^ 2)
    exact h1.log (ne_of_gt hpos)
  have harct : HasDerivAt (fun s : ℝ => Real.arctan (s / a)) (a / (a ^ 2 + t ^ 2)) t := by
    have h1 : HasDerivAt (fun s : ℝ => s / a) (1 / a) t := (hasDerivAt_id t).div_const a
    have h2 := h1.arctan
    convert h2 using 1
    field_simp
  have h2 : HasDerivAt (fun s : ℝ => ((1 / 2 : ℝ) : ℂ) * (Real.log (s ^ 2 + a ^ 2) : ℂ))
      (((1 / 2 : ℝ) : ℂ) * (((2 * t) / (t ^ 2 + a ^ 2) : ℝ) : ℂ)) t :=
    (hlog.ofReal_comp).const_mul ((1 / 2 : ℝ) : ℂ)
  have h3 : HasDerivAt (fun s : ℝ => I * (Real.arctan (s / a) : ℂ))
      (I * (((a / (a ^ 2 + t ^ 2) : ℝ)) : ℂ)) t :=
    (harct.ofReal_comp).const_mul I
  have h := h2.sub h3
  have hne : ((t : ℂ) + (a : ℂ) * I) ≠ 0 := by
    intro hc
    have := congrArg Complex.im hc
    simp [ha] at this
  have hfin : ((t : ℂ) + (a : ℂ) * I) *
      (((1 / 2 : ℝ) : ℂ) * (((2 * t) / (t ^ 2 + a ^ 2) : ℝ) : ℂ)
        - I * (((a / (a ^ 2 + t ^ 2) : ℝ)) : ℂ)) = 1 := by
    have hsq : ((t : ℂ) ^ 2 + (a : ℂ) ^ 2) ≠ 0 := by
      have : (t : ℂ) ^ 2 + (a : ℂ) ^ 2 = ((t ^ 2 + a ^ 2 : ℝ) : ℂ) := by push_cast; ring
      rw [this]; exact_mod_cast ne_of_gt hpos
    push_cast
    rw [show ((a : ℂ) ^ 2 + (t : ℂ) ^ 2) = ((t : ℂ) ^ 2 + (a : ℂ) ^ 2) by ring]
    field_simp
    ring_nf
    rw [show I ^ 2 = (-1 : ℂ) by rw [pow_two]; exact Complex.I_mul_I]
    ring
  have hD : (((1 / 2 : ℝ) : ℂ) * (((2 * t) / (t ^ 2 + a ^ 2) : ℝ) : ℂ)
        - I * (((a / (a ^ 2 + t ^ 2) : ℝ)) : ℂ)) = ((t : ℂ) + (a : ℂ) * I)⁻¹ :=
    (inv_eq_of_mul_eq_one_right hfin).symm
  rwa [hD] at h

/-- Antiderivative of `v ↦ (a + i v)⁻¹` for `a ≠ 0`. -/
lemma hasDerivAt_add_mul_I_inv (a t : ℝ) (ha : a ≠ 0) :
    HasDerivAt (fun s : ℝ => (Real.arctan (s / a) : ℂ)
        - (I / 2) * (Real.log (a ^ 2 + s ^ 2) : ℂ)) (((a : ℂ) + (t : ℂ) * I)⁻¹) t := by
  have hpos : (0 : ℝ) < a ^ 2 + t ^ 2 := by
    have h : 0 < a ^ 2 := sq_pos_of_ne_zero ha
    nlinarith [sq_nonneg t]
  have hlog : HasDerivAt (fun s : ℝ => Real.log (a ^ 2 + s ^ 2))
      ((2 * t) / (a ^ 2 + t ^ 2)) t := by
    have h1 : HasDerivAt (fun s : ℝ => a ^ 2 + s ^ 2) (2 * t) t := by
      simpa using ((hasDerivAt_id (x := t)).pow 2).const_add (a ^ 2)
    exact h1.log (ne_of_gt hpos)
  have harct : HasDerivAt (fun s : ℝ => Real.arctan (s / a)) (a / (a ^ 2 + t ^ 2)) t := by
    have h1 : HasDerivAt (fun s : ℝ => s / a) (1 / a) t := (hasDerivAt_id t).div_const a
    have h2 := h1.arctan
    convert h2 using 1
    field_simp
  have h2 : HasDerivAt (fun s : ℝ => (Real.arctan (s / a) : ℂ))
      (((a / (a ^ 2 + t ^ 2) : ℝ)) : ℂ) t := harct.ofReal_comp
  have h3 : HasDerivAt (fun s : ℝ => (I / 2) * (Real.log (a ^ 2 + s ^ 2) : ℂ))
      ((I / 2) * (((2 * t) / (a ^ 2 + t ^ 2) : ℝ) : ℂ)) t :=
    (hlog.ofReal_comp).const_mul (I / 2)
  have h := h2.sub h3
  have hne : ((a : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro hc
    have := congrArg Complex.re hc
    simp [ha] at this
  have hfin : ((a : ℂ) + (t : ℂ) * I) *
      ((((a / (a ^ 2 + t ^ 2) : ℝ)) : ℂ)
        - (I / 2) * (((2 * t) / (a ^ 2 + t ^ 2) : ℝ) : ℂ)) = 1 := by
    have hsq : ((a : ℂ) ^ 2 + (t : ℂ) ^ 2) ≠ 0 := by
      have : (a : ℂ) ^ 2 + (t : ℂ) ^ 2 = ((a ^ 2 + t ^ 2 : ℝ) : ℂ) := by push_cast; ring
      rw [this]; exact_mod_cast ne_of_gt hpos
    push_cast
    field_simp
    ring_nf
    rw [show I ^ 2 = (-1 : ℂ) by rw [pow_two]; exact Complex.I_mul_I]
    ring
  have hD : ((((a / (a ^ 2 + t ^ 2) : ℝ)) : ℂ)
        - (I / 2) * (((2 * t) / (a ^ 2 + t ^ 2) : ℝ) : ℂ)) = ((a : ℂ) + (t : ℂ) * I)⁻¹ :=
    (inv_eq_of_mul_eq_one_right hfin).symm
  rwa [hD] at h

/-- Translation covariance of the rectangle boundary functional. -/
lemma rectBoundary_comp_sub (g : ℂ → ℂ) (a b c d : ℝ) (lam : ℂ) :
    rectBoundary (fun z => g (z - lam)) (a + lam.re) (b + lam.re) (c + lam.im) (d + lam.im)
      = rectBoundary g a b c d := by
  obtain ⟨u, v⟩ := lam
  have h1 : (∫ x : ℝ in a + u..b + u, g ((x : ℂ) + ((c + v : ℝ) : ℂ) * I - (⟨u, v⟩ : ℂ)))
      = ∫ x : ℝ in a..b, g ((x : ℂ) + (c : ℂ) * I) := by
    have hcongr : (fun x : ℝ => g ((x : ℂ) + ((c + v : ℝ) : ℂ) * I - (⟨u, v⟩ : ℂ)))
        = fun x : ℝ => (fun t : ℝ => g ((t : ℂ) + (c : ℂ) * I)) (x + (-u)) := by
      funext x
      congr 1
      rw [Complex.mk_eq_add_mul_I]
      push_cast
      ring
    rw [hcongr, intervalIntegral.integral_comp_add_right
      (f := fun t : ℝ => g ((t : ℂ) + (c : ℂ) * I)) (d := -u)]
    norm_num
  have h2 : (∫ x : ℝ in a + u..b + u, g ((x : ℂ) + ((d + v : ℝ) : ℂ) * I - (⟨u, v⟩ : ℂ)))
      = ∫ x : ℝ in a..b, g ((x : ℂ) + (d : ℂ) * I) := by
    have hcongr : (fun x : ℝ => g ((x : ℂ) + ((d + v : ℝ) : ℂ) * I - (⟨u, v⟩ : ℂ)))
        = fun x : ℝ => (fun t : ℝ => g ((t : ℂ) + (d : ℂ) * I)) (x + (-u)) := by
      funext x
      congr 1
      rw [Complex.mk_eq_add_mul_I]
      push_cast
      ring
    rw [hcongr, intervalIntegral.integral_comp_add_right
      (f := fun t : ℝ => g ((t : ℂ) + (d : ℂ) * I)) (d := -u)]
    norm_num
  have h3 : (∫ y : ℝ in c + v..d + v, g (((b + u : ℝ) : ℂ) + (y : ℂ) * I - (⟨u, v⟩ : ℂ)))
      = ∫ y : ℝ in c..d, g ((b : ℂ) + (y : ℂ) * I) := by
    have hcongr : (fun y : ℝ => g (((b + u : ℝ) : ℂ) + (y : ℂ) * I - (⟨u, v⟩ : ℂ)))
        = fun y : ℝ => (fun t : ℝ => g ((b : ℂ) + (t : ℂ) * I)) (y + (-v)) := by
      funext y
      congr 1
      rw [Complex.mk_eq_add_mul_I]
      push_cast
      ring
    rw [hcongr, intervalIntegral.integral_comp_add_right
      (f := fun t : ℝ => g ((b : ℂ) + (t : ℂ) * I)) (d := -v)]
    norm_num
  have h4 : (∫ y : ℝ in c + v..d + v, g (((a + u : ℝ) : ℂ) + (y : ℂ) * I - (⟨u, v⟩ : ℂ)))
      = ∫ y : ℝ in c..d, g ((a : ℂ) + (y : ℂ) * I) := by
    have hcongr : (fun y : ℝ => g (((a + u : ℝ) : ℂ) + (y : ℂ) * I - (⟨u, v⟩ : ℂ)))
        = fun y : ℝ => (fun t : ℝ => g ((a : ℂ) + (t : ℂ) * I)) (y + (-v)) := by
      funext y
      congr 1
      rw [Complex.mk_eq_add_mul_I]
      push_cast
      ring
    rw [hcongr, intervalIntegral.integral_comp_add_right
      (f := fun t : ℝ => g ((a : ℂ) + (t : ℂ) * I)) (d := -v)]
    norm_num
  simp only [rectBoundary, h1, h2, h3, h4]

/-- The integral of `(t + i a)⁻¹` over `[-ε, ε]` for `a = -ε`. -/
lemma integral_inv_add_mul_I_neg (ε : ℝ) (hε : 0 < ε) :
    (∫ t : ℝ in -ε..ε, (((t : ℂ) + ((-ε : ℝ) : ℂ) * I))⁻¹) = I * (Real.pi / 2) := by
  have hint : IntervalIntegrable (fun t : ℝ => (((t : ℂ) + ((-ε : ℝ) : ℂ) * I))⁻¹) volume (-ε) ε := by
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.inv₀ (by fun_prop) ?_
    intro t _
    intro h
    have := congrArg Complex.im h
    simp [hε.ne'] at this
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s : ℝ => ((1 / 2 : ℝ) : ℂ) * (Real.log (s ^ 2 + (-ε) ^ 2) : ℂ)
      - I * (Real.arctan (s / (-ε)) : ℂ))
    (f' := fun t : ℝ => (((t : ℂ) + ((-ε : ℝ) : ℂ) * I))⁻¹)
    (fun t _ => hasDerivAt_inv_add_mul_I (-ε) t (by linarith)) hint
  rw [hfund]
  have hlog : Real.log ((-ε) ^ 2 + (-ε) ^ 2) = Real.log (ε ^ 2 + (-ε) ^ 2) := by ring_nf
  rw [hlog]
  have ha1 : Real.arctan (ε / (-ε)) = -(Real.pi / 4) := by
    have h : ε / (-ε) = -1 := by field_simp
    rw [h, Real.arctan_neg, Real.arctan_one]
  have ha2 : Real.arctan (-ε / (-ε)) = Real.pi / 4 := by
    have h : -ε / (-ε) = 1 := by field_simp
    rw [h, Real.arctan_one]
  rw [ha1, ha2]
  push_cast
  ring

/-- The integral of `(t + i a)⁻¹` over `[-ε, ε]` for `a = ε`. -/
lemma integral_inv_add_mul_I_pos (ε : ℝ) (hε : 0 < ε) :
    (∫ t : ℝ in -ε..ε, (((t : ℂ) + ((ε : ℝ) : ℂ) * I))⁻¹) = -(I * (Real.pi / 2)) := by
  have hint : IntervalIntegrable (fun t : ℝ => (((t : ℂ) + ((ε : ℝ) : ℂ) * I))⁻¹) volume (-ε) ε := by
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.inv₀ (by fun_prop) ?_
    intro t _
    intro h
    have := congrArg Complex.im h
    simp [hε.ne'] at this
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s : ℝ => ((1 / 2 : ℝ) : ℂ) * (Real.log (s ^ 2 + (ε : ℝ) ^ 2) : ℂ)
      - I * (Real.arctan (s / (ε : ℝ)) : ℂ))
    (f' := fun t : ℝ => (((t : ℂ) + ((ε : ℝ) : ℂ) * I))⁻¹)
    (fun t _ => hasDerivAt_inv_add_mul_I ε t (by linarith)) hint
  rw [hfund]
  have ha1 : Real.arctan (ε / (ε : ℝ)) = Real.pi / 4 := by
    have h : ε / ε = 1 := by field_simp
    rw [h, Real.arctan_one]
  have ha2 : Real.arctan (-ε / (ε : ℝ)) = -(Real.pi / 4) := by
    have h : -ε / ε = -1 := by field_simp
    rw [h, Real.arctan_neg, Real.arctan_one]
  rw [ha1, ha2]
  push_cast
  ring

/-- The integral of `(i a + t i)⁻¹` type edges: real part `-ε`. -/
lemma integral_add_mul_I_inv_neg (ε : ℝ) (hε : 0 < ε) :
    (∫ t : ℝ in -ε..ε, ((((-ε : ℝ) : ℂ) + (t : ℂ) * I))⁻¹) = -(Real.pi / 2) := by
  have hint : IntervalIntegrable (fun t : ℝ => ((((-ε : ℝ) : ℂ) + (t : ℂ) * I))⁻¹) volume (-ε) ε := by
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.inv₀ (by fun_prop) ?_
    intro t _
    intro h
    have := congrArg Complex.re h
    simp [hε.ne'] at this
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s : ℝ => (Real.arctan (s / (-ε)) : ℂ)
      - (I / 2) * (Real.log ((-ε) ^ 2 + s ^ 2) : ℂ))
    (f' := fun t : ℝ => ((((-ε : ℝ) : ℂ) + (t : ℂ) * I))⁻¹)
    (fun t _ => hasDerivAt_add_mul_I_inv (-ε) t (by linarith)) hint
  rw [hfund]
  have hlog : Real.log ((-ε) ^ 2 + (-ε) ^ 2) = Real.log ((-ε) ^ 2 + ε ^ 2) := by ring_nf
  rw [hlog]
  have ha1 : Real.arctan (ε / (-ε)) = -(Real.pi / 4) := by
    have h : ε / (-ε) = -1 := by field_simp
    rw [h, Real.arctan_neg, Real.arctan_one]
  have ha2 : Real.arctan (-ε / (-ε)) = Real.pi / 4 := by
    have h : -ε / (-ε) = 1 := by field_simp
    rw [h, Real.arctan_one]
  rw [ha1, ha2]
  push_cast
  ring

/-- The integral of the right edge: real part `ε`. -/
lemma integral_add_mul_I_inv_pos (ε : ℝ) (hε : 0 < ε) :
    (∫ t : ℝ in -ε..ε, ((((ε : ℝ) : ℂ) + (t : ℂ) * I))⁻¹) = Real.pi / 2 := by
  have hint : IntervalIntegrable (fun t : ℝ => ((((ε : ℝ) : ℂ) + (t : ℂ) * I))⁻¹) volume (-ε) ε := by
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.inv₀ (by fun_prop) ?_
    intro t _
    intro h
    have := congrArg Complex.re h
    simp [hε.ne'] at this
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s : ℝ => (Real.arctan (s / (ε : ℝ)) : ℂ)
      - (I / 2) * (Real.log ((ε : ℝ) ^ 2 + s ^ 2) : ℂ))
    (f' := fun t : ℝ => ((((ε : ℝ) : ℂ) + (t : ℂ) * I))⁻¹)
    (fun t _ => hasDerivAt_add_mul_I_inv ε t (by linarith)) hint
  rw [hfund]
  have ha1 : Real.arctan (ε / (ε : ℝ)) = Real.pi / 4 := by
    have h : ε / ε = 1 := by field_simp
    rw [h, Real.arctan_one]
  have ha2 : Real.arctan (-ε / (ε : ℝ)) = -(Real.pi / 4) := by
    have h : -ε / ε = -1 := by field_simp
    rw [h, Real.arctan_neg, Real.arctan_one]
  rw [ha1, ha2]
  push_cast
  ring

/-- **The residue of `(z - lam)⁻¹` on a square centred at `lam`:** `∮ dz/(z - lam) = 2π i`.  This
fixes the normalization of the Cauchy–Pompeiu formula. -/
theorem rectBoundary_inv_sub_eq_two_pi_I {lam : ℂ} {ε : ℝ} (hε : 0 < ε) :
    rectBoundary (fun z => (z - lam)⁻¹) (lam.re - ε) (lam.re + ε) (lam.im - ε) (lam.im + ε)
      = 2 * (Real.pi : ℂ) * I := by
  have hcenter : rectBoundary (fun z : ℂ => z⁻¹) (-ε) ε (-ε) ε = 2 * (Real.pi : ℂ) * I := by
    simp only [rectBoundary]
    rw [integral_inv_add_mul_I_neg ε hε, integral_inv_add_mul_I_pos ε hε,
      integral_add_mul_I_inv_neg ε hε, integral_add_mul_I_inv_pos ε hε]
    ring
  have hc := rectBoundary_comp_sub (fun z : ℂ => z⁻¹) (-ε) ε (-ε) ε lam
  rw [show -ε + lam.re = lam.re - ε by ring, show ε + lam.re = lam.re + ε by ring,
    show -ε + lam.im = lam.im - ε by ring, show ε + lam.im = lam.im + ε by ring] at hc
  rw [hc, hcenter]

/-! ## From the hole identity to the plane representation -/

/-- The first-order extension is `C¹` when `f` is `C²`. -/
lemma contDiff_almostAnalyticExt_one {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 (almostAnalyticExt f) := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hd1 : ContDiff ℝ 1 (deriv f) := by
    simpa using ContDiff.iterate_deriv' (𝕜 := ℝ) (n := 1) (k := 1) (by simpa using hf)
  have h1 : ContDiff ℝ 1 (fun z : ℂ => (f z.re : ℂ)) := by
    have h := (Complex.ofRealCLM.contDiff (n := (1 : ℕ∞))).comp (hf1.comp Complex.reCLM.contDiff)
    simpa [Function.comp_def] using h
  have h2 : ContDiff ℝ 1 (fun z : ℂ => (z.im : ℂ)) := by
    have h := (Complex.ofRealCLM.contDiff (n := (1 : ℕ∞))).comp Complex.imCLM.contDiff
    simpa [Function.comp_def] using h
  have h3 : ContDiff ℝ 1 (fun z : ℂ => ((deriv f z.re : ℝ) : ℂ)) := by
    have h := (Complex.ofRealCLM.contDiff (n := (1 : ℕ∞))).comp (hd1.comp Complex.reCLM.contDiff)
    simpa [Function.comp_def] using h
  have h4 : ContDiff ℝ 1 (fun z : ℂ => (I : ℂ) * ((z.im : ℂ) * ((deriv f z.re : ℝ) : ℂ))) :=
    contDiff_const.mul (h2.mul h3)
  have h5 : ContDiff ℝ 1 (fun z : ℂ => (f z.re : ℂ) + (I : ℂ) * ((z.im : ℂ) * ((deriv f z.re : ℝ) : ℂ))) :=
    h1.add h4
  have hgoal : (fun z : ℂ => (f z.re : ℂ) + (I : ℂ) * ((z.im : ℂ) * ((deriv f z.re : ℝ) : ℂ)))
      = almostAnalyticExt f := by
    funext z
    simp [almostAnalyticExt]
    ring
  rw [hgoal] at h5
  exact h5

/-- The cut-off extension is `C¹` when `f` is `C²`. -/
lemma contDiff_almostAnalyticExtCut_one {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 (almostAnalyticExtCut f) := by
  have hext := contDiff_almostAnalyticExt_one hf
  have hy : ContDiff ℝ 1 (fun z : ℂ => (yCut z.im : ℂ)) := by
    have h := (Complex.ofRealCLM.contDiff (n := (1 : ℕ∞))).comp
      ((contDiff_yCut 1).comp Complex.imCLM.contDiff)
    simpa [Function.comp_def] using h
  have h : ContDiff ℝ 1 (fun z : ℂ => almostAnalyticExt f z * (yCut z.im : ℂ)) :=
    hext.mul hy
  exact h

/-- The `∂̄` numerator of the cut-off extension, as a function of `z`. -/
def dbarNum (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  I • fderiv ℝ (almostAnalyticExtCut f) z 1 - fderiv ℝ (almostAnalyticExtCut f) z I

lemma continuous_dbarNum {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) : Continuous (dbarNum f) := by
  have hfd : Continuous (fderiv ℝ (almostAnalyticExtCut f)) :=
    (contDiff_almostAnalyticExtCut_one hf).continuous_fderiv (by norm_num)
  have h1 : Continuous (fun z : ℂ => fderiv ℝ (almostAnalyticExtCut f) z 1) :=
    hfd.clm_apply continuous_const
  have h2 : Continuous (fun z : ℂ => fderiv ℝ (almostAnalyticExtCut f) z I) :=
    hfd.clm_apply continuous_const
  exact ((continuous_const.mul h1).sub h2)

lemma hasCompactSupport_dbarNum {f : ℝ → ℝ} (hfc : HasCompactSupport f) :
    HasCompactSupport (dbarNum f) := by
  refine (hasCompactSupport_almostAnalyticExtCut hfc).mono' ?_
  intro z hz
  by_contra hzt
  rw [notMem_tsupport_iff_eventuallyEq] at hzt
  apply hz
  simp only [dbarNum]
  rw [hzt.fderiv_eq]
  simp

/-- A global norm bound on the `∂̄` numerator. -/
lemma exists_norm_dbarNum_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) : ∃ M, ∀ z : ℂ, ‖dbarNum f z‖ ≤ M := by
  have hcont := continuous_dbarNum hf
  have hK : IsCompact (tsupport (dbarNum f)) := hasCompactSupport_dbarNum hfc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max M 0, fun z => ?_⟩
  by_cases hz : z ∈ tsupport (dbarNum f)
  · exact le_trans (hM z hz) (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hz]
    simp

/-- A bound on the second derivative of `f`. -/
lemma exists_norm_deriv_deriv_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) : ∃ M, ∀ x : ℝ, ‖deriv (deriv f) x‖ ≤ M := by
  have hcont : Continuous (deriv (deriv f)) := by
    have h2 : ContDiff ℝ 1 (deriv f) := by
      simpa using ContDiff.iterate_deriv' (𝕜 := ℝ) (n := 1) (k := 1) (by simpa using hf)
    exact h2.continuous_deriv_one
  have hK : IsCompact (tsupport (deriv (deriv f))) := hfc.deriv.deriv
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max M 0, fun x => ?_⟩
  by_cases hx : x ∈ tsupport (deriv (deriv f))
  · exact le_trans (hM x hx) (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx]
    simp

/-- **Global boundedness of the Cauchy–Pompeiu integrand** for the cut-off extension, using the
linear vanishing of the `∂̄` numerator on the real axis. -/
lemma exists_norm_pompeiuIntegrand_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (lam : ℝ) :
    ∃ M, ∀ z : ℂ,
      ‖pompeiuIntegrand (almostAnalyticExtCut f) (lam : ℂ) z‖ ≤ M := by
  obtain ⟨M₁, hM₁⟩ := exists_norm_dbarNum_le hf hfc
  obtain ⟨M₂, hM₂⟩ := exists_norm_deriv_deriv_le hf hfc
  have hM₁nn : 0 ≤ M₁ := le_trans (norm_nonneg _) (hM₁ 0)
  have hM₂nn : 0 ≤ M₂ := le_trans (norm_nonneg _) (hM₂ 0)
  have hmaxnn : 0 ≤ max M₁ M₂ := le_trans hM₁nn (le_max_left _ _)
  refine ⟨max M₁ M₂, fun z => ?_⟩
  -- the numerator is bounded by `|Im z| * max M₁ M₂`
  have hnum : ‖I • fderiv ℝ (almostAnalyticExtCut f) z 1
      - fderiv ℝ (almostAnalyticExtCut f) z I‖ ≤ |z.im| * max M₁ M₂ := by
    rcases eq_or_lt_of_le (abs_nonneg z.im) with h0 | h0
    · have him0 : z.im = 0 := abs_eq_zero.mp h0.symm
      have hle := norm_dbar_almostAnalyticExtCut_le hf (z := z) (by rw [him0]; norm_num) hM₂
      have hzero : ‖I • fderiv ℝ (almostAnalyticExtCut f) z 1
          - fderiv ℝ (almostAnalyticExtCut f) z I‖ ≤ 0 := by simpa [him0] using hle
      simpa [him0] using hzero
    · rcases lt_or_ge |z.im| 1 with h1 | h1
      · exact le_trans (norm_dbar_almostAnalyticExtCut_le hf h1 hM₂)
          (mul_le_mul_of_nonneg_left (le_max_right _ _) (abs_nonneg _))
      · have hb : ‖I • fderiv ℝ (almostAnalyticExtCut f) z 1
            - fderiv ℝ (almostAnalyticExtCut f) z I‖ ≤ M₁ := hM₁ z
        calc ‖I • fderiv ℝ (almostAnalyticExtCut f) z 1
              - fderiv ℝ (almostAnalyticExtCut f) z I‖
            ≤ M₁ := hb
          _ ≤ max M₁ M₂ := le_max_left _ _
          _ = 1 * max M₁ M₂ := (one_mul _).symm
          _ ≤ |z.im| * max M₁ M₂ :=
            mul_le_mul_of_nonneg_right h1 (le_trans hM₁nn (le_max_left _ _))
  simp only [pompeiuIntegrand]
  rw [norm_mul, norm_inv]
  rcases eq_or_ne z (lam : ℂ) with rfl | hz
  · simp only [sub_self, inv_zero, norm_zero, mul_zero]
    exact hmaxnn
  · have hnorm : 0 < ‖z - (lam : ℂ)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
    have hden : |z.im| ≤ ‖z - (lam : ℂ)‖ := by
      have h1 : (z - (lam : ℂ)).im = z.im := by simp
      calc |z.im| = |(z - (lam : ℂ)).im| := by rw [h1]
        _ ≤ ‖z - (lam : ℂ)‖ := Complex.abs_im_le_norm _
    rcases eq_or_lt_of_le (abs_nonneg z.im) with h0 | h0
    · have him0 : z.im = 0 := abs_eq_zero.mp h0.symm
      have hzero : ‖I • fderiv ℝ (almostAnalyticExtCut f) z 1
          - fderiv ℝ (almostAnalyticExtCut f) z I‖ ≤ 0 := by
        have hle := norm_dbar_almostAnalyticExtCut_le hf (z := z) (by rw [him0]; norm_num) hM₂
        simpa [him0] using hle
      rw [show I • fderiv ℝ (almostAnalyticExtCut f) z 1
          - fderiv ℝ (almostAnalyticExtCut f) z I = 0 from
        norm_eq_zero.mp (le_antisymm hzero (norm_nonneg _))]
      simp only [norm_zero, zero_mul]
      exact hmaxnn
    · have hinvle : (‖z - (lam : ℂ)‖)⁻¹ ≤ (|z.im|)⁻¹ := by
        rw [inv_le_inv₀ hnorm h0]
        exact hden
      calc ‖I • fderiv ℝ (almostAnalyticExtCut f) z 1
            - fderiv ℝ (almostAnalyticExtCut f) z I‖ * (‖z - (lam : ℂ)‖)⁻¹
          ≤ (|z.im| * max M₁ M₂) * (|z.im|)⁻¹ :=
            mul_le_mul hnum hinvle (inv_nonneg.mpr (norm_nonneg _))
              (mul_nonneg (abs_nonneg _) (le_trans hM₁nn (le_max_left _ _)))
        _ = max M₁ M₂ := by
            rw [mul_comm (|z.im|) (max M₁ M₂), mul_assoc,
              mul_inv_cancel₀ (ne_of_gt h0), mul_one]

/-- The cut-off extension is globally Lipschitz (its derivative is continuous and compactly
supported). -/
lemma exists_lipschitz_almostAnalyticExtCut {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z w : ℂ,
      ‖almostAnalyticExtCut f z - almostAnalyticExtCut f w‖ ≤ C * ‖z - w‖ := by
  have hF : ContDiff ℝ 1 (almostAnalyticExtCut f) := contDiff_almostAnalyticExtCut_one hf
  have hcont : Continuous (fun z : ℂ => fderiv ℝ (almostAnalyticExtCut f) z) :=
    hF.continuous_fderiv (by norm_num)
  have hsupp : HasCompactSupport (fun z : ℂ => fderiv ℝ (almostAnalyticExtCut f) z) := by
    refine (hasCompactSupport_almostAnalyticExtCut hfc).mono' ?_
    intro z hz
    by_contra hzt
    rw [notMem_tsupport_iff_eventuallyEq] at hzt
    apply hz
    show fderiv ℝ (almostAnalyticExtCut f) z = 0
    rw [hzt.fderiv_eq]
    simp
  have hK : IsCompact (tsupport (fun z : ℂ => fderiv ℝ (almostAnalyticExtCut f) z)) := hsupp
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  have hC' : ∀ z : ℂ, ‖fderiv ℝ (almostAnalyticExtCut f) z‖ ≤ max C 0 := by
    intro z
    by_cases hz : z ∈ tsupport (fun z : ℂ => fderiv ℝ (almostAnalyticExtCut f) z)
    · exact le_trans (hC z hz) (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hz]
      simp
  refine ⟨max C 0, le_max_right _ _, fun z w => ?_⟩
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le
    (f := almostAnalyticExtCut f) (s := Set.univ) (C := max C 0)
    (fun x _ => hF.differentiable (by norm_num) |>.differentiableAt)
    (fun x _ => hC' x) convex_univ (Set.mem_univ z) (Set.mem_univ w)
  simpa [norm_sub_rev] using h

/-- Interval integrability of the vertical edge functions of the weight `(z - lam)⁻¹`. -/
lemma intervalIntegrable_inv_sub_edge {lam : ℂ} {c : ℝ} {a b : ℝ} (hc : c ≠ lam.im) :
    IntervalIntegrable (fun x : ℝ => (((x : ℂ) + (c : ℂ) * I) - lam)⁻¹) volume a b := by
  apply ContinuousOn.intervalIntegrable
  refine ContinuousOn.inv₀ (by fun_prop) ?_
  intro x _
  exact sub_ne_zero.mpr (ne_of_im_ne hc)

/-- Interval integrability of the horizontal edge functions of the weight `(z - lam)⁻¹`. -/
lemma intervalIntegrable_inv_sub_edge_horiz {lam : ℂ} {c : ℝ} {a b : ℝ} (hc : c ≠ lam.re) :
    IntervalIntegrable (fun y : ℝ => (((c : ℂ) + (y : ℂ) * I) - lam)⁻¹) volume a b := by
  apply ContinuousOn.intervalIntegrable
  refine ContinuousOn.inv₀ (by fun_prop) ?_
  intro y _
  exact sub_ne_zero.mpr (ne_of_re_ne hc)

/-- The boundary functional respects pointwise equality. -/
lemma rectBoundary_congr {g h : ℂ → ℂ} {a b c d : ℝ} (H : ∀ z, g z = h z) :
    rectBoundary g a b c d = rectBoundary h a b c d := by
  simp only [rectBoundary, H]

/-- Additivity of the boundary functional for sums of functions whose edge functions are interval
integrable. -/
lemma rectBoundary_add {g₁ g₂ : ℂ → ℂ} {a b c d : ℝ}
    (h1c : IntervalIntegrable (fun x : ℝ => g₁ ((x : ℂ) + (c : ℂ) * I)) volume a b)
    (h2c : IntervalIntegrable (fun x : ℝ => g₂ ((x : ℂ) + (c : ℂ) * I)) volume a b)
    (h1d : IntervalIntegrable (fun x : ℝ => g₁ ((x : ℂ) + (d : ℂ) * I)) volume a b)
    (h2d : IntervalIntegrable (fun x : ℝ => g₂ ((x : ℂ) + (d : ℂ) * I)) volume a b)
    (h1b : IntervalIntegrable (fun y : ℝ => g₁ ((b : ℂ) + (y : ℂ) * I)) volume c d)
    (h2b : IntervalIntegrable (fun y : ℝ => g₂ ((b : ℂ) + (y : ℂ) * I)) volume c d)
    (h1a : IntervalIntegrable (fun y : ℝ => g₁ ((a : ℂ) + (y : ℂ) * I)) volume c d)
    (h2a : IntervalIntegrable (fun y : ℝ => g₂ ((a : ℂ) + (y : ℂ) * I)) volume c d) :
    rectBoundary (fun z => g₁ z + g₂ z) a b c d
      = rectBoundary g₁ a b c d + rectBoundary g₂ a b c d := by
  simp only [rectBoundary]
  rw [intervalIntegral.integral_add h1c h2c, intervalIntegral.integral_add h1d h2d,
    intervalIntegral.integral_add h1b h2b, intervalIntegral.integral_add h1a h2a]
  ring

/-- Decomposition of the hole's boundary functional: the constant part contributes the residue
`2π i F lam`, and the remainder is the boundary functional of the bounded quotient
`(F - F lam)/(z - lam)`. -/
lemma rectBoundary_hole_decomp {F : ℂ → ℂ} (hF : Continuous F) {lam : ℂ} {ε : ℝ} (hε : 0 < ε) :
    rectBoundary (fun z => F z / (z - lam)) (lam.re - ε) (lam.re + ε) (lam.im - ε) (lam.im + ε)
      = F lam * (2 * (Real.pi : ℂ) * I)
        + rectBoundary (fun z => (F z - F lam) / (z - lam))
            (lam.re - ε) (lam.re + ε) (lam.im - ε) (lam.im + ε) := by
  have hc : lam.im - ε ≠ lam.im := by linarith
  have hd : lam.im + ε ≠ lam.im := by linarith
  have ha : lam.re - ε ≠ lam.re := by linarith
  have hb : lam.re + ε ≠ lam.re := by linarith
  -- pointwise decomposition
  have hpt : ∀ z : ℂ, F z / (z - lam)
      = F lam * (z - lam)⁻¹ + (F z - F lam) / (z - lam) := by
    intro z
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  rw [rectBoundary_congr hpt,
    rectBoundary_add (g₁ := fun z => F lam * (z - lam)⁻¹)
      (g₂ := fun z => (F z - F lam) / (z - lam))
      ((intervalIntegrable_inv_sub_edge (lam := lam) (c := lam.im - ε) hc).const_mul (F lam))
      (intervalIntegrable_quot_segment (hF.sub continuous_const) (fun x _ => ne_of_im_ne hc))
      ((intervalIntegrable_inv_sub_edge (lam := lam) (c := lam.im + ε) hd).const_mul (F lam))
      (intervalIntegrable_quot_segment (hF.sub continuous_const) (fun x _ => ne_of_im_ne hd))
      ((intervalIntegrable_inv_sub_edge_horiz (lam := lam) (c := lam.re + ε) hb).const_mul (F lam))
      (intervalIntegrable_quot_segment_horiz (hF.sub continuous_const) hb)
      ((intervalIntegrable_inv_sub_edge_horiz (lam := lam) (c := lam.re - ε) ha).const_mul (F lam))
      (intervalIntegrable_quot_segment_horiz (hF.sub continuous_const) ha)]
  -- the weight part is constant times the residue
  have hw : rectBoundary (fun z => (z - lam)⁻¹) (lam.re - ε) (lam.re + ε)
      (lam.im - ε) (lam.im + ε) = 2 * (Real.pi : ℂ) * I :=
    rectBoundary_inv_sub_eq_two_pi_I hε
  have hsmul : rectBoundary (fun z => F lam * (z - lam)⁻¹) (lam.re - ε) (lam.re + ε)
      (lam.im - ε) (lam.im + ε)
        = F lam * rectBoundary (fun z => (z - lam)⁻¹) (lam.re - ε) (lam.re + ε)
            (lam.im - ε) (lam.im + ε) := by
    simp only [rectBoundary]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    ring
  rw [hsmul, hw]

/-- **Estimate of the remainder term on the hole boundary.** -/
lemma norm_rectBoundary_hole_le {F : ℂ → ℂ} {lam : ℂ} {ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C)
    (hLip : ∀ z, ‖F z - F lam‖ ≤ C * ‖z - lam‖) :
    ‖rectBoundary (fun z => (F z - F lam) / (z - lam))
        (lam.re - ε) (lam.re + ε) (lam.im - ε) (lam.im + ε)‖ ≤ 8 * C * ε := by
  have hedge : ∀ z : ℂ, z ≠ lam → ‖(F z - F lam) / (z - lam)‖ ≤ C := by
    intro z hz
    rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hz))]
    exact hLip z
  simp only [rectBoundary]
  set A : ℂ := ∫ x : ℝ in lam.re - ε..lam.re + ε,
    (F ((x : ℂ) + ((lam.im - ε : ℝ) : ℂ) * I) - F lam) /
      (((x : ℂ) + ((lam.im - ε : ℝ) : ℂ) * I) - lam) with hAdef
  set B : ℂ := ∫ x : ℝ in lam.re - ε..lam.re + ε,
    (F ((x : ℂ) + ((lam.im + ε : ℝ) : ℂ) * I) - F lam) /
      (((x : ℂ) + ((lam.im + ε : ℝ) : ℂ) * I) - lam) with hBdef
  set C₁ : ℂ := ∫ y : ℝ in lam.im - ε..lam.im + ε,
    (F (((lam.re + ε : ℝ) : ℂ) + (y : ℂ) * I) - F lam) /
      ((((lam.re + ε : ℝ) : ℂ) + (y : ℂ) * I) - lam) with hC1def
  set C₂ : ℂ := ∫ y : ℝ in lam.im - ε..lam.im + ε,
    (F (((lam.re - ε : ℝ) : ℂ) + (y : ℂ) * I) - F lam) /
      ((((lam.re - ε : ℝ) : ℂ) + (y : ℂ) * I) - lam) with hC2def
  have h1 : ‖A‖ ≤ C * (2 * ε) := by
    rw [hAdef]
    refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const (C := C) ?_) ?_
    · intro x _
      exact hedge _ (ne_of_im_ne (by linarith))
    · rw [show (lam.re + ε) - (lam.re - ε) = 2 * ε from by ring,
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * ε)]
  have h2 : ‖B‖ ≤ C * (2 * ε) := by
    rw [hBdef]
    refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const (C := C) ?_) ?_
    · intro x _
      exact hedge _ (ne_of_im_ne (by linarith))
    · rw [show (lam.re + ε) - (lam.re - ε) = 2 * ε from by ring,
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * ε)]
  have h3 : ‖C₁‖ ≤ C * (2 * ε) := by
    rw [hC1def]
    refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const (C := C) ?_) ?_
    · intro y _
      exact hedge _ (ne_of_re_ne (by linarith))
    · rw [show (lam.im + ε) - (lam.im - ε) = 2 * ε from by ring,
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * ε)]
  have h4 : ‖C₂‖ ≤ C * (2 * ε) := by
    rw [hC2def]
    refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const (C := C) ?_) ?_
    · intro y _
      exact hedge _ (ne_of_re_ne (by linarith))
    · rw [show (lam.im + ε) - (lam.im - ε) = 2 * ε from by ring,
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * ε)]
  have hI : ‖(I : ℂ)‖ = 1 := Complex.norm_I
  have hb1 : ‖A - B‖ ≤ C * (2 * ε) + C * (2 * ε) := by
    calc ‖A - B‖ ≤ ‖A‖ + ‖B‖ := norm_sub_le A B
      _ ≤ C * (2 * ε) + C * (2 * ε) := by linarith
  have hb2 : ‖(I : ℂ) * C₁‖ ≤ C * (2 * ε) := by
    rw [norm_mul, hI, one_mul]
    exact h3
  have hb3 : ‖(I : ℂ) * C₂‖ ≤ C * (2 * ε) := by
    rw [norm_mul, hI, one_mul]
    exact h4
  have hkey : ‖A - B + I * C₁ - I * C₂‖ ≤ ‖A - B‖ + ‖(I : ℂ) * C₁‖ + ‖(I : ℂ) * C₂‖ := by
    have h := norm_sub_le (A - B + I * C₁) (I * C₂)
    have h' := norm_add_le (A - B) (I * C₁)
    linarith
  have hsum : C * (2 * ε) + C * (2 * ε) + C * (2 * ε) + C * (2 * ε) = 8 * C * ε := by ring
  linarith [hkey, hb1, hb2, hb3, hsum]

/-- **Limit of the hole's boundary functional.**  For a continuous `F` that is Lipschitz at `lam`,
the boundary functional of `F/(z - lam)` over the shrinking square tends to `2π i F lam`. -/
lemma tendsto_boundary_hole {F : ℂ → ℂ} (hF : Continuous F) {lam : ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hLip : ∀ z, ‖F z - F lam‖ ≤ C * ‖z - lam‖) :
    Tendsto (fun ε : ℝ => rectBoundary (fun z => F z / (z - lam))
        (lam.re - ε) (lam.re + ε) (lam.im - ε) (lam.im + ε))
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * (Real.pi : ℂ) * I * F lam)) := by
  have hev : (fun ε : ℝ => rectBoundary (fun z => F z / (z - lam))
        (lam.re - ε) (lam.re + ε) (lam.im - ε) (lam.im + ε))
      =ᶠ[𝓝[>] (0 : ℝ)] fun ε : ℝ => F lam * (2 * (Real.pi : ℂ) * I)
        + rectBoundary (fun z => (F z - F lam) / (z - lam))
            (lam.re - ε) (lam.re + ε) (lam.im - ε) (lam.im + ε) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact rectBoundary_hole_decomp hF hε
  have hH : Tendsto (fun ε : ℝ => rectBoundary (fun z => (F z - F lam) / (z - lam))
        (lam.re - ε) (lam.re + ε) (lam.im - ε) (lam.im + ε)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun ε : ℝ => 8 * C * ε) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact norm_rectBoundary_hole_le hε hC hLip
    · have h : Tendsto (fun ε : ℝ => 8 * C * ε) (𝓝[>] (0 : ℝ)) (𝓝 (8 * C * 0)) :=
        tendsto_const_nhds.mul (tendsto_id.mono_left nhdsWithin_le_nhds)
      simpa using h
  have hmain : Tendsto (fun ε : ℝ => F lam * (2 * (Real.pi : ℂ) * I)
        + rectBoundary (fun z => (F z - F lam) / (z - lam))
            (lam.re - ε) (lam.re + ε) (lam.im - ε) (lam.im + ε))
      (𝓝[>] (0 : ℝ)) (𝓝 (F lam * (2 * (Real.pi : ℂ) * I) + 0)) :=
    tendsto_const_nhds.add hH
  have := hmain.congr' hev.symm
  simpa [mul_comm, mul_left_comm, mul_assoc, add_comm] using this

/-- The plane integrand associated with the cut-off extension. -/
@[reducible] def planeIntegrand (f : ℝ → ℝ) (lam : ℝ) (p : ℝ × ℝ) : ℂ :=
  pompeiuIntegrand (almostAnalyticExtCut f) (lam : ℂ) ((p.1 : ℂ) + (p.2 : ℂ) * I)

/-- The uncurried Cauchy–Pompeiu integrand is a.e. strongly measurable. -/
lemma aestronglyMeasurable_uncurry_pompeiuIntegrand {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (lam : ℂ) :
    AEStronglyMeasurable (Function.uncurry (fun x y : ℝ =>
      pompeiuIntegrand (almostAnalyticExtCut f) lam ((x : ℂ) + (y : ℂ) * I)))
      volume := by
  have hnum : Continuous (fun z : ℂ => I • fderiv ℝ (almostAnalyticExtCut f) z 1
      - fderiv ℝ (almostAnalyticExtCut f) z I) := continuous_dbarNum hf
  have hinv : Measurable (fun z : ℂ => (z - lam)⁻¹) := by fun_prop
  have hQ : Measurable (fun z : ℂ => pompeiuIntegrand (almostAnalyticExtCut f) lam z) := by
    simp only [pompeiuIntegrand]
    exact hnum.measurable.mul hinv
  have hφ : Measurable (fun p : ℝ × ℝ => ((p.1 : ℂ) + (p.2 : ℂ) * I)) := by fun_prop
  have h := hQ.comp hφ
  exact h.aestronglyMeasurable

/-- The uncurried Cauchy–Pompeiu integrand is integrable on every rectangle. -/
lemma integrableOn_uncurry_pompeiuIntegrand {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (lam : ℝ) (a b c d : ℝ) :
    IntegrableOn (Function.uncurry (fun x y : ℝ =>
      pompeiuIntegrand (almostAnalyticExtCut f) (lam : ℂ) ((x : ℂ) + (y : ℂ) * I)))
      (Set.Ioc a b ×ˢ Set.Ioc c d) volume := by
  obtain ⟨M, hM⟩ := exists_norm_pompeiuIntegrand_le hf hfc lam
  have hfin : (volume.prod volume) (Set.Ioc a b ×ˢ Set.Ioc c d) < ⊤ := by
    rw [Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioc]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  refine IntegrableOn.of_bound hfin
    ((aestronglyMeasurable_uncurry_pompeiuIntegrand hf (lam : ℂ)).restrict) M ?_
  filter_upwards with p
  exact hM _

/-- Integrability of the plane integrand on a rectangle. -/
lemma integrableOn_planeIntegrand {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (lam : ℝ) (a b c d : ℝ) :
    IntegrableOn (planeIntegrand f lam) (Set.Ioc a b ×ˢ Set.Ioc c d) volume :=
  integrableOn_uncurry_pompeiuIntegrand hf hfc lam a b c d

/-- An iterated interval integral of the Cauchy–Pompeiu integrand is the set integral over the
corresponding half-open rectangle. -/
lemma integral_interval_prod_pompeiuIntegrand {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (lam : ℝ) {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    (∫ x : ℝ in a..b, ∫ y : ℝ in c..d,
        pompeiuIntegrand (almostAnalyticExtCut f) (lam : ℂ) ((x : ℂ) + (y : ℂ) * I))
      = ∫ p : ℝ × ℝ in Set.Ioc a b ×ˢ Set.Ioc c d,
          pompeiuIntegrand (almostAnalyticExtCut f) (lam : ℂ) ((p.1 : ℂ) + (p.2 : ℂ) * I) := by
  simp only [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  exact (setIntegral_prod _ (integrableOn_uncurry_pompeiuIntegrand hf hfc lam a b c d)).symm

/-- The four rectangles surrounding the hole, as a single set. -/
def holeSurround (lam ε X Y : ℝ) : Set (ℝ × ℝ) :=
  (Set.Ioc (-X) (lam - ε) ×ˢ Set.Ioc (-Y) Y)
    ∪ ((Set.Ioc (lam + ε) X ×ˢ Set.Ioc (-Y) Y)
      ∪ ((Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc ε Y)
        ∪ (Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc (-Y) (-ε))))

/-- The square hole. -/
def holeSet (lam ε : ℝ) : Set (ℝ × ℝ) := Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc (-ε) ε

/-- The big rectangle. -/
def bigRectSet (X Y : ℝ) : Set (ℝ × ℝ) := Set.Ioc (-X) X ×ˢ Set.Ioc (-Y) Y

lemma measurableSet_bigRectSet (X Y : ℝ) : MeasurableSet (bigRectSet X Y) :=
  measurableSet_Ioc.prod measurableSet_Ioc

lemma measurableSet_holeSet (lam ε : ℝ) : MeasurableSet (holeSet lam ε) :=
  measurableSet_Ioc.prod measurableSet_Ioc

lemma measurableSet_holeSurround (lam ε X Y : ℝ) : MeasurableSet (holeSurround lam ε X Y) := by
  unfold holeSurround
  repeat' first
    | apply MeasurableSet.union
    | exact measurableSet_Ioc.prod measurableSet_Ioc

/-- The key set decomposition: the big rectangle is the four surrounding rectangles together with
the hole. -/
lemma bigRectSet_eq_holeSurround_union {lam ε X Y : ℝ} (hX : |lam| < X) (hY : 2 < Y)
    (hε : 0 < ε) (hεX : ε < X - |lam|) (hεY : ε < Y) :
    bigRectSet X Y = holeSurround lam ε X Y ∪ holeSet lam ε := by
  have hlam1 : lam ≤ |lam| := le_abs_self lam
  have hlam2 : -|lam| ≤ lam := neg_abs_le lam
  have h1 : lam - ε < X := by linarith
  have h2 : -X < lam - ε := by linarith
  have h3 : lam + ε < X := by linarith
  have h4 : -X < lam + ε := by linarith
  have hx2 : Set.Ioc (-X) X = Set.Ioc (-X) (lam - ε) ∪ Set.Ioc (lam - ε) X :=
    (Set.Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)).symm
  have hx1 : Set.Ioc (lam - ε) X = Set.Ioc (lam - ε) (lam + ε) ∪ Set.Ioc (lam + ε) X :=
    (Set.Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)).symm
  have hyA : Set.Ioc (-Y) ε = Set.Ioc (-Y) (-ε) ∪ Set.Ioc (-ε) ε :=
    (Set.Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith : -ε ≤ ε)).symm
  have hy1 : Set.Ioc (-Y) Y = Set.Ioc (-Y) ε ∪ Set.Ioc ε Y :=
    (Set.Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith : ε ≤ Y)).symm
  have hy2 : Set.Ioc (-Y) Y = Set.Ioc (-Y) (-ε) ∪ Set.Ioc (-ε) ε ∪ Set.Ioc ε Y := by
    rw [← hyA, hy1]
  unfold bigRectSet holeSurround holeSet
  rw [hx2, hx1, hy2]
  simp only [Set.prod_union, Set.union_prod, Set.union_assoc, Set.union_left_comm,
    Set.union_comm]

lemma disjoint_Ioc_prod_left {a b c d : ℝ} (h : b ≤ c) (s t : Set ℝ) :
    Disjoint (Set.Ioc a b ×ˢ s) (Set.Ioc c d ×ˢ t) := by
  rw [Set.disjoint_left]
  rintro ⟨x, y⟩ ⟨h1, -⟩ ⟨h2, -⟩
  rw [Set.mem_Ioc] at h1 h2
  exact absurd h2.1 (not_lt.mpr (le_trans h1.2 h))

lemma disjoint_Ioc_prod_right {a b c d : ℝ} (h : b ≤ c) (s t : Set ℝ) :
    Disjoint (s ×ˢ Set.Ioc a b) (t ×ˢ Set.Ioc c d) := by
  rw [Set.disjoint_left]
  rintro ⟨x, y⟩ ⟨-, h1⟩ ⟨-, h2⟩
  rw [Set.mem_Ioc] at h1 h2
  exact absurd h2.1 (not_lt.mpr (le_trans h1.2 h))

/-- The integral over the four surrounding rectangles is the sum of the four slab integrals. -/
lemma setIntegral_holeSurround_eq {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {lam X Y ε : ℝ} (hε : 0 < ε) (hX : |lam| < X) (hεX : ε < X - |lam|) (hεY : ε < Y) :
    (∫ p in holeSurround lam ε X Y, planeIntegrand f lam p)
      = (∫ p in Set.Ioc (-X) (lam - ε) ×ˢ Set.Ioc (-Y) Y, planeIntegrand f lam p
           )
        + (∫ p in Set.Ioc (lam + ε) X ×ˢ Set.Ioc (-Y) Y, planeIntegrand f lam p
           )
        + (∫ p in Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc ε Y, planeIntegrand f lam p
           )
        + (∫ p in Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc (-Y) (-ε), planeIntegrand f lam p
           ) := by
  have hlam1 : lam ≤ |lam| := le_abs_self lam
  have hlam2 : -|lam| ≤ lam := neg_abs_le lam
  have hAB : Disjoint (Set.Ioc (-X) (lam - ε) ×ˢ Set.Ioc (-Y) Y)
      (Set.Ioc (lam + ε) X ×ˢ Set.Ioc (-Y) Y) :=
    disjoint_Ioc_prod_left (by linarith) _ _
  have hAC : Disjoint (Set.Ioc (-X) (lam - ε) ×ˢ Set.Ioc (-Y) Y)
      (Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc ε Y) :=
    disjoint_Ioc_prod_left (by linarith) _ _
  have hAD : Disjoint (Set.Ioc (-X) (lam - ε) ×ˢ Set.Ioc (-Y) Y)
      (Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc (-Y) (-ε)) :=
    disjoint_Ioc_prod_left (by linarith) _ _
  have hBC : Disjoint (Set.Ioc (lam + ε) X ×ˢ Set.Ioc (-Y) Y)
      (Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc ε Y) :=
    (disjoint_Ioc_prod_left (a := lam - ε) (b := lam + ε) (c := lam + ε)
      (le_refl _) _ _).symm
  have hBD : Disjoint (Set.Ioc (lam + ε) X ×ˢ Set.Ioc (-Y) Y)
      (Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc (-Y) (-ε)) :=
    (disjoint_Ioc_prod_left (a := lam - ε) (b := lam + ε) (c := lam + ε)
      (le_refl _) _ _).symm
  have hCD : Disjoint (Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc ε Y)
      (Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc (-Y) (-ε)) :=
    (disjoint_Ioc_prod_right (a := -Y) (b := -ε) (c := ε) (d := Y) (by linarith) _ _).symm
  have hcol : IntegrableOn (planeIntegrand f lam)
      (Set.Ioc (lam - ε) X ×ˢ Set.Ioc (-Y) Y) (volume.prod volume) :=
    integrableOn_planeIntegrand hf hfc lam (lam - ε) X (-Y) Y
  have hBCD : IntegrableOn (planeIntegrand f lam)
      (Set.Ioc (lam + ε) X ×ˢ Set.Ioc (-Y) Y
        ∪ (Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc ε Y
          ∪ Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc (-Y) (-ε))) (volume.prod volume) := by
    refine hcol.mono_set ?_
    rintro p hp
    simp only [Set.mem_prod, Set.mem_union, Set.mem_Ioc] at hp ⊢
    rcases hp with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact ⟨⟨by linarith [hx.1], hx.2⟩, hy⟩
    · exact ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, ⟨by linarith [hy.1, hεY], hy.2⟩⟩
    · exact ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, ⟨hy.1, by linarith [hy.2]⟩⟩
  have hCD' : IntegrableOn (planeIntegrand f lam)
      (Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc ε Y
        ∪ Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc (-Y) (-ε)) (volume.prod volume) := by
    refine hcol.mono_set ?_
    rintro p hp
    simp only [Set.mem_prod, Set.mem_union, Set.mem_Ioc] at hp ⊢
    rcases hp with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact ⟨⟨hx.1, by linarith [hx.2]⟩, ⟨by linarith [hy.1, hεY], hy.2⟩⟩
    · exact ⟨⟨hx.1, by linarith [hx.2]⟩, ⟨hy.1, by linarith [hy.2]⟩⟩
  have hstep1 : (∫ p in (Set.Ioc (-X) (lam - ε) ×ˢ Set.Ioc (-Y) Y)
        ∪ ((Set.Ioc (lam + ε) X ×ˢ Set.Ioc (-Y) Y)
          ∪ ((Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc ε Y)
            ∪ (Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc (-Y) (-ε)))),
        planeIntegrand f lam p)
      = (∫ p in Set.Ioc (-X) (lam - ε) ×ˢ Set.Ioc (-Y) Y, planeIntegrand f lam p
           )
        + ∫ p in (Set.Ioc (lam + ε) X ×ˢ Set.Ioc (-Y) Y)
          ∪ ((Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc ε Y)
            ∪ (Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc (-Y) (-ε))),
            planeIntegrand f lam p :=
    setIntegral_union (hAB.union_right (hAC.union_right hAD))
      (by repeat' first
            | apply MeasurableSet.union
            | exact measurableSet_Ioc.prod measurableSet_Ioc)
      (integrableOn_planeIntegrand hf hfc lam (-X) (lam - ε) (-Y) Y) hBCD
  have hstep2 : (∫ p in (Set.Ioc (lam + ε) X ×ˢ Set.Ioc (-Y) Y)
          ∪ ((Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc ε Y)
            ∪ (Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc (-Y) (-ε))),
        planeIntegrand f lam p)
      = (∫ p in Set.Ioc (lam + ε) X ×ˢ Set.Ioc (-Y) Y, planeIntegrand f lam p
           )
        + ∫ p in (Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc ε Y)
            ∪ (Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc (-Y) (-ε)),
            planeIntegrand f lam p :=
    setIntegral_union (hBC.union_right hBD)
      (by repeat' first
            | apply MeasurableSet.union
            | exact measurableSet_Ioc.prod measurableSet_Ioc)
      (integrableOn_planeIntegrand hf hfc lam (lam + ε) X (-Y) Y) hCD'
  have hstep3 : (∫ p in (Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc ε Y)
          ∪ (Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc (-Y) (-ε)),
        planeIntegrand f lam p)
      = (∫ p in Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc ε Y, planeIntegrand f lam p
           )
        + ∫ p in Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc (-Y) (-ε), planeIntegrand f lam p
            :=
    setIntegral_union hCD (measurableSet_Ioc.prod measurableSet_Ioc)
      (integrableOn_planeIntegrand hf hfc lam (lam - ε) (lam + ε) ε Y)
      (integrableOn_planeIntegrand hf hfc lam (lam - ε) (lam + ε) (-Y) (-ε))
  rw [show holeSurround lam ε X Y
      = (Set.Ioc (-X) (lam - ε) ×ˢ Set.Ioc (-Y) Y)
        ∪ ((Set.Ioc (lam + ε) X ×ˢ Set.Ioc (-Y) Y)
          ∪ ((Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc ε Y)
            ∪ (Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc (-Y) (-ε)))) from rfl,
    hstep1, hstep2, hstep3]
  ring

/-- The plane integrand vanishes off the support of the cut-off extension. -/
lemma planeIntegrand_eq_zero_of_notMem_tsupport {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {lam : ℝ}
    {z : ℂ} (hz : z ∉ tsupport (almostAnalyticExtCut f)) :
    pompeiuIntegrand (almostAnalyticExtCut f) (lam : ℂ) z = 0 := by
  have hzt : almostAnalyticExtCut f =ᶠ[𝓝 z] 0 := by
    rw [← notMem_tsupport_iff_eventuallyEq]; exact hz
  have hfd : fderiv ℝ (almostAnalyticExtCut f) z = 0 := by
    rw [hzt.fderiv_eq]; simp
  simp [pompeiuIntegrand, dbarNum, hfd]



/-- **Area limit**: the sum of the four slab integrals converges to the integral over the big
rectangle, the hole integral tending to zero. -/
lemma tendsto_area_hole {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {lam X Y : ℝ} (hX : |lam| < X) (hY : 2 < Y) :
    Tendsto (fun ε : ℝ =>
        (∫ x : ℝ in -X..lam - ε, ∫ y : ℝ in -Y..Y,
            pompeiuIntegrand (almostAnalyticExtCut f) (lam : ℂ) ((x : ℂ) + (y : ℂ) * I))
        + ((∫ x : ℝ in lam + ε..X, ∫ y : ℝ in -Y..Y,
            pompeiuIntegrand (almostAnalyticExtCut f) (lam : ℂ) ((x : ℂ) + (y : ℂ) * I))
          + ((∫ x : ℝ in lam - ε..lam + ε, ∫ y : ℝ in ε..Y,
              pompeiuIntegrand (almostAnalyticExtCut f) (lam : ℂ) ((x : ℂ) + (y : ℂ) * I))
            + (∫ x : ℝ in lam - ε..lam + ε, ∫ y : ℝ in -Y..-ε,
              pompeiuIntegrand (almostAnalyticExtCut f) (lam : ℂ) ((x : ℂ) + (y : ℂ) * I)))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ p in bigRectSet X Y, planeIntegrand f lam p)) := by
  obtain ⟨M, hM⟩ := exists_norm_pompeiuIntegrand_le hf hfc lam
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hlam1 : lam ≤ |lam| := le_abs_self lam
  have hlam2 : -|lam| ≤ lam := neg_abs_le lam
  have hε₀ : 0 < X - |lam| := by
    have := abs_lt.mp hX; linarith [this.2]
  have hhole : Tendsto (fun ε : ℝ => ∫ p in holeSet lam ε, planeIntegrand f lam p)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun ε : ℝ => M * (4 * ε ^ 2)) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hεpos : (0 : ℝ) < ε := hε
      have hfin : (volume.prod volume) (holeSet lam ε) < ⊤ := by
        rw [holeSet, Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioc]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
      have hle : ‖∫ p in holeSet lam ε, planeIntegrand f lam p‖
          ≤ M * (volume.prod volume).real (holeSet lam ε) := by
        refine norm_setIntegral_le_of_norm_le_const hfin ?_
        intro p _
        exact hM _
      have h1 : lam + ε - (lam - ε) = 2 * ε := by ring
      have h2 : ε - -ε = 2 * ε := by ring
      have hvol : (volume.prod volume).real (holeSet lam ε) = 4 * ε ^ 2 := by
        have hdef : (volume.prod volume).real (holeSet lam ε)
            = ((volume.prod volume) (holeSet lam ε)).toReal := rfl
        rw [hdef, holeSet, Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioc, h1, h2,
          ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith [hεpos] : (0:ℝ) ≤ 2 * ε)]
        ring
      rw [hvol] at hle
      exact hle
    · have h2 : Tendsto (fun ε : ℝ => (4 : ℝ) * ε ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have h : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
          tendsto_id.mono_left nhdsWithin_le_nhds
        simpa using (tendsto_const_nhds.mul (h.pow 2))
      have h3 : Tendsto (fun ε : ℝ => M * (4 * ε ^ 2)) (𝓝[>] (0 : ℝ)) (𝓝 (M * 0)) :=
        h2.const_mul M
      simpa using h3
  have hdec : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      (∫ x : ℝ in -X..lam - ε, ∫ y : ℝ in -Y..Y,
          pompeiuIntegrand (almostAnalyticExtCut f) (lam : ℂ) ((x : ℂ) + (y : ℂ) * I))
        + ((∫ x : ℝ in lam + ε..X, ∫ y : ℝ in -Y..Y,
            pompeiuIntegrand (almostAnalyticExtCut f) (lam : ℂ) ((x : ℂ) + (y : ℂ) * I))
          + ((∫ x : ℝ in lam - ε..lam + ε, ∫ y : ℝ in ε..Y,
              pompeiuIntegrand (almostAnalyticExtCut f) (lam : ℂ) ((x : ℂ) + (y : ℂ) * I))
            + (∫ x : ℝ in lam - ε..lam + ε, ∫ y : ℝ in -Y..-ε,
              pompeiuIntegrand (almostAnalyticExtCut f) (lam : ℂ) ((x : ℂ) + (y : ℂ) * I))))
      = (∫ p in bigRectSet X Y,
            pompeiuIntegrand (almostAnalyticExtCut f) (lam : ℂ) ((p.1 : ℂ) + (p.2 : ℂ) * I))
        - (∫ p in holeSet lam ε,
            pompeiuIntegrand (almostAnalyticExtCut f) (lam : ℂ) ((p.1 : ℂ) + (p.2 : ℂ) * I)) := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0:ℝ) < X - |lam| from hε₀)),
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0:ℝ) < 1 from one_pos))] with ε hε hεX hε1
    have hεpos : (0 : ℝ) < ε := hε
    have hεX' : ε < X - |lam| := hεX
    have hε1' : ε < 1 := hε1
    have hεY : ε < Y := by linarith
    have hsurr : (∫ p in holeSurround lam ε X Y,
        pompeiuIntegrand (almostAnalyticExtCut f) (lam : ℂ) ((p.1 : ℂ) + (p.2 : ℂ) * I))
        = (∫ p in Set.Ioc (-X) (lam - ε) ×ˢ Set.Ioc (-Y) Y,
              pompeiuIntegrand (almostAnalyticExtCut f) (lam : ℂ) ((p.1 : ℂ) + (p.2 : ℂ) * I))
          + ((∫ p in Set.Ioc (lam + ε) X ×ˢ Set.Ioc (-Y) Y,
              pompeiuIntegrand (almostAnalyticExtCut f) (lam : ℂ) ((p.1 : ℂ) + (p.2 : ℂ) * I))
            + ((∫ p in Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc ε Y,
              pompeiuIntegrand (almostAnalyticExtCut f) (lam : ℂ) ((p.1 : ℂ) + (p.2 : ℂ) * I))
              + (∫ p in Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc (-Y) (-ε),
              pompeiuIntegrand (almostAnalyticExtCut f) (lam : ℂ) ((p.1 : ℂ) + (p.2 : ℂ) * I)))) := by
      have h := setIntegral_holeSurround_eq (f := f) hf hfc hε hX hεX hεY
      simpa only [planeIntegrand, add_assoc] using h
    rw [integral_interval_prod_pompeiuIntegrand hf hfc lam
        (by linarith [hεX', hlam2] : -X ≤ lam - ε) (by linarith : -Y ≤ Y),
      integral_interval_prod_pompeiuIntegrand hf hfc lam
        (by linarith [hεX', hlam1] : lam + ε ≤ X) (by linarith : -Y ≤ Y),
      integral_interval_prod_pompeiuIntegrand hf hfc lam
        (by linarith [hεpos] : lam - ε ≤ lam + ε) (by linarith [hεY] : ε ≤ Y),
      integral_interval_prod_pompeiuIntegrand hf hfc lam
        (by linarith [hεpos] : lam - ε ≤ lam + ε) (by linarith [hεY] : -Y ≤ -ε),
      ← hsurr, bigRectSet_eq_holeSurround_union hX hY hε hεX hεY]
    have hdisj : Disjoint (holeSurround lam ε X Y) (holeSet lam ε) := by
      rw [Set.disjoint_left]
      intro p hp hq
      rw [holeSurround] at hp
      simp only [holeSet, Set.mem_prod, Set.mem_union, Set.mem_Ioc] at hp hq
      rcases hp with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
      · linarith [hx.1, hx.2, hq.1, hq.2]
      · linarith [hx.1, hx.2, hq.1, hq.2]
      · linarith [hx.1, hx.2, hq.1, hq.2]
      · linarith [hx.1, hx.2, hq.1, hq.2]
    rw [setIntegral_union (f := fun p : ℝ × ℝ =>
        pompeiuIntegrand (almostAnalyticExtCut f) (lam : ℂ) ((p.1 : ℂ) + (p.2 : ℂ) * I))
      hdisj (measurableSet_holeSet lam ε)
      (by
        have hbig : IntegrableOn (planeIntegrand f lam)
            (Set.Ioc (-X) X ×ˢ Set.Ioc (-Y) Y) (volume.prod volume) :=
          integrableOn_planeIntegrand hf hfc lam (-X) X (-Y) Y
        refine hbig.mono_set ?_
        intro p hp
        rw [holeSurround] at hp
        simp only [Set.mem_prod, Set.mem_union, Set.mem_Ioc] at hp ⊢
        rcases hp with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
        · exact ⟨⟨hx.1, by linarith [hx.2]⟩, hy⟩
        · exact ⟨⟨by linarith [hx.1], hx.2⟩, hy⟩
        · exact ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, ⟨by linarith [hy.1], hy.2⟩⟩
        · exact ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, ⟨hy.1, by linarith [hy.2]⟩⟩)
      (integrableOn_planeIntegrand hf hfc lam (lam - ε) (lam + ε) (-ε) ε)]
    ring
  have hlim : Tendsto (fun ε : ℝ => (∫ p in bigRectSet X Y,
        pompeiuIntegrand (almostAnalyticExtCut f) (lam : ℂ) ((p.1 : ℂ) + (p.2 : ℂ) * I))
        - (∫ p in holeSet lam ε,
            pompeiuIntegrand (almostAnalyticExtCut f) (lam : ℂ) ((p.1 : ℂ) + (p.2 : ℂ) * I)))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ p in bigRectSet X Y,
        pompeiuIntegrand (almostAnalyticExtCut f) (lam : ℂ) ((p.1 : ℂ) + (p.2 : ℂ) * I))) := by
    have h := hhole.const_sub (∫ p in bigRectSet X Y,
      pompeiuIntegrand (almostAnalyticExtCut f) (lam : ℂ) ((p.1 : ℂ) + (p.2 : ℂ) * I))
    simpa using h
  exact hlim.congr' (by filter_upwards [hdec] with ε hε; exact hε.symm)

/-- Off the strip `|Im z| ≤ 2` the cut-off extension vanishes. -/
lemma almostAnalyticExtCut_eq_zero_of_two_le_abs_im {f : ℝ → ℝ} {z : ℂ} (h : 2 ≤ |z.im|) :
    almostAnalyticExtCut f z = 0 := by
  rw [almostAnalyticExtCut, yCut_zero_of_two_le h, Complex.ofReal_zero, mul_zero]

/-- Points with `|Im z| > 2` are not in the support of the cut-off extension. -/
lemma notMem_tsupport_almostAnalyticExtCut_of_lt_abs_im {f : ℝ → ℝ} {z : ℂ}
    (h : 2 < |z.im|) : z ∉ tsupport (almostAnalyticExtCut f) := by
  rw [notMem_tsupport_iff_eventuallyEq]
  filter_upwards [((Complex.continuous_im.abs).continuousAt.eventually (Ioi_mem_nhds h))] with w hw
  exact almostAnalyticExtCut_eq_zero_of_two_le_abs_im (le_of_lt hw)

/-- Points with `|Re z| ≥ X` are not in the support, provided `X` dominates `|Re|` there. -/
lemma notMem_tsupport_of_le_abs_re {f : ℝ → ℝ} {X : ℝ}
    (hXsupp : ∀ z ∈ tsupport (almostAnalyticExtCut f), |z.re| < X) {z : ℂ} (h : X ≤ |z.re|) :
    z ∉ tsupport (almostAnalyticExtCut f) := by
  intro hz
  linarith [hXsupp z hz]

/-- **Cauchy–Pompeiu representation of the cut-off extension.**  For a `C²` compactly supported
`f` and every real `lam` one has
`f lam = (i / 2π) ∫∫ ∂̄F(z)/(z - lam) dx dy` with `F` the cut-off almost-analytic extension. -/
theorem pompeiu_plane {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (lam : ℝ) :
    (f lam : ℂ) = (I / (2 * (Real.pi : ℂ))) *
      ∫ x : ℝ, ∫ y : ℝ,
        pompeiuIntegrand (almostAnalyticExtCut f) (lam : ℂ) ((x : ℂ) + (y : ℂ) * I) := by
  have hF1 : ContDiff ℝ 1 (almostAnalyticExtCut f) := contDiff_almostAnalyticExtCut_one hf
  have hFc : Continuous (almostAnalyticExtCut f) := hF1.continuous
  obtain ⟨C, hC, hLip⟩ := exists_lipschitz_almostAnalyticExtCut hf hfc
  -- the horizontal bound `X` and the vertical bound `Y = 3`
  have hKc : IsCompact (tsupport (almostAnalyticExtCut f)) :=
    hasCompactSupport_almostAnalyticExtCut hfc
  have hKr : IsCompact (Complex.re '' tsupport (almostAnalyticExtCut f)) :=
    hKc.image Complex.continuous_re
  obtain ⟨X₀, hX₀⟩ := hKr.exists_bound_of_continuousOn continuous_id.continuousOn
  set X : ℝ := max X₀ |lam| + 1 with hXdef
  have hX₀X : X₀ < X := by
    rw [hXdef]; have := le_max_left X₀ |lam|; linarith
  have hX : |lam| < X := by
    rw [hXdef]; have := le_max_right X₀ |lam|; linarith
  have hXpos : (0 : ℝ) < X := by
    rw [hXdef]; have := le_max_right X₀ |lam|; have := abs_nonneg lam; linarith
  have hXsupp : ∀ z ∈ tsupport (almostAnalyticExtCut f), |z.re| < X := by
    intro z hz
    have h1 : ‖z.re‖ ≤ X₀ := hX₀ _ ⟨z, hz, rfl⟩
    have h2 : |z.re| ≤ X₀ := by simpa [Real.norm_eq_abs] using h1
    linarith
  have hY : (2 : ℝ) < 3 := by norm_num
  -- the two limits
  have hlimB : Tendsto (fun ε : ℝ => rectBoundary
      (fun z => almostAnalyticExtCut f z / (z - (lam : ℂ)))
      ((lam : ℂ).re - ε) ((lam : ℂ).re + ε) ((lam : ℂ).im - ε) ((lam : ℂ).im + ε))
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * (Real.pi : ℂ) * I * (f lam : ℂ))) := by
    have h := tendsto_boundary_hole (F := almostAnalyticExtCut f) hFc hC
      (fun z => hLip z (lam : ℂ))
    simpa [almostAnalyticExtCut_ofReal] using h
  have hlimA := tendsto_area_hole (f := f) hf hfc (lam := lam) (X := X) (Y := 3) hX hY
  -- the master identity at every small scale
  have hident : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      - rectBoundary (fun z => almostAnalyticExtCut f z / (z - (lam : ℂ)))
          (lam - ε) (lam + ε) (-ε) ε
        = (∫ x : ℝ in -X..lam - ε, ∫ y : ℝ in -3..3,
            pompeiuIntegrand (almostAnalyticExtCut f) (lam : ℂ) ((x : ℂ) + (y : ℂ) * I))
          + ((∫ x : ℝ in lam + ε..X, ∫ y : ℝ in -3..3,
              pompeiuIntegrand (almostAnalyticExtCut f) (lam : ℂ) ((x : ℂ) + (y : ℂ) * I))
            + ((∫ x : ℝ in lam - ε..lam + ε, ∫ y : ℝ in ε..3,
              pompeiuIntegrand (almostAnalyticExtCut f) (lam : ℂ) ((x : ℂ) + (y : ℂ) * I))
              + (∫ x : ℝ in lam - ε..lam + ε, ∫ y : ℝ in -3..-ε,
              pompeiuIntegrand (almostAnalyticExtCut f) (lam : ℂ) ((x : ℂ) + (y : ℂ) * I)))) := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0:ℝ) < X - |lam| from by
        have := abs_lt.mp hX; linarith [this.2])),
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0:ℝ) < (1:ℝ) from one_pos)),
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0:ℝ) < (3:ℝ) from by norm_num))] with ε hε hεX hε1 hε3
    have hεpos : (0 : ℝ) < ε := hε
    have hεX' : ε < X - |lam| := hεX
    have hlam1 : lam ≤ |lam| := le_abs_self lam
    have hlam2 : -|lam| ≤ lam := neg_abs_le lam
    have hε3' : ε < 3 := hε3
    -- the boundary functional over the big rectangle vanishes
    have hbnd0 : rectBoundary (fun z => almostAnalyticExtCut f z / (z - (lam : ℂ)))
        (-X) X (-3) 3 = 0 := by
      have hzero : ∀ z : ℂ, |z.re| ≥ X ∨ |z.im| ≥ 3 →
          almostAnalyticExtCut f z / (z - (lam : ℂ)) = 0 := by
        intro z hz
        have hz0 : almostAnalyticExtCut f z = 0 := by
          rcases hz with h | h
          · exact image_eq_zero_of_notMem_tsupport
              (notMem_tsupport_of_le_abs_re hXsupp h)
          · exact almostAnalyticExtCut_eq_zero_of_two_le_abs_im (by linarith)
        rw [hz0, zero_div]
      simp only [rectBoundary]
      have h1 : (∫ x : ℝ in -X..X,
          almostAnalyticExtCut f ((x : ℂ) + ((-3 : ℝ) : ℂ) * I) /
            (((x : ℂ) + ((-3 : ℝ) : ℂ) * I) - (lam : ℂ))) = 0 := by
        rw [show (0 : ℂ) = ∫ x : ℝ in -X..X, (0 : ℂ) from by simp]
        refine intervalIntegral.integral_congr (fun x _ => ?_)
        exact hzero _ (Or.inr (by simp))
      have h2 : (∫ x : ℝ in -X..X,
          almostAnalyticExtCut f ((x : ℂ) + ((3 : ℝ) : ℂ) * I) /
            (((x : ℂ) + ((3 : ℝ) : ℂ) * I) - (lam : ℂ))) = 0 := by
        rw [show (0 : ℂ) = ∫ x : ℝ in -X..X, (0 : ℂ) from by simp]
        refine intervalIntegral.integral_congr (fun x _ => ?_)
        exact hzero _ (Or.inr (by simp))
      have h3 : (∫ y : ℝ in -3..3,
          almostAnalyticExtCut f (((X : ℝ) : ℂ) + (y : ℂ) * I) /
            ((((X : ℝ) : ℂ) + (y : ℂ) * I) - (lam : ℂ))) = 0 := by
        rw [show (0 : ℂ) = ∫ y : ℝ in -3..3, (0 : ℂ) from by simp]
        refine intervalIntegral.integral_congr (fun y _ => ?_)
        refine hzero _ (Or.inl ?_)
        have hz : ((↑X : ℂ) + ↑y * I).re = X := by simp
        rw [hz, abs_of_nonneg hXpos.le]
      have h4 : (∫ y : ℝ in -3..3,
          almostAnalyticExtCut f (((-X : ℝ) : ℂ) + (y : ℂ) * I) /
            ((((-X : ℝ) : ℂ) + (y : ℂ) * I) - (lam : ℂ))) = 0 := by
        rw [show (0 : ℂ) = ∫ y : ℝ in -3..3, (0 : ℂ) from by simp]
        refine intervalIntegral.integral_congr (fun y _ => ?_)
        refine hzero _ (Or.inl ?_)
        have hz : ((↑(-X) : ℂ) + ↑y * I).re = -X := by simp
        rw [hz, abs_of_nonpos (by linarith : (-X : ℝ) ≤ 0)]
        linarith
      rw [h1, h2, h3, h4]
      ring
    -- apply the hole identity
    have hmain := rectBoundary_sub_hole_eq (F := almostAnalyticExtCut f) hF1
      (a := -X) (b := X) (c := -3) (d := 3) (lam := (lam : ℂ)) hεpos
      (show -X < (lam : ℂ).re - ε by
        simp only [Complex.ofReal_re]; linarith [hεX', hlam2])
      (show (lam : ℂ).re + ε < X by
        simp only [Complex.ofReal_re]; linarith [hεX', hlam1])
      (show (-3 : ℝ) < (lam : ℂ).im - ε by
        simp only [Complex.ofReal_im]; linarith)
      (show (lam : ℂ).im + ε < 3 by
        simp only [Complex.ofReal_im]; linarith)
    rw [hbnd0] at hmain
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_sub, zero_add] at hmain
    rw [hmain]
    ring
  -- take limits
  have hneg : Tendsto (fun ε : ℝ => - rectBoundary
      (fun z => almostAnalyticExtCut f z / (z - (lam : ℂ))) (lam - ε) (lam + ε) (-ε) ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (-(2 * (Real.pi : ℂ) * I * (f lam : ℂ)))) := by
    simpa using hlimB.neg
  have hsum : Tendsto (fun ε : ℝ =>
      (∫ x : ℝ in -X..lam - ε, ∫ y : ℝ in -3..3,
          pompeiuIntegrand (almostAnalyticExtCut f) (lam : ℂ) ((x : ℂ) + (y : ℂ) * I))
        + ((∫ x : ℝ in lam + ε..X, ∫ y : ℝ in -3..3,
            pompeiuIntegrand (almostAnalyticExtCut f) (lam : ℂ) ((x : ℂ) + (y : ℂ) * I))
          + ((∫ x : ℝ in lam - ε..lam + ε, ∫ y : ℝ in ε..3,
              pompeiuIntegrand (almostAnalyticExtCut f) (lam : ℂ) ((x : ℂ) + (y : ℂ) * I))
            + (∫ x : ℝ in lam - ε..lam + ε, ∫ y : ℝ in -3..-ε,
              pompeiuIntegrand (almostAnalyticExtCut f) (lam : ℂ) ((x : ℂ) + (y : ℂ) * I)))))
      (𝓝[>] (0 : ℝ)) (𝓝 (-(2 * (Real.pi : ℂ) * I * (f lam : ℂ)))) :=
    hneg.congr' (by filter_upwards [hident] with ε hε; exact hε)
  have hval : (-(2 * (Real.pi : ℂ) * I * (f lam : ℂ)))
      = ∫ p in bigRectSet X 3, planeIntegrand f lam p :=
    tendsto_nhds_unique hsum hlimA
  -- algebra
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have h2pi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    have : (2 : ℂ) ≠ 0 := by norm_num
    exact mul_ne_zero this hpi
  have hkey : (2 * (Real.pi : ℂ) * I) * (f lam : ℂ) = - ∫ p in bigRectSet X 3, planeIntegrand f lam p := by
    have := hval
    linear_combination -this
  have halg : (f lam : ℂ) = (I / (2 * (Real.pi : ℂ))) * (∫ p in bigRectSet X 3, planeIntegrand f lam p) := by
    have h1 : (f lam : ℂ) = -(∫ p in bigRectSet X 3, planeIntegrand f lam p) /
        (2 * (Real.pi : ℂ) * I) := by
      rw [eq_div_iff (mul_ne_zero h2pi hI)]
      rw [mul_comm (f lam : ℂ) (2 * (Real.pi : ℂ) * I)]
      exact hkey
    rw [h1]
    rw [show -(∫ p in bigRectSet X 3, planeIntegrand f lam p) / (2 * (Real.pi : ℂ) * I)
        = -(∫ p in bigRectSet X 3, planeIntegrand f lam p) * (2 * (Real.pi : ℂ) * I)⁻¹
        from rfl]
    rw [show (2 * (Real.pi : ℂ) * I)⁻¹ = -I / (2 * (Real.pi : ℂ)) from by
      have hIinv : (I : ℂ)⁻¹ = -I := by
        rw [inv_eq_of_mul_eq_one_right]
        rw [mul_neg, Complex.I_mul_I]
        norm_num
      rw [show (2 * (Real.pi : ℂ) * I) = (2 * (Real.pi : ℂ)) * I from rfl, mul_inv, hIinv,
        div_eq_mul_inv]
      ring]
    ring
  rw [halg]
  congr 1
  -- the plane integral equals the integral over the big rectangle
  have hconv : (∫ p in bigRectSet X 3, planeIntegrand f lam p)
      = ∫ x : ℝ, ∫ y : ℝ,
          pompeiuIntegrand (almostAnalyticExtCut f) (lam : ℂ) ((x : ℂ) + (y : ℂ) * I) := by
    rw [show bigRectSet X 3 = Set.Ioc (-X) X ×ˢ Set.Ioc (-3 : ℝ) 3 from rfl]
    change (∫ p in Set.Ioc (-X) X ×ˢ Set.Ioc (-3 : ℝ) 3, planeIntegrand f lam p
        ∂(volume.prod volume))
      = ∫ x : ℝ, ∫ y : ℝ,
          pompeiuIntegrand (almostAnalyticExtCut f) (lam : ℂ) ((x : ℂ) + (y : ℂ) * I)
    rw [setIntegral_prod _ (integrableOn_planeIntegrand hf hfc lam (-X) X (-3) 3)]
    have hinner : ∀ x : ℝ, (∫ y : ℝ in Set.Ioc (-3 : ℝ) 3, planeIntegrand f lam (x, y))
        = ∫ y : ℝ, planeIntegrand f lam (x, y) := by
      intro x
      refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => ?_)
      rw [Set.mem_Ioc, not_and_or] at hy
      have hy2 : 2 < |y| := by
        rcases hy with h | h
        · rw [not_lt] at h
          rw [abs_of_nonpos (by linarith)]
          linarith
        · rw [not_le] at h
          rw [abs_of_pos (by linarith)]
          linarith
      have hy2' : 2 < |(((x : ℂ) + (y : ℂ) * I)).im| := by simpa using hy2
      exact planeIntegrand_eq_zero_of_notMem_tsupport hf
        (notMem_tsupport_almostAnalyticExtCut_of_lt_abs_im hy2')
    have houter : (∫ x : ℝ in Set.Ioc (-X) X, ∫ y : ℝ, planeIntegrand f lam (x, y))
        = ∫ x : ℝ, ∫ y : ℝ, planeIntegrand f lam (x, y) := by
      refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)
      rw [Set.mem_Ioc, not_and_or] at hx
      have hx2 : X ≤ |x| := by
        rcases hx with h | h
        · rw [not_lt] at h
          rw [abs_of_nonpos (by linarith)]
          linarith
        · rw [not_le] at h
          rw [abs_of_pos (by linarith)]
          linarith
      have hzero : (fun y : ℝ => planeIntegrand f lam (x, y)) = fun _ => 0 := by
        funext y
        refine planeIntegrand_eq_zero_of_notMem_tsupport hf
          (notMem_tsupport_of_le_abs_re hXsupp ?_)
        have hre : (((x : ℂ) + (y : ℂ) * I)).re = x := by simp
        rw [hre]
        exact hx2
      rw [hzero]
      simp
    simp only [hinner, houter]

  exact hconv

end

end GUEStrongConvergence
