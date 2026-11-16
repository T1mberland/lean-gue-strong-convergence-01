/-
# Higher-order almost-analytic (Helffer--Sjöstrand) extensions

The first-order extension `almostAnalyticExt f z = f x + i y f' x` of
`Probability/HelfferSjostrand.lean` has `∂̄` vanishing only *linearly* on the real axis.  When it is
paired with the trivial resolvent comparison bound `‖g_N − g‖ ≤ 2d/|Im z|` and integrated over the
strip `|Im z| < η_A`, the linear vanishing produces an `N`-independent constant.

This file builds the standard higher-order cure: for `f : ℝ → ℝ` and `k ≥ 1` set

  `ext_k f (x + i y) = ∑_{j<k} (i y)^j / j! · f^{(j)}(x)`,

with `f^{(j)}` implemented as `iteratedDeriv j f`.  Then

  `∂̄ ext_k = (i/2) · (i y)^{k-1}/(k-1)! · f^{(k)}(x) + (cut-off terms)`,

so the `∂̄` term vanishes to order `k-1` at the real axis.  Composing with the bump `yCut` in the
imaginary direction gives a smooth compactly supported extension `almostAnalyticExtOrderCut k f`
which agrees with `f` on `ℝ` and whose `∂̄` obeys `‖∂̄‖ ≤ |y|^{k-1}/(k-1)! · M` on `|y| < 1` whenever
`‖f^{(k)}‖ ≤ M`.

## Main results

* `extOrderTerm` — the `j`-th summand; `almostAnalyticExtOrder k f` — the order-`k` extension;
* `almostAnalyticExtOrder_ofReal` — it agrees with `f` on the real axis (for `1 ≤ k`);
* `hasFDerivAt_almostAnalyticExtOrder`, `fderiv_almostAnalyticExtOrder_one`,
  `fderiv_almostAnalyticExtOrder_I` — its real Fréchet derivative;
* `dbar_almostAnalyticExtOrder` — the exact `∂̄` formula
  `I • fderiv (ext_{k+1}) z 1 − fderiv (ext_{k+1}) z I = I · (I y)^k / k! · f^{(k+1)}(x)`;
* `norm_dbar_almostAnalyticExtOrder_le` — the bound `‖∂̄‖ ≤ |y|^k / k! · M`;
* `almostAnalyticExtOrderCut`, `hasCompactSupport_almostAnalyticExtOrderCut`,
  `dbar_almostAnalyticExtOrderCut`, `norm_dbar_almostAnalyticExtOrderCut_le`;
* `norm_strip_integral_dbar_order_le` — **weighted strip estimate**:
  `‖∫_{-η}^{η}∫_{-X}^{X} ∂̄F · |y|^{-β}‖ ≤ (M/k!) · (2X) · η^{k-β} · 2η` for `β < k`, `η < 1`;
  the weight `|y|^{-β}` is where a resolvent-difference bound `‖g_N − g‖ ≤ C|y|^{-β}` enters, so
  a bound with coefficient `C = C₀/N²` gives a strip contribution `O(N⁻²)`;
* `exists_norm_dbarNumOrder_le`, `norm_far_integral_dbar_order_le` — global `∂̄` bound and the
  **far-region estimate** `‖∫_c^d∫_{-X}^{X} ∂̄F · |y|^{-5}‖ ≤ B · (2X) · η₀^{-5} · (d-c)` for
  `η₀ ≤ c ≤ d`, `η₀ > 0`.
-/
import GUEStrongConvergence.Probability.HelfferSjostrand

open MeasureTheory Set Filter Topology intervalIntegral
open Complex
open scoped Real Topology NNReal ENNReal Interval

namespace GUEStrongConvergence

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

/-! ## The higher-order almost-analytic extension -/

/-- The `j`-th summand `(i y)^j / j! · f^{(j)}(x)` of the order-`k` extension. -/
def extOrderTerm (j : ℕ) (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  (I * (z.im : ℂ)) ^ j / (j.factorial : ℂ) * ((iteratedDeriv j f z.re : ℝ) : ℂ)

/-- The order-`k` almost-analytic (Helffer--Sjöstrand) extension
`z ↦ ∑_{j<k} (i Im z)^j / j! · f^{(j)}(Re z)`. -/
def almostAnalyticExtOrder (k : ℕ) (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range k, extOrderTerm j f z

/-- The extension as a function-level finite sum of the summands. -/
lemma almostAnalyticExtOrder_eq_funSum (k : ℕ) (f : ℝ → ℝ) :
    almostAnalyticExtOrder k f = ∑ j ∈ Finset.range k, extOrderTerm j f := by
  funext z
  simp [almostAnalyticExtOrder, Finset.sum_apply]

/-- The `k`-th "boundary" profile `(i y)^{k-1}/(k-1)! · f^{(k)}(x)` appearing in the `∂̄` of the
order-`k` extension.  It is `0` for `k = 0`. -/
def extOrderDbarProfile (k : ℕ) (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  if k = 0 then 0 else
    (I * (z.im : ℂ)) ^ (k - 1) / ((k - 1).factorial : ℂ) * ((iteratedDeriv k f z.re : ℝ) : ℂ)

@[simp]
lemma extOrderDbarProfile_zero (f : ℝ → ℝ) (z : ℂ) : extOrderDbarProfile 0 f z = 0 := by
  simp [extOrderDbarProfile]

lemma extOrderDbarProfile_succ (k : ℕ) (f : ℝ → ℝ) (z : ℂ) :
    extOrderDbarProfile (k + 1) f z =
      (I * (z.im : ℂ)) ^ k / (k.factorial : ℂ) * ((iteratedDeriv (k + 1) f z.re : ℝ) : ℂ) := by
  simp [extOrderDbarProfile]

lemma extOrderTerm_apply (j : ℕ) (f : ℝ → ℝ) (z : ℂ) :
    extOrderTerm j f z =
      (I * (z.im : ℂ)) ^ j / (j.factorial : ℂ) * ((iteratedDeriv j f z.re : ℝ) : ℂ) := rfl

/-- The order-`k` extension agrees with `f` on the real axis (for `1 ≤ k`). -/
@[simp]
lemma almostAnalyticExtOrder_ofReal (k : ℕ) (hk : 1 ≤ k) (f : ℝ → ℝ) (x : ℝ) :
    almostAnalyticExtOrder k f (x : ℂ) = (f x : ℂ) := by
  have hmem : 0 ∈ Finset.range k := Finset.mem_range.mpr hk
  rw [almostAnalyticExtOrder, Finset.sum_eq_single 0]
  · simp [extOrderTerm]
  · intro j _ hj
    simp [extOrderTerm, zero_pow hj]
  · intro h
    exact absurd hmem h

/-! ## The real Fréchet derivative of a single summand -/

/-- **The real Fréchet derivative of the `j`-th summand** of the order-`k` extension, for
`j < k`.  The `x`-dependence contributes through `f^{(j+1)}` and the `y`-dependence through
`f^{(j)}`. -/
theorem hasFDerivAt_extOrderTerm {f : ℝ → ℝ} {k j : ℕ} (hf : ContDiff ℝ k f) (hj : j < k)
    (z : ℂ) :
    HasFDerivAt (extOrderTerm j f)
      (ContinuousLinearMap.smulRight Complex.reCLM
          ((I * (z.im : ℂ)) ^ j / (j.factorial : ℂ)
            * ((iteratedDeriv (j + 1) f z.re : ℝ) : ℂ))
        + ContinuousLinearMap.smulRight Complex.imCLM
          ((((j : ℂ) * (I * (z.im : ℂ)) ^ (j - 1) * I) / (j.factorial : ℂ))
            * ((iteratedDeriv j f z.re : ℝ) : ℂ))) z := by
  have hfj : Differentiable ℝ (iteratedDeriv j f) :=
    hf.differentiable_iteratedDeriv j (by exact_mod_cast hj)
  have hg : HasFDerivAt (fun w : ℂ => ((iteratedDeriv j f w.re : ℝ) : ℂ))
      (ContinuousLinearMap.smulRight Complex.reCLM
        ((iteratedDeriv (j + 1) f z.re : ℝ) : ℂ)) z := by
    refine hasFDerivAt_ofReal_comp_re ?_
    rw [iteratedDeriv_succ]
    exact hfj.differentiableAt.hasDerivAt
  have hu : HasFDerivAt (fun w : ℂ => (I * (w.im : ℂ)) ^ j / (j.factorial : ℂ))
      (ContinuousLinearMap.smulRight Complex.imCLM
        (((j : ℂ) * (I * (z.im : ℂ)) ^ (j - 1) * I) / (j.factorial : ℂ))) z := by
    have hbase : HasFDerivAt (fun w : ℂ => I * (w.im : ℂ))
        (ContinuousLinearMap.smulRight Complex.imCLM I) z := by
      have h := (hasFDerivAt_ofReal_comp_im z).const_mul I
      convert h using 1
      ext v
      simp
      ring
    have hdiv : HasFDerivAt (fun w : ℂ => (I * (w.im : ℂ)) ^ j / (j.factorial : ℂ))
        (((j.factorial : ℂ))⁻¹ •
          ((j • (I * (z.im : ℂ)) ^ (j - 1)) • ContinuousLinearMap.smulRight Complex.imCLM I)) z := by
      have := (hbase.pow j).const_mul ((j.factorial : ℂ))⁻¹
      simpa [div_eq_inv_mul] using this
    convert hdiv using 1
    ext v
    simp
    ring
  have hmul := hu.mul hg
  convert hmul using 1
  · ext w
    simp [extOrderTerm, div_eq_inv_mul]
  · ext v
    simp
    ring

/-- The derivative of the `j`-th summand in the real direction. -/
theorem fderiv_extOrderTerm_one {f : ℝ → ℝ} {k j : ℕ} (hf : ContDiff ℝ k f) (hj : j < k) (z : ℂ) :
    fderiv ℝ (extOrderTerm j f) z 1 =
      (I * (z.im : ℂ)) ^ j / (j.factorial : ℂ) * ((iteratedDeriv (j + 1) f z.re : ℝ) : ℂ) := by
  rw [(hasFDerivAt_extOrderTerm hf hj z).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
    Complex.reCLM_apply, Complex.imCLM_apply, Complex.one_re, Complex.one_im, Complex.ofReal_one,
    Complex.ofReal_zero, zero_smul, add_zero, one_smul]

/-- The derivative of the `j`-th summand in the imaginary direction. -/
theorem fderiv_extOrderTerm_I {f : ℝ → ℝ} {k j : ℕ} (hf : ContDiff ℝ k f) (hj : j < k) (z : ℂ) :
    fderiv ℝ (extOrderTerm j f) z I =
      (((j : ℂ) * (I * (z.im : ℂ)) ^ (j - 1) * I) / (j.factorial : ℂ))
        * ((iteratedDeriv j f z.re : ℝ) : ℂ) := by
  rw [(hasFDerivAt_extOrderTerm hf hj z).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
    Complex.reCLM_apply, Complex.imCLM_apply, Complex.I_re, Complex.I_im, Complex.ofReal_one,
    Complex.ofReal_zero, zero_smul, zero_add, one_smul]

/-! ## The derivative of the full extension -/

/-- **The real Fréchet derivative of the order-`k` extension.** -/
theorem hasFDerivAt_almostAnalyticExtOrder {f : ℝ → ℝ} {k : ℕ} (hf : ContDiff ℝ k f) (z : ℂ) :
    HasFDerivAt (almostAnalyticExtOrder k f)
      (∑ j ∈ Finset.range k,
        (ContinuousLinearMap.smulRight Complex.reCLM
            ((I * (z.im : ℂ)) ^ j / (j.factorial : ℂ)
              * ((iteratedDeriv (j + 1) f z.re : ℝ) : ℂ))
          + ContinuousLinearMap.smulRight Complex.imCLM
            ((((j : ℂ) * (I * (z.im : ℂ)) ^ (j - 1) * I) / (j.factorial : ℂ))
              * ((iteratedDeriv j f z.re : ℝ) : ℂ)))) z := by
  have h := HasFDerivAt.sum (u := Finset.range k)
    (A := fun j => extOrderTerm j f)
    (A' := fun j =>
      (ContinuousLinearMap.smulRight Complex.reCLM
          ((I * (z.im : ℂ)) ^ j / (j.factorial : ℂ)
            * ((iteratedDeriv (j + 1) f z.re : ℝ) : ℂ))
        + ContinuousLinearMap.smulRight Complex.imCLM
          ((((j : ℂ) * (I * (z.im : ℂ)) ^ (j - 1) * I) / (j.factorial : ℂ))
            * ((iteratedDeriv j f z.re : ℝ) : ℂ))))
    (fun j hj => hasFDerivAt_extOrderTerm hf (Finset.mem_range.mp hj) z)
  rw [almostAnalyticExtOrder_eq_funSum]
  exact h

/-- The derivative of the order-`k` extension in the real direction. -/
theorem fderiv_almostAnalyticExtOrder_one {f : ℝ → ℝ} {k : ℕ} (hf : ContDiff ℝ k f) (z : ℂ) :
    fderiv ℝ (almostAnalyticExtOrder k f) z 1 =
      ∑ j ∈ Finset.range k,
        ((I * (z.im : ℂ)) ^ j / (j.factorial : ℂ)
          * ((iteratedDeriv (j + 1) f z.re : ℝ) : ℂ)) := by
  rw [(hasFDerivAt_almostAnalyticExtOrder hf z).fderiv]
  rw [sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
    Complex.reCLM_apply, Complex.imCLM_apply, Complex.one_re, Complex.one_im, Complex.ofReal_one,
    Complex.ofReal_zero, zero_smul, add_zero, one_smul]

/-- The derivative of the order-`k` extension in the imaginary direction. -/
theorem fderiv_almostAnalyticExtOrder_I {f : ℝ → ℝ} {k : ℕ} (hf : ContDiff ℝ k f) (z : ℂ) :
    fderiv ℝ (almostAnalyticExtOrder k f) z I =
      ∑ j ∈ Finset.range k,
        ((((j : ℂ) * (I * (z.im : ℂ)) ^ (j - 1) * I) / (j.factorial : ℂ))
          * ((iteratedDeriv j f z.re : ℝ) : ℂ)) := by
  rw [(hasFDerivAt_almostAnalyticExtOrder hf z).fderiv]
  rw [sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
    Complex.reCLM_apply, Complex.imCLM_apply, Complex.I_re, Complex.I_im, Complex.ofReal_one,
    Complex.ofReal_zero, zero_smul, zero_add, one_smul]

/-! ## The `∂̄` of the higher-order extension -/

/-- **The `∂̄` of a single summand telescopes.**  The `j`-th summand contributes
`I · W_{j+1} − I · W_j`, where `W_j` is the profile `extOrderDbarProfile j`. -/
theorem dbar_extOrderTerm {f : ℝ → ℝ} {k j : ℕ} (hf : ContDiff ℝ k f) (hj : j < k) (z : ℂ) :
    I • fderiv ℝ (extOrderTerm j f) z 1 - fderiv ℝ (extOrderTerm j f) z I =
      I * extOrderDbarProfile (j + 1) f z - I * extOrderDbarProfile j f z := by
  rw [fderiv_extOrderTerm_one hf hj, fderiv_extOrderTerm_I hf hj,
    extOrderDbarProfile_succ]
  rcases j with _ | j
  · simp only [extOrderDbarProfile_zero, mul_zero, sub_zero]
    simp
  · have hfact : ((j + 1).factorial : ℂ) = (((j + 1 : ℕ)) : ℂ) * (j.factorial : ℂ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hfac1_ne : (((j + 1).factorial : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (j + 1)
    have hfac_ne : ((j.factorial : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero j
    have hj1 : (((j + 1 : ℕ)) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    simp only [extOrderDbarProfile_succ, Nat.add_sub_cancel, smul_eq_mul]
    field_simp
    rw [hfact]
    ring

/-- **The exact `∂̄` of the order-`k+1` extension**, in profile form:
`I • fderiv (ext_{k+1}) z 1 − fderiv (ext_{k+1}) z I = I · extOrderDbarProfile (k+1) f z`. -/
theorem dbar_almostAnalyticExtOrder_profile {f : ℝ → ℝ} (k : ℕ) {K : ℕ}
    (hf : ContDiff ℝ K f) (hK : k + 1 ≤ K) (z : ℂ) :
    I • fderiv ℝ (almostAnalyticExtOrder (k + 1) f) z 1
        - fderiv ℝ (almostAnalyticExtOrder (k + 1) f) z I =
      I * extOrderDbarProfile (k + 1) f z := by
  induction k with
  | zero =>
    have hfun : almostAnalyticExtOrder 1 f = extOrderTerm 0 f := by
      funext w
      simp [almostAnalyticExtOrder]
    have h := dbar_extOrderTerm (f := f) (k := K) (j := 0) hf (by omega) z
    rw [hfun]
    simpa [extOrderDbarProfile] using h
  | succ k ih =>
    have hfun : almostAnalyticExtOrder (k + 2) f
        = fun w => almostAnalyticExtOrder (k + 1) f w + extOrderTerm (k + 1) f w := by
      funext w
      simp only [almostAnalyticExtOrder, Finset.sum_range_succ]
    have hkK : k + 1 ≤ K := by omega
    have hfd : fderiv ℝ (almostAnalyticExtOrder (k + 2) f) z
        = fderiv ℝ (almostAnalyticExtOrder (k + 1) f) z
          + fderiv ℝ (extOrderTerm (k + 1) f) z := by
      rw [hfun]
      exact fderiv_add (by
        exact (hasFDerivAt_almostAnalyticExtOrder (k := k + 1)
          (hf.of_le (by exact_mod_cast hkK)) z).differentiableAt) (by
        exact (hasFDerivAt_extOrderTerm hf (by omega) z).differentiableAt)
    rw [hfd]
    have hsplit : I • (fderiv ℝ (almostAnalyticExtOrder (k + 1) f) z
          + fderiv ℝ (extOrderTerm (k + 1) f) z) 1
        - (fderiv ℝ (almostAnalyticExtOrder (k + 1) f) z
          + fderiv ℝ (extOrderTerm (k + 1) f) z) I
        = (I • fderiv ℝ (almostAnalyticExtOrder (k + 1) f) z 1
            - fderiv ℝ (almostAnalyticExtOrder (k + 1) f) z I)
          + (I • fderiv ℝ (extOrderTerm (k + 1) f) z 1
            - fderiv ℝ (extOrderTerm (k + 1) f) z I) := by
      simp only [ContinuousLinearMap.add_apply, smul_add]
      ring
    have ih' := ih hkK
    have hterm := dbar_extOrderTerm (f := f) (k := K) (j := k + 1) hf (by omega) z
    rw [show (k + 1) + 1 = k + 2 from by ring] at hterm
    rw [hsplit, ih', hterm]
    ring

/-- **The exact `∂̄` of the order-`k+1` extension.**  It is `I · (I y)^k / k! · f^{(k+1)}(x)`,
i.e. it vanishes to order `k` on the real axis. -/
theorem dbar_almostAnalyticExtOrder {f : ℝ → ℝ} (k : ℕ) {K : ℕ} (hf : ContDiff ℝ K f)
    (hK : k + 1 ≤ K) (z : ℂ) :
    I • fderiv ℝ (almostAnalyticExtOrder (k + 1) f) z 1
        - fderiv ℝ (almostAnalyticExtOrder (k + 1) f) z I =
      I * ((I * (z.im : ℂ)) ^ k / (k.factorial : ℂ)
        * ((iteratedDeriv (k + 1) f z.re : ℝ) : ℂ)) := by
  rw [dbar_almostAnalyticExtOrder_profile k hf hK z, extOrderDbarProfile_succ]

/-- **Norm bound on the `∂̄` of the order-`k+1` extension**: it is bounded by
`|Im z|^k / k! · M` whenever `‖f^{(k+1)}‖ ≤ M`. -/
theorem norm_dbar_almostAnalyticExtOrder_le {f : ℝ → ℝ} {k K : ℕ} (hf : ContDiff ℝ K f)
    (hK : k + 1 ≤ K) (z : ℂ) {M : ℝ} (hM : ∀ x, ‖iteratedDeriv (k + 1) f x‖ ≤ M) :
    ‖I • fderiv ℝ (almostAnalyticExtOrder (k + 1) f) z 1
        - fderiv ℝ (almostAnalyticExtOrder (k + 1) f) z I‖
      ≤ |z.im| ^ k / (k.factorial : ℝ) * M := by
  rw [dbar_almostAnalyticExtOrder k hf hK z]
  have hfac : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hb : |iteratedDeriv (k + 1) f z.re| ≤ M := by
    have := hM z.re
    rwa [Real.norm_eq_abs] at this
  have hnormfac : ‖((k.factorial : ℕ) : ℂ)‖ = (k.factorial : ℝ) := by
    rw [show ((k.factorial : ℕ) : ℂ) = ((k.factorial : ℝ) : ℂ) from by push_cast; ring]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hfac]
  calc ‖I * ((I * (z.im : ℂ)) ^ k / (k.factorial : ℂ)
        * ((iteratedDeriv (k + 1) f z.re : ℝ) : ℂ))‖
      = |z.im| ^ k / (k.factorial : ℝ) * |iteratedDeriv (k + 1) f z.re| := by
        simp only [norm_mul, Complex.norm_I, one_mul, norm_div, norm_pow, Complex.norm_real,
          Real.norm_eq_abs, hnormfac]
    _ ≤ |z.im| ^ k / (k.factorial : ℝ) * M := by
        gcongr


/-! ## The cut-off higher-order extension -/

/-- The cut-off order-`k` almost-analytic extension: the extension multiplied by the smooth bump
`yCut` in the imaginary direction.  It is smooth, compactly supported, agrees with `f` on the real
axis, and its `∂̄` vanishes to order `k-1` on a neighbourhood of the real axis. -/
def almostAnalyticExtOrderCut (k : ℕ) (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  almostAnalyticExtOrder k f z * (yCut z.im : ℂ)

/-- The cut-off order-`k` extension agrees with `f` on the real axis. -/
@[simp]
lemma almostAnalyticExtOrderCut_ofReal (k : ℕ) (hk : 1 ≤ k) (f : ℝ → ℝ) (x : ℝ) :
    almostAnalyticExtOrderCut k f (x : ℂ) = (f x : ℂ) := by
  rw [almostAnalyticExtOrderCut, almostAnalyticExtOrder_ofReal k hk, Complex.ofReal_im,
    yCut_one_of_mem (by norm_num : |(0 : ℝ)| ≤ 1)]
  simp

/-! ## The support of the cut-off extension -/

/-- The `j`-th iterated derivative is supported in the support of `f`. -/
lemma tsupport_iteratedDeriv_subset {f : ℝ → ℝ} (j : ℕ) :
    tsupport (iteratedDeriv j f) ⊆ tsupport f := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ]
    exact subset_trans tsupport_deriv_subset ih

/-- The support of the cut-off order-`k` extension is contained in the image of
`tsupport f × tsupport yCut`. -/
lemma support_almostAnalyticExtOrderCut_subset {f : ℝ → ℝ} {k : ℕ} :
    Function.support (almostAnalyticExtOrderCut k f) ⊆
      (fun p : ℝ × ℝ => ((p.1 : ℂ) + (p.2 : ℂ) * I)) '' (tsupport f ×ˢ tsupport yCut) := by
  intro z hz
  have hzre : z.re ∈ tsupport f := by
    by_contra h
    have hzero : almostAnalyticExtOrder k f z = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hd : iteratedDeriv j f z.re = 0 :=
        image_eq_zero_of_notMem_tsupport (f := iteratedDeriv j f)
          (fun hmem => h (tsupport_iteratedDeriv_subset j hmem))
      simp [extOrderTerm, hd]
    apply hz
    simp [almostAnalyticExtOrderCut, hzero]
  have hzim : z.im ∈ tsupport yCut := by
    by_contra h
    have h0 : yCut z.im = 0 := by
      by_contra h'
      exact h (subset_tsupport yCut h')
    apply hz
    simp [almostAnalyticExtOrderCut, h0]
  exact ⟨(z.re, z.im), ⟨hzre, hzim⟩, by simp⟩

/-- The cut-off order-`k` extension has compact support when `f` does. -/
lemma hasCompactSupport_almostAnalyticExtOrderCut {f : ℝ → ℝ} {k : ℕ}
    (hfc : HasCompactSupport f) : HasCompactSupport (almostAnalyticExtOrderCut k f) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (K := (fun p : ℝ × ℝ => ((p.1 : ℂ) + (p.2 : ℂ) * I)) '' (tsupport f ×ˢ tsupport yCut))
  · have h1 : IsCompact (tsupport yCut) := hasCompactSupport_yCut
    have h2 : IsCompact (tsupport f) := hfc
    exact (h2.prod h1).image (by fun_prop)
  · exact support_almostAnalyticExtOrderCut_subset

/-! ## The `∂̄` of the cut-off extension -/

/-- The `∂̄` of a product `F · (ρ ∘ Im)`: the weight is holomorphic, so the `∂̄` of `F` is
multiplied by `ρ`, and the derivative of `ρ` contributes a term supported away from the real
axis. -/
theorem dbar_mul_ofReal_comp_im {F : ℂ → ℂ} {ρ : ℝ → ℝ} {z : ℂ}
    (hF : DifferentiableAt ℝ F z) (hρ : Differentiable ℝ ρ) :
    I • fderiv ℝ (fun w => F w * (ρ w.im : ℂ)) z 1
        - fderiv ℝ (fun w => F w * (ρ w.im : ℂ)) z I =
      (ρ z.im : ℂ) * (I • fderiv ℝ F z 1 - fderiv ℝ F z I)
        - ((deriv ρ z.im : ℝ) : ℂ) * F z := by
  have hA : HasFDerivAt F (fderiv ℝ F z) z := hF.hasFDerivAt
  have hr : HasFDerivAt (fun w : ℂ => (ρ w.im : ℂ))
      (ContinuousLinearMap.smulRight Complex.imCLM ((deriv ρ z.im : ℝ) : ℂ)) z :=
    hasFDerivAt_ofReal_comp_im' (hρ.differentiableAt.hasDerivAt)
  have hG : HasFDerivAt (fun w => F w * (ρ w.im : ℂ))
      (F z • ContinuousLinearMap.smulRight Complex.imCLM ((deriv ρ z.im : ℝ) : ℂ)
        + ((ρ z.im : ℝ) : ℂ) • fderiv ℝ F z) z := by
    have h := hA.mul hr
    rw [hA.fderiv]
    exact h
  have key : I • fderiv ℝ (fun w => F w * (ρ w.im : ℂ)) z 1
        - fderiv ℝ (fun w => F w * (ρ w.im : ℂ)) z I
      = (ρ z.im : ℂ) * (I • (fderiv ℝ F z) 1 - (fderiv ℝ F z) I)
        - ((deriv ρ z.im : ℝ) : ℂ) * F z := by
    rw [hG.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, Complex.imCLM_apply]
    simp [Complex.one_im, Complex.I_im]
    ring
  exact key

/-- **The `∂̄` of the cut-off order-`k+1` extension.** -/
theorem dbar_almostAnalyticExtOrderCut {f : ℝ → ℝ} {k K : ℕ} (hf : ContDiff ℝ K f)
    (hK : k + 1 ≤ K) (z : ℂ) :
    I • fderiv ℝ (almostAnalyticExtOrderCut (k + 1) f) z 1
        - fderiv ℝ (almostAnalyticExtOrderCut (k + 1) f) z I =
      (yCut z.im : ℂ) * (I * ((I * (z.im : ℂ)) ^ k / (k.factorial : ℂ)
          * ((iteratedDeriv (k + 1) f z.re : ℝ) : ℂ)))
        - ((deriv yCut z.im : ℝ) : ℂ) * almostAnalyticExtOrder (k + 1) f z := by
  have hK' : k + 1 ≤ K := hK
  have hF : DifferentiableAt ℝ (almostAnalyticExtOrder (k + 1) f) z :=
    (hasFDerivAt_almostAnalyticExtOrder (k := k + 1) (hf.of_le (by exact_mod_cast hK')) z).differentiableAt
  have hρ : Differentiable ℝ yCut := (contDiff_yCut 1).differentiable (by norm_num)
  change I • fderiv ℝ (fun w : ℂ => almostAnalyticExtOrder (k + 1) f w * (yCut w.im : ℂ)) z 1
      - fderiv ℝ (fun w : ℂ => almostAnalyticExtOrder (k + 1) f w * (yCut w.im : ℂ)) z I = _
  rw [dbar_mul_ofReal_comp_im hF hρ, dbar_almostAnalyticExtOrder k hf hK z]

/-- On the strip `|Im z| < 1` the cut-off is locally `1`, so the `∂̄` of the cut-off order-`k+1`
extension is bounded by `|Im z|^k / k! · M`. -/
theorem norm_dbar_almostAnalyticExtOrderCut_le {f : ℝ → ℝ} {k K : ℕ} (hf : ContDiff ℝ K f)
    (hK : k + 1 ≤ K) {z : ℂ} (hz : |z.im| < 1) {M : ℝ}
    (hM : ∀ x, ‖iteratedDeriv (k + 1) f x‖ ≤ M) :
    ‖I • fderiv ℝ (almostAnalyticExtOrderCut (k + 1) f) z 1
        - fderiv ℝ (almostAnalyticExtOrderCut (k + 1) f) z I‖
      ≤ |z.im| ^ k / (k.factorial : ℝ) * M := by
  have hmem : z.im ∈ Metric.ball (0 : ℝ) yBump.rIn := by
    have h1 : yBump.rIn = 1 := rfl
    rw [h1, Real.ball_zero_eq_Ioo]
    exact abs_lt.mp hz
  have hρ1 : yCut =ᶠ[𝓝 z.im] 1 := by
    simpa [yCut] using ContDiffBump.eventuallyEq_one_of_mem_ball (f := yBump) hmem
  have hderiv : deriv yCut z.im = 0 := by
    rw [Filter.EventuallyEq.deriv_eq hρ1]
    simp
  rw [dbar_almostAnalyticExtOrderCut hf hK z, hderiv]
  simp only [Complex.ofReal_zero, zero_mul, sub_zero]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hρle : |yCut z.im| ≤ 1 := by
    rw [abs_of_nonneg (yCut_nonneg z.im)]
    simpa [yCut] using ContDiffBump.le_one (f := yBump) (x := z.im)
  have hinner : ‖I * ((I * (z.im : ℂ)) ^ k / (k.factorial : ℂ)
      * ((iteratedDeriv (k + 1) f z.re : ℝ) : ℂ))‖
      = |z.im| ^ k / (k.factorial : ℝ) * |iteratedDeriv (k + 1) f z.re| := by
    have hfac : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
    have hnormfac : ‖((k.factorial : ℕ) : ℂ)‖ = (k.factorial : ℝ) := by
      rw [show ((k.factorial : ℕ) : ℂ) = ((k.factorial : ℝ) : ℂ) from by push_cast; ring]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hfac]
    simp only [norm_mul, Complex.norm_I, one_mul, norm_div, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, hnormfac]
  rw [hinner]
  have hb : |iteratedDeriv (k + 1) f z.re| ≤ M := by
    have := hM z.re
    rwa [Real.norm_eq_abs] at this
  calc |yCut z.im| * (|z.im| ^ k / (k.factorial : ℝ) * |iteratedDeriv (k + 1) f z.re|)
      ≤ 1 * (|z.im| ^ k / (k.factorial : ℝ) * M) := by gcongr
    _ = |z.im| ^ k / (k.factorial : ℝ) * M := one_mul _

/-! ## Regularity of the cut-off extension -/

/-- The `j`-th iterated derivative of a `C^{1+j}` function is `C¹`. -/
lemma contDiff_iteratedDeriv_one {f : ℝ → ℝ} {j K : ℕ} (hf : ContDiff ℝ K f) (hK : 1 + j ≤ K) :
    ContDiff ℝ 1 (iteratedDeriv j f) := by
  have h := ContDiff.iterate_deriv' (𝕜 := ℝ) 1 j
    (by simpa using (hf.of_le (by exact_mod_cast hK)))
  simpa [iteratedDeriv_eq_iterate] using h

/-- The order-`k+1` extension is `C¹` when `f` is `C^{k+1}`. -/
lemma contDiff_almostAnalyticExtOrder_one {f : ℝ → ℝ} {k K : ℕ} (hf : ContDiff ℝ K f)
    (hK : k + 1 ≤ K) : ContDiff ℝ 1 (almostAnalyticExtOrder (k + 1) f) := by
  change ContDiff ℝ 1 (fun z : ℂ => ∑ j ∈ Finset.range (k + 1), extOrderTerm j f z)
  refine ContDiff.sum (fun j hj => ?_)
  have hj' : j ≤ k := by
    have := Finset.mem_range.mp hj
    omega
  have hpoly : ContDiff ℝ 1 (fun z : ℂ => (I * (z.im : ℂ)) ^ j / (j.factorial : ℂ)) := by
    have him : ContDiff ℝ 1 (fun z : ℂ => ((z.im : ℝ) : ℂ)) := by
      have h := (Complex.ofRealCLM.contDiff (n := (1 : ℕ∞))).comp Complex.imCLM.contDiff
      simpa [Function.comp_def] using h
    have hconst : ContDiff ℝ 1 (fun z : ℂ => I * ((z.im : ℝ) : ℂ)) := contDiff_const.mul him
    exact (hconst.pow j).div_const ((j.factorial : ℂ))
  have hgd : ContDiff ℝ 1 (iteratedDeriv j f) :=
    contDiff_iteratedDeriv_one hf (by omega)
  have hcomp : ContDiff ℝ 1 (fun z : ℂ => ((iteratedDeriv j f z.re : ℝ) : ℂ)) := by
    have h := (Complex.ofRealCLM.contDiff (n := (1 : ℕ∞))).comp
      (hgd.comp Complex.reCLM.contDiff)
    simpa [Function.comp_def] using h
  exact hpoly.mul hcomp

/-- The cut-off order-`k+1` extension is `C¹` when `f` is `C^{k+1}`. -/
lemma contDiff_almostAnalyticExtOrderCut_one {f : ℝ → ℝ} {k K : ℕ} (hf : ContDiff ℝ K f)
    (hK : k + 1 ≤ K) : ContDiff ℝ 1 (almostAnalyticExtOrderCut (k + 1) f) := by
  have hext := contDiff_almostAnalyticExtOrder_one hf hK
  have hy : ContDiff ℝ 1 (fun z : ℂ => (yCut z.im : ℂ)) := by
    have h := (Complex.ofRealCLM.contDiff (n := (1 : ℕ∞))).comp
      ((contDiff_yCut 1).comp Complex.imCLM.contDiff)
    simpa [Function.comp_def] using h
  have h : ContDiff ℝ 1 (fun z : ℂ => almostAnalyticExtOrder (k + 1) f z * (yCut z.im : ℂ)) :=
    hext.mul hy
  change ContDiff ℝ 1 (fun z : ℂ => almostAnalyticExtOrder (k + 1) f z * (yCut z.im : ℂ))
  exact h


/-! ## The weighted strip estimate -/

/-- The `∂̄` numerator of the cut-off order-`k` extension. -/
def dbarNumOrder (k : ℕ) (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  I • fderiv ℝ (almostAnalyticExtOrderCut k f) z 1
    - fderiv ℝ (almostAnalyticExtOrderCut k f) z I

/-- **Weighted strip estimate for the order-`k+1` extension.**

For the cut-off order-`k+1` extension with `‖f^{(k+1)}‖ ≤ M`, every `0 ≤ β < k` and every
`0 ≤ η < 1`,

`‖∫_{-η}^{η} ∫_{-X}^{X} ∂̄F(x+iy) · |y|^{-β}‖ ≤ (M/k!) · (2X) · η^{k-β} · 2η`.

The weight `|y|^{-β}` is where the resolvent comparison enters: if
`‖g_N(z) − g(z)‖ ≤ C · |y|^{-β}` on the strip with `β < k`, the strip contribution is
`C · (M/k!) · (2X) · 2η^{k+1-β}` — `C` times a constant of the test function alone.  With the
trivial resolvent bound (`β = 1`) and `k ≥ 2` this is `O(η^k)`; with a bound `C = C₀/N²` it is
`O(N⁻²)`. -/
theorem norm_strip_integral_dbar_order_le {f : ℝ → ℝ} {k K : ℕ} (hf : ContDiff ℝ K f)
    (hK : k + 1 ≤ K) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x, ‖iteratedDeriv (k + 1) f x‖ ≤ M)
    {X η β : ℝ} (hX : 0 ≤ X) (hη : 0 ≤ η) (hη1 : η < 1)
    (hβ0 : 0 ≤ β) (hβ : β < k) :
    ‖∫ y in (-η)..η, ∫ x in (-X)..X,
        dbarNumOrder (k + 1) f ((x : ℂ) + (y : ℂ) * I) * ((|y| ^ (-β) : ℝ) : ℂ)‖
      ≤ (M / (k.factorial : ℝ)) * (2 * X) * η ^ ((k : ℝ) - β) * (2 * η) := by
  have hfac : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  -- pointwise bound on the weighted `∂̄` when `|y| ≤ η`
  have hpt : ∀ (x y : ℝ), |y| ≤ η →
      ‖dbarNumOrder (k + 1) f ((x : ℂ) + (y : ℂ) * I) * ((|y| ^ (-β) : ℝ) : ℂ)‖
        ≤ (M / (k.factorial : ℝ)) * η ^ ((k : ℝ) - β) := by
    intro x y hy
    have hnormC : ‖dbarNumOrder (k + 1) f ((x : ℂ) + (y : ℂ) * I)‖
        ≤ |y| ^ k / (k.factorial : ℝ) * M := by
      have h := norm_dbar_almostAnalyticExtOrderCut_le (f := f) (k := k) (K := K) hf hK
        (z := ((x : ℂ) + (y : ℂ) * I)) (by simpa using lt_of_le_of_lt hy hη1) hM
      simpa [dbarNumOrder] using h
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg y) _)]
    rcases eq_or_ne y 0 with rfl | hyne
    · have hk0 : k ≠ 0 := by
        intro hk
        rw [hk] at hβ
        push_cast at hβ
        linarith
      have hz : ‖dbarNumOrder (k + 1) f ((x : ℂ) + ((0 : ℝ) : ℂ) * I)‖ = 0 := by
        have h := hnormC
        rw [abs_zero, zero_pow hk0, zero_div, zero_mul] at h
        exact le_antisymm h (norm_nonneg _)
      rw [hz, zero_mul]
      exact mul_nonneg (div_nonneg hM0 hfac.le) (Real.rpow_nonneg hη _)
    · have hypos : 0 < |y| := abs_pos.mpr hyne
      have hcomb : |y| ^ k / (k.factorial : ℝ) * M * |y| ^ (-β)
          = (M / (k.factorial : ℝ)) * |y| ^ ((k : ℝ) - β) := by
        rw [show (k : ℝ) - β = k + (-β) by ring, Real.rpow_add hypos, Real.rpow_natCast]
        field_simp
      have hmono : (M / (k.factorial : ℝ)) * |y| ^ ((k : ℝ) - β)
          ≤ (M / (k.factorial : ℝ)) * η ^ ((k : ℝ) - β) := by
        refine mul_le_mul_of_nonneg_left ?_ (div_nonneg hM0 hfac.le)
        exact Real.rpow_le_rpow (abs_nonneg y) hy (by linarith)
      calc ‖dbarNumOrder (k + 1) f ((x : ℂ) + (y : ℂ) * I)‖ * |y| ^ (-β)
          ≤ (|y| ^ k / (k.factorial : ℝ) * M) * |y| ^ (-β) := by
            exact mul_le_mul_of_nonneg_right hnormC (Real.rpow_nonneg (abs_nonneg y) _)
        _ = (M / (k.factorial : ℝ)) * |y| ^ ((k : ℝ) - β) := hcomb
        _ ≤ (M / (k.factorial : ℝ)) * η ^ ((k : ℝ) - β) := hmono
  -- inner integral, for `y` in the strip
  have hinner : ∀ y ∈ Set.uIoc (-η) η,
      ‖∫ x in (-X)..X,
        dbarNumOrder (k + 1) f ((x : ℂ) + (y : ℂ) * I) * ((|y| ^ (-β) : ℝ) : ℂ)‖
      ≤ ((M / (k.factorial : ℝ)) * η ^ ((k : ℝ) - β)) * (2 * X) := by
    intro y hy
    have hyI : y ∈ Set.Ioc (-η) η := by
      simpa [Set.uIoc_of_le (by linarith : -η ≤ η)] using hy
    have hyabs : |y| ≤ η := abs_le.mpr ⟨by linarith [hyI.1], hyI.2⟩
    have hC := norm_integral_le_of_norm_le_const (a := -X) (b := X)
      (C := (M / (k.factorial : ℝ)) * η ^ ((k : ℝ) - β))
      (f := fun x : ℝ => dbarNumOrder (k + 1) f ((x : ℂ) + (y : ℂ) * I)
        * ((|y| ^ (-β) : ℝ) : ℂ)) (fun x _ => hpt x y hyabs)
    have h2X : |X - (-X)| = 2 * X := by
      rw [show X - (-X) = 2 * X by ring, abs_of_nonneg (by linarith)]
    rwa [h2X] at hC
  -- outer integral
  refine le_trans (norm_integral_le_of_norm_le_const
    (C := ((M / (k.factorial : ℝ)) * η ^ ((k : ℝ) - β)) * (2 * X))
    (fun y hy => hinner y hy)) ?_
  rw [show η - (-η) = 2 * η by ring, abs_of_nonneg (by linarith)]
  have hEq : ((M / (k.factorial : ℝ)) * η ^ ((k : ℝ) - β)) * (2 * X) * (2 * η)
      = (M / (k.factorial : ℝ)) * (2 * X) * η ^ ((k : ℝ) - β) * (2 * η) := by ring
  rw [hEq]


/-! ## Global bound and the far-region estimate -/

/-- Continuity of the `∂̄` numerator of the cut-off order-`k` extension. -/
lemma continuous_dbarNumOrder {f : ℝ → ℝ} {k K : ℕ} (hf : ContDiff ℝ K f) (hK : k + 1 ≤ K) :
    Continuous (dbarNumOrder (k + 1) f) := by
  have hF : ContDiff ℝ 1 (almostAnalyticExtOrderCut (k + 1) f) :=
    contDiff_almostAnalyticExtOrderCut_one hf hK
  have hfd : Continuous (fderiv ℝ (almostAnalyticExtOrderCut (k + 1) f)) :=
    hF.continuous_fderiv (by norm_num)
  have h1 : Continuous (fun z : ℂ =>
      fderiv ℝ (almostAnalyticExtOrderCut (k + 1) f) z 1) :=
    hfd.clm_apply continuous_const
  have h2 : Continuous (fun z : ℂ =>
      fderiv ℝ (almostAnalyticExtOrderCut (k + 1) f) z I) :=
    hfd.clm_apply continuous_const
  exact (continuous_const.mul h1).sub h2

/-- The `∂̄` numerator of the cut-off extension is compactly supported. -/
lemma hasCompactSupport_dbarNumOrder {f : ℝ → ℝ} {k : ℕ} (hfc : HasCompactSupport f) :
    HasCompactSupport (dbarNumOrder k f) := by
  refine (hasCompactSupport_almostAnalyticExtOrderCut (k := k) hfc).mono' ?_
  intro z hz
  by_contra hzt
  rw [notMem_tsupport_iff_eventuallyEq] at hzt
  apply hz
  simp only [dbarNumOrder]
  rw [hzt.fderiv_eq]
  simp

/-- A global bound on the `∂̄` numerator of the cut-off order-`k+1` extension. -/
lemma exists_norm_dbarNumOrder_le {f : ℝ → ℝ} {k K : ℕ} (hf : ContDiff ℝ K f) (hK : k + 1 ≤ K)
    (hfc : HasCompactSupport f) :
    ∃ B, 0 ≤ B ∧ ∀ z : ℂ, ‖dbarNumOrder (k + 1) f z‖ ≤ B := by
  have hcont := continuous_dbarNumOrder hf hK
  have hKc : IsCompact (tsupport (dbarNumOrder (k + 1) f)) :=
    hasCompactSupport_dbarNumOrder (k := k + 1) hfc
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max B 0, le_max_right B 0, fun z => ?_⟩
  by_cases hz : z ∈ tsupport (dbarNumOrder (k + 1) f)
  · exact le_trans (hB z hz) (le_max_left B 0)
  · rw [image_eq_zero_of_notMem_tsupport (f := dbarNumOrder (k + 1) f) hz]
    simpa using le_max_right B 0

/-- **Far-region estimate for the order-`k+1` extension.**

Off the strip `|Im z| ≥ η₀ > 0` the `∂̄` of the cut-off extension is globally bounded by `B`,
so the weighted integral over any vertical range `[c, d]` with `η₀ ≤ c` is bounded by
`B · (2X) · η₀⁻⁵ · (d - c)`.  (The cut-off extension is supported in `|Im z| ≤ 2`, so the
whole far region is covered by `[η₀, 2]` and `[-2, -η₀]`.) -/
theorem norm_far_integral_dbar_order_le {f : ℝ → ℝ} {k K : ℕ} (hf : ContDiff ℝ K f)
    (hK : k + 1 ≤ K) {B : ℝ} (hB : ∀ z : ℂ, ‖dbarNumOrder (k + 1) f z‖ ≤ B)
    {X η₀ c d : ℝ} (hX : 0 ≤ X) (hη₀ : 0 < η₀) (hc : η₀ ≤ c) (hcd : c ≤ d) :
    ‖∫ y in c..d, ∫ x in (-X)..X,
        dbarNumOrder (k + 1) f ((x : ℂ) + (y : ℂ) * I) * ((|y| ^ (-5 : ℝ) : ℝ) : ℂ)‖
      ≤ B * (2 * X) * η₀ ^ (-5 : ℝ) * (d - c) := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg (dbarNumOrder (k + 1) f 0)) (hB 0)
  have hη₀5 : 0 ≤ η₀ ^ (-5 : ℝ) := Real.rpow_nonneg hη₀.le _
  have hpt : ∀ (x y : ℝ), y ∈ Set.uIoc c d →
      ‖dbarNumOrder (k + 1) f ((x : ℂ) + (y : ℂ) * I) * ((|y| ^ (-5 : ℝ) : ℝ) : ℂ)‖
        ≤ B * η₀ ^ (-5 : ℝ) := by
    intro x y hy
    have hyI : y ∈ Set.Ioc c d := by
      simpa [Set.uIoc_of_le hcd] using hy
    have hyc : c ≤ y := le_of_lt hyI.1
    have hypos : 0 < |y| := abs_pos.mpr (by linarith)
    have hy_ge : η₀ ≤ |y| := by
      rw [abs_of_pos (by linarith : (0:ℝ) < y)]; exact le_trans hc hyc
    have hle : |y| ^ (-5 : ℝ) ≤ η₀ ^ (-5 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hη₀ hy_ge (by norm_num)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg y) (-5 : ℝ))]
    exact mul_le_mul (hB _) hle (Real.rpow_nonneg (abs_nonneg y) (-5 : ℝ)) hB0
  have hinner : ∀ y ∈ Set.uIoc c d,
      ‖∫ x in (-X)..X,
        dbarNumOrder (k + 1) f ((x : ℂ) + (y : ℂ) * I) * ((|y| ^ (-5 : ℝ) : ℝ) : ℂ)‖
      ≤ (B * η₀ ^ (-5 : ℝ)) * (2 * X) := by
    intro y hy
    have hC := norm_integral_le_of_norm_le_const (a := -X) (b := X)
      (C := B * η₀ ^ (-5 : ℝ))
      (f := fun x : ℝ => dbarNumOrder (k + 1) f ((x : ℂ) + (y : ℂ) * I)
        * ((|y| ^ (-5 : ℝ) : ℝ) : ℂ)) (fun x _ => hpt x y hy)
    have h2X : |X - (-X)| = 2 * X := by
      rw [show X - (-X) = 2 * X by ring, abs_of_nonneg (by linarith)]
    rwa [h2X] at hC
  refine le_trans (norm_integral_le_of_norm_le_const (C := (B * η₀ ^ (-5 : ℝ)) * (2 * X))
    (fun y hy => hinner y hy)) ?_
  rw [show d - c = d - c from rfl, abs_of_nonneg (by linarith)]
  have hEq : (B * η₀ ^ (-5 : ℝ)) * (2 * X) * (d - c)
      = B * (2 * X) * η₀ ^ (-5 : ℝ) * (d - c) := by ring
  rw [hEq]

end

end GUEStrongConvergence
