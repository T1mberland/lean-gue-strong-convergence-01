/-
# The cfc trace derivative for the affine GUE pencil

This module proves the single analytic input left open in
`Probability/LemmaVSmooth.lean`: the **cfc trace derivative**

`d/dt tau_N(f(H_N(x with coordinate p := t)))|_{t = t₀}
  = tau_N(f'(H_N(x with coordinate p := t₀)) · D_p)`.

The proof follows the classical route: on the compact interval `I_x` containing the spectra of
the whole affine family `H + s • D` (`|s| ≤ |t₀ - x_p| + 1`), approximate `f` simultaneously in
`C⁰` and `C¹` by polynomials (`exists_polynomial_c1_approx`), use the exact polynomial trace
derivative (`hasDerivAt_trace_polyMatrix` / `hasDerivAt_gueStatisticNorm_update`) and pass to
the limit by uniform convergence (`hasDerivAt_of_tendstoUniformlyOn`).  The spectral bound is
obtained from the Hilbert–Schmidt norm (`eigenvalues_abs_le_sqrt_hsNorm`) and the elementary
estimate `hsNorm (H + s • D) ≤ 2 hsNorm H + 2 s² hsNorm D`, which avoids any operator-norm
comparison.

## Main results

* `hasDerivAt_gueStatisticCfc_update` — the cfc trace derivative at an arbitrary point, for
  `f : ℝ → ℝ` of class `C¹`;
* `ae_hasDerivAt_gueStatisticCfc_update` — the same, in the `∀ᵐ x, ∀ t` form required by the
  Gaussian Poincaré inequality (in fact it holds for **every** `x`);
* `lemmaV_sharp_smooth` — the smooth Lemma V with the trace-derivative hypothesis discharged;
* `lemmaS_V_input_unconditional` — the unconditional `(V)` input of the spectral-exclusion
  argument.

## Note on the hypothesis on `f`

The trace derivative genuinely requires `f` to be differentiable, not merely to have a
continuous `deriv` in the sense of the total function `deriv f` (which is `0` at the points
where `f` is not differentiable).  The correct hypothesis is `ContDiff ℝ 1 f`, which is what
the smooth Lemma V of the paper assumes.  We also provide the form with explicit hypotheses
`Differentiable ℝ f` and `Continuous (deriv f)`.
-/
import GUEStrongConvergence.Probability.LemmaVSmooth
import GUEStrongConvergence.Probability.SmoothSpectralVariance
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped RealInnerProductSpace ENNReal NNReal Topology Polynomial BigOperators

namespace GUEStrongConvergence

noncomputable section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] {N : ℕ}

/-! ### Generic bounds for the continuous functional calculus -/

section Generic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The continuous functional calculus of a polynomial is the polynomial functional calculus. -/
lemma cfc_polyMatrix_eq (q : ℝ[X]) (M : Matrix n n ℂ) (hM : M.IsHermitian) :
    cfc (fun y : ℝ => q.eval y) M = polyMatrix q M := by
  rw [cfc_polynomial q M (isHermitian_iff_isSelfAdjoint.mp hM)]
  rfl

/-- Subtraction rule for the cfc of a Hermitian matrix, with explicit continuity. -/
lemma cfc_sub_of_hermitian (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (M : Matrix n n ℂ) (hM : M.IsHermitian) :
    cfc (fun y : ℝ => f y - g y) M = cfc f M - cfc g M :=
  cfc_sub (f := f) (g := g) (a := M) (hf := hf.continuousOn) (hg := hg.continuousOn)

/-- **Trace formula** for the cfc with the generic `cfc`. -/
lemma trace_cfc_eq_sum_eigenvalues_matrix (M : Matrix n n ℂ) (hM : M.IsHermitian) (g : ℝ → ℝ) :
    (cfc g M).trace = ∑ i, ((g (hM.eigenvalues i) : ℝ) : ℂ) := by
  rw [Matrix.IsHermitian.cfc_eq hM g]
  exact trace_cfc_eq_sum_eigenvalues_general M hM g

/-- **Hilbert–Schmidt norm of a cfc** as the sum of squares over the eigenvalues. -/
lemma hsNorm_cfc_eq_sum_eigenvalues (M : Matrix n n ℂ) (hM : M.IsHermitian) (g : ℝ → ℝ)
    (hg : Continuous g) :
    hsNorm (cfc g M) = ∑ i, (g (hM.eigenvalues i)) ^ 2 := by
  rw [Matrix.IsHermitian.cfc_eq hM g, hsNorm_cfc_eq M hM g hg,
    trace_cfc_eq_sum_eigenvalues_general M hM (fun y => (g y) ^ 2)]
  rw [Complex.re_sum]
  exact Finset.sum_congr rfl fun i _ => Complex.ofReal_re _

/-- **Trace bound for a cfc.**  If the spectrum of `M` lies in `[-R, R]` and `|g| ≤ C` there,
then `|Tr(g(M))| ≤ card · C`. -/
lemma abs_trace_cfc_le (M : Matrix n n ℂ) (hM : M.IsHermitian) (g : ℝ → ℝ)
    {R C : ℝ} (hlam : ∀ i, |hM.eigenvalues i| ≤ R)
    (hC : ∀ y : ℝ, |y| ≤ R → |g y| ≤ C) :
    ‖(cfc g M).trace‖ ≤ (Fintype.card n : ℝ) * C := by
  rw [trace_cfc_eq_sum_eigenvalues_matrix M hM g]
  calc ‖∑ i, ((g (hM.eigenvalues i) : ℝ) : ℂ)‖
      ≤ ∑ i, ‖((g (hM.eigenvalues i) : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ = ∑ i, |g (hM.eigenvalues i)| := by simp
    _ ≤ ∑ i, C := Finset.sum_le_sum fun i _ => hC _ (hlam i)
    _ = (Fintype.card n : ℝ) * C := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Hilbert–Schmidt bound for a cfc.**  Under the same spectral hypotheses,
`‖g(M)‖_F² ≤ card · C²`. -/
lemma hsNorm_cfc_le (M : Matrix n n ℂ) (hM : M.IsHermitian) (g : ℝ → ℝ)
    (hg : Continuous g) {R C : ℝ} (hlam : ∀ i, |hM.eigenvalues i| ≤ R)
    (hC : ∀ y : ℝ, |y| ≤ R → |g y| ≤ C) (hC0 : 0 ≤ C) :
    hsNorm (cfc g M) ≤ (Fintype.card n : ℝ) * C ^ 2 := by
  rw [hsNorm_cfc_eq_sum_eigenvalues M hM g hg]
  calc ∑ i, (g (hM.eigenvalues i)) ^ 2
      ≤ ∑ i, C ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hC _ (hlam i)) 2
    _ = (Fintype.card n : ℝ) * C ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Hilbert–Schmidt Cauchy–Schwarz for the trace pairing**:
`|Tr(A B)| ≤ ‖A‖_F ‖B‖_F`. -/
lemma norm_trace_mul_le_sqrt_hsNorm (A B : Matrix n n ℂ) :
    ‖(A * B).trace‖ ≤ Real.sqrt (hsNorm A) * Real.sqrt (hsNorm B) := by
  have htr : (A * B).trace = ∑ i, ∑ j, A i j * B j i := by
    simp [Matrix.trace, Matrix.mul_apply]
  have h1 : ‖∑ i, ∑ j, A i j * B j i‖ ≤ ∑ i, ∑ j, ‖A i j‖ * ‖B j i‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    exact (norm_sum_le _ _).trans (le_of_eq (by simp only [norm_mul]))
  have h2 : (∑ i, ∑ j, ‖A i j‖ * ‖B j i‖) ≤ Real.sqrt (hsNorm A) * Real.sqrt (hsNorm B) := by
    have hsum : (∑ i, ∑ j, ‖A i j‖ * ‖B j i‖)
        = ∑ x : n × n, ‖A x.1 x.2‖ * ‖B x.2 x.1‖ := by
      rw [Fintype.sum_prod_type]
    have hA : (∑ x : n × n, ‖A x.1 x.2‖ ^ 2) = hsNorm A := by
      rw [Fintype.sum_prod_type]; rfl
    have hB : (∑ x : n × n, ‖B x.2 x.1‖ ^ 2) = hsNorm B := by
      rw [Fintype.sum_prod_type, hsNorm, Finset.sum_comm]
    rw [hsum, ← hA, ← hB]
    simpa using Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (n × n))
      (fun x => ‖A x.1 x.2‖) (fun x => ‖B x.2 x.1‖)
  rw [htr]
  exact h1.trans h2

/-- The Hilbert–Schmidt norm of a sum is controlled by twice the sum of the pieces. -/
lemma hsNorm_add_le (A B : Matrix n n ℂ) :
    hsNorm (A + B) ≤ 2 * hsNorm A + 2 * hsNorm B := by
  have hentry : ∀ a b : n, ‖(A + B) a b‖ ^ 2 ≤ 2 * ‖A a b‖ ^ 2 + 2 * ‖B a b‖ ^ 2 := by
    intro a b
    have hsum : ‖(A + B) a b‖ ≤ ‖A a b‖ + ‖B a b‖ := by
      simpa [Matrix.add_apply] using norm_add_le (A a b) (B a b)
    have h2 := pow_le_pow_left₀ (norm_nonneg _) hsum 2
    have h3 : (‖A a b‖ + ‖B a b‖) ^ 2 ≤ 2 * ‖A a b‖ ^ 2 + 2 * ‖B a b‖ ^ 2 := by
      nlinarith [sq_nonneg (‖A a b‖ - ‖B a b‖)]
    exact h2.trans h3
  calc hsNorm (A + B) = ∑ a, ∑ b, ‖(A + B) a b‖ ^ 2 := rfl
    _ ≤ ∑ a, ∑ b, (2 * ‖A a b‖ ^ 2 + 2 * ‖B a b‖ ^ 2) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hentry a b
    _ = 2 * hsNorm A + 2 * hsNorm B := by
        simp only [hsNorm, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- The Hilbert–Schmidt norm of a real multiple. -/
lemma hsNorm_smul (s : ℝ) (D : Matrix n n ℂ) :
    hsNorm (s • D) = s ^ 2 * hsNorm D := by
  have hentry : ∀ a b : n, ‖(s • D) a b‖ ^ 2 = s ^ 2 * ‖D a b‖ ^ 2 := by
    intro a b
    have h : ‖(s • D) a b‖ = |s| * ‖D a b‖ := by
      rw [Matrix.smul_apply, Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [h, mul_pow, sq_abs]
  calc hsNorm (s • D) = ∑ a, ∑ b, ‖(s • D) a b‖ ^ 2 := rfl
    _ = ∑ a, ∑ b, s ^ 2 * ‖D a b‖ ^ 2 := by
        simp only [hentry]
    _ = s ^ 2 * hsNorm D := by
        rw [hsNorm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]

/-- **Affine Hilbert–Schmidt bound**: `‖H + s • D‖_F² ≤ 2‖H‖_F² + 2 s² ‖D‖_F²`. -/
lemma hsNorm_add_smul_le (H D : Matrix n n ℂ) (s : ℝ) :
    hsNorm (H + s • D) ≤ 2 * hsNorm H + 2 * s ^ 2 * hsNorm D := by
  calc hsNorm (H + s • D) ≤ 2 * hsNorm H + 2 * hsNorm (s • D) := hsNorm_add_le H (s • D)
    _ = 2 * hsNorm H + 2 * s ^ 2 * hsNorm D := by rw [hsNorm_smul]; ring

end Generic

/-! ### The coordinate direction is Hermitian -/

/-- The coefficient matrix of a coordinate direction is conjugate-symmetric. -/
lemma star_gueMatrixCoeff (p : GUECoord ι N) (i : ι) (a b : Fin N) :
    star (gueMatrixCoeff p i b a) = gueMatrixCoeff p i a b := by
  unfold gueMatrixCoeff
  by_cases h₁ : (i, (a, b)) = p <;> by_cases h₂ : (i, (b, a)) = p
  all_goals
    simp only [h₁, h₂, ite_true, ite_false, star_mul, star_add, star_gueAlpha, star_gueBeta,
      star_zero, Complex.star_def, Complex.conj_ofReal, mul_one, mul_zero,
      add_zero, add_comm, mul_comm]

/-- **The GUE coordinate direction is Hermitian** when the coefficients are. -/
lemma gueDirMatrix_isHermitian (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (p : GUECoord ι N) : (gueDirMatrix A p).IsHermitian := by
  ext a b
  simp only [Matrix.conjTranspose_apply, gueDirMatrix, star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hA' : star (A i b.1 a.1) = A i a.1 b.1 := by
    have h := congrFun (congrFun (hA i) a.1) b.1
    simpa only [Matrix.conjTranspose_apply] using h
  rw [star_mul, hA', star_gueMatrixCoeff, mul_comm]

/-! ### Numerical bounds on the normalization constant -/

lemma gueNormConst_nonneg : 0 ≤ gueNormConst d N := by
  rw [gueNormConst]; positivity

lemma card_prod_fin_eq : Fintype.card (d × Fin N) = Fintype.card d * N := by
  rw [Fintype.card_prod, Fintype.card_fin]

lemma gueNormConst_mul_card_le_one :
    gueNormConst d N * (Fintype.card (d × Fin N) : ℝ) ≤ 1 := by
  rw [gueNormConst, card_prod_fin_eq]
  by_cases h : Fintype.card d * N = 0
  · simp [h]
  · have hpos : (0 : ℝ) < ((Fintype.card d * N : ℕ) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero h
    rw [inv_mul_cancel₀ hpos.ne']

lemma gueNormConst_mul_sqrt_card_le_one :
    gueNormConst d N * Real.sqrt (Fintype.card (d × Fin N) : ℝ) ≤ 1 := by
  rw [gueNormConst, card_prod_fin_eq]
  set m : ℕ := Fintype.card d * N with hm
  by_cases h : m = 0
  · rw [h]; simp
  · have hpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
    have hsqrt : Real.sqrt (m : ℝ) ≤ (m : ℝ) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by linarith, ?_⟩
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ (m : ℝ) by linarith)
        (show (0 : ℝ) ≤ (m : ℝ) - 1 by linarith)]
    calc (m : ℝ)⁻¹ * Real.sqrt (m : ℝ) ≤ (m : ℝ)⁻¹ * (m : ℝ) :=
          mul_le_mul_of_nonneg_left hsqrt (by positivity)
      _ = 1 := inv_mul_cancel₀ hpos.ne'


/-! ### Uniform convergence transfer -/

/-- If the approximants are pointwise within `e n` of the limit on `s` and `e n → 0`, then the
convergence is uniform on `s`. -/
lemma tendstoUniformlyOn_of_abs_sub_le {F : ℕ → ℝ → ℝ} {G : ℝ → ℝ} {s : Set ℝ}
    {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0))
    (h : ∀ (n : ℕ) (u : ℝ), u ∈ s → |F n u - G u| ≤ e n) :
    TendstoUniformlyOn F G atTop s := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hev : ∀ᶠ n : ℕ in atTop, e n < ε := he.eventually (eventually_lt_nhds hε)
  filter_upwards [hev] with n hn u hu
  rw [Real.dist_eq, abs_sub_comm]
  exact lt_of_le_of_lt (h n u hu) hn

/-- **The cfc trace derivative of the affine GUE pencil.**  For `f : ℝ → ℝ` of class `C¹`, the
coordinate statistic `t ↦ tau_N(f(H_N(x` with coordinate `p` set to `t)))` is differentiable at
every `t₀`, with derivative `tau_N(f'(H_N(x` with coordinate `p` set to `t₀)) · D_p)`. -/
theorem hasDerivAt_gueStatisticCfc_update (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian)
    (x : EuclideanSpace ℝ (GUECoord ι N)) (p : GUECoord ι N) (t₀ : ℝ) :
    HasDerivAt (fun u : ℝ => gueStatisticCfc f A₀ A hA₀ hA (euclidUpdate x p u))
      (gueStatisticCfcDir f A₀ A hA₀ hA p (euclidUpdate x p t₀)) t₀ := by
  classical
  set H : Matrix (d × Fin N) (d × Fin N) ℂ := guePencilMatrix A₀ A (WithLp.ofLp x) with hHdef
  set D : Matrix (d × Fin N) (d × Fin N) ℂ := gueDirMatrix A p with hDdef
  set xp : ℝ := (WithLp.ofLp x) p with hxpdef
  have hH : H.IsHermitian := guePencilMatrix_isHermitian A₀ A hA₀ hA (WithLp.ofLp x)
  have hD : D.IsHermitian := gueDirMatrix_isHermitian A hA p
  have hmat : ∀ u : ℝ,
      guePencilMatrix A₀ A (WithLp.ofLp (euclidUpdate x p u)) = H + (u - xp) • D := by
    intro u
    rw [ofLp_euclidUpdate, guePencilMatrix_update_eq]
  have hFfun : (fun u : ℝ => gueStatisticCfc f A₀ A hA₀ hA (euclidUpdate x p u))
      = fun u : ℝ => guePencilNormTrace (cfc f (H + (u - xp) • D)) := by
    funext u
    simp only [gueStatisticCfc, guePencilCfc_eq_cfc, hmat u]
  have hGval : gueStatisticCfcDir f A₀ A hA₀ hA p (euclidUpdate x p t₀)
      = guePencilNormTrace (cfc (deriv f) (H + (t₀ - xp) • D) * D) := by
    simp only [gueStatisticCfcDir, guePencilCfc_eq_cfc, hmat t₀, ← hDdef]
  -- the Hermitian affine family
  have hHu : ∀ u : ℝ, (H + (u - xp) • D).IsHermitian := by
    intro u
    exact hH.add (hD.smul (k := u - xp) (by simp [IsSelfAdjoint]))
  -- the common compact spectral bound
  set c : ℝ := |t₀ - xp| + 1 with hcdef
  set R2 : ℝ := 2 * hsNorm H + 2 * c ^ 2 * hsNorm D with hR2def
  have hR2 : 0 ≤ R2 := by
    rw [hR2def]
    nlinarith [hsNorm_nonneg H, hsNorm_nonneg D, sq_nonneg c]
  set R : ℝ := Real.sqrt R2 + 1 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have hRneg : -R < 0 := by linarith
  have hspec : ∀ u : ℝ, |u - t₀| < 1 → ∀ i : d × Fin N, |(hHu u).eigenvalues i| ≤ R := by
    intro u hu i
    have hs : |u - xp| ≤ c := by
      rw [hcdef]
      calc |u - xp| = |(u - t₀) + (t₀ - xp)| := by ring_nf
        _ ≤ |u - t₀| + |t₀ - xp| := abs_add_le _ _
        _ ≤ 1 + |t₀ - xp| := by linarith
        _ = |t₀ - xp| + 1 := by ring
    have hb : hsNorm (H + (u - xp) • D) ≤ R2 := by
      rw [hR2def]
      have h1 := hsNorm_add_smul_le H D (u - xp)
      have h2 : (u - xp) ^ 2 ≤ c ^ 2 := by
        simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hs 2
      nlinarith [hsNorm_nonneg H, hsNorm_nonneg D]
    have h2 : Real.sqrt (hsNorm (H + (u - xp) • D)) ≤ Real.sqrt R2 :=
      Real.sqrt_le_sqrt hb
    have h3 : Real.sqrt R2 < R := by
      rw [hRdef]; linarith [Real.sqrt_nonneg R2]
    exact (eigenvalues_abs_le_sqrt_hsNorm (H + (u - xp) • D) (hHu u) i).trans (h2.trans h3.le)
  -- the approximation accuracy
  set eps : ℕ → ℝ := fun n => (1 : ℝ) / ((n : ℝ) + 1) / (1 + Real.sqrt (hsNorm D)) with hepsdef
  have heps_pos : ∀ n : ℕ, 0 < eps n := by
    intro n
    rw [hepsdef]
    positivity
  have heps_tend : Tendsto eps atTop (𝓝 0) := by
    rw [hepsdef]
    have h : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using h.div_const (1 + Real.sqrt (hsNorm D))
  -- the polynomial approximants
  have happrox : ∀ n : ℕ, ∃ q : ℝ[X],
      (∀ y ∈ Set.Icc (-R) R, |q.eval y - f y| < eps n) ∧
        (∀ y ∈ Set.Icc (-R) R, |q.derivative.eval y - deriv f y| < eps n) :=
    fun n => exists_polynomial_c1_approx f hf hRneg hRpos (ε := eps n) (heps_pos n)
  choose q hq using happrox
  -- the limiting functions and their polynomial approximants
  have hFbound : ∀ (n : ℕ) (u : ℝ), u ∈ Metric.ball t₀ 1 →
      |guePencilNormTrace (polyMatrix (q n) (H + (u - xp) • D))
        - guePencilNormTrace (cfc f (H + (u - xp) • D))| ≤ eps n := by
    intro n u hu
    have hu' : |u - t₀| < 1 := by
      simpa [Real.dist_eq] using Metric.mem_ball.mp hu
    have hspecu := hspec u hu'
    have hM := hHu u
    have hbnd : ‖(cfc (fun y : ℝ => (q n).eval y - f y) (H + (u - xp) • D)).trace‖
        ≤ (Fintype.card (d × Fin N) : ℝ) * eps n := by
      refine abs_trace_cfc_le (M := H + (u - xp) • D) (hM := hM)
        (g := fun y : ℝ => (q n).eval y - f y) (R := R) (C := eps n) ?_ ?_
      · intro i; exact hspecu i
      · intro y hy
        exact le_of_lt ((hq n).1 y (Set.mem_Icc.mpr (abs_le.mp hy)))
    have hdiff : polyMatrix (q n) (H + (u - xp) • D) - cfc f (H + (u - xp) • D)
        = cfc (fun y : ℝ => (q n).eval y - f y) (H + (u - xp) • D) := by
      rw [← cfc_polyMatrix_eq (q n) _ hM,
        ← cfc_sub_of_hermitian (fun y : ℝ => (q n).eval y) f (Polynomial.continuous (q n))
          hf.continuous _ hM]
    have hsub : guePencilNormTrace (polyMatrix (q n) (H + (u - xp) • D))
        - guePencilNormTrace (cfc f (H + (u - xp) • D))
        = gueNormConst d N
          * ((cfc (fun y : ℝ => (q n).eval y - f y) (H + (u - xp) • D)).trace).re := by
      rw [guePencilNormTrace, guePencilNormTrace, ← hdiff, Matrix.trace_sub, Complex.sub_re]
      ring
    have hcoef : 0 ≤ gueNormConst d N := gueNormConst_nonneg
    rw [hsub, abs_mul]
    calc |gueNormConst d N| * |((cfc (fun y : ℝ => (q n).eval y - f y)
            (H + (u - xp) • D)).trace).re|
        = gueNormConst d N * |((cfc (fun y : ℝ => (q n).eval y - f y)
            (H + (u - xp) • D)).trace).re| := by rw [abs_of_nonneg hcoef]
      _ ≤ gueNormConst d N * ‖(cfc (fun y : ℝ => (q n).eval y - f y)
            (H + (u - xp) • D)).trace‖ :=
          mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hcoef
      _ ≤ gueNormConst d N * ((Fintype.card (d × Fin N) : ℝ) * eps n) :=
          mul_le_mul_of_nonneg_left hbnd hcoef
      _ = (gueNormConst d N * (Fintype.card (d × Fin N) : ℝ)) * eps n := by ring
      _ ≤ 1 * eps n :=
          mul_le_mul_of_nonneg_right gueNormConst_mul_card_le_one (le_of_lt (heps_pos n))
      _ = eps n := one_mul _
  have hGbound : ∀ (n : ℕ) (u : ℝ), u ∈ Metric.ball t₀ 1 →
      |guePencilNormTrace (polyMatrix (q n).derivative (H + (u - xp) • D) * D)
        - guePencilNormTrace (cfc (deriv f) (H + (u - xp) • D) * D)|
        ≤ eps n * Real.sqrt (hsNorm D) := by
    intro n u hu
    have hu' : |u - t₀| < 1 := by
      simpa [Real.dist_eq] using Metric.mem_ball.mp hu
    have hspecu := hspec u hu'
    have hM := hHu u
    have hcont : Continuous (fun y : ℝ => (q n).derivative.eval y - deriv f y) :=
      (Polynomial.continuous (q n).derivative).sub hf.continuous_deriv_one
    have hbnd : hsNorm (cfc (fun y : ℝ => (q n).derivative.eval y - deriv f y)
          (H + (u - xp) • D))
        ≤ (Fintype.card (d × Fin N) : ℝ) * (eps n) ^ 2 := by
      refine hsNorm_cfc_le (M := H + (u - xp) • D) (hM := hM)
        (g := fun y : ℝ => (q n).derivative.eval y - deriv f y) (hg := hcont)
        (R := R) (C := eps n) ?_ ?_ (le_of_lt (heps_pos n))
      · intro i; exact hspecu i
      · intro y hy
        exact le_of_lt ((hq n).2 y (Set.mem_Icc.mpr (abs_le.mp hy)))
    have hdiff : polyMatrix (q n).derivative (H + (u - xp) • D) * D
        - cfc (deriv f) (H + (u - xp) • D) * D
        = cfc (fun y : ℝ => (q n).derivative.eval y - deriv f y)
            (H + (u - xp) • D) * D := by
      rw [← cfc_polyMatrix_eq (q n).derivative _ hM, ← sub_mul,
        ← cfc_sub_of_hermitian (fun y : ℝ => (q n).derivative.eval y) (deriv f)
          (Polynomial.continuous (q n).derivative) hf.continuous_deriv_one _ hM]
    have hsub : guePencilNormTrace (polyMatrix (q n).derivative (H + (u - xp) • D) * D)
        - guePencilNormTrace (cfc (deriv f) (H + (u - xp) • D) * D)
        = gueNormConst d N
          * ((cfc (fun y : ℝ => (q n).derivative.eval y - deriv f y)
              (H + (u - xp) • D) * D).trace).re := by
      rw [guePencilNormTrace, guePencilNormTrace, ← hdiff, Matrix.trace_sub, Complex.sub_re]
      ring
    have hcoef : 0 ≤ gueNormConst d N := gueNormConst_nonneg
    have hK : 0 ≤ Real.sqrt (hsNorm D) := Real.sqrt_nonneg _
    rw [hsub, abs_mul]
    calc |gueNormConst d N| * |((cfc (fun y : ℝ => (q n).derivative.eval y - deriv f y)
            (H + (u - xp) • D) * D).trace).re|
        = gueNormConst d N * |((cfc (fun y : ℝ => (q n).derivative.eval y - deriv f y)
            (H + (u - xp) • D) * D).trace).re| := by rw [abs_of_nonneg hcoef]
      _ ≤ gueNormConst d N * ‖(cfc (fun y : ℝ => (q n).derivative.eval y - deriv f y)
            (H + (u - xp) • D) * D).trace‖ :=
          mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hcoef
      _ ≤ gueNormConst d N
            * (Real.sqrt (hsNorm (cfc (fun y : ℝ => (q n).derivative.eval y - deriv f y)
                (H + (u - xp) • D))) * Real.sqrt (hsNorm D)) := by
          refine mul_le_mul_of_nonneg_left ?_ hcoef
          exact norm_trace_mul_le_sqrt_hsNorm _ _
      _ ≤ gueNormConst d N
            * (Real.sqrt ((Fintype.card (d × Fin N) : ℝ) * (eps n) ^ 2)
              * Real.sqrt (hsNorm D)) := by
          refine mul_le_mul_of_nonneg_left ?_ hcoef
          exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hbnd) hK
      _ = (gueNormConst d N * Real.sqrt (Fintype.card (d × Fin N) : ℝ))
            * (eps n * Real.sqrt (hsNorm D)) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (le_of_lt (heps_pos n))]
          ring
      _ ≤ 1 * (eps n * Real.sqrt (hsNorm D)) :=
          mul_le_mul_of_nonneg_right gueNormConst_mul_sqrt_card_le_one
            (mul_nonneg (le_of_lt (heps_pos n)) hK)
      _ = eps n * Real.sqrt (hsNorm D) := one_mul _
  -- uniform convergence of the values and of the derivatives
  have hU1 : TendstoUniformlyOn
      (fun n : ℕ => fun u : ℝ => guePencilNormTrace (polyMatrix (q n) (H + (u - xp) • D)))
      (fun u : ℝ => guePencilNormTrace (cfc f (H + (u - xp) • D)))
      atTop (Metric.ball t₀ 1) :=
    tendstoUniformlyOn_of_abs_sub_le heps_tend hFbound
  have hU2 : TendstoUniformlyOn
      (fun n : ℕ => fun u : ℝ =>
        guePencilNormTrace (polyMatrix (q n).derivative (H + (u - xp) • D) * D))
      (fun u : ℝ => guePencilNormTrace (cfc (deriv f) (H + (u - xp) • D) * D))
      atTop (Metric.ball t₀ 1) := by
    refine tendstoUniformlyOn_of_abs_sub_le ?_ hGbound
    have h := heps_tend.mul_const (Real.sqrt (hsNorm D))
    simpa using h
  -- the polynomial approximants are differentiable with the announced derivative
  have hd : ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, u ∈ Metric.ball t₀ 1 →
      HasDerivAt (fun u : ℝ => guePencilNormTrace (polyMatrix (q n) (H + (u - xp) • D)))
        (guePencilNormTrace (polyMatrix (q n).derivative (H + (u - xp) • D) * D)) u := by
    refine Eventually.of_forall fun n => ?_
    have hFn : (fun u : ℝ => guePencilNormTrace (polyMatrix (q n) (H + (u - xp) • D)))
        = fun u : ℝ => gueStatisticNorm (q n) A₀ A (euclidUpdate x p u) := by
      funext u
      simp only [gueStatisticNorm, hmat u]
    have hGn : (fun u : ℝ =>
          guePencilNormTrace (polyMatrix (q n).derivative (H + (u - xp) • D) * D))
        = fun u : ℝ => gueStatisticNormDir (q n) A₀ A p (euclidUpdate x p u) := by
      funext u
      simp only [gueStatisticNormDir, gueDerivMatrix, hmat u, ← hDdef]
    intro u hu
    have hval := congrFun hGn u
    have h := hasDerivAt_gueStatisticNorm_update (q n) A₀ A x p u
    rw [← hFn, ← hval] at h
    exact h
  -- pointwise convergence of the values
  have hconv : ∀ u : ℝ, u ∈ Metric.ball t₀ 1 →
      Tendsto (fun n : ℕ => guePencilNormTrace (polyMatrix (q n) (H + (u - xp) • D)))
        atTop (𝓝 (guePencilNormTrace (cfc f (H + (u - xp) • D)))) := by
    intro u hu
    have hb : ∀ n : ℕ, |guePencilNormTrace (polyMatrix (q n) (H + (u - xp) • D))
        - guePencilNormTrace (cfc f (H + (u - xp) • D))| ≤ eps n :=
      fun n => hFbound n u hu
    have hlim : Tendsto (fun n : ℕ =>
        |guePencilNormTrace (polyMatrix (q n) (H + (u - xp) • D))
          - guePencilNormTrace (cfc f (H + (u - xp) • D))|) atTop (𝓝 0) :=
      squeeze_zero (fun n => abs_nonneg _) hb heps_tend
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa [Real.norm_eq_abs] using hlim
  -- assemble
  have hmain : HasDerivAt (fun u : ℝ => guePencilNormTrace (cfc f (H + (u - xp) • D)))
      (guePencilNormTrace (cfc (deriv f) (H + (t₀ - xp) • D) * D)) t₀ :=
    hasDerivAt_of_tendstoUniformlyOn Metric.isOpen_ball hU2 hd hconv
      (Metric.mem_ball_self zero_lt_one)
  rw [hFfun, hGval]
  exact hmain


/-- **The cfc trace derivative almost everywhere, for all `t`.**  In fact the pointwise theorem
holds for every `x`, so no exceptional set is needed. -/
theorem ae_hasDerivAt_gueStatisticCfc_update (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) (p : GUECoord ι N) :
    ∀ᵐ x ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))), ∀ t : ℝ,
      HasDerivAt (fun u : ℝ => gueStatisticCfc f A₀ A hA₀ hA (euclidUpdate x p u))
        (gueStatisticCfcDir f A₀ A hA₀ hA p (euclidUpdate x p t)) t :=
  Filter.Eventually.of_forall fun x t =>
    hasDerivAt_gueStatisticCfc_update f hf A₀ A hA₀ hA x p t

/-- The trace derivative in the form with an explicit differentiability hypothesis on `f`
(equivalent to `ContDiff ℝ 1 f`). -/
theorem hasDerivAt_gueStatisticCfc_update_of_continuous_deriv (f : ℝ → ℝ)
    (hfd : Differentiable ℝ f) (hf' : Continuous (deriv f))
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian)
    (x : EuclideanSpace ℝ (GUECoord ι N)) (p : GUECoord ι N) (t₀ : ℝ) :
    HasDerivAt (fun u : ℝ => gueStatisticCfc f A₀ A hA₀ hA (euclidUpdate x p u))
      (gueStatisticCfcDir f A₀ A hA₀ hA p (euclidUpdate x p t₀)) t₀ :=
  hasDerivAt_gueStatisticCfc_update f (contDiff_one_iff_deriv.mpr ⟨hfd, hf'⟩)
    A₀ A hA₀ hA x p t₀

/-! ### The unconditional smooth Lemma V -/

/-- **Smooth Lemma V, with the trace-derivative hypothesis discharged.**  For `f : ℝ → ℝ` of
class `C¹`,

`Var(tau_N(f(H_N))) ≤ 2 (∑_i frob(A_i)²) / (card d) / N² · E[tau_N((f')²(H_N))]`.

Compared with `lemmaV_sharp_smooth_of_traceDeriv`, the analytic hypothesis `hderiv` is now a
theorem (`ae_hasDerivAt_gueStatisticCfc_update`), and `Continuous f`, `Continuous (deriv f)` are
supplied by `ContDiff ℝ 1 f`. -/
theorem lemmaV_sharp_smooth [Nonempty d] (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) (hN : 0 < N)
    (hF : MemLp (gueStatisticCfc f A₀ A hA₀ hA) 2
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
    (hDmem : ∀ p : GUECoord ι N, MemLp (gueStatisticCfcDir f A₀ A hA₀ hA p) 2
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
    (hpoly : ∀ p : GUECoord ι N,
      ∀ᵐ x ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))),
        PolyGrowth (fun u : ℝ => gueStatisticCfc f A₀ A hA₀ hA (euclidUpdate x p u)) ∧
        PolyGrowth (fun u : ℝ =>
          gueStatisticCfcDir f A₀ A hA₀ hA p (euclidUpdate x p u)))
    (hint : Integrable
      (fun x => hsNorm (guePencilCfc (deriv f) A₀ A hA₀ hA x))
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) :
    variance (gueStatisticCfc f A₀ A hA₀ hA)
        (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      ≤ 2 * (∑ i, (frob (A i)) ^ 2) / (Fintype.card d : ℝ) / (N : ℝ) ^ 2 *
          ∫ x, gueStatisticCfc (fun y => (deriv f y) ^ 2) A₀ A hA₀ hA x
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
  lemmaV_sharp_smooth_of_traceDeriv f hf.continuous hf.continuous_deriv_one A₀ A hA₀ hA hN
    hF hDmem hpoly (fun p => ae_hasDerivAt_gueStatisticCfc_update f hf A₀ A hA₀ hA p) hint

/-- The trace derivative in the `∀ᵐ x, ∀ t` form, from differentiability and continuity of the
derivative. -/
theorem ae_hasDerivAt_gueStatisticCfc_update_of_continuous_deriv (f : ℝ → ℝ)
    (hfd : Differentiable ℝ f) (hf' : Continuous (deriv f))
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) (p : GUECoord ι N) :
    ∀ᵐ x ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))), ∀ t : ℝ,
      HasDerivAt (fun u : ℝ => gueStatisticCfc f A₀ A hA₀ hA (euclidUpdate x p u))
        (gueStatisticCfcDir f A₀ A hA₀ hA p (euclidUpdate x p t)) t :=
  Filter.Eventually.of_forall fun x t =>
    hasDerivAt_gueStatisticCfc_update_of_continuous_deriv f hfd hf' A₀ A hA₀ hA x p t

/-- **Smooth Lemma V** in the form with explicit hypotheses `Differentiable ℝ f` and
`Continuous (deriv f)` (jointly equivalent to `ContDiff ℝ 1 f`). -/
theorem lemmaV_sharp_smooth_of_differentiable [Nonempty d] (f : ℝ → ℝ)
    (hfd : Differentiable ℝ f) (hf' : Continuous (deriv f))
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) (hN : 0 < N)
    (hF : MemLp (gueStatisticCfc f A₀ A hA₀ hA) 2
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
    (hDmem : ∀ p : GUECoord ι N, MemLp (gueStatisticCfcDir f A₀ A hA₀ hA p) 2
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
    (hpoly : ∀ p : GUECoord ι N,
      ∀ᵐ x ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))),
        PolyGrowth (fun u : ℝ => gueStatisticCfc f A₀ A hA₀ hA (euclidUpdate x p u)) ∧
        PolyGrowth (fun u : ℝ =>
          gueStatisticCfcDir f A₀ A hA₀ hA p (euclidUpdate x p u)))
    (hint : Integrable
      (fun x => hsNorm (guePencilCfc (deriv f) A₀ A hA₀ hA x))
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) :
    variance (gueStatisticCfc f A₀ A hA₀ hA)
        (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      ≤ 2 * (∑ i, (frob (A i)) ^ 2) / (Fintype.card d : ℝ) / (N : ℝ) ^ 2 *
          ∫ x, gueStatisticCfc (fun y => (deriv f y) ^ 2) A₀ A hA₀ hA x
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
  lemmaV_sharp_smooth_of_traceDeriv f hfd.continuous hf' A₀ A hA₀ hA hN
    hF hDmem hpoly (fun p => ae_hasDerivAt_gueStatisticCfc_update_of_continuous_deriv
      f hfd hf' A₀ A hA₀ hA p) hint

/-- **The unconditional `(V)` input of the spectral-exclusion argument (Lemma S).**  This is
`lemmaV_sharp_smooth` under the name used by the Lemma-S interface. -/
theorem lemmaS_V_input_unconditional [Nonempty d] (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) (hN : 0 < N)
    (hF : MemLp (gueStatisticCfc f A₀ A hA₀ hA) 2
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
    (hDmem : ∀ p : GUECoord ι N, MemLp (gueStatisticCfcDir f A₀ A hA₀ hA p) 2
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
    (hpoly : ∀ p : GUECoord ι N,
      ∀ᵐ x ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))),
        PolyGrowth (fun u : ℝ => gueStatisticCfc f A₀ A hA₀ hA (euclidUpdate x p u)) ∧
        PolyGrowth (fun u : ℝ =>
          gueStatisticCfcDir f A₀ A hA₀ hA p (euclidUpdate x p u)))
    (hint : Integrable
      (fun x => hsNorm (guePencilCfc (deriv f) A₀ A hA₀ hA x))
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) :
    variance (gueStatisticCfc f A₀ A hA₀ hA)
        (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      ≤ 2 * (∑ i, (frob (A i)) ^ 2) / (Fintype.card d : ℝ) / (N : ℝ) ^ 2 *
          ∫ x, gueStatisticCfc (fun y => (deriv f y) ^ 2) A₀ A hA₀ hA x
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
  lemmaV_sharp_smooth f hf A₀ A hA₀ hA hN hF hDmem hpoly hint


end

end GUEStrongConvergence
