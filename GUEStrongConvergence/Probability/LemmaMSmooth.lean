/-
# Lemma M, smooth form: the finite-side Cauchy–Pompeiu trace identity and Fubini

The smooth (Cauchy–Pompeiu) form of Lemma M compares the mean of the normalized trace
`τ_N(f(H_N))` with the plane integral of the `∂̄` weight times the averaged resolvent.  The
present file supplies the **finite side** of that comparison, in the eigenvalue-free
(matrix-resolvent) form:

`∫_ω Tr(f(H(ω))) dμ = (I/2π) ∫∫ ∂̄F(z) · (∫_ω Tr((z - H(ω))⁻¹) dμ)`,

for a measurable family of Hermitian matrices and `f` of class `C²` with compact support.

The proof has three ingredients:

* the pointwise matrix-resolvent identity `trace_cfc_eq_plane_integral_resolvent`
  (`Probability/TracePompeiu.lean`), applied at every sample `ω`;
* joint measurability of `(ω, z) ↦ Tr((z - H(ω))⁻¹)`, proved here from
  `Matrix.inv_def` (the inverse is a rational function of the entries) together with
  measurability of the determinant and the adjugate;
* the absolute bound `‖Tr((z - H)⁻¹)‖ ≤ n |Im z|⁻¹` for nonreal `z`, together with the
  linear vanishing `‖∂̄F(z)‖ ≤ |Im z| · max ‖f''‖` of the cut-off extension near the real
  axis.  The two bounds multiply to the uniform constant `n · max ‖∂̄F‖` (and to `0` at
  `Im z = 0`, where `∂̄F` vanishes), which makes the double integral integrable and Fubini
  applicable.

## Main results

* `continuous_matrix_det`, `measurable_matrix_inv` — the determinant and the matrix inverse
  are measurable functions of the entries;
* `norm_trace_resolvent_le` — `‖Tr((z - H)⁻¹)‖ ≤ card n · |Im z|⁻¹` for Hermitian `H`;
* `dbarNum_ofReal` — the `∂̄` numerator of the cut-off extension vanishes on the real axis;
* `integral_trace_cfc_eq_plane_integral` — the finite-side Fubini identity;
* `integral_gueStatisticCfc_eq_plane_integral` — the same identity for the GUE pencil
  statistic `τ_N(f(H_N))`, with the inner averaged resolvent identified with
  `N · Tr_d(g_N(z))`, `g_N = gueResolventMean` being the averaged partial-trace resolvent of
  `Probability/AveragedResolvent.lean`.  This is the finite side of the smooth Lemma M in the
  exact normalization of the Lemma-S input `hM`.

## What is *not* proved here (the two remaining gaps)

The comparison with the limit, `|E[τ_N(f(H_N))] − τ(f(h))| ≤ C(f,A)/N²`, needs two further
inputs, neither of which follows from the present material:

1. **A uniform-in-`z` sharp resolvent comparison.**  `frob_gueResolventMean_sub_limit_le_sharp`
   requires `2 (card d)² ∑ᵢ frob(Aᵢ)² ≤ (Im z)²`, i.e. `|Im z| ≥ η_A` for a *fixed* constant
   `η_A`.  On the strip `|Im z| < η_A` only the deterministic bound
   `frob(g_N − g) ≤ 2 (card d)/|Im z|` is available; multiplied by the linear vanishing
   `|∂̄F| = O(|Im z|)` this gives a strip contribution of order **one**, not of order `N⁻²`.
   Hence the present route yields at best `|Eτ_N(f) − τ(f(h))| ≤ C₁(f,A)/N² + C₂(f,A)`
   (and `O(N^{-1/3})` if one is allowed to shrink the vertical support of the extension with
   `N`); the sharp rate `O(N⁻²)` needs a resolvent-difference bound that is better than
   `1/|Im z|` near the real axis.
2. **A limit-side (operator-valued) Cauchy–Pompeiu representation.**  `τ(f(h))` is the
   continuous functional calculus of the limit block element; identifying it with
   `(I/2π) ∫∫ ∂̄F(z) · τ(Tr_d((z − h)⁻¹))` requires the spectral measure of the states of the
   limit algebra (or an operator-valued Pompeiu formula).  `Probability/LimitSideSpectral.lean`
   records this as the unproved `LimitHSTraceRepresentation`.

Both gaps are *analytic*, not bookkeeping: the identities proved here are exact.
-/
import GUEStrongConvergence.Probability.TracePompeiu
import GUEStrongConvergence.Probability.CfcTraceDerivative
import GUEStrongConvergence.Probability.AveragedResolvent
import GUEStrongConvergence.Probability.DysonLimitSharp

open MeasureTheory ProbabilityTheory Matrix Filter Topology Complex
open scoped Matrix.Norms.Frobenius ComplexOrder ENNReal NNReal Topology BigOperators

namespace GUEStrongConvergence

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Measurability of the matrix inverse -/

/-- The determinant is a continuous (hence measurable) function of the entries. -/
lemma continuous_matrix_det : Continuous (fun M : Matrix n n ℂ => M.det) := by
  have h : (fun M : Matrix n n ℂ => M.det)
      = fun M => ∑ σ : Equiv.Perm n, (Equiv.Perm.sign σ : ℂ) * ∏ i, M (σ i) i := by
    funext M; exact Matrix.det_apply' M
  rw [h]
  refine continuous_finset_sum _ (fun σ _ => continuous_const.mul ?_)
  exact continuous_finset_prod _ (fun i _ => (continuous_apply i).comp (continuous_apply (σ i)))

lemma measurable_matrix_det : Measurable (fun M : Matrix n n ℂ => M.det) :=
  continuous_matrix_det.measurable

lemma measurable_matrix_adjugate : Measurable (fun M : Matrix n n ℂ => M.adjugate) := by
  refine Matrix.measurable_iff.mpr (fun i j => ?_)
  have h : (fun M : Matrix n n ℂ => M.adjugate i j)
      = fun M => (M.updateRow j (Pi.single i (1 : ℂ))).det := by
    funext M; exact Matrix.adjugate_apply M i j
  rw [h]
  refine measurable_matrix_det.comp (Matrix.measurable_iff.mpr (fun a b => ?_))
  by_cases hab : a = j
  · subst hab
    simp only [Matrix.updateRow_apply, if_true]
    exact measurable_const
  · simp only [Matrix.updateRow_apply, if_neg hab]
    exact Matrix.measurable_apply

lemma measurable_matrix_inv : Measurable (fun M : Matrix n n ℂ => M⁻¹) := by
  have h : (fun M : Matrix n n ℂ => M⁻¹)
      = fun M => (Ring.inverse M.det) • M.adjugate := by
    funext M; rw [Matrix.inv_def]
  rw [h]
  have hc : Measurable (fun M : Matrix n n ℂ => Ring.inverse M.det) := by
    have h2 : (fun M : Matrix n n ℂ => Ring.inverse M.det) = fun M => (M.det)⁻¹ := by
      funext M; exact Ring.inverse_eq_inv _
    rw [h2]
    exact measurable_matrix_det.inv
  exact hc.smul measurable_matrix_adjugate

lemma measurable_matrix_trace : Measurable (fun M : Matrix n n ℂ => M.trace) := by
  simp only [Matrix.trace]
  exact Finset.measurable_sum _ (fun i _ => Matrix.measurable_apply)

/-! ## The uniform trace bound and the vanishing of `∂̄F` on the real axis -/

/-- **Uniform bound on the trace of the resolvent.**  For a Hermitian matrix `H` and a
nonreal `z`, the modulus of `Tr((z - H)⁻¹)` is at most `card n · |Im z|⁻¹`.  (Off the real
axis `Matrix.inv` is the genuine inverse, so the eigenvalue representation applies.) -/
lemma norm_trace_resolvent_le (H : Matrix n n ℂ) (hH : H.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) :
    ‖Matrix.trace ((z • (1 : Matrix n n ℂ) - H)⁻¹)‖
      ≤ (Fintype.card n : ℝ) * |z.im|⁻¹ := by
  classical
  rw [← resolventTrace_eq_trace_inv H hH z (fun i h => hz (by rw [h]; simp))]
  rw [resolventTrace]
  have himpos : 0 < |z.im| := abs_pos.mpr hz
  calc ‖∑ i, (z - ((hH.eigenvalues i : ℝ) : ℂ))⁻¹‖
      ≤ ∑ i, ‖(z - ((hH.eigenvalues i : ℝ) : ℂ))⁻¹‖ := norm_sum_le _ _
    _ = ∑ i, (‖z - ((hH.eigenvalues i : ℝ) : ℂ)‖)⁻¹ := by simp [norm_inv]
    _ ≤ ∑ _i : n, |z.im|⁻¹ := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        have hne : z - ((hH.eigenvalues i : ℝ) : ℂ) ≠ 0 := by
          intro h
          exact hz (by rw [sub_eq_zero.mp h]; simp)
        have hnorm : 0 < ‖z - ((hH.eigenvalues i : ℝ) : ℂ)‖ := norm_pos_iff.mpr hne
        refine (inv_le_inv₀ hnorm himpos).mpr ?_
        calc |z.im| = |(z - ((hH.eigenvalues i : ℝ) : ℂ)).im| := by simp
          _ ≤ ‖z - ((hH.eigenvalues i : ℝ) : ℂ)‖ := Complex.abs_im_le_norm _
    _ = (Fintype.card n : ℝ) * |z.im|⁻¹ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **The `∂̄` numerator vanishes on the real axis.**  The cut-off extension equals `f` on
the real axis, where the vertical cut-off equals `1`, so the correction term `y f'` and the
`ρ'` term both vanish. -/
lemma dbarNum_ofReal {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : ℝ) :
    dbarNum f (x : ℂ) = 0 := by
  have hρd : Differentiable ℝ yCut := (contDiff_yCut 1).differentiable (by norm_num)
  have hderiv : deriv yCut (0 : ℝ) = 0 := by
    have hmem : (0 : ℝ) ∈ Metric.ball (0 : ℝ) yBump.rIn := by
      have h1 : yBump.rIn = 1 := rfl
      rw [h1, Real.ball_zero_eq_Ioo]; norm_num
    have h1 : yCut =ᶠ[𝓝 (0 : ℝ)] 1 := by
      simpa [yCut] using ContDiffBump.eventuallyEq_one_of_mem_ball (f := yBump) hmem
    rw [Filter.EventuallyEq.deriv_eq h1]
    simp
  have h := dbar_almostAnalyticExtCut (f := f) (ρ := yCut) hf hρd (x : ℂ)
  have hdbar : dbarNum f (x : ℂ) =
      I • fderiv ℝ (fun w : ℂ => almostAnalyticExt f w * (yCut w.im : ℂ)) (x : ℂ) 1
        - fderiv ℝ (fun w : ℂ => almostAnalyticExt f w * (yCut w.im : ℂ)) (x : ℂ) I := rfl
  rw [hdbar, h]
  simp [hderiv]

/-! ## The finite-side Fubini identity -/

/-- The point of the plane associated with a pair of real coordinates. -/
def zOf (p : ℝ × ℝ) : ℂ := (p.1 : ℂ) + (p.2 : ℂ) * I

@[simp] lemma zOf_re (p : ℝ × ℝ) : (zOf p).re = p.1 := by simp [zOf]
@[simp] lemma zOf_im (p : ℝ × ℝ) : (zOf p).im = p.2 := by simp [zOf]

lemma continuous_zOf : Continuous zOf := by unfold zOf; fun_prop

/-- **Joint measurability of the plane integrand.**  For a measurable family of matrices the
pair `(ω, z) ↦ ∂̄F(z) · Tr((z - H(ω))⁻¹)` is jointly measurable: the resolvent is a rational
function of the entries (`Matrix.inv_def`). -/
lemma measurable_uncurry_planeIntegrand
    {Ω : Type*} [MeasurableSpace Ω]
    (H : Ω → Matrix n n ℂ) (hHm : Measurable H) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    Measurable (Function.uncurry fun ω (p : ℝ × ℝ) =>
      dbarNum f (zOf p) * Matrix.trace ((zOf p) • (1 : Matrix n n ℂ) - H ω)⁻¹) := by
  have hz_meas : Measurable (fun q : Ω × (ℝ × ℝ) => zOf q.2) :=
    continuous_zOf.measurable.comp measurable_snd
  have hmat : Measurable (fun q : Ω × (ℝ × ℝ) =>
      (zOf q.2) • (1 : Matrix n n ℂ) - H q.1) := by
    refine Matrix.measurable_iff.mpr (fun a b => ?_)
    have hentry : ∀ q : Ω × (ℝ × ℝ),
        ((zOf q.2) • (1 : Matrix n n ℂ) - H q.1) a b
          = (if a = b then zOf q.2 else 0) - H q.1 a b := by
      intro q
      rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      by_cases hab : a = b <;> simp [hab]
    simp only [hentry]
    refine Measurable.sub ?_ ?_
    · by_cases hab : a = b
      · simp only [hab, if_true]; exact hz_meas
      · simp only [hab, if_false]; exact measurable_const
    · exact Matrix.measurable_apply.comp (hHm.comp measurable_fst)
  have hmeas_inner : Measurable (fun q : Ω × (ℝ × ℝ) =>
      Matrix.trace ((zOf q.2) • (1 : Matrix n n ℂ) - H q.1)⁻¹) :=
    measurable_matrix_trace.comp (measurable_matrix_inv.comp hmat)
  have h2 : Measurable (fun q : Ω × (ℝ × ℝ) => dbarNum f (zOf q.2)) :=
    (continuous_dbarNum hf).measurable.comp hz_meas
  exact h2.mul hmeas_inner

/-- **Finite-side Cauchy–Pompeiu trace identity with Fubini.**

For a measurable family of Hermitian matrices `H` and a `C²` compactly supported `f`,
`∫_ω Tr(f(H(ω))) = (I/2π) ∫∫ ∂̄F(z) ∫_ω Tr((z - H(ω))⁻¹)`. -/
theorem integral_trace_cfc_eq_plane_integral
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (H : Ω → Matrix n n ℂ) (hH : ∀ ω, (H ω).IsHermitian) (hHm : Measurable H)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ∫ ω, (cfc f (H ω)).trace ∂μ =
      (I / (2 * (Real.pi : ℂ))) *
        ∫ p : ℝ × ℝ, dbarNum f (zOf p) *
          (∫ ω, Matrix.trace ((zOf p) • (1 : Matrix n n ℂ) - H ω)⁻¹ ∂μ) := by
  classical
  have hpt : ∀ ω, (cfc f (H ω)).trace =
      (I / (2 * (Real.pi : ℂ))) * ∫ p : ℝ × ℝ,
        dbarNum f (zOf p) *
          Matrix.trace ((zOf p) • (1 : Matrix n n ℂ) - H ω)⁻¹ := by
    intro ω
    rw [Matrix.IsHermitian.cfc_eq (hH ω) f]
    exact trace_cfc_eq_plane_integral_resolvent (H ω) (hH ω) hf hfc
  simp_rw [hpt, integral_const_mul]
  congr 1
  -- measurability of the joint integrand
  have hmeas : Measurable (Function.uncurry fun ω (p : ℝ × ℝ) =>
      dbarNum f (zOf p) * Matrix.trace ((zOf p) • (1 : Matrix n n ℂ) - H ω)⁻¹) :=
    measurable_uncurry_planeIntegrand H hHm hf
  -- the support rectangle
  have hKc : IsCompact (tsupport (dbarNum f)) := hasCompactSupport_dbarNum hfc
  obtain ⟨X, hXpos, hX⟩ : ∃ X : ℝ, 0 < X ∧
      ∀ z ∈ tsupport (dbarNum f), |z.re| < X := by
    have hKr : IsCompact (Complex.re '' tsupport (dbarNum f)) :=
      hKc.image Complex.continuous_re
    obtain ⟨X₀, hX₀⟩ := hKr.exists_bound_of_continuousOn continuous_id.continuousOn
    refine ⟨max X₀ 0 + 1, by have := le_max_right X₀ 0; linarith, fun z hz => ?_⟩
    have h1 : ‖z.re‖ ≤ X₀ := hX₀ _ ⟨z, hz, rfl⟩
    have h2 : |z.re| ≤ X₀ := by simpa [Real.norm_eq_abs] using h1
    have h3 : X₀ ≤ max X₀ 0 := le_max_left _ _
    linarith
  obtain ⟨Y, hYpos, hY⟩ : ∃ Y : ℝ, 0 < Y ∧
      ∀ z ∈ tsupport (dbarNum f), |z.im| < Y := by
    have hKi : IsCompact (Complex.im '' tsupport (dbarNum f)) :=
      hKc.image Complex.continuous_im
    obtain ⟨Y₀, hY₀⟩ := hKi.exists_bound_of_continuousOn continuous_id.continuousOn
    refine ⟨max Y₀ 0 + 1, by have := le_max_right Y₀ 0; linarith, fun z hz => ?_⟩
    have h1 : ‖z.im‖ ≤ Y₀ := hY₀ _ ⟨z, hz, rfl⟩
    have h2 : |z.im| ≤ Y₀ := by simpa [Real.norm_eq_abs] using h1
    have h3 : Y₀ ≤ max Y₀ 0 := le_max_left _ _
    linarith
  -- bounds on `∂̄F`
  obtain ⟨M, hM⟩ := exists_norm_dbarNum_le hf hfc
  obtain ⟨M₂, hM₂⟩ := exists_norm_deriv_deriv_le hf hfc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hM₂0 : 0 ≤ M₂ := (norm_nonneg _).trans (hM₂ 0)
  have hmax0 : 0 ≤ max M M₂ := le_trans hM0 (le_max_left _ _)
  set C : ℝ := max M M₂ * (Fintype.card n : ℝ) with hCdef
  have hC0 : 0 ≤ C := mul_nonneg hmax0 (by positivity)
  -- linear vanishing near the real axis
  have hlin : ∀ z : ℂ, |z.im| < 1 → ‖dbarNum f z‖ ≤ |z.im| * max M M₂ := by
    intro z hz
    have h := norm_dbar_almostAnalyticExtCut_le hf hz hM₂
    have h' : dbarNum f z
        = I • fderiv ℝ (almostAnalyticExtCut f) z 1
          - fderiv ℝ (almostAnalyticExtCut f) z I := rfl
    rw [h']
    exact h.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (abs_nonneg _))
  -- the pointwise bound by the rectangle indicator
  have hbound : ∀ q : Ω × (ℝ × ℝ),
      ‖Function.uncurry (fun ω (p : ℝ × ℝ) => dbarNum f (zOf p) *
        Matrix.trace ((zOf p) • (1 : Matrix n n ℂ) - H ω)⁻¹) q‖
      ≤ C * (Set.Icc (-X) X ×ˢ Set.Icc (-Y) Y).indicator (fun _ => (1 : ℝ)) q.2 := by
    intro q
    obtain ⟨ω, p⟩ := q
    show ‖dbarNum f (zOf p) * Matrix.trace ((zOf p) • (1 : Matrix n n ℂ) - H ω)⁻¹‖
      ≤ C * (Set.Icc (-X) X ×ˢ Set.Icc (-Y) Y).indicator (fun _ => (1 : ℝ)) p
    rw [norm_mul]
    by_cases hp : p ∈ Set.Icc (-X) X ×ˢ Set.Icc (-Y) Y
    · rw [Set.indicator_of_mem hp, mul_one]
      rcases eq_or_ne p.2 0 with h0 | h0
      · have hzp : zOf p = ((p.1 : ℝ) : ℂ) := by simp [zOf, h0]
        rw [hzp, dbarNum_ofReal hf]
        simp [hC0]
      · have hzpim : (zOf p).im = p.2 := zOf_im p
        have hdb : ‖dbarNum f (zOf p)‖ ≤ max M M₂ := by
          rcases lt_or_ge |(zOf p).im| 1 with h1 | h1
          · have h1' : |p.2| < 1 := by rw [← hzpim]; exact h1
            refine (hlin _ h1).trans ?_
            rw [hzpim]
            calc |p.2| * max M M₂ ≤ 1 * max M M₂ :=
                  mul_le_mul_of_nonneg_right (le_of_lt h1') hmax0
              _ = max M M₂ := one_mul _
          · exact (hM _).trans (le_max_left _ _)
        have htr := norm_trace_resolvent_le (H ω) (hH ω) (by rw [hzpim]; exact h0)
        have hcard0 : 0 ≤ (Fintype.card n : ℝ) := by positivity
        rcases lt_or_ge |p.2| 1 with h1 | h1
        · have hdb' : ‖dbarNum f (zOf p)‖ ≤ |p.2| * max M M₂ := by
            have h2 := hlin _ (by rw [hzpim]; exact h1)
            rwa [hzpim] at h2
          calc ‖dbarNum f (zOf p)‖ * ‖Matrix.trace ((zOf p) • (1 : Matrix n n ℂ) - H ω)⁻¹‖
              ≤ (|p.2| * max M M₂) * ((Fintype.card n : ℝ) * |(zOf p).im|⁻¹) := by
                  refine mul_le_mul hdb' htr (norm_nonneg _) (by positivity)
            _ = C := by
                  rw [hzpim, hCdef]
                  have habs : |p.2| ≠ 0 := ne_of_gt (abs_pos.mpr h0)
                  field_simp
        · calc ‖dbarNum f (zOf p)‖ * ‖Matrix.trace ((zOf p) • (1 : Matrix n n ℂ) - H ω)⁻¹‖
              ≤ (max M M₂) * ((Fintype.card n : ℝ) * |(zOf p).im|⁻¹) := by
                  refine mul_le_mul hdb htr (norm_nonneg _) hmax0
            _ ≤ (max M M₂) * ((Fintype.card n : ℝ) * 1) := by
                  refine mul_le_mul_of_nonneg_left ?_ hmax0
                  refine mul_le_mul_of_nonneg_left ?_ hcard0
                  rw [hzpim]
                  exact inv_le_one_of_one_le₀ h1
            _ = C := by rw [hCdef]; ring
    · rw [Set.indicator_of_notMem hp, mul_zero]
      have hznot : zOf p ∉ tsupport (dbarNum f) := by
        intro hmem
        apply hp
        refine ⟨?_, ?_⟩
        · rw [Set.mem_Icc]
          have h1 := hX _ hmem
          rw [zOf_re] at h1
          exact abs_le.mp h1.le
        · rw [Set.mem_Icc]
          have h1 := hY _ hmem
          rw [zOf_im] at h1
          exact abs_le.mp h1.le
      rw [image_eq_zero_of_notMem_tsupport hznot]
      simp
  -- the dominating integrable function
  have hdom : Integrable (fun q : Ω × (ℝ × ℝ) =>
      C * (Set.Icc (-X) X ×ˢ Set.Icc (-Y) Y).indicator (fun _ => (1 : ℝ)) q.2)
      (μ.prod (volume : Measure (ℝ × ℝ))) := by
    have hKmeas : MeasurableSet (Set.Icc (-X) X ×ˢ Set.Icc (-Y) Y : Set (ℝ × ℝ)) :=
      measurableSet_Icc.prod measurableSet_Icc
    have hKfin : (volume : Measure (ℝ × ℝ)) (Set.Icc (-X) X ×ˢ Set.Icc (-Y) Y) < ∞ :=
      (isCompact_Icc.prod isCompact_Icc).measure_lt_top
    have hg : Integrable (fun p : ℝ × ℝ =>
        C * (Set.Icc (-X) X ×ˢ Set.Icc (-Y) Y).indicator (fun _ => (1 : ℝ)) p)
        (volume : Measure (ℝ × ℝ)) := by
      have h1 : Integrable ((Set.Icc (-X) X ×ˢ Set.Icc (-Y) Y).indicator
          (fun _ => (1 : ℝ))) (volume : Measure (ℝ × ℝ)) := by
        rw [integrable_indicator_iff hKmeas]
        exact integrableOn_const hKfin.ne
      exact h1.const_mul C
    exact hg.comp_snd μ
  have hInt : Integrable (Function.uncurry fun ω (p : ℝ × ℝ) =>
      dbarNum f (zOf p) * Matrix.trace ((zOf p) • (1 : Matrix n n ℂ) - H ω)⁻¹)
      (μ.prod (volume : Measure (ℝ × ℝ))) := by
    refine Integrable.mono' hdom hmeas.aestronglyMeasurable ?_
    filter_upwards with q
    exact hbound q
  -- Fubini
  rw [integral_integral_swap hInt]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  exact integral_const_mul _ _

/-! ## Bounds and measurability of the trace of the cfc -/

section TraceCfc

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A continuous compactly supported function is globally bounded in modulus. -/
lemma exists_abs_le_of_hasCompactSupport {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) : ∃ C, ∀ y : ℝ, |f y| ≤ C := by
  have hK : IsCompact (tsupport f) := hfc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C 0, fun y => ?_⟩
  by_cases hy : y ∈ tsupport f
  · have h1 : ‖f y‖ ≤ C := hC y hy
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hy]
    exact le_trans (le_of_eq (abs_zero)) (le_max_right _ _)

/-- **Trace bound for the cfc of a globally bounded function.** -/
lemma norm_trace_cfc_le {g : ℝ → ℝ} {C : ℝ} (hC : ∀ y : ℝ, |g y| ≤ C)
    (M : Matrix n n ℂ) (hM : M.IsHermitian) :
    ‖(cfc g M).trace‖ ≤ (Fintype.card n : ℝ) * C := by
  rw [trace_cfc_eq_sum_eigenvalues_matrix M hM g]
  calc ‖∑ i, ((g (hM.eigenvalues i) : ℝ) : ℂ)‖
      ≤ ∑ i, ‖((g (hM.eigenvalues i) : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ = ∑ i, |g (hM.eigenvalues i)| := by simp
    _ ≤ ∑ _i : n, C := Finset.sum_le_sum (fun i _ => hC _)
    _ = (Fintype.card n : ℝ) * C := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Measurability of the trace of the cfc**, through the plane representation of
`integral_trace_cfc_eq_plane_integral`: it is the integral over the plane of a jointly
measurable integrand. -/
lemma aemeasurable_trace_cfc
    (H : Ω → Matrix n n ℂ) (hH : ∀ ω, (H ω).IsHermitian) (hHm : Measurable H)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    AEMeasurable (fun ω => (cfc f (H ω)).trace) μ := by
  have hmeas := measurable_uncurry_planeIntegrand H hHm hf
  have h2 : StronglyMeasurable (fun ω => ∫ p : ℝ × ℝ, dbarNum f (zOf p) *
      Matrix.trace ((zOf p) • (1 : Matrix n n ℂ) - H ω)⁻¹ ∂(volume : Measure (ℝ × ℝ))) :=
    hmeas.stronglyMeasurable.integral_prod_right'
  have hEq : (fun ω => (cfc f (H ω)).trace) = fun ω => (I / (2 * (Real.pi : ℂ))) *
      ∫ p : ℝ × ℝ, dbarNum f (zOf p) *
        Matrix.trace ((zOf p) • (1 : Matrix n n ℂ) - H ω)⁻¹ ∂(volume : Measure (ℝ × ℝ)) := by
    funext ω
    rw [Matrix.IsHermitian.cfc_eq (hH ω) f]
    exact trace_cfc_eq_plane_integral_resolvent (H ω) (hH ω) hf hfc
  rw [hEq]
  exact (h2.const_mul _).aemeasurable

/-- **Integrability of the trace of the cfc** in a measurable family of Hermitian matrices. -/
lemma integrable_trace_cfc [IsProbabilityMeasure μ]
    (H : Ω → Matrix n n ℂ) (hH : ∀ ω, (H ω).IsHermitian) (hHm : Measurable H)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Integrable (fun ω => (cfc f (H ω)).trace) μ := by
  obtain ⟨C, hC⟩ := exists_abs_le_of_hasCompactSupport hf.continuous hfc
  refine Integrable.of_bound (aemeasurable_trace_cfc H hH hHm hf hfc).aestronglyMeasurable
    ((Fintype.card n : ℝ) * C) ?_
  filter_upwards with ω
  exact norm_trace_cfc_le hC (H ω) (hH ω)

end TraceCfc

/-! ## The GUE pencil: identification of the averaged resolvent trace -/

section Pencil

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] {N : ℕ}

/-- **The pencil resolvent is the matrix inverse.**  Both are `Ring.inverse` of the same
element; no resolvent-set hypothesis is needed. -/
lemma guePencilResolvent_eq_matrix_inv
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (x : GUECoord ι N → ℝ) (z : ℂ) :
    guePencilResolvent A₀ A x z
      = (z • (1 : Matrix (d × Fin N) (d × Fin N) ℂ) - guePencilMatrix A₀ A x)⁻¹ := by
  rw [guePencilResolvent, resolvent, Matrix.nonsing_inv_eq_ringInverse, Algebra.algebraMap_eq_smul_one]
  congr 1

/-- **The full trace versus the normalized partial trace.** -/
lemma trace_eq_card_mul_trace_partialTraceN (hN : (N : ℂ) ≠ 0)
    (M : Matrix (d × Fin N) (d × Fin N) ℂ) :
    Matrix.trace M = (N : ℂ) * Matrix.trace (partialTraceN (N := N) M) := by
  simp only [Matrix.trace, Matrix.diag_apply, Finset.mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [show partialTraceN (N := N) M u u = (N : ℂ)⁻¹ * ∑ k : Fin N, M (u, k) (u, k) from rfl,
    ← mul_assoc, mul_inv_cancel₀ hN, one_mul]

/-- The trace identity for a `CStarMatrix` (the type is a synonym for `Matrix`). -/
lemma trace_eq_card_mul_trace_partialTraceN' (hN : (N : ℂ) ≠ 0)
    (M : CStarMatrix (d × Fin N) (d × Fin N) ℂ) :
    Matrix.trace M = (N : ℂ) * Matrix.trace (partialTraceN (N := N) M) := by
  have key := trace_eq_card_mul_trace_partialTraceN (d := d) (N := N) hN
    (CStarMatrix.ofMatrix.symm M)
  have hM : (CStarMatrix.ofMatrix.symm M : Matrix (d × Fin N) (d × Fin N) ℂ) = M := rfl
  rw [hM] at key
  exact key

/-- Integrability of a partial-trace entry for any nonreal `z` (the project's
`integrable_guePartialTrace_entry` is stated for `0 < Im z` only). -/
lemma integrable_guePartialTrace_entry_gen
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (hN : 0 < N) (u v : d) :
    Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
  Integrable.of_bound
    ((continuous_guePartialTrace_entry A₀ A hA₀ hA z hz u v).aestronglyMeasurable)
    (|z.im|⁻¹)
    (ae_of_all _ fun x => norm_guePartialTrace_entry_le A₀ A hA₀ hA _ z hz hN u v)

/-- **Identification of the inner integral with the averaged partial trace.**  For nonreal
`z`, the mean of the full resolvent trace is `N` times the trace of `g_N(z)`. -/
lemma integral_trace_guePencilResolvent_eq
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (hN : 0 < N) {z : ℂ} (hz : z.im ≠ 0) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        Matrix.trace ((z • (1 : Matrix (d × Fin N) (d × Fin N) ℂ) - guePencilMatrix A₀ A x)⁻¹)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      = (N : ℂ) * Matrix.trace (gueResolventMean (N := N) A₀ A z) := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  simp_rw [← guePencilResolvent_eq_matrix_inv, trace_eq_card_mul_trace_partialTraceN' hNc]
  rw [integral_const_mul]
  congr 1
  simp only [Matrix.trace, Matrix.diag_apply]
  rw [integral_finsetSum Finset.univ (f := fun u (x : EuclideanSpace ℝ (GUECoord ι N)) =>
      partialTraceN (N := N) (guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z) u u)
      (fun u _ => by
        simpa only [guePartialTrace] using
          integrable_guePartialTrace_entry_gen A₀ A hA₀ hA z hz hN u u)]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  exact (gueResolventMean_apply (N := N) A₀ A z u u).symm

/-- **The mean of the trace of `f(H_N)` as a plane integral of the averaged resolvent.** -/
theorem integral_trace_guePencilCfc_eq_plane_integral
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (hN : 0 < N) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), (cfc f (guePencilMatrix A₀ A x)).trace
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      = (I / (2 * (Real.pi : ℂ))) *
          ∫ p : ℝ × ℝ, dbarNum f (zOf p) *
            ((N : ℂ) * Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p))) := by
  rw [integral_trace_cfc_eq_plane_integral (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      guePencilMatrix A₀ A x)
      (fun x => guePencilMatrix_isHermitian A₀ A hA₀ hA _)
      (continuous_guePencilMatrix A₀ A).measurable hf hfc]
  congr 1
  have hnull : (volume : Measure (ℝ × ℝ)) {p : ℝ × ℝ | p.2 = 0} = 0 := by
    have h1 : {p : ℝ × ℝ | p.2 = 0} = Set.univ ×ˢ ({0} : Set ℝ) := by
      ext p; simp
    rw [h1]
    change ((volume : Measure ℝ).prod (volume : Measure ℝ)) (Set.univ ×ˢ ({0} : Set ℝ)) = 0
    rw [Measure.prod_prod]
    simp
  refine integral_congr_ae ?_
  filter_upwards [compl_mem_ae_iff.mpr hnull] with p hp
  rw [integral_trace_guePencilResolvent_eq A₀ A hA₀ hA hN (by rw [zOf_im]; exact hp)]

/-- **Lemma M, smooth form, finite side, in the normalization of the pencil statistic.**

The mean of `τ_N(f(H_N))` is the real part of the plane integral of `∂̄F` against the
matrix trace of the averaged partial-trace resolvent `g_N`. -/
theorem integral_gueStatisticCfc_eq_plane_integral
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (hN : 0 < N) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), gueStatisticCfc (N := N) f A₀ A hA₀ hA x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      = gueNormConst d N *
          ((I / (2 * (Real.pi : ℂ))) *
            ∫ p : ℝ × ℝ, dbarNum f (zOf p) *
              ((N : ℂ) * Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p)))).re := by
  have hInt : Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      (cfc f (guePencilMatrix A₀ A x)).trace)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
    integrable_trace_cfc (fun x : EuclideanSpace ℝ (GUECoord ι N) => guePencilMatrix A₀ A x)
      (fun x => guePencilMatrix_isHermitian A₀ A hA₀ hA _)
      (continuous_guePencilMatrix A₀ A).measurable hf hfc
  simp_rw [gueStatisticCfc, guePencilNormTrace, guePencilCfc_eq_cfc]
  rw [integral_const_mul]
  congr 1
  have hre : ∫ x : EuclideanSpace ℝ (GUECoord ι N),
      (cfc f (guePencilMatrix A₀ A x)).trace.re
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      = (∫ x : EuclideanSpace ℝ (GUECoord ι N),
          (cfc f (guePencilMatrix A₀ A x)).trace
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))).re := by
    simpa using Complex.reCLM.integral_comp_comm hInt
  rw [hre, integral_trace_guePencilCfc_eq_plane_integral A₀ A hA₀ hA hN hf hfc]

end Pencil

end

end GUEStrongConvergence
