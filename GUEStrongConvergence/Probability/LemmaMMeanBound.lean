/-
# Lemma M with a mean-resolvent bound: the plane-integral reduction and its residual

The smooth form of Lemma M compares the mean `E τ_N(f(H_N))` of the GUE pencil with the limit
statistic.  The Cauchy--Pompeiu representation (`Probability/LemmaMSmooth.lean`) writes the mean
as the plane integral

`E τ_N(f(H_N)) = (card d)⁻¹ · Re ((I/2π) ∫∫ ∂̄F(z) · Tr_d(g_N(z)))`,

where `g_N(z) = gueResolventMean A₀ A z` is the averaged partial-trace resolvent
(`integral_gueStatisticCfc_eq_plane_integral'`, the normalization in which `gueNormConst` and
the factor `N` cancel).  Comparing with the same plane integral of the *limit* Cauchy transform
`g = operatorMatrixPencilCauchy A₀ A` turns the discrepancy into the single scalar quantity

`S_N(f) = ∫∫ ‖∂̄F(z)‖ · frob (g_N(z) − g(z))`,

so the whole `N`-dependence of Lemma M sits in one weighted resolvent-difference mass.

The file then controls `S_N(f)` from the **single analytic hypothesis**

`hgN : ∀ N z, z.im ≠ 0 → frob (gueResolventMean (N := N) A₀ A z) ≤ M`

(a uniform *a priori* bound on the mean resolvent), together with the companion condition
`2 M² ∑ ‖A_i‖² ≤ 1` needed by the sharp stability comparison.  Off the strip `Im z < η₀` the
sharp comparison `frob_gueResolventMean_sub_limit_le_sharp_of_bound`
(`Probability/DysonStabilityBound.lean`) applies with bound `M` for *both* resolvents
(`frob g ≤ card d / |Im z| ≤ card d/η₀ ≤ M` is the hypothesis `hMd`), and gives

`frob (g_N(z) − g(z)) ≤ C_far / N²`,
`C_far = 2 M (card d) (2 (card d)² √(card d) (∑‖A_i‖²)) (2 ∑‖A_i‖²)`.

On the strip only the deterministic bound `frob (g_N − g) ≤ M + card d |Im z|⁻¹` is available
(`frob_sub_pencilCauchy_le_of_mean_bound`).

## Main results

* `norm_trace_le_card_mul_frob` — `‖Tr M‖ ≤ card d · frob M`;
* `integral_gueStatisticCfc_eq_plane_integral'` — the mean in the normalization `(card d)⁻¹`;
* `abs_integral_gueStatisticCfc_le_of_mean_bound` — `|E τ_N(f)| ≤ M/(2π) ∫∫ ‖∂̄F‖`;
* `frob_gueResolventMean_le_abs` — the deterministic bound in both half-planes;
* `sharp_weight_le`, `frob_sub_pencilCauchy_le_of_mean_bound` — the pointwise comparison under
  `hgN`: sharp `O(N⁻²)` off the strip, deterministic bound on the strip;
* `smooth_trace_comparison_of_mean_bound` — **Lemma M with explicit constants**:
  `|E τ_N(f) − guePlaneLimit| ≤ (2π)⁻¹ ∫∫ ‖∂̄F‖ (C_far/N² + M + card d |Im z|⁻¹)`.

## What is *not* proved here (the exact residual)

1. **The strip term.**  The weight `M + card d |Im z|⁻¹` is not `O(N⁻²)`; with the first-order
   extension `‖∂̄F‖ ≤ |Im z| ‖f''‖` the strip contributes an `N`-independent constant, and this
   is sharp for this extension.  Closing Lemma M needs `∂̄` vanishing of order `≥ 5`, i.e. the
   order-6 extension `almostAnalyticExtOrderCut 6 f` together with **the order-6 Cauchy--Pompeiu
   representation** (the analogue of `trace_cfc_eq_plane_integral_resolvent` for
   `dbarNumOrder 6 f`), after which `norm_strip_integral_dbar_order_le` and
   `norm_far_integral_dbar_order_le` (`Probability/HigherExtension.lean`) supply the `O(N⁻²)`
   bound.  This is the one genuinely missing analytic input.
2. **The lower half-plane.**  The sharp comparison is proved in main only for `Im z > 0`, so the
   `N⁻²` far-region gain above is confined to the upper half-plane.  Extending it needs the
   conjugation/transpose symmetry `g_N(conj z) = conj (g_N(z)ᵀ)` of the GUE model (and the
   corresponding statement for the limit transform).
3. **Two integrability side conditions** (`hIntN`, `hIntLim` in the main theorem): the plane
   integrands `∂̄F · Tr_d(g_N)` and `∂̄F · Tr_d(g)` are integrable.  These are technical (they
   follow from continuity of `z ↦ Tr_d(g_N(z))` and `z ↦ Tr_d(g(z))`), not estimate content;
   `integrable_norm_dbarNum_zOf`, `integrable_norm_dbarNum_mul_inv_im_zOf` and
   `volume_im_eq_zero` provide the majorants used.
4. **The limit side.**  `guePlaneLimit A₀ A f` is the plane integral of `∂̄F` against the limit
   Fock resolvent trace; its identification with `τ_d(τ(f(h)))` for the block limit element `h`
   is `Probability/LimitHSRepresentation.lean` (`limitHSTraceRepresentation_of_contDiff`) plus
   the identification of the Fock pencil with the block limit element.

No `sorry`, no new axioms.
-/
import GUEStrongConvergence.Probability.LemmaMSmooth
import GUEStrongConvergence.Probability.DysonStabilityBound
import GUEStrongConvergence.Probability.HigherExtension

open MeasureTheory ProbabilityTheory Matrix Filter Topology Complex
open FreeProbability FreeProbability.Fock
open scoped Matrix.Norms.Frobenius ComplexOrder ENNReal NNReal Topology BigOperators

namespace GUEStrongConvergence

noncomputable section

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d] [DecidableEq ι] [Nonempty d]

/-! ## The trace is controlled by the Frobenius norm -/

/-- **Trace bound.**  `‖Tr M‖ ≤ card d · ‖M‖_F` for a `d × d` matrix. -/
lemma norm_trace_le_card_mul_frob (M : Matrix d d ℂ) :
    ‖Matrix.trace M‖ ≤ (Fintype.card d : ℝ) * frob M := by
  have htr : Matrix.trace M = ∑ i : d, M i i := rfl
  rw [htr]
  calc ‖∑ i : d, M i i‖ ≤ ∑ i : d, ‖M i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : d, frob M := Finset.sum_le_sum (fun i _ => norm_entry_le_frob M i i)
    _ = (Fintype.card d : ℝ) * frob M := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The trace of the averaged resolvent is bounded by `card d · M` under a mean-resolvent bound
`M`. -/
lemma norm_trace_gueResolventMean_le (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) {N : ℕ}
    {M : ℝ} (z : ℂ)
    (hg : frob (gueResolventMean (N := N) A₀ A z) ≤ M) :
    ‖Matrix.trace (gueResolventMean (N := N) A₀ A z)‖ ≤ (Fintype.card d : ℝ) * M :=
  (norm_trace_le_card_mul_frob _).trans
    (mul_le_mul_of_nonneg_left hg (by positivity))


/-! ## Rectangle data and integrability of the plane weights -/

section PlaneGeometry

variable {f : ℝ → ℝ}

/-- `∂̄F = dbarNum f` is supported in a rectangle of the plane. -/
lemma exists_rect_support_dbarNum (_hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ∃ (X Y : ℝ), 0 < X ∧ 0 < Y ∧ ∀ p : ℝ × ℝ,
      p ∉ Set.Icc (-X) X ×ˢ Set.Icc (-Y) Y → ‖dbarNum f (zOf p)‖ = 0 := by
  have hKc : IsCompact (tsupport (dbarNum f)) := hasCompactSupport_dbarNum hfc
  obtain ⟨X, hXpos, hX⟩ : ∃ X : ℝ, 0 < X ∧ ∀ z ∈ tsupport (dbarNum f), |z.re| < X := by
    have hKr : IsCompact (Complex.re '' tsupport (dbarNum f)) := hKc.image Complex.continuous_re
    obtain ⟨X₀, hX₀⟩ := hKr.exists_bound_of_continuousOn continuous_id.continuousOn
    refine ⟨max X₀ 0 + 1, by linarith [le_max_right X₀ 0], fun z hz => ?_⟩
    have h1 : ‖z.re‖ ≤ X₀ := hX₀ _ ⟨z, hz, rfl⟩
    have h2 : |z.re| ≤ X₀ := by simpa [Real.norm_eq_abs] using h1
    linarith [le_max_left X₀ 0]
  obtain ⟨Y, hYpos, hY⟩ : ∃ Y : ℝ, 0 < Y ∧ ∀ z ∈ tsupport (dbarNum f), |z.im| < Y := by
    have hKi : IsCompact (Complex.im '' tsupport (dbarNum f)) := hKc.image Complex.continuous_im
    obtain ⟨Y₀, hY₀⟩ := hKi.exists_bound_of_continuousOn continuous_id.continuousOn
    refine ⟨max Y₀ 0 + 1, by linarith [le_max_right Y₀ 0], fun z hz => ?_⟩
    have h1 : ‖z.im‖ ≤ Y₀ := hY₀ _ ⟨z, hz, rfl⟩
    have h2 : |z.im| ≤ Y₀ := by simpa [Real.norm_eq_abs] using h1
    linarith [le_max_left Y₀ 0]
  refine ⟨X, Y, hXpos, hYpos, fun p hp => ?_⟩
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
  rw [image_eq_zero_of_notMem_tsupport hznot, norm_zero]

/-- `∂̄F = dbarNum f` is bounded by `B` inside a rectangle and vanishes outside it. -/
lemma exists_rect_bound_dbarNum (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ∃ (X Y B : ℝ), 0 < X ∧ 0 < Y ∧ 0 ≤ B ∧
      ∀ p : ℝ × ℝ, ‖dbarNum f (zOf p)‖ ≤
        B * (Set.Icc (-X) X ×ˢ Set.Icc (-Y) Y).indicator (fun _ => (1 : ℝ)) p := by
  obtain ⟨X, Y, hXpos, hYpos, hsupp⟩ := exists_rect_support_dbarNum hf hfc
  obtain ⟨B, hB⟩ := exists_norm_dbarNum_le hf hfc
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  refine ⟨X, Y, B, hXpos, hYpos, hB0, fun p => ?_⟩
  by_cases hp : p ∈ Set.Icc (-X) X ×ˢ Set.Icc (-Y) Y
  · rw [Set.indicator_of_mem hp, mul_one]
    exact hB (zOf p)
  · rw [Set.indicator_of_notMem hp, mul_zero, hsupp p hp]

/-- A constant multiple of the indicator of a compact rectangle is integrable. -/
lemma integrable_rect_indicator (X Y C : ℝ) :
    Integrable (fun p : ℝ × ℝ =>
      C * (Set.Icc (-X) X ×ˢ Set.Icc (-Y) Y).indicator (fun _ => (1 : ℝ)) p)
      (volume : Measure (ℝ × ℝ)) := by
  have hKmeas : MeasurableSet (Set.Icc (-X) X ×ˢ Set.Icc (-Y) Y : Set (ℝ × ℝ)) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hKfin : (volume : Measure (ℝ × ℝ)) (Set.Icc (-X) X ×ˢ Set.Icc (-Y) Y) < ∞ :=
    (isCompact_Icc.prod isCompact_Icc).measure_lt_top
  have h1 : Integrable ((Set.Icc (-X) X ×ˢ Set.Icc (-Y) Y).indicator
      (fun _ => (1 : ℝ))) (volume : Measure (ℝ × ℝ)) := by
    rw [integrable_indicator_iff hKmeas]
    exact integrableOn_const hKfin.ne
  exact h1.const_mul C

/-- The plane weight `‖∂̄F(z)‖` is integrable. -/
lemma integrable_norm_dbarNum_zOf (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Integrable (fun p : ℝ × ℝ => ‖dbarNum f (zOf p)‖) (volume : Measure (ℝ × ℝ)) := by
  obtain ⟨X, Y, B, hXpos, hYpos, hB0, hB⟩ := exists_rect_bound_dbarNum hf hfc
  refine Integrable.mono' (integrable_rect_indicator X Y B)
    (((continuous_dbarNum hf).comp continuous_zOf).norm.aestronglyMeasurable)
    (Eventually.of_forall fun p => ?_)
  simpa using hB p

/-- The weighted plane integral `∫∫ ‖∂̄F(z)‖ |Im z|⁻¹` is finite: the linear vanishing of `∂̄F`
on the real axis makes the weight integrable. -/
lemma integrable_norm_dbarNum_mul_inv_im_zOf (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    Integrable (fun p : ℝ × ℝ => ‖dbarNum f (zOf p)‖ * |p.2|⁻¹)
      (volume : Measure (ℝ × ℝ)) := by
  obtain ⟨X, Y, hXpos, hYpos, hsupp⟩ := exists_rect_support_dbarNum hf hfc
  obtain ⟨B, hB⟩ := exists_norm_dbarNum_le hf hfc
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  obtain ⟨M₂, hM₂⟩ := exists_norm_deriv_deriv_le hf hfc
  have hM₂0 : 0 ≤ M₂ := le_trans (norm_nonneg _) (hM₂ 0)
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => ‖dbarNum f (zOf p)‖ * |p.2|⁻¹)
      (volume : Measure (ℝ × ℝ)) :=
    (((continuous_dbarNum hf).comp continuous_zOf).norm.measurable.mul
      ((continuous_abs.comp continuous_snd).measurable.inv)).aestronglyMeasurable
  refine Integrable.mono' (integrable_rect_indicator X Y (max M₂ B)) hmeas
    (Eventually.of_forall fun p => ?_)
  show ‖‖dbarNum f (zOf p)‖ * |p.2|⁻¹‖ ≤
    max M₂ B * (Set.Icc (-X) X ×ˢ Set.Icc (-Y) Y).indicator (fun _ => (1 : ℝ)) p
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  by_cases hp : p ∈ Set.Icc (-X) X ×ˢ Set.Icc (-Y) Y
  · rw [Set.indicator_of_mem hp, mul_one]
    rcases eq_or_ne p.2 0 with h0 | h0
    · rw [h0]
      simp only [abs_zero]
      rw [_root_.inv_zero, mul_zero]
      exact le_trans hB0 (le_max_right _ _)
    · have hpos : 0 < |p.2| := abs_pos.mpr h0
      rcases lt_or_ge |p.2| 1 with h1 | h1
      · have hlin := norm_dbar_almostAnalyticExtCut_le (f := f) hf (z := zOf p)
          (by rw [zOf_im]; exact h1) hM₂
        rw [zOf_im] at hlin
        calc ‖dbarNum f (zOf p)‖ * |p.2|⁻¹ ≤ (|p.2| * M₂) * |p.2|⁻¹ := by
              exact mul_le_mul_of_nonneg_right hlin (by positivity)
          _ = M₂ := by field_simp
          _ ≤ max M₂ B := le_max_left _ _
      · calc ‖dbarNum f (zOf p)‖ * |p.2|⁻¹ ≤ B * |p.2|⁻¹ :=
              mul_le_mul_of_nonneg_right (hB (zOf p)) (by positivity)
          _ ≤ B * 1 := by
              refine mul_le_mul_of_nonneg_left ?_ hB0
              exact inv_le_one_of_one_le₀ h1
          _ = B := mul_one B
          _ ≤ max M₂ B := le_max_right _ _
  · rw [Set.indicator_of_notMem hp, mul_zero, hsupp p hp]
    simp

/-- The set of points of the plane with vanishing imaginary part is null. -/
lemma volume_im_eq_zero : (volume : Measure (ℝ × ℝ)) {p : ℝ × ℝ | p.2 = 0} = 0 := by
  have h1 : {p : ℝ × ℝ | p.2 = 0} = Set.univ ×ˢ ({0} : Set ℝ) := by
    ext p; simp
  rw [h1]
  change ((volume : Measure ℝ).prod (volume : Measure ℝ)) (Set.univ ×ˢ ({0} : Set ℝ)) = 0
  rw [Measure.prod_prod]
  simp

end PlaneGeometry

/-- The real part of `n • z` for a natural `n`. -/
lemma natCast_mul_re (n : ℕ) (z : ℂ) : ((n : ℂ) * z).re = (n : ℝ) * z.re := by
  rw [Complex.mul_re]
  simp

/-! ## The mean as a normalized plane integral -/

section PlaneIdentity

variable {N : ℕ}

/-- **Lemma M, smooth form, in the normalization of the limit statistic.**

The mean of `τ_N(f(H_N))` is `(card d)⁻¹` times the real part of the plane integral of `∂̄F`
against the trace of the averaged partial-trace resolvent `g_N`; this removes both `gueNormConst`
and the factor `N` of `integral_gueStatisticCfc_eq_plane_integral`. -/
theorem integral_gueStatisticCfc_eq_plane_integral' (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (hN : 0 < N) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), gueStatisticCfc (N := N) f A₀ A hA₀ hA x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      = (Fintype.card d : ℝ)⁻¹ *
          ((I / (2 * (Real.pi : ℂ))) *
            ∫ p : ℝ × ℝ, dbarNum f (zOf p) *
              Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p))).re := by
  rw [integral_gueStatisticCfc_eq_plane_integral A₀ A hA₀ hA hN hf hfc]
  have hInt : (∫ p : ℝ × ℝ, dbarNum f (zOf p) *
        ((N : ℂ) * Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p))))
      = (N : ℂ) * ∫ p : ℝ × ℝ, dbarNum f (zOf p) *
          Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p)) := by
    have h1 : ∀ p : ℝ × ℝ, dbarNum f (zOf p) *
        ((N : ℂ) * Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p)))
        = (N : ℂ) * (dbarNum f (zOf p) *
            Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p))) := fun p => by ring
    simp_rw [h1]
    exact integral_const_mul _ _
  rw [hInt]
  have hcomm : (I / (2 * (Real.pi : ℂ))) *
      ((N : ℂ) * ∫ p : ℝ × ℝ, dbarNum f (zOf p) *
        Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p)))
      = (N : ℂ) * ((I / (2 * (Real.pi : ℂ))) *
        ∫ p : ℝ × ℝ, dbarNum f (zOf p) *
          Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p))) := by ring
  rw [hcomm, natCast_mul_re]
  -- the normalization constants
  have hcard : (Fintype.card d : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hnorm : gueNormConst d N * ((N : ℝ) *
      ((I / (2 * (Real.pi : ℂ))) *
      ∫ p : ℝ × ℝ, dbarNum f (zOf p) *
        Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p))).re)
      = (Fintype.card d : ℝ)⁻¹ * ((I / (2 * (Real.pi : ℂ))) *
      ∫ p : ℝ × ℝ, dbarNum f (zOf p) *
        Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p))).re := by
    rw [gueNormConst]
    have hcast : (((Fintype.card d * N : ℕ)) : ℝ) = (Fintype.card d : ℝ) * (N : ℝ) := by
      push_cast
      ring
    rw [hcast]
    field_simp
  exact hnorm

/-- **The mean is uniformly bounded by the mean-resolvent bound.**

If the averaged resolvent is bounded by `M` in Frobenius norm at every nonreal `z`, then
`|E τ_N(f(H_N))| ≤ M/(2π) · ∫∫ ‖∂̄F‖` for every `N`.  This is the crudest consequence of the
mean-resolvent hypothesis; the point of the present file is the *sharper* decomposition
`smooth_trace_comparison_of_mean_bound` below. -/
theorem abs_integral_gueStatisticCfc_le_of_mean_bound (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (hN : 0 < N) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {M : ℝ}
    (hgN : ∀ (N' : ℕ) (z : ℂ), z.im ≠ 0 →
      frob (gueResolventMean (N := N') A₀ A z) ≤ M) :
    |∫ x : EuclideanSpace ℝ (GUECoord ι N), gueStatisticCfc (N := N) f A₀ A hA₀ hA x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))|
      ≤ M / (2 * Real.pi) * ∫ p : ℝ × ℝ, ‖dbarNum f (zOf p)‖ := by
  rw [integral_gueStatisticCfc_eq_plane_integral' A₀ A hA₀ hA hN hf hfc]
  set Af : ℝ := ∫ p : ℝ × ℝ, ‖dbarNum f (zOf p)‖ with hAf
  have hAf0 : 0 ≤ Af := integral_nonneg (fun p => norm_nonneg _)
  have hcard0 : (0 : ℝ) < (Fintype.card d : ℝ) := by
    have := Fintype.card_ne_zero (α := d)
    positivity
  have hInt : ‖∫ p : ℝ × ℝ, dbarNum f (zOf p) *
      Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p))‖
      ≤ ∫ p : ℝ × ℝ, ‖dbarNum f (zOf p)‖ * ((Fintype.card d : ℝ) * M) := by
    refine norm_integral_le_of_norm_le (g := fun p : ℝ × ℝ =>
      ‖dbarNum f (zOf p)‖ * ((Fintype.card d : ℝ) * M)) ?_ ?_
    · exact (integrable_norm_dbarNum_zOf hf hfc).mul_const _
    · filter_upwards [(compl_mem_ae_iff).mpr volume_im_eq_zero] with p hp
      have hz : (zOf p).im ≠ 0 := by rwa [zOf_im]
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (norm_trace_gueResolventMean_le A₀ A (zOf p) (hgN N (zOf p) hz)) (norm_nonneg _)
  have hInt' : (∫ p : ℝ × ℝ, ‖dbarNum f (zOf p)‖ * ((Fintype.card d : ℝ) * M))
      = ((Fintype.card d : ℝ) * M) * Af := by
    rw [hAf, integral_mul_const]
    ring
  have hnormW : ‖(I / (2 * (Real.pi : ℂ))) * ∫ p : ℝ × ℝ, dbarNum f (zOf p) *
      Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p))‖
      ≤ (2 * Real.pi)⁻¹ * (((Fintype.card d : ℝ) * M) * Af) := by
    have hc : ‖(I : ℂ) / (2 * (Real.pi : ℂ))‖ = (2 * Real.pi)⁻¹ := by
      rw [norm_div, Complex.norm_I]
      have h2 : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
        rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) from by push_cast; ring]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [h2, one_div]
    rw [norm_mul, hc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← hInt']
    exact hInt
  calc |(Fintype.card d : ℝ)⁻¹ * ((I / (2 * (Real.pi : ℂ))) *
        ∫ p : ℝ × ℝ, dbarNum f (zOf p) *
          Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p))).re|
      ≤ (Fintype.card d : ℝ)⁻¹ * ‖(I / (2 * (Real.pi : ℂ))) *
          ∫ p : ℝ × ℝ, dbarNum f (zOf p) *
            Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p))‖ := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (Fintype.card d : ℝ)⁻¹)]
        exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by positivity)
    _ ≤ (Fintype.card d : ℝ)⁻¹ * ((2 * Real.pi)⁻¹ * (((Fintype.card d : ℝ) * M) * Af)) := by
        exact mul_le_mul_of_nonneg_left hnormW (by positivity)
    _ = M / (2 * Real.pi) * Af := by
        have hcard : (Fintype.card d : ℝ) ≠ 0 := ne_of_gt hcard0
        field_simp

end PlaneIdentity

/-! ## Both half-planes: the deterministic averaged-resolvent bound -/

section BothHalfPlanes

variable {N : ℕ}

/-- Frobenius bound for the finite-`N` average, valid in **both** half-planes (the statement of
`frob_gueResolventMean_le` is restricted to `0 < Im z`). -/
theorem frob_gueResolventMean_le_abs (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (z : ℂ) (hz : z.im ≠ 0)
    (hN : 0 < N) :
    frob (gueResolventMean (N := N) A₀ A z) ≤ (Fintype.card d : ℝ) * |z.im|⁻¹ := by
  refine frob_le_card_mul_of_entry_le _ (fun u v => ?_) (by positivity)
  rw [gueResolventMean_apply]
  calc ‖∫ x, guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))‖
      ≤ ∫ x, ‖guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v‖
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ _x, |z.im|⁻¹ ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
        refine integral_mono ?_ (integrable_const _) (fun x => ?_)
        · exact (integrable_guePartialTrace_entry_gen A₀ A hA₀ hA z hz hN u v).norm
        · exact norm_guePartialTrace_entry_le A₀ A hA₀ hA _ z hz hN u v
    _ = |z.im|⁻¹ := by simp

end BothHalfPlanes

/-! ## The sharp weighted comparison under the mean-resolvent bound -/

section SharpComparison

variable {N : ℕ}

/-- Simplification of the `|Im z|⁻⁴` weight of the sharp comparison off the unit strip. -/
lemma sharp_weight_le (N : ℕ) (hN : 0 < N) {S t : ℝ} (hS : 0 ≤ S) (ht0 : 0 < t)
    (ht1 : 1 ≤ t) :
    2 * (gueScale N) ^ 2 * S * (t⁻¹) ^ 4 / (N : ℝ) ≤ 2 * S / (N : ℝ) ^ 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hk : (t⁻¹) ^ 4 ≤ 1 := by
    have h1 : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht1
    have h0 : 0 ≤ t⁻¹ := le_of_lt (inv_pos.mpr ht0)
    calc (t⁻¹) ^ 4 ≤ 1 ^ 4 := pow_le_pow_left₀ h0 h1 4
      _ = 1 := one_pow 4
  rw [gueScale_sq N]
  have hkey : 2 * (N : ℝ)⁻¹ * S * (t⁻¹) ^ 4 / (N : ℝ) = (2 * S / (N : ℝ) ^ 2) * (t⁻¹) ^ 4 := by
    field_simp
  rw [hkey]
  calc (2 * S / (N : ℝ) ^ 2) * (t⁻¹) ^ 4 ≤ (2 * S / (N : ℝ) ^ 2) * 1 := by
        refine mul_le_mul_of_nonneg_left hk ?_
        positivity
    _ = 2 * S / (N : ℝ) ^ 2 := mul_one _

/-- **Pointwise sharp comparison under the mean-resolvent hypothesis.**

Off the strip `Im z < η₀` (with `η₀ ≥ 1` and `card d ≤ M η₀`) the mean-resolvent bound `M`
gives the sharp `O(N⁻² |Im z|⁻⁴)` comparison; on the strip only the deterministic bound
`M + card d |Im z|⁻¹` is available. -/
theorem frob_sub_pencilCauchy_le_of_mean_bound (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (hN : 0 < N) {M η₀ : ℝ}
    (hM0 : 0 ≤ M) (hη₀1 : 1 ≤ η₀)
    (hη : 2 * M ^ 2 * (∑ i, (frob (A i)) ^ 2) ≤ 1)
    (hMd : (Fintype.card d : ℝ) ≤ M * η₀)
    (hgN : ∀ (N' : ℕ) (z : ℂ), z.im ≠ 0 →
      frob (gueResolventMean (N := N') A₀ A z) ≤ M)
    {z : ℂ} (hz : z.im ≠ 0) :
    frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
      ≤ (if η₀ ≤ z.im then
            2 * M * (Fintype.card d : ℝ) *
              (2 * (Fintype.card d : ℝ) ^ 2 * Real.sqrt (Fintype.card d : ℝ) *
                (∑ i, (frob (A i)) ^ 2) * (2 * (∑ i, (frob (A i)) ^ 2))) / (N : ℝ) ^ 2
          else 0)
        + (M + (Fintype.card d : ℝ) * |z.im|⁻¹) := by
  have htriv : frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
      ≤ M + (Fintype.card d : ℝ) * |z.im|⁻¹ := by
    refine (frob_sub_le _ _).trans ?_
    exact add_le_add (hgN N z hz) (frob_operatorMatrixPencilCauchy_le A₀ A hA₀ hA z hz)
  by_cases hy : η₀ ≤ z.im
  · rw [if_pos hy]
    have hzpos : 0 < z.im := lt_of_lt_of_le (by linarith) hy
    have hgb : frob (operatorMatrixPencilCauchy A₀ A z) ≤ M := by
      refine (frob_operatorMatrixPencilCauchy_le A₀ A hA₀ hA z (ne_of_gt hzpos)).trans ?_
      rw [abs_of_pos hzpos]
      calc (Fintype.card d : ℝ) * (z.im)⁻¹ ≤ (Fintype.card d : ℝ) * η₀⁻¹ := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            simpa [one_div] using one_div_le_one_div_of_le (by linarith : (0:ℝ) < η₀) hy
        _ ≤ M := by
            have h := mul_le_mul_of_nonneg_right hMd
              (inv_nonneg.mpr (by linarith : (0 : ℝ) ≤ η₀))
            rw [mul_assoc, mul_inv_cancel₀ (by linarith : η₀ ≠ 0), mul_one] at h
            exact h
    have hsharp := frob_gueResolventMean_sub_limit_le_sharp_of_bound A₀ A hA₀ hA z hzpos hN
      hM0 (hgN N z (ne_of_gt hzpos)) hgb hη
    refine hsharp.trans ?_
    have hSnn : (0 : ℝ) ≤ ∑ i, (frob (A i)) ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hk := sharp_weight_le N hN hSnn hzpos (le_trans hη₀1 hy)
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hKsharp : 2 * M * ((Fintype.card d : ℝ) *
          (2 * (Fintype.card d : ℝ) ^ 2 * Real.sqrt (Fintype.card d : ℝ) *
            (∑ i, (frob (A i)) ^ 2) *
            (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4 / (N : ℝ))))
        = 2 * M * (Fintype.card d : ℝ) *
            (2 * (Fintype.card d : ℝ) ^ 2 * Real.sqrt (Fintype.card d : ℝ) *
              (∑ i, (frob (A i)) ^ 2) *
              (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4 / (N : ℝ))) := by
      ring
    rw [hKsharp]
    have hstep : 2 * M * (Fintype.card d : ℝ) *
          (2 * (Fintype.card d : ℝ) ^ 2 * Real.sqrt (Fintype.card d : ℝ) *
            (∑ i, (frob (A i)) ^ 2) *
            (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4 / (N : ℝ)))
        ≤ 2 * M * (Fintype.card d : ℝ) *
            (2 * (Fintype.card d : ℝ) ^ 2 * Real.sqrt (Fintype.card d : ℝ) *
              (∑ i, (frob (A i)) ^ 2) * (2 * (∑ i, (frob (A i)) ^ 2) / (N : ℝ) ^ 2)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact hk
    refine hstep.trans ?_
    have heq : 2 * M * (Fintype.card d : ℝ) *
          (2 * (Fintype.card d : ℝ) ^ 2 * Real.sqrt (Fintype.card d : ℝ) *
            (∑ i, (frob (A i)) ^ 2) * (2 * (∑ i, (frob (A i)) ^ 2) / (N : ℝ) ^ 2))
        = 2 * M * (Fintype.card d : ℝ) *
            (2 * (Fintype.card d : ℝ) ^ 2 * Real.sqrt (Fintype.card d : ℝ) *
              (∑ i, (frob (A i)) ^ 2) * (2 * (∑ i, (frob (A i)) ^ 2))) / (N : ℝ) ^ 2 := by
      field_simp
    rw [heq]
    exact le_add_of_nonneg_right (by positivity)
  · rw [if_neg hy]
    simpa using htriv

end SharpComparison

/-! ## The limit plane integral and Lemma M under a mean-resolvent bound -/

section MainTheorem

variable {N : ℕ}

/-- The limit statistic in plane-integral form:
`(card d)⁻¹ Re ((I/2π) ∫∫ ∂̄F(z) · Tr_d(g(z)))` with `g = operatorMatrixPencilCauchy A₀ A` the
limit Cauchy transform.  This is the object that Lemma M compares the mean with (its identity
with `τ_d(τ(f(h)))` for the limit element `h` is the limit-side representation
`limitHSTraceRepresentation_of_contDiff` together with the identification of the Fock pencil with
the block limit element). -/
def guePlaneLimit (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (f : ℝ → ℝ) : ℝ :=
  (Fintype.card d : ℝ)⁻¹ * ((I / (2 * (Real.pi : ℂ))) *
    ∫ p : ℝ × ℝ, dbarNum f (zOf p) *
      Matrix.trace (operatorMatrixPencilCauchy A₀ A (zOf p))).re

/-- **Lemma M, smooth form, under a mean-resolvent bound.**

Assume `frob (gueResolventMean A₀ A z) ≤ M` for every nonreal `z` (the single missing *a priori*
input, an exactly typed hypothesis), together with the companion condition
`2 M² ∑ ‖A_i‖² ≤ 1` and the geometric conditions `η₀ ≥ 1`, `card d ≤ M η₀` (so that the
deterministic bound `card d / |Im z| ≤ M` for the limit resolvent holds off the strip).  Then,
for every `N ≥ 1`,

`|E τ_N(f(H_N)) − guePlaneLimit| ≤ (2π card d)⁻¹ ∫∫ ‖∂̄F‖ (C_far/N² + card d M + (card d)² |Im z|⁻¹)`

with `C_far = 2 M card d (2 (card d)² √(card d) (∑‖A_i‖²)) (2 ∑‖A_i‖²)`.  The `C_far/N²` term is
the sharp contribution of the region `Im z ≥ η₀`; the remaining `card d M + (card d)²|Im z|⁻¹`
is the contribution of the strip, where only the deterministic resolvent bound is available. -/
theorem smooth_trace_comparison_of_mean_bound (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (hN : 0 < N) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {M η₀ : ℝ}
    (hM0 : 0 ≤ M) (hη₀1 : 1 ≤ η₀)
    (hη : 2 * M ^ 2 * (∑ i, (frob (A i)) ^ 2) ≤ 1)
    (hMd : (Fintype.card d : ℝ) ≤ M * η₀)
    (hgN : ∀ (N' : ℕ) (z : ℂ), z.im ≠ 0 →
      frob (gueResolventMean (N := N') A₀ A z) ≤ M)
    (hIntN : Integrable (fun p : ℝ × ℝ => dbarNum f (zOf p) *
      Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p))))
    (hIntLim : Integrable (fun p : ℝ × ℝ => dbarNum f (zOf p) *
      Matrix.trace (operatorMatrixPencilCauchy A₀ A (zOf p)))) :
    |∫ x : EuclideanSpace ℝ (GUECoord ι N), gueStatisticCfc (N := N) f A₀ A hA₀ hA x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) - guePlaneLimit A₀ A f|
      ≤ (2 * Real.pi)⁻¹ *
          ∫ p : ℝ × ℝ, ‖dbarNum f (zOf p)‖ *
            (2 * M * (Fintype.card d : ℝ) *
                (2 * (Fintype.card d : ℝ) ^ 2 * Real.sqrt (Fintype.card d : ℝ) *
                  (∑ i, (frob (A i)) ^ 2) * (2 * (∑ i, (frob (A i)) ^ 2))) / (N : ℝ) ^ 2
              + M + (Fintype.card d : ℝ) * |p.2|⁻¹) := by
  classical
  rw [integral_gueStatisticCfc_eq_plane_integral' A₀ A hA₀ hA hN hf hfc, guePlaneLimit]
  set c : ℝ := (Fintype.card d : ℝ) with hc
  set K : ℝ := 2 * c ^ 2 * Real.sqrt c * (∑ i, (frob (A i)) ^ 2) *
    (2 * (∑ i, (frob (A i)) ^ 2)) with hK
  set Cf : ℝ := 2 * M * c * K with hCf
  have hc0 : (0 : ℝ) ≤ c := by positivity
  have hS0 : (0 : ℝ) ≤ ∑ i, (frob (A i)) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hCf0 : 0 ≤ Cf := by rw [hCf]; positivity
  set W : ℝ × ℝ → ℝ := fun p => Cf / (N : ℝ) ^ 2 + M + c * |p.2|⁻¹ with hW
  have hW0 : ∀ p, 0 ≤ W p := by
    intro p; rw [hW]; positivity
  -- the difference of the two plane integrals as a single integral
  set Ai : ℂ := ∫ p : ℝ × ℝ, dbarNum f (zOf p) *
    Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p)) with hAi
  set Bi : ℂ := ∫ p : ℝ × ℝ, dbarNum f (zOf p) *
    Matrix.trace (operatorMatrixPencilCauchy A₀ A (zOf p)) with hBi
  set Di : ℂ := ∫ p : ℝ × ℝ, dbarNum f (zOf p) *
    Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p) - operatorMatrixPencilCauchy A₀ A (zOf p))
    with hDi
  have hAB : Ai - Bi = Di := by
    rw [hAi, hBi, hDi, ← integral_sub hIntN hIntLim]
    congr 1
    ext p
    rw [Matrix.trace_sub]
    ring
  -- integrability of the weights
  have hWmeas : Measurable (fun p : ℝ × ℝ => Cf / (N : ℝ) ^ 2 + M + c * |p.2|⁻¹) := by
    refine Measurable.add (Measurable.add measurable_const measurable_const) ?_
    have hcont : Continuous fun p : ℝ × ℝ => |p.2| :=
      continuous_abs.comp (continuous_snd : Continuous fun p : ℝ × ℝ => p.2)
    exact hcont.measurable.inv.const_mul c
  have hWint : Integrable (fun p : ℝ × ℝ => ‖dbarNum f (zOf p)‖ * W p)
      (volume : Measure (ℝ × ℝ)) := by
    have hC0 : (0 : ℝ) ≤ Cf / (N : ℝ) ^ 2 + M + c := by positivity
    refine Integrable.mono' (((integrable_norm_dbarNum_zOf hf hfc).add
      (integrable_norm_dbarNum_mul_inv_im_zOf hf hfc)).mul_const
        (Cf / (N : ℝ) ^ 2 + M + c)) ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact ((continuous_dbarNum hf).comp continuous_zOf).norm.measurable.mul hWmeas |>.aestronglyMeasurable
    · rw [hW]
      show ‖‖dbarNum f (zOf p)‖ * (Cf / (N : ℝ) ^ 2 + M + c * |p.2|⁻¹)‖ ≤
        (‖dbarNum f (zOf p)‖ + ‖dbarNum f (zOf p)‖ * |p.2|⁻¹) * (Cf / (N : ℝ) ^ 2 + M + c)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hinv : |p.2|⁻¹ ≤ 1 + |p.2|⁻¹ := by linarith [inv_nonneg.mpr (abs_nonneg p.2)]
      have hWy : Cf / (N : ℝ) ^ 2 + M + c * |p.2|⁻¹
          ≤ (Cf / (N : ℝ) ^ 2 + M + c) * (1 + |p.2|⁻¹) := by
        have h1 : c ≤ Cf / (N : ℝ) ^ 2 + M + c := by
          have := div_nonneg hCf0 (by positivity : (0:ℝ) ≤ (N:ℝ)^2)
          linarith
        have h2 : 0 ≤ |p.2|⁻¹ := inv_nonneg.mpr (abs_nonneg _)
        nlinarith [mul_le_mul_of_nonneg_right h1 h2, hC0, hc0]
      calc ‖dbarNum f (zOf p)‖ * W p
          ≤ ‖dbarNum f (zOf p)‖ * ((Cf / (N : ℝ) ^ 2 + M + c) * (1 + |p.2|⁻¹)) :=
            mul_le_mul_of_nonneg_left hWy (norm_nonneg _)
        _ = (‖dbarNum f (zOf p)‖ + ‖dbarNum f (zOf p)‖ * |p.2|⁻¹) *
              (Cf / (N : ℝ) ^ 2 + M + c) := by ring
  -- the norm bound on the resolvent difference
  have hbd : ‖Di‖ ≤ c * ∫ p : ℝ × ℝ, ‖dbarNum f (zOf p)‖ * W p := by
    rw [hDi]
    have hmaj : Integrable (fun p : ℝ × ℝ => (‖dbarNum f (zOf p)‖ * W p) * c)
        (volume : Measure (ℝ × ℝ)) := hWint.mul_const c
    refine (norm_integral_le_of_norm_le hmaj ?_).trans ?_
    · filter_upwards [(compl_mem_ae_iff).mpr volume_im_eq_zero] with p hp
      have hz : (zOf p).im ≠ 0 := by rwa [zOf_im]
      rw [norm_mul]
      have hcmp := frob_sub_pencilCauchy_le_of_mean_bound A₀ A hA₀ hA hN hM0 hη₀1 hη hMd hgN hz
      have hbound : frob (gueResolventMean (N := N) A₀ A (zOf p) -
          operatorMatrixPencilCauchy A₀ A (zOf p)) ≤ W p := by
        have h1 : (if η₀ ≤ p.2 then
            2 * M * c * K / (N : ℝ) ^ 2 else 0) ≤ Cf / (N : ℝ) ^ 2 := by
          split_ifs with h
          · rw [hCf]
          · exact div_nonneg hCf0 (by positivity)
        rw [zOf_im] at hcmp
        rw [hW, hc]
        linarith
      calc ‖dbarNum f (zOf p)‖ * ‖Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p) -
            operatorMatrixPencilCauchy A₀ A (zOf p))‖
          ≤ ‖dbarNum f (zOf p)‖ * (c * W p) := by
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            refine (norm_trace_le_card_mul_frob _).trans ?_
            exact mul_le_mul_of_nonneg_left hbound hc0
        _ = (‖dbarNum f (zOf p)‖ * W p) * c := by ring
    · rw [integral_mul_const]
      exact le_of_eq (by ring)
  -- assemble the constants
  have hre : (I / (2 * (Real.pi : ℂ)) * Ai).re - (I / (2 * (Real.pi : ℂ)) * Bi).re
      = (I / (2 * (Real.pi : ℂ)) * Di).re := by
    rw [← Complex.sub_re, ← mul_sub, hAB]
  have hnorm : ‖(I / (2 * (Real.pi : ℂ))) * Di‖ = (2 * Real.pi)⁻¹ * ‖Di‖ := by
    rw [norm_mul]
    congr 1
    rw [norm_div, Complex.norm_I]
    have h2 : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
      rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) from by push_cast; ring]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [h2, one_div]
  calc |c⁻¹ * (I / (2 * (Real.pi : ℂ)) * Ai).re - c⁻¹ * (I / (2 * (Real.pi : ℂ)) * Bi).re|
      = c⁻¹ * |(I / (2 * (Real.pi : ℂ)) * Di).re| := by
        rw [← mul_sub, ← hre, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < c⁻¹)]
    _ ≤ c⁻¹ * ‖(I / (2 * (Real.pi : ℂ))) * Di‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by positivity)
    _ = c⁻¹ * ((2 * Real.pi)⁻¹ * ‖Di‖) := by rw [hnorm]
    _ ≤ c⁻¹ * ((2 * Real.pi)⁻¹ * (c * ∫ p : ℝ × ℝ, ‖dbarNum f (zOf p)‖ * W p)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hbd (by positivity)
    _ = (2 * Real.pi)⁻¹ * ∫ p : ℝ × ℝ, ‖dbarNum f (zOf p)‖ *
          (2 * M * c * (2 * c ^ 2 * Real.sqrt c * (∑ i, (frob (A i)) ^ 2) *
              (2 * (∑ i, (frob (A i)) ^ 2))) / (N : ℝ) ^ 2 + M + c * |p.2|⁻¹) := by
        rw [hW, hCf, hK]
        have hcne : c ≠ 0 := by
          rw [hc]
          exact_mod_cast Fintype.card_ne_zero (α := d)
        field_simp

end MainTheorem

end

end GUEStrongConvergence
