/-
# Lemma M from a weighted resolvent strip estimate

The order-`k` mean comparison `smooth_trace_comparison_of_mean_bound_order`
(`Probability/PompeiuOrderK.lean`) bounds the discrepancy
`|E τ_N(f(H_N)) − guePlaneLimitOrder k A₀ A f|` by the plane integral

`(2π)⁻¹ ∫∫ ‖∂̄_k f(z)‖ (C_far/N² + M + card d |Im z|⁻¹)`.

The `M + card d |Im z|⁻¹` term is *not* `O(N⁻²)`: it is the crude deterministic resolvent
bound, and integrating it against `‖∂̄_k f‖` gives an `N`-independent constant.  This file
closes that last step **under the single missing analytic input**: a weighted bound on the
resolvent difference on the strip where `∂̄_k f` lives,

`frob (g_N(z) − g(z)) ≤ C_s |Im z|^(−β) / N²`  for `|Im z| < η₀`, with `β < k`.

Because `∂̄_k f` is supported in `|Im z| ≤ 2` (`yCut` vanishes for `|Im z| ≥ 2`), the choice
`η₀ > 2` makes the far region (`|Im z| ≥ η₀`) contribute *exactly zero*, so the weighted strip
estimate controls the whole plane integral.  Then

`|E τ_N(f(H_N)) − guePlaneLimitOrder k A₀ A f| ≤ (2π)⁻¹ C_s (∫∫ ‖∂̄_k f‖ |Im z|^(−β)) / N²`,

a single explicit finite constant (the integral is finite because `β < k` kills the
singularity at `Im z = 0`).

Note that no uniform mean-resolvent bound (`frob g_N ≤ M`), no stability condition
`2 M² ∑‖A_i‖² ≤ 1` and no geometric condition `card d ≤ M η₀` are needed: the weighted strip
estimate replaces all of them.  This is why the result below is stated with fewer hypotheses
than `smooth_trace_comparison_of_mean_bound_order`.

## Main results

* `WeightedStripBound` — the precise weighted strip hypothesis (eventual in `N`);
* `integrable_norm_dbarNumOrder_mul_rpow_neg` — `‖∂̄_k f(z)‖ |Im z|^(−β)` is integrable for
  `0 ≤ β < k` (the exponent threshold that makes the constant finite);
* `dbarNumOrder_eq_zero_of_two_lt_abs_im` — `∂̄_k f` vanishes off `|Im z| ≤ 2`;
* **`smooth_trace_comparison_of_weighted_strip`** — the pure `O(N⁻²)` comparison at a fixed
  `N`, from the strip hypothesis at that `N`;
* **`eventually_smooth_trace_comparison_of_weighted_strip`** — the same, in the eventual form
  consumed by `FlatLemmaM`;
* **`abs_integral_gueStatisticCfc_le_of_weighted_strip`** — the pure `O(N⁻²)` bound for the mean
  itself, when the limit statistic vanishes (the `hWb` shape).

## Packaging, and the exact remaining gap

The second half of the file packages the corollary into the downstream interface.

* `weightedStripConstant f k C_s β = (2π)⁻¹ C_s ∫∫ ‖∂̄_k f‖ |Im z|^(−β)` is the explicit finite
  constant (finite for `β < k`);
* `eventually_abs_integral_gueStatisticCfc_le_of_weighted_strip` is the `hWb` shape (mean bound
  when the limit statistic vanishes);
* `IsSmoothCutoffZeroOn` is `IsSmoothCutoff` *plus* `f = 0` and `f' = 0` on the target set —
  the two properties that `IsSmoothCutoff` drops but `exists_contDiff_two_cutoff` provides.
  They are what makes the limit statistics of `f` and `(f')²` vanish;
* `hWb_of_flatLemmaM_deriv` is the bookkeeping step `|mean| ≤ C/N² ⇒ mean ≤ C/N²`;
* `flatLemmaM_of_weightedStrip` derives `FlatLemmaM` from `WeightedStripBound` (at block
  `N + 1`) — but only given two **explicit identification hypotheses**:
  - `hstat : ∀ N, ∫ flatStat r k F z N g = ∫ gueStatisticCfc (N := N+1) g A₀ A hA₀ hA`
    (the flat statistic is the GUE statistic of the realisation `(A₀, A)`);
  - `hlim0 : guePlaneLimitOrder k A₀ A g = 0` (the limit statistic vanishes; follows from
    `g = 0` on the limit spectrum through the limit-side representation).

  Neither is available on main.  `hstat` is the integrated form of the **flat ⟶ GUE
  identification** (`FlatGUEStatisticEq` below), a Kronecker/reindexing identity — bookkeeping,
  not analysis, but not present in the repository.  `hlim0` needs the identification of
  `guePlaneLimitOrder` with `τ(g(h))`, also not packaged on main.
* `PencilLemmaSResidual_of_weightedStrip`, `PencilLemmaSData_of_weightedStrip` assemble the
  residual bundle from the two mean comparisons (using `f` and `(f')²`);
* `WeightedMeanInputs` is the all-`k` `FlatLemmaM` footprint; `PencilLemmaSResidualInputs`,
  `PencilLemmaSInputs` and finally
  `GUEStrongConvergenceStatement_of_weightedMeanInputs : ScalarSpectralInclusion r →
  WeightedMeanInputs r → GUEStrongConvergenceStatement r` are the downstream chain;
* `FlatGUEStatisticEq` records the precise missing identification;
* `WeightedStripDataAt r k F z ε` (for `1 ≤ k`) bundles the strengthened cutoff, the GUE
  realisation, `WeightedStripBound`, the two vanishing statements and the four integrability
  side conditions;
* `WeightedStripInputs r` is the honest conditional input bundle: `WeightedStripDataAt` for
  every `1 ≤ k`, **plus** a separate `k = 0` first-order mean-comparison footprint (the
  order-`k` Cauchy--Pompeiu identity needs `1 ≤ k`, and `WeightedStripBound` with `β < 0` is
  impossible, so `k = 0` cannot be produced by the same mechanism);
* **`GUEStrongConvergenceStatement_of_weightedStripInputs :
  ScalarSpectralInclusion r → WeightedStripInputs r → GUEStrongConvergenceStatement r`** — the
  final conditional theorem.  Its hypotheses are exactly `ScalarSpectralInclusion r` and the
  explicit bundle `WeightedStripInputs r`; the weighted strip bounds enter through
  `WeightedStripBound`, and the extra hypotheses are the typed identifications recorded in
  `FlatGUEStatisticEq` / the vanishing statements / the `k = 0` first-order footprint.
  This is a genuine **reduction**, not a proof of Lemma M: the identification hypotheses are
  not derived here.

No `sorry`, no new axioms.
-/
import GUEStrongConvergence.Probability.PompeiuOrderK
import GUEStrongConvergence.StrongConvergence.FlatHVField
import GUEStrongConvergence.StrongConvergence.FlattenPencil
import GUEStrongConvergence.StrongConvergence.CutoffExclusion

open MeasureTheory ProbabilityTheory Matrix Filter Topology Complex
open FreeProbability FreeProbability.Fock
open scoped Matrix.Norms.Frobenius ComplexOrder ENNReal NNReal Topology BigOperators

namespace GUEStrongConvergence

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 10000000

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] [Nonempty d]
  {N : ℕ}

/-! ## The weighted strip hypothesis -/

/-- **The weighted strip bound.**  For all sufficiently large `N` and every nonreal `z` in the
strip `|Im z| < η₀`, the averaged resolvent differs from the limit Cauchy transform by at most
`C_s |Im z|^(−β) / N²`.

This is the *single* analytic input left by the order-`k` mean comparison: it is exactly the
weighted resolvent-difference estimate that the higher-order almost-analytic extension
(`∂̄ = O(|Im z|^k)`) is designed to consume.  It is a hypothesis here, not a theorem. -/
def WeightedStripBound (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (_k : ℕ) (η₀ C_s β : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ z : ℂ, z.im ≠ 0 → |z.im| < η₀ →
    frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
      ≤ C_s * |z.im| ^ (-β) / (N : ℝ) ^ 2

/-! ## The support of `∂̄_k f` in the imaginary direction -/

/-- The cut-off order-`k` extension vanishes in a neighbourhood of every point with
`2 < |Im z|`, hence so does its `∂̄`. -/
lemma dbarNumOrder_eq_zero_of_two_lt_abs_im {f : ℝ → ℝ} {k : ℕ} {z : ℂ}
    (hz : 2 < |z.im|) : dbarNumOrder (k + 1) f z = 0 := by
  have hopen : {w : ℂ | 2 < |w.im|} ∈ 𝓝 z :=
    (isOpen_lt continuous_const
      (continuous_abs.comp Complex.continuous_im)).mem_nhds hz
  have heq : almostAnalyticExtOrderCut (k + 1) f =ᶠ[𝓝 z] 0 := by
    filter_upwards [hopen] with w hw
    simp [almostAnalyticExtOrderCut, yCut_zero_of_two_le hw.le]
  have hd : fderiv ℝ (almostAnalyticExtOrderCut (k + 1) f) z = 0 := by
    rw [heq.fderiv_eq]
    exact fderiv_const_apply (0 : ℂ)
  simp [dbarNumOrder, hd]

/-! ## Integrability of the weighted `∂̄` mass -/

/-- The rectangle support of `∂̄_k f`: there are `X, Y > 0` with `∂̄` supported in
`[-X,X] × [-Y,Y]`. -/
lemma exists_rect_support_dbarNumOrder {f : ℝ → ℝ} {k : ℕ}
    (hfc : HasCompactSupport f) :
    ∃ (X Y : ℝ), 0 < X ∧ 0 < Y ∧ ∀ p : ℝ × ℝ,
      p ∉ Set.Icc (-X) X ×ˢ Set.Icc (-Y) Y → ‖dbarNumOrder (k + 1) f (zOf p)‖ = 0 := by
  have hKc : IsCompact (tsupport (dbarNumOrder (k + 1) f)) :=
    hasCompactSupport_dbarNumOrder (k := k + 1) hfc
  obtain ⟨X, hXpos, hX⟩ : ∃ X : ℝ, 0 < X ∧
      ∀ z ∈ tsupport (dbarNumOrder (k + 1) f), |z.re| < X := by
    have hKr : IsCompact (Complex.re '' tsupport (dbarNumOrder (k + 1) f)) :=
      hKc.image Complex.continuous_re
    obtain ⟨X₀, hX₀⟩ := hKr.exists_bound_of_continuousOn continuous_id.continuousOn
    refine ⟨max X₀ 0 + 1, by positivity, fun z hz => ?_⟩
    have h1 : ‖z.re‖ ≤ X₀ := hX₀ _ ⟨z, hz, rfl⟩
    have h2 : |z.re| ≤ X₀ := by simpa [Real.norm_eq_abs] using h1
    linarith [le_max_left X₀ 0]
  obtain ⟨Y, hYpos, hY⟩ : ∃ Y : ℝ, 0 < Y ∧
      ∀ z ∈ tsupport (dbarNumOrder (k + 1) f), |z.im| < Y := by
    have hKi : IsCompact (Complex.im '' tsupport (dbarNumOrder (k + 1) f)) :=
      hKc.image Complex.continuous_im
    obtain ⟨Y₀, hY₀⟩ := hKi.exists_bound_of_continuousOn continuous_id.continuousOn
    refine ⟨max Y₀ 0 + 1, by positivity, fun z hz => ?_⟩
    have h1 : ‖z.im‖ ≤ Y₀ := hY₀ _ ⟨z, hz, rfl⟩
    have h2 : |z.im| ≤ Y₀ := by simpa [Real.norm_eq_abs] using h1
    linarith [le_max_left Y₀ 0]
  refine ⟨X, Y, hXpos, hYpos, fun p hp => ?_⟩
  have hznot : zOf p ∉ tsupport (dbarNumOrder (k + 1) f) := by
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

/-- **The weighted `∂̄_k f` mass is finite for `β < k`.**  The vanishing order `k` at the real
axis dominates the weight `|Im z|^(−β)` exactly when `β < k`. -/
lemma integrable_norm_dbarNumOrder_mul_rpow_neg {f : ℝ → ℝ} {k K : ℕ} (hk : 1 ≤ k)
    (hf : ContDiff ℝ K f) (hK : k + 1 ≤ K) (hfc : HasCompactSupport f)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβk : β < k) :
    Integrable (fun p : ℝ × ℝ => ‖dbarNumOrder (k + 1) f (zOf p)‖ * |p.2| ^ (-β))
      (volume : Measure (ℝ × ℝ)) := by
  obtain ⟨X, Y, hXpos, hYpos, hsupp⟩ := exists_rect_support_dbarNumOrder (k := k) hfc
  obtain ⟨B, hB0, hB⟩ := exists_norm_dbarNumOrder_le (f := f) (k := k) (K := K) hf hK hfc
  obtain ⟨M₂, hM₂⟩ := exists_norm_iteratedDeriv_le (k := k + 1) hf hK hfc
  have hM₂0 : 0 ≤ M₂ := le_trans (norm_nonneg _) (hM₂ 0)
  have hfac : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hMfac0 : 0 ≤ M₂ / (k.factorial : ℝ) := div_nonneg hM₂0 hfac.le
  set C : ℝ := max (M₂ / (k.factorial : ℝ)) B with hC
  have hC0 : 0 ≤ C := le_trans hMfac0 (le_max_left _ _)
  have hβcont : Continuous fun p : ℝ × ℝ => |p.2| ^ β :=
    (continuous_abs.comp continuous_snd).rpow_const (fun _ => Or.inr hβ0)
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => ‖dbarNumOrder (k + 1) f (zOf p)‖ * |p.2| ^ (-β))
      (volume : Measure (ℝ × ℝ)) := by
    have h2 : AEStronglyMeasurable
        (fun p : ℝ × ℝ => ‖dbarNumOrder (k + 1) f (zOf p)‖ * (|p.2| ^ β)⁻¹)
        (volume : Measure (ℝ × ℝ)) :=
      (((continuous_dbarNumOrder hf hK).comp continuous_zOf).norm.measurable.mul
        (measurable_inv.comp hβcont.measurable)).aestronglyMeasurable
    refine h2.congr (Eventually.of_forall fun p => ?_)
    simp only [Real.rpow_neg (abs_nonneg p.2) β]
  refine Integrable.mono' (integrable_rect_indicator X Y C) hmeas
    (Eventually.of_forall fun p => ?_)
  show ‖‖dbarNumOrder (k + 1) f (zOf p)‖ * |p.2| ^ (-β)‖ ≤
    C * (Set.Icc (-X) X ×ˢ Set.Icc (-Y) Y).indicator (fun _ => (1 : ℝ)) p
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  by_cases hp : p ∈ Set.Icc (-X) X ×ˢ Set.Icc (-Y) Y
  · rw [Set.indicator_of_mem hp, mul_one]
    rcases eq_or_ne p.2 0 with h0 | h0
    · -- on the real axis `∂̄` vanishes to order `k ≥ 1`
      have hk0 : k ≠ 0 := by omega
      have hzle : ‖dbarNumOrder (k + 1) f (zOf p)‖ ≤ 0 := by
        have h := norm_dbar_almostAnalyticExtOrderCut_le (f := f) (k := k) (K := K) hf hK
          (z := zOf p) (by rw [zOf_im, h0]; norm_num) hM₂
        rw [zOf_im, h0, abs_zero, zero_pow hk0, zero_div, zero_mul] at h
        simpa [dbarNumOrder] using h
      have hz0 : ‖dbarNumOrder (k + 1) f (zOf p)‖ = 0 := le_antisymm hzle (norm_nonneg _)
      rw [hz0, zero_mul]
      exact hC0
    · have hpos : 0 < |p.2| := abs_pos.mpr h0
      have hw0 : 0 ≤ |p.2| ^ (-β) := Real.rpow_nonneg (abs_nonneg _) _
      rcases lt_or_ge |p.2| 1 with h1 | h1
      · have hlin := norm_dbar_almostAnalyticExtOrderCut_le (f := f) (k := k) (K := K) hf hK
          (z := zOf p) (by rw [zOf_im]; exact h1) hM₂
        rw [zOf_im] at hlin
        -- `|y|^k * |y|^(-β) = |y|^(k-β) ≤ 1`
        have hcomb : |p.2| ^ k * |p.2| ^ (-β) = |p.2| ^ ((k : ℝ) - β) := by
          rw [← Real.rpow_natCast |p.2| k, ← Real.rpow_add hpos]
          ring_nf
        have hle1 : |p.2| ^ ((k : ℝ) - β) ≤ 1 :=
          Real.rpow_le_one (abs_nonneg _) h1.le (by linarith)
        have hkey : |p.2| ^ k * |p.2| ^ (-β) ≤ 1 := by rw [hcomb]; exact hle1
        calc ‖dbarNumOrder (k + 1) f (zOf p)‖ * |p.2| ^ (-β)
            ≤ (|p.2| ^ k / (k.factorial : ℝ) * M₂) * |p.2| ^ (-β) :=
              mul_le_mul_of_nonneg_right hlin hw0
          _ = (M₂ / (k.factorial : ℝ)) * (|p.2| ^ k * |p.2| ^ (-β)) := by ring
          _ ≤ (M₂ / (k.factorial : ℝ)) * 1 :=
              mul_le_mul_of_nonneg_left hkey hMfac0
          _ ≤ C := le_trans (le_of_eq (mul_one _)) (le_max_left _ _)
      · have hlin := hB (zOf p)
        have hinv1 : |p.2| ^ (-β) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
        have hBle : B ≤ C := le_max_right _ _
        calc ‖dbarNumOrder (k + 1) f (zOf p)‖ * |p.2| ^ (-β)
            ≤ B * |p.2| ^ (-β) := mul_le_mul_of_nonneg_right hlin hw0
          _ ≤ B * 1 := mul_le_mul_of_nonneg_left hinv1 hB0
          _ = B := mul_one B
          _ ≤ C := hBle
  · rw [Set.indicator_of_notMem hp, mul_zero, hsupp p hp]
    simp

/-! ## The pure `N⁻²` comparison -/

/-- **Lemma M from a weighted strip estimate (fixed `N`).**

Given the weighted resolvent comparison on the strip `|Im z| < η₀` (with `η₀ > 2`, so that the
`∂̄` support `|Im z| ≤ 2` lies inside the strip and the far region contributes nothing) at this
`N`, and the two integrability side conditions, the mean discrepancy is `O(N⁻²)` with the single
explicit constant `(2π)⁻¹ C_s ∫∫ ‖∂̄_k f‖ |Im z|^(−β)`.

No a priori mean-resolvent bound is needed: the weighted strip bound plays its role on the
whole support of `∂̄_k f`. -/
theorem smooth_trace_comparison_of_weighted_strip (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (hN : 0 < N)
    {f : ℝ → ℝ} {k K : ℕ} (hk : 1 ≤ k) (hf : ContDiff ℝ K f) (hK : k + 1 ≤ K)
    (hfc : HasCompactSupport f) {η₀ C_s β : ℝ} (hη₀2 : 2 < η₀)
    (hC_s : 0 ≤ C_s) (hβ0 : 0 ≤ β) (hβk : β < k)
    (hstripN : ∀ z : ℂ, z.im ≠ 0 → |z.im| < η₀ →
      frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
        ≤ C_s * |z.im| ^ (-β) / (N : ℝ) ^ 2)
    (hIntN : Integrable (fun p : ℝ × ℝ => dbarNumOrder (k + 1) f (zOf p) *
      Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p))))
    (hIntLim : Integrable (fun p : ℝ × ℝ => dbarNumOrder (k + 1) f (zOf p) *
      Matrix.trace (operatorMatrixPencilCauchy A₀ A (zOf p)))) :
    |∫ x : EuclideanSpace ℝ (GUECoord ι N), gueStatisticCfc (N := N) f A₀ A hA₀ hA x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) - guePlaneLimitOrder k A₀ A f|
      ≤ (2 * Real.pi)⁻¹ * (C_s *
          ∫ p : ℝ × ℝ, ‖dbarNumOrder (k + 1) f (zOf p)‖ * |p.2| ^ (-β)) / (N : ℝ) ^ 2 := by
  classical
  rw [integral_gueStatisticCfc_eq_plane_integral_order' A₀ A hA₀ hA hN hk hf hK hfc,
    guePlaneLimitOrder]
  set c : ℝ := (Fintype.card d : ℝ) with hc
  have hc0 : (0 : ℝ) < c := by
    rw [hc]
    exact_mod_cast Fintype.card_pos
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set W : ℝ := ∫ p : ℝ × ℝ, ‖dbarNumOrder (k + 1) f (zOf p)‖ * |p.2| ^ (-β) with hW
  have hW0 : 0 ≤ W := integral_nonneg (fun p => by positivity)
  obtain ⟨M₂, hM₂⟩ := exists_norm_iteratedDeriv_le (k := k + 1) hf hK hfc
  set Ai : ℂ := ∫ p : ℝ × ℝ, dbarNumOrder (k + 1) f (zOf p) *
    Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p)) with hAi
  set Bi : ℂ := ∫ p : ℝ × ℝ, dbarNumOrder (k + 1) f (zOf p) *
    Matrix.trace (operatorMatrixPencilCauchy A₀ A (zOf p)) with hBi
  -- the difference of the plane integrals is the integral of the resolvent difference
  have hAB : Ai - Bi = ∫ p : ℝ × ℝ, dbarNumOrder (k + 1) f (zOf p) *
      Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p) -
        operatorMatrixPencilCauchy A₀ A (zOf p)) := by
    rw [hAi, hBi, ← integral_sub hIntN hIntLim]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [Matrix.trace_sub]
    ring
  -- integrability of the weighted majorant
  have hWi : Integrable (fun p : ℝ × ℝ =>
      ‖dbarNumOrder (k + 1) f (zOf p)‖ * |p.2| ^ (-β)) :=
    integrable_norm_dbarNumOrder_mul_rpow_neg hk hf hK hfc hβ0 hβk
  -- pointwise bound on the resolvent difference
  have hpoint : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)),
      ‖dbarNumOrder (k + 1) f (zOf p) *
        Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p) -
          operatorMatrixPencilCauchy A₀ A (zOf p))‖
        ≤ ‖dbarNumOrder (k + 1) f (zOf p)‖ *
            (c * (C_s * |p.2| ^ (-β) / (N : ℝ) ^ 2)) := by
    refine Eventually.of_forall fun p => ?_
    by_cases hy0 : p.2 = 0
    · have hk0 : k ≠ 0 := by omega
      have hzle : ‖dbarNumOrder (k + 1) f (zOf p)‖ ≤ 0 := by
        have h := norm_dbar_almostAnalyticExtOrderCut_le (f := f) (k := k) (K := K) hf hK
          (z := zOf p) (by rw [zOf_im, hy0]; norm_num) hM₂
        rw [zOf_im, hy0, abs_zero, zero_pow hk0, zero_div, zero_mul] at h
        simpa [dbarNumOrder] using h
      have hz0 : ‖dbarNumOrder (k + 1) f (zOf p)‖ = 0 :=
        le_antisymm hzle (norm_nonneg _)
      rw [norm_mul, hz0]
      simp
    · by_cases hlt : |p.2| < η₀
      · have hz : (zOf p).im ≠ 0 := by rw [zOf_im]; exact hy0
        have hbound := hstripN (zOf p) hz (by rwa [zOf_im])
        rw [zOf_im] at hbound
        calc ‖dbarNumOrder (k + 1) f (zOf p) *
              Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p) -
                operatorMatrixPencilCauchy A₀ A (zOf p))‖
            = ‖dbarNumOrder (k + 1) f (zOf p)‖ *
                ‖Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p) -
                  operatorMatrixPencilCauchy A₀ A (zOf p))‖ := norm_mul _ _
          _ ≤ ‖dbarNumOrder (k + 1) f (zOf p)‖ *
                (c * frob (gueResolventMean (N := N) A₀ A (zOf p) -
                  operatorMatrixPencilCauchy A₀ A (zOf p))) := by
              refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
              rw [hc]
              exact norm_trace_le_card_mul_frob _
          _ ≤ ‖dbarNumOrder (k + 1) f (zOf p)‖ *
                (c * (C_s * |p.2| ^ (-β) / (N : ℝ) ^ 2)) := by
              refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
              exact mul_le_mul_of_nonneg_left hbound hc0.le
      · have hfar : dbarNumOrder (k + 1) f (zOf p) = 0 := by
          refine dbarNumOrder_eq_zero_of_two_lt_abs_im ?_
          rw [zOf_im]
          exact lt_of_lt_of_le hη₀2 (not_lt.mp hlt)
        rw [hfar]
        simp
  -- the weighted integral
  have hmaj : Integrable (fun p : ℝ × ℝ =>
      ‖dbarNumOrder (k + 1) f (zOf p)‖ * (c * (C_s * |p.2| ^ (-β) / (N : ℝ) ^ 2))) := by
    refine (hWi.mul_const (c * (C_s / (N : ℝ) ^ 2))).congr
      (Eventually.of_forall fun p => ?_)
    ring
  have hdiff : ‖Ai - Bi‖ ≤ c * (C_s / (N : ℝ) ^ 2) * W := by
    rw [hAB]
    refine (norm_integral_le_of_norm_le hmaj hpoint).trans (le_of_eq ?_)
    have hcongr : (fun p : ℝ × ℝ =>
        ‖dbarNumOrder (k + 1) f (zOf p)‖ * (c * (C_s * |p.2| ^ (-β) / (N : ℝ) ^ 2)))
        = fun p : ℝ × ℝ =>
          (c * (C_s / (N : ℝ) ^ 2)) *
            (‖dbarNumOrder (k + 1) f (zOf p)‖ * |p.2| ^ (-β)) := by
      funext p
      ring
    rw [hcongr, integral_const_mul, hW]
  -- final absolute-value algebra
  have hre : (I / (2 * (Real.pi : ℂ)) * Ai).re - (I / (2 * (Real.pi : ℂ)) * Bi).re
      = (I / (2 * (Real.pi : ℂ)) * (Ai - Bi)).re := by
    rw [← Complex.sub_re, ← mul_sub]
  have hnorm : ‖(I / (2 * (Real.pi : ℂ))) * (Ai - Bi)‖ = (2 * Real.pi)⁻¹ * ‖Ai - Bi‖ := by
    rw [norm_mul]
    congr 1
    rw [norm_div, Complex.norm_I]
    have h2 : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
      rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) from by push_cast; ring]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [h2, one_div]
  have hcne : c ≠ 0 := hc0.ne'
  calc |c⁻¹ * (I / (2 * (Real.pi : ℂ)) * Ai).re -
        c⁻¹ * (I / (2 * (Real.pi : ℂ)) * Bi).re|
      = c⁻¹ * |(I / (2 * (Real.pi : ℂ)) * (Ai - Bi)).re| := by
        rw [← mul_sub, ← hre, abs_mul, abs_of_pos (by positivity)]
    _ ≤ c⁻¹ * ‖(I / (2 * (Real.pi : ℂ))) * (Ai - Bi)‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by positivity)
    _ = c⁻¹ * ((2 * Real.pi)⁻¹ * ‖Ai - Bi‖) := by rw [hnorm]
    _ ≤ c⁻¹ * ((2 * Real.pi)⁻¹ * (c * (C_s / (N : ℝ) ^ 2) * W)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hdiff (by positivity)
    _ = (2 * Real.pi)⁻¹ * (C_s * W) / (N : ℝ) ^ 2 := by
        field_simp

/-! ## Eventual form and the mean bound -/

/-- **The weighted strip bound gives the pure `O(N⁻²)` comparison, eventually in `N`.**

This is the form consumed by `FlatLemmaM`: the hypotheses are the eventual weighted strip
bound, the eventual integrability of the finite-`N` plane integrand, and the (fixed)
integrability of the limit plane integrand. -/
theorem eventually_smooth_trace_comparison_of_weighted_strip (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    {f : ℝ → ℝ} {k K : ℕ} (hk : 1 ≤ k) (hf : ContDiff ℝ K f) (hK : k + 1 ≤ K)
    (hfc : HasCompactSupport f) {η₀ C_s β : ℝ} (hη₀2 : 2 < η₀)
    (hC_s : 0 ≤ C_s) (hβ0 : 0 ≤ β) (hβk : β < k)
    (hstrip : WeightedStripBound A₀ A k η₀ C_s β)
    (hIntN : ∀ᶠ N : ℕ in atTop, Integrable (fun p : ℝ × ℝ =>
      dbarNumOrder (k + 1) f (zOf p) *
        Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p))))
    (hIntLim : Integrable (fun p : ℝ × ℝ => dbarNumOrder (k + 1) f (zOf p) *
      Matrix.trace (operatorMatrixPencilCauchy A₀ A (zOf p)))) :
    ∀ᶠ N : ℕ in atTop,
      |∫ x : EuclideanSpace ℝ (GUECoord ι N), gueStatisticCfc (N := N) f A₀ A hA₀ hA x
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) - guePlaneLimitOrder k A₀ A f|
        ≤ (2 * Real.pi)⁻¹ * (C_s *
            ∫ p : ℝ × ℝ, ‖dbarNumOrder (k + 1) f (zOf p)‖ * |p.2| ^ (-β)) / (N : ℝ) ^ 2 := by
  filter_upwards [hstrip, hIntN, eventually_gt_atTop (0 : ℕ)] with N hstr hInt hN
  exact smooth_trace_comparison_of_weighted_strip A₀ A hA₀ hA hN hk hf hK hfc hη₀2 hC_s
    hβ0 hβk hstr hInt hIntLim

/-- **The mean itself is `O(N⁻²)` when the limit statistic vanishes.**  This is the `hWb`
shape: applied to `(f')²`, whose limit statistic vanishes because `f' = 0` on the spectrum of
the limit pencil (the cut-off is locally constant there). -/
theorem abs_integral_gueStatisticCfc_le_of_weighted_strip (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (hN : 0 < N)
    {f : ℝ → ℝ} {k K : ℕ} (hk : 1 ≤ k) (hf : ContDiff ℝ K f) (hK : k + 1 ≤ K)
    (hfc : HasCompactSupport f) {η₀ C_s β : ℝ} (hη₀2 : 2 < η₀)
    (hC_s : 0 ≤ C_s) (hβ0 : 0 ≤ β) (hβk : β < k)
    (hstripN : ∀ z : ℂ, z.im ≠ 0 → |z.im| < η₀ →
      frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
        ≤ C_s * |z.im| ^ (-β) / (N : ℝ) ^ 2)
    (hIntN : Integrable (fun p : ℝ × ℝ => dbarNumOrder (k + 1) f (zOf p) *
      Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p))))
    (hIntLim : Integrable (fun p : ℝ × ℝ => dbarNumOrder (k + 1) f (zOf p) *
      Matrix.trace (operatorMatrixPencilCauchy A₀ A (zOf p))))
    (hlim0 : guePlaneLimitOrder k A₀ A f = 0) :
    |∫ x : EuclideanSpace ℝ (GUECoord ι N), gueStatisticCfc (N := N) f A₀ A hA₀ hA x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))|
      ≤ (2 * Real.pi)⁻¹ * (C_s *
          ∫ p : ℝ × ℝ, ‖dbarNumOrder (k + 1) f (zOf p)‖ * |p.2| ^ (-β)) / (N : ℝ) ^ 2 := by
  have h := smooth_trace_comparison_of_weighted_strip A₀ A hA₀ hA hN hk hf hK hfc hη₀2 hC_s
    hβ0 hβk hstripN hIntN hIntLim
  simpa [hlim0] using h

noncomputable section

/-! ## The explicit constant and the eventual mean bound -/

/-- The finite constant of the weighted-strip mean comparison:
`(2π)⁻¹ C_s ∫∫ ‖∂̄_k f‖ |Im z|^(−β)`. -/
def weightedStripConstant (f : ℝ → ℝ) (k : ℕ) (C_s β : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * (C_s *
    ∫ p : ℝ × ℝ, ‖dbarNumOrder (k + 1) f (zOf p)‖ * |p.2| ^ (-β))

lemma weightedStripConstant_nonneg {f : ℝ → ℝ} {k : ℕ} {C_s β : ℝ} (hC_s : 0 ≤ C_s) :
    0 ≤ weightedStripConstant f k C_s β := by
  refine mul_nonneg (by positivity) (mul_nonneg hC_s ?_)
  exact integral_nonneg (fun p => by positivity)

section EventualMean

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] [Nonempty d]

/-- **The eventual mean bound with the explicit weighted-strip constant.**  The `hWb` shape:
when the limit statistic vanishes, the mean itself is `O(N⁻²)`. -/
theorem eventually_abs_integral_gueStatisticCfc_le_of_weighted_strip
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) {f : ℝ → ℝ} {k K : ℕ} (hk : 1 ≤ k)
    (hf : ContDiff ℝ K f) (hK : k + 1 ≤ K) (hfc : HasCompactSupport f)
    {η₀ C_s β : ℝ} (hη₀2 : 2 < η₀) (hC_s : 0 ≤ C_s) (hβ0 : 0 ≤ β) (hβk : β < k)
    (hstrip : WeightedStripBound A₀ A k η₀ C_s β)
    (hIntN : ∀ᶠ N : ℕ in atTop, Integrable (fun p : ℝ × ℝ =>
      dbarNumOrder (k + 1) f (zOf p) *
        Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p))))
    (hIntLim : Integrable (fun p : ℝ × ℝ => dbarNumOrder (k + 1) f (zOf p) *
      Matrix.trace (operatorMatrixPencilCauchy A₀ A (zOf p))))
    (hlim0 : guePlaneLimitOrder k A₀ A f = 0) :
    ∀ᶠ N : ℕ in atTop,
      |∫ x : EuclideanSpace ℝ (GUECoord ι N), gueStatisticCfc (N := N) f A₀ A hA₀ hA x
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))|
        ≤ weightedStripConstant f k C_s β / (N : ℝ) ^ 2 := by
  have h := eventually_smooth_trace_comparison_of_weighted_strip A₀ A hA₀ hA hk hf hK hfc
    hη₀2 hC_s hβ0 hβk hstrip hIntN hIntLim
  filter_upwards [h] with N hN
  simpa [weightedStripConstant, hlim0] using hN

end EventualMean

/-! ## Packaging the flattened pencil -/

section Flat

variable {r k : ℕ} {F : RatPolyIdx r (k + 1)} {z : ℝ}

/-- **A smooth cutoff vanishing, with vanishing derivative, on the target set.**  This is the
stronger cutoff actually produced by `exists_contDiff_two_cutoff`; `IsSmoothCutoff` alone does
not record it.  It is exactly what makes the limit statistics of `f` and `(f')²` vanish. -/
structure IsSmoothCutoffZeroOn (S : Set ℝ) (ε : ℝ) (f : ℝ → ℝ) : Prop where
  /-- the underlying smooth cutoff -/
  smooth : IsSmoothCutoff S ε f
  /-- the cutoff vanishes on the target set -/
  eq_zero : ∀ x ∈ S, f x = 0
  /-- the derivative vanishes on the target set -/
  deriv_eq_zero : ∀ x ∈ S, deriv f x = 0

/-- The strengthened smooth cutoff exists: the construction of `exists_contDiff_two_cutoff`
provides all the required properties. -/
theorem exists_isSmoothCutoffZeroOn {S : Set ℝ} {ε : ℝ} (hS : IsCompact S) (hε : 0 < ε) :
    ∃ f : ℝ → ℝ, IsSmoothCutoffZeroOn S ε f ∧ ContDiff ℝ 2 f := by
  obtain ⟨f, hcd2, h0, hzero, hone, hle, hderiv, hsupp⟩ := exists_contDiff_two_cutoff hS hε
  exact ⟨f, ⟨⟨hcd2.of_le (by norm_num), h0, hle, hone, hsupp⟩, hzero, hderiv⟩, hcd2⟩

/-- **`hWb` from a mean comparison for `(f')²`.**  This is the bookkeeping step: a bound on the
absolute value of the mean gives the one-sided bound used by the `(W)` field. -/
lemma hWb_of_flatLemmaM_deriv {f : ℝ → ℝ} {C' : ℝ}
    (hMderiv : FlatLemmaM r k F z (fun y => (deriv f y) ^ 2) C') :
    ∀ᶠ N : ℕ in atTop,
      ∫ x, flatStat r k F z N (fun y => (deriv f y) ^ 2) x
        ∂(commonGaussianMeasure (Fin r)) ≤ C' / (N : ℝ) ^ 2 := by
  filter_upwards [hMderiv] with N hN
  exact (abs_le.mp hN).2

/-- **`FlatLemmaM` from a weighted strip bound, given the flat ⟶ GUE identification.**

`hstat` identifies the flattened statistic at block `N` with the GUE statistic of the
realisation `(A₀, A)` at block `N + 1`; `hlim0` is the vanishing of the limit statistic (a
consequence of `g = 0` on the limit spectrum through the limit-side representation, which is not
packaged in the repository).  These two are explicit hypotheses: the theorem is a *reduction*
of `FlatLemmaM` to the weighted strip bound plus those identifications, not a proof of Lemma M.

The cut-off regularity `ContDiff ℝ (k+1) g` and compact support are those required by the
order-`k` Cauchy--Pompeiu representation. -/
theorem flatLemmaM_of_weightedStrip
    {g : ℝ → ℝ} {d' : ℕ} [NeZero d'] (A₀ : Matrix (Fin d') (Fin d') ℂ)
    (A : Fin r → Matrix (Fin d') (Fin d') ℂ) (hA₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) (hk : 1 ≤ k) {η₀ C_s β : ℝ} (hη₀2 : 2 < η₀)
    (hC_s : 0 ≤ C_s) (hβ0 : 0 ≤ β) (hβk : β < k) (hg : ContDiff ℝ (k + 1) g)
    (hgc : HasCompactSupport g) (hstrip : WeightedStripBound A₀ A k η₀ C_s β)
    (hstat : ∀ N : ℕ,
      ∫ x, flatStat r k F z N g x ∂(commonGaussianMeasure (Fin r))
        = ∫ y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)),
            gueStatisticCfc (N := N + 1) g A₀ A hA₀ hA y
              ∂(stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))))
    (hlim0 : guePlaneLimitOrder k A₀ A g = 0)
    (hIntN : ∀ᶠ N : ℕ in atTop, Integrable (fun p : ℝ × ℝ =>
      dbarNumOrder (k + 1) g (zOf p) *
        Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p))))
    (hIntLim : Integrable (fun p : ℝ × ℝ => dbarNumOrder (k + 1) g (zOf p) *
      Matrix.trace (operatorMatrixPencilCauchy A₀ A (zOf p)))) :
    FlatLemmaM r k F z g (weightedStripConstant g k C_s β) := by
  -- the mean comparison at block `n + 1`, from the strip bound and integrability at block `n + 1`
  have hmain : ∀ᶠ N : ℕ in atTop,
      |∫ y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)),
          gueStatisticCfc (N := N + 1) g A₀ A hA₀ hA y
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1))))|
        ≤ weightedStripConstant g k C_s β / ((N + 1 : ℕ) : ℝ) ^ 2 := by
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hstrip
    obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 hIntN
    refine eventually_atTop.2 ⟨max N₀ M₀, fun n hn => ?_⟩
    have hn₀ : N₀ ≤ n + 1 := le_trans (le_max_left N₀ M₀) (by omega)
    have hm₀ : M₀ ≤ n + 1 := le_trans (le_max_right N₀ M₀) (by omega)
    have hfixed := abs_integral_gueStatisticCfc_le_of_weighted_strip (N := n + 1) A₀ A hA₀ hA
      (by omega) hk hg (K := k + 1) le_rfl hgc hη₀2 hC_s hβ0 hβk
      (fun w hw hlt => hN₀ (n + 1) hn₀ w hw hlt) (hM₀ (n + 1) hm₀) hIntLim hlim0
    simpa [weightedStripConstant] using hfixed
  filter_upwards [hmain, eventually_ge_atTop (1 : ℕ)] with N hN hN1
  rw [hstat N]
  refine hN.trans ?_
  have hC0 : 0 ≤ weightedStripConstant g k C_s β := weightedStripConstant_nonneg (f := g) hC_s
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hsq : (N : ℝ) ^ 2 ≤ ((N : ℝ) + 1) ^ 2 := by nlinarith
  push_cast
  exact div_le_div_of_nonneg_left hC0 (by positivity) hsq

end Flat


/-! ## From the weighted mean comparison to the final theorem -/

section FinalConditional

variable {r : ℕ}

local instance : Nontrivial (closedSemicircularAlgebra (Fin r)) :=
  (closedGeneratedVacuumState (Fin r)).toProbabilitySpace.nontrivial

local instance : PartialOrder (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrder _

local instance : StarOrderedRing (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrderedRing _

/-- **`PencilLemmaSResidual` from the two mean comparisons.**  The variance field `hV` is
discharged unconditionally by `PencilLemmaSResidual_of_smoothCutoff_hV`; the `(W)` bound `hWb`
is exactly the one-sided form of the mean comparison for `(f')²` (bookkeeping). -/
theorem PencilLemmaSResidual_of_weightedStrip {k : ℕ} {F : RatPolyIdx r (k + 1)} {z : ℝ}
    {ε : ℝ} {f : ℝ → ℝ} (C' : ℝ)
    (hcut : IsSmoothCutoffZeroOn (specC (h1PencilLimit r k F z)) ε f)
    (hM : FlatLemmaM r k F z f (2 * flatContractionConst r k F / pencilVDim r k F))
    (hMderiv : FlatLemmaM r k F z (fun y => (deriv f y) ^ 2) C') (hC' : 0 ≤ C') :
    PencilLemmaSResidual r k F z f (2 * flatContractionConst r k F / pencilVDim r k F) C' :=
  PencilLemmaSResidual_of_smoothCutoff_hV k F z C' hcut.smooth hcut.smooth.contDiff hM
    (hWb_of_flatLemmaM_deriv hMderiv)

/-- **`PencilLemmaSData` from the two mean comparisons.**  All the other side conditions
(`hZ`, `hWint`, `hW0`, `hV`) are discharged by `PencilLemmaSData_of_smoothCutoff_hV`. -/
theorem PencilLemmaSData_of_weightedStrip {k : ℕ} {F : RatPolyIdx r (k + 1)} {z ε : ℝ}
    {f : ℝ → ℝ} (C' : ℝ)
    (hcut : IsSmoothCutoffZeroOn (specC (h1PencilLimit r k F z)) ε f)
    (hM : FlatLemmaM r k F z f (2 * flatContractionConst r k F / pencilVDim r k F))
    (hMderiv : FlatLemmaM r k F z (fun y => (deriv f y) ^ 2) C') (hC' : 0 ≤ C') :
    PencilLemmaSData r k F z ε f (2 * flatContractionConst r k F / pencilVDim r k F) C' :=
  PencilLemmaSData_of_smoothCutoff_hV k F z ε C' hcut.smooth hM
    (hWb_of_flatLemmaM_deriv hMderiv) hC'

/-- **The `FlatLemmaM` footprint of the weighted strip bounds.**

At every canonical dilated polynomial, pencil parameter and radius it provides a strengthened
cutoff `f` (`f = 0` and `f' = 0` on the limit spectrum) together with the two mean comparisons
that the weighted strip bound yields (through `flatLemmaM_of_weightedStrip`, once the plain
flat ⟶ GUE identification `FlatGUEStatisticEq` and the two limit-statistic vanishing statements
are supplied): the comparison for `f` and the comparison for `(f')²`.

The gap between this bundle and `WeightedStripBound`-only is precisely `FlatGUEStatisticEq`
plus the limit-statistic vanishing; see the module docstring. -/
def WeightedMeanInputs (r : ℕ) : Prop :=
  ∀ (k : ℕ) (F : RatPolyIdx r (k + 1)) (z ε : ℝ), 0 < ε →
    ∃ (f : ℝ → ℝ) (C C' : ℝ),
      IsSmoothCutoffZeroOn (specC (h1PencilLimit r k F z)) ε f ∧
      FlatLemmaM r k F z f C ∧
      FlatLemmaM r k F z (fun y => (deriv f y) ^ 2) C' ∧
      0 ≤ C ∧ 0 ≤ C'

/-- **The residual-input bundle from the weighted mean comparisons.**  The mean constant is
enlarged to `max C (2 * flatContractionConst / pencilVDim)` so that the variance field can be
instantiated at the same constant; this only weakens the mean comparison. -/
theorem PencilLemmaSResidualInputs_of_weightedMeanInputs (h : WeightedMeanInputs r) :
    PencilLemmaSResidualInputs r := by
  intro k F z ε hε
  obtain ⟨f, C, C', hcut, hM, hMderiv, hC, hC'⟩ := h k F z ε hε
  have hC₀0 : 0 ≤ 2 * flatContractionConst r k F / pencilVDim r k F :=
    flatContractionConst_div_pencilVDim_nonneg k F
  set Cm : ℝ := max C (2 * flatContractionConst r k F / pencilVDim r k F) with hCm
  have hCm0 : 0 ≤ Cm := le_trans hC (le_max_left _ _)
  have hM' : FlatLemmaM r k F z f Cm := by
    filter_upwards [hM] with N hN
    refine hN.trans ?_
    exact div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
  have hV : ∀ᶠ N : ℕ in atTop,
      variance (flatStat r k F z N f) (commonGaussianMeasure (Fin r))
        ≤ Cm / (N : ℝ) ^ 2 * ∫ x, flatStat r k F z N (fun y => (deriv f y) ^ 2) x
            ∂(commonGaussianMeasure (Fin r)) := by
    filter_upwards [hV_field_residual_shape k F z hcut.smooth hcut.smooth.contDiff] with N hN
    refine hN.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (integral_flatStat_sq_nonneg k F z f N)
    exact div_le_div_of_nonneg_right (le_max_right _ _) (by positivity)
  exact ⟨f, Cm, C', hcut.smooth, ⟨hM', hV, hWb_of_flatLemmaM_deriv hMderiv⟩, hCm0, hC'⟩

/-- **The six Lemma-S inputs from the weighted mean comparisons.** -/
theorem PencilLemmaSInputs_of_weightedMeanInputs (h : WeightedMeanInputs r) :
    PencilLemmaSInputs r :=
  PencilLemmaSInputs_of_residualInputs (PencilLemmaSResidualInputs_of_weightedMeanInputs h)

/-- **The project target from scalar spectral inclusion and the weighted mean comparisons.**

Every hypothesis is explicit: `hScalar` is the scalar spectral inclusion for the leading GUE
matrix, and `h` is the `FlatLemmaM` footprint of the weighted strip bounds (see
`WeightedMeanInputs`).  The passage from `h` to the final statement is the already verified
chain `PencilLemmaSResidualInputs → PencilLemmaSInputs → H1CanonicalDilated →
GUEStrongConvergenceStatement`. -/
theorem GUEStrongConvergenceStatement_of_weightedMeanInputs
    (hScalar : ScalarSpectralInclusion r) (h : WeightedMeanInputs r) :
    GUEStrongConvergenceStatement r :=
  GUEStrongConvergenceStatement_of_scalarSpectralInclusion_and_lemmaSInputs hScalar
    (PencilLemmaSInputs_of_weightedMeanInputs h)

/-- **The missing flat ⟶ GUE identification**, in integrated form: the flattened statistic of
the `F`-th dilated polynomial at block `N` is the GUE statistic of the matrix realisation
`(A₀, A)` (of size `d' + 1`) at block `N + 1`, for every test function `g`.

This is the integrated form of the Kronecker/reindexing identity
`flatPencilBlk r k F N z y = Matrix.reindex (pencilFlatIdx r k F N) (pencilFlatIdx r k F N)
  (guePencilMatrix A₀ A y)` together with `gueStatisticCfc_eq_normTrace_guePencilMatrixFinOn`
and `integral_flatStat_eq_blk`.  It is *not* on main: it is a bookkeeping (not analytic) gap
recorded here explicitly rather than assumed silently. -/
def FlatGUEStatisticEq (r k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ) (d' : ℕ)
    (A₀ : Matrix (Fin (d' + 1)) (Fin (d' + 1)) ℂ)
    (A : Fin r → Matrix (Fin (d' + 1)) (Fin (d' + 1)) ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) : Prop :=
  ∀ (N : ℕ) (g : ℝ → ℝ),
    ∫ x, flatStat r k F z N g x ∂(commonGaussianMeasure (Fin r))
      = ∫ y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)),
          gueStatisticCfc (N := N + 1) g A₀ A hA₀ hA y
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1))))

/-- **The weighted-strip data at one pencil for `1 ≤ k`.**  It provides the strengthened cutoff
with the regularity needed by the order-`k` extensions of `f` and `(f')²`, a GUE realisation
with the explicit identification `FlatGUEStatisticEq`, the weighted strip bound with `η₀ > 2`,
the vanishing of the two limit statistics, and the four plane-integrand integrability side
conditions. -/
def WeightedStripDataAt (r k : ℕ) (F : RatPolyIdx r (k + 1)) (z ε : ℝ) : Prop :=
  ∃ (d' : ℕ) (A₀ : Matrix (Fin (d' + 1)) (Fin (d' + 1)) ℂ)
    (A : Fin r → Matrix (Fin (d' + 1)) (Fin (d' + 1)) ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (η₀ C_s β : ℝ) (hη₀2 : 2 < η₀) (hC_s : 0 ≤ C_s) (hβ0 : 0 ≤ β) (hβk : β < k)
    (f : ℝ → ℝ) (C' : ℝ),
    IsSmoothCutoffZeroOn (specC (h1PencilLimit r k F z)) ε f ∧
    ContDiff ℝ (k + 1) f ∧
    ContDiff ℝ (k + 1) (fun y => (deriv f y) ^ 2) ∧
    HasCompactSupport f ∧
    WeightedStripBound A₀ A k η₀ C_s β ∧
    FlatGUEStatisticEq r k F z d' A₀ A hA₀ hA ∧
    guePlaneLimitOrder k A₀ A f = 0 ∧
    guePlaneLimitOrder k A₀ A (fun y => (deriv f y) ^ 2) = 0 ∧
    (∀ᶠ N : ℕ in atTop, Integrable (fun p : ℝ × ℝ =>
      dbarNumOrder (k + 1) f (zOf p) *
        Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p)))) ∧
    Integrable (fun p : ℝ × ℝ => dbarNumOrder (k + 1) f (zOf p) *
      Matrix.trace (operatorMatrixPencilCauchy A₀ A (zOf p))) ∧
    (∀ᶠ N : ℕ in atTop, Integrable (fun p : ℝ × ℝ =>
      dbarNumOrder (k + 1) (fun y => (deriv f y) ^ 2) (zOf p) *
        Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p)))) ∧
    Integrable (fun p : ℝ × ℝ =>
      dbarNumOrder (k + 1) (fun y => (deriv f y) ^ 2) (zOf p) *
        Matrix.trace (operatorMatrixPencilCauchy A₀ A (zOf p))) ∧
    0 ≤ C'

/-- **The weighted-strip input bundle.**

* for `1 ≤ k`, the weighted-strip GUE data `WeightedStripDataAt` at every canonical dilated
  polynomial, pencil parameter and radius;
* for `k = 0`, the (first-order) mean-comparison footprint, which is a *separate* residual: the
  order-`k` weighted-strip machinery starts at `k = 1`, since the order-`k` Cauchy--Pompeiu
  identity requires `1 ≤ k`.

The three identification/vanishing statements inside `WeightedStripDataAt` are the honest extra
hypotheses: they are not derived in the repository (see `FlatGUEStatisticEq`). -/
def WeightedStripInputs (r : ℕ) : Prop :=
  (∀ (k : ℕ) (F : RatPolyIdx r (k + 1)) (z ε : ℝ), 1 ≤ k → 0 < ε →
    WeightedStripDataAt r k F z ε) ∧
  (∀ (F : RatPolyIdx r (0 + 1)) (z ε : ℝ), 0 < ε →
    ∃ (f : ℝ → ℝ) (C C' : ℝ),
      IsSmoothCutoffZeroOn (specC (h1PencilLimit r 0 F z)) ε f ∧
      FlatLemmaM r 0 F z f C ∧
      FlatLemmaM r 0 F z (fun y => (deriv f y) ^ 2) C' ∧
      0 ≤ C ∧ 0 ≤ C')

/-- **The weighted strip inputs give the mean comparisons.**  For `1 ≤ k` this applies
`flatLemmaM_of_weightedStrip` to `f` and to `(f')²`, using the identification and the
integrability fields of `WeightedStripDataAt`; for `k = 0` it uses the separate first-order
field. -/
theorem WeightedMeanInputs_of_weightedStripInputs (h : WeightedStripInputs r) :
    WeightedMeanInputs r := by
  intro k F z ε hε
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    exact h.2 F z ε hε
  · obtain ⟨d', A₀, A, hA₀, hA, η₀, C_s, β, hη₀2, hC_s, hβ0, hβk, f, C',
      hcut, hreg, hregw, hfc, hstrip, hstat, hlim0, hlim0w, hIntNf, hIntLimf, hIntNw,
      hIntLimw, hC'⟩ := h.1 k F z ε hkpos hε
    exact ⟨f, weightedStripConstant f k C_s β,
      weightedStripConstant (fun y => (deriv f y) ^ 2) k C_s β, hcut,
      flatLemmaM_of_weightedStrip (d' := d' + 1) A₀ A hA₀ hA hkpos hη₀2 hC_s hβ0 hβk
        hreg hfc hstrip (fun N => hstat N f) hlim0 hIntNf hIntLimf,
      flatLemmaM_of_weightedStrip (d' := d' + 1) A₀ A hA₀ hA hkpos hη₀2 hC_s hβ0 hβk
        hregw hcut.smooth.compactSupport hstrip
        (fun N => hstat N (fun y => (deriv f y) ^ 2)) hlim0w hIntNw hIntLimw,
      weightedStripConstant_nonneg hC_s, weightedStripConstant_nonneg hC_s⟩

/-- **The residual-input bundle from the weighted strip inputs.** -/
theorem PencilLemmaSResidualInputs_of_weightedStripInputs (h : WeightedStripInputs r) :
    PencilLemmaSResidualInputs r :=
  PencilLemmaSResidualInputs_of_weightedMeanInputs (WeightedMeanInputs_of_weightedStripInputs h)

/-- **The project target from scalar spectral inclusion and the weighted strip bounds.**

This is the final conditional form: `GUEStrongConvergenceStatement r` from
`ScalarSpectralInclusion r` and `WeightedStripInputs r`.  The weighted strip bounds enter
through `WeightedStripBound`; the three identification/vanishing statements are explicit fields
of `WeightedStripDataAt` (see `FlatGUEStatisticEq` and the module docstring), and `k = 0` is a
separate explicit first-order mean-comparison field. -/
theorem GUEStrongConvergenceStatement_of_weightedStripInputs
    (hScalar : ScalarSpectralInclusion r) (h : WeightedStripInputs r) :
    GUEStrongConvergenceStatement r :=
  GUEStrongConvergenceStatement_of_weightedMeanInputs hScalar
    (WeightedMeanInputs_of_weightedStripInputs h)

end FinalConditional

end

end

end GUEStrongConvergence
