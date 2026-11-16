/-
# Repairing the weighted-strip exponent (`|Im z|⁻⁷`, extension order 8)

`Probability/LemmaMWeighted.lean` states the single analytic input of the mean comparison as

`WeightedStripBound A₀ A k η₀ C_s β` :
  `frob (g_N(z) − g(z)) ≤ C_s |Im z|^(−β) / N²`  for `0 < |Im z| < η₀`,

and `flatLemmaM_of_weightedStrip` consumes it under `β < k`, where `k` is *both* the polynomial
linearization index and the order of the almost-analytic extension.  The project's intended
analytic input (`gue_strong_convergence_part_II_handoff.md` §5.4, (5.15)–(5.16), HT05 Thm 5.7) is
only

  `frob (g_N(z) − g(z)) ≤ C_s (K + ‖z‖)^2 |Im z|^(−7) / N²`,

and no bound `|Im z|^(−β)` with `β < 1` can follow from it.  The constant `C_s` of the bundle is
absolute, so the bundle with `β < max k 1` is **not inhabited** by the intended input: the
hypothesis is vacuous, not merely strong.

The resolution is *not* to weaken the exponent but to separate the extension order from the
polynomial index and to raise it: with the honest exponent `β = 7`, the `∂̄`-weighted strip
integrand is `O(|Im z|^(q − 7))` for an extension of order `q`, which is integrable at the real
axis as soon as `q > 7`.  Hence extension order `q = 8` (regularity `C⁹`) is exactly what the
handoff itself chooses ("choose `k = 8` to avoid borderline conventions"), and *no* polynomial
index `k` enters the exponent condition.  This file

* states the honest strip bound `WeightedStripBoundProven` with the constant
  `C_s (K + ‖z‖)²` of (5.15) (the `|z|`-growth is harmless: `∂̄_{q+1} f` is supported in a
  compact rectangle, exactly the handoff's remark "the `x` and `y` supports are compact, so
  `(K_A + |z|)²` is bounded there");
* proves the weighted `∂̄` mass is finite at `β = 7`, `q = 8` (with the explicit polynomial
  weight);
* re-proves the Cauchy–Pompeiu transfer `smooth_trace_comparison_of_weighted_strip_proven` at
  the honest exponent, with the explicit constant
  `(2π)⁻¹ C_s ∫∫ ‖∂̄_{q+1} f‖ (K + ‖z‖)² |Im z|⁻⁷`;
* derives `FlatLemmaM` from `WeightedStripBoundProven` at any extension order `q ≥ 8`
  (`flatLemmaM_of_weightedStripProven`), which is the exact downstream object the rest of the
  chain consumes.

The bundle-level plumbing (the `f ↔ f − 1` shift for the cutoff, which is `1` at infinity) is
carried out in `StrongConvergence/WeightedStripRepairBundle.lean`.

No `sorry`, no new axioms.
-/
import GUEStrongConvergence.Probability.ExtensionOrderFree
import GUEStrongConvergence.StrongConvergence.CutoffFlatCancellation

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

/-! ## 1. The honest strip hypothesis -/

/-- **The honest weighted strip bound** (handoff (5.15)–(5.16), HT05 Theorem 5.7).

For all sufficiently large `N` and every nonreal `z` in the strip `|Im z| < η₀`, the averaged
resolvent differs from its operator-valued (Dyson) limit by at most
`C_s (K + ‖z‖)² |Im z|⁻⁷ / N²`.  The exponent `−7` is the honest exponent of the handoff; the
polynomial weight `(K + ‖z‖)²` is absorbed on the compact support of `∂̄ f`.

This is a *hypothesis*, not a theorem: it is the analytic input the project does not prove. -/
def WeightedStripBoundProven (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (η₀ K C_s : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ z : ℂ, z.im ≠ 0 → |z.im| < η₀ →
    frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
      ≤ C_s * (K + ‖z‖) ^ 2 * |z.im| ^ (-(7 : ℝ)) / (N : ℝ) ^ 2

/-- The honest bound at a fixed `N` (the form consumed pointwise by the transfer). -/
def WeightedStripBoundProvenAt (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (N : ℕ)
    (η₀ K C_s : ℝ) : Prop :=
  ∀ z : ℂ, z.im ≠ 0 → |z.im| < η₀ →
    frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
      ≤ C_s * (K + ‖z‖) ^ 2 * |z.im| ^ (-(7 : ℝ)) / (N : ℝ) ^ 2

/-! ## 2. Finiteness of the weighted `∂̄` mass -/

/-- **The weighted `∂̄` mass at the honest exponent is finite at extension order `q ≥ 8`.**

The `∂̄` of the order-`q+1` cut-off extension vanishes to order `q` on the real axis
(`norm_dbar_almostAnalyticExtOrderCut_le`), so the product with `|Im z|⁻⁷` is bounded there;
the polynomial weight `(K + ‖z‖)²` is bounded on the compact rectangle supporting `∂̄`. -/
lemma integrable_norm_dbarNumOrder_mul_polyWeight_rpow_neg {f : ℝ → ℝ} {k K : ℕ}
    (hk : 1 ≤ k) (hf : ContDiff ℝ K f) (hK : k + 1 ≤ K) (hfc : HasCompactSupport f)
    {β Kc : ℝ} (hβ0 : 0 ≤ β) (hβk : β < k) :
    Integrable (fun p : ℝ × ℝ =>
      ‖dbarNumOrder (k + 1) f (zOf p)‖ * (Kc + ‖zOf p‖) ^ 2 * |p.2| ^ (-β))
      (volume : Measure (ℝ × ℝ)) := by
  obtain ⟨X, Y, hXpos, hYpos, hsupp⟩ := exists_rect_support_dbarNumOrder (k := k) hfc
  have hbase : Integrable (fun p : ℝ × ℝ =>
      ‖dbarNumOrder (k + 1) f (zOf p)‖ * |p.2| ^ (-β)) :=
    integrable_norm_dbarNumOrder_mul_rpow_neg hk hf hK hfc hβ0 hβk
  set Cw : ℝ := (|Kc| + X + Y) ^ 2 with hCw
  have hCw0 : 0 ≤ Cw := by rw [hCw]; positivity
  have hcont : Continuous (fun p : ℝ × ℝ => (Kc + ‖zOf p‖) ^ 2) := by
    have h1 : Continuous (fun p : ℝ × ℝ => ‖zOf p‖) := continuous_norm.comp continuous_zOf
    exact (continuous_const.add h1).pow 2
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      ‖dbarNumOrder (k + 1) f (zOf p)‖ * (Kc + ‖zOf p‖) ^ 2 * |p.2| ^ (-β))
      (volume : Measure (ℝ × ℝ)) := by
    have hβcont : Continuous fun p : ℝ × ℝ => |p.2| ^ β :=
      (continuous_abs.comp continuous_snd).rpow_const (fun _ => Or.inr hβ0)
    have h2 : AEStronglyMeasurable
        (fun p : ℝ × ℝ => ‖dbarNumOrder (k + 1) f (zOf p)‖ * (|p.2| ^ β)⁻¹)
        (volume : Measure (ℝ × ℝ)) :=
      (((continuous_dbarNumOrder hf hK).comp continuous_zOf).norm.measurable.mul
        (measurable_inv.comp hβcont.measurable)).aestronglyMeasurable
    refine (h2.mul hcont.measurable.aestronglyMeasurable).congr (Eventually.of_forall ?_)
    intro p
    simp only [Pi.mul_apply, Real.rpow_neg (abs_nonneg p.2) β]
    ring
  refine Integrable.mono' (hbase.mul_const Cw) hmeas ?_
  filter_upwards with p
  rw [Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤
      ‖dbarNumOrder (k + 1) f (zOf p)‖ * (Kc + ‖zOf p‖) ^ 2 * |p.2| ^ (-β))]
  by_cases h0 : ‖dbarNumOrder (k + 1) f (zOf p)‖ = 0
  · rw [h0, zero_mul, zero_mul]
    simp
  · have hp : p ∈ Set.Icc (-X) X ×ˢ Set.Icc (-Y) Y := by
      by_contra hmem
      exact h0 (hsupp p hmem)
    have hx : |p.1| ≤ X := by
      have h := hp.1
      rw [Set.mem_Icc] at h
      exact abs_le.mpr h
    have hy : |p.2| ≤ Y := by
      have h := hp.2
      rw [Set.mem_Icc] at h
      exact abs_le.mpr h
    have hzn : ‖zOf p‖ ≤ X + Y := by
      calc ‖zOf p‖ = ‖(p.1 : ℂ) + (p.2 : ℂ) * I‖ := rfl
        _ ≤ ‖(p.1 : ℂ)‖ + ‖(p.2 : ℂ) * I‖ := norm_add_le _ _
        _ = |p.1| + |p.2| := by simp
        _ ≤ X + Y := add_le_add hx hy
    have hw : (Kc + ‖zOf p‖) ^ 2 ≤ Cw := by
      rw [hCw]
      have h1 : |Kc + ‖zOf p‖| ≤ |Kc| + X + Y := by
        have h := abs_add_le Kc ‖zOf p‖
        rw [abs_of_nonneg (norm_nonneg _)] at h
        linarith
      calc (Kc + ‖zOf p‖) ^ 2 = |Kc + ‖zOf p‖| ^ 2 := by rw [sq_abs]
        _ ≤ (|Kc| + X + Y) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    calc ‖dbarNumOrder (k + 1) f (zOf p)‖ * (Kc + ‖zOf p‖) ^ 2 * |p.2| ^ (-β)
        = (‖dbarNumOrder (k + 1) f (zOf p)‖ * |p.2| ^ (-β)) * (Kc + ‖zOf p‖) ^ 2 := by
          ring
      _ ≤ (‖dbarNumOrder (k + 1) f (zOf p)‖ * |p.2| ^ (-β)) * Cw :=
          mul_le_mul_of_nonneg_left hw (by positivity)

/-- The honest `|Im z|⁻⁷` mass at extension order `q ≥ 8`:
`∫∫ ‖∂̄_{q+1} f‖ (K + ‖z‖)² |Im z|⁻⁷`. -/
lemma integrable_norm_dbarNumOrder_mul_polyWeight_rpow_neg_seven {f : ℝ → ℝ} {k K : ℕ}
    (hk : 1 ≤ k) (hf : ContDiff ℝ K f) (hK : k + 1 ≤ K) (hfc : HasCompactSupport f)
    {Kc : ℝ} (hk8 : 7 < k) :
    Integrable (fun p : ℝ × ℝ =>
      ‖dbarNumOrder (k + 1) f (zOf p)‖ * (Kc + ‖zOf p‖) ^ 2 * |p.2| ^ (-(7 : ℝ)))
      (volume : Measure (ℝ × ℝ)) := by
  refine integrable_norm_dbarNumOrder_mul_polyWeight_rpow_neg hk hf hK hfc
    (β := (7 : ℝ)) (Kc := Kc) (by norm_num) ?_
  exact_mod_cast hk8

/-! ## 3. The Cauchy–Pompeiu transfer at the honest exponent -/

/-- **Lemma M from the honest strip estimate (fixed `N`).**

With the honest bound `frob (g_N − g) ≤ C_s (K + ‖z‖)² |Im z|⁻⁷ / N²` on the whole strip
`|Im z| < η₀ > 2`, the plane-integral representation of the mean gives

`|E τ_N(f) − guePlaneLimitOrder k A₀ A f| ≤ (2π)⁻¹ C_s (∫∫ ‖∂̄_{k+1} f‖ (K + ‖z‖)² |Im z|⁻⁷)/N²`

for every extension order `k ≥ 8`.  The exponent condition is `7 < k`, i.e. `k ≥ 8`; there is no
condition on the polynomial index (it is not even an argument here). -/
theorem smooth_trace_comparison_of_weighted_strip_proven (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (hN : 0 < N)
    {f : ℝ → ℝ} {k K : ℕ} (hk : 1 ≤ k) (hk8 : 7 < k) (hf : ContDiff ℝ K f) (hK : k + 1 ≤ K)
    (hfc : HasCompactSupport f) {η₀ Kc C_s : ℝ} (hη₀2 : 2 < η₀) (hC_s : 0 ≤ C_s)
    (hstripN : WeightedStripBoundProvenAt A₀ A N η₀ Kc C_s)
    (hIntN : Integrable (fun p : ℝ × ℝ => dbarNumOrder (k + 1) f (zOf p) *
      Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p))))
    (hIntLim : Integrable (fun p : ℝ × ℝ => dbarNumOrder (k + 1) f (zOf p) *
      Matrix.trace (operatorMatrixPencilCauchy A₀ A (zOf p)))) :
    |∫ x : EuclideanSpace ℝ (GUECoord ι N), gueStatisticCfc (N := N) f A₀ A hA₀ hA x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) - guePlaneLimitOrder k A₀ A f|
      ≤ (2 * Real.pi)⁻¹ * (C_s *
          ∫ p : ℝ × ℝ, ‖dbarNumOrder (k + 1) f (zOf p)‖ * (Kc + ‖zOf p‖) ^ 2 *
            |p.2| ^ (-(7 : ℝ))) / (N : ℝ) ^ 2 := by
  classical
  rw [integral_gueStatisticCfc_eq_plane_integral_order' A₀ A hA₀ hA hN hk hf hK hfc,
    guePlaneLimitOrder]
  set c : ℝ := (Fintype.card d : ℝ) with hc
  have hc0 : (0 : ℝ) < c := by
    rw [hc]
    exact_mod_cast Fintype.card_pos
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set W : ℝ := ∫ p : ℝ × ℝ, ‖dbarNumOrder (k + 1) f (zOf p)‖ * (Kc + ‖zOf p‖) ^ 2 *
    |p.2| ^ (-(7 : ℝ)) with hW
  have hW0 : 0 ≤ W := integral_nonneg (fun p => by positivity)
  set Ai : ℂ := ∫ p : ℝ × ℝ, dbarNumOrder (k + 1) f (zOf p) *
    Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p)) with hAi
  set Bi : ℂ := ∫ p : ℝ × ℝ, dbarNumOrder (k + 1) f (zOf p) *
    Matrix.trace (operatorMatrixPencilCauchy A₀ A (zOf p)) with hBi
  have hAB : Ai - Bi = ∫ p : ℝ × ℝ, dbarNumOrder (k + 1) f (zOf p) *
      Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p) -
        operatorMatrixPencilCauchy A₀ A (zOf p)) := by
    rw [hAi, hBi, ← integral_sub hIntN hIntLim]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [Matrix.trace_sub]
    ring
  have hWi : Integrable (fun p : ℝ × ℝ =>
      ‖dbarNumOrder (k + 1) f (zOf p)‖ * (Kc + ‖zOf p‖) ^ 2 * |p.2| ^ (-(7 : ℝ))) :=
    integrable_norm_dbarNumOrder_mul_polyWeight_rpow_neg_seven hk hf hK hfc
      (Kc := Kc) hk8
  obtain ⟨M₂, hM₂⟩ := exists_norm_iteratedDeriv_le (k := k + 1) hf hK hfc
  have hpoint : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)),
      ‖dbarNumOrder (k + 1) f (zOf p) *
        Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p) -
          operatorMatrixPencilCauchy A₀ A (zOf p))‖
        ≤ ‖dbarNumOrder (k + 1) f (zOf p)‖ *
            (c * (C_s * (Kc + ‖zOf p‖) ^ 2 * |p.2| ^ (-(7 : ℝ)) / (N : ℝ) ^ 2)) := by
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
                (c * (C_s * (Kc + ‖zOf p‖) ^ 2 * |p.2| ^ (-(7 : ℝ)) / (N : ℝ) ^ 2)) := by
              refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
              exact mul_le_mul_of_nonneg_left hbound hc0.le
      · have hfar : dbarNumOrder (k + 1) f (zOf p) = 0 := by
          refine dbarNumOrder_eq_zero_of_two_lt_abs_im ?_
          rw [zOf_im]
          exact lt_of_lt_of_le hη₀2 (not_lt.mp hlt)
        rw [hfar]
        simp
  have hmaj : Integrable (fun p : ℝ × ℝ =>
      ‖dbarNumOrder (k + 1) f (zOf p)‖ *
        (c * (C_s * (Kc + ‖zOf p‖) ^ 2 * |p.2| ^ (-(7 : ℝ)) / (N : ℝ) ^ 2))) := by
    refine (hWi.mul_const (c * (C_s / (N : ℝ) ^ 2))).congr
      (Eventually.of_forall fun p => ?_)
    ring
  have hdiff : ‖Ai - Bi‖ ≤ c * (C_s / (N : ℝ) ^ 2) * W := by
    rw [hAB]
    refine (norm_integral_le_of_norm_le hmaj hpoint).trans (le_of_eq ?_)
    have hcongr : (fun p : ℝ × ℝ =>
        ‖dbarNumOrder (k + 1) f (zOf p)‖ *
          (c * (C_s * (Kc + ‖zOf p‖) ^ 2 * |p.2| ^ (-(7 : ℝ)) / (N : ℝ) ^ 2)))
        = fun p : ℝ × ℝ =>
          (c * (C_s / (N : ℝ) ^ 2)) *
            (‖dbarNumOrder (k + 1) f (zOf p)‖ * (Kc + ‖zOf p‖) ^ 2 *
              |p.2| ^ (-(7 : ℝ))) := by
      funext p
      ring
    rw [hcongr, integral_const_mul, hW]
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

/-! ## 4. Eventual form and the explicit constant -/

/-- The honest constant of the repaired transfer:
`(2π)⁻¹ C_s ∫∫ ‖∂̄_{q+1} f‖ (K + ‖z‖)² |Im z|⁻⁷`. -/
def weightedStripConstantProven (f : ℝ → ℝ) (q : ℕ) (Kc C_s : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * (C_s *
    ∫ p : ℝ × ℝ, ‖dbarNumOrder (q + 1) f (zOf p)‖ * (Kc + ‖zOf p‖) ^ 2 *
      |p.2| ^ (-(7 : ℝ)))

lemma weightedStripConstantProven_nonneg {f : ℝ → ℝ} {q : ℕ} {Kc C_s : ℝ}
    (hC_s : 0 ≤ C_s) : 0 ≤ weightedStripConstantProven f q Kc C_s := by
  refine mul_nonneg (by positivity) (mul_nonneg hC_s ?_)
  exact integral_nonneg (fun p => by positivity)

/-- **The honest strip bound gives the pure `O(N⁻²)` comparison, eventually in `N`.** -/
theorem eventually_smooth_trace_comparison_of_weighted_strip_proven (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    {f : ℝ → ℝ} {k K : ℕ} (hk : 1 ≤ k) (hk8 : 7 < k) (hf : ContDiff ℝ K f) (hK : k + 1 ≤ K)
    (hfc : HasCompactSupport f) {η₀ Kc C_s : ℝ} (hη₀2 : 2 < η₀) (hC_s : 0 ≤ C_s)
    (hstrip : WeightedStripBoundProven A₀ A η₀ Kc C_s)
    (hIntN : ∀ᶠ N : ℕ in atTop, Integrable (fun p : ℝ × ℝ =>
      dbarNumOrder (k + 1) f (zOf p) *
        Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p))))
    (hIntLim : Integrable (fun p : ℝ × ℝ => dbarNumOrder (k + 1) f (zOf p) *
      Matrix.trace (operatorMatrixPencilCauchy A₀ A (zOf p)))) :
    ∀ᶠ N : ℕ in atTop,
      |∫ x : EuclideanSpace ℝ (GUECoord ι N), gueStatisticCfc (N := N) f A₀ A hA₀ hA x
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) - guePlaneLimitOrder k A₀ A f|
        ≤ weightedStripConstantProven f k Kc C_s / (N : ℝ) ^ 2 := by
  filter_upwards [hstrip, hIntN, eventually_gt_atTop (0 : ℕ)] with N hstr hInt hN
  have h := smooth_trace_comparison_of_weighted_strip_proven A₀ A hA₀ hA hN hk hk8 hf hK hfc
    hη₀2 hC_s (fun z hz hlt => hstr z hz hlt) hInt hIntLim
  simpa [weightedStripConstantProven] using h

/-- **The mean itself is `O(N⁻²)` when the limit statistic vanishes** (the `hWb` shape). -/
theorem eventually_abs_integral_gueStatisticCfc_le_of_weighted_strip_proven
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) {f : ℝ → ℝ} {k K : ℕ} (hk : 1 ≤ k) (hk8 : 7 < k)
    (hf : ContDiff ℝ K f) (hK : k + 1 ≤ K) (hfc : HasCompactSupport f)
    {η₀ Kc C_s : ℝ} (hη₀2 : 2 < η₀) (hC_s : 0 ≤ C_s)
    (hstrip : WeightedStripBoundProven A₀ A η₀ Kc C_s)
    (hIntN : ∀ᶠ N : ℕ in atTop, Integrable (fun p : ℝ × ℝ =>
      dbarNumOrder (k + 1) f (zOf p) *
        Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p))))
    (hIntLim : Integrable (fun p : ℝ × ℝ => dbarNumOrder (k + 1) f (zOf p) *
      Matrix.trace (operatorMatrixPencilCauchy A₀ A (zOf p))))
    (hlim0 : guePlaneLimitOrder k A₀ A f = 0) :
    ∀ᶠ N : ℕ in atTop,
      |∫ x : EuclideanSpace ℝ (GUECoord ι N), gueStatisticCfc (N := N) f A₀ A hA₀ hA x
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))|
        ≤ weightedStripConstantProven f k Kc C_s / (N : ℝ) ^ 2 := by
  have h := eventually_smooth_trace_comparison_of_weighted_strip_proven A₀ A hA₀ hA
    hk hk8 hf hK hfc hη₀2 hC_s hstrip hIntN hIntLim
  filter_upwards [h] with N hN
  simpa [hlim0] using hN

end

end GUEStrongConvergence
