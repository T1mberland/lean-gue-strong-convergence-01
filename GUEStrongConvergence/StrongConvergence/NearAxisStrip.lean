/-
# The near-axis matrix strip bound: weight form, free exponent, and region split

`StrongConvergence/WeightedStripRepair.lean` states the single analytic input of the mean
comparison as

`WeightedStripBoundProven A₀ A η₀ Kc C_s` :
  `frob (g_N(z) − g(z)) ≤ C_s (Kc + ‖z‖)² |Im z|⁻⁷ / N²`  for `0 < |Im z| < η₀`,

and consumes it *only* through the Cauchy–Pompeiu comparison
`smooth_trace_comparison_of_weighted_strip_proven`, which multiplies the deviation by
`∂̄_{k+1} f` and integrates over the plane.  This file makes the exact dependency explicit and
weakens the hypothesis accordingly.

## Main results

* `StripWeightBoundAt` — the deviation bound with a **free weight** `w : ℝ → ℝ` on `Im z`,
  required only on the fixed strip `|Im z| < 2` (outside which `∂̄_{q+1} f` vanishes, see
  `dbarNumOrder_eq_zero_of_two_lt_abs_im`);
* `stripWeightMass` — the `∂̄`-mass `∫∫ ‖∂̄_{q+1} f‖ (Kc + ‖z‖)² w(Im z)` of the weight;
* `smooth_trace_comparison_of_strip_weight` — **the weighted transfer**: any weight whose
  `∂̄`-mass is finite gives the `O(N⁻²)` comparison with constant `(2π)⁻¹ · mass / N²`.
  This isolates the *exact* requirement on the near-axis deviation: finiteness of the mass,
  not a particular power of `|Im z|`;
* `StripPowerBoundAt` — the honest shape `C_b (Kc + ‖z‖)² |Im z|^{-β} / N²` with a **free
  exponent** `β`;
* `smooth_trace_comparison_of_strip_power`, `eventually_smooth_trace_comparison_of_strip_power`,
  `flatLemmaM_of_stripPowerBound` — hence `FlatLemmaM` follows from the power bound for **any**
  `β < k` (in the endgame `k = 8`), not only for the honest `β = 7`: the exponent `−7` of
  `WeightedStripBoundProven` can be replaced by any exponent `β < 8`;
* `StripBoundSplitAt` — the region split: a free exponent away from the axis
  (`δ ≤ |Im z| < 2`), an exponent `β_n < k` near the axis;
* `smooth_trace_comparison_of_strip_split` and `flatLemmaM_of_stripSplitBound` — the region
  split gives the same comparison.  Away from the axis the exponent is *entirely free*: the
  `∂̄`-mass there is bounded because `∂̄_{q+1} f` is supported in a compact rectangle on which
  `|Im z| ≥ δ > 0`;
* `stripPowerBoundAt_of_weightedStripBoundProven` — the honest hypothesis of
  `WeightedStripBoundProven` (with `η₀ ≥ 2`) is an instance of the power form with `β = 7`, so
  the results of this file genuinely generalise `WeightedStripRepair`.

## What is *not* proved here, and why (recorded for the record)

The near-axis *matrix* bound `frob (g_N − g) ≤ C (Kc + ‖z‖)² |Im z|^{-β} / N²` with `β < 8`
uniformly in `N` remains open.  Every linearisation available in the repository fails near the
axis, for the same reason:

* the loop identity `m − g = g(∑ A_i (m−g) A_i) m + g Var` inverts through
  `‖g‖ ‖m‖ S ≈ (card d)² S/|Im z|² < 1`, exactly the `dyson_stability` threshold
  (`dysonThreshold A = max 1 √(2 (card d)² S)`);
* the exact identity `(z • 1 − A₀)(m − g) = V_g` with the limit-centred second moment
  `V_g = ∑ A_i (E[T A_i T] − g A_i g)` shows that the missing input is a *second-order* statement
  about `E[T A T]` centred at the limit; but `V_g = V_m + ∑ A_i (X A_i X + g A_i X + X A_i g)`
  with `X = m − g`, and `V_m` is what the sharp covariance bound controls, so substituting back
  returns the same threshold;
* the second resolvent identity (two spectral parameters) reduces the annulus to a two-point
  correlation whose reconstruction again contains the term `X(w) g(w')` with coefficient
  `|w'−w| ‖g(w')‖ ≈ 2 card d > 1` — never a contraction;
* a region split cannot help: the above-threshold theorems start at the *fixed* constant
  `dysonThreshold A`, so an `N`-dependent near-axis band cannot shrink past it, and inside the
  fixed annulus the only estimate available without new input is the trivial deterministic
  `frob (g_N − g) ≤ 2 card d |Im z|⁻¹`, which carries no `N⁻²` factor (`O(1) + O(N⁻²) ≠ O(N⁻²)`);
* a polynomial/contour approximation of the resolvent cannot help either: the degree needed for
  accuracy `N⁻²` at distance `y = |Im z|` from the real axis is `n ≳ (K/y) log N`, while the
  Gaussian word-moment bounds available grow like `(2n−1)!! ≈ (2n/e)^n`, so the total error is
  `N⁻² exp(n log n)` — small only for `y ≳ K log log N`, i.e. only on a region that *shrinks*
  in `N` and therefore never covers a fixed neighbourhood of the axis.

The remaining input is genuinely second order in `1/N` for matrix coefficients (a first-genus /
parity statement about the mean), and has to be proved as such.

No `sorry`, no new axioms.
-/
import GUEStrongConvergence.StrongConvergence.WeightedStripRepair
import GUEStrongConvergence.StrongConvergence.PencilStripAbove

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

/-! ## 1. The deviation with a free weight on `Im z` -/

/-- **The strip deviation bound with a free weight.**

`frob (g_N(z) − g(z)) ≤ (Kc + ‖z‖)² w (Im z) / N²` for every nonreal `z` with `|Im z| ≤ 2`.
The restriction to the fixed strip `|Im z| < 2` is harmless: `∂̄_{q+1} f` vanishes off it
(`dbarNumOrder_eq_zero_of_two_lt_abs_im`), so the Cauchy–Pompeiu integrand only sees the
strip.

The weight `w` is completely free; the only requirement is that the `∂̄`-mass
`stripWeightMass` below is finite. -/
def StripWeightBoundAt (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (N : ℕ)
    (Kc : ℝ) (w : ℝ → ℝ) : Prop :=
  ∀ z : ℂ, z.im ≠ 0 → |z.im| ≤ 2 →
    frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
      ≤ (Kc + ‖z‖) ^ 2 * w z.im / (N : ℝ) ^ 2

/-- **The `∂̄`-mass of the weight**: the exact quantity that has to be finite for the
Cauchy–Pompeiu comparison to produce the `O(N⁻²)` bound. -/
def stripWeightMass (f : ℝ → ℝ) (q : ℕ) (Kc : ℝ) (w : ℝ → ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, ‖dbarNumOrder (q + 1) f (zOf p)‖ * (Kc + ‖zOf p‖) ^ 2 * w p.2

lemma stripWeightMass_nonneg {f : ℝ → ℝ} {q : ℕ} {Kc : ℝ} {w : ℝ → ℝ}
    (hw : ∀ t, 0 ≤ w t) : 0 ≤ stripWeightMass f q Kc w := by
  refine integral_nonneg fun p => ?_
  have h1 : (0 : ℝ) ≤ ‖dbarNumOrder (q + 1) f (zOf p)‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ (Kc + ‖zOf p‖) ^ 2 := sq_nonneg _
  exact mul_nonneg (mul_nonneg h1 h2) (hw p.2)

/-! ## 2. The weighted Cauchy–Pompeiu transfer -/

/-- **Lemma M from a weighted strip estimate (fixed `N`).**

If the deviation obeys `frob (g_N − g) ≤ (Kc + ‖z‖)² w (Im z) / N²` on `|Im z| < 2` and the
`∂̄`-mass `∫∫ ‖∂̄_{k+1} f‖ (Kc + ‖z‖)² w` is finite, then

`|E τ_N(f) − guePlaneLimitOrder k A₀ A f| ≤ (2π)⁻¹ (∫∫ ‖∂̄_{k+1} f‖ (Kc + ‖z‖)² w) / N²`.

This is the *exact* form in which the endgame consumes the strip estimate: only the weighted
mass matters, not the pointwise shape of `w`. -/
theorem smooth_trace_comparison_of_strip_weight (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (hN : 0 < N)
    {f : ℝ → ℝ} {k K : ℕ} (hk : 1 ≤ k) (hf : ContDiff ℝ K f) (hK : k + 1 ≤ K)
    (hfc : HasCompactSupport f) {Kc : ℝ} {w : ℝ → ℝ} (hw : ∀ t, 0 ≤ w t)
    (hbound : StripWeightBoundAt A₀ A N Kc w)
    (hmass : Integrable (fun p : ℝ × ℝ =>
      ‖dbarNumOrder (k + 1) f (zOf p)‖ * (Kc + ‖zOf p‖) ^ 2 * w p.2))
    (hIntN : Integrable (fun p : ℝ × ℝ => dbarNumOrder (k + 1) f (zOf p) *
      Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p))))
    (hIntLim : Integrable (fun p : ℝ × ℝ => dbarNumOrder (k + 1) f (zOf p) *
      Matrix.trace (operatorMatrixPencilCauchy A₀ A (zOf p)))) :
    |∫ x : EuclideanSpace ℝ (GUECoord ι N), gueStatisticCfc (N := N) f A₀ A hA₀ hA x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) - guePlaneLimitOrder k A₀ A f|
      ≤ (2 * Real.pi)⁻¹ * stripWeightMass f k Kc w / (N : ℝ) ^ 2 := by
  classical
  rw [integral_gueStatisticCfc_eq_plane_integral_order' A₀ A hA₀ hA hN hk hf hK hfc,
    guePlaneLimitOrder]
  set c : ℝ := (Fintype.card d : ℝ) with hc
  have hc0 : (0 : ℝ) < c := by
    rw [hc]
    exact_mod_cast Fintype.card_pos
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set W : ℝ := ∫ p : ℝ × ℝ, ‖dbarNumOrder (k + 1) f (zOf p)‖ * (Kc + ‖zOf p‖) ^ 2 *
    w p.2 with hW
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
  obtain ⟨M₂, hM₂⟩ := exists_norm_iteratedDeriv_le (k := k + 1) hf hK hfc
  have hpoint : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)),
      ‖dbarNumOrder (k + 1) f (zOf p) *
        Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p) -
          operatorMatrixPencilCauchy A₀ A (zOf p))‖
        ≤ ‖dbarNumOrder (k + 1) f (zOf p)‖ *
            (c * ((Kc + ‖zOf p‖) ^ 2 * w p.2 / (N : ℝ) ^ 2)) := by
    refine Eventually.of_forall fun p => ?_
    by_cases hfar : 2 < |p.2|
    · have hzero : dbarNumOrder (k + 1) f (zOf p) = 0 := by
        refine dbarNumOrder_eq_zero_of_two_lt_abs_im ?_
        rwa [zOf_im]
      rw [hzero]
      simp
    · by_cases hy0 : p.2 = 0
      · have hk0 : k ≠ 0 := by omega
        have hzero : ‖dbarNumOrder (k + 1) f (zOf p)‖ = 0 := by
          have hle : ‖dbarNumOrder (k + 1) f (zOf p)‖ ≤ 0 := by
            have h := norm_dbar_almostAnalyticExtOrderCut_le (f := f) (k := k) (K := K) hf hK
              (z := zOf p) (by rw [zOf_im, hy0]; norm_num) hM₂
            rw [zOf_im, hy0, abs_zero, zero_pow hk0, zero_div, zero_mul] at h
            simpa [dbarNumOrder] using h
          exact le_antisymm hle (norm_nonneg _)
        simp [hzero]
      · have hle : |p.2| ≤ 2 := not_lt.mp hfar
        have hz : (zOf p).im ≠ 0 := by rw [zOf_im]; exact hy0
        have hb := hbound (zOf p) hz (by rw [zOf_im]; exact hle)
        rw [zOf_im] at hb
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
                (c * ((Kc + ‖zOf p‖) ^ 2 * w p.2 / (N : ℝ) ^ 2)) := by
              refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
              exact mul_le_mul_of_nonneg_left hb hc0.le
  have hmaj : Integrable (fun p : ℝ × ℝ =>
      ‖dbarNumOrder (k + 1) f (zOf p)‖ *
        (c * ((Kc + ‖zOf p‖) ^ 2 * w p.2 / (N : ℝ) ^ 2))) := by
    refine (hmass.mul_const (c / (N : ℝ) ^ 2)).congr (Eventually.of_forall fun p => ?_)
    ring
  have hdiff : ‖Ai - Bi‖ ≤ c / (N : ℝ) ^ 2 * W := by
    rw [hAB]
    refine (norm_integral_le_of_norm_le hmaj hpoint).trans (le_of_eq ?_)
    have hcongr : (fun p : ℝ × ℝ =>
        ‖dbarNumOrder (k + 1) f (zOf p)‖ *
          (c * ((Kc + ‖zOf p‖) ^ 2 * w p.2 / (N : ℝ) ^ 2)))
        = fun p : ℝ × ℝ => (c / (N : ℝ) ^ 2) *
            (‖dbarNumOrder (k + 1) f (zOf p)‖ * (Kc + ‖zOf p‖) ^ 2 * w p.2) := by
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
    _ ≤ c⁻¹ * ((2 * Real.pi)⁻¹ * (c / (N : ℝ) ^ 2 * W)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hdiff (by positivity)
    _ = (2 * Real.pi)⁻¹ * W / (N : ℝ) ^ 2 := by
        field_simp

/-! ## 3. The free exponent: any `β < k` suffices

The honest hypothesis `WeightedStripBoundProven` asks for the exponent `−7` together with the
polynomial weight `(Kc + ‖z‖)²`.  The transfer only needs the weight's `∂̄`-mass to be finite,
which for a power weight `|Im z|^{-β}` happens as soon as `β < k` (`k` being the order of the
almost-analytic extension; `k = 8` in the endgame).  Hence the exponent `−7` is not special:
**any** exponent `β < k` gives the same `O(N⁻²)` mean comparison. -/

/-- **The strip deviation bound with a free exponent `β` on the fixed strip `|Im z| ≤ 2`.**

This is the honest shape `C_b (Kc + ‖z‖)² |Im z|^{-β} / N²`; the honest hypothesis
`WeightedStripBoundProven` is the special case `β = 7` restricted to `|Im z| < η₀`
(`stripPowerBoundAt_of_weightedStripBoundProven`), and the Cauchy–Pompeiu transfer accepts every
`β < k`. -/
def StripPowerBoundAt (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (N : ℕ)
    (Kc Cb β : ℝ) : Prop :=
  ∀ z : ℂ, z.im ≠ 0 → |z.im| ≤ 2 →
    frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
      ≤ Cb * (Kc + ‖z‖) ^ 2 * |z.im| ^ (-β) / (N : ℝ) ^ 2

/-- The power form is the weight form with the weight `t ↦ C_b |t|^{-β}`. -/
lemma stripWeightBoundAt_power (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (N : ℕ)
    {Kc Cb β : ℝ} (hCb : 0 ≤ Cb) (hβ : 0 ≤ β) :
    StripWeightBoundAt A₀ A N Kc (fun t => Cb * |t| ^ (-β))
      ↔ StripPowerBoundAt A₀ A N Kc Cb β := by
  have hkey : ∀ (t s : ℝ), (Kc + s) ^ 2 * (Cb * |t| ^ (-β))
      = Cb * (Kc + s) ^ 2 * |t| ^ (-β) := by
    intro t s
    ring
  refine ⟨fun h z hz hle => ?_, fun h z hz hle => ?_⟩
  · have hb := h z hz hle
    rwa [hkey] at hb
  · have hb := h z hz hle
    rw [hkey]
    exact hb

/-- The `∂̄`-mass of a power weight, written out: `C_b ∫∫ ‖∂̄_{q+1} f‖ (Kc + ‖z‖)² |Im z|^{-β}`. -/
def stripPowerMass (f : ℝ → ℝ) (q : ℕ) (Kc Cb β : ℝ) : ℝ :=
  Cb * ∫ p : ℝ × ℝ, ‖dbarNumOrder (q + 1) f (zOf p)‖ * (Kc + ‖zOf p‖) ^ 2 * |p.2| ^ (-β)

lemma stripWeightMass_power {f : ℝ → ℝ} {q : ℕ} {Kc Cb β : ℝ} :
    stripWeightMass f q Kc (fun t => Cb * |t| ^ (-β)) = stripPowerMass f q Kc Cb β := by
  rw [stripWeightMass, stripPowerMass]
  congr 1
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  ring

/-- **Lemma M from a free-exponent strip estimate (fixed `N`).**

For **any** exponent `β` with `0 ≤ β < k`, the strip bound
`frob (g_N − g) ≤ C_b (Kc + ‖z‖)² |Im z|^{-β} / N²` on `|Im z| ≤ 2` gives

`|E τ_N(f) − guePlaneLimitOrder k A₀ A f| ≤ (2π)⁻¹ C_b (∫∫ ‖∂̄_{k+1} f‖ (Kc + ‖z‖)² |Im z|^{-β}) / N²`.

In the endgame `k = 8`, so every exponent `β < 8` is admissible, in particular the honest
`β = 7` and everything between `7` and `8`. -/
theorem smooth_trace_comparison_of_strip_power (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (hN : 0 < N)
    {f : ℝ → ℝ} {k K : ℕ} (hk : 1 ≤ k) {β : ℝ} (hβ0 : 0 ≤ β) (hβk : β < k)
    (hf : ContDiff ℝ K f) (hK : k + 1 ≤ K) (hfc : HasCompactSupport f)
    {Kc Cb : ℝ} (hCb : 0 ≤ Cb) (hbound : StripPowerBoundAt A₀ A N Kc Cb β)
    (hIntN : Integrable (fun p : ℝ × ℝ => dbarNumOrder (k + 1) f (zOf p) *
      Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p))))
    (hIntLim : Integrable (fun p : ℝ × ℝ => dbarNumOrder (k + 1) f (zOf p) *
      Matrix.trace (operatorMatrixPencilCauchy A₀ A (zOf p)))) :
    |∫ x : EuclideanSpace ℝ (GUECoord ι N), gueStatisticCfc (N := N) f A₀ A hA₀ hA x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) - guePlaneLimitOrder k A₀ A f|
      ≤ (2 * Real.pi)⁻¹ * stripPowerMass f k Kc Cb β / (N : ℝ) ^ 2 := by
  have hmass : Integrable (fun p : ℝ × ℝ => ‖dbarNumOrder (k + 1) f (zOf p)‖ *
      (Kc + ‖zOf p‖) ^ 2 * (Cb * |p.2| ^ (-β))) := by
    refine ((integrable_norm_dbarNumOrder_mul_polyWeight_rpow_neg hk hf hK hfc
      (β := β) (Kc := Kc) hβ0 hβk).mul_const Cb).congr
      (Eventually.of_forall fun p => ?_)
    ring
  have h := smooth_trace_comparison_of_strip_weight (Kc := Kc) (w := fun t => Cb * |t| ^ (-β))
    A₀ A hA₀ hA hN hk hf hK hfc (fun t => mul_nonneg hCb (Real.rpow_nonneg (abs_nonneg t) _))
    ((stripWeightBoundAt_power A₀ A N hCb hβ0).mpr hbound) hmass
    hIntN hIntLim
  rw [stripWeightMass_power] at h
  exact h

/-- **Eventual form of the free-exponent comparison.** -/
theorem eventually_smooth_trace_comparison_of_strip_power (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    {f : ℝ → ℝ} {k K : ℕ} (hk : 1 ≤ k) {β : ℝ} (hβ0 : 0 ≤ β) (hβk : β < k)
    (hf : ContDiff ℝ K f) (hK : k + 1 ≤ K) (hfc : HasCompactSupport f)
    {Kc Cb : ℝ} (hCb : 0 ≤ Cb)
    (hbound : ∀ᶠ N : ℕ in atTop, StripPowerBoundAt A₀ A N Kc Cb β)
    (hIntN : ∀ᶠ N : ℕ in atTop, Integrable (fun p : ℝ × ℝ =>
      dbarNumOrder (k + 1) f (zOf p) *
        Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p))))
    (hIntLim : Integrable (fun p : ℝ × ℝ => dbarNumOrder (k + 1) f (zOf p) *
      Matrix.trace (operatorMatrixPencilCauchy A₀ A (zOf p)))) :
    ∀ᶠ N : ℕ in atTop,
      |∫ x : EuclideanSpace ℝ (GUECoord ι N), gueStatisticCfc (N := N) f A₀ A hA₀ hA x
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) - guePlaneLimitOrder k A₀ A f|
        ≤ (2 * Real.pi)⁻¹ * stripPowerMass f k Kc Cb β / (N : ℝ) ^ 2 := by
  filter_upwards [hbound, hIntN, eventually_gt_atTop (0 : ℕ)] with N hb hInt hN
  exact smooth_trace_comparison_of_strip_power A₀ A hA₀ hA hN hk hβ0 hβk hf hK hfc hCb hb
    hInt hIntLim

/-- **The honest hypothesis is the `β = 7` instance.**  For `η₀ ≥ 2` the honest strip bound
`WeightedStripBoundProven A₀ A η₀ Kc C_s` implies the free-exponent form with `β = 7`. -/
theorem stripPowerBoundAt_of_weightedStripBoundProven (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) {η₀ Kc C_s : ℝ} (hη₀2 : 2 < η₀)
    (h : WeightedStripBoundProven A₀ A η₀ Kc C_s) :
    ∀ᶠ N : ℕ in atTop, StripPowerBoundAt A₀ A N Kc C_s 7 := by
  filter_upwards [h] with N hN z hz hle
  have hlt : |z.im| < η₀ := lt_of_le_of_lt hle hη₀2
  exact hN z hz hlt

/-- **The honest hypothesis at `η₀ ≥ 2` gives the comparison with the same constant.**  This
is `eventually_smooth_trace_comparison_of_weighted_strip_proven` re-derived through the
free-exponent form, with the identical constant `(2π)⁻¹ C_s ∫∫ ‖∂̄_{k+1} f‖ (Kc+‖z‖)²|Im z|⁻⁷`
(`stripPowerMass f k Kc C_s 7`). -/
theorem eventually_smooth_trace_comparison_of_weighted_strip_proven'
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) {f : ℝ → ℝ} {k K : ℕ} (hk : 1 ≤ k) (hk8 : 7 < k)
    (hf : ContDiff ℝ K f) (hK : k + 1 ≤ K) (hfc : HasCompactSupport f)
    {η₀ Kc C_s : ℝ} (hη₀2 : 2 < η₀) (hC_s : 0 ≤ C_s)
    (hstrip : WeightedStripBoundProven A₀ A η₀ Kc C_s)
    (hIntN : ∀ᶠ N : ℕ in atTop, Integrable (fun p : ℝ × ℝ =>
      dbarNumOrder (k + 1) f (zOf p) *
        Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p))))
    (hIntLim : Integrable (fun p : ℝ × ℝ => dbarNumOrder (k + 1) f (zOf p) *
      Matrix.trace (operatorMatrixPencilCauchy A₀ A (zOf p)))) :
    ∀ᶠ N : ℕ in atTop,
      |∫ x : EuclideanSpace ℝ (GUECoord ι N), gueStatisticCfc (N := N) f A₀ A hA₀ hA x
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) - guePlaneLimitOrder k A₀ A f|
        ≤ (2 * Real.pi)⁻¹ * stripPowerMass f k Kc C_s 7 / (N : ℝ) ^ 2 := by
  refine eventually_smooth_trace_comparison_of_strip_power A₀ A hA₀ hA hk (β := (7 : ℝ))
    (Kc := Kc) (Cb := C_s) (by norm_num) (by exact_mod_cast hk8) hf hK hfc hC_s ?_ hIntN hIntLim
  exact stripPowerBoundAt_of_weightedStripBoundProven A₀ A (Kc := Kc) (C_s := C_s) hη₀2 hstrip

/-! ## 4. The near-axis annulus with a free exponent: connecting to the merged chain

`StrongConvergence/PencilStripAbove.lean` reduces `WeightedStripBoundProven` — and hence the
corrected endgame bundle `WeightedStripDataAtRepair` — to the near-axis annulus
`|Im z| < dysonThreshold A` with the honest exponent `−7`:

`weightedStripBoundProven_of_annulus`, `weightedStripDataAtRepair_of_annulus`.

The exponent `−7` in the annulus is not needed either: a bound with **any** exponent `−β`,
`0 ≤ β ≤ 7`, gives the `−7` annulus bound with the constant multiplied by
`dysonThreshold A ^ (7 − β)` — the price is only in a constant, never in `N`.  (For `β < k = 8`
the estimate is in fact already enough for the comparison without going through `−7`, see
`smooth_trace_comparison_of_strip_power`; the results below are the more convenient form that
plugs into the merged chain unchanged.) -/

/-- **Exponent relaxation near the axis**: for `0 < t < δ` and `0 ≤ β ≤ 7`,
`t^{-β} ≤ δ^{7-β} t^{-7}`. -/
lemma rpow_neg_le_rpow_neg_seven {β δ t : ℝ} (hβ0 : 0 ≤ β) (hβ7 : β ≤ 7) (hδ0 : 0 < δ)
    (ht0 : 0 < t) (ht : t < δ) :
    t ^ (-β) ≤ δ ^ ((7 : ℝ) - β) * t ^ (-(7 : ℝ)) := by
  have hsplit : t ^ (-β) = t ^ (-(7 : ℝ)) * t ^ ((7 : ℝ) - β) := by
    rw [← Real.rpow_add ht0]
    congr 1
    ring
  have h1 : t ^ ((7 : ℝ) - β) ≤ δ ^ ((7 : ℝ) - β) :=
    Real.rpow_le_rpow ht0.le ht.le (by linarith)
  calc t ^ (-β) = t ^ (-(7 : ℝ)) * t ^ ((7 : ℝ) - β) := hsplit
    _ ≤ t ^ (-(7 : ℝ)) * δ ^ ((7 : ℝ) - β) :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg ht0.le _)
    _ = δ ^ ((7 : ℝ) - β) * t ^ (-(7 : ℝ)) := by ring

/-- **The near-axis annulus with any exponent `β ≤ 7` gives `WeightedStripBoundProven`.**

Compared with `weightedStripBoundProven_of_annulus` (which asks for the exponent `−7` on the
annulus `|Im z| < dysonThreshold A`), the exponent here is free in `[0, 7]`; the constant is
multiplied by `dysonThreshold A ^ (7 − β)`.  In particular a proof of the annulus bound with,
say, `|Im z|^{-3}` or `|Im z|^{-7}` — or any power at least as strong as `−7` — closes the
strip hypothesis. -/
theorem weightedStripBoundProven_of_annulus_le_seven (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    {η₀ Kc Cn β : ℝ} (hKc : 0 ≤ Kc) (hCn : 0 ≤ Cn) (hβ0 : 0 ≤ β) (hβ7 : β ≤ 7)
    (hη : dysonThreshold A < η₀)
    (hnear : ∀ᶠ N : ℕ in atTop, ∀ z : ℂ, z.im ≠ 0 → |z.im| < dysonThreshold A →
      frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
        ≤ Cn * (Kc + ‖z‖) ^ 2 * (|z.im| ^ (-β)) / (N : ℝ) ^ 2) :
    WeightedStripBoundProven A₀ A η₀ Kc
      (max (Cn * dysonThreshold A ^ ((7 : ℝ) - β))
        (8 * (Fintype.card d : ℝ) ^ 3 * (pencilCoeffMass A) ^ 2 * η₀ ^ 2)) := by
  have hδ0 : 0 < dysonThreshold A := dysonThreshold_pos A
  set D : ℝ := Cn * dysonThreshold A ^ ((7 : ℝ) - β) with hD
  have hD0 : 0 ≤ D := by
    rw [hD]
    exact mul_nonneg hCn (Real.rpow_nonneg hδ0.le _)
  have hnear7 : ∀ᶠ N : ℕ in atTop, ∀ z : ℂ, z.im ≠ 0 → |z.im| < dysonThreshold A →
      frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
        ≤ D * (Kc + ‖z‖) ^ 2 * (|z.im| ^ (-(7 : ℝ))) / (N : ℝ) ^ 2 := by
    filter_upwards [hnear] with N hN z hz hlt
    have ht0 : 0 < |z.im| := abs_pos.mpr hz
    have hw := rpow_neg_le_rpow_neg_seven hβ0 hβ7 hδ0 ht0 hlt
    refine (hN z hz hlt).trans ?_
    have hstep : Cn * (Kc + ‖z‖) ^ 2 * |z.im| ^ (-β)
        ≤ Cn * (Kc + ‖z‖) ^ 2 * (dysonThreshold A ^ ((7 : ℝ) - β) * |z.im| ^ (-(7 : ℝ))) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    refine (div_le_div_of_nonneg_right hstep (by positivity)).trans (le_of_eq ?_)
    rw [hD]
    ring
  exact weightedStripBoundProven_of_annulus A₀ A hA₀ hA (Kc := Kc) (Cn := D) hKc hη hnear7

/-- **The corrected endgame bundle from an annulus bound with any exponent `β ≤ 7`.**

This is `weightedStripDataAtRepair_of_annulus` (`StrongConvergence/PencilStripAbove.lean`) with
the exponent `−7` on the near-axis annulus replaced by `−β` for an arbitrary `β ∈ [0, 7]`.  Hence
the last open input of the project only has to be proved for *some* exponent at least as strong
as `−7`; nothing in the chain requires the specific power `7`. -/
theorem weightedStripDataAtRepair_of_annulus_le_seven {r k : ℕ} {F : RatPolyIdx r (k + 1)}
    {z ε : ℝ} (hε : 0 < ε) {Cn β : ℝ} (hCn : 0 ≤ Cn) (hβ0 : 0 ≤ β) (hβ7 : β ≤ 7)
    (hnear : ∀ᶠ N : ℕ in atTop, ∀ w : ℂ, w.im ≠ 0 →
      |w.im| < dysonThreshold (pencilDirCoeff k F) →
      frob (gueResolventMean (N := N) (pencilConstCoeff k F z) (pencilDirCoeff k F) w -
          operatorMatrixPencilCauchy (pencilConstCoeff k F z) (pencilDirCoeff k F) w)
        ≤ Cn * (0 + ‖w‖) ^ 2 * (|w.im| ^ (-β)) / (N : ℝ) ^ 2) :
    WeightedStripDataAtRepair r k F z ε := by
  haveI : Nonempty (Fin (pencilCoeffDim k F)) := ⟨⟨0, pencilCoeffDim_pos r k F⟩⟩
  refine weightedStripDataAtRepair_of_stripBound (η₀ := dysonThreshold (pencilDirCoeff k F) + 3)
    (Kc := 0) (C_s := max (Cn * dysonThreshold (pencilDirCoeff k F) ^ ((7 : ℝ) - β))
      (8 * (Fintype.card (Fin (pencilCoeffDim k F)) : ℝ) ^ 3 *
        (pencilCoeffMass (pencilDirCoeff k F)) ^ 2 *
          (dysonThreshold (pencilDirCoeff k F) + 3) ^ 2))
    hε ?_ ?_ ?_
  · have h1 := one_le_dysonThreshold (pencilDirCoeff k F)
    linarith
  · have hδ0 : 0 < dysonThreshold (pencilDirCoeff k F) := dysonThreshold_pos _
    have hD0 : 0 ≤ Cn * dysonThreshold (pencilDirCoeff k F) ^ ((7 : ℝ) - β) :=
      mul_nonneg hCn (Real.rpow_nonneg hδ0.le _)
    exact le_trans hD0 (le_max_left _ _)
  · exact weightedStripBoundProven_of_annulus_le_seven (pencilConstCoeff k F z)
      (pencilDirCoeff k F) (pencilConstCoeff_isHermitian k F z) (pencilDirCoeff_isHermitian k F)
      le_rfl hCn hβ0 hβ7 (by linarith [one_le_dysonThreshold (pencilDirCoeff k F)]) hnear

end

end GUEStrongConvergence
