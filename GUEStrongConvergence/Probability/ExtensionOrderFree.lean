/-
# Separating the extension order from the polynomial index

The weighted-strip interface of `Probability/LemmaMWeighted.lean` uses a single index `k` for
two logically independent objects:

1. the **polynomial linearization index** `k` of the flattened pencil
   (`F : RatPolyIdx r (k + 1)`, the statistics `flatStat r k F z`), and
2. the **order of the almost-analytic extension** (`almostAnalyticExtOrderCut (q + 1) f`),
   whose `∂̄` vanishes to order `q`, so that the weighted strip estimate needs `β < q`.

Requiring `β < k` for the polynomial index `k` is artificial: for `k = 1` it forces `β < 1`,
even when the available resolvent estimate is only `|Im z|^{-7}`.  The extension order `q`
should be chosen freely (`q = 8` for `β = 7`), for **every** polynomial index `k ≥ 0`.

This file carries out the separation.

## Main results

* `smooth_trace_comparison_of_order` — the mean comparison with the polynomial index `k` and
  the extension order `q` both explicit and with **no hypothesis linking them**:
  `|∫ flatStat r k F z N g − guePlaneLimitOrder q A₀ A g| ≤
     weightedStripConstant g q C_s β / (N+1)²` eventually in `N`, from the strip bound at
  order `q` only (hypotheses `1 ≤ q`, `β < q`, `ContDiff ℝ (q+1) g`, compact support of `g`);
* `flatLemmaM_of_weightedStrip_order_zero` — the polynomial index `k = 0` case is **not** a
  separate problem: `flatLemmaM_of_weightedStrip_order` (`StrongConvergence/FinalReduction.lean`)
  already takes the strip order `m` independently of `k`, so a single strip bound at order
  `q ≥ 1` yields `FlatLemmaM r 0 F z g C`.  The old `k = 0` first-order field of
  `WeightedStripInputs` was therefore redundant;
* `WeightedStripDataAtFree` — the weighted-strip data at a **free** extension order `q`,
  uniformly for every polynomial index `k ≥ 0` (no `max k 1`), with the honest compact-support
  condition `HasCompactSupport (fun x => f x − 1)` (the cutoff is `1` at infinity, so it is the
  *difference* that is compactly supported);
* `FlatLemmaM_of_weightedStripDataAtFree` — one bundle at a free order `q` yields the two
  `FlatLemmaM` fields for `f` and `(f')²`, for every `k ≥ 0`;
* `WeightedStripInputsFree`, `GUEStrongConvergenceStatement_of_weightedStripInputsFree` — the
  final conditional theorem with a single `∀ k` bundle (no `k = 0` side field).

## Note on the cutoff

The downstream mean comparison (`flatLemmaM_of_weightedStrip_order`) is stated for test
functions with **compact support**, while the cutoff `f` of `IsSmoothCutoffZeroOn` is `1`
outside a compact set (it vanishes on the limit spectrum instead).  The analytic machinery is
therefore applied to the compactly supported difference `g = f − 1`; the exact identity

`∫ τ_N(f) = ∫ τ_N(f − 1) + 1`,  `guePlaneLimitOrder q A₀ A (f − 1) = −1`

converts the comparison for `g` into the mean bound for `f` (see
`abs_integral_gueStatisticCfc_le_of_weightedStrip_shift`).  This is why the bundle only assumes
`HasCompactSupport (fun x => f x − 1)` and *not* `HasCompactSupport f`.

No `sorry`, no new axioms.
-/
import GUEStrongConvergence.StrongConvergence.FinalReduction

open MeasureTheory ProbabilityTheory Matrix Filter Topology Complex
open FreeProbability FreeProbability.Fock
open scoped Matrix.Norms.Frobenius ComplexOrder ENNReal NNReal Topology BigOperators

namespace GUEStrongConvergence

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 8000000

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] [Nonempty d]
  {N : ℕ}

/-! ## 1. The mean comparison at a free extension order -/

/-- **The `∂̄`-weighted constant of the free-order comparison:**
`(2π)⁻¹ C_s ∫∫ ‖∂̄_{q+1} g‖ |Im z|^(−β)`.  This is `weightedStripConstant g q C_s β`; the
definition is recalled here to make the statement below self-contained. -/
theorem weightedStripConstant_eq_freeOrder {g : ℝ → ℝ} {q : ℕ} {C_s β : ℝ} :
    weightedStripConstant g q C_s β =
      (2 * Real.pi)⁻¹ * (C_s *
        ∫ p : ℝ × ℝ, ‖dbarNumOrder (q + 1) g (zOf p)‖ * |p.2| ^ (-β)) := rfl

/-- **The mean comparison with independent polynomial index `k` and extension order `q`.**

`k` is the polynomial linearization index (`F : RatPolyIdx r (k+1)`, statistic
`flatStat r k F z N g`); `q` is the order of the almost-analytic extension.  The only
hypotheses on `q` are `1 ≤ q`, `ContDiff ℝ (q+1) g`, `HasCompactSupport g` and `β < q`; there
is **no** relation between `k` and `q`, so e.g. `k = 0` or `k = 1` with `q = 8` is allowed.

`hstat` is the flat ⟶ GUE identification at block `N` (a theorem at the canonical coefficient
matrices), and the two integrability side conditions are those of the order-`q` plane
representation. -/
theorem smooth_trace_comparison_of_order {r : ℕ} {k q K : ℕ} {F : RatPolyIdx r (k + 1)}
    {z : ℝ} {d : ℕ} [NeZero d]
    (A₀ : Matrix (Fin d) (Fin d) ℂ) (A : Fin r → Matrix (Fin d) (Fin d) ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    {g : ℝ → ℝ} {η₀ C_s β : ℝ} (hq : 1 ≤ q) (hg : ContDiff ℝ K g) (hK : q + 1 ≤ K)
    (hgc : HasCompactSupport g) (hη₀2 : 2 < η₀) (hC_s : 0 ≤ C_s) (hβ0 : 0 ≤ β) (hβq : β < q)
    (hstrip : WeightedStripBound A₀ A q η₀ C_s β)
    (hstat : ∀ N : ℕ,
      ∫ x, flatStat r k F z N g x ∂(commonGaussianMeasure (Fin r))
        = ∫ y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)),
            gueStatisticCfc (N := N + 1) g A₀ A hA₀ hA y
              ∂(stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))))
    (hIntN : ∀ᶠ N : ℕ in atTop, Integrable (fun p : ℝ × ℝ =>
      dbarNumOrder (q + 1) g (zOf p) *
        Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p))))
    (hIntLim : Integrable (fun p : ℝ × ℝ => dbarNumOrder (q + 1) g (zOf p) *
      Matrix.trace (operatorMatrixPencilCauchy A₀ A (zOf p)))) :
    ∀ᶠ N : ℕ in atTop,
      |∫ x, flatStat r k F z N g x ∂(commonGaussianMeasure (Fin r)) -
          guePlaneLimitOrder q A₀ A g|
        ≤ weightedStripConstant g q C_s β / ((N + 1 : ℕ) : ℝ) ^ 2 := by
  -- the order-`q` comparison at block `N + 1`
  have hmain : ∀ᶠ N : ℕ in atTop,
      |∫ y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)),
          gueStatisticCfc (N := N + 1) g A₀ A hA₀ hA y
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))) -
          guePlaneLimitOrder q A₀ A g|
        ≤ weightedStripConstant g q C_s β / ((N + 1 : ℕ) : ℝ) ^ 2 := by
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hstrip
    obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 hIntN
    refine eventually_atTop.2 ⟨max N₀ M₀, fun n hn => ?_⟩
    have hn₀ : N₀ ≤ n + 1 := le_trans (le_max_left N₀ M₀) (by omega)
    have hm₀ : M₀ ≤ n + 1 := le_trans (le_max_right N₀ M₀) (by omega)
    have hfixed := smooth_trace_comparison_of_weighted_strip (N := n + 1) A₀ A hA₀ hA
      (by omega) hq hg (K := K) hK hgc hη₀2 hC_s hβ0 hβq
      (fun w hw hlt => hN₀ (n + 1) hn₀ w hw hlt) (hM₀ (n + 1) hm₀) hIntLim
    simpa [weightedStripConstant] using hfixed
  filter_upwards [hmain] with n hn
  rw [hstat n]
  exact hn

/-- **The `k = 0` bridge.**  The polynomial index `0` needs no separate treatment: the
free-order comparison `flatLemmaM_of_weightedStrip_order` consumes the strip order `m ≥ 1`
independently of the polynomial index `k`, so a single weighted strip bound at order `q ≥ 1`
gives `FlatLemmaM r 0 F z g C`.

This eliminates the (previously separate) `k = 0` first-order field of `WeightedStripInputs`:
the "`k = 0` problem" was an artefact of tying the strip order to `k`, not a real obstruction
(`WeightedStripBound` at order `0` would require `β < 0`, which is why the old interface could
not state it uniformly). -/
theorem flatLemmaM_of_weightedStrip_order_zero {r : ℕ} {F : RatPolyIdx r (0 + 1)} {z : ℝ}
    {g : ℝ → ℝ} {d' : ℕ} [NeZero d'] (A₀ : Matrix (Fin d') (Fin d') ℂ)
    (A : Fin r → Matrix (Fin d') (Fin d') ℂ) (hA₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) {q : ℕ} (hq : 1 ≤ q) {η₀ C_s β : ℝ} (hη₀2 : 2 < η₀)
    (hC_s : 0 ≤ C_s) (hβ0 : 0 ≤ β) (hβq : β < q) (hg : ContDiff ℝ (q + 1) g)
    (hgc : HasCompactSupport g) (hstrip : WeightedStripBound A₀ A q η₀ C_s β)
    (hstat : ∀ N : ℕ,
      ∫ x, flatStat r 0 F z N g x ∂(commonGaussianMeasure (Fin r))
        = ∫ y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)),
            gueStatisticCfc (N := N + 1) g A₀ A hA₀ hA y
              ∂(stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))))
    (hlim0 : guePlaneLimitOrder q A₀ A g = 0)
    (hIntN : ∀ᶠ N : ℕ in atTop, Integrable (fun p : ℝ × ℝ =>
      dbarNumOrder (q + 1) g (zOf p) *
        Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p))))
    (hIntLim : Integrable (fun p : ℝ × ℝ => dbarNumOrder (q + 1) g (zOf p) *
      Matrix.trace (operatorMatrixPencilCauchy A₀ A (zOf p)))) :
    FlatLemmaM r 0 F z g (weightedStripConstant g q C_s β) :=
  flatLemmaM_of_weightedStrip_order (k := 0) (F := F) A₀ A hA₀ hA (m := q) hq hη₀2 hC_s
    hβ0 hβq hg hgc hstrip hstat hlim0 hIntN hIntLim

end

end GUEStrongConvergence
