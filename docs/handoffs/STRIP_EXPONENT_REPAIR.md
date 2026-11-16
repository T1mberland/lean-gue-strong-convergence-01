# Strip exponent repair — `|Im z|⁻⁷` and extension order 8

## The defect
`WeightedStripDataAtFinal` (`FinalReduction.lean`) demands a pointwise bound
`frob (g_N(z) − g(z)) ≤ C_s |Im z|^(−β)/N²` for **every** `0 < |Im z| < η₀`, with `β < max k 1`
(so `β < 1` at `k = 0`).  The intended input (handoff §5.4, (5.15)–(5.16), HT05 Thm 5.7) is
`≤ 4C_A (K_A+|z|)² |Im z|⁻⁷/N²`, and the repo's own sharp Dyson estimate
(`frob_gueResolventMean_sub_limit_le_sharp`) gives only `|Im z|⁻⁵/N²`, and only for
`(Im z)² ≥ 2d²∑frob(A_i)²`.  So the bundle is not inhabited by the intended input.

## Exact exponent bookkeeping
* The transfer integrates `‖∂̄_{q+1} g(z)‖ · frob(deviation at z)` over the plane
  (`smooth_trace_comparison_of_weighted_strip`, `dbarNumOrder`, `zOf`).
* `‖∂̄_{q+1} g‖ ≤ |Im z|^q / q! · M` near the real axis
  (`norm_dbar_almostAnalyticExtOrderCut_le`); the extension order is `q`, regularity `C^{q+1}`.
* With the honest exponent `β`, the integrand is `O(|Im z|^{q−β})`; `∫_0 |t|^{q−β}dt < ∞` iff
  `β < q + 1`.  The code's *bounded-majorant* route (`integrable_norm_dbarNumOrder_mul_rpow_neg`)
  proves this under the sufficient condition `β < q`.
* Hence `β = 7` needs `q ≥ 8` (regularity `C⁹`); the handoff itself says "choose `k = 8` to
  avoid borderline conventions".  The polynomial index `k` must **not** enter this condition.
* `β < k` is used *only* to prove finiteness of the weighted `∂̄` mass (and hence integrability
  of the majorant); nothing downstream uses it (`FlatLemmaM` carries an arbitrary constant).
  So it is a real analytic requirement, but one on the *extension order*, not on `k`.

## Corrected hypothesis (stated, not proved)
`WeightedStripBoundProven A₀ A η₀ K C_s` (`StrongConvergence/WeightedStripRepair.lean`):
`∀ᶠ N, ∀ z, z.im ≠ 0 → |z.im| < η₀ → frob (g_N z − g z) ≤ C_s (K + ‖z‖)² |z.im|⁻⁷ / N²`
— exactly (5.15) with `(K_A+|z|)²` kept; the weight is harmless on the compact support of `∂̄`.

## Proved in Lean (branch `feat/strip-exponent`)
* `WeightedStripRepair.lean`: `integrable_norm_dbarNumOrder_mul_polyWeight_rpow_neg(_seven)`
  (weighted `∂̄` mass finite at `β = 7`, `q = 8`), `smooth_trace_comparison_of_weighted_strip_proven`,
  `eventually_smooth_trace_comparison_of_weighted_strip_proven`,
  `eventually_abs_integral_gueStatisticCfc_le_of_weighted_strip_proven`, with the explicit
  constant `weightedStripConstantProven`.
* `WeightedStripRepairBundle.lean`: `flatLemmaM_of_weightedStripProven` (honest bound at any
  order `m ≥ 8` ⟹ `FlatLemmaM`), `limitTraceCfcC_sub_one_eq_neg_one`,
  `guePlaneLimitOrder_sub_one_eq_neg_one`, `integral_flatStat_sub_one`,
  `flatLemmaM_of_weightedStripProven_sub_one` (`FlatLemmaM` for the cutoff `f` itself, via
  `g = f − 1`).  Axioms: propext/Classical.choice/Quot.sound only.

## Remaining gap
`WeightedStripDataAtRepair` / `WeightedStripInputsRepair` and
`WeightedMeanInputs_of_weightedStripRepair` (and the scalar field ⟹
`GUEStrongConvergenceStatement_of_weightedStripRepair`) are **not** yet formalized: the bundle
definition needs the local `CStarAlgebra (h1Alim r k F)` instance that `FinalReduction.lean`
keeps private, and the first producer draft timed out.  The scalar `ScalarWeightedStripDataAt`
(`β < 1`, order 1) has the same defect and needs the same treatment.
