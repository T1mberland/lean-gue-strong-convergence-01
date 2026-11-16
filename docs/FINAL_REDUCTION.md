# Final reduction: what remains for `GUEStrongConvergenceStatement r`

This document records the *exact* current logical state of the project, so that any
future session can pick up the last step without re-deriving the reduction.

## The target

`StrongConvergence/Target.lean` defines `GUEStrongConvergenceStatement r` (a.s. strong
convergence of every fixed matrix-coefficient `*`-polynomial in the normalized GUE family,
`r` generators, matrix size `d × N`).

## What is proved unconditionally (main)

* **II.B, completely**: mean limit (`Probability/GUEPairingMapEntries.mean_limit`), the exact
  genus expansion, the block-diagonal factorization (`Probability/GUEBlockSplitFinal.hblock`),
  the sharp word variance, the free-moment bridge
  (`StrongConvergence/FreeMomentBridgeProof.freeMomentBridge`), and
  `ae_all_words_gueNormTrace_tau_unconditional` — the `hWords` input.
* **`hEdge`** (`StrongConvergence/CutoffExclusion.eventually_tupleNorm_gueFamily_le_of_scalarSpectralInclusion`)
  and **`hB`** (`StrongConvergence/FinalWiring.hB_of_*`) — both derived.
* **Final assembly**: `StrongConvergence/FinalWiring.GUEStrongConvergenceStatement_of_scalarSpectralInclusion`
  and `GUEStrongConvergenceStatement_of_scalarSpectralInclusion_and_lemmaSInputs`
  (in `StrongConvergence/FlattenPencil.lean`).
* **II.A estimates**: exact finite-`N` master identity, sharp `O(N⁻²)` two-point variance
  (affine and flattened pencils), limit Dyson equation, parametric stability, the sharp
  averaged-resolvent comparison, the Cauchy–Pompeiu plane representation (scalar, operator,
  measure forms), the finite- and limit-side Helffer–Sjöstrand representations, the order-`k`
  almost-analytic extension with weighted strip bounds, the smooth cutoff construction, and the
  growing-dimension spectral-exclusion lemma.
* **`hV`** for the flattened family: `StrongConvergence/FlatHVField.PencilLemmaSData_of_smoothCutoff_hV`.
* **`hZ`, `hWint`, `hW0`**: `StrongConvergence/FlatSideConditions`.

## The exact remaining hypothesis

`PencilLemmaSResidualInputs r` (resp. `hM`/`hWb` for `ScalarSpectralInclusion r`) needs, for
each `(k, F, z, ε > 0)`, a smooth cutoff `f` with

* `hM`: `∀ᶠ N, |∫ τ_N(f(ℒ_z))| ≤ C/N²`   — **Lemma M**, the smooth mean comparison;
* `hWb`: `∀ᶠ N, ∫ τ_N((f')²(ℒ_z)) ≤ C'/N²` — Lemma M applied to `(f')²`.

Everything else is a theorem. Note `hWb` follows from `hM` because `deriv f = 0` on `spec(h)`,
so `τ((f')²(h)) = 0`.

## Why Lemma M is the hard step (precise)

The Cauchy–Pompeiu / Helffer–Sjöstrand route reduces `hM` to

  `∫∫ |∂̄F(z)| · ‖g_N(z) − g(z)‖`,

and the sharp comparison `‖g_N(z) − g(z)‖ ≤ C|Im z|⁻⁵/N²` requires the stability ball condition
`2·frob g·frob g'·∑frob A_i² ≤ 1`. With the trivial `‖g‖ ≤ |Im z|⁻¹` this leaves a fixed strip
where only the trivial `2d/|Im z|` holds, whose contribution is a constant in `N` — for every
extension order. A pointwise `|Im z|^{−1/2}` bound does not help (the condition still has a fixed
threshold). What is needed is a bound on the inverse linearized Dyson map
`(1 − g·Σ A_i(·)A_i g')⁻¹` uniform in the bulk — equivalently the local law / bounded Stieltjes
transform of the limit spectral measure — which is absent from both this repository and
`lean-free-prob`. With `Probability/HigherExtension.norm_strip_integral_dbar_order_le`, *any*
coefficient bound `|y|^{-(β-1)}`, `β < k`, converts immediately into the `O(N⁻²)` estimate.

## Verification protocol

* Verify worker files with `lake env lean -DautoImplicit=false <file>` (plain `lake env lean`
  does **not** apply the lakefile's `autoImplicit := false`).
* Integration: `lake build`, then `lake build GUEStrongConvergenceVerification`, then
  `lake env lean GUEStrongConvergence/Verification/Integrity.lean` (rejecting audit).
