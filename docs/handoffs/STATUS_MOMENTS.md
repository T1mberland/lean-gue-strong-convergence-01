# STATUS — probability / moment side (Worker A, branch `feat/moment-audit`)

All statements below are kernel-checked (`lake env lean -DautoImplicit=false`), axioms only
`propext`, `Classical.choice`, `Quot.sound`. New files only; root module list untouched.

## (i) Moment-limit theorems that are HYPOTHESIS-FREE (unconditional in `r`)

| declaration | file | statement |
| --- | --- | --- |
| `hblock` | `Probability/GUEBlockSplitFinal.lean:652` | block-diagonal factorization of the two-walk slot sum (was a hypothesis of `GUEAllWords`) |
| `ae_all_words_gueNormTrace_genusSum_unconditional` | `Probability/GUEBlockSplitFinal.lean:662` | one `∀ᵐ` event: every `w` has `τ_N(w) → wordLimit w` |
| `ae_all_words_gueNormTrace_tau_unconditional r` | `StrongConvergence/FreeMomentBridgeProof.lean:257` | same, with limit `tau r w` (target shape `hWords`) |
| `ae_all_traceWord_moments_converge` / `_tau` (new) | `Probability/MomentStatus.lean` | capstone restatements of the two above |
| `norm_genus_sum_sub_limit_le` (new) | `Probability/GenusSecondOrder.lean` | abstract 2nd-order genus lemma |
| `abs_integral_gueNormTrace_sub_wordLimit_le_inv_sq` (new) | `Probability/GenusSecondOrder.lean` | mean error `≤ (∑_p ‖label_p‖)/N²`, no `1/N` term |
| `integral_gueNormTrace_eq_wordLimit_of_odd` (new) | `Probability/GenusSecondOrder.lean` | odd words: mean `=` limit exactly, all `N ≥ 1` |

The countable intersection over words is `MeasureTheory.ae_all_iff` (already in `GUEAllWords`).
**Verdict: target part II.B (moment side) is unconditional.** Nothing is missing.

## (ii) What is still gated

Exactly one bundle: `WeightedStripInputsFinal r` (`StrongConvergence/FinalReduction.lean:659`),
via `GUEStrongConvergenceStatement_of_weightedStripInputsFinal`; equivalently the pair
(`H1CanonicalDilated r`, `ScalarSpectralInclusion r`) in `FinalWiring.lean:337`. Its core is
`WeightedStripBound` (`Probability/LemmaMWeighted.lean:123`): pointwise
`frob (g_N z − g z) ≤ C_s |Im z|^{−β}/N²` for **all** `0 < |Im z| < η₀`, with `0 ≤ β < max k 1`
(so `β < 1` for `k = 0` and the scalar field `ScalarWeightedStripDataAt`).

## (iii) Vacuity defects — audit verdict

* Not circular: `WeightedStripBound` is about the **expectation** `E[partial tr (z−H)^{−1}]`,
  not an a.s. norm statement, so it is not implied by (nor equivalent to) the conclusion.
* **But it is pointwise-stronger than the truth.** The sharp Dyson estimate proves
  `frob(g_N − g) ≤ 8 d⁴√d (∑ frob A_i²)² |Im z|^{−5}/N²` only under
  `(Im z)² ≥ 2 d² ∑ frob A_i²` (`DysonLimitSharp.frob_gueResolventMean_sub_limit_le_sharp`).
  At the Airy edge scale `|Im z| ≍ N^{−2/3}` the mean resolvent differs from its limit by
  `N^{−1/3}`-type terms, while the required RHS is `C_s N^{2β/3−2} ≤ C_s N^{−4/3}` for `β < 1`.
  So the bound, as a statement about *all* `z` in the strip, is **likely false** (the integrated
  form actually used is plausibly true: the near-real layer has measure `N^{−4/3}` and the
  cut-off's `∂̄` vanishes like `d²` there). Hence the conditional endgame is at risk of being
  vacuous. New Lean facts pinning the gap: `WeightedStripBoundIn`,
  `weightedStripBound_iff_in` (near-real region vs away region),
  `frob_gueResolventMean_sub_limit_le_of_ge` (positive-imaginary away region is a theorem),
  `WeightedStripResidual` + `weightedStripBound_of_residual_and_awayPos` (the residual is exactly
  `{|Im z| < c}` plus the negative-imaginary away half; the latter needs the adjoint symmetry).

## (iv) Mixed traces (matrix coefficients): CORRECTED verdict — **no `1/N` term**

Earlier note in this file claimed `E τ(A X B X) = τ(AB)/N`; that was wrong (the contraction
orientation was misidentified). The single GUE covariance is `E[X_ab X_cd] = δ_ad δ_bc / N`
(`integral_gueMatrix_mul`), so for `tr(A X B X)` the two `X`'s contract on **both** index pairs
and each coefficient only sees its diagonal:

  `E tr(A X B X) = N⁻¹ (Σ_a A_aa)(Σ_l B_ll) = N⁻¹ tr(A) tr(B)`,

i.e. `E τ_N(A X B X) = τ_N(A) τ_N(B)` **exactly, for every `N`**, with no `1/N` correction.
Kernel-checked in new file `Probability/MixedSecondMoment.lean`:

* `integral_trace_mul_gueMatrix_mul_gueMatrix (A B) (i) :
    ∫ x, tr(A * gueMatrix x i * B * gueMatrix x i) = (N:ℂ)⁻¹ * tr A * tr B`
* `integral_normalizedTrace_mul_gueMatrix_mul_gueMatrix (A B) (i) :
    ∫ x, (N:ℂ)⁻¹ * tr(A X B X) = ((N:ℂ)⁻¹ * tr A) * ((N:ℂ)⁻¹ * tr B)`
  (axions: propext/Classical.choice/Quot.sound only)

This matches `MixedTrace.lean:81 integral_gueNormalizedMixedTrace : E τ_N(G_i G_j) = δ_ij`
exactly for all `N`, and it means matrix-coefficient insertions do **not** consume an `N`-factor:
the `1/N` from the covariance is exactly compensated by the free diagonal sum. Consequence for the
pencil side: the mixed-trace mean is `N⁰`-accurate at this order, so it is **not** a source of
`1/N` errors, and the `N^{-2}` mean input of `FlatLemmaM` is combinatorially consistent with
matrix coefficients. Still open: the same exact genus form for longer mixed words
(`N^{-(m+1)} Σ_p label_p N^{c(p)}` with `label_p` a product of block traces), and the
adjoint/reflection symmetry needed to remove the negative-imaginary residual of
`WeightedStripResidual` (`MomentStatus.lean`).

## (v) Mixed genus form — length-4 exact mean and what remains

**The length-4 mixed mean (derived, and normalization-checked in Lean).**  With
`E[X_ab X_cd] = δ_ad δ_bc / N`, the three Wick pairings of `tr(A X B X C X D X)` contract to

| pairing | index constraints | value |
| --- | --- | --- |
| `(12)(34)` (non-crossing) | `b=e, d=c, f=a, h=g` | `tr(AC) tr(B) tr(D)` |
| `(14)(23)` (non-crossing) | `b=a, h=c, d=g, e=f` | `tr(A) tr(C) tr(BD)` |
| `(13)(24)` (crossing) | `b=g, c=f, d=a, e=h` | `tr(ADCB)` |

so `E tr(A X B X C X D X) = N⁻² ( tr(AC)tr(B)tr(D) + tr(A)tr(C)tr(BD) + tr(ADCB) )`
(`MixedGenusForm.lengthFourMixedRHS`).  The two non-crossing terms carry three traces (= three
faces, `m+1 = 3`), the crossing term only one, and `c(p) ≤ m-1 = 1`: **the `pairOrbitCount`
exponent is the scalar one and the label of a pairing is the product of the traces of the
coefficient products around its faces.**  Kernel-checked consistency:
`lengthFourMixedRHS_one : lengthFourMixedRHS 1 1 1 1 = 2N + 1/N`, i.e. `E τ(X⁴) = 2 + 1/N²`,
matching the scalar Catalan value.  In the *dilated* normalization (`A = A_d ⊗ 1`, `τ = tr_{dN}/(dN)`)
the same computation gives `E τ_{dN} = (1/d) N^{-(m+1)} Σ_p (∏_{faces} tr_d) N^{c(p)}`, i.e. `O(1)`
with no `1/N` term.

**Analysis side is DONE (proved).**  `MixedGenusForm.mixedGenusMomentAccuracy`: for *any* word
whose exact genus expansion is available (hypothesis `hgenus`, as in `genus_limit`), the mean is
`N⁻²`-accurate with constant `∑_p ‖label_p‖`, using `norm_genus_sum_sub_limit_le`.  So no further
analysis is needed for the pencil side; only the exact expansion of the mixed word is missing.

**What the full genus form still needs (formalization, not mathematics):**
1. *Index-contraction collapses* — one finite-sum lemma per pairing, e.g.
   `Σ_{a..h} A_ab B_cd C_ef D_gh δ_be δ_dc δ_fa δ_hg = tr(AC)tr(B)tr(D)`.  These are `Finset`
   `sum_ite_eq` manipulations over 8 indices, one per pairing (3 for length 4, `(2m-1)!!` in
   general); mechanical but verbose.  The 2-generator analogue is done
   (`MixedSecondMoment.integral_trace_mul_gueMatrix_mul_gueMatrix`).
2. *Wick expansion with coefficients* — expressing `E ∏_{j} X_{...}` via
   `integral_gueProd_eq_gueWick` / `gueWick_four` before the collapses.
3. *Tensor bookkeeping* for the pencil — rewriting `A = A_d ⊗ 1`, `X = 1 ⊗ X_N` and splitting the
   trace into `tr_d` over faces times `N` per face, so that the `N`-exponent is literally
   `pairOrbitCount p - (m+1)` and the labels are `tr_d`-face products (bounded by
   `‖A‖^{deg}`).  This is where the `1/d` and `tr_d` of the dilated normalization enter.
The scalar case of 1–2 is already in the repo (`GUEWordMoments`, `GUEPairingCast`); the mixed
coefficient version is the missing piece.
