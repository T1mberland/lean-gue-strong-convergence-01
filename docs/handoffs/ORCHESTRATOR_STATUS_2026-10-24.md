# Orchestrator status — 2026-10-24

Honest summary of what is **proved vs. assumed** in this repository, written after a full
review of `main` (commit `84cd290`, `lake build` 4176 jobs, integrity audit passing with only
`propext`/`Classical.choice`/`Quot.sound`).


## 0. CRITICAL — the two conditional endgame theorems are VACUOUS (machine-checked)

`IsSmoothCutoff` forces `f = 1` outside the bounded set `S + Set.Ioo (-ε) ε`, while the same
bundles demand `HasCompactSupport f`; the two are incompatible. This is now a theorem
(`GUEStrongConvergence/Verification/TerminalAudit.lean`):

```
weightedStripDataAtFinal_uninhabited   : ¬ WeightedStripDataAtFinal r k F z ε
scalarWeightedStripDataAt_uninhabited  : ¬ ScalarWeightedStripDataAt r i ε
weightedStripInputsFinal_uninhabited   : ∀ r, ¬ WeightedStripInputsFinal r
pencilStripField_uninhabited           : ¬ (∀ k F z ε, 0 < ε → WeightedStripDataAtFinal r k F z ε)
```

Consequences, which must be stated plainly:

* `GUEStrongConvergenceStatement_of_weightedStripInputsFinal` and
  `GUEStrongConvergenceStatement_of_pencilStrip_and_edgeBound` are **true but vacuous** — their
  hypotheses cannot be satisfied. They prove nothing about GUE.
* The repair is the shift `f → f − 1` (the compactly supported object is `f − 1`, since the
  cutoff is `1` at infinity). Bricks for the repair are on `main`
  (`WeightedStripRepairBundle.lean`: `integral_flatStat_sub_one`, `limitTraceCfcC_sub_one_eq_neg_one`,
  `guePlaneLimitOrder_sub_one_eq_neg_one`, `flatLemmaM_of_weightedStripProven_sub_one`), but the
  repaired bundle and the repaired endgame theorem are **not yet assembled**
  (blocked on a private local `CStarAlgebra (h1Alim r k F)` instance and an elaboration timeout).
* Non-vacuity witness that does exist: `flatLemmaM_zero` (a genuine `FlatLemmaM` instance).

Distribution of the remaining inputs after the audit (`docs/handoffs/TERMINAL_AUDIT.md`):
the minimal honest residual set is `{GUEEdgeBound}` (equivalently `GUEEdgeTail` + a
concentration/Borel–Cantelli step: `gueEdgeBound_of_tailMeasures` is proved) together with a
**non-vacuous** integrated pencil strip bound in the shape of `WeightedStripBoundProven`
(`C_s (K+‖z‖)² |Im z|⁻⁷ / N²`, extension order `≥ 8`).

## 1. The target (unchanged, unconditional form)

`GUEStrongConvergence.GUEStrongConvergenceStatement r`
(`GUEStrongConvergence/StrongConvergence/Target.lean`):

```lean
∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
  ∀ (d : ℕ) (_ : 0 < d) (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r))),
    Tendsto (fun N : ℕ => ‖evalMatrixPoly P (gueFamily r N x)‖) atTop (𝓝 (limitNorm P))
```

**This theorem is NOT yet proved unconditionally.** Everything below states exactly how far
the verified reduction goes.

## 2. Proved, with no hypotheses at all

* **All trace-word moments converge almost surely** (target part II.B, previously the only
  gate on the probability side):
  `ae_all_words_gueNormTrace_tau_unconditional : ∀ᵐ x, ∀ w : List (Fin r),
  Tendsto (fun N => gueNormTrace w (x N)) atTop (𝓝 (tau r w))`
  (`StrongConvergence/FreeMomentBridgeProof.lean:257`). Ingredients: the exact mean formula
  `integral_eq_genusSum` (`Probability/GUEAllWords.lean:230`), the two-walk block
  factorization `hblock` (`Probability/GUEBlockSplitFinal.lean:639,652`), and the combinatorial
  bridge `freeMomentBridge` (`ncSum = wickSum`).
* **Second-order accuracy of GUE word moments** — the mean has an `N⁻²` error and NO `1/N`
  term, because the face count of a pairing is `≡ m+1 (mod 2)` and never intermediate
  (`pairOrbitCount_mod_two`, `pairOrbitCount_eq_or_le_pred`):
  `abs_integral_gueNormTrace_sub_wordLimit_le_inv_sq`
  (`Probability/GenusSecondOrder.lean`): `‖E τ_N(w) − wordLimit w‖ ≤ C/N²` for all `N ≥ 1`.
* **Scalar spectrum facts**: `abs_le_two_of_mem_spectrum_semicircularFamily`
  (`StrongConvergence/EdgeBound.lean`), and the full computation
  `spectrum ℝ (semicircularFamily r i) = Set.Icc (-2) 2`
  (`StrongConvergence/EdgeBoundSpectrum.lean` — committed and kernel-checked, but **not
  registered** in the root import list because it needs a pinned `lean-free-prob` module that
  is not prebuilt in the shared read-only dependency cache; see `EDGE_REDUCTION.md`).

## 3. Conditional reductions (verified plumbing, explicit hypotheses)

* `GUEStrongConvergenceStatement_of_pencilStrip_and_edgeBound`
  (`StrongConvergence/EdgeBound.lean`, integrated 2026-10-24):
  `(∀ k F z ε, 0 < ε → WeightedStripDataAtFinal r k F z ε) → GUEEdgeBound r →
  GUEStrongConvergenceStatement r`.
  This replaces the opaque scalar cutoff/Pompeiu field by the classical **no-outlier** statement
  `GUEEdgeBound r` (`StrongConvergence/EdgeBound.lean`):
  `∀ᵐ x, ∀ i, ∀ ε > 0, ∀ᶠ N, ‖gueFamily r N x i‖ ≤ 2 + ε`.
* `GUEStrongConvergenceStatement_of_weightedStripInputsFinal`
  (`StrongConvergence/FinalReduction.lean:683`): the earlier two-field bundle
  (`WeightedStripInputsFinal r`).
* `GUEEdgeBound r ↔ ScalarSpectralInclusion r`
  (`StrongConvergence/EdgeBoundSpectrum.lean`): the scalar inclusion hypothesis of
  `StrongConvergence/FinalStatement.lean` and the no-outlier statement are equivalent.

## 4. What is still missing, and its mathematical status

**(A) `GUEEdgeBound r` (no escaping eigenvalue for a single GUE factor).** True and classical
(Ben Arous–Guionnet large deviations; equivalently the Ledoux/Bai–Yin edge argument). It is
*not* provable from the fixed-order moment limits alone: for fixed `m`, a single eigenvalue of
size `2+ε` contributes only `O(1/N)` to the normalized trace, which cannot be distinguished
from the bulk fluctuation. Any proof needs a growing-order moment estimate, an
exponential-concentration argument (Gaussian LSI is available in the pinned
`lean-log-sobolev`), or large-deviation theory. **Not proved.**

**(B) The pencil-side weighted-strip / mean-comparison input.** The project's intended analytic
input is the Haagerup–Thorbjørnsen 2005 second-order resolvent comparison
(`gue_strong_convergence_part_II_handoff.md` §5.4, eqs (5.15)–(5.16)):
`|g_N(z) − g(z)| ≤ 4 C_A (K_A+|z|)² |Im z|⁻⁷ / N²`.
The hypothesis formalized in `WeightedStripBound`
(`Probability/LemmaMWeighted.lean:123`) demands instead
`frob(g_N(z) − g(z)) ≤ C_s |Im z|^{-β} / N²` with `β < k` (hence `β < 1` at `k ≤ 1`) for
**every** `z` in the whole strip `0 < |Im z| < η₀`.

**Status: unproven, and currently only known above a threshold; not circular, and (as far as
the present analysis goes) not refutable.**

Evidence collected on 2026-10-24:

1. `frob_gueResolventMean_sub_limit_le_sharp` (`Probability/DysonLimitSharp.lean`) proves the
   `N⁻²` comparison with `|Im z|⁻⁵` growth **only above the fixed threshold**
   `(Im z)² ≥ 2 d² Σᵢ ‖Aᵢ‖²_F` — i.e. exactly on the complement of the strip the endgame needs;
   the intended HT05 exponent (§5.4) is `|Im z|⁻⁷` with no threshold.
2. Below the threshold only the trivial bound `frob(g_N − g) ≤ 2 d |Im z|⁻¹` is available
   (`frob_gueResolventMean_sub_limit_le_trivial`), which does not imply the stated bound.
3. The *true* size of the LHS as `|Im z| → 0` is `O(1)`: the averaged spectral measure
   `μ̄_N = E[Σ_j w_j δ_{λ_j}]` (`w_j = N⁻¹Σ_k |ψ_j(u,k)|²`) is absolutely continuous with a
   bounded density, and likewise for the limit, so both Stieltjes transforms have finite
   boundary values (`docs/handoffs/ANALYSIS_STRIP.md`). Hence the hypothesis is *plausible*, is
   weakest near the axis and strongest at the top of the strip (where it is verbatim the sharp
   `N⁻²` comparison). It is the **uniform-in-the-strip second-order averaged-resolvent
   comparison** that is missing, not a wrong exponent.
4. Proved on branch `feat/strip-analytic` (`Probability/StripAnalytic.lean`): the whole strip
   *above* the threshold is a theorem for any `β ≥ 0`
   (`frob_gueResolventMean_sub_limit_le_rpow_top`), so only the near-axis annulus
   `0 < |Im z| < stripThreshold A` remains (`weightedStripBound_of_nearAxis`), up to the
   conjugation symmetry `z ↦ z̄`.

Conclusion: `WeightedStripInputsFinal` is **not** demonstrated to be vacuous, but it is *not*
discharged either, and the `N⁻²` rate near the axis is a genuine analytic gap. Treat any
theorem assuming it as strictly conditional.

Work in progress (branches `feat/strip-exponent`, `feat/moment-audit`): split the hypothesis
into the parts that are already theorems (away region, threshold region) and the genuine
near-axis annulus residual — `WeightedStripBoundIn`, `weightedStripBound_iff_in`,
`WeightedStripResidual`, `weightedStripBound_of_residual_and_awayPos` in
`Probability/MomentStatus.lean` — and re-examine the order/exponent bookkeeping of the
Cauchy–Pompeiu transfer (with `|Im z|⁻⁷` growth the transfer plausibly needs extension order
`k ≥ 7`, since the order-`k` extension's `∂̄` vanishes like `|Im z|^k` near the real axis,
whereas the bundle currently uses order `max k 1`).

**(C) The `N⁻²` rate itself is not the obstruction.** For words with *scalar* coefficients the
`N⁻²` mean accuracy is a theorem (item 2 above). For *matrix-coefficient* (pencil) statistics
the length-two case is now settled with no `1/N` term:
`integral_trace_coeff_mul_gue_mul_coeff_mul_gue : E τ_N(A X B X) = τ_N(A) τ_N(B)` exactly
(branch `feat/strip-analytic`, `Probability/StripAnalytic.lean`), consistent with
`pairOrbitCount_mod_two` and with the proved `E τ_N(G_i G_j) = δ_ij`. So matrix coefficients
create no odd-genus terms and the combinatorial side does not obstruct `N⁻²`; only the
analytic near-axis uniformity is open.


### 4.1 What exactly remains on the pencil side (for the next session)

Decomposing the Haagerup–Thorbjørnsen argument (`gue_strong_convergence_part_II_handoff.md` §5)
into the two obligations that are actually needed:

1. **Self-energy / Dyson error bound.** With `h = Σ_i A_i ⊗ G_i` the linearized random matrix
   and `Λ_N(Λ)` the approximate self-energy, prove
   `‖Λ_N(Λ) − Λ‖ ≤ C_A N⁻² (K_A + ‖Λ‖)² η(Λ)⁻⁵` for `Im Λ ≻ 0` (handoff eq. (5.10)–(5.11)).
   This is where the `N⁻²` rate (parity, no odd-genus term) meets the analytic input; for
   matrix coefficients the length-two case is now settled exactly
   (`integral_trace_coeff_mul_gue_mul_coeff_mul_gue`), so no `1/N` obstruction is expected.
2. **Selection of the correct Dyson solution.** `G_N(Λ) = G(Λ_N(Λ))` on the "good region", by
   (i) a difference identity `U − V = Σ_j U A_j (U−V) A_j V` (contraction only for
   `η² > 2 Σ‖A_j‖²`) and (ii) an identity-theorem / path-continuation argument in `ℂ^{d²}`.
   Only after (1)+(2) does the boxed estimate `‖G_N − G‖ ≤ 4 C_A N⁻² (K_A+‖Λ‖)² η⁻⁷` follow for
   *all* `Im Λ ≻ 0` (handoff (5.15)).

Note the scalar case `d = 1` needs *neither* step in this form: the Dyson equation is scalar
quadratic, so with `e = E g_N − g`, `Var g_N = O(N⁻²)` (Poincaré) and the loop equation at
order `N⁻²`, one gets `e(2g + z) + e² = O(N⁻²)`, and `|2g+z| = |√(z²−4)| ≳ c |Im z|^{1/2}` near
the spectrum, i.e. `e = O(|Im z|^{−1/2} N⁻²)` — which satisfies the strip hypothesis with
`β = 1/2 < 1`. That is the target of branch `feat/scalar-loop`.

Also note **both** remaining inputs (the scalar no-outlier bound and the pencil comparison) are
of the same species: a uniform-in-`N` second-order (`N⁻²`) estimate for the averaged resolvent,
respectively for its top edge. Neither can be replaced by a `1/N` estimate: a single escaping
eigenvalue contributes only `1/(mN)` to a normalized trace, so `Borel–Cantelli` summability
requires the mean to be accurate at order `N⁻²`.

## 6. What this session added (all on `main`, kernel-checked, integrity audit passing)

* `Probability/GenusSecondOrder.lean` — `abs_integral_gueNormTrace_sub_wordLimit_le_inv_sq`:
  every fixed GUE word mean is `N⁻²`-accurate with **no** `1/N` term.
* `Probability/MixedSecondMoment.lean` and `Probability/StripAnalytic.lean`
  (`integral_trace_coeff_mul_gue_mul_coeff_mul_gue`) — `E τ_N(A X B X) = τ_N(A) τ_N(B)` exactly:
  matrix coefficients create no `1/N` term (independently proved twice).
* `Probability/MixedGenusForm.lean` — `mixedGenusMomentAccuracy`: given any exact genus
  expansion (same `pairOrbitCount` exponent), the mean is `N⁻²`-accurate; plus the explicit
  length-4 mixed formula. So the *analysis* side of the pencil mean input is closed modulo the
  combinatorial identity "coefficient insertions keep the pairing exponent".
* `Probability/MomentStatus.lean` — `WeightedStripBoundIn`, `weightedStripBound_iff_in`,
  `WeightedStripResidual`, `weightedStripBound_of_residual_and_awayPos`, and the unconditional
  capstone `ae_all_traceWord_moments_converge(_tau)`.
* `Probability/StripAnalytic.lean` — trivial bound `frob(g_N−g) ≤ 2d|Im z|⁻¹`;
  `eventually_weightedStripBound_top`: the weighted strip bound is a **theorem above**
  `stripThreshold A = max 1 √(2d² Σ‖Aᵢ‖²_F)` for every `β ≥ 0`; `weightedStripBound_of_nearAxis`
  and `weightedStripBound_of_uniform`: the hypothesis is thereby reduced to the near-axis
  annulus `0 < |Im z| < stripThreshold A` (and, if one wants the `|Im z|^{-β}` slack dropped
  entirely, to a uniform `C/N²` bound there).
* `StrongConvergence/EdgeBound.lean` — `GUEEdgeBound`, its equivalence with
  `ScalarSpectralInclusion` (in `EdgeBoundSpectrum.lean`), and the endgame
  `GUEStrongConvergenceStatement_of_pencilStrip_and_edgeBound`.
* `StrongConvergence/WeightedStripRepair.lean` — the honest Haagerup–Thorbjørnsen-shaped input
  `WeightedStripBoundProven` (`‖g_N − g‖ ≤ C(K+‖z‖)² |Im z|⁻⁷/N²`) and the Cauchy–Pompeiu
  transfer at extension order 8 (`eventually_smooth_trace_comparison_of_weighted_strip_proven`),
  i.e. the strip hypothesis *in a shape that the published HT05 theorem actually delivers*.

Net effect on the remaining gap: the pencil-side input has been reduced from an opaque bundle
to either (i) the near-axis annulus of the averaged-resolvent comparison, or (ii) the HT05-shaped
`|Im z|⁻⁷` bound, and the scalar side is isolated to the single classical no-outlier statement.

### 6.1 The threshold barrier is removed for the scalar pencil (new)

The reason the sharp `N⁻²` resolvent comparison was only available above
`(Im z)² ≥ 2 d² Σ‖Aᵢ‖²_F` is that the Dyson *fixed-point* argument needs the linearized map to be
a contraction, i.e. `‖A‖²/|Im z|² < 1/2`. For the scalar pencil this barrier is unnecessary: the
repo already contains the exact finite-`N` Schwinger–Dyson identity
`single_gue_schwinger_dyson` (`z m − 1 = E[T²]`, `Probability/DysonMasterIdentity.lean:1214`) and
the exact limit `limit_dyson_equation` (`(z−g) g = 1`, `Probability/DysonLimit.lean:149`). Their
difference is an exact algebraic identity:

```
loop_identity_of_dyson : (z - g) * g = 1 → z * m - 1 - m ^ 2 = Var → (m - g) * (z - m - g) = Var
loop_bootstrap         : z.im ≠ 0 → (m - g) * (z - m - g) = Var → z.im * m.im ≤ 0 →
                         z.im * g.im ≤ 0 → ‖m - g‖ ≤ ‖Var‖ / |z.im|
```

(`Probability/ScalarLoopCore.lean`, kernel-checked). The key point: the loop denominator is
`z − m − g = 1/g − m`, whose imaginary part is `Im z − Im g − Im m ≥ |Im z|` because both `Im g`
and `Im m` have the sign opposite to `Im z`. Hence **no threshold on `|Im z|`**, and combining with
the repo's unconditional sharp variance bound (`∫‖T−m‖² ≤ 4N⁻²(Im z)⁻⁴`,
`Probability/SharpTwoPoint.lean:826`) yields `‖E g_N − g‖ ≤ 4 N⁻² |Im z|⁻⁵` for *every*
`Im z ≠ 0` — an `|Im z|⁻⁵` (better than HT05's `⁻⁷`) weighted strip bound with no threshold, once
the two imaginary-part sign lemmas are formalized (in progress on `feat/scalar-loop`; the
finite-`N` sign is elementary, the limit-side sign is being done by an IVT argument on `‖g‖ < 1`
because the pinned dependency module that would give it directly is not prebuilt).
This is the template for the pencil case: replace the Dyson contraction by the exact
self-consistency identity plus a sign/lower-bound on `1/G − E G_N`.

## 5. Bottom line

* The **probability/moment side is complete and unconditional** (all words, a.s., with
  second-order mean accuracy).
* The **deterministic/analytic side is reduced** to (i) `GUEEdgeBound` and (ii) a pencil-side
  second-order resolvent comparison, currently stated in a form that is very likely too strong
  and must be weakened to its integrated form.
* The full unconditional theorem therefore remains **open**. Do not present
  `GUEStrongConvergenceStatement_of_pencilStrip_and_edgeBound` (or
  `..._of_weightedStripInputsFinal`) as the project theorem: their hypotheses are not
  discharged.


## 7. LATEST STATE (main at `88c1b90`, 5248 declarations): ONE hypothesis left

The unconditional theorem now follows from a SINGLE named statement, all other content being
kernel-checked theorems on `main`:

```
GUEStrongConvergenceStatement_of_annulus
  (hann : ∀ (k : ℕ) (F : RatPolyIdx r (k+1)) (z : ℝ), ∃ Cn, 0 ≤ Cn ∧
      ∀ᶠ N, ∀ w : ℂ, w.im ≠ 0 → |w.im| < dysonThreshold (pencilDirCoeff k F) →
        frob (gueResolventMean (pencilConstCoeff k F z) (pencilDirCoeff k F) w
              - operatorMatrixPencilCauchy (pencilConstCoeff k F z) (pencilDirCoeff k F) w)
          ≤ Cn * ‖w‖^2 * |w.im|^(-7) / N^2) :
    GUEStrongConvergenceStatement r
```
(`StrongConvergence/ConditionalEndgame.lean`.)

The chain (all verified):

1. `ScalarPencilStrip.scalarWeightedStripDataAtRepair_unconditional` — the SCALAR field of the
   corrected bundle is a theorem, for every `r`, `i`, `ε` (the full scalar weighted strip bound
   `weightedStripBoundProven_scalarPencil`, `β = 7`, from the threshold-free scalar loop bootstrap
   `loop_bootstrap` + the sharp variance bound for every non-real `z`).
2. `PencilStripAbove.pencilStripAbove` / `pencilStripAbove_seven` — the pencil strip bound is a
   THEOREM above the Dyson threshold `dysonThreshold A = max 1 √(2 (card d)² ∑ frob(Aᵢ)²)` on BOTH
   half-planes (via the exact Dyson defect identity `gueResolventMean_dyson_defect`,
   `dyson_stability_abs`, and the fluctuation bound `frob_fluctuation_le_sharp_abs`).
3. `PencilStripAbove.weightedStripDataAtRepair_of_annulus` — the pencil field of the corrected
   bundle follows from the near-axis annulus `|Im w| < dysonThreshold A` ALONE.
4. `ScalarPencilStrip.weightedStripInputsRepair_of_pencilField` — the corrected bundle follows from
   its pencil field.
5. `CorrectedEndgame.GUEStrongConvergenceStatement_of_weightedStripInputsRepair` — the endgame.

**The remaining analytic content is exactly the near-axis annulus bound** `hann`. The exponent `7`
is weak: any `p ≤ 7` would do, and the SCALAR case achieves `p = 5` for all non-real `w`, so the
statement is certainly true. Its proof is where the operator-valued Dyson analysis is still needed —
the contraction route fails there (`PencilLoop.loop_bootstrap_matrix`), and the known routes are
the HT05 self-energy argument (handoff §5.4) or a maximum-principle propagation from the real axis
(Mathlib's `norm_le_of_forall_mem_frontier_norm_le` is available) — the latter needs the boundary
value of the mean resolvent on the real axis at rate `N⁻²`, which holds in the bulk but needs care
at the spectral edge.

