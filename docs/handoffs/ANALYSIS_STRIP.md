# Feasibility of `WeightedStripBound` — verdict (Worker B, branch `feat/strip-analytic`)

## The two sides
* `gueResolventMean A₀ A z = ∫ x, (N⁻¹ ∑_k R(z,x)_{(u,k),(v,k)}) dμ_G(x)`: the **Gaussian mean**
  of the normalized partial trace of the resolvent of the Hermitian pencil `A₀⊗1 + ∑ Aᵢ⊗Gᵢ`.
* `operatorMatrixPencilCauchy A₀ A z = φ_vac(resolvent (operatorMatrixPencil A₀ A) z)`: the
  operator-valued Cauchy transform of the **limit free-semicircular pencil** (Fock space), i.e.
  the deterministic limit object, replaced random `Gᵢ ↦` free semicircular operators.
* `frob` = entrywise ℓ² norm of a `d × d` matrix. LHS is measured in `frob`, `d` fixed.

## Size of the LHS (kernel-checked facts)
1. Trivial, both half-planes: `frob(g_N − g) ≤ 2 d |Im z|⁻¹` (new:
   `frob_gueResolventMean_sub_limit_le_trivial`).
2. Sharp `N⁻²` (`frob_gueResolventMean_sub_limit_le_sharp`): for `Im z > 0` and
   `2 d² ∑ᵢ‖Aᵢ‖²_F ≤ (Im z)²`,
   `frob(g_N − g) ≤ 8 d⁴ √d (∑‖Aᵢ‖²_F)² (Im z)⁻⁵ / N²`.
   So `1/N²` is **not** a typo: it is a theorem — but only above the **fixed** threshold
   `η_A = √(2 d² ∑‖Aᵢ‖²_F)`, i.e. exactly on the *complement* of the strip the endgame needs.
3. On `0 < |Im z| < η_A` nothing better than (1) is available, and (1) cannot imply the stated
   bound: `2d/|y| ≤ C_s |y|^(−β)/N² ⟺ 2d N² ≤ C_s |y|^(1−β)`, which fails as `|y| → 0` for `β < 1`.
   (The weight `|y|^(−β)` is *weakest* as `|y| → 0` and *strongest* at `|y| ≈ η₀`; at the top of
   the strip the hypothesis is verbatim the sharp `N⁻²` comparison.)

## Is it FALSIFIED for β < 1? No
The only mechanism producing `|y|⁻¹` is a pole, i.e. an **atom** of the averaged spectral measure
at a real point. But for `u = v`,
`g_N(z)_{uu} = ∫ dμ̄_N(λ)/(λ−z)` with `μ̄_N = E[∑_j w_j δ_{λ_j}]`,
`w_j = N⁻¹ ∑_k |ψ_j(u,k)|² ≥ 0`, `∑_j w_j = 1`; since the GUE joint eigenvalue density is smooth
and full-rank, `E[w_j φ(λ_j)] = ∫ φ(λ) E[w_j|λ_j=λ] f_j(λ) dλ`, so `μ̄_N` is **absolutely
continuous** and `Im g_N(E+iy)_{uu} → π f_N(E)` is finite as `y → 0` (same for `g`). Hence the LHS
is `O(1)` as `|y| → 0`: the *true* weight is `|y|⁰`. The stated inequality is therefore plausible
(not refutable), but it is strictly stronger than any current estimate near the axis.

## Verdict: (b) — keep it as a hypothesis; the exponent `|y|^(−β)` is right, the `N⁻²` near the axis is the gap
`WeightedStripBound` is not derivable from the current machinery. What is missing is precisely a
**uniform-in-the-strip** `N⁻²` averaged-resolvent comparison (equivalently: bulk boundedness of the
averaged/limit Stieltjes transform plus a uniform inverse of the linearized Dyson operator).
The exact statement provable today (new, kernel-checked, `Probability/StripAnalytic.lean`) is
`weightedStripBound_of_nearAxis` + `eventually_weightedStripBound_top` (pointwise form:
`frob_gueResolventMean_sub_limit_le_rpow_top`; composed upper-half-plane form:
`eventually_upperHalfStrip_of_nearAxis`, with `stripThreshold A = max 1 √(2 d² S)`):

`∀ᶠ N, ∀ z, 0 < Im z → stripThreshold A ≤ Im z → Im z < η₀ →`
`  frob(g_N − g) ≤ (8 d⁴√d S² · max 1 (η₀^(β−5))) (Im z)^(−β)/N²`,  `S = ∑ᵢ‖Aᵢ‖²_F`,

i.e. the *whole* strip above `stripThreshold A` is a theorem (any `β ≥ 0`), and
`WeightedStripBound` follows from that plus the near-axis annulus `0 < |Im z| < stripThreshold A`
alone (`lower-half-plane` part of the annulus above the threshold is the conjugation mirror
`z ↦ z̄`, `frob` is conjugation invariant — not yet formalized).
No weakening to `1/N` is either needed or implied: a `1/N`-only rate does not close the endgame.

## Sanity check (orchestrator's question)
`E τ_N(A X B X) = τ_N(A) τ_N(B)` **exactly** for fixed `A,B` and one normalized GUE `X`
(`StripAnalytic.lean`: `integral_trace_coeff_mul_gue_mul_coeff_mul_gue` and its normalized-trace
form `integral_gueNormTrace_mixed`): no `1/N` term appears, consistent with
`pairOrbitCount_mod_two`. Matrix coefficients create no odd-genus
terms, so the combinatorial side does not obstruct `N⁻²`; only the analytic near-axis uniformity
is open.

---

## Task 1 (turn 2): deterministic hypotheses of `flatLemmaM_of_weightedStrip`

New modules (kernel-checked, axioms only propext/Classical.choice/Quot.sound):

* `Probability/LimitSideIdentifications.lean`
  - `trace_operatorMatrixPencilCauchy_eq_blockLimitResolventTrace_fin` — the closed-pencil bridge
    `Tr(operatorMatrixPencilCauchy A₀ A z) = blockLimitResolventTrace (closedPencil A₀ A) z` at an
    **arbitrary** square size `Fin n` (`[NeZero n]`), removing the `Fin (d'+1)` restriction of
    `Probability/LimitBridge.lean`;
  - `guePlaneLimitOrder_eq_zero_of_isSmoothCutoffZeroOn` — **`hlim0` closed modulo one
    geometric input**: `IsSmoothCutoffZeroOn S ε g` + `spectrum ℝ (closedPencil A₀ A) ⊆ S` ⇒
    `guePlaneLimitOrder k A₀ A g = 0` (variant `..._of_eq_zero_on_subset` from `g = 0` on `S`);
  - `integrable_dbarNumOrder_mul_trace_operatorMatrixPencilCauchy_fin` — **`hIntLim` closed
    unconditionally** for every `C^{k+1}` compactly supported `g`;
  - `integral_flatStat_eq_gueStatisticCfc_pencil` — **`hstat`** (it is
    `integral_flatStat_eq_gueStatisticCfc_canonical`; it was being re-passed, now recorded in the
    exact consumed shape).
* `StrongConvergence/StripSideConditions.lean`
  - `flatLemmaM_of_weightedStrip_of_spectralInclusion` — `FlatLemmaM r k F z g C` from
    (i) the weighted strip bound at the canonical pencil, (ii) the cutoff data
    `IsSmoothCutoffZeroOn (specC (h1PencilLimit r k F z)) ε g`, (iii) **only** the spectral
    inclusion `spectrum ℝ (closedPencil (pencilConstCoeff k F z) (pencilDirCoeff k F)) ⊆
    specC (h1PencilLimit r k F z)`. The four deterministic hypotheses are derived.
  - `flatLemmaM_deriv_of_weightedStrip_of_spectralInclusion` — the same for `(g')²`.

**Remaining (exact statement).** The single hole left in this group is

`spectrum ℝ (closedPencil (n := Fin (pencilCoeffDim k F)) (pencilConstCoeff k F z)
  (pencilDirCoeff k F)) ⊆ specC (h1PencilLimit r k F z)`

(the Kronecker/affine coefficient identity `flatPencilBlk = reindex (guePencilMatrix A₀ A)`), plus
the plane integrability `hIntN`, which is `eventually_integrable_dbarNumOrder_mul_trace_gueResolventMean`
(`Probability/LimitBridge.lean`, unconditional, already used above).

---

## Task 2 (turn 2): conjugation symmetry and the half-planes actually covered

New module `Probability/ResolventConj.lean` (kernel-checked, axioms only
propext/Classical.choice/Quot.sound):

* `star_resolvent_of_star_eq` — `star (resolvent P z) = resolvent P (star z)` for self-adjoint
  `P` in a `ℂ`-star-algebra (from `Ring.inverse_star`, `star_sub`, `algebraMap_star_comm`);
* `frob_star`, `frob_sub_star` — `frob` is `star`-invariant;
* `guePencilResolvent_star`, `guePencilResolvent_star_apply`, `guePartialTrace_star`,
  **`gueResolventMean_star`** : `star (gueResolventMean A₀ A z) = gueResolventMean A₀ A (star z)`
  — the **mean side is unconditional** (Hermitian `A₀, A_i`);
* `frob_gueResolventMean_sub_limit_star_of_limit`,
  `weightedStripBound_lowerHalf_of_upperHalf_of_limit`,
  `weightedStripBound_of_upperHalf_of_limit` — the deviation is conjugation invariant and an
  upper half-plane strip estimate transfers to the full strip, **given** the limit-side identity
  `star (operatorMatrixPencilCauchy A₀ A z) = operatorMatrixPencilCauchy A₀ A (star z)`.

**Half-plane status.**  The near-axis annulus (the only remaining analytic input) is now proved
for `Im z > 0` (`eventually_upperHalfStrip_of_nearAxis`) and, *conditionally on the limit-side
identity above*, the conjugation symmetry gives `Im z < 0` for free.  The upper part of the strip
`stripThreshold A ≤ Im z < η₀` is unconditional on `Im z > 0`
(`eventually_weightedStripBound_top`), and the trivial bound `2d|Im z|⁻¹` is unconditional on
both half-planes.  So the only non-symmetric-looking gap left is the mean-side-free statement on
`Im z < 0`, which reduces to the limit-side conjugation identity.

**Obstruction (limit side, not closed).**  The proof needs `Ring.inverse_star` / `Matrix.star_apply`
at `CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι)`.  That type carries `CStarMatrix.instStar`
whereas the generic Mathlib lemmas elaborate `star` via `StarRing.toStarAddMonoid.toStar`; `rw`
cannot fire at entry level (the two star structures are not syntactically the same instance).  The
scalar-valued case used for `gueResolventMean` is unaffected.  Closing it needs either a
resolvent-star lemma for the operator-valued matrix algebra in the pinned `lean-free-prob` oleans,
or a local `Star`-instance alignment; ~20 min were spent and it was dropped per instructions.
