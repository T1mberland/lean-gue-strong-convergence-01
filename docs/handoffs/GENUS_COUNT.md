# Growing-order genus count — kernel-checked partial bounds and the missing lemma

Worker D, branch `feat/genus-count` (worktree `.worktrees/wGenusD`, from `main` at `b3fc9ce`).

This note records (a) exactly what the existing genus machinery yields for the
growing-order moment bound, (b) the new kernel-checked partial results, and (c) the
precise combinatorial lemma that is still missing on the only known unconditional
route to `GUEEdgeBound`.

No `sorry`, no `admit`, no new axioms. Axioms of every new theorem are only
`propext`, `Classical.choice`, `Quot.sound`.

## 1. What the existing expansion gives

For a word `w` with `w.length = 2m` the exact expansion
(`integral_gueNormTrace_eq_genus_canonical`,
`Probability/GUEWordGenusExpansionInstance.lean:308`) is

  `E τ_N(w) = (N : ℂ)^{-(m+1)} ∑_{p : GUEPairing l} gueLabelWeight l p * (N : ℂ)^{c(p)}`,

where `l = gueCanonicalEntries w m hl hN`, `c(p) = pairOrbitCount p`, and

* `‖gueLabelWeight l p‖ ≤ 1` (`norm_gueLabelWeight_le_one`, `GUEVarianceFinal.lean:238`);
* `c(p) = m + 1` for non-crossing `p` (`pairOrbitCount_eq_of_isNonCrossing`,
  `GUEPairingEar.lean:939`);
* `c(p) ≤ m - 1` for crossing `p` (`pairOrbitCount_le_of_not_isNonCrossing`,
  `GUEPairingGenusSplit.lean:1053`);
* `c(p) ≡ m + 1 (mod 2)` (`pairOrbitCount_mod_two`), so
  `g(p) := (m + 1 - c(p))/2 ∈ {0, …, ⌊m/2⌋}` is an integer.

No file in `Probability/GUEPairing*.lean` contains a count of pairings by orbit count
(`grep` for `pairOrbitCount`, `genus`, `nonCrossing`, `Catalan`: only the dichotomy
above and the cardinality-free structural lemmas exist).  The total number of pairings
of `2m` entries was not available in the repo either; it is proved here.

## 2. New kernel-checked results

All in `Probability/GenusMomentBounds.lean` (imported once from the root module).

| declaration | statement |
|---|---|
| `pairingCount_eq_doubleFactorial` | the number of pairings of `2m` entries is exactly `(2m-1)!!` |
| `pairingCount_le_doubleFactorial` | `Fintype.card (GUEPairing l) ≤ (l.length - 1)!!` for every `l` |
| `norm_pairing_label_sum_le` | `‖∑_p label p · N^{c(p)}‖ ≤ ∑_p N^{c(p)}` when `‖label‖ ≤ 1` |
| `pairingWeightSum_le_dichotomy` | `∑_p N^{c(p)} ≤ nc·N^{m+1} + cr·N^{m-1}` |
| `norm_integral_gueNormTrace_le_dichotomy` | `‖E τ_N(w)‖ ≤ nc + cr / N²` |
| `norm_genusSum_le_dichotomy` | the same dichotomy for the unnormalized `genusSum` |
| `norm_integral_gueNormTrace_le_of_pairingWeightSum` | if `∑_p N^{c(p)} ≤ C^m N^{m+1}` then `‖E τ_N(w)‖ ≤ C^m` |
| `norm_integral_gueNormTrace_le_doubleFactorial` | `‖E τ_N(w)‖ ≤ nc + (2m-1)!!/N²` |
| `norm_integral_gueNormTrace_le_doubleFactorial_mul` | `‖E τ_N(w)‖ ≤ (2m-1)!! (1 + N^{-2})` |
| `norm_integral_gueNormTrace_le_const` | for fixed `m`, `‖E τ_N(w)‖ ≤ 2(2m-1)!!` for **all** `N ≥ 1` |

Here `nc` is the number of non-crossing pairings of `l` and `cr` the number of crossing
ones; every statement is uniform in the word `w` of the fixed length `2m`, and holds for
every dimension `N ≥ 1`.  The requested easy bounds are thus kernel-checked except for
the *identification* `nc = Catalan_m` (see §4, item 2): the dichotomy is stated with `nc`
symbolically, and `nc ≤ (2m-1)!!` is immediate.

`norm_integral_gueNormTrace_le_of_pairingWeightSum` is the precise interface: the whole
remaining content of the growing-order bound is a count of pairings, never analysis.

## 3. Why the crude bound fails, and the exact missing lemma

For a pairing `p` of `2m` entries put `g(p) = (m+1-c(p))/2` and
`ε_g(m) = #{p : c(p) = m + 1 - 2g} = #{p : g(p) = g}`.  Then

  `|E τ_N(w)| ≤ ∑_{g=0}^{⌊m/2⌋} ε_g(m) N^{-2g} = Catalan_m + ∑_{g≥1} ε_g(m) N^{-2g}`.

The crude bound uses only `ε_g ≤ (2m-1)!!`, so it controls the crossing part by
`(2m-1)!!/N²`.  For `m = c log N` this is `≈ exp(c log N · log log N)/N²`, which
**diverges**, so it cannot be summed over `N` (Borel–Cantelli fails).

**Missing lemma (Harer–Zagier genus count).**
There exist absolute constants `K ≥ 1` and `c > 0` such that for all `m ≥ 1` and all
`g` with `3g ≤ m`,

  `ε_g(m) ≤ 4^m · (K · m^3)^g / g!`.

Equivalently, for `g ≤ m/3` the ratio `ε_g(m)/4^m` is at most `(K m^3)^g/g!`; this is
the polynomial-in-`m` growth of the Harer–Zagier count of genus-`g` pairings (for `g = 1`
the exact value is `ε_1(m) = Catalan_m · (m-1)m(m+1)/12`, so the shape is right).  The
restriction `g ≤ m/3` is essential: for `g ≈ m/2` the count `ε_g` is of the order of the
*total* number of pairings, so no `(m^3)^g/g!` bound can hold there.  For `g > m/3` the
proof below uses only `ε_g ≤ (2m-1)!!`.

## 4. How the missing lemma yields the uniform bound (the reduction is arithmetic)

Assume the Harer–Zagier lemma with constants `K, c`, and let `G = ⌊m/3⌋`.

* Small genera (`1 ≤ g ≤ G`):
  `∑_{g=1}^G ε_g(m) N^{-2g} ≤ 4^m ∑_g (K m^3/N^2)^g/g! ≤ 4^m · exp(K m^3/N^2)`.
  For `m ≤ c N^{2/3}` the exponent is `≤ K c^3`, hence this part is `≤ e^{Kc^3} 4^m`.
* Large genera (`g > G`): `ε_g ≤ (2m-1)!!` and, for `N ≥ 2`,
  `∑_{g>G} N^{-2g} ≤ 2 N^{-2G}`, so this part is `≤ 2(2m-1)!! N^{-2G}`.  Since
  `G ≥ m/3 - 1` and `(2m-1)!! ≤ (2m)^m`, it is `≤ 2N^2 (2m/N^{2/3})^m`, which is `≤ 1`
  once `N^{2/3} ≥ 4m`.

Therefore, for every `δ > 0` there are `c_δ > 0` and `m_δ` such that

  `|E τ_N(w)| ≤ (4+δ)^m`   for all `m_δ ≤ m ≤ c_δ N^{2/3}`, all `N ≥ 2`, all `|w| = 2m`.

Markov plus `τ_N(X^{2m}) ≥ ‖X‖^{2m}/N` then gives

  `P(‖X‖ > 2+ε) ≤ N (4+δ)^m / (2+ε)^{2m}`,

and with `m = ⌊C log N⌋`, `C = ε / log((2+ε)^2/(4+δ))`, the exponent of `N` is
`1 - C log((2+ε)^2/(4+δ)) < -1`, so the probabilities are summable.  This would prove
`GUEEdgeTail` and hence, by `gueEdgeBound_of_tailMeasures`
(`Verification/TerminalAudit.lean:288`), `GUEEdgeBound`.

The two ingredients *not* formalized are therefore:

1. **The Harer–Zagier genus count** stated in §3 (the genuine research-level input).
2. **(Optional, for the sharp constant)** the evaluation `nc = Catalan_m` for the exact
   `GUEPairing`/`IsNonCrossing` encoding, i.e. the usual Wick/Catalan count of
   non-crossing pairings.  Nothing in the present file needs it: the dichotomy is stated
   with `nc` symbolically and bounded by `(2m-1)!!`.

Two further observations about the shape of a future proof:

* `ε_g(m)` is a finite cardinality of a decidable subtype of `GUEPairing`, so the missing
  lemma is a statement about `Fintype.card` of a filtered `Finset`; it can be attacked
  either through the Harer–Zagier recursion or through the Dyck-path/opening-set encoding
  of `IsNonCrossing`.
* The parity input (`pairOrbitCount_mod_two`) is already available and is what makes `g`
  an integer; the remaining work is counting, not algebra.

## 5. Build and integrity

* `lake build GUEStrongConvergence.Probability.GenusMomentBounds` — success.
* `lake build GUEStrongConvergence` (root, with the new import) — success (see commit log).
* `#print axioms` on every theorem in §2 — only `propext`, `Classical.choice`,
  `Quot.sound`.
* `grep sorry/admit` — none.

**No unconditional growing-order bound and no `GUEEdgeBound` is claimed here.**  The
honest content is the kernel-checked reduction and the explicit statement of the missing
combinatorial lemma.
