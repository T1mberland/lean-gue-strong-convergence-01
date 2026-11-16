# Feasibility: proving `GUEEdgeBound` from the exact all-words mean

Worker C, 2026-10-24. Rigorous analysis of the Bai--Yin scheme from
`Probability/GUEAllWords.lean:230 integral_eq_genusSum`.

## The scheme, written out

For a word of even length `2m`, `E τ_N(w) = N^{-(m+1)} · genusSum w N`, and `genusSum` is a
sum over pairings `q` of `gueLabelWeight q · N^{pairOrbitCount q}` with
`‖gueLabelWeight q‖ ≤ 1`, `pairOrbitCount q = m+1` iff `q` is non-crossing and
`≤ m-1` otherwise (`GUEPairingEar.lean:920`, `GUEPairingGenusSplit.lean:1055`). Hence, for the
one-generator word `X^{2m}`, **if** the non-crossing label sum is the Catalan number `C_m`
(the standard Wick value; not yet verified for this exact `GUEPairing` encoding) and there are
at most `(#pairings) = (2m-1)!!` pairings, then
`E τ_N(X^{2m}) ≤ C_m + (2m-1)!! / N² ≤ 4^m + (2m-1)!! / N²`.

Markov: `τ_N(X^{2m}) ≥ λ_max(X)^{2m}/N`, so
`P(λ_max ≥ 2+ε) ≤ N · E τ_N(X^{2m}) / (2+ε)^{2m}`.

## The decisive obstruction

With `m = c log N`, the error term is `(2m-1)!!/N² ≈ exp(c log N · log log N)/N²`, which
**diverges**; the bound `4^m + (2m-1)!!/N²` therefore cannot be summed over `N` and does not
yield Borel--Cantelli. What is needed is a uniform-in-`m` genus bound, e.g.
`E τ_N(X^{2m}) ≤ (4+δ)^m (1+o(1))` for `m ≪ N^{2/3}`, i.e. control of the *total* crossed
(non-planar) contribution, not its crude pairing count `(2m-1)!!`. That uniform estimate is
exactly the classical Bai--Yin input (Harer--Zagier recursion / orthogonal-polynomial moment
computation, or a large-deviation/LSI argument); it is **not** derivable from the genus
dichotomy plus `‖label‖ ≤ 1`.

## Reachable unconditional sub-results (not yet formalized)

* The deterministic trace--Markov step `P(‖X‖ ≥ 2+ε) ≤ N E τ_N(X^{2m})/(2+ε)^{2m}`.
* The algebraic genus split `E τ_N(X^{2m}) ≤ C_m + (#pairings)/N²` (needs the `GUEPairing`
  cardinality bound and the non-crossing label evaluation; both are combinatorial, no
  analysis). This is honest but, as shown above, insufficient for `GUEEdgeBound`.

**No kernel-checked proof of `GUEEdgeBound` or of the uniform genus bound is claimed.**
