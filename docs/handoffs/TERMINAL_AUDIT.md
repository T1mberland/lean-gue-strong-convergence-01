# Terminal-hypothesis audit (Worker D, branch `feat/terminal-audit`)

Machine-checked companion: `GUEStrongConvergence/Verification/TerminalAudit.lean` (kernel-checked;
axioms only `propext`, `Classical.choice`, `Quot.sound`; no `sorry`). Audit of the two final
conditional theorems: `GUEStrongConvergenceStatement_of_weightedStripInputsFinal`
(`FinalReduction.lean:683`) and `GUEStrongConvergenceStatement_of_pencilStrip_and_edgeBound`
(`EdgeBound.lean:152`).

| Lean name | file:line | statement (mathematical) | discharged? | status |
|---|---|---|---|---|
| `WeightedStripBound` | `Probability/LemmaMWeighted.lean:123` | `frob(g_N(z)−g(z)) ≤ C_s|Im z|^{−β}/N²` for **all** `0<|Im z|<η₀`, `0≤β<max k 1` | **NO** — hypothesis only (LemmaMWeighted:420,485,552; FinalReduction:87) | **(c) likely false pointwise.** `g` is the vacuum expectation of the free pencil resolvent (fixed point of the operator-valued Dyson equation, not an explicit integral). At the Airy edge `|Im z|≍N^{−2/3}` the mean deviates at `N^{−1/3}`, RHS `≤C N^{−4/3}`; the repo's sharp Dyson bound needs `|Im z|^{−5}` and a lower threshold. The integrated (Cauchy–Pompeiu-weighted) form is the plausible truth. |
| `WeightedStripDataAtFinal` | `StrongConvergence/FinalReduction.lean:134` | `∃ η₀>2,C_s,β<max k 1,f,C'`, cutoff zero on `specC`, `C^{k+1}` reg., **`HasCompactSupport f`**, strip bound | **NO**, and **uninhabited** (`weightedStripDataAtFinal_uninhabited`) | **(c) false as stated**: `IsSmoothCutoff.eq_one` forces `f=1` outside a bounded set, contradicting `HasCompactSupport f` for compact `specC`. Repair: `HasCompactSupport (f−1)`. |
| `ScalarWeightedStripDataAt` | `StrongConvergence/FinalReduction.lean:399` | same at `A₀=0`, `A=scalarPencilCoeff i`, order 1, `β<1` | **NO**, uninhabited (`scalarWeightedStripDataAt_uninhabited`) | **(c) false as stated** (same defect). Unused in the newer `EdgeBound` architecture. |
| `WeightedStripInputsFinal` | `StrongConvergence/FinalReduction.lean:659` | conjunction of the two fields above | **NO**, uninhabited (`weightedStripInputsFinal_uninhabited`) | **(c)**: makes `…_of_weightedStripInputsFinal` **vacuous**. |
| `WeightedStripDataAt'''` (and the `At`, `At'`, `At''` lineage) | `Probability/LimitFlatten.lean:679` | six-field bundle ending in `HasCompactSupport f ∧ WeightedStripBound` | **NO**, uninhabited (`weightedStripDataAtTriplePrime_uninhabited`); "producers" in `LimitBridge.lean` only rename it | **(c) false as stated**; the lineage is a renaming chain, not a discharge. |
| `GUEEdgeBound` | `StrongConvergence/EdgeBound.lean:60` | a.s. `∀ i ε>0`, eventually `‖G_i‖ ≤ 2+ε` | **NO** (classical; no producer) | **(b) true**, needs large deviations / Gaussian concentration. Clean missing input: `GUEEdgeTail` (summability of `P(‖G_i‖>2+ε)`); `gueEdgeBound_of_tailMeasures` proves tail ⇒ edge by Borel–Cantelli. |
| `FlatLemmaM` | `StrongConvergence/FlatSideConditions.lean:271` | `|E τ_N(f)| ≤ C/N²` eventually | producer `flatLemmaM_of_weightedStrip` (conditional on `WeightedStripBound`); genuine instance `flatLemmaM_zero` | (b) for general `f`; (a) for `f=0` (proved). Not terminal. |
| `IsSmoothCutoffZeroOn`, `IsSmoothCutoff` | `LemmaMWeighted.lean:512`, `ScalarInclusionSmooth.lean:393` | smooth cutoff, zero and zero-derivative on `S`, `(f')²` compact support | **YES** `exists_isSmoothCutoffZeroOn` / `exists_isSmoothCutoff` (instantiated in the audit file at `specC` and at `spectrum semicircular`) | (a) classical. |
| `hV` field of `PencilLemmaSResidual` | `FlatSideConditions.lean:281` | `Var(τ_N(f)) ≤ C/N²·E τ_N((f')²)` | **YES** `hV_field_residual_shape` (`FlatHVField.lean:305`) | (a) Poincaré/Cauchy–Schwarz; no longer a hypothesis. |
| `PencilSpectralInclusionData`, `H1CanonicalDilated` | `PencilSpectralInclusion.lean:580`, `FinalWiring.lean:313` | a.s. eventual spectrum inclusion of the flattened/canonical pencils | conditional producers `pencilSpectralInclusionData_of_lemmaSInputs`, `H1CanonicalDilated_of_lemmaSInputs` | (b) true (local law); strictly weaker than the norm target, not equivalent to it. |
| `ScalarSpectralInclusion` | `CutoffExclusion.lean:331` | a.s. spectrum of `G_i` within `ε` of `spectrum(semicircular)` | conditional producer on the vacuous scalar bundle | (b); `⟺ GUEEdgeBound` (`EdgeBoundSpectrum.lean`). |
| `hWords` (II.B) | `FinalStatement.lean:53` | a.s. all normalized trace words → free moments | **YES** `ae_all_words_gueNormTrace_tau_unconditional` (`FreeMomentBridgeProof.lean:257`), `hblock`, `freeMomentBridge` | (a) unconditional. |
| `hEdge`, `hB` | `FinalStatement.lean` | `tupleNorm ≤ 3r`; deterministic polynomial bound | **YES** from `GUEEdgeBound` (`EdgeBound.lean`, `FinalWiring.lean:256`) | (a) deterministic. |
| `hstat`, `hlim0`, `hIntLim` | old `WeightedStripDataAt*` | flat↔GUE transport, limit-statistic vanishing, plane integrability | **not** in the two final theorems; theorems at canonical coefficients | (a) discharged (`flatGUEStatisticEqCont_canonical`, `guePlaneLimitOrder_eq_zero_of_eq_zero_on_spectrum`, `…integrable_dbarNumOrder…`). |

## Conclusion: the minimal honest residual set

Both final theorems are currently **vacuous**, not conditional proofs: `HasCompactSupport f`
together with `IsSmoothCutoff`'s `f = 1` off a bounded set makes every weighted-strip bundle
uninhabited (`not_exists_isSmoothCutoffZeroOn_and_hasCompactSupport`, and the five
`*_uninhabited` theorems). The vacuity is *not* circularity but it invalidates the conditional
endgame until `f` is replaced by `f−1` (bricks already on main: `CutoffCompactSupport`,
`CutoffCancellation`, `CutoffFlatCancellation`, `ExtensionLinearity`). After that mechanical
repair the honest residual set has exactly two items: (1) `GUEEdgeBound r` — true and classical,
reducible to the tail summability `GUEEdgeTail r` plus concentration, and *not* derivable from
fixed-order moment limits; (2) a **weak/integrated** pencil strip estimate — the pointwise
`WeightedStripBound` with `β<max k 1` on the whole strip is very likely false (edge regime), so
only its Cauchy–Pompeiu-weighted form should be assumed, and the extension order must be large
enough (`k ≥ 7` for the honest `|Im z|^{−7}` growth). Nothing else in the graph is terminal;
in particular the variance field, `hWords`, `hEdge`, `hB` and the identification fields are
all theorems.
