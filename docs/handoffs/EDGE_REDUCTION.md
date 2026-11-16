# Edge reduction (`feat/edge-reduction`, Worker C, 2026-10-24)

Kernel-checked in `StrongConvergence/EdgeBound.lean`:
* `GUEEdgeBound r` — a.s. for all `i`, `ε > 0`, eventually `‖gueFamily r N x i‖ ≤ 2 + ε`
  (classical GUE no-outlier / edge statement; no cutoffs, no Cauchy--Pompeiu constants).
* `gueEdgeBound_of_scalarSpectralInclusion`, `eventually_tupleNorm_gueFamily_le_of_gueEdgeBound`,
  and `GUEStrongConvergenceStatement_of_pencilStrip_and_edgeBound`: the project target from
  the uniform pencil weighted-strip field plus `GUEEdgeBound r` only.
* `StrongConvergence/EdgeBoundSpectrum.lean`: `scalarSpectralInclusion_of_gueEdgeBound` and
  `gueEdgeBound_iff_scalarSpectralInclusion`, using `spectrum_semicircularFamily`
  (`spectrum ℝ (semicircularFamily r i) = Set.Icc (-2) 2`, restated from the pinned
  `FreeProbability.Fock.spectrum_closedSemicircular_real`).

Honest improvement: the scalar field `ScalarWeightedStripDataAt` is no longer assumed; the
edge bound is a classical, clearly-true statement. **`GUEEdgeBound` is NOT proved here**: it
needs a concentration / large-deviation upper bound for `λ_max` of GUE (Guionnet--Zeitouni
log-Sobolev, or Ben Arous--Guionnet large deviations for the empirical measure).

Build note: `EdgeBoundSpectrum` imports the pinned module
`FreeProbability.Semicircular.SpectralIdentification`, which is not prebuilt in the shared
`.lake/packages`; it was checked against the pinned sources and is not registered in
`GUEStrongConvergence.lean` (only `EdgeBound` is, in one added line).
