# lean-gue-strong-convergence

An independent Lean 4 / Mathlib formalization of the **strong-convergence
linearization argument** described in
[`gue_linearization_formalization_handoff.md`](gue_linearization_formalization_handoff.md).

The deterministic core of the argument is: *moment convergence + one-sided
spectral inclusion for Hermitian pencils* implies *operator-norm convergence of
every fixed `*`-polynomial in the generators*.  The formalization is organized
into three phases:

1. **Setup** — an independent Lake project reusing the upstream
   [`lean-free-probability-01`](https://github.com/T1mberland/lean-free-probability-01)
   library as a pinned, read-only dependency.
2. **Linearization** — the block-algebra realization of a noncommutative
   matrix-coefficient polynomial, the self-adjoint affine pencil `ℒ_z`, and the
   Schur-complement invertibility equivalence `zI - P(x) invertible ↔ ℒ_z(x)
   invertible`.
3. **Strong convergence** — the abstract transfer theorem (uniform generator
   bounds, the moving-eigenvalue contradiction, the faithful-state even-moment
   formula, and the Hermitian dilation).

## Pinned toolchain and dependencies

| Component | Pin |
|---|---|
| Lean | `leanprover/lean4:v4.34.1` (`lean-toolchain`) |
| Mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| `lean-free-prob` | `fa4067d9fd8ea56d8e39651e9a7871538e4fb333` (read-only) |

The upstream library is never modified. The polynomial bridge imports its algebraic
interfaces, and the trace-convergence module reuses its summable-deviations
Borel–Cantelli theorem. Only already-installed pinned dependencies are inspected.

## Layout

```
GUEStrongConvergence/
  Linearization/
    SchurComplement.lean    ring-level Schur complement with explicit inverses
    NilpotentShift.lean     block shift T_w, nilpotence, geometric inverse
    WordRealization.lean    direct-sum realization u Q^{-1} v = q
    SelfAdjointPencil.lean  the pencil ℒ, B, E, Schur reduction, IsUnit, §2.4
    Evaluation.lean         matrix-coefficient evaluation matWordEval + applications
    PolynomialBridge.lean   bridge to upstream WordPolynomial.evaluate  (upstream import)
  StrongConvergence/
    HermitianDilation.lean  algebraic core of the §3.4 Hermitian dilation
  Probability/
    GUEModel.lean           normalized GUE, covariance, coordinate derivatives
    HermitianCoordinates.lean  explicit Hermitian basis
    Fierz.lean              completeness identity
    CommonSpace.lean        all dimensions on one space; iid Gaussian coordinates
    GaussianIBP.lean        one-dimensional and second-order Gaussian IBP
    SteinIdentity.lean      finite-dimensional coordinate IBP
    GaussianMoments.lean    Gaussian tails and analytic Poincaré machinery
    Variance.lean           conditional variance-identity reduction
    PolynomialPoincare.lean genuine Poincaré and variance bounds under polynomial growth
    TraceMoments.lean       exact first normalized trace moments and tail bound
    TraceConvergence.lean   simultaneous almost-sure first trace limit
    QuadraticTrace.lean     second trace as a Gaussian square sum; exact mean
    MixedTrace.lean         ordered two-letter trace as an inner product; exact means
    GaussianWick.lean       all-order coordinate Wick recursion and pairing formula
    GaussianTensorization.lean  two-factor L² variance tensorization and Gaussian corollary
    GaussianSquareSum.lean  exact square-sum fourth moment and second-trace variance
    QuadraticConvergence.lean   almost-sure square trace limit for all labels
    MixedTraceVariance.lean     exact variance of every two-letter trace
    MixedTraceConvergence.lean  simultaneous almost-sure two-letter trace limits
  Verification/
    Axioms.lean             historical named-declaration axiom printout
    Integrity.lean          rejecting transitive whitelist audit of root declarations
```

## Build and verify

```sh
lake build
lake build GUEStrongConvergenceVerification
lake env lean GUEStrongConvergence/Verification/Integrity.lean
lake env lean GUEStrongConvergence/Verification/Axioms.lean
git diff --check
```

The verification library includes a rejecting transitive audit of every declaration in
`GUEStrongConvergence` reachable from the root library. It fails if any project axiom
or transitive axiom outside `[propext, Classical.choice, Quot.sound]` is found. The
historical named-declaration printout remains available as supplementary evidence.

## Status — **PROVED**

```
theorem GUEStrongConvergenceStatement_of_selfEnergy (r : ℕ) : GUEStrongConvergenceStatement r
```
**No hypotheses other than `r`. Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
No `sorry`, no `admit`, no new axioms.** (Main `fd24326`. Full build 4216 jobs; verification
library 4219 jobs; rejecting integrity audit passes on 5650 declarations.)

That is: for the normalized GUE tuple on the common Gaussian space, almost surely, for every fixed
coefficient dimension `d > 0` and every fixed matrix-coefficient noncommutative `*`-polynomial `P`,
the operator norm of `P` evaluated at the finite-`N` tuple converges to the operator norm of `P`
evaluated at the free semicircular family (`StrongConvergence/Target.lean`).

### How it is proved — the Haagerup–Thorbjørnsen (2005) self-energy argument

| Module | Content |
|---|---|
| `HT05FiniteMean` | mean-centred defect `D` with `frob D ≤ 4(card d)²(∑frob Aᵢ²)²N⁻²y⁻⁴`; exact factorization `selfEnergy − z·1 = −D·m⁻¹`; the Stieltjes representation of `−Im m` |
| `HT05Invertibility` | `−Im⟨v,mv⟩ ≤ −(y/(4(‖z‖²+K²)))‖v‖²` → `IsUnit m`, `frob (m⁻¹) ≤ card d·4(‖z‖²+K²)/y`, and the **unconditional self-energy error** `frob (Λ − z·1) ≤ 16(card d)³S²(‖z‖²+K²)N⁻²y⁻⁵` |
| `HT05Analytic`, `HT05AnalyticOperator`, `HT05ArgumentAnalytic` | analyticity of `z ↦ gueResolventMean` (entrywise → matrix level) and of the matrix argument `B ↦ operatorMatrixArgumentCauchy` |
| `HT05Comparison` | exact operator second-resolvent identity and the `(card d)²` Frobenius transfer, giving the good/bad-region comparison |
| `HT05LimitConjugation` | `star (operatorMatrixPencilCauchy A₀ A z) = operatorMatrixPencilCauchy A₀ A (star z)` — the lower half-plane, unconditionally |
| `HT05PhysicalBranch`, `HT05Harness`, `HT05Final` | the good region (open, path-connected), `IsUnit` by Neumann series, `‖res‖ ≤ 2/Im z`, and the **small-point** form of the Dyson uniqueness theorem giving `m = G(Λ − A₀)` on the good region |
| `HT05Discharge` | path-connectedness of the weighted good region, an explicit small point, and the discharge of the weighted interface `HT05Inputs'` at the canonical pencils |

The two decisive reuses of the pinned `lean-free-prob` dependency are
`matrixDyson_analytic_unique_of_small_point` (the analytic/physical branch selection, HT05 Prop. 5.6)
and `operatorMatrixPencilCauchy_negativeImaginaryPart_posDef`.

A subtlety worth recording: the *unweighted* interface `HT05Inputs` is **false** for large `|Re z|`
(the self-energy error genuinely carries a `‖z‖²` factor), so the final chain runs through the
weighted interface `HT05Inputs'`, whose good/bad split absorbs large-`|Re z|` points in the bad branch.

See [`CURRENT_TASK.md`](CURRENT_TASK.md) for the current verified queue. Its older
append-only history is retained as history, not as a substitute for checking source.
