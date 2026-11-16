# II.A (spectral inclusion / no outliers): verified bricks and exact residual

Branch `feat/spectral-inclusion` (Worker E).  All declarations below are
kernel-checked with no `sorry` and only the standard axioms
`propext, Classical.choice, Quot.sound` (checked with `#print axioms`).

## Verified bricks

### 1. `Probability/GaussianTailTransport.lean`
Transport of the `lean-log-sobolev` concentration library from
`EuclideanSpace ℝ (Fin n)` to the basis-independent Mathlib Gaussian on an
arbitrary finite Euclidean space:

* `standardGaussian_eq_stdGaussian (n) : LogSobolev.standardGaussian n = stdGaussian (EuclideanSpace ℝ (Fin n))`
* `standardGaussian_map_piLpCongrLeft (κ) :
    (LogSobolev.standardGaussian (Fintype.card κ)).map
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin κ).symm) =
      stdGaussian (EuclideanSpace ℝ κ)`
* `gaussian_measure_abs_ge_le_stdGaussian (hf : LipschitzWith K f) (hr : 0 ≤ r) :
    (stdGaussian (EuclideanSpace ℝ κ)).real {x | r ≤ |f x - ∫ y, f y ∂stdGaussian _|} ≤
      2 * Real.exp (-r^2 / (2 * K^2))`

The GUE coordinate space is `EuclideanSpace ℝ (GUECoord ι N)` with
`stdGaussian`, so concentration is now directly available for GUE observables.

### 2. `Probability/ResolventConcentration.lean`
The sharp ℓ² input for the `1/N` variance proxy (this is the brick that rules
out the lossy `K² ~ N` bound obtained from bare operator norms):

* `quadform M u = ∑ a, ∑ b, star (u a) * M a b * u b`
* `quadform_star_mul_self (s u) : (quadform (star s * s) u).re = ∑ c, ‖∑ b, s c b * u b‖²`
* `quadform_nonneg (hM : 0 ≤ M) (u) : 0 ≤ (quadform M u).re`
  (via `StarOrderedRing.nonneg_iff` and closure induction over `star s * s`)
* `quadform_algebraMap (c u) : quadform (algebraMap ℝ _ c) u = ↑(c * ∑ k, ‖u k‖²)`
* **`sum_sq_star_mul_le {R} {η} (hR : ‖R‖ ≤ η) (hη : 0 ≤ η) (u) :
    ∑ k, ‖∑ a, star (u a) * R a k‖² ≤ η² * ∑ k, ‖u k‖²`**

For a GUE resolvent `R = R_N(z)` and `η = (z.im)⁻¹`, this gives the `η²` factor
with **no** dimension loss.  Together with the entrywise second-resolvent
estimate this yields the `1/N` concentration scale.

### 3. `Probability/ResolventPencilAlgebra.lean`
* `guePencilDirection_apply` : entry formula for the coordinate derivative.
* `guePencil_sub_eq_sum_smul :
    guePencil A₀ A x - guePencil A₀ A y = ∑ p, (x p - y p) • guePencilDirection A p`
* `guePencilResolvent_sub :
    R(x) - R(y) = R(x) * (H(x) - H(y)) * R(y)`
  (second resolvent identity, from `Ring.inverse_sub_inverse`).

### 4. `Probability/ResolventPencilPairing.lean`
* `direction_pairing_eq :` for `p = (i,(a,b))`,
  ```
  ∑ k l, W k * (guePencilDirection A p) k l * Z l
    = ∑ x ∑ x₂, scale * α * (W (x,a) * A i x x₂ * Z (x₂,b))
    + ∑ x ∑ x₂, scale * β * (W (x,b) * A i x x₂ * Z (x₂,a))
  ```
  (the direction matrix only sees the two slices `a`, `b`).  This is the
  combinatorial identity needed to pass from the coordinate sum to the
  Frobenius-norm estimate.

### 5. `Probability/CommonSpaceBorelCantelli.lean`
* `ae_eventually_not_mem_of_summable :
    (∀ N, MeasurableSet (P N)) →
    Summable (fun N => (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))).real (P N)) →
    ∀ᵐ x ∂(commonGaussianMeasure ι), ∀ᶠ N in atTop, x N ∉ P N`
  (first Borel–Cantelli lemma on the countable product, using
  `commonGaussianMeasure_map_eval`).

## Sparse bound and Lipschitz concentration (now proved)

Both the sparse direction-pairing bound and the Lipschitz/tail brick are now
kernel-checked:

* `Probability/ResolventSparseBound.lean`
  - `frob M = sqrt (∑ c c', ‖M c c'‖²)`
  - `sum_sq_direction_pairing_le`:
    `∑ p ‖∑ k l W k D_p k l Z l‖² ≤ 2 * gueScale N² * (∑ i frob(A i)²) * ‖W‖² * ‖Z‖²`
  - `sum_sq_direction_pairing_le_swap` (paired index order).
* `Probability/ResolventLipschitz.lean`
  - `pairing_mul_eq`, `pairing_sum_smul`, `pairing_diff_eq`
  - `norm_sum_mul_le` (finite Cauchy–Schwarz)
  - `sum_sq_rowComb_le`, `sum_sq_matVec_le` (sharp `(im z)⁻²` bounds)
  - `resolventLipschitzConst A z u v = sqrt (2 * gueScale N² * ∑ frob(A i)² * (im z)⁻⁴ * ‖u‖² ‖v‖²)`
  - `resolventPairing_lipschitz : LipschitzWith (toNNReal K) (fun x => (resolventPairing A z u v x).re)`
  - `resolventPairing_tail : μ.real {r ≤ |Φ - EΦ|} ≤ 2 exp(-r²/(2K²))`

The remaining item is the combinatorial step (c).
Write `frob M = Real.sqrt (∑ c, ∑ c', ‖M c c'‖²)` (Frobenius norm of a fixed
`d × d` matrix) and for `W Z : d × Fin N → ℂ`

```
∑ p : GUECoord ι N,
    ‖∑ k, ∑ l, W k * (guePencilDirection A p) k l * Z l‖^2
  ≤ 2 * (gueScale N)^2 * (∑ i, (frob (A i))^2)
        * (∑ k, ‖W k‖²) * (∑ k, ‖Z k‖²)
```

(`gueScale N ^ 2 = (N : ℝ)⁻¹`).  The combinatorial half is *already proved* as
`direction_pairing_eq` above.  Remaining steps:

1. Cauchy–Schwarz on the `d × d` index set
   (`Finset.sum_mul_sq_le_sq_mul_sq`) gives
   `‖∑ c ∑ c', W (c,a) * (A i) c c' * Z (c',b)‖
      ≤ frob (A i) * sqrt (∑ c, ‖W (c,a)‖²) * sqrt (∑ c', ‖Z (c',b)‖²)`.
   A verified template for this estimate is available in the branch history
   (`abs_inner_slice_le`, removable once the bound is in the library).
2. `|α|² = |β|² = 1/2` gives `|α P + β P'|² ≤ |P|² + |P'|²`, and
   `∑_{a,b} ‖W_a‖² ‖Z_b‖² = (∑_a ‖W_a‖²)(∑_b ‖Z_b‖²) = ‖W‖² ‖Z‖²`
   (`Finset.sum_mul_sum`), giving the stated constant `2/N * ∑ frob(A i)²`.

Consequently, for `u v : d × Fin N → ℂ`, `z.im > 0`, the pairing
`Φ(x) = (∑ a b, star (u a) * guePencilResolvent A₀ A x z a b * v b).re`
satisfies `LipschitzWith K Φ` with

```
K = (z.im)⁻⁴.sqrt-free form:
K² = (z.im)⁻⁴ * (2 * (∑ i, (frob (A i))^2) * (N : ℝ)⁻¹)
       * (∑ k, ‖u k‖²) * (∑ k, ‖v k‖²)
```

(indeed `‖W‖² ≤ (z.im)⁻² ∑‖u‖²` and `‖Z‖² ≤ (z.im)⁻² ∑‖v‖²` by
`sum_sq_star_mul_le` applied to `R(x)^*` and `R(y)`), hence the tail

```
P(|Φ - E Φ| ≥ r) ≤ 2 exp(-r² / (2 K²))
```

by `gaussian_measure_abs_ge_le_stdGaussian`.  At fixed `r`, this is
`exp(-c N)` with `c = c(r, z, A, u, v) > 0`, hence summable in `N`.

## Remaining assembly (after the residual)

1. ε-net over unit vectors of `ℂ^{dN}` (size `≤ (1+2/ε)^{2dN}`) plus the
   residual bound for each net pair gives, for fixed `z` and `r > 0`,
   `P(‖R_N(z) - E R_N(z)‖ ≥ r) ≤ exp(-c N)`.
2. Apply `ae_eventually_not_mem_of_summable` with `P N = {‖R_N(z) - E R_N(z)‖ ≥ r}`.
3. Use the mean resolvent convergence `‖E R_N(z) - R_h(z)‖ → 0` (the genuinely
   analytic residual of II.A, independent of this concentration work) to get
   `z ∉ σ(H_N)` eventually a.s. whenever `z ∉ σ(h)`: choose `r < dist(z, σ(h))`.
4. Countably many rational `z` with `0 < im z` plus a compact exhaustion gives
   the pathwise statement `∀ᵐ x, ∀ k, ...` and hence `SpectralInclusion`.

No step above assumes norm convergence of `P(G_N)` or `hH1`.

## Verification

From the primary checkout (never from the worktree):

```
lake env lean <worktree>/GUEStrongConvergence/Probability/GaussianTailTransport.lean
lake env lean <worktree>/GUEStrongConvergence/Probability/ResolventConcentration.lean
lake env lean <worktree>/GUEStrongConvergence/Probability/ResolventPencilAlgebra.lean
lake env lean <worktree>/GUEStrongConvergence/Probability/CommonSpaceBorelCantelli.lean
```

## Concentration step: what is true, and why fixed-`z` norm concentration cannot close II.A

Branch `feat/concentration-net` (Worker L), file
`Probability/ResolventNetConcentration.lean` (kernel-checked, only
`propext, Classical.choice, Quot.sound`).

### Delivered

* `resolventVarianceConst A z = 2 (∑ᵢ ‖Aᵢ‖_F²) (im z)⁻⁴` and
  `resolventLipschitzConst_sq_le`: for vectors of squared norm at most one,
  `K_N² ≤ resolventVarianceConst A z / N`.
* `summable_two_exp_neg_mul`: `∑_N 2 exp(-(r²/2C) N) < ∞` for `r, C > 0`.
* `gaussian_tail_le_of_lipschitz_sq_le`: tail at scale `r` from `K² ≤ B`,
  including the degenerate case `B = 0` (`K = 0` ⇒ constant ⇒ empty event).
* **`ae_eventually_abs_resolventPairing_sub_integral_lt` / `_le`**: for any fixed
  families of bounded vectors, almost surely
  `|Re ⟨u_N, R_N(z) v_N⟩ - ∫ Re ⟨u_N, R_N(z) v_N⟩| < r` eventually, for **every**
  fixed `r > 0` (no restriction on `r`).
* `resolventMean` (entrywise mean) and `pairing_resolventMean`: pairing against
  the mean matrix equals the integral of the pairing.
* `measureReal_net_iUnion_le`: the finite `ε`-net union bound
  `P(∃ u,v ∈ s, deviation) ≤ card(s)² · b`.
* **`ae_eventually_net_pairing_le`**: given a net `s N` of unit vectors with
  `card (s N) ≤ k N` and `∑_N k_N² · 2 exp(-r²N/(8C)) < ∞`, almost surely every
  net pairing is eventually within `r/2` of its mean.

### The arbitrary-`r` operator-norm statement is false

The claim `∀ᵐ x, ∀ᶠ N, ‖R_N(z,x) - E R_N(z,x)‖ ≤ r` for **every** fixed `r > 0`
fails at fixed `z` with `im z > 0`:

1. The verified constant satisfies `K_N² ≤ C/N` with `C = 2(∑‖Aᵢ‖_F²)(im z)⁻⁴`
   independent of `N`, while the unit sphere of `ℂ^{dN}` has real dimension `2dN`.
   The `ε`-net union bound gives
   `P(‖R-ER‖ ≥ r) ≤ (1+2/ε)^{4dN} 2 exp(-r²N/(8C))`, i.e.
   `2 exp(N[4d log(1+2/ε) - r²/(8C)])`, whose exponent is **positive** for small
   fixed `r`: no summability, so Borel–Cantelli cannot apply.  The typical size of
   the supremum is `√(K² · 2dN) = √(2Cd)`, constant in `N`.
2. Concrete counterexample: `d = 1`, `A₀ = 0`, `A₁ = 1`, `z = 2i`.  Then
   `H = GUE(N)` with entries of variance `1/N`, `R = (H-z)⁻¹` and `E R = m_N I` by
   unitary invariance.  For each eigenvector `u_j` with eigenvalue `λ_j` in the
   semicircle bulk,
   `(R - ER) u_j = ((λ_j - 2i)⁻¹ - m_N) u_j`, so
   `‖R - ER‖ ≥ |(λ_j-2i)⁻¹ - m_N| → |i/2 - i(1-√2)| = √2 - 1/2 ≈ 0.914 > 0`.
   The statement therefore fails for every `r < 0.9`.
3. The same computation shows that the mean-limit input `‖E R_N(z) - R_h(z)‖ → 0`
   does not upgrade to `R_N(z) → R_h(z)` in operator norm: only the scalar mean
   converges, the matrix itself does not.

### Consequence for II.A and remaining routes

**II.A cannot be closed by fixed-`z` operator-norm concentration.**  The remaining
honest routes are:

(i) a quantitative local law for the Stieltjes transform `(1/dN) tr R_N(z)`
    together with eigenvalue counting / rank arguments, or
(ii) an edge / maximum-principle argument starting from the *mean* Dyson equation
    plus a quantitative stability estimate for the resolvent.

Both are beyond the current bricks.  Nothing in this file (and nothing in the
repository) claims any spectral-inclusion conclusion conditionally on the false
arbitrary-`r` norm statement.

### Not included

The deterministic passage from net pairings to the operator norm (the standard
`ε`-net approximation) and the norm-concentration-around-the-mean statement
`|‖R_N - E R_N‖ - E‖R_N - E R_N‖| ≤ r` both need the `C⋆`-module operator-norm
characterisation `CStarMatrix.norm_le_of_forall_inner_le` together with the pairing
identity `⟪w, toCLM M v⟫ = ∑ star(w a) M b a v b`.  That route is currently
obstructed by `WithCStarModule` instance mismatches (`SMul ℂ (κ → ℂ)` versus
`SMul ℂ (C⋆ᵐᵒᵈ(ℂ, κ → ℂ))` under the implicit transparency level) in this
toolchain; it is recorded as the precise next engineering step.
