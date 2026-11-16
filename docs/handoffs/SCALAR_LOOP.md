# Scalar GUE loop equation — status (branch `feat/scalar-loop`)

## Proved and kernel-checked (new file `Probability/ScalarLoopCore.lean`)

* `loop_identity_of_dyson` (exact, no threshold, no concentration input):
  if `(z - g) * g = 1` and `z * m - 1 - m^2 = Var`, then `(m - g) * (z - m - g) = Var`.
  Equivalently `(m - g) * (1/g - m) = Var` since `1/g = z - g`.  Here `m = E[T_N]`,
  `T_N = N^{-1} tr (z - G_N)^{-1}`, `Var = E[T_N^2] - m^2`.
* `loop_bootstrap`: from that exact identity plus `Im z * Im m <= 0` and `Im z * Im g <= 0`,
  `‖m - g‖ <= ‖Var‖ / |Im z|` — **no lower bound on `|Im z|`**.

## Exact inputs already in the repo (reused, not reproved)

* `single_gue_schwinger_dyson` (`Probability/DysonMasterIdentity.lean:1214`), exact finite `N`:
  `z * m - 1 = E[T_N^2]` (so `z * m - 1 - m^2 = Var`).
* `limit_dyson_equation` (`Probability/DysonLimit.lean:149`), at `d = 1`, `A = 1`:
  `(z - g) * g = 1`.
* `integral_norm_sq_fluctuation_scalar_le` (`Probability/SharpTwoPoint.lean:826`), **unconditional
  in `Im z`**: `∫ ‖T_N - m‖^2 <= 4 N^{-2} (Im z)^{-4}`; hence `‖Var‖ <= 4 N^{-2} |Im z|^{-4}`.

## Honest conclusion (if the two sign lemmas land)

`|E g_N(z) - g(z)| <= 4 N^{-2} |Im z|^{-5}` for **all** `0 < |Im z|`, i.e.
`WeightedStripBound 0 (fun _ => 1) k η₀ C_s 5` for every `η₀`, `C_s = 4`.  Power `β = 5`
(better than HT05's 7).  The loop denominator `1/g - m = z - g - m` has
`Im(1/g - m) = Im z - Im g - Im m`, and both imaginary parts have the sign opposite to `Im z`
(Cauchy transforms of positive measures), giving `|Im(1/g - m)| >= |Im z|`.

## Still open (the only gaps)

1. `Im z * Im m <= 0` for the finite-`N` mean: from `Im (z-G)^{-1} = -Im z (z-G)^{-1}(z-G)^{-*}`
   entrywise (`R - R^* = (z̄ - z) R R^*`, only `(z-H)R = 1` needed; `CStarMatrix.mul_apply`,
   `star_apply`, `Complex.mul_conj` available).
2. `Im z * Im g <= 0` for the limit.  `FreeProbability.OperatorValued.MatrixCauchyImaginary` is
   **not compiled** in `.lake/packages` (read-only, only 74/521 dep modules built), so its
   `operatorMatrixPencilCauchy_negativeImaginaryPart_posSemidef` is unusable.  Fallback: prove
   `‖g z‖ < 1` on `Im z ≠ 0` by IVT (`‖g‖ != 1` since `‖g‖ = 1` forces `z = g + 1/g = g + conj g`
   real; `‖g‖ <= 1/|Im z| < 1` far away; continuity from
   `hasDerivAt_resolvent_const_left`), then `Im z = Im g (1 - 1/‖g‖^2)` gives the sign.
   The IVT/continuity step is the remaining formalization work.
3. Assemble `m`, `g` at `d = Fin 1`, `ι = Unit` and instantiate `WeightedStripBound`.

## Note on the existing matrix route

`frob_gueResolventMean_sub_limit_le_sharp` already gives `β = 5` but **only under the threshold**
`2 d^2 ∑ frob(A_i)^2 <= (Im z)^2` (i.e. `|Im z| >= sqrt 2` at `d = 1`), which is exactly what
blocks the strip.  The loop route above removes that threshold.
