/-
# The scalar GUE loop (Dyson) equation: exact second-order structure

This file isolates the *algebraic and elementary-analytic* core of the scalar loop route to the
second-order resolvent-mean estimate for one GUE matrix (`d = 1`).

Let `m = E[T_N(z)]` with `T_N = N⁻¹ tr (z - G_N)⁻¹`, and let `g` be the limit Cauchy transform.
The project already has the **exact finite-`N` Schwinger--Dyson identity**
`single_gue_schwinger_dyson` (`Probability/DysonMasterIdentity.lean`),
`z * m - 1 = E[T_N²]`, and the exact limit Dyson equation `limit_dyson_equation`
(`Probability/DysonLimit.lean`), `(z - g) * g = 1`.

**Exact second-order identity.**  Writing `Var = E[T_N²] - m²` (so that subtracting the two
Dyson equations gives `z * m - 1 - m² = Var`), the two equations combine to

`(m - g) * (z - m - g) = Var`,

equivalently `(m - g) * (1/g - m) = Var`, using `1/g = z - g`.
The loop equation therefore determines `m - g` in closed form, with *no* stability threshold:
`m - g = Var / (1/g - m)`.

**Why this beats the matrix stability route.**  `dyson_stability` needs the contractivity
condition `2 M² ∑ frob(A_i)² ≤ 1`, which for `d = 1` forces `|Im z| ≥ √2` and is exactly what
blocks the strip estimate of the smooth Lemma M.  In the scalar loop identity the denominator is
`1/g - m = z - g - m`, and `Im(1/g - m) = Im z - Im g - Im m`.  Both `Im m` and `Im g` have the
sign *opposite* to `Im z` (they are Cauchy transforms of positive measures), so
`|Im(1/g - m)| ≥ |Im z|` and

`|m - g| ≤ |Var| / |Im z|`

with **no lower bound on `|Im z|`**.  Combined with the *unconditional* sharp scalar variance
bound already in the project, `integral_norm_sq_fluctuation_scalar_le`
(`Probability/SharpTwoPoint.lean`: `∫ ‖T_N - m‖² ≤ 4 N⁻² (Im z)⁻⁴`, valid for all `0 < Im z`),
this yields `|m - g| ≤ 4 N⁻² |Im z|⁻⁵`, i.e. `WeightedStripBound 0 (fun _ => 1) k η₀ C_s 5`
for **every** `η₀`.  The only inputs still to be formalized are the two sign lemmas
`Im z * Im m ≤ 0` and `Im z * Im g ≤ 0` (see `docs/handoffs/SCALAR_LOOP.md`).

## Main results

* `loop_identity_of_dyson` — the exact identity `(m - g) * (z - m - g) = Var`;
* `loop_bootstrap` — `‖m - g‖ ≤ ‖Var‖ / |Im z|` from the exact identity and the two sign facts.
-/
import GUEStrongConvergence.Probability.DysonLimit

open MeasureTheory ProbabilityTheory Matrix Filter
open FreeProbability
open scoped Matrix.Norms.Frobenius ComplexOrder ENNReal NNReal Topology

namespace GUEStrongConvergence

noncomputable section

/-- **Exact scalar loop identity.**  If `g` solves the limit Dyson equation `(z - g) * g = 1` and
`m` satisfies the exact finite-`N` loop equation in the form `z * m - 1 - m² = Var` (i.e.
`Var = E[T_N²] - m²`), then `(m - g) * (z - m - g) = Var`, equivalently
`(m - g) * (1/g - m) = Var`.  No threshold on `|Im z|` and no concentration input is used. -/
theorem loop_identity_of_dyson {m g Var z : ℂ}
    (hg : (z - g) * g = 1) (hm : z * m - 1 - m ^ 2 = Var) :
    (m - g) * (z - m - g) = Var := by
  have hg' : z * g - 1 - g ^ 2 = 0 := by linear_combination hg
  linear_combination hm - hg'

/-- **Loop bootstrap.**  From the exact identity `(m - g) * (z - m - g) = Var` and the sign
facts `Im z * Im m ≤ 0`, `Im z * Im g ≤ 0` (both are Cauchy transforms of positive measures), the
denominator `z - m - g` has imaginary part of modulus at least `|Im z|`, hence
`‖m - g‖ ≤ ‖Var‖ / |Im z|`.  In particular a second-order variance bound gives a second-order
bound on `‖m - g‖` **uniformly down to the real axis**. -/
theorem loop_bootstrap {m g Var z : ℂ} (hz : z.im ≠ 0)
    (hid : (m - g) * (z - m - g) = Var)
    (hm : z.im * m.im ≤ 0) (hg : z.im * g.im ≤ 0) :
    ‖m - g‖ ≤ ‖Var‖ / |z.im| := by
  have hy : z.im ≠ 0 := hz
  have hden : |z.im| ≤ ‖z - m - g‖ := by
    have him : (z - m - g).im = z.im - m.im - g.im := by
      simp [Complex.sub_im]
    have hkey : z.im ^ 2 ≤ z.im * (z - m - g).im := by
      rw [him]
      nlinarith [hm, hg]
    have habs : |(z - m - g).im| ≤ ‖z - m - g‖ := Complex.abs_im_le_norm _
    have hsq : z.im ^ 2 ≤ (z - m - g).im ^ 2 := by nlinarith [hkey, sq_nonneg z.im]
    calc |z.im| = Real.sqrt (z.im ^ 2) := (Real.sqrt_sq_eq_abs z.im).symm
      _ ≤ Real.sqrt ((z - m - g).im ^ 2) := Real.sqrt_le_sqrt hsq
      _ = |(z - m - g).im| := Real.sqrt_sq_eq_abs _
      _ ≤ ‖z - m - g‖ := habs
  have hnorm : ‖m - g‖ * ‖z - m - g‖ = ‖Var‖ := by
    rw [← norm_mul, hid]
  have hpos : 0 < |z.im| := abs_pos.mpr hy
  have hdpos : 0 < ‖z - m - g‖ := lt_of_lt_of_le hpos hden
  have h1 : ‖m - g‖ = ‖Var‖ / ‖z - m - g‖ := by
    rw [eq_div_iff hdpos.ne']
    exact hnorm
  rw [h1]
  exact div_le_div_of_nonneg_left (norm_nonneg _) hpos hden

end
end GUEStrongConvergence
