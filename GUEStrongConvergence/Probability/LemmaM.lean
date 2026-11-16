/-
# Lemma M, step 1: the polynomial functional calculus as a Cauchy contour integral

This file supplies the **analytic infrastructure** for Lemma M, the smooth normalized-trace
comparison `|E[τ_N(f(H_N))] − τ(f(h))| ≤ C(f,A)/N²`: a contour-integral representation of the
polynomial functional calculus in a complex Banach algebra, and the resulting *quantitative*
comparison bound.  It is the piece that Mathlib is missing.

Mathlib has the Cauchy integral formula for scalar- and vector-valued functions
(`Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable`), but it does **not**
have the holomorphic functional calculus for Banach algebras: there is no lemma identifying
`Polynomial.aeval a P` with `(2πi)⁻¹ ∮ P(z) (z − a)⁻¹ dz`.  This file proves it, for a contour
that is a circle of radius strictly larger than `‖a‖`, together with the sharp resolvent norm
bounds that make the contour estimates effective.  Everything is developed for an arbitrary
complex Banach algebra `A` (`NormedRing`, `NormedAlgebra ℂ`, `CompleteSpace`, `NormOneClass`),
so it applies to matrices, `CStarMatrix`, and operator algebras alike.

## Main results

* `Ring.inverse_eq_of_mul_eq_one` — inverse uniqueness for `Ring.inverse` from two-sided
  inverse identities (the workhorse that keeps the algebra elementary);
* `geom_series_eq_one_add_mul_tsum`, `norm_tsum_geom_series_le` — the geometric series
  `∑ tⁿ = 1 + t ∑ tⁿ` and the uniform bound `‖∑ tⁿ‖ ≤ (1 − ‖t‖)⁻¹`;
* `resolvent_eq_smul_tsum` — `(z − a)⁻¹ = z⁻¹ • ∑ ((z⁻¹) • a)ⁿ` for `‖a‖ < ‖z‖`;
* `norm_resolvent_le` — `‖(z − a)⁻¹‖ ≤ (‖z‖ − ‖a‖)⁻¹`;
* `resolvent_eq_sum_range_add_tail` — the finite geometric expansion with explicit tail
  `(z − a)⁻¹ = ∑_{k<n} z^{-(k+1)} a^k + z^{-n} (a^n (z − a)⁻¹)`;
* `smul_resolvent_eq_one_add`, `resolvent_pow_smul_eq_sum_add` — the algebraic recursion
  `z (z−a)⁻¹ = 1 + a (z−a)⁻¹` and the monomial division identity
  `z^k (z−a)⁻¹ = ∑_{j<k} z^{k-1-j} a^j + a^k (z−a)⁻¹` (nonnegative powers only);
* `circleIntegral_resolvent` — **`∮_{|z|=R} (z − a)⁻¹ dz = 2πi • 1`**;
* `circleIntegral_resolvent_pow` — `∮_{|z|=R} z^k (z − a)⁻¹ dz = 2πi • a^k`;
* `circleIntegral_resolvent_polynomial` — **`P(a) = (2πi)⁻¹ ∮_{|z|=R} P(z) (z − a)⁻¹ dz`**
  for `P : ℂ[X]`, together with the real-coefficient form
  `circleIntegral_resolvent_polynomial_real` matching the project's `polyMatrix`;
* `apply_aeval_eq_circleIntegral` — the functional form
  `φ(P(a)) = (2πi)⁻¹ ∮ P(z) φ((z − a)⁻¹) dz` for `φ : A →L[ℂ] ℂ`;
* `norm_aeval_sub_le` — the quantitative contour bound
  `‖P(a) − P(b)‖ ≤ R · sup_{|z|=R}|P(z)| · sup_{|z|=R}‖(z−a)⁻¹ − (z−b)⁻¹‖`;
* `norm_aeval_sub_le_of_apply` — the state/trace form for two functionals on (possibly
  different) algebras, which is the shape consumed by the averaged-resolvent comparison;
* `continuousAt_resolvent_prod`, `continuousOn_integral_resolvent` — joint continuity of the
  resolvent and continuity of the *averaged* resolvent `z ↦ ∫_ω (z − H(ω))⁻¹ dμ`;
* `circleIntegral_integral_swap` — **Fubini for the circle contour**: for a bounded, jointly
  continuous scalar integrand, `∮_z ∫_ω = ∫_ω ∮_z`;
* `mean_aeval_sub_le_of_apply` — **the mean-level polynomial Lemma M reduction**:
  if the averaged resolvents satisfy `‖φ(∫_ω (z − H(ω))⁻¹) − ψ((z − a)⁻¹)‖ ≤ C` on the circle,
  then `‖∫_ω φ(P(H(ω))) − ψ(P(a))‖ ≤ R · sup|P| · C`; the real-coefficient form
  `mean_aeval_sub_le_of_apply_real` matches `polyMatrix P H` for `P : ℝ[X]`.

## What remains for the full Lemma M, and the exact missing inputs

The polynomial reduction is now *complete* modulo two inputs.  For a fixed polynomial `P`, a
circle radius `R` and a bound `r < R` for the finite family, `mean_aeval_sub_le_of_apply` gives

  `‖E[φ(P(H_N))] − ψ(P(a))‖ ≤ R · sup_{|z|=R}|P(z)| · sup_{|z|=R}‖φ(g_N(z)) − ψ(g(z))‖`,

where `g_N(z) = ∫_ω (z − H_N(ω))⁻¹ dμ` is the averaged resolvent (the contour/expectation
interchange is `circleIntegral_integral_swap`).  In the project's notation
`φ = trace ∘ (id_d ⊗ tr_N)` on `d × N` matrices and `ψ = trace ∘ matrixExpectation` on the
free Fock pencil, so the hypothesis `hC` is exactly the sharp averaged-resolvent comparison.
Two inputs are **not** in this file and are not available elsewhere in the project or Mathlib:

1. the sharp `O(N⁻²)` averaged-resolvent comparison for *general* pencils (`gueResolventMean`
   versus `operatorMatrixPencilCauchy`); main has only the honest `O(1/N)` bound
   `frob_gueResolventMean_sub_limit_le`, and the sharp two-point variance `SharpTwoPoint` is
   proved only for the scalar single-GUE model.  Given it, `hC = C₀/N²` and the displayed bound
   is `(R · sup|P| · C₀)/N² = C(P,A)/N²`;
2. the passage from polynomials to `C²`/smooth `f`: `f` is a real cutoff, not holomorphic, so
   the holomorphic contour identity alone cannot represent `f(H)`.  The standard route is the
   Cauchy–Pompeiu formula for an almost-analytic extension (a `∂̄` double integral), which
   Mathlib does not have; polynomial approximation cannot give a uniform `O(N⁻²)` rate because
   the contour constant grows with the degree.

Three further pieces of plumbing remain on the project side and are purely instantiation work:

* packaging the normalized trace (restricted to Hermitian matrices, then extended ℂ-linearly) as
  a `ContinuousLinearMap`, and converting the Frobenius-norm averaged-resolvent bound into the
  scalar bound `hC` (using `|trace M| ≤ d · ‖M‖_F`);
* **truncation**.  `mean_aeval_sub_le_of_apply` needs a *uniform in `ω`* spectral bound
  `‖H ω‖ ≤ r < R` (this is what makes one fixed circle work for every sample).  Gaussian
  matrices are unbounded, so one applies the theorem to the finite measure
  `μ.restrict {ω | ‖H ω‖ ≤ r}` — the statement is valid for any finite measure, not only a
  probability — and then controls the complement `{‖H ω‖ > r}` separately; by Gaussian
  concentration that complement is exponentially small in `N`, hence `o(N⁻²)`, for `r` above
  the limiting edge;
* the finite-measure (rather than probability) form of the conclusion compares
  `∫_E φ(P(H ω))` with the single value `ψ(P(a))`; if `E` is not of full measure the limit side
  must be multiplied by `μ(E)`, and the difference `(1 − μ(E)) · ‖ψ(P(a))‖` is again part of
  the (exponentially small) complement estimate.
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Polynomial.AlgebraMap

open scoped Topology Polynomial Ring Real
open Metric Filter
open MeasureTheory Complex

namespace GUEStrongConvergence

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [NormOneClass A]

/-! ### Inverse uniqueness and the geometric series -/

/-- **Uniqueness of `Ring.inverse`.** If `x` has the two-sided inverse `y`, then `x⁻¹ʳ = y`.
This is the elementary replacement for the (nonexistent) generic lemma in Mathlib. -/
theorem Ring.inverse_eq_of_mul_eq_one {x y : A} (h₁ : x * y = 1) (h₂ : y * x = 1) :
    x⁻¹ʳ = y := by
  have hx : IsUnit x := isUnit_iff_exists.mpr ⟨y, h₁, h₂⟩
  have hmul : x * x⁻¹ʳ = x * y := by rw [Ring.mul_inverse_cancel x hx, h₁]
  calc x⁻¹ʳ = x⁻¹ʳ * (x * x⁻¹ʳ) := by rw [Ring.mul_inverse_cancel x hx, mul_one]
    _ = x⁻¹ʳ * (x * y) := by rw [hmul]
    _ = (x⁻¹ʳ * x) * y := by rw [mul_assoc]
    _ = 1 * y := by rw [Ring.inverse_mul_cancel x hx]
    _ = y := one_mul y

/-- The geometric series in a complete normed algebra satisfies `∑ tⁿ = 1 + t ∑ tⁿ`. -/
theorem geom_series_eq_one_add_mul_tsum (t : A) (h : ‖t‖ < 1) :
    (∑' n : ℕ, t ^ n) = 1 + t * ∑' n : ℕ, t ^ n := by
  have h₁ : t * (∑' n : ℕ, t ^ n) = ∑' n : ℕ, t ^ (n + 1) :=
    geom_series_mul_shift t h
  have h₂ : (∑' n : ℕ, t ^ (n + 1)) = (∑' n : ℕ, t ^ n) - 1 :=
    geom_series_succ t h
  rw [h₁, h₂]
  abel

/-- Uniform bound for the geometric series, obtained from `∑ tⁿ = 1 + t ∑ tⁿ` alone
(no summability of norms is needed). -/
theorem norm_tsum_geom_series_le (t : A) (h : ‖t‖ < 1) :
    ‖∑' n : ℕ, t ^ n‖ ≤ (1 - ‖t‖)⁻¹ := by
  have hG := geom_series_eq_one_add_mul_tsum t h
  have hb : ‖∑' n : ℕ, t ^ n‖ ≤ 1 + ‖t‖ * ‖∑' n : ℕ, t ^ n‖ := by
    calc ‖∑' n : ℕ, t ^ n‖ = ‖1 + t * ∑' n : ℕ, t ^ n‖ := by
          conv_lhs => rw [hG]
      _ ≤ ‖(1 : A)‖ + ‖t * ∑' n : ℕ, t ^ n‖ := norm_add_le _ _
      _ ≤ 1 + ‖t‖ * ‖∑' n : ℕ, t ^ n‖ := by
          rw [norm_one]
          gcongr
          exact norm_mul_le _ _
  have hpos : 0 < 1 - ‖t‖ := by linarith
  rw [inv_eq_one_div, le_div_iff₀ hpos]
  nlinarith


/-! ### The resolvent as a geometric series, and its norm bound -/

/-- `(z • 1) * (z⁻¹ • 1) = 1` in a complex normed algebra. -/
lemma smul_one_mul_smul_one_inv {z : ℂ} (hz : z ≠ 0) :
    (z • (1 : A)) * (z⁻¹ • (1 : A)) = 1 := by
  rw [smul_mul_assoc, one_mul, smul_smul, mul_inv_cancel₀ hz, one_smul]

/-- `(z⁻¹ • 1) * (z • 1) = 1` in a complex normed algebra. -/
lemma smul_one_inv_mul_smul_one {z : ℂ} (hz : z ≠ 0) :
    (z⁻¹ • (1 : A)) * (z • (1 : A)) = 1 := by
  rw [smul_mul_assoc, one_mul, smul_smul, inv_mul_cancel₀ hz, one_smul]

/-- `(algebraMap ℂ A z)⁻¹ʳ = z⁻¹ • 1` for `z ≠ 0`. -/
lemma algebraMap_inverse_eq_smul_one {z : ℂ} (hz : z ≠ 0) :
    (algebraMap ℂ A z)⁻¹ʳ = z⁻¹ • (1 : A) := by
  refine Ring.inverse_eq_of_mul_eq_one ?_ ?_
  · rw [Algebra.algebraMap_eq_smul_one]
    exact smul_one_mul_smul_one_inv hz
  · rw [Algebra.algebraMap_eq_smul_one]
    exact smul_one_inv_mul_smul_one hz

/-- `‖z⁻¹ • a‖ < 1` when `‖a‖ < ‖z‖`. -/
lemma norm_smul_inv_lt_one {a : A} {z : ℂ} (hz : 0 < ‖z‖) (h : ‖a‖ < ‖z‖) :
    ‖z⁻¹ • a‖ < 1 := by
  rw [norm_smul, norm_inv, ← div_eq_inv_mul, div_lt_one hz]
  exact h

/-- **The resolvent as a geometric series**:
`(z − a)⁻¹ = z⁻¹ • ∑ ((z⁻¹) • a)ⁿ` whenever `‖a‖ < ‖z‖`. -/
theorem resolvent_eq_smul_tsum (a : A) {z : ℂ} (hz : 0 < ‖z‖) (h : ‖a‖ < ‖z‖) :
    resolvent a z = z⁻¹ • ∑' n : ℕ, (z⁻¹ • a) ^ n := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hz
  have ht : ‖z⁻¹ • a‖ < 1 := norm_smul_inv_lt_one hz h
  set t : A := z⁻¹ • a with htdef
  have hfac : algebraMap ℂ A z - a = algebraMap ℂ A z * (1 - t) := by
    rw [Algebra.algebraMap_eq_smul_one, htdef, mul_sub, mul_one, smul_mul_assoc, one_mul,
      smul_smul, mul_inv_cancel₀ hz0, one_smul]
  have hGmul : (∑' n : ℕ, t ^ n) * (1 - t) = 1 := geom_series_mul_neg t ht
  have hGmul' : (1 - t) * (∑' n : ℕ, t ^ n) = 1 := mul_neg_geom_series t ht
  refine Ring.inverse_eq_of_mul_eq_one ?_ ?_
  · calc (algebraMap ℂ A z - a) * (z⁻¹ • ∑' n : ℕ, t ^ n)
        = algebraMap ℂ A z * ((1 - t) * (z⁻¹ • ∑' n : ℕ, t ^ n)) := by
          rw [hfac, mul_assoc]
      _ = algebraMap ℂ A z * (z⁻¹ • ((1 - t) * ∑' n : ℕ, t ^ n)) := by rw [mul_smul_comm]
      _ = algebraMap ℂ A z * (z⁻¹ • (1 : A)) := by rw [hGmul']
      _ = 1 := by
          rw [Algebra.algebraMap_eq_smul_one]
          exact smul_one_mul_smul_one_inv hz0
  · calc (z⁻¹ • ∑' n : ℕ, t ^ n) * (algebraMap ℂ A z - a)
        = (z⁻¹ • ∑' n : ℕ, t ^ n) * (algebraMap ℂ A z * (1 - t)) := by rw [hfac]
      _ = z⁻¹ • ((∑' n : ℕ, t ^ n) * (algebraMap ℂ A z * (1 - t))) := by rw [smul_mul_assoc]
      _ = z⁻¹ • (((∑' n : ℕ, t ^ n) * algebraMap ℂ A z) * (1 - t)) := by rw [mul_assoc]
      _ = z⁻¹ • ((algebraMap ℂ A z * ∑' n : ℕ, t ^ n) * (1 - t)) := by
          rw [Algebra.commutes]
      _ = z⁻¹ • (algebraMap ℂ A z * ((∑' n : ℕ, t ^ n) * (1 - t))) := by rw [mul_assoc]
      _ = z⁻¹ • (algebraMap ℂ A z * 1) := by rw [hGmul]
      _ = 1 := by
          rw [mul_one, Algebra.algebraMap_eq_smul_one, smul_smul, inv_mul_cancel₀ hz0, one_smul]

/-- **Norm bound for the resolvent**: `‖(z − a)⁻¹‖ ≤ (‖z‖ − ‖a‖)⁻¹` for `‖a‖ < ‖z‖`. -/
theorem norm_resolvent_le (a : A) {z : ℂ} (hz : 0 < ‖z‖) (h : ‖a‖ < ‖z‖) :
    ‖resolvent a z‖ ≤ (‖z‖ - ‖a‖)⁻¹ := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hz
  have ht : ‖z⁻¹ • a‖ < 1 := norm_smul_inv_lt_one hz h
  rw [resolvent_eq_smul_tsum a hz h]
  have hG := norm_tsum_geom_series_le (z⁻¹ • a) ht
  have hpos : 0 < ‖z‖ - ‖a‖ := by linarith
  have htn : ‖z⁻¹ • a‖ = ‖z‖⁻¹ * ‖a‖ := by rw [norm_smul, norm_inv]
  calc ‖z⁻¹ • ∑' n : ℕ, (z⁻¹ • a) ^ n‖
      = ‖z⁻¹‖ * ‖∑' n : ℕ, (z⁻¹ • a) ^ n‖ := norm_smul _ _
    _ = ‖z‖⁻¹ * ‖∑' n : ℕ, (z⁻¹ • a) ^ n‖ := by rw [norm_inv]
    _ ≤ ‖z‖⁻¹ * (1 - ‖z⁻¹ • a‖)⁻¹ := by
        gcongr
    _ = (‖z‖ - ‖a‖)⁻¹ := by
        rw [htn]
        field_simp


/-! ### The finite geometric expansion with explicit tail -/

/-- **Finite geometric expansion**: `∑ tⁿ = ∑_{k<n} t^k + t^n ∑ tⁿ`. -/
theorem geom_series_eq_sum_range_add_pow_mul (t : A) (h : ‖t‖ < 1) (n : ℕ) :
    (∑' k : ℕ, t ^ k) = ∑ k ∈ Finset.range n, t ^ k + t ^ n * ∑' k : ℕ, t ^ k := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : t ^ n * (∑' k : ℕ, t ^ k)
          = t ^ n + t ^ (n + 1) * ∑' k : ℕ, t ^ k := by
        conv_lhs => rw [geom_series_eq_one_add_mul_tsum t h]
        rw [mul_add, mul_one, ← mul_assoc, ← pow_succ]
      calc (∑' k : ℕ, t ^ k)
          = ∑ k ∈ Finset.range n, t ^ k + t ^ n * ∑' k : ℕ, t ^ k := ih
        _ = ∑ k ∈ Finset.range n, t ^ k
              + (t ^ n + t ^ (n + 1) * ∑' k : ℕ, t ^ k) := by rw [hstep]
        _ = ∑ k ∈ Finset.range (n + 1), t ^ k + t ^ (n + 1) * ∑' k : ℕ, t ^ k := by
              rw [Finset.sum_range_succ]
              abel

/-- **The resolvent with explicit geometric tail**:
`(z − a)⁻¹ = ∑_{k<n} z^{-(k+1)} a^k + z^{-n} (a^n (z − a)⁻¹)` for `‖a‖ < ‖z‖`. -/
theorem resolvent_eq_sum_range_add_tail (a : A) {z : ℂ} (hz : 0 < ‖z‖) (h : ‖a‖ < ‖z‖)
    (n : ℕ) :
    resolvent a z
      = ∑ k ∈ Finset.range n, (z⁻¹) ^ (k + 1) • a ^ k
        + (z⁻¹) ^ n • (a ^ n * resolvent a z) := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hz
  have ht : ‖z⁻¹ • a‖ < 1 := norm_smul_inv_lt_one hz h
  set t : A := z⁻¹ • a with htdef
  have hG : (∑' k : ℕ, t ^ k) = ∑ k ∈ Finset.range n, t ^ k + t ^ n * ∑' k : ℕ, t ^ k :=
    geom_series_eq_sum_range_add_pow_mul t ht n
  have hzg : z • resolvent a z = ∑' k : ℕ, t ^ k := by
    rw [resolvent_eq_smul_tsum a hz h, smul_smul, mul_inv_cancel₀ hz0, one_smul]
  have hterm : ∀ k : ℕ, z⁻¹ • t ^ k = (z⁻¹) ^ (k + 1) • a ^ k := by
    intro k
    rw [htdef, smul_pow, smul_smul, mul_comm, ← pow_succ]
  have htail : z⁻¹ • (t ^ n * (∑' k : ℕ, t ^ k)) = (z⁻¹) ^ n • (a ^ n * resolvent a z) := by
    have hsplit : t ^ n * (z • resolvent a z) = ((z⁻¹) ^ n * z) • (a ^ n * resolvent a z) := by
      rw [htdef, smul_pow, smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [← hzg, hsplit, smul_smul, show z⁻¹ * ((z⁻¹) ^ n * z) = (z⁻¹) ^ n by field_simp]
  conv_lhs => rw [resolvent_eq_smul_tsum a hz h]
  rw [hG, smul_add, Finset.smul_sum]
  rw [show (∑ k ∈ Finset.range n, z⁻¹ • t ^ k) = ∑ k ∈ Finset.range n, (z⁻¹) ^ (k + 1) • a ^ k
    from Finset.sum_congr rfl fun k _ => hterm k, htail]


/-! ### Circle-integral tools -/

/-- **Left multiplication by a fixed algebra element commutes with the circle integral.** -/
theorem circleIntegral_const_mul_of_circleIntegrable (c : A) {f : ℂ → A} {R : ℝ}
    (hf : CircleIntegrable f 0 R) :
    (∮ z in C(0, R), c * f z) = c * ∮ z in C(0, R), f z := by
  rw [circleIntegral, circleIntegral]
  change (∫ θ in 0..2 * π, deriv (circleMap 0 R) θ • (c * f (circleMap 0 R θ)))
      = c * ∫ θ in 0..2 * π, deriv (circleMap 0 R) θ • f (circleMap 0 R θ)
  rw [show (∫ θ in 0..2 * π, deriv (circleMap 0 R) θ • (c * f (circleMap 0 R θ)))
      = ∫ θ in 0..2 * π,
          (NonUnitalAlgHom.Lmul ℂ A c) (deriv (circleMap 0 R) θ • f (circleMap 0 R θ)) from by
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    show deriv (circleMap 0 R) θ • (c * f (circleMap 0 R θ))
        = c * (deriv (circleMap 0 R) θ • f (circleMap 0 R θ))
    rw [mul_smul_comm]]
  exact ContinuousLinearMap.intervalIntegral_comp_comm (NonUnitalAlgHom.Lmul ℂ A c) hf.out

/-- The resolvent is continuous on any circle of radius `R > ‖a‖`. -/
theorem continuousOn_resolvent {a : A} {R : ℝ} (hR : ‖a‖ < R) :
    ContinuousOn (fun z : ℂ => resolvent a z) (sphere 0 R) := by
  have hsub : sphere 0 R ⊆ resolventSet ℂ a := by
    intro z hz
    have hz' : ‖z‖ = R := by simpa using Metric.mem_sphere.mp hz
    exact spectrum.mem_resolventSet_of_norm_lt (by rw [hz']; exact hR)
  exact (HasDerivAt.continuousOn
    (fun z hz => spectrum.hasDerivAt_resolvent_const_left hz)).mono hsub

/-- `∮_{|z|=R} (z⁻¹)^{k+1} dz` is `2πi` for `k = 0` and `0` otherwise. -/
theorem circleIntegral_inv_pow_succ {R : ℝ} (hR : 0 < R) (k : ℕ) :
    (∮ z in C(0, R), ((z⁻¹ : ℂ) ^ (k + 1))) = if k = 0 then 2 * π * I else 0 := by
  have hR0 : R ≠ 0 := ne_of_gt hR
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [ite_eq_left rfl]
    simp only [Nat.zero_add, pow_one]
    simpa using circleIntegral.integral_sub_center_inv (0 : ℂ) hR0
  · rw [ite_eq_right hk.ne']
    have hcongr : (∮ z in C(0, R), ((z⁻¹ : ℂ) ^ (k + 1)))
        = ∮ z in C(0, R), (z - 0) ^ (-((k + 1 : ℕ) : ℤ)) := by
      refine circleIntegral.integral_congr hR.le (fun z hz => ?_)
      have hz0 : z ≠ 0 := by
        intro h
        have hz' : ‖z‖ = R := by simpa using Metric.mem_sphere.mp hz
        rw [h] at hz'
        simp at hz'
        linarith
      rw [sub_zero, zpow_neg_coe_of_pos _ (Nat.succ_pos k), inv_pow]
    rw [hcongr]
    have hne : (-((k + 1 : ℕ) : ℤ)) ≠ -1 := by omega
    rw [circleIntegral.integral_sub_zpow_of_ne hne 0 0 R]

/-! ### The circle integral of the resolvent -/

/-- The finite geometric partial sums of the resolvent. -/
def resolventPartial (a : A) (n : ℕ) (z : ℂ) : A :=
  ∑ k ∈ Finset.range n, (z⁻¹) ^ (k + 1) • a ^ k

lemma sphere_ne_zero {R : ℝ} (hR : 0 < R) : ∀ z ∈ sphere (0 : ℂ) R, z ≠ 0 := by
  intro z hz h
  have hz' : ‖z‖ = R := by simpa using Metric.mem_sphere.mp hz
  rw [h] at hz'
  simp at hz'
  linarith

/-- The partial sums are continuous, hence circle integrable. -/
theorem circleIntegrable_resolventPartial {R : ℝ} (hR : 0 < R) (a : A) (n : ℕ) :
    CircleIntegrable (resolventPartial a n) 0 R := by
  refine ContinuousOn.circleIntegrable hR.le ?_
  refine continuousOn_finsetSum _ (fun k _ => ?_)
  exact ((continuousOn_id.inv₀ (sphere_ne_zero hR)).pow (k + 1)).smul continuousOn_const

/-- The circle integral of the resolvent is `2πi • 1`. -/
theorem circleIntegral_resolvent (a : A) {R : ℝ} (hR : ‖a‖ < R) :
    (∮ z in C(0, R), resolvent a z) = (2 * π * I : ℂ) • (1 : A) := by
  have hRpos : 0 < R := lt_of_le_of_lt (norm_nonneg a) hR
  have hne := sphere_ne_zero hRpos
  have hres_int : CircleIntegrable (fun z : ℂ => resolvent a z) 0 R :=
    (continuousOn_resolvent hR).circleIntegrable hRpos.le
  -- value of the partial-sum integrals
  have hSval : ∀ n, 1 ≤ n → (∮ z in C(0, R), resolventPartial a n z)
      = (2 * π * I : ℂ) • (1 : A) := by
    intro n hn
    have hstep1 : (∮ z in C(0, R), resolventPartial a n z)
        = ∑ k ∈ Finset.range n,
            ∮ z in C(0, R), ((z⁻¹ : ℂ) ^ (k + 1) • a ^ k) := by
      refine circleIntegral.integral_fun_sum (fun k _ => ?_)
      exact (((continuousOn_id.inv₀ hne).pow (k + 1)).smul
        continuousOn_const).circleIntegrable hRpos.le
    rw [hstep1, Finset.sum_congr rfl
      (fun k _ => circleIntegral.integral_smul_const (fun z : ℂ => (z⁻¹) ^ (k + 1)) (a ^ k) 0 R)]
    rw [Finset.sum_eq_single (0 : ℕ)]
    · rw [circleIntegral_inv_pow_succ hRpos 0, ite_eq_left rfl]
      simp
    · intro k _ hk
      rw [circleIntegral_inv_pow_succ hRpos k, ite_eq_right hk, zero_smul]
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega : 0 < n)) h
  -- the tail is uniformly small
  have htail : ∀ n, 1 ≤ n →
      ‖(∮ z in C(0, R), resolvent a z) - (2 * π * I : ℂ) • (1 : A)‖
        ≤ (2 * π * R * (R - ‖a‖)⁻¹) * (‖a‖ / R) ^ n := by
    intro n hn
    have heq : (∮ z in C(0, R), resolvent a z) - (2 * π * I : ℂ) • (1 : A)
        = ∮ z in C(0, R), resolvent a z - resolventPartial a n z := by
      rw [← hSval n hn,
        circleIntegral.integral_sub hres_int (circleIntegrable_resolventPartial hRpos a n)]
    rw [heq]
    have hbound : ∀ z ∈ sphere (0 : ℂ) R,
        ‖resolvent a z - resolventPartial a n z‖
          ≤ (R ^ n)⁻¹ * ‖a‖ ^ n * (R - ‖a‖)⁻¹ := by
      intro z hz
      have hz' : ‖z‖ = R := by simpa using Metric.mem_sphere.mp hz
      have hzpos : 0 < ‖z‖ := by rw [hz']; exact hRpos
      have htailz := resolvent_eq_sum_range_add_tail a hzpos (by rw [hz']; exact hR) n
      have hzero : resolvent a z - resolventPartial a n z
          = (z⁻¹) ^ n • (a ^ n * resolvent a z) := by
        conv_lhs => rw [htailz]
        rw [resolventPartial]
        abel
      have hRle : ‖resolvent a z‖ ≤ (R - ‖a‖)⁻¹ := by
        have h := norm_resolvent_le a hzpos (by rw [hz']; exact hR)
        rwa [hz'] at h
      have h1 : ‖a ^ n * resolvent a z‖ ≤ ‖a‖ ^ n * (R - ‖a‖)⁻¹ := by
        have hm := NonUnitalSeminormedRing.norm_mul_le (a ^ n) (resolvent a z)
        refine hm.trans ?_
        exact mul_le_mul (norm_pow_le a n) hRle (norm_nonneg _) (by positivity)
      have hcoef : ‖(z⁻¹) ^ n‖ ≤ (R ^ n)⁻¹ := by
        calc ‖(z⁻¹) ^ n‖ ≤ ‖z⁻¹‖ ^ n := norm_pow_le _ n
          _ = (‖z‖ ^ n)⁻¹ := by rw [norm_inv, ← inv_pow]
          _ = (R ^ n)⁻¹ := by rw [hz']
      rw [hzero]
      calc ‖(z⁻¹) ^ n • (a ^ n * resolvent a z)‖
          = ‖(z⁻¹) ^ n‖ * ‖a ^ n * resolvent a z‖ := norm_smul _ _
        _ ≤ (R ^ n)⁻¹ * (‖a‖ ^ n * (R - ‖a‖)⁻¹) :=
            mul_le_mul hcoef h1 (norm_nonneg _) (by positivity)
        _ = (R ^ n)⁻¹ * ‖a‖ ^ n * (R - ‖a‖)⁻¹ := by ring
    have hnorm := circleIntegral.norm_integral_le_of_norm_le_const hRpos.le
      (fun z hz => hbound z hz)
    refine hnorm.trans (le_of_eq ?_)
    rw [div_pow]
    have hRne : R ≠ 0 := ne_of_gt hRpos
    field_simp
  -- take the limit
  have hlim : Tendsto (fun n : ℕ => (2 * π * R * (R - ‖a‖)⁻¹) * (‖a‖ / R) ^ n)
      atTop (𝓝 0) := by
    have hlt : ‖a‖ / R < 1 := by
      rw [div_lt_one hRpos]
      exact hR
    have h0 : 0 ≤ ‖a‖ / R := by positivity
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h0 hlt).const_mul
      (2 * π * R * (R - ‖a‖)⁻¹)
  have hle : ‖(∮ z in C(0, R), resolvent a z) - (2 * π * I : ℂ) • (1 : A)‖ ≤ 0 := by
    refine le_of_tendsto_of_tendsto tendsto_const_nhds hlim ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact htail n hn
  have hnorm0 : ‖(∮ z in C(0, R), resolvent a z) - (2 * π * I : ℂ) • (1 : A)‖ = 0 :=
    le_antisymm hle (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm0)


/-- The key algebraic recursion for the resolvent: `z • R = 1 + a R`, `R = z⁻¹ + z⁻¹ a R`. -/
theorem smul_resolvent_eq_one_add (a : A) {z : ℂ} (hz : 0 < ‖z‖) (h : ‖a‖ < ‖z‖) :
    z • resolvent a z = 1 + a * resolvent a z := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hz
  have ht : ‖z⁻¹ • a‖ < 1 := norm_smul_inv_lt_one hz h
  set t : A := z⁻¹ • a with htdef
  have hzg : z • resolvent a z = ∑' k : ℕ, t ^ k := by
    rw [resolvent_eq_smul_tsum a hz h, smul_smul, mul_inv_cancel₀ hz0, one_smul]
  rw [hzg, geom_series_eq_one_add_mul_tsum t ht]
  congr 1
  rw [htdef, ← hzg, smul_mul_assoc, mul_smul_comm, smul_smul, inv_mul_cancel₀ hz0, one_smul]

/-- **The monomial division identity**:
`z^k (z − a)⁻¹ = ∑_{j<k} z^{k-1-j} a^j + a^k (z − a)⁻¹`, with only nonnegative powers. -/
theorem resolvent_pow_smul_eq_sum_add (a : A) {z : ℂ} (hz : 0 < ‖z‖) (h : ‖a‖ < ‖z‖) (k : ℕ) :
    (z : ℂ) ^ k • resolvent a z
      = ∑ j ∈ Finset.range k, (z : ℂ) ^ (k - 1 - j) • a ^ j + a ^ k * resolvent a z := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep : (z : ℂ) ^ (k + 1) • resolvent a z
          = z • ((z : ℂ) ^ k • resolvent a z) := by rw [pow_succ', smul_smul]
      rw [hstep, ih, smul_add, Finset.smul_sum]
      have hterm : ∀ j ∈ Finset.range k, z • ((z : ℂ) ^ (k - 1 - j) • a ^ j)
          = (z : ℂ) ^ (k - j) • a ^ j := by
        intro j hj
        have hj' : j < k := Finset.mem_range.mp hj
        rw [smul_smul, ← pow_succ']
        rw [show k - 1 - j + 1 = k - j by omega]
      have htail : z • (a ^ k * resolvent a z)
          = a ^ k + a ^ (k + 1) * resolvent a z := by
        have hcomm : z • (a ^ k * resolvent a z) = a ^ k * (z • resolvent a z) := by
          rw [Algebra.smul_def, Algebra.smul_def]
          rw [← mul_assoc, Algebra.commutes, mul_assoc]
        rw [hcomm, smul_resolvent_eq_one_add a hz h, mul_add, mul_one, ← mul_assoc, ← pow_succ]
      rw [Finset.sum_congr rfl hterm, htail]
      have hsum : (∑ j ∈ Finset.range (k + 1), (z : ℂ) ^ (k + 1 - 1 - j) • a ^ j)
          = ∑ j ∈ Finset.range k, (z : ℂ) ^ (k - j) • a ^ j + a ^ k := by
        rw [Finset.sum_range_succ,
          Finset.sum_congr rfl (fun j hj => by
            have hj' : j < k := Finset.mem_range.mp hj
            rw [show k + 1 - 1 - j = k - j by omega]),
          show (z : ℂ) ^ (k + 1 - 1 - k) • a ^ k = a ^ k by
            rw [show k + 1 - 1 - k = 0 by omega, pow_zero, one_smul]]
      rw [hsum]
      abel

/-- `∮_{|z|=R} z^m dz = 0` for `R > 0` and `m ≥ 0`. -/
theorem circleIntegral_pow {R : ℝ} (hR : 0 < R) (m : ℕ) :
    (∮ z in C(0, R), ((z : ℂ) ^ m)) = 0 := by
  have hcongr : (∮ z in C(0, R), ((z : ℂ) ^ m))
      = ∮ z in C(0, R), (z - 0) ^ ((m : ℤ)) := by
    refine circleIntegral.integral_congr hR.le (fun z _ => ?_)
    rw [sub_zero, zpow_natCast]
  rw [hcongr]
  have hm : ((m : ℤ)) ≠ -1 := by omega
  rw [circleIntegral.integral_sub_zpow_of_ne hm 0 0 R]

/-- **Monomial Cauchy identity**: `∮_{|z|=R} z^k (z − a)⁻¹ dz = 2πi a^k` for `‖a‖ < R`. -/
theorem circleIntegral_resolvent_pow (a : A) {R : ℝ} (hR : ‖a‖ < R) (k : ℕ) :
    (∮ z in C(0, R), (z : ℂ) ^ k • resolvent a z)
      = (2 * π * I : ℂ) • a ^ k := by
  have hRpos : 0 < R := lt_of_le_of_lt (norm_nonneg a) hR
  have hres_int : CircleIntegrable (fun z : ℂ => resolvent a z) 0 R :=
    (continuousOn_resolvent hR).circleIntegrable hRpos.le
  have hsum_int : CircleIntegrable
      (fun z : ℂ => ∑ j ∈ Finset.range k, (z : ℂ) ^ (k - 1 - j) • a ^ j) 0 R := by
    refine ContinuousOn.circleIntegrable hRpos.le ?_
    refine continuousOn_finsetSum _ (fun j _ => ?_)
    exact (continuousOn_id.pow (k - 1 - j)).smul continuousOn_const
  have htail_int : CircleIntegrable (fun z : ℂ => a ^ k * resolvent a z) 0 R := by
    refine ContinuousOn.circleIntegrable hRpos.le ?_
    exact continuousOn_const.mul (continuousOn_resolvent hR)
  -- replace the integrand by the explicit polynomial plus the constant multiple
  have hcongr : (∮ z in C(0, R), (z : ℂ) ^ k • resolvent a z)
      = ∮ z in C(0, R),
          ((∑ j ∈ Finset.range k, (z : ℂ) ^ (k - 1 - j) • a ^ j) + a ^ k * resolvent a z) := by
    refine circleIntegral.integral_congr hRpos.le (fun z hz => ?_)
    have hz' : ‖z‖ = R := by simpa using Metric.mem_sphere.mp hz
    exact resolvent_pow_smul_eq_sum_add a (by rw [hz']; exact hRpos) (by rw [hz']; exact hR) k
  rw [hcongr, circleIntegral.integral_add hsum_int htail_int]
  -- the polynomial part integrates to zero
  have hzero : (∮ z in C(0, R),
      ∑ j ∈ Finset.range k, (z : ℂ) ^ (k - 1 - j) • a ^ j) = 0 := by
    rw [circleIntegral.integral_fun_sum (fun j _ => ?_)]
    · refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [circleIntegral.integral_smul_const, circleIntegral_pow hRpos (k - 1 - j), zero_smul]
    · exact ((continuousOn_id.pow (k - 1 - j)).smul continuousOn_const).circleIntegrable hRpos.le
  rw [hzero, zero_add, circleIntegral_const_mul_of_circleIntegrable (a ^ k) hres_int,
    circleIntegral_resolvent a hR]
  rw [mul_smul_comm, mul_one]

/-- **Polynomial Cauchy identity**: for every complex polynomial `P`,
`P(a) = (2πi)⁻¹ ∮_{|z|=R} P(z) (z − a)⁻¹ dz` whenever `‖a‖ < R`. -/
theorem circleIntegral_resolvent_polynomial (a : A) {R : ℝ} (hR : ‖a‖ < R) (P : ℂ[X]) :
    (2 * π * I : ℂ)⁻¹ • (∮ z in C(0, R), (P.eval z) • resolvent a z) = Polynomial.aeval a P := by
  have hRpos : 0 < R := lt_of_le_of_lt (norm_nonneg a) hR
  set n := P.natDegree + 1 with hn
  have hP : Polynomial.aeval a P = ∑ k ∈ Finset.range n, P.coeff k • a ^ k :=
    Polynomial.aeval_eq_sum_range (p := P) a
  have hPz : ∀ z : ℂ, P.eval z = ∑ k ∈ Finset.range n, P.coeff k * z ^ k := by
    intro z
    rw [Polynomial.eval_eq_sum_range, hn]
  have hfun : (fun z : ℂ => (P.eval z) • resolvent a z)
      = fun z : ℂ => ∑ k ∈ Finset.range n, P.coeff k • ((z : ℂ) ^ k • resolvent a z) := by
    funext z
    rw [hPz, Finset.sum_smul]
    exact Finset.sum_congr rfl (fun k _ => by rw [mul_smul])
  have hterm_int : ∀ k ∈ Finset.range n, CircleIntegrable
      (fun z : ℂ => P.coeff k • ((z : ℂ) ^ k • resolvent a z)) 0 R := by
    intro k _
    exact ContinuousOn.circleIntegrable hRpos.le
      (continuousOn_const.smul ((continuousOn_id.pow k).smul (continuousOn_resolvent hR)))
  rw [hfun, circleIntegral.integral_fun_sum hterm_int]
  have hval : (∑ k ∈ Finset.range n,
      ∮ z in C(0, R), P.coeff k • ((z : ℂ) ^ k • resolvent a z))
      = (2 * π * I : ℂ) • ∑ k ∈ Finset.range n, P.coeff k • a ^ k := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [circleIntegral.integral_smul, circleIntegral_resolvent_pow a hR k, smul_smul, smul_smul,
      mul_comm]
  rw [hval, ← hP, smul_smul]
  rw [show (2 * π * I : ℂ)⁻¹ * (2 * π * I) = 1 by field_simp]
  exact one_smul _ _


/-! ### Quantitative contour comparison bounds -/

/-- A continuous linear functional commutes with the circle integral. -/
theorem ContinuousLinearMap.circleIntegral_comp (φ : A →L[ℂ] ℂ) {f : ℂ → A} {R : ℝ}
    (hf : CircleIntegrable f 0 R) :
    φ (∮ z in C(0, R), f z) = ∮ z in C(0, R), φ (f z) := by
  rw [circleIntegral, circleIntegral, ← ContinuousLinearMap.intervalIntegral_comp_comm φ hf.out]
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  rw [ContinuousLinearMap.map_smul]

/-- **Real-polynomial form**, matching the project's `polyMatrix P H = aeval H P` for
`P : ℝ[X]`. -/
theorem circleIntegral_resolvent_polynomial_real (a : A) {R : ℝ} (hR : ‖a‖ < R) (P : ℝ[X]) :
    (2 * π * I : ℂ)⁻¹ • (∮ z in C(0, R),
        ((P.map (algebraMap ℝ ℂ)).eval z) • resolvent a z)
      = Polynomial.aeval a P := by
  rw [circleIntegral_resolvent_polynomial a hR (P.map (algebraMap ℝ ℂ))]
  rw [Polynomial.aeval_map_algebraMap]

/-- **Functional Cauchy identity**: `φ(P(a)) = (2πi)⁻¹ ∮ P(z) φ((z − a)⁻¹) dz`. -/
theorem apply_aeval_eq_circleIntegral (φ : A →L[ℂ] ℂ) (a : A) {R : ℝ}
    (hR : ‖a‖ < R) (P : ℂ[X]) :
    φ (Polynomial.aeval a P)
      = (2 * π * I : ℂ)⁻¹ * ∮ z in C(0, R), P.eval z * φ (resolvent a z) := by
  have hRpos : 0 < R := lt_of_le_of_lt (norm_nonneg a) hR
  have hpint : CircleIntegrable (fun z : ℂ => P.eval z • resolvent a z) 0 R := by
    refine ContinuousOn.circleIntegrable hRpos.le ?_
    exact (Polynomial.continuous P).continuousOn.smul (continuousOn_resolvent hR)
  conv_lhs => rw [← circleIntegral_resolvent_polynomial a hR P]
  rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.circleIntegral_comp φ hpint]
  congr 1
  refine circleIntegral.integral_congr hRpos.le (fun z _ => ?_)
  rw [ContinuousLinearMap.map_smul, smul_eq_mul]

/-- The sphere of positive radius is nonempty. -/
lemma sphere_nonempty {R : ℝ} (hR : 0 < R) : (sphere (0 : ℂ) R).Nonempty :=
  ⟨(R : ℂ), by
    rw [Metric.mem_sphere, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]⟩

/-- **Quantitative contour comparison (operator form)**: if the resolvents differ by at most
`C` and `|P| ≤ M` on the circle of radius `R`, then `‖P(a) − P(b)‖ ≤ R M C`. -/
theorem norm_aeval_sub_le (a b : A) (P : ℂ[X]) {R M C : ℝ}
    (ha : ‖a‖ < R) (hb : ‖b‖ < R)
    (hM : ∀ z ∈ sphere (0 : ℂ) R, ‖P.eval z‖ ≤ M)
    (hC : ∀ z ∈ sphere (0 : ℂ) R, ‖resolvent a z - resolvent b z‖ ≤ C) :
    ‖Polynomial.aeval a P - Polynomial.aeval b P‖ ≤ R * M * C := by
  have hRpos : 0 < R := lt_of_le_of_lt (norm_nonneg a) ha
  obtain ⟨z₀, hz₀⟩ := sphere_nonempty hRpos
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM z₀ hz₀)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC z₀ hz₀)
  have hint1 : CircleIntegrable (fun z : ℂ => P.eval z • resolvent a z) 0 R := by
    refine ContinuousOn.circleIntegrable hRpos.le ?_
    exact (Polynomial.continuous P).continuousOn.smul (continuousOn_resolvent ha)
  have hint2 : CircleIntegrable (fun z : ℂ => P.eval z • resolvent b z) 0 R := by
    refine ContinuousOn.circleIntegrable hRpos.le ?_
    exact (Polynomial.continuous P).continuousOn.smul (continuousOn_resolvent hb)
  have hsub : Polynomial.aeval a P - Polynomial.aeval b P
      = (2 * π * I : ℂ)⁻¹ • ∮ z in C(0, R),
          (P.eval z • (resolvent a z - resolvent b z)) := by
    conv_lhs => rw [← circleIntegral_resolvent_polynomial a ha P,
      ← circleIntegral_resolvent_polynomial b hb P]
    rw [← smul_sub, ← circleIntegral.integral_sub hint1 hint2]
    congr 1
    refine circleIntegral.integral_congr hRpos.le (fun z _ => ?_)
    rw [smul_sub]
  rw [hsub]
  have hbound : ∀ z ∈ sphere (0 : ℂ) R,
      ‖P.eval z • (resolvent a z - resolvent b z)‖ ≤ M * C := by
    intro z hz
    rw [norm_smul]
    exact mul_le_mul (hM z hz) (hC z hz) (norm_nonneg _) hM0
  refine (circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hRpos.le
    hbound).trans (le_of_eq ?_)
  ring

/-- **Quantitative contour comparison (state/trace form)**: for continuous linear functionals
`φ`, `ψ` on possibly different algebras, the difference of `φ(P(a))` and `ψ(P(b))` is bounded
by `R · sup|P| · sup‖φ((z−a)⁻¹) − ψ((z−b)⁻¹)‖` on the circle of radius `R`.

This is the exact shape consumed by the averaged-resolvent comparison: take `φ` the normalized
trace on the finite matrix algebra and `ψ` the trace composed with the vacuum expectation. -/
theorem norm_aeval_sub_le_of_apply
    {B : Type*} [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B] [NormOneClass B]
    (φ : A →L[ℂ] ℂ) (ψ : B →L[ℂ] ℂ) (a : A) (b : B) (P : ℂ[X]) {R M C : ℝ}
    (ha : ‖a‖ < R) (hb : ‖b‖ < R)
    (hM : ∀ z ∈ sphere (0 : ℂ) R, ‖P.eval z‖ ≤ M)
    (hC : ∀ z ∈ sphere (0 : ℂ) R, ‖φ (resolvent a z) - ψ (resolvent b z)‖ ≤ C) :
    ‖φ (Polynomial.aeval a P) - ψ (Polynomial.aeval b P)‖ ≤ R * M * C := by
  have hRpos : 0 < R := lt_of_le_of_lt (norm_nonneg a) ha
  obtain ⟨z₀, hz₀⟩ := sphere_nonempty hRpos
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM z₀ hz₀)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC z₀ hz₀)
  have hint1 : CircleIntegrable (fun z : ℂ => P.eval z * φ (resolvent a z)) 0 R := by
    refine ContinuousOn.circleIntegrable hRpos.le ?_
    exact (Polynomial.continuous P).continuousOn.mul
      (φ.continuous.comp_continuousOn (continuousOn_resolvent ha))
  have hint2 : CircleIntegrable (fun z : ℂ => P.eval z * ψ (resolvent b z)) 0 R := by
    refine ContinuousOn.circleIntegrable hRpos.le ?_
    exact (Polynomial.continuous P).continuousOn.mul
      (ψ.continuous.comp_continuousOn (continuousOn_resolvent hb))
  rw [apply_aeval_eq_circleIntegral φ a ha P, apply_aeval_eq_circleIntegral ψ b hb P]
  set I1 : ℂ := ∮ z in C(0, R), P.eval z * φ (resolvent a z) with hI1
  set I2 : ℂ := ∮ z in C(0, R), P.eval z * ψ (resolvent b z) with hI2
  have hfac : (2 * π * I : ℂ)⁻¹ * I1 - (2 * π * I : ℂ)⁻¹ * I2
      = (2 * π * I : ℂ)⁻¹ * (I1 - I2) := (mul_sub _ _ _).symm
  have hI : I1 - I2 = ∮ z in C(0, R),
      (P.eval z * φ (resolvent a z) - P.eval z * ψ (resolvent b z)) := by
    rw [hI1, hI2, circleIntegral.integral_sub hint1 hint2]
  rw [hfac, hI]
  have hbound : ∀ z ∈ sphere (0 : ℂ) R,
      ‖P.eval z * φ (resolvent a z) - P.eval z * ψ (resolvent b z)‖ ≤ M * C := by
    intro z hz
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (hM z hz) (hC z hz) (norm_nonneg _) hM0
  have hmain := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    (c := 0) hRpos.le hbound
  simpa only [smul_eq_mul] using hmain.trans (le_of_eq (by ring : R * (M * C) = R * M * C))


/-! ### Interchanging the circle integral with a probability average (Fubini) -/

/-- **Fubini for circle integrals**: a bounded, jointly continuous scalar integrand may be
integrated over the circle and over a finite measure in either order.  This is the step that
upgrades the pointwise contour comparison to the comparison of means. -/
theorem circleIntegral_integral_swap
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {F : ℂ → Ω → ℂ} {R C : ℝ} (hR : 0 ≤ R)
    (hF : ContinuousOn (Function.uncurry F) (sphere (0 : ℂ) R ×ˢ (Set.univ : Set Ω)))
    (hC : ∀ z ∈ sphere (0 : ℂ) R, ∀ ω, ‖F z ω‖ ≤ C) :
    (∮ z in C(0, R), ∫ ω, F z ω ∂μ) = ∫ ω, (∮ z in C(0, R), F z ω) ∂μ := by
  haveI hfin : IsFiniteMeasure (volume.restrict (Set.uIoc 0 (2 * π))) := by
    rw [Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
    infer_instance
  have hderiv : Continuous fun θ : ℝ => deriv (circleMap 0 R) θ := by
    have h : Continuous fun θ : ℝ => circleMap 0 R θ * I :=
      (continuous_circleMap 0 R).mul continuous_const
    simpa [deriv_circleMap, Pi.mul_def] using h
  have hT : Continuous fun p : ℝ × Ω => (circleMap 0 R p.1, p.2) :=
    ((continuous_circleMap 0 R).comp continuous_fst).prodMk continuous_snd
  have hTF : Continuous fun p : ℝ × Ω =>
      Function.uncurry F (circleMap 0 R p.1, p.2) :=
    hF.comp_continuous hT (fun p => ⟨circleMap_mem_sphere 0 hR p.1, Set.mem_univ p.2⟩)
  have hG : Continuous fun p : ℝ × Ω =>
      deriv (circleMap 0 R) p.1 • Function.uncurry F (circleMap 0 R p.1, p.2) :=
    (hderiv.comp continuous_fst).smul hTF
  have hint : Integrable (fun p : ℝ × Ω =>
      deriv (circleMap 0 R) p.1 • F (circleMap 0 R p.1) p.2)
      ((volume.restrict (Set.uIoc 0 (2 * π))).prod μ) := by
    refine Integrable.of_bound hG.aestronglyMeasurable (|R| * C) (ae_of_all _ ?_)
    intro p
    rw [norm_smul, deriv_circleMap, norm_mul, norm_I, mul_one, norm_circleMap_zero]
    exact mul_le_mul_of_nonneg_left (hC _ (circleMap_mem_sphere 0 hR p.1) p.2) (abs_nonneg R)
  conv_lhs => rw [circleIntegral]
  rw [intervalIntegral.integral_congr (fun θ _ =>
    (integral_smul (deriv (circleMap 0 R) θ) (fun ω => F (circleMap 0 R θ) ω)).symm)]
  rw [intervalIntegral_integral_swap hint]
  simp only [circleIntegral]


/-! ### Continuity of the resolvent in both variables, and of its average -/

/-- Joint continuity of `(z, a) ↦ (z − a)⁻¹` at points of the resolvent set. -/
theorem continuousAt_resolvent_prod {z : ℂ} {a : A} (hz : z ∈ resolventSet ℂ a) :
    ContinuousAt (fun p : ℂ × A => resolvent p.2 p.1) (z, a) := by
  have hinv : ContinuousAt Ring.inverse (algebraMap ℂ A z - a) :=
    (differentiableAt_inverse (𝕜 := ℂ) hz).continuousAt
  have harg : ContinuousAt (fun p : ℂ × A => algebraMap ℂ A p.1 - p.2) (z, a) := by
    fun_prop
  have hcomp : ContinuousAt (fun p : ℂ × A => Ring.inverse (algebraMap ℂ A p.1 - p.2)) (z, a) :=
    ContinuousAt.comp (f := fun p : ℂ × A => algebraMap ℂ A p.1 - p.2) (g := Ring.inverse) hinv harg
  simpa [resolvent] using hcomp

/-- For a continuous family `H` and a parameter `z` that is not in the spectrum of any `H ω`,
the map `ω ↦ (z − H ω)⁻¹` is continuous. -/
theorem continuous_resolvent_comp {Ω : Type*} [TopologicalSpace Ω]
    {H : Ω → A} (hHc : Continuous H) {z : ℂ} (hz : ∀ ω, z ∈ resolventSet ℂ (H ω)) :
    Continuous fun ω => resolvent (H ω) z := by
  refine continuous_iff_continuousAt.mpr (fun ω => ?_)
  exact (continuousAt_resolvent_prod (hz ω)).comp
    (f := fun ω => (z, H ω)) (continuous_const.prodMk hHc).continuousAt

section Mean

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [SecondCountableTopology Ω] {μ : Measure Ω}

/-- **Continuity of the averaged resolvent** on a neighbourhood of a circle above the uniform
spectral bound, by dominated convergence. -/
theorem continuousOn_integral_resolvent [IsFiniteMeasure μ]
    (H : Ω → A) (hHc : Continuous H) {r : ℝ} (hH0 : 0 ≤ r) (hH : ∀ ω, ‖H ω‖ ≤ r)
    {R : ℝ} (hr : r < R) :
    ContinuousOn (fun z : ℂ => ∫ ω, resolvent (H ω) z ∂μ)
      {z : ℂ | (r + R) / 2 < ‖z‖} := by
  have hRpos : 0 < R := lt_of_le_of_lt hH0 hr
  have hr'r : r < (r + R) / 2 := by linarith
  have hr'R : (r + R) / 2 < R := by linarith
  have hpos : 0 < (r + R) / 2 - r := by linarith
  have hbound : Integrable (fun _ : Ω => ((r + R) / 2 - r)⁻¹) μ := integrable_const _
  refine continuousOn_of_dominated (s := {z : ℂ | (r + R) / 2 < ‖z‖}) ?_ ?_ hbound ?_
  · intro z hz
    exact (continuous_resolvent_comp hHc (fun ω => by
      exact spectrum.mem_resolventSet_of_norm_lt (by
        have hz' : (r + R) / 2 < ‖z‖ := hz
        exact lt_of_le_of_lt (hH ω) (lt_trans hr'r hz')))).aestronglyMeasurable
  · intro z hz
    filter_upwards with ω
    have hz' : (r + R) / 2 < ‖z‖ := hz
    have h1 : 0 < ‖z‖ := by linarith [hH0, hr]
    have h2 : ‖H ω‖ < ‖z‖ := lt_of_le_of_lt (hH ω) (lt_trans hr'r hz')
    refine (norm_resolvent_le (H ω) h1 h2).trans ?_
    have hb : 0 < (r + R) / 2 - r := by linarith
    have ha : 0 < ‖z‖ - ‖H ω‖ := by linarith [hH ω]
    exact (inv_le_inv₀ ha hb).mpr (by linarith [hH ω])
  · filter_upwards with ω
    have hcont : ContinuousOn (fun z : ℂ => resolvent (H ω) z) (resolventSet ℂ (H ω)) :=
      HasDerivAt.continuousOn (s := resolventSet ℂ (H ω))
        (fun z hz => spectrum.hasDerivAt_resolvent_const_left hz)
    exact hcont.mono (fun z hz =>
      spectrum.mem_resolventSet_of_norm_lt (by
        have hz' : (r + R) / 2 < ‖z‖ := hz
        exact lt_of_le_of_lt (hH ω) (lt_trans hr'r hz')))

/-- **Mean-level polynomial Lemma M reduction.**  Let `H ω` be a bounded continuous family of
Banach-algebra elements (the finite-`N` pencil at each sample), `φ` the finite-side trace
functional and `ψ` the limit-side functional.  If on a circle of radius `R` the *averaged*
resolvents are within `C` of each other, then the difference of the mean of `φ(P(H ω))` and
`ψ(P(a))` is at most `R · sup|P| · C`.

This is the exact form in which the sharp `O(N⁻²)` averaged-resolvent comparison
(`gueResolventMean` versus `operatorMatrixPencilCauchy`) feeds Lemma M. -/
theorem mean_aeval_sub_le_of_apply [IsFiniteMeasure μ]
    {B : Type*} [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B] [NormOneClass B]
    (H : Ω → A) (hHc : Continuous H) {r : ℝ} (hH0 : 0 ≤ r) (hH : ∀ ω, ‖H ω‖ ≤ r)
    (φ : A →L[ℂ] ℂ) (ψ : B →L[ℂ] ℂ) (a : B) (P : ℂ[X]) {R M C : ℝ}
    (hr : r < R) (ha : ‖a‖ < R)
    (hM : ∀ z ∈ sphere (0 : ℂ) R, ‖P.eval z‖ ≤ M)
    (hC : ∀ z ∈ sphere (0 : ℂ) R,
      ‖φ (∫ ω, resolvent (H ω) z ∂μ) - ψ (resolvent a z)‖ ≤ C) :
    ‖(∫ ω, φ (Polynomial.aeval (H ω) P) ∂μ) - ψ (Polynomial.aeval a P)‖ ≤ R * M * C := by
  have hRpos : 0 < R := lt_of_le_of_lt hH0 hr
  obtain ⟨z₀, hz₀⟩ := sphere_nonempty hRpos
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM z₀ hz₀)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC z₀ hz₀)
  -- uniform resolvent bound on the circle
  have hresb : ∀ z ∈ sphere (0 : ℂ) R, ∀ ω, ‖resolvent (H ω) z‖ ≤ (R - r)⁻¹ := by
    intro z hz ω
    have hz' : ‖z‖ = R := by simpa using Metric.mem_sphere.mp hz
    have hzpos : 0 < ‖z‖ := by rw [hz']; linarith
    have hlt : ‖H ω‖ < ‖z‖ := by rw [hz']; exact lt_of_le_of_lt (hH ω) hr
    have h := norm_resolvent_le (H ω) hzpos hlt
    rw [hz'] at h
    refine h.trans ((inv_le_inv₀ ?_ ?_).mpr ?_)
    · linarith
    · linarith
    · linarith [hH ω]
  -- joint continuity of the scalar integrand
  have hFcont : ContinuousOn
      (Function.uncurry (fun z : ℂ => fun ω : Ω => P.eval z * φ (resolvent (H ω) z)))
      (sphere (0 : ℂ) R ×ˢ (Set.univ : Set Ω)) := by
    intro p hp
    have hz' : ‖p.1‖ = R := by simpa using Metric.mem_sphere.mp hp.1
    have hzmem : p.1 ∈ resolventSet ℂ (H p.2) :=
      spectrum.mem_resolventSet_of_norm_lt (by rw [hz']; exact lt_of_le_of_lt (hH p.2) hr)
    have hres : ContinuousAt (fun p : ℂ × Ω => resolvent (H p.2) p.1) p :=
      (continuousAt_resolvent_prod hzmem).comp
        (f := fun p : ℂ × Ω => (p.1, H p.2))
        (g := fun p : ℂ × A => resolvent p.2 p.1)
        (continuous_fst.continuousAt.prodMk
          (hHc.continuousAt.comp continuous_snd.continuousAt))
    have hpeval : ContinuousAt (fun p : ℂ × Ω => P.eval p.1) p :=
      (Polynomial.continuous P).continuousAt.comp continuous_fst.continuousAt
    have hmain : ContinuousAt
        (fun p : ℂ × Ω => P.eval p.1 * φ (resolvent (H p.2) p.1)) p :=
      hpeval.mul (φ.continuous.continuousAt.comp hres)
    show ContinuousWithinAt (fun p : ℂ × Ω => P.eval p.1 * φ (resolvent (H p.2) p.1))
      (sphere (0 : ℂ) R ×ˢ (Set.univ : Set Ω)) p
    exact hmain.continuousWithinAt
  -- uniform bound for Fubini
  have hFbound : ∀ z ∈ sphere (0 : ℂ) R, ∀ ω,
      ‖P.eval z * φ (resolvent (H ω) z)‖ ≤ M * (‖φ‖ * (R - r)⁻¹) := by
    intro z hz ω
    rw [norm_mul]
    refine mul_le_mul (hM z hz) ?_ (norm_nonneg _) hM0
    calc ‖φ (resolvent (H ω) z)‖ ≤ ‖φ‖ * ‖resolvent (H ω) z‖ := φ.le_opNorm _
      _ ≤ ‖φ‖ * (R - r)⁻¹ := by gcongr; exact hresb z hz ω
  -- integrability of the averaged resolvent at a point of the circle
  have hintR_sphere : ∀ z ∈ sphere (0 : ℂ) R, Integrable (fun ω => resolvent (H ω) z) μ := by
    intro z hz
    have hz' : ‖z‖ = R := by simpa using Metric.mem_sphere.mp hz
    have hcont : Continuous fun ω => resolvent (H ω) z :=
      continuous_resolvent_comp hHc (fun ω =>
        spectrum.mem_resolventSet_of_norm_lt (by rw [hz']; exact lt_of_le_of_lt (hH ω) hr))
    refine Integrable.of_bound hcont.aestronglyMeasurable ((R - r)⁻¹) (ae_of_all _ (fun ω => ?_))
    exact hresb z hz ω
  -- continuity of the averaged resolvent on the circle
  have hmeancont : ContinuousOn (fun z : ℂ => ∫ ω, resolvent (H ω) z ∂μ) (sphere (0 : ℂ) R) :=
    (continuousOn_integral_resolvent H hHc hH0 hH hr).mono (fun z hz => by
      have hz' : ‖z‖ = R := by simpa using Metric.mem_sphere.mp hz
      show (r + R) / 2 < ‖z‖
      rw [hz']; linarith)
  -- the mean contour identity
  have hmean : ∫ ω, φ (Polynomial.aeval (H ω) P) ∂μ
      = (2 * π * I : ℂ)⁻¹ *
          ∮ z in C(0, R), P.eval z * φ (∫ ω, resolvent (H ω) z ∂μ) := by
    have hpt : ∀ ω, φ (Polynomial.aeval (H ω) P)
        = (2 * π * I : ℂ)⁻¹ * ∮ z in C(0, R), P.eval z * φ (resolvent (H ω) z) :=
      fun ω => apply_aeval_eq_circleIntegral φ (H ω) (lt_of_le_of_lt (hH ω) hr) P
    simp_rw [hpt]
    rw [integral_const_mul]
    congr 1
    rw [← circleIntegral_integral_swap hRpos.le hFcont hFbound]
    refine circleIntegral.integral_congr hRpos.le (fun z hz => ?_)
    rw [integral_const_mul,
      ContinuousLinearMap.integral_comp_comm φ (hintR_sphere z hz)]
  -- integrability of both circle integrands
  have hcont1 : CircleIntegrable
      (fun z : ℂ => P.eval z * φ (∫ ω, resolvent (H ω) z ∂μ)) 0 R := by
    refine ContinuousOn.circleIntegrable hRpos.le ?_
    exact (Polynomial.continuous P).continuousOn.mul
      (φ.continuous.comp_continuousOn hmeancont)
  have hcont2 : CircleIntegrable (fun z : ℂ => P.eval z * ψ (resolvent a z)) 0 R := by
    refine ContinuousOn.circleIntegrable hRpos.le ?_
    exact (Polynomial.continuous P).continuousOn.mul
      (ψ.continuous.comp_continuousOn (continuousOn_resolvent ha))
  rw [hmean, apply_aeval_eq_circleIntegral ψ a ha P]
  set I1 : ℂ := ∮ z in C(0, R), P.eval z * φ (∫ ω, resolvent (H ω) z ∂μ) with hI1
  set I2 : ℂ := ∮ z in C(0, R), P.eval z * ψ (resolvent a z) with hI2
  have hfac : (2 * π * I : ℂ)⁻¹ * I1 - (2 * π * I : ℂ)⁻¹ * I2
      = (2 * π * I : ℂ)⁻¹ * (I1 - I2) := (mul_sub _ _ _).symm
  have hI : I1 - I2 = ∮ z in C(0, R),
      (P.eval z * φ (∫ ω, resolvent (H ω) z ∂μ) - P.eval z * ψ (resolvent a z)) := by
    rw [hI1, hI2, circleIntegral.integral_sub hcont1 hcont2]
  rw [hfac, hI]
  have hbound : ∀ z ∈ sphere (0 : ℂ) R,
      ‖P.eval z * φ (∫ ω, resolvent (H ω) z ∂μ) - P.eval z * ψ (resolvent a z)‖ ≤ M * C := by
    intro z hz
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (hM z hz) (hC z hz) (norm_nonneg _) hM0
  have hmain := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    (c := 0) hRpos.le hbound
  simpa only [smul_eq_mul] using hmain.trans (le_of_eq (by ring : R * (M * C) = R * M * C))

/-- Real-coefficient form of `mean_aeval_sub_le_of_apply`, matching `polyMatrix P H` for
`P : ℝ[X]`. -/
theorem mean_aeval_sub_le_of_apply_real [IsFiniteMeasure μ]
    {B : Type*} [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B] [NormOneClass B]
    (H : Ω → A) (hHc : Continuous H) {r : ℝ} (hH0 : 0 ≤ r) (hH : ∀ ω, ‖H ω‖ ≤ r)
    (φ : A →L[ℂ] ℂ) (ψ : B →L[ℂ] ℂ) (a : B) (P : ℝ[X]) {R M C : ℝ}
    (hr : r < R) (ha : ‖a‖ < R)
    (hM : ∀ z ∈ sphere (0 : ℂ) R, ‖(P.map (algebraMap ℝ ℂ)).eval z‖ ≤ M)
    (hC : ∀ z ∈ sphere (0 : ℂ) R,
      ‖φ (∫ ω, resolvent (H ω) z ∂μ) - ψ (resolvent a z)‖ ≤ C) :
    ‖(∫ ω, φ (Polynomial.aeval (H ω) P) ∂μ) - ψ (Polynomial.aeval a P)‖ ≤ R * M * C := by
  have h := mean_aeval_sub_le_of_apply H hHc hH0 hH φ ψ a (P.map (algebraMap ℝ ℂ)) hr ha hM hC
  simpa only [Polynomial.aeval_map_algebraMap] using h

end Mean


end

end GUEStrongConvergence
