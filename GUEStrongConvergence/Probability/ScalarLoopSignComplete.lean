/-
# Threshold-free scalar strip bound on both half-planes

This file completes the two sign inputs of the scalar loop bootstrap
(`Probability/ScalarLoopCore.lean`, `loop_bootstrap`), namely

* `Im z · Im m ≤ 0` for the finite-`N` resolvent mean `m = gueResolventMean`,
* `Im z · Im g ≤ 0` for the limit Cauchy transform `g = operatorMatrixPencilCauchy`,

and then assembles the unconditional (threshold-free) scalar strip estimate
`‖m - g‖ ≤ 4 N⁻² |Im z|⁻⁵` for **every** nonreal `z`, together with the resulting
`WeightedStripBound gueScalarA₀ gueScalarA 0 η₀ 4 5`.

## (1) Gaussian averaging

`guePencilResolvent_im_diag_mul_im_nonpos` (`Probability/ScalarLoopSign.lean`) gives the
per-entry sign `Im z · Im R_{aa} ≤ 0`.  The partial trace is
`(id_d ⊗ tr_N) R = N⁻¹ ∑_k R_{(u,k),(v,k)}`, so the imaginary part of the `(u,u)` entry of
`guePartialTrace` is `N⁻¹ ∑_k Im R_{(u,k),(u,k)}` and has the opposite sign to `Im z`;
integrating over the Gaussian measure preserves the sign.  The only cast input is
`((N : ℂ)⁻¹).re = (N : ℝ)⁻¹`.

Declarations: `guePartialTrace_im_mul_im_nonpos`,
`integrable_guePartialTrace_entry_of_im_ne_zero` (integrability for `Im z ≠ 0`, avoiding any
sign condition), and `gueResolventMean_im_mul_im_nonpos`.

## (2) The limit-side sign (no IVT, no threshold)

`operatorMatrixPencilCauchy A₀ A z` is the entrywise vacuum expectation of the genuine matrix
resolvent `R = (z - H)⁻¹` of the affine Fock pencil `H = operatorMatrixPencil A₀ A`.  The exact
identity `R - R* = (z̄ - z) R R*` holds in the C*-algebra `CStarMatrix d d (WordSpace ι →L[ℂ] _)`
(it is `StarProbabilitySpace.inverse_sub_star_inverse` applied to `algebraMap ℂ _ z - H`), and its
`(u,u)` entry after applying the (positive) vacuum state gives

`Im (E R)_{uu} = -Im z · S`,  `S = ∑_j Re E[(R R*)_{uj}] ≥ 0`,

because `R R*` has a nonnegative diagonal in a positive state
(`StarProbabilitySpace.positive`).  Hence

`Im z · Im g_{uu} = -(Im z)² S ≤ 0`

for **every** `Im z ≠ 0` (both half-planes).  This avoids the `‖g‖ < 1` / IVT route entirely and
does not need the (unbuilt) dependency module `MatrixCauchyImaginary`.

Declarations: `vacuumExpectation_mul_star_re_nonneg`,
`vacuumExpectation_mul_star_im_eq_zero`, `operatorMatrixPencilCauchy_im_mul_im_nonpos`.

## (3) Conjugation symmetry and the variance bound on both half-planes

The sharp scalar variance bound `integral_norm_sq_fluctuation_scalar_le`
(`Probability/SharpTwoPoint.lean`) is stated for `0 < Im z`, but its integrand is a squared
modulus of `T_N - E T_N`, and both factors are `star`-equivariant in the spectral parameter:
`guePartialTrace_star` (`Probability/ResolventConj.lean`) and `gueResolventMean_star`.  Hence the
integrand at `z̄` is the conjugate of the integrand at `z`, so the integral is unchanged and the
bound transfers to `Im z < 0`:

`integral_norm_sq_fluctuation_scalar_le_abs :`
`∫ ‖T_N(z) - E T_N(z)‖² ≤ 4 N⁻² |Im z|⁻⁴` for **every** `Im z ≠ 0`.

## (4) Assembly

At `d = Unit`, `A₀ = 0`, `A = 1`, with `T_N(z) = N⁻¹ tr (z - G)⁻¹`, `m = E[T_N]`, `g` the limit
Dyson solution (`norm_gueResolventMean_sub_limit_le_of_var` is the whole chain with the variance
input abstract, for any `Im z ≠ 0`):

* `single_gue_schwinger_dyson` gives `z m - 1 = E[T_N²]`;
* the elementary expansion `E[T_N²] - m² = E[(T_N - m)²]` turns this into the exact loop
  identity `(m - g)(z - m - g) = Var` with `Var = E[(T_N - m)²]` (`loop_identity_of_dyson`);
* the two sign facts give `|Im(z - m - g)| ≥ |Im z|`, hence `‖m - g‖ ≤ ‖Var‖ / |Im z|`
  (`loop_bootstrap`);
* the sharp variance bound gives `‖Var‖ ≤ 4 N⁻² |Im z|⁻⁴`.

Results (all `N > 0`):

* `norm_gueResolventMean_sub_limit_le_five_full` and its `frob` form
  `frob_gueResolventMean_sub_limit_le_five_full`: for every `z` with `z.im ≠ 0`,
  `‖g_N(z) - g(z)‖ ≤ 4 N⁻² |Im z|⁻⁵` (Frobenius norm in the `frob` form);
* `norm_gueResolventMean_sub_limit_le_five` / `frob_gueResolventMean_sub_limit_le_five`:
  the upper half-plane statements `≤ 4 N⁻² (Im z)⁻⁵`, kept for compatibility;
* `weightedStripBound_gueScalar (η₀) : WeightedStripBound gueScalarA₀ gueScalarA 0 η₀ 4 5`,
  i.e. the full weighted strip hypothesis with `C_s = 4`, `β = 5`, valid for every strip width
  `η₀` and with no half-plane restriction.

Note that the limit-side conjugation identity
`star (operatorMatrixPencilCauchy A₀ A z) = operatorMatrixPencilCauchy A₀ A (z̄)` is **not**
needed for any of these results: the lower half-plane is handled at the level of the variance
integrand, and then the whole loop assembly is re-run at `z` itself, where both the finite-`N`
and the limit Dyson equations (and both sign facts) are already available for `Im z ≠ 0`.
-/
import GUEStrongConvergence.Probability.ScalarLoopCore
import GUEStrongConvergence.Probability.SharpTwoPoint
import GUEStrongConvergence.Probability.DysonMasterIdentity
import GUEStrongConvergence.Probability.ResolventConj
import FreeProbability.Analytic.CauchyHalfPlane
import FreeProbability.OperatorValued.MatrixExpectation
import FreeProbability.Fock.VacuumState

open MeasureTheory ProbabilityTheory Matrix Filter
open FreeProbability FreeProbability.Fock
open scoped Matrix.Norms.Frobenius ComplexOrder ENNReal NNReal Topology

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace GUEStrongConvergence

variable {ι d : Type*} {N : ℕ} [Fintype ι] [Fintype d] [DecidableEq d] [DecidableEq ι]

noncomputable section

/-! ### (0) The per-entry sign, ported

`Probability/ScalarLoopSign.lean` proves the per-entry sign
`guePencilResolvent_im_diag_mul_im_nonpos`.  That module also declares two file-local
`PartialOrder`/`StarOrderedRing` instances on `WordSpace ι →L[ℂ] WordSpace ι` whose generated
auxiliary declaration names collide with the identical ones in `Probability/DysonLimitSharp.lean`
(the two modules cannot be imported into the same environment).  Since the root module does
import `DysonLimitSharp`, we restate the per-entry lemma here, verbatim, under a primed name.
This is the only duplicated proof in this file. -/

/-- **Diagonal resolvent imaginary-part identity for the Hermitian GUE pencil** (ported from
`Probability/ScalarLoopSign.lean`).  For every entry `a`,
`Im z · Im (guePencilResolvent … a a) ≤ 0`. -/
theorem guePencilResolvent_im_diag_mul_im_nonpos'
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (x : GUECoord ι N → ℝ) (z : ℂ) (hz : z.im ≠ 0) (a : d × Fin N) :
    z.im * (guePencilResolvent A₀ A x z a a).im ≤ 0 := by
  classical
  set R : CStarMatrix (d × Fin N) (d × Fin N) ℂ := guePencilResolvent A₀ A x z with hR
  set X : CStarMatrix (d × Fin N) (d × Fin N) ℂ :=
    algebraMap ℂ (CStarMatrix (d × Fin N) (d × Fin N) ℂ) z - guePencil A₀ A x with hX
  have hXR : X * R = 1 := resolvent_mul_guePencil A₀ A hA₀ hA x z hz
  have hdiff : star X - X = (star z - z) • (1 : CStarMatrix (d × Fin N) (d × Fin N) ℂ) := by
    rw [hX]
    simp only [Algebra.algebraMap_eq_smul_one, star_sub, star_smul, star_one,
      (guePencil_isSelfAdjoint A₀ A hA₀ hA x).star_eq, sub_smul]
    abel
  have key : R - star R = star R * (star X - X) * R := by
    have h1 : star R * star X = 1 := by
      have h := congrArg star hXR
      simpa using h
    have h2 : star R * star X * R = R := by rw [h1, one_mul]
    have h3 : star R * X * R = star R := by rw [mul_assoc, hXR, mul_one]
    calc R - star R = star R * star X * R - star R * X * R := by rw [h2, h3]
      _ = star R * (star X - X) * R := by noncomm_ring
  have key2 : R - star R = (star z - z) • (star R * R) := by
    rw [key, hdiff, mul_smul_comm, mul_one, smul_mul_assoc]
  have hentry : R a a - star (R a a) = (star z - z) * ((star R * R) a a) := by
    have h := congrArg (fun M : CStarMatrix (d × Fin N) (d × Fin N) ℂ => M a a) key2
    simpa [CStarMatrix.sub_apply, CStarMatrix.smul_apply, CStarMatrix.star_apply,
      smul_eq_mul] using h
  have hgram : (star R * R) a a = ((∑ j : d × Fin N, ‖R j a‖ ^ 2 : ℝ) : ℂ) := by
    rw [CStarMatrix.mul_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [CStarMatrix.star_apply, Complex.star_def, mul_comm, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
  set S : ℝ := ∑ j : d × Fin N, ‖R j a‖ ^ 2 with hSdef
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hzstar : (star z - z).im = -2 * z.im := by
    simp only [Complex.star_def, Complex.sub_im, Complex.conj_im]
    ring
  have him : 2 * (R a a).im = -2 * z.im * S := by
    have h := congrArg Complex.im hentry
    rw [hgram] at h
    simp only [Complex.sub_im, Complex.star_def, Complex.conj_im, Complex.mul_im,
      Complex.ofReal_im, Complex.ofReal_re, mul_zero] at h
    linarith
  have ha : (R a a).im = -z.im * S := by linarith
  rw [ha, show z.im * (-z.im * S) = -(z.im ^ 2 * S) by ring]
  exact neg_nonpos.mpr (mul_nonneg (sq_nonneg _) hS)

/-! ### (1) The Gaussian averaging step -/

/-- **Sign of the imaginary part of a partial-trace entry.**  `N⁻¹ ∑_k Im R_{(u,k),(u,k)}` has
the sign opposite to `Im z`, because every diagonal resolvent entry does. -/
theorem guePartialTrace_im_mul_im_nonpos
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (x : GUECoord ι N → ℝ) (z : ℂ) (hz : z.im ≠ 0) (u : d) :
    z.im * (guePartialTrace A₀ A z x u u).im ≤ 0 := by
  classical
  have hNre : ((N : ℂ)⁻¹).re = (N : ℝ)⁻¹ := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re]
  have hNim : ((N : ℂ)⁻¹).im = 0 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_im]
  have hNnn : (0 : ℝ) ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg N)
  -- the imaginary part of the sum of the diagonal resolvent entries
  have hsum : (∑ k : Fin N, guePencilResolvent A₀ A x z (u, k) (u, k)).im
      = ∑ k : Fin N, (guePencilResolvent A₀ A x z (u, k) (u, k)).im := by
    simpa using map_sum Complex.imCLM.toAddMonoidHom
      (fun k : Fin N => guePencilResolvent A₀ A x z (u, k) (u, k)) Finset.univ
  have hsign : ∑ k : Fin N, z.im * (guePencilResolvent A₀ A x z (u, k) (u, k)).im ≤ 0 :=
    Finset.sum_nonpos fun k _ =>
      guePencilResolvent_im_diag_mul_im_nonpos' A₀ A hA₀ hA x z hz (u, k)
  rw [guePartialTrace_apply, Complex.mul_im, hNre, hNim, hsum, zero_mul, add_zero]
  have hre : z.im * ((N : ℝ)⁻¹ * ∑ k : Fin N,
      (guePencilResolvent A₀ A x z (u, k) (u, k)).im)
      = (N : ℝ)⁻¹ * ∑ k : Fin N, z.im *
        (guePencilResolvent A₀ A x z (u, k) (u, k)).im := by
    rw [← Finset.mul_sum]
    ring
  rw [hre]
  exact mul_nonpos_of_nonneg_of_nonpos hNnn hsign

/-- Integrability of a partial-trace entry, without any sign condition on `Im z`. -/
lemma integrable_guePartialTrace_entry_of_im_ne_zero
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (u v : d) :
    Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · rw [hN]
    simp [guePartialTrace, partialTraceN]
  · refine Integrable.of_bound
      ((continuous_guePartialTrace_entry A₀ A hA₀ hA z hz u v).aestronglyMeasurable)
      |z.im|⁻¹ ?_
    filter_upwards with x
    exact norm_guePartialTrace_entry_le A₀ A hA₀ hA _ z hz hN u v

/-- **Gaussian averaging: the finite-`N` resolvent mean has the correct imaginary sign.**
For `Im z ≠ 0` and every `u`, `Im z · Im (g_N(z))_{uu} ≤ 0`. -/
theorem gueResolventMean_im_mul_im_nonpos
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (u : d) :
    z.im * (gueResolventMean (N := N) A₀ A z u u).im ≤ 0 := by
  classical
  have hint : Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u u)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
    integrable_guePartialTrace_entry_of_im_ne_zero (N := N) A₀ A hA₀ hA z hz u u
  have h1 : (∫ x, guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u u
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))).im
      = ∫ x, (guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u u).im
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    have h := ContinuousLinearMap.integral_comp_comm (L := Complex.imCLM)
      (φ := fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u u) hint
    simpa [Complex.imCLM_apply] using h.symm
  rw [gueResolventMean_apply, h1, ← integral_const_mul]
  exact integral_nonpos fun x =>
    guePartialTrace_im_mul_im_nonpos A₀ A hA₀ hA x z hz u


/-! ### (2) The limit-side sign fact -/

/-- The vacuum expectation of `a * star a` is a nonnegative real number. -/
lemma vacuumExpectation_mul_star_re_nonneg {I : Type*}
    (a : WordSpace I →L[ℂ] WordSpace I) :
    0 ≤ ((vacuumState I).expectation (a * star a)).re := by
  have h := (vacuumState I).positive (star a)
  simpa using h.1

/-- The vacuum expectation of `a * star a` is real. -/
lemma vacuumExpectation_mul_star_im_eq_zero {I : Type*}
    (a : WordSpace I →L[ℂ] WordSpace I) :
    ((vacuumState I).expectation (a * star a)).im = 0 := by
  have h := (vacuumState I).map_star (a * star a)
  have hss : star (a * star a) = a * star a := by rw [star_mul, star_star]
  rw [hss] at h
  have := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at this
  linarith

/-- **Limit-side sign fact.**  The diagonal entries of the operator-valued matrix Cauchy
transform of a Hermitian affine Fock pencil have imaginary part of the sign opposite to
`Im z`, for every nonreal `z` (both half-planes).

This is the exact identity `R - R* = (z̄ - z) R R*` in the matrix C*-algebra, pushed through the
entrywise vacuum expectation, whose positivity makes the diagonal of `E[R R*]` a nonnegative
real number. -/
theorem operatorMatrixPencilCauchy_im_mul_im_nonpos
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (u : d) :
    z.im * (operatorMatrixPencilCauchy A₀ A z u u).im ≤ 0 := by
  classical
  have hH : IsSelfAdjoint (operatorMatrixPencil A₀ A) :=
    operatorMatrixPencil_isSelfAdjoint A₀ A hA₀ hA
  letI : PartialOrder (WordSpace ι →L[ℂ] WordSpace ι) :=
    CStarAlgebra.spectralOrder _
  letI : StarOrderedRing (WordSpace ι →L[ℂ] WordSpace ι) :=
    CStarAlgebra.spectralOrderedRing _
  have hres : z ∈ resolventSet ℂ (operatorMatrixPencil A₀ A) :=
    StarProbabilitySpace.selfAdjoint_mem_resolventSet_of_im_ne_zero
      (operatorMatrixPencil A₀ A) hH z hz
  have hx : IsUnit (algebraMap ℂ (CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι)) z
      - operatorMatrixPencil A₀ A) := hres
  -- the exact star identity in the matrix C*-algebra
  have hs : star (algebraMap ℂ (CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι)) z
        - operatorMatrixPencil A₀ A)
      - (algebraMap ℂ (CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι)) z
        - operatorMatrixPencil A₀ A)
      = (star z - z) • (1 : CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι)) := by
    rw [Algebra.algebraMap_eq_smul_one]
    rw [star_sub (z • (1 : CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι)))
      (operatorMatrixPencil A₀ A)]
    rw [star_smul z (1 : CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι)), star_one,
      hH.star_eq, sub_smul (star z) z (1 : CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι))]
    abel
  have hr : resolvent (operatorMatrixPencil A₀ A) z
        - star (resolvent (operatorMatrixPencil A₀ A) z)
      = (star z - z) • (resolvent (operatorMatrixPencil A₀ A) z
        * star (resolvent (operatorMatrixPencil A₀ A) z)) := by
    have h := StarProbabilitySpace.inverse_sub_star_inverse
      (algebraMap ℂ (CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι)) z
        - operatorMatrixPencil A₀ A) hx
    rw [hs] at h
    simpa only [resolvent, mul_smul_comm, mul_one, smul_mul_assoc] using h
  -- push through the entrywise vacuum expectation
  have he : matrixExpectation (vacuumState ι).toProbabilitySpace
        (resolvent (operatorMatrixPencil A₀ A) z)
      - matrixExpectation (vacuumState ι).toProbabilitySpace
        (star (resolvent (operatorMatrixPencil A₀ A) z))
      = (star z - z) • matrixExpectation (vacuumState ι).toProbabilitySpace
        (resolvent (operatorMatrixPencil A₀ A) z
          * star (resolvent (operatorMatrixPencil A₀ A) z)) := by
    calc matrixExpectation (vacuumState ι).toProbabilitySpace
          (resolvent (operatorMatrixPencil A₀ A) z)
        - matrixExpectation (vacuumState ι).toProbabilitySpace
          (star (resolvent (operatorMatrixPencil A₀ A) z))
        = matrixExpectation (vacuumState ι).toProbabilitySpace
          (resolvent (operatorMatrixPencil A₀ A) z
            - star (resolvent (operatorMatrixPencil A₀ A) z)) :=
          (LinearMap.map_sub (matrixExpectation (vacuumState ι).toProbabilitySpace) _ _).symm
      _ = matrixExpectation (vacuumState ι).toProbabilitySpace
          ((star z - z) • (resolvent (operatorMatrixPencil A₀ A) z
            * star (resolvent (operatorMatrixPencil A₀ A) z))) := by rw [hr]
      _ = (star z - z) • matrixExpectation (vacuumState ι).toProbabilitySpace
          (resolvent (operatorMatrixPencil A₀ A) z
            * star (resolvent (operatorMatrixPencil A₀ A) z)) :=
          LinearMap.map_smul (matrixExpectation (vacuumState ι).toProbabilitySpace) _ _
  have hd : matrixExpectation (vacuumState ι).toProbabilitySpace
        (resolvent (operatorMatrixPencil A₀ A) z) u u
      - matrixExpectation (vacuumState ι).toProbabilitySpace
        (star (resolvent (operatorMatrixPencil A₀ A) z)) u u
      = (star z - z) * (matrixExpectation (vacuumState ι).toProbabilitySpace
        (resolvent (operatorMatrixPencil A₀ A) z
          * star (resolvent (operatorMatrixPencil A₀ A) z)) u u) := by
    have h := congrArg (fun M : Matrix d d ℂ => M u u) he
    simpa only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] using h
  -- the star of the mean, entrywise
  have hstar : matrixExpectation (vacuumState ι).toProbabilitySpace
        (star (resolvent (operatorMatrixPencil A₀ A) z)) u u
      = star (matrixExpectation (vacuumState ι).toProbabilitySpace
        (resolvent (operatorMatrixPencil A₀ A) z) u u) := by
    rw [matrixExpectation_apply, matrixExpectation_apply]
    have hentry : (star (resolvent (operatorMatrixPencil A₀ A) z)
        : Matrix d d (WordSpace ι →L[ℂ] WordSpace ι)) u u
        = star ((resolvent (operatorMatrixPencil A₀ A) z) u u) := rfl
    rw [hentry]
    exact (vacuumState ι).map_star _
  -- the diagonal of `E[R R*]` as a nonnegative real number
  set R : CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι) :=
    resolvent (operatorMatrixPencil A₀ A) z with hR
  set S : ℝ := ∑ j : d,
    ((vacuumState ι).expectation (R u j * star (R u j))).re with hS
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun j _ =>
    vacuumExpectation_mul_star_re_nonneg (R u j)
  have hdiag : matrixExpectation (vacuumState ι).toProbabilitySpace
        (resolvent (operatorMatrixPencil A₀ A) z
          * star (resolvent (operatorMatrixPencil A₀ A) z)) u u = (S : ℂ) := by
    rw [hR] at hS
    change ((vacuumState ι).expectation
      ((resolvent (operatorMatrixPencil A₀ A) z
        * star (resolvent (operatorMatrixPencil A₀ A) z)) u u)) = (S : ℂ)
    have hmul : (resolvent (operatorMatrixPencil A₀ A) z
        * star (resolvent (operatorMatrixPencil A₀ A) z)) u u
        = ∑ j : d, (resolvent (operatorMatrixPencil A₀ A) z) u j
          * star ((resolvent (operatorMatrixPencil A₀ A) z) u j) := by
      rw [CStarMatrix.mul_apply]
      exact Finset.sum_congr rfl fun j _ => by rw [CStarMatrix.star_apply]
    rw [hmul, map_sum, hS, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    apply Complex.ext
    · simp
    · simpa using vacuumExpectation_mul_star_im_eq_zero
        ((resolvent (operatorMatrixPencil A₀ A) z) u j)
  -- imaginary parts
  have him : 2 * (matrixExpectation (vacuumState ι).toProbabilitySpace
        (resolvent (operatorMatrixPencil A₀ A) z) u u).im = -2 * z.im * S := by
    have h := congrArg Complex.im hd
    rw [hstar, hdiag] at h
    have hL : (matrixExpectation (vacuumState ι).toProbabilitySpace
          (resolvent (operatorMatrixPencil A₀ A) z) u u
        - star (matrixExpectation (vacuumState ι).toProbabilitySpace
          (resolvent (operatorMatrixPencil A₀ A) z) u u)).im
        = 2 * (matrixExpectation (vacuumState ι).toProbabilitySpace
          (resolvent (operatorMatrixPencil A₀ A) z) u u).im := by
      simp only [Complex.sub_im, Complex.star_def, Complex.conj_im]
      ring
    have hR' : ((star z - z) * (S : ℂ)).im = -2 * z.im * S := by
      rw [Complex.mul_im]
      simp only [Complex.ofReal_im, Complex.ofReal_re, Complex.sub_re, Complex.sub_im,
        Complex.star_def, Complex.conj_re, Complex.conj_im, sub_self, zero_mul, mul_zero,
        add_zero]
      ring
    rw [hL, hR'] at h
    exact h
  have hfin : z.im * (matrixExpectation (vacuumState ι).toProbabilitySpace
        (resolvent (operatorMatrixPencil A₀ A) z) u u).im ≤ 0 := by
    have h1 : (matrixExpectation (vacuumState ι).toProbabilitySpace
        (resolvent (operatorMatrixPencil A₀ A) z) u u).im = -z.im * S := by
      linarith
    rw [h1]
    nlinarith [mul_nonneg (sq_nonneg z.im) hSnn]
  have hcauchy : operatorMatrixPencilCauchy A₀ A z
      = matrixExpectation (vacuumState ι).toProbabilitySpace
        (resolvent (operatorMatrixPencil A₀ A) z) := rfl
  rw [hcauchy]
  exact hfin


/-! ### (3) Conjugation symmetry and the variance bound on both half-planes -/

/-- Diagonal entry form of `guePartialTrace_star`: the partial trace at `z̄` is the conjugate of
the partial trace at `z`. -/
lemma guePartialTrace_scalar_star (z : ℂ) (x : GUECoord Unit N → ℝ) :
    guePartialTrace gueScalarA₀ gueScalarA (star z) x () () =
      star (guePartialTrace gueScalarA₀ gueScalarA z x () ()) :=
  guePartialTrace_star gueScalarA₀ gueScalarA isHermitian_zero (fun _ => isHermitian_one)
    x z () ()

/-- Diagonal entry form of `gueResolventMean_star`: the averaged partial trace at `z̄` is the
conjugate of the averaged partial trace at `z`. -/
lemma gueResolventMean_scalar_star (z : ℂ) :
    gueResolventMean (N := N) gueScalarA₀ gueScalarA (star z) () () =
      star (gueResolventMean (N := N) gueScalarA₀ gueScalarA z () ()) := by
  have h := gueResolventMean_star (N := N) gueScalarA₀ gueScalarA isHermitian_zero
    (fun _ => isHermitian_one) z
  calc gueResolventMean (N := N) gueScalarA₀ gueScalarA (star z) () ()
      = (star (gueResolventMean (N := N) gueScalarA₀ gueScalarA z)) () () := by rw [← h]
    _ = star (gueResolventMean (N := N) gueScalarA₀ gueScalarA z () ()) :=
        Matrix.star_apply _ () ()

/-- **The sharp scalar variance bound for every nonreal `z`.**  The `0 < Im z` statement
`integral_norm_sq_fluctuation_scalar_le` transfers to the lower half-plane because the integrand
is a squared modulus and both factors are `star`-equivariant in `z` (`guePartialTrace_scalar_star`,
`gueResolventMean_scalar_star`). -/
theorem integral_norm_sq_fluctuation_scalar_le_abs (z : ℂ) (hz : z.im ≠ 0) (hN : 0 < N) :
    ∫ x, ‖guePartialTrace gueScalarA₀ gueScalarA z x () () -
        gueResolventMean (N := N) gueScalarA₀ gueScalarA z () ()‖ ^ 2
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord Unit N)))
      ≤ 4 * (N : ℝ)⁻¹ ^ 2 * |z.im|⁻¹ ^ 4 := by
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · -- lower half-plane: apply the upper half-plane bound at `star z`
    have hzpos : 0 < (star z).im := by simpa [Complex.star_def] using hneg
    have h := integral_norm_sq_fluctuation_scalar_le (N := N) (star z) hzpos hN
    have hinteq : (∫ x, ‖guePartialTrace gueScalarA₀ gueScalarA z x () () -
          gueResolventMean (N := N) gueScalarA₀ gueScalarA z () ()‖ ^ 2
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord Unit N))))
        = ∫ x, ‖guePartialTrace gueScalarA₀ gueScalarA (star z) x () () -
            gueResolventMean (N := N) gueScalarA₀ gueScalarA (star z) () ()‖ ^ 2
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord Unit N))) := by
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      show ‖guePartialTrace gueScalarA₀ gueScalarA z (x : GUECoord Unit N → ℝ) () () -
          gueResolventMean (N := N) gueScalarA₀ gueScalarA z () ()‖ ^ 2
        = ‖guePartialTrace gueScalarA₀ gueScalarA (star z) (x : GUECoord Unit N → ℝ) () () -
          gueResolventMean (N := N) gueScalarA₀ gueScalarA (star z) () ()‖ ^ 2
      rw [guePartialTrace_scalar_star, gueResolventMean_scalar_star, ← star_sub, norm_star]
    rw [hinteq]
    refine h.trans (le_of_eq ?_)
    have hpow : ((star z).im)⁻¹ ^ 4 = |z.im|⁻¹ ^ 4 := by
      rw [Complex.star_def, Complex.conj_im, abs_of_neg hneg]
    rw [hpow]
  · -- upper half-plane: the existing bound
    have h := integral_norm_sq_fluctuation_scalar_le (N := N) z hpos hN
    simpa [abs_of_pos hpos] using h

/-! ### (4) The threshold-free scalar strip estimate on both half-planes -/

/-- **Loop bootstrap at fixed `z` with the variance bound as a hypothesis.**  This is the whole
assembly chain (Schwinger--Dyson, variance expansion, exact loop identity, `loop_bootstrap`) with
the variance input left abstract; it works for every `Im z ≠ 0`. -/
theorem norm_gueResolventMean_sub_limit_le_of_var (z : ℂ) (hz : z.im ≠ 0) (hN : 0 < N) {C : ℝ}
    (hVar : ∫ x, ‖guePartialTrace gueScalarA₀ gueScalarA z (x : GUECoord Unit N → ℝ) () () -
        gueResolventMean (N := N) gueScalarA₀ gueScalarA z () ()‖ ^ 2
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord Unit N))) ≤ C) :
    ‖gueResolventMean (N := N) gueScalarA₀ gueScalarA z () () -
      operatorMatrixPencilCauchy gueScalarA₀ gueScalarA z () ()‖ ≤ C / |z.im| := by
  classical
  set T : EuclideanSpace ℝ (GUECoord Unit N) → ℂ := fun x =>
    guePartialTrace gueScalarA₀ gueScalarA z (x : GUECoord Unit N → ℝ) () () with hT
  set m : ℂ := gueResolventMean (N := N) gueScalarA₀ gueScalarA z () () with hm
  set g : ℂ := operatorMatrixPencilCauchy gueScalarA₀ gueScalarA z () () with hg
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  -- the mean is the integral of the partial trace
  have hmT : m = ∫ x, T x ∂(stdGaussian (EuclideanSpace ℝ (GUECoord Unit N))) := by
    rw [hm, hT]
    exact gueResolventMean_apply gueScalarA₀ gueScalarA z () ()
  -- boundedness and integrability of the partial trace
  have hTbound : ∀ x, ‖T x‖ ≤ |z.im|⁻¹ := by
    intro x
    rw [hT]
    change ‖guePartialTrace gueScalarA₀ gueScalarA z (x : GUECoord Unit N → ℝ) () ()‖
      ≤ |z.im|⁻¹
    exact norm_guePartialTrace_entry_le gueScalarA₀ gueScalarA isHermitian_zero
      (fun _ => isHermitian_one) _ z hz hN () ()
  have hTcont : Continuous T := by
    rw [hT]
    exact continuous_guePartialTrace_entry gueScalarA₀ gueScalarA isHermitian_zero
      (fun _ => isHermitian_one) z hz () ()
  have hTint : Integrable T (stdGaussian (EuclideanSpace ℝ (GUECoord Unit N))) := by
    rw [hT]
    exact integrable_guePartialTrace_entry_of_im_ne_zero gueScalarA₀ gueScalarA isHermitian_zero
      (fun _ => isHermitian_one) z hz () ()
  have hT2int : Integrable (fun x => T x * T x)
      (stdGaussian (EuclideanSpace ℝ (GUECoord Unit N))) := by
    refine Integrable.of_bound ((hTcont.mul hTcont).aestronglyMeasurable)
      (|z.im|⁻¹ * |z.im|⁻¹) ?_
    filter_upwards with x
    rw [norm_mul]
    exact mul_le_mul (hTbound x) (hTbound x) (norm_nonneg _) (by positivity)
  -- expansion of the variance
  have hvar : (∫ x, T x * T x ∂(stdGaussian (EuclideanSpace ℝ (GUECoord Unit N)))) - m ^ 2
      = ∫ x, (T x - m) ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (GUECoord Unit N))) := by
    have hexp : ∀ x, (T x - m) ^ 2 = T x * T x - m * T x - T x * m + m * m := by
      intro x; ring
    rw [show (∫ x, (T x - m) ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (GUECoord Unit N))))
        = ∫ x, (T x * T x - m * T x - T x * m + m * m)
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord Unit N))) from
        integral_congr_ae (ae_of_all _ hexp)]
    have hiA : Integrable (fun x => T x * T x)
        (stdGaussian (EuclideanSpace ℝ (GUECoord Unit N))) := hT2int
    have hiB : Integrable (fun x => m * T x)
        (stdGaussian (EuclideanSpace ℝ (GUECoord Unit N))) := hTint.const_mul m
    have hiC : Integrable (fun x => T x * m)
        (stdGaussian (EuclideanSpace ℝ (GUECoord Unit N))) := hTint.mul_const m
    have hiD : Integrable (fun _ : EuclideanSpace ℝ (GUECoord Unit N) => m * m)
        (stdGaussian (EuclideanSpace ℝ (GUECoord Unit N))) := integrable_const (m * m)
    have hiAB : Integrable (fun x => T x * T x - m * T x)
        (stdGaussian (EuclideanSpace ℝ (GUECoord Unit N))) := hiA.sub hiB
    have hiABC : Integrable (fun x => T x * T x - m * T x - T x * m)
        (stdGaussian (EuclideanSpace ℝ (GUECoord Unit N))) := hiAB.sub hiC
    rw [integral_add hiABC hiD, integral_sub hiAB hiC, integral_sub hiA hiB,
      integral_const_mul, integral_mul_const, integral_const]
    rw [← hmT]
    simp
    ring
  -- the exact finite-`N` Schwinger--Dyson equation
  have hSD : z * m - 1 = ∫ x, T x * T x
      ∂(stdGaussian (EuclideanSpace ℝ (GUECoord Unit N))) := by
    rw [hm, hT]
    exact single_gue_schwinger_dyson z hz hNc
  have hm_eq : z * m - 1 - m ^ 2
      = ∫ x, (T x - m) ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (GUECoord Unit N))) := by
    linear_combination hSD + hvar
  -- the exact limit Dyson equation
  have hg_eq : (z - g) * g = 1 := by
    have hlim := limit_dyson_equation gueScalarA₀ gueScalarA isHermitian_zero
      (fun _ => isHermitian_one) z hz
    have h := congrArg (fun M : Matrix Unit Unit ℂ => M () ()) hlim
    rw [hg]
    simpa [Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.sum_apply] using h
  -- the sign facts
  have hmsign : z.im * m.im ≤ 0 := by
    rw [hm]
    exact gueResolventMean_im_mul_im_nonpos gueScalarA₀ gueScalarA isHermitian_zero
      (fun _ => isHermitian_one) z hz ()
  have hgsign : z.im * g.im ≤ 0 := by
    rw [hg]
    exact operatorMatrixPencilCauchy_im_mul_im_nonpos gueScalarA₀ gueScalarA
      isHermitian_zero (fun _ => isHermitian_one) z hz ()
  -- the loop bootstrap
  have hid : (m - g) * (z - m - g)
      = ∫ x, (T x - m) ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (GUECoord Unit N))) :=
    loop_identity_of_dyson hg_eq hm_eq
  have hbs : ‖m - g‖ ≤ (‖∫ x, (T x - m) ^ 2
      ∂(stdGaussian (EuclideanSpace ℝ (GUECoord Unit N)))‖) / |z.im| :=
    loop_bootstrap hz hid hmsign hgsign
  -- the variance input
  have hVar_le : ‖∫ x, (T x - m) ^ 2
      ∂(stdGaussian (EuclideanSpace ℝ (GUECoord Unit N)))‖ ≤ C := by
    calc ‖∫ x, (T x - m) ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (GUECoord Unit N)))‖
        ≤ ∫ x, ‖(T x - m) ^ 2‖
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord Unit N))) :=
          norm_integral_le_integral_norm _
      _ = ∫ x, ‖T x - m‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (GUECoord Unit N))) := by
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          exact norm_pow _ 2
      _ ≤ C := by simpa [hT, hm] using hVar
  calc ‖m - g‖ ≤ (‖∫ x, (T x - m) ^ 2
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord Unit N)))‖) / |z.im| := hbs
    _ ≤ C / |z.im| := div_le_div_of_nonneg_right hVar_le (abs_nonneg _)

/-- **Unconditional scalar strip bound.**  For the scalar single GUE (`d = Unit`, `A₀ = 0`,
`A = 1`) and every `z` in the upper half-plane,

`‖g_N(z) - g(z)‖ ≤ 4 N⁻² (Im z)⁻⁵`,

with **no lower bound on `Im z`**. -/
theorem norm_gueResolventMean_sub_limit_le_five (z : ℂ) (hz : 0 < z.im) (hN : 0 < N) :
    ‖gueResolventMean (N := N) gueScalarA₀ gueScalarA z () () -
      operatorMatrixPencilCauchy gueScalarA₀ gueScalarA z () ()‖
      ≤ 4 * (N : ℝ)⁻¹ ^ 2 * (z.im)⁻¹ ^ 5 := by
  have h := norm_gueResolventMean_sub_limit_le_of_var (N := N) z hz.ne' hN
    (C := 4 * (N : ℝ)⁻¹ ^ 2 * (z.im)⁻¹ ^ 4)
    (integral_norm_sq_fluctuation_scalar_le (N := N) z hz hN)
  rw [abs_of_pos hz] at h
  refine h.trans (le_of_eq ?_)
  rw [div_eq_mul_inv]
  ring

/-- **The threshold-free scalar strip bound on both half-planes.**
`‖g_N(z) - g(z)‖ ≤ 4 N⁻² |Im z|⁻⁵` for every nonreal `z`. -/
theorem norm_gueResolventMean_sub_limit_le_five_full (z : ℂ) (hz : z.im ≠ 0) (hN : 0 < N) :
    ‖gueResolventMean (N := N) gueScalarA₀ gueScalarA z () () -
      operatorMatrixPencilCauchy gueScalarA₀ gueScalarA z () ()‖
      ≤ 4 * (N : ℝ)⁻¹ ^ 2 * |z.im|⁻¹ ^ 5 := by
  have h := norm_gueResolventMean_sub_limit_le_of_var (N := N) z hz hN
    (C := 4 * (N : ℝ)⁻¹ ^ 2 * |z.im|⁻¹ ^ 4)
    (integral_norm_sq_fluctuation_scalar_le_abs (N := N) z hz hN)
  refine h.trans (le_of_eq ?_)
  rw [div_eq_mul_inv]
  ring

/-- For the scalar case (`d = Unit`) the Frobenius norm of the deviation is the modulus of its
only entry. -/
lemma frob_gueResolventMean_sub_limit_entry (z : ℂ) :
    frob (gueResolventMean (N := N) gueScalarA₀ gueScalarA z -
      operatorMatrixPencilCauchy gueScalarA₀ gueScalarA z)
      = ‖gueResolventMean (N := N) gueScalarA₀ gueScalarA z () () -
        operatorMatrixPencilCauchy gueScalarA₀ gueScalarA z () ()‖ := by
  have hdiff : (gueResolventMean (N := N) gueScalarA₀ gueScalarA z -
      operatorMatrixPencilCauchy gueScalarA₀ gueScalarA z) () ()
      = gueResolventMean (N := N) gueScalarA₀ gueScalarA z () () -
        operatorMatrixPencilCauchy gueScalarA₀ gueScalarA z () () := by
    rw [Matrix.sub_apply]
  have h2 : (frob (gueResolventMean (N := N) gueScalarA₀ gueScalarA z -
      operatorMatrixPencilCauchy gueScalarA₀ gueScalarA z)) ^ 2
      = ‖gueResolventMean (N := N) gueScalarA₀ gueScalarA z () () -
        operatorMatrixPencilCauchy gueScalarA₀ gueScalarA z () ()‖ ^ 2 := by
    rw [frob_sq]
    simp [hdiff]
  calc frob (gueResolventMean (N := N) gueScalarA₀ gueScalarA z -
        operatorMatrixPencilCauchy gueScalarA₀ gueScalarA z)
      = Real.sqrt ((frob (gueResolventMean (N := N) gueScalarA₀ gueScalarA z -
          operatorMatrixPencilCauchy gueScalarA₀ gueScalarA z)) ^ 2) :=
        (Real.sqrt_sq (frob_nonneg _)).symm
    _ = Real.sqrt (‖gueResolventMean (N := N) gueScalarA₀ gueScalarA z () () -
          operatorMatrixPencilCauchy gueScalarA₀ gueScalarA z () ()‖ ^ 2) := by rw [h2]
    _ = ‖gueResolventMean (N := N) gueScalarA₀ gueScalarA z () () -
          operatorMatrixPencilCauchy gueScalarA₀ gueScalarA z () ()‖ :=
        Real.sqrt_sq (norm_nonneg _)

/-- **`frob` form of the threshold-free scalar strip bound.**  This is the shape consumed by
`WeightedStripBound`: on the upper half-plane the Frobenius norm of the averaged resolvent
difference is `O(N⁻² (Im z)⁻⁵)`. -/
theorem frob_gueResolventMean_sub_limit_le_five (z : ℂ) (hz : 0 < z.im) (hN : 0 < N) :
    frob (gueResolventMean (N := N) gueScalarA₀ gueScalarA z -
      operatorMatrixPencilCauchy gueScalarA₀ gueScalarA z)
      ≤ 4 * (N : ℝ)⁻¹ ^ 2 * (z.im)⁻¹ ^ 5 := by
  rw [frob_gueResolventMean_sub_limit_entry]
  exact norm_gueResolventMean_sub_limit_le_five (N := N) z hz hN

/-- **`frob` form of the threshold-free scalar strip bound on both half-planes.** -/
theorem frob_gueResolventMean_sub_limit_le_five_full (z : ℂ) (hz : z.im ≠ 0) (hN : 0 < N) :
    frob (gueResolventMean (N := N) gueScalarA₀ gueScalarA z -
      operatorMatrixPencilCauchy gueScalarA₀ gueScalarA z)
      ≤ 4 * (N : ℝ)⁻¹ ^ 2 * |z.im|⁻¹ ^ 5 := by
  rw [frob_gueResolventMean_sub_limit_entry]
  exact norm_gueResolventMean_sub_limit_le_five_full (N := N) z hz hN

/-- **The full weighted strip bound for the scalar single GUE**, with the honest exponent `β = 5`
and constant `C_s = 4`, for every `η₀` and with no half-plane restriction. -/
theorem weightedStripBound_gueScalar (η₀ : ℝ) :
    WeightedStripBound gueScalarA₀ gueScalarA 0 η₀ 4 5 := by
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN z hz _
  have hNpos : 0 < N := by omega
  have h := frob_gueResolventMean_sub_limit_le_five_full (N := N) z hz hNpos
  refine h.trans (le_of_eq ?_)
  have hzabs : (0 : ℝ) < |z.im| := abs_pos.mpr hz
  have hrpow : |z.im| ^ (-5 : ℝ) = (|z.im| ^ 5)⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hzabs), Real.rpow_ofNat]
  rw [hrpow, div_eq_mul_inv, inv_pow, inv_pow]
  ring

end

end GUEStrongConvergence
