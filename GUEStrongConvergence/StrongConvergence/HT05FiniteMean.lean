/-
# The finite-`N` mean half of the HT05 self-energy argument

This file carries out, for the finite-`N` averaged partial trace
`m = gueResolventMean A₀ A z`, the *mean* half of the Haagerup--Thorbjørnsen self-energy
argument.  It is the finite-`N` companion of the limit self-energy
`z • 1 ↦ A₀ + ∑ i, A i * g * A i` of the free-probability Dyson equation.

## Setup

`T(z,x) = (id_d ⊗ tr_N)(z • 1 - H(x))⁻¹`, `m = E[T]`, `y = z.im > 0`.  The exact finite-`N`
master identity (`gue_dyson_master_identity`) reads

`(z • 1 - A₀) * m - 1 = ∑ i, A i * E[T * A i * T]`.

## What is proved here (all unconditional, kernel-checked, no extra axioms)

* **The mean-centred defect** (`meanCentredDefect`), the difference between the exact
  quadratic term `E[T A i T]` and its mean-field replacement `m A i m`:
  * `frob_meanCentredDefect_le`:
    `frob D ≤ 4 (card d)² (∑ i, frob(A i)²)² N⁻² (im z)⁻⁴`,
    by summing the sharp two-point covariance bound `covariance_partialTrace_mul_le_sharp`
    over `i` with `frob_mul_le`.  The defect is the *mean*-centred one; the limit-centred
    second moment `V_g` is not used.

* **The self-energy and the exact factorization** (`selfEnergy`):
  * `sum_quadratic_eq_mean_add_defect`: the master identity's quadratic term splits as
    `∑ i, A i * E[T A i T] = (∑ i, A i * m * A i) * m + D`;
  * `selfEnergy_sub_smul_one_mul`: `(selfEnergy - z • 1) * m = -D`;
  * `selfEnergy_sub_smul_one`:
    `selfEnergy A₀ A z - z • 1 = -D * m⁻¹`.
    (The last two take the two-sided inverse identities `m * m⁻¹ = 1`, `m⁻¹ * m = 1` as
    explicit hypotheses; supplying them is exactly the invertibility statement of Task 2.)

* **The scalar Stieltjes structure of the resolvent** (the analytic input for the lower
  bound on `‖m⁻¹‖`):
  * `resolvent_qform_im`: for Hermitian coefficients and `y ≠ 0`,
    `Im ∑_{a b} conj(w_a) R_{a b} w_b = -y ∑_j ‖(R* w)_j‖²`, from the exact C⋆-algebra
    identity `R - R* = -2 i y R R*`;
  * `partialTrace_qform_eq` / `partialTrace_qform_im`: the partial trace's pairing is the
    average `N⁻¹ ∑_k` of the pairings against the slice vectors `sliceVec v k = v ⊗ e_k`;
  * `gueResolventMean_qform_im`:
    `Im ∑_{u w} conj(v_u) m_{u w} v_w
      = -y N⁻¹ ∑_k ∫ ∑_j ‖R*(x) (v ⊗ e_k)_j‖² ∂μ`, so `-Im m` is a positive
    semi-definite matrix.

* **The exact second moment of a GUE slice** (the input for the quantitative lower bound):
  * `integral_gueMatrix_mul_star`: `E[G_{i,ab} conj G_{j,cd}] = δ_ij δ_ac δ_bd / N`
    (from `integral_gueMatrix_mul` and the pointwise `conj G_{ab} = G_{ba}`);
  * `integral_normSq_sum_gueMatrix`:
    `∫ ‖∑ i, G_{i,ab} w_i‖² = N⁻¹ ∑ i, ‖w_i‖²`.

## What is *not* proved here (remaining work, in order)

1. `frob (m⁻¹)` bound / invertibility of `m`.  The missing analytic estimate is
   `∫ ‖(z - H)(v ⊗ e_k)‖² ≤ C (∑_a ‖v_a‖²)` with `C = 4 (‖z‖² + (frob A₀ + ∑ frob A_i)²)`,
   obtained from the pointwise expansion
   `((z - H)(v ⊗ e_k))_{(a,k')} = δ_{k'k} ((z - A₀)v)_a - ∑ i, (G_i)_{k'k} ((A i) v)_a`
   together with `integral_normSq_sum_gueMatrix` (no `N`-loss: the slice second moment is
   exactly `N⁻¹ ∑_i ‖(A i) v‖²`).  Combined with the per-slice Cauchy--Schwarz/Jensen
   inequality `∫ ‖R* w‖² ≥ ‖w‖⁴ / ∫ ‖(z - H) w‖²` and `gueResolventMean_qform_im`, this
   gives `-Im m ⪰ c • 1` with `c = y / (card d * C)`, hence `IsUnit m.det` and
   `frob (m⁻¹) ≤ (card d)² / c`.
2. The self-energy error bound
   `frob (selfEnergy - z • 1) ≤ frob D * frob (m⁻¹)`, combining 1 with
   `frob_meanCentredDefect_le` and `selfEnergy_sub_smul_one`.
-/
import GUEStrongConvergence.Probability.SharpTwoPoint
import GUEStrongConvergence.Probability.ScalarLoopSignComplete
import GUEStrongConvergence.Probability.EdgeConcentration
import GUEStrongConvergence.Probability.DysonLimit
import GUEStrongConvergence.Probability.DysonMasterIdentity

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped Matrix.Norms.Elementwise ComplexOrder ENNReal NNReal Topology

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

namespace GUEStrongConvergence

noncomputable section

variable {ι d : Type*} {N : ℕ} [Fintype ι] [Fintype d] [DecidableEq d] [DecidableEq ι]

/-! ## The exact quadratic mean `E[T B T]` -/

/-- The exact finite-`N` quadratic mean `E[T B T]`, written as the entrywise integral of the
pointwise matrix product `T(z,x) * B * T(z,x)`. -/
def guePartialTraceMulMean (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (z : ℂ)
    (B : Matrix d d ℂ) : Matrix d d ℂ :=
  Matrix.of fun u v =>
    ∫ x, (guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) * B *
        guePartialTrace A₀ A z (x : GUECoord ι N → ℝ)) u v
      ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))

@[simp] lemma guePartialTraceMulMean_apply (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (z : ℂ)
    (B : Matrix d d ℂ) (u v : d) :
    guePartialTraceMulMean (N := N) A₀ A z B u v =
      ∫ x, (guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) * B *
          guePartialTrace A₀ A z (x : GUECoord ι N → ℝ)) u v
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := rfl

/-! ## The mean-centred defect -/

/-- **The mean-centred defect** of the finite-`N` Dyson equation,
`D = ∑ i, A i * (E[T A i T] − m A i m)`, where `m = E[T]`.
This is the difference between the exact quadratic term and its mean-field replacement;
it is *not* the limit-centred second moment `V_g`. -/
def meanCentredDefect (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (z : ℂ) : Matrix d d ℂ :=
  ∑ i, A i * (guePartialTraceMulMean (N := N) A₀ A z (A i) -
    gueResolventMean (N := N) A₀ A z * A i * gueResolventMean (N := N) A₀ A z)

/-- The master identity with the quadratic mean written through `guePartialTraceMulMean`. -/
theorem gue_master_identity_defect_form (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (hN : (N : ℂ) ≠ 0) :
    (z • (1 : Matrix d d ℂ) - A₀) * gueResolventMean (N := N) A₀ A z - 1
      = ∑ i, A i * guePartialTraceMulMean (N := N) A₀ A z (A i) := by
  simpa only [guePartialTraceMulMean] using gue_dyson_master_identity A₀ A hA₀ hA z hz hN

/-- The sharp two-point covariance bound, in the exact shape of the mean-centred defect. -/
theorem frob_quadratic_sub_mean_le (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (hN : 0 < N) (B : Matrix d d ℂ) (hB : B.IsHermitian) :
    frob (guePartialTraceMulMean (N := N) A₀ A z B -
        gueResolventMean (N := N) A₀ A z * B * gueResolventMean (N := N) A₀ A z)
      ≤ 2 * (Fintype.card d : ℝ) ^ 2 * frob B *
          (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4 / (N : ℝ)) :=
  covariance_partialTrace_mul_le_sharp A₀ A hA₀ hA z hz hN B hB

/-- **Sharp Frobenius bound for the mean-centred defect.**
`frob D ≤ 4 (card d)² (∑ i, frob(A i)²)² N⁻² (im z)⁻⁴`. -/
theorem frob_meanCentredDefect_le (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (hN : 0 < N) :
    frob (meanCentredDefect (N := N) A₀ A z)
      ≤ 4 * (Fintype.card d : ℝ) ^ 2 * (∑ i, (frob (A i)) ^ 2) ^ 2 *
          ((N : ℝ)⁻¹) ^ 2 * ((z.im)⁻¹) ^ 4 := by
  classical
  set S : ℝ := ∑ i, (frob (A i)) ^ 2 with hS
  have hstep : ∀ i : ι, frob (A i * (guePartialTraceMulMean (N := N) A₀ A z (A i) -
      gueResolventMean (N := N) A₀ A z * A i * gueResolventMean (N := N) A₀ A z))
      ≤ (4 * (Fintype.card d : ℝ) ^ 2 * S * (gueScale N) ^ 2 * ((z.im)⁻¹) ^ 4 /
          (N : ℝ)) * (frob (A i)) ^ 2 := by
    intro i
    refine (frob_mul_le _ _).trans ?_
    have h := frob_quadratic_sub_mean_le A₀ A hA₀ hA z hz hN (A i) (hA i)
    have hf0 : 0 ≤ frob (A i) := frob_nonneg _
    calc frob (A i) * frob (guePartialTraceMulMean (N := N) A₀ A z (A i) -
          gueResolventMean (N := N) A₀ A z * A i * gueResolventMean (N := N) A₀ A z)
        ≤ frob (A i) * (2 * (Fintype.card d : ℝ) ^ 2 * frob (A i) *
            (2 * (gueScale N) ^ 2 * (∑ j, (frob (A j)) ^ 2) * ((z.im)⁻¹) ^ 4 /
              (N : ℝ))) :=
          mul_le_mul_of_nonneg_left (by simpa only [hS] using h) hf0
      _ = (4 * (Fintype.card d : ℝ) ^ 2 * S * (gueScale N) ^ 2 * ((z.im)⁻¹) ^ 4 /
            (N : ℝ)) * (frob (A i)) ^ 2 := by
          rw [hS]; ring
  refine (frob_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ => hstep i).trans ?_
  refine le_of_eq ?_
  rw [← Finset.mul_sum, ← hS, gueScale_sq N]
  field_simp

/-! ## The self-energy and the exact factorization -/

/-- The finite-`N` self-energy `Λ = A₀ + ∑ i, A i * m * A i + m⁻¹`, the finite-`N` analogue of
the limit self-energy `A₀ + ∑ i, A i * g * A i`. -/
def selfEnergy (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (z : ℂ) : Matrix d d ℂ :=
  A₀ + ∑ i, A i * gueResolventMean (N := N) A₀ A z * A i +
    (gueResolventMean (N := N) A₀ A z)⁻¹

/-- The quadratic term of the master identity, split into its mean-field part and the
mean-centred defect. -/
theorem sum_quadratic_eq_mean_add_defect (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (z : ℂ) :
    (∑ i, A i * guePartialTraceMulMean (N := N) A₀ A z (A i))
      = (∑ i, A i * gueResolventMean (N := N) A₀ A z * A i) *
          gueResolventMean (N := N) A₀ A z
        + meanCentredDefect (N := N) A₀ A z := by
  classical
  have hterm : ∀ i : ι, A i * guePartialTraceMulMean (N := N) A₀ A z (A i)
      = (A i * gueResolventMean (N := N) A₀ A z * A i) *
          gueResolventMean (N := N) A₀ A z
        + A i * (guePartialTraceMulMean (N := N) A₀ A z (A i) -
            gueResolventMean (N := N) A₀ A z * A i * gueResolventMean (N := N) A₀ A z) := by
    intro i
    noncomm_ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib, ← Finset.sum_mul]
  rfl

/-- **The finite-`N` Dyson identity shifted by the self-energy.**  Multiplying the self-energy
defect by `m` produces exactly minus the mean-centred defect. -/
theorem selfEnergy_sub_smul_one_mul (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (hN : (N : ℂ) ≠ 0)
    (hm : gueResolventMean (N := N) A₀ A z * (gueResolventMean (N := N) A₀ A z)⁻¹ = 1)
    (hmL : (gueResolventMean (N := N) A₀ A z)⁻¹ * gueResolventMean (N := N) A₀ A z = 1) :
    (selfEnergy (N := N) A₀ A z - z • (1 : Matrix d d ℂ)) *
        gueResolventMean (N := N) A₀ A z
      = -(meanCentredDefect (N := N) A₀ A z) := by
  classical
  have hmaster := gue_master_identity_defect_form (N := N) A₀ A hA₀ hA z hz hN
  rw [sum_quadratic_eq_mean_add_defect (N := N) A₀ A z] at hmaster
  have hsub : (z • (1 : Matrix d d ℂ) - A₀) * gueResolventMean (N := N) A₀ A z
      = z • gueResolventMean (N := N) A₀ A z -
          A₀ * gueResolventMean (N := N) A₀ A z := by
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]
  have hz1 : z • gueResolventMean (N := N) A₀ A z
      = A₀ * gueResolventMean (N := N) A₀ A z + 1 +
          (∑ i, A i * gueResolventMean (N := N) A₀ A z * A i) *
            gueResolventMean (N := N) A₀ A z
        + meanCentredDefect (N := N) A₀ A z := by
    have h := hmaster
    rw [hsub] at h
    calc z • gueResolventMean (N := N) A₀ A z
        = (z • gueResolventMean (N := N) A₀ A z -
            A₀ * gueResolventMean (N := N) A₀ A z - 1) +
            A₀ * gueResolventMean (N := N) A₀ A z + 1 := by abel
      _ = ((∑ i, A i * gueResolventMean (N := N) A₀ A z * A i) *
              gueResolventMean (N := N) A₀ A z + meanCentredDefect (N := N) A₀ A z) +
            A₀ * gueResolventMean (N := N) A₀ A z + 1 := by rw [← h]
      _ = A₀ * gueResolventMean (N := N) A₀ A z + 1 +
            (∑ i, A i * gueResolventMean (N := N) A₀ A z * A i) *
              gueResolventMean (N := N) A₀ A z +
            meanCentredDefect (N := N) A₀ A z := by abel
  have hexp : (selfEnergy (N := N) A₀ A z - z • (1 : Matrix d d ℂ)) *
        gueResolventMean (N := N) A₀ A z
      = (A₀ + ∑ i, A i * gueResolventMean (N := N) A₀ A z * A i) *
            gueResolventMean (N := N) A₀ A z
        + (gueResolventMean (N := N) A₀ A z)⁻¹ * gueResolventMean (N := N) A₀ A z
        - z • gueResolventMean (N := N) A₀ A z := by
    rw [selfEnergy, Matrix.sub_mul, Matrix.add_mul, Matrix.add_mul, Matrix.smul_mul,
      Matrix.one_mul]
  rw [hexp, Matrix.add_mul, hmL, hz1]
  abel

/-- **The exact self-energy factorization.**
`selfEnergy A₀ A z - z • 1 = -(meanCentredDefect A₀ A z) * m⁻¹`. -/
theorem selfEnergy_sub_smul_one (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (hN : (N : ℂ) ≠ 0)
    (hm : gueResolventMean (N := N) A₀ A z * (gueResolventMean (N := N) A₀ A z)⁻¹ = 1)
    (hmL : (gueResolventMean (N := N) A₀ A z)⁻¹ * gueResolventMean (N := N) A₀ A z = 1) :
    selfEnergy (N := N) A₀ A z - z • (1 : Matrix d d ℂ)
      = -(meanCentredDefect (N := N) A₀ A z) * (gueResolventMean (N := N) A₀ A z)⁻¹ := by
  classical
  have hmain := selfEnergy_sub_smul_one_mul (N := N) A₀ A hA₀ hA z hz hN hm hmL
  calc selfEnergy (N := N) A₀ A z - z • (1 : Matrix d d ℂ)
      = (selfEnergy (N := N) A₀ A z - z • (1 : Matrix d d ℂ)) *
          gueResolventMean (N := N) A₀ A z *
          (gueResolventMean (N := N) A₀ A z)⁻¹ := by
        rw [mul_assoc, hm, mul_one]
    _ = -(meanCentredDefect (N := N) A₀ A z) *
          (gueResolventMean (N := N) A₀ A z)⁻¹ := by rw [hmain]

/-! ## The scalar Stieltjes structure of the resolvent

For a Hermitian pencil and `y = Im z ≠ 0`, the resolvent `R = (z - H)⁻¹` satisfies
`R - R* = -2 i y · R R*`.  Consequently the sesquilinear pairing `⟪w, R w⟫` has imaginary part
`-y ‖R* w‖²`; after partial trace and Gaussian averaging this turns the imaginary part of the
mean into an average of Hilbert–Schmidt norms, which is what the lower bound on `‖m⁻¹‖` needs.
-/

/-- The resolvent satisfies `R * (z - H) = 1` as well. -/
lemma resolvent_mul_guePencil_sub (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (x : GUECoord ι N → ℝ) (z : ℂ) (hz : z.im ≠ 0) :
    guePencilResolvent A₀ A x z *
        (algebraMap ℂ (CStarMatrix (d × Fin N) (d × Fin N) ℂ) z - guePencil A₀ A x) = 1 := by
  have hunit : IsUnit (algebraMap ℂ (CStarMatrix (d × Fin N) (d × Fin N) ℂ) z -
      guePencil A₀ A x) := guePencil_mem_resolventSet A₀ A hA₀ hA x z hz
  simpa [guePencilResolvent, resolvent] using Ring.inverse_mul_cancel _ hunit

/-- **The resolvent pairing is a scalar Stieltjes transform.**
For every `w : d × Fin N → ℂ`,
`Im ∑_{a b} conj(w_a) R_{a b} w_b = -(Im z) ∑_j ‖(R* w)_j‖²`. -/
theorem resolvent_qform_im (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (x : GUECoord ι N → ℝ) (z : ℂ) (hz : z.im ≠ 0) (w : d × Fin N → ℂ) :
    (∑ a, ∑ b, star (w a) * guePencilResolvent A₀ A x z a b * w b).im
      = -z.im * ∑ j, ‖matVec (star (guePencilResolvent A₀ A x z)) w j‖ ^ 2 := by
  classical
  set R : CStarMatrix (d × Fin N) (d × Fin N) ℂ := guePencilResolvent A₀ A x z with hR
  set X : CStarMatrix (d × Fin N) (d × Fin N) ℂ :=
    algebraMap ℂ (CStarMatrix (d × Fin N) (d × Fin N) ℂ) z - guePencil A₀ A x with hX
  have hXR : X * R = 1 := resolvent_mul_guePencil A₀ A hA₀ hA x z hz
  have hRX : R * X = 1 := resolvent_mul_guePencil_sub A₀ A hA₀ hA x z hz
  have hdiff : star X - X = (star z - z) • (1 : CStarMatrix (d × Fin N) (d × Fin N) ℂ) := by
    rw [hX]
    simp only [Algebra.algebraMap_eq_smul_one, star_sub, star_smul, star_one,
      (guePencil_isSelfAdjoint A₀ A hA₀ hA x).star_eq, sub_smul]
    abel
  -- the key algebraic identity `R - R* = (conj z - z) • (R R*)`
  have key : R - star R = R * (star X - X) * star R := by
    have h1 : star X * star R = 1 := by
      rw [← star_mul, hRX, star_one]
    have e1 : R * star X * star R = R := by rw [mul_assoc, h1, mul_one]
    have e2 : R * X * star R = star R := by rw [hRX, one_mul]
    calc R - star R = R * star X * star R - R * X * star R := by rw [e1, e2]
      _ = R * (star X - X) * star R := by noncomm_ring
  have key2 : R - star R = (star z - z) • (R * star R) := by
    rw [key, hdiff, CStarMatrix.mul_smul, mul_one, CStarMatrix.smul_mul]
  -- entrywise form
  have hentry : ∀ a b, (R - star R) a b = (star z - z) * (R * star R) a b := by
    intro a b
    have h := congrArg (fun M : CStarMatrix (d × Fin N) (d × Fin N) ℂ => M a b) key2
    simpa [CStarMatrix.sub_apply, CStarMatrix.smul_apply, smul_eq_mul] using h
  -- pair the identity against `w`
  have hpair : (∑ a, ∑ b, star (w a) * (R - star R) a b * w b)
      = (star z - z) * ∑ a, ∑ b, star (w a) * (R * star R) a b * w b := by
    simp only [hentry, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  -- the conjugate of the pairing
  have hexpand : star (∑ a, ∑ b, star (w a) * R a b * w b)
      = ∑ a, ∑ b, star (w b) * (star (R a b) * w a) := by
    rw [star_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [star_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [star_mul, star_mul, star_star]
  have hconj : (∑ a, ∑ b, star (w a) * (star R) a b * w b)
      = star (∑ a, ∑ b, star (w a) * R a b * w b) := by
    rw [hexpand]
    rw [show (∑ a, ∑ b, star (w a) * (star R) a b * w b)
        = ∑ a, ∑ b, star (w a) * (star (R b a) * w b) from by
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [CStarMatrix.star_apply]
      ring]
    rw [Finset.sum_comm]
  -- `R R*` paired against `w` is the sum of the squared norms of `R* w`
  have hgram : (∑ a, ∑ b, star (w a) * (R * star R) a b * w b)
      = ((∑ j, ‖matVec (star R) w j‖ ^ 2 : ℝ) : ℂ) := by
    have hmul : ∀ a b, (R * star R) a b = ∑ j, R a j * star (R b j) := by
      intro a b
      rw [CStarMatrix.mul_apply]
      exact Finset.sum_congr rfl fun j _ => by rw [CStarMatrix.star_apply]
    have hterm : ∀ a b, star (w a) * (∑ j, R a j * star (R b j)) * w b
        = ∑ j, star (w a) * R a j * star (R b j) * w b := by
      intro a b
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have hstep : (∑ a, ∑ b, star (w a) * (R * star R) a b * w b)
        = ∑ j, (∑ a, star (w a) * R a j) * (∑ b, star (R b j) * w b) := by
      conv_lhs => enter [2, a, 2, b]; rw [hmul a b, hterm a b]
      conv_lhs => enter [2, a]; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    have hrow : ∀ j, (∑ a, star (w a) * R a j) = star (matVec (star R) w j) := by
      intro j
      rw [matVec, star_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [star_mul, CStarMatrix.star_apply, star_star]
    have hcol : ∀ j, (∑ b, star (R b j) * w b) = matVec (star R) w j := by
      intro j
      rw [matVec]
      exact Finset.sum_congr rfl fun b _ => by rw [CStarMatrix.star_apply]
    rw [hstep, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hrow j, hcol j]
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  -- assemble
  have hsplit2 : (∑ a, ∑ b, star (w a) * R a b * w b) -
      (∑ a, ∑ b, star (w a) * (star R) a b * w b)
      = ∑ a, ∑ b, star (w a) * (R - star R) a b * w b := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [CStarMatrix.sub_apply]
    ring
  have hmain : (∑ a, ∑ b, star (w a) * R a b * w b) -
      (∑ a, ∑ b, star (w a) * (star R) a b * w b)
      = (star z - z) * ((∑ j, ‖matVec (star R) w j‖ ^ 2 : ℝ) : ℂ) := by
    rw [hsplit2, hpair, hgram]
  have him : (∑ a, ∑ b, star (w a) * R a b * w b).im
      = -z.im * ∑ j, ‖matVec (star R) w j‖ ^ 2 := by
    have h := congrArg Complex.im hmain
    rw [hconj] at h
    simp only [Complex.sub_im, Complex.star_def, Complex.conj_im, Complex.mul_im,
      Complex.ofReal_im, Complex.ofReal_re, mul_zero, add_zero, sub_zero] at h
    have h2 : (-z.im - z.im) * (∑ j, ‖matVec (star R) w j‖ ^ 2)
        = 2 * (-(z.im * ∑ j, ‖matVec (star R) w j‖ ^ 2)) := by ring
    rw [h2] at h
    simp only [Complex.star_def] at h ⊢
    rw [neg_mul]
    linarith
  exact him

/-! ## The quadratic form of the partial trace

`T = (id_d ⊗ tr_N) R` is an average over the `N` slice vectors `v ⊗ e_k` of the quadratic
forms of `R`.  This is the bridge between the scalar Stieltjes identity for `R` and the mean
`m`: the imaginary part of `⟪v, m v⟫` is an average of Hilbert--Schmidt norms of
`R* (v ⊗ e_k)`.
-/

/-- The vector `v ⊗ e_k`, supported on the `k`-th `N`-slice. -/
def sliceVec (v : d → ℂ) (k : Fin N) : d × Fin N → ℂ := fun p => v p.1 * (if p.2 = k then 1 else 0)

@[simp] lemma sliceVec_apply (v : d → ℂ) (k : Fin N) (a : d) (k' : Fin N) :
    sliceVec v k (a, k') = v a * (if k' = k then 1 else 0) := rfl

lemma sum_normSq_sliceVec (v : d → ℂ) (k : Fin N) :
    (∑ p : d × Fin N, ‖sliceVec v k p‖ ^ 2) = ∑ a : d, ‖v a‖ ^ 2 := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single k (fun k' _ hk' => by simp [sliceVec, hk'])
    (fun hk => absurd (Finset.mem_univ k) hk)]
  simp [sliceVec]

/-- Collapsing the `N`-block summation against the slice vector. -/
lemma sum_slice_pairing (v : d → ℂ) (k : Fin N) (M : d × Fin N → d × Fin N → ℂ) :
    (∑ a : d × Fin N, ∑ b : d × Fin N, star (sliceVec v k a) * M a b * sliceVec v k b)
      = ∑ u, ∑ w, star (v u) * M (u, k) (w, k) * v w := by
  classical
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  conv_lhs => enter [2, u]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_eq_single k (fun k' _ hk' => by simp [sliceVec, hk'])
    (fun hk => absurd (Finset.mem_univ k) hk)]
  rw [Finset.sum_eq_single k (fun l _ hl => by simp [sliceVec, hl])
    (fun hk => absurd (Finset.mem_univ k) hk)]
  simp [sliceVec]

/-- The pairing of the partial trace against `v` is the average over slices of the pairings of
the resolvent against the slice vectors. -/
theorem partialTrace_qform_eq (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (z : ℂ)
    (x : GUECoord ι N → ℝ) (v : d → ℂ) :
    (∑ u, ∑ w, star (v u) * guePartialTrace A₀ A z x u w * v w)
      = (N : ℂ)⁻¹ * ∑ k : Fin N, ∑ a : d × Fin N, ∑ b : d × Fin N,
          star (sliceVec v k a) * guePencilResolvent A₀ A x z a b * sliceVec v k b := by
  classical
  have hterm : ∀ u w : d, star (v u) * guePartialTrace A₀ A z x u w * v w
      = ∑ k : Fin N, (N : ℂ)⁻¹ *
          (star (v u) * guePencilResolvent A₀ A x z (u, k) (w, k) * v w) := by
    intro u w
    rw [guePartialTrace_apply]
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hRHS : (∑ k : Fin N, ∑ a : d × Fin N, ∑ b : d × Fin N,
        star (sliceVec v k a) * guePencilResolvent A₀ A x z a b * sliceVec v k b)
      = ∑ k : Fin N, ∑ u, ∑ w,
          star (v u) * guePencilResolvent A₀ A x z (u, k) (w, k) * v w := by
    refine Finset.sum_congr rfl fun k _ => ?_
    exact sum_slice_pairing v k (fun a b => guePencilResolvent A₀ A x z a b)
  simp only [hterm, hRHS]
  conv_lhs => enter [2, u]; rw [Finset.sum_comm]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.mul_sum]

/-- **The pointwise imaginary part of the partial-trace pairing.** -/
theorem partialTrace_qform_im (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (x : GUECoord ι N → ℝ) (v : d → ℂ) :
    (∑ u, ∑ w, star (v u) * guePartialTrace A₀ A z x u w * v w).im
      = -z.im * (N : ℝ)⁻¹ * ∑ k : Fin N, ∑ j,
          ‖matVec (star (guePencilResolvent A₀ A x z)) (sliceVec v k) j‖ ^ 2 := by
  classical
  have hNre : ((N : ℂ)⁻¹).re = (N : ℝ)⁻¹ := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re]
  have hNim : ((N : ℂ)⁻¹).im = 0 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_im]
  have hmap : (∑ k : Fin N, ∑ a : d × Fin N, ∑ b : d × Fin N,
      star (sliceVec v k a) * guePencilResolvent A₀ A x z a b * sliceVec v k b).im
      = ∑ k : Fin N, (∑ a : d × Fin N, ∑ b : d × Fin N,
          star (sliceVec v k a) * guePencilResolvent A₀ A x z a b * sliceVec v k b).im := by
    simpa using map_sum Complex.imCLM.toAddMonoidHom
      (fun k => (∑ a : d × Fin N, ∑ b : d × Fin N,
        star (sliceVec v k a) * guePencilResolvent A₀ A x z a b * sliceVec v k b)) Finset.univ
  have hsum : (∑ k : Fin N, ∑ a : d × Fin N, ∑ b : d × Fin N,
      star (sliceVec v k a) * guePencilResolvent A₀ A x z a b * sliceVec v k b).im
      = ∑ k : Fin N, (-z.im * ∑ j,
          ‖matVec (star (guePencilResolvent A₀ A x z)) (sliceVec v k) j‖ ^ 2) := by
    rw [hmap]
    exact Finset.sum_congr rfl fun k _ =>
      resolvent_qform_im A₀ A hA₀ hA x z hz (sliceVec v k)
  rw [partialTrace_qform_eq, Complex.mul_im, hNre, hNim, zero_mul, add_zero, hsum,
    Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- Integrability (and boundedness) of `x ↦ ∑_j ‖R(x)* w_j‖²`. -/
lemma integrable_sum_normSq_matVec_star (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (hN : 0 < N) (w : d × Fin N → ℂ) :
    Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      ∑ j, ‖matVec (star (guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z)) w j‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  classical
  have hz' : z.im ≠ 0 := ne_of_gt hz
  have hcont_entry : ∀ j : d × Fin N, Continuous (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      matVec (star (guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z)) w j) := by
    intro j
    have hfun : (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        matVec (star (guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z)) w j)
        = fun (x : EuclideanSpace ℝ (GUECoord ι N)) =>
            ∑ b, star (guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z b j) * w b := by
      funext x
      rw [matVec]
      exact Finset.sum_congr rfl fun b _ => by rw [CStarMatrix.star_apply]
    rw [hfun]
    exact continuous_finsetSum _ fun b _ =>
      ((continuous_guePencilResolvent_entry_euclid A₀ A hA₀ hA z hz' b j).star).mul
        continuous_const
  have hcont : Continuous (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      ∑ j, ‖matVec (star (guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z)) w j‖ ^ 2) :=
    continuous_finsetSum _ fun j _ => ((hcont_entry j).norm).pow 2
  refine Integrable.of_bound hcont.aestronglyMeasurable
    ((Fintype.card (d × Fin N) : ℝ) * ((z.im)⁻¹ * ∑ b, ‖w b‖) ^ 2)
    (ae_of_all _ fun x => ?_)
  have hb : ∑ j, ‖matVec (star (guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z)) w j‖ ^ 2
      ≤ (Fintype.card (d × Fin N) : ℝ) * ((z.im)⁻¹ * ∑ b, ‖w b‖) ^ 2 := by
    have hentry : ∀ j : d × Fin N,
        ‖matVec (star (guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z)) w j‖
          ≤ (z.im)⁻¹ * ∑ b, ‖w b‖ := by
      intro j
      rw [matVec]
      refine (norm_sum_le _ _).trans ?_
      have hbound : ∀ b : d × Fin N,
          ‖(star (guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z)) j b * w b‖
            ≤ (z.im)⁻¹ * ‖w b‖ := by
        intro b
        rw [norm_mul, CStarMatrix.star_apply]
        have h1 : ‖star (guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z b j)‖
            = ‖guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z b j‖ := norm_star _
        rw [h1]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        calc ‖guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z b j‖ ≤ |z.im|⁻¹ :=
              CStarMatrix.norm_entry_le_norm.trans
                (norm_guePencilResolvent_le A₀ A hA₀ hA (x : GUECoord ι N → ℝ) z hz')
          _ = (z.im)⁻¹ := by rw [abs_of_pos hz]
      calc ∑ b, ‖(star (guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z)) j b * w b‖
          ≤ ∑ b, (z.im)⁻¹ * ‖w b‖ := Finset.sum_le_sum fun b _ => hbound b
        _ = (z.im)⁻¹ * ∑ b, ‖w b‖ := by rw [Finset.mul_sum]
    calc ∑ j, ‖matVec (star (guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z)) w j‖ ^ 2
        ≤ ∑ _j : d × Fin N, ((z.im)⁻¹ * ∑ b, ‖w b‖) ^ 2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          exact pow_le_pow_left₀ (norm_nonneg _) (hentry j) 2
      _ = (Fintype.card (d × Fin N) : ℝ) * ((z.im)⁻¹ * ∑ b, ‖w b‖) ^ 2 := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hnn : (0 : ℝ) ≤ ∑ j, ‖matVec (star (guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z)) w j‖ ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [Real.norm_of_nonneg hnn]
  exact hb

/-- **The imaginary part of the finite-`N` mean's quadratic form.** -/
theorem gueResolventMean_qform_im (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (hN : 0 < N) (v : d → ℂ) :
    (∑ u, ∑ w, star (v u) * gueResolventMean (N := N) A₀ A z u w * v w).im
      = -z.im * (N : ℝ)⁻¹ * ∑ k : Fin N,
          ∫ x, ∑ j, ‖matVec (star (guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z))
              (sliceVec v k) j‖ ^ 2
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  classical
  have hz' : z.im ≠ 0 := ne_of_gt hz
  -- pointwise integrability of the pairing
  have hpt_int : ∀ u w : d, Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      star (v u) * guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u w * v w)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    intro u w
    have h := integrable_guePartialTrace_entry A₀ A hA₀ hA z hz hN u w
    refine (h.const_mul (star (v u) * v w)).congr (ae_of_all _ fun x => ?_)
    ring
  -- (1) the pairing of the mean is the integral of the pointwise pairing
  have hInt : (∑ u, ∑ w, star (v u) * gueResolventMean (N := N) A₀ A z u w * v w)
      = ∫ x, (∑ u, ∑ w, star (v u) * guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u w * v w)
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    have hterm : ∀ u w : d, star (v u) * gueResolventMean (N := N) A₀ A z u w * v w
        = ∫ x, star (v u) * guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u w * v w
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
      intro u w
      rw [gueResolventMean_apply]
      calc star (v u) *
            (∫ x : EuclideanSpace ℝ (GUECoord ι N),
              guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u w
              ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) * v w
          = (star (v u) * v w) *
            (∫ x : EuclideanSpace ℝ (GUECoord ι N),
              guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u w
              ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) := by ring
        _ = ∫ x : EuclideanSpace ℝ (GUECoord ι N),
              (star (v u) * v w) * guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u w
              ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
            (MeasureTheory.integral_const_mul _ _).symm
        _ = ∫ x : EuclideanSpace ℝ (GUECoord ι N),
              star (v u) * guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u w * v w
              ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
            integral_congr_ae (ae_of_all _ fun x => by ring)
    calc (∑ u, ∑ w, star (v u) * gueResolventMean (N := N) A₀ A z u w * v w)
        = ∑ u, ∑ w, ∫ x, star (v u) * guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u w * v w
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
          Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => hterm u w
      _ = ∑ u, ∫ x, ∑ w, star (v u) * guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u w * v w
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [integral_finsetSum]
          intro w _
          exact hpt_int u w
      _ = ∫ x, ∑ u, ∑ w, star (v u) * guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u w * v w
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
          rw [integral_finsetSum]
          intro u _
          exact integrable_finsetSum _ fun w _ => hpt_int u w
  -- (2) pass to the imaginary part inside the integral
  have hIntIm : Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      ∑ u, ∑ w, star (v u) * guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u w * v w)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
    integrable_finsetSum _ fun u _ => integrable_finsetSum _ fun w _ => hpt_int u w
  have him : (∑ u, ∑ w, star (v u) * gueResolventMean (N := N) A₀ A z u w * v w).im
      = ∫ x, (∑ u, ∑ w, star (v u) * guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u w * v w).im
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    rw [hInt]
    have h := ContinuousLinearMap.integral_comp_comm (L := Complex.imCLM)
      (φ := fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        ∑ u, ∑ w, star (v u) * guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u w * v w)
      hIntIm
    simpa [Complex.imCLM_apply] using h.symm
  -- (3) insert the pointwise identity and integrate
  rw [him]
  have hcongr : (∫ x : EuclideanSpace ℝ (GUECoord ι N),
        (∑ u, ∑ w, star (v u) * guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u w * v w).im
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
      = ∫ x : EuclideanSpace ℝ (GUECoord ι N),
          (-z.im * (N : ℝ)⁻¹ * ∑ k : Fin N, ∑ j,
            ‖matVec (star (guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z)) (sliceVec v k) j‖ ^ 2)
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    exact partialTrace_qform_im A₀ A hA₀ hA z hz' (x : GUECoord ι N → ℝ) v
  rw [hcongr]
  rw [integral_const_mul]
  congr 1
  rw [integral_finsetSum]
  intro k _
  exact integrable_sum_normSq_matVec_star A₀ A hA₀ hA z hz hN (sliceVec v k)

/-! ## The second moment of the Gaussian pencil along a slice

The exact second moment of the pencil requires only the complex covariance
`E[G_{i,ab} conj G_{j,cd}] = δ_{ij} δ_{ac} δ_{bd} / N` of the GUE blocks, which follows from
`integral_gueMatrix_mul` and the pointwise Hermiticity `conj G_{ab} = G_{ba}`.
-/

/-- Covariance of the normalized GUE entries with one conjugate factor. -/
lemma integral_gueMatrix_mul_star (i j : ι) (a b c d : Fin N) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        gueMatrix (x : GUECoord ι N → ℝ) i a b * star (gueMatrix (x : GUECoord ι N → ℝ) j c d)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      = if i = j ∧ a = c ∧ b = d then ((N : ℝ)⁻¹ : ℂ) else 0 := by
  have hpt : ∀ x : EuclideanSpace ℝ (GUECoord ι N),
      star (gueMatrix (x : GUECoord ι N → ℝ) j c d)
        = gueMatrix (x : GUECoord ι N → ℝ) j d c := by
    intro x
    have h := congrArg (fun M : Matrix (Fin N) (Fin N) ℂ => M d c)
      (gueMatrix_conjTranspose (x : GUECoord ι N → ℝ) j)
    simpa only [Matrix.conjTranspose_apply] using h
  calc ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        gueMatrix (x : GUECoord ι N → ℝ) i a b * star (gueMatrix (x : GUECoord ι N → ℝ) j c d)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      = ∫ x : EuclideanSpace ℝ (GUECoord ι N),
          gueMatrix (x : GUECoord ι N → ℝ) i a b * gueMatrix (x : GUECoord ι N → ℝ) j d c
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
        integral_congr_ae (ae_of_all _ fun x => by simp only [hpt x])
    _ = if i = j ∧ a = c ∧ b = d then ((N : ℝ)⁻¹ : ℂ) else 0 := by
        rw [integral_gueMatrix_mul]

/-- **Second moment of a fixed entry of a weighted sum of GUE blocks.** -/
lemma integral_normSq_sum_gueMatrix (w : ι → ℂ) (a b : Fin N) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        ‖∑ i, gueMatrix (x : GUECoord ι N → ℝ) i a b * w i‖ ^ 2
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      = (N : ℝ)⁻¹ * ∑ i, ‖w i‖ ^ 2 := by
  classical
  have hprod_int : ∀ i j : ι, Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      (w i * star (w j)) * (gueMatrix (x : GUECoord ι N → ℝ) i a b *
        star (gueMatrix (x : GUECoord ι N → ℝ) j a b)))
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    intro i j
    refine Integrable.const_mul ?_ _
    exact memLp_one_iff_integrable.mp
      (MemLp.mul (p := 2) (q := 2) (r := 1) (memLp_gueMatrix_entry (N := N) i a b)
        (memLp_gueMatrix_entry (N := N) j a b).star)
  -- the complex-valued pointwise expansion
  have hpt : ∀ y : GUECoord ι N → ℝ,
      ((‖∑ i, gueMatrix y i a b * w i‖ ^ 2 : ℝ) : ℂ)
        = ∑ i, ∑ j, (w i * star (w j)) * (gueMatrix y i a b * star (gueMatrix y j a b)) := by
    intro y
    have hcast : ((‖∑ i, gueMatrix y i a b * w i‖ ^ 2 : ℝ) : ℂ)
        = (↑‖∑ i, gueMatrix y i a b * w i‖) ^ 2 := by push_cast; ring
    rw [hcast, ← Complex.mul_conj']
    rw [show (starRingEnd ℂ) (∑ i, gueMatrix y i a b * w i)
        = ∑ i, star (w i) * star (gueMatrix y i a b) from by
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul]
      simp only [Complex.star_def]
      ring]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hC : (∫ x : EuclideanSpace ℝ (GUECoord ι N),
        ((‖∑ i, gueMatrix (x : GUECoord ι N → ℝ) i a b * w i‖ ^ 2 : ℝ) : ℂ)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
      = ((N : ℝ)⁻¹ * ∑ i, ‖w i‖ ^ 2 : ℝ) := by
    have hpt_eq : (∫ x : EuclideanSpace ℝ (GUECoord ι N),
          ((‖∑ i, gueMatrix (x : GUECoord ι N → ℝ) i a b * w i‖ ^ 2 : ℝ) : ℂ)
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
        = ∫ x : EuclideanSpace ℝ (GUECoord ι N),
            ∑ i, ∑ j, (w i * star (w j)) *
              (gueMatrix (x : GUECoord ι N → ℝ) i a b *
                star (gueMatrix (x : GUECoord ι N → ℝ) j a b))
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      exact hpt (x : GUECoord ι N → ℝ)
    rw [hpt_eq, integral_finsetSum]
    · rw [show ((N : ℝ)⁻¹ * ∑ i, ‖w i‖ ^ 2 : ℝ) = ∑ i, (N : ℝ)⁻¹ * ‖w i‖ ^ 2 from by
        rw [Finset.mul_sum]]
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum]
      · rw [Finset.sum_eq_single i]
        · rw [integral_const_mul, integral_gueMatrix_mul_star, if_pos (by simp)]
          rw [show w i * star (w i) = ((‖w i‖ ^ 2 : ℝ) : ℂ) from by
            rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]]
          push_cast
          ring
        · intro j _ hj
          rw [integral_const_mul, integral_gueMatrix_mul_star,
            if_neg (fun h : i = j ∧ a = a ∧ b = b => hj h.1.symm), mul_zero]
        · intro h
          exact absurd (Finset.mem_univ i) h
      · intro j _
        exact hprod_int i j
    · intro i _
      exact integrable_finsetSum _ fun j _ => hprod_int i j
  rw [show (∫ x : EuclideanSpace ℝ (GUECoord ι N),
        ((‖∑ i, gueMatrix (x : GUECoord ι N → ℝ) i a b * w i‖ ^ 2 : ℝ) : ℂ)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
      = ((∫ x : EuclideanSpace ℝ (GUECoord ι N),
          ‖∑ i, gueMatrix (x : GUECoord ι N → ℝ) i a b * w i‖ ^ 2
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) : ℝ) : ℂ) from
    integral_ofReal] at hC
  exact Complex.ofReal_injective hC

end

end GUEStrongConvergence
