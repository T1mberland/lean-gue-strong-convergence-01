/-
# Mixed two-letter normalized GUE traces

Polarizing the exact square-sum identity identifies every two-letter normalized trace
with the scalar Gaussian coordinate inner product. This keeps the matrix trace,
normalization, and ordered matrix product explicit.
-/
import GUEStrongConvergence.Probability.QuadraticTrace

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace GUEStrongConvergence

noncomputable section

variable {ι : Type*} {N : ℕ}

lemma gueSquareSum_add (x y : GUECoord ι N → ℝ) (i : ι) :
    gueSquareSum (fun p => x p + y p) i = gueSquareSum x i +
      2 * (∑ a : Fin N, ∑ b : Fin N, x (i, (a, b)) * y (i, (a, b))) + gueSquareSum y i := by
  simp only [gueSquareSum, add_sq, Finset.sum_add_distrib]
  simp_rw [mul_assoc, ← Finset.mul_sum]

/-- Polarization identifies the unnormalized GUE trace product with the real coordinate
inner product. This is an algebraic identity for arbitrary coordinate vectors. -/
lemma trace_gueUnscaled_mul_coords (x y : GUECoord ι N → ℝ) (i : ι) :
    Matrix.trace (gueUnscaled x i * gueUnscaled y i) =
      ((∑ a : Fin N, ∑ b : Fin N, x (i, (a, b)) * y (i, (a, b))) : ℝ) := by
  have hadd : gueUnscaled (fun p => x p + y p) i = gueUnscaled x i + gueUnscaled y i := by
    ext a b
    simp only [gueUnscaled, Matrix.add_apply]
    push_cast
    ring
  have h := trace_gueUnscaled_mul_self (fun p => x p + y p) i
  rw [hadd] at h
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.trace_add,
    trace_gueUnscaled_mul_self] at h
  rw [Matrix.trace_mul_comm (gueUnscaled y i) (gueUnscaled x i)] at h
  rw [gueSquareSum_add] at h
  push_cast at h ⊢
  linear_combination h / 2

lemma trace_gueMatrix_mul_coords (x y : GUECoord ι N → ℝ) (i : ι) :
    Matrix.trace (gueMatrix x i * gueMatrix y i) =
      ((N : ℝ)⁻¹ : ℂ) *
        ((∑ a : Fin N, ∑ b : Fin N, x (i, (a, b)) * y (i, (a, b))) : ℝ) := by
  have hpt (a b : Fin N) : gueMatrix x i a b * gueMatrix y i b a =
      ((N : ℝ)⁻¹ : ℂ) * (gueUnscaled x i a b * gueUnscaled y i b a) := by
    simp only [gueMatrix]
    calc
      _ = ((gueScale N : ℂ) * (gueScale N : ℂ)) *
          (gueUnscaled x i a b * gueUnscaled y i b a) := by ring
      _ = _ := by rw [gueScale_mul_self_complex]
  calc
    _ = ∑ a : Fin N, ∑ b : Fin N, gueMatrix x i a b * gueMatrix y i b a := by
      simp [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    _ = ((N : ℝ)⁻¹ : ℂ) * Matrix.trace (gueUnscaled x i * gueUnscaled y i) := by
      simp_rw [hpt]
      simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.mul_sum]
    _ = _ := by rw [trace_gueUnscaled_mul_coords]

/-- Scalar coordinate expression for the real normalized mixed trace. -/
def gueNormalizedMixedTrace (x : GUECoord ι N → ℝ) (i j : ι) : ℝ :=
  (N : ℝ)⁻¹ ^ 2 * ∑ a : Fin N, ∑ b : Fin N, x (i, (a, b)) * x (j, (a, b))

lemma gueNormalizedMixedTrace_self (x : GUECoord ι N → ℝ) (i : ι) :
    gueNormalizedMixedTrace x i i = gueNormalizedSquareTrace x i := by
  simp only [gueNormalizedMixedTrace, gueNormalizedSquareTrace, gueSquareSum, pow_two]

/-- The actual ordered matrix product has the claimed real normalized trace. -/
lemma gueNormalizedMixedTrace_eq_matrix_trace (x : GUECoord ι N → ℝ) (i j : ι) :
    (gueNormalizedMixedTrace x i j : ℂ) =
      (N : ℂ)⁻¹ * Matrix.trace (gueMatrix x i * gueMatrix x j) := by
  have h := trace_gueMatrix_mul_coords x (fun p => x (j, p.2)) i
  have hy : gueMatrix (fun p : GUECoord ι N => x (j, p.2)) i = gueMatrix x j := rfl
  rw [hy] at h
  rw [h]
  simp [gueNormalizedMixedTrace, pow_two, mul_assoc]

lemma integral_gueNormalizedMixedTrace [Fintype ι] [DecidableEq ι]
    (i j : ι) (hN : 0 < N) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), gueNormalizedMixedTrace x i j
      ∂stdGaussian (EuclideanSpace ℝ (GUECoord ι N)) = if i = j then 1 else 0 := by
  have hInt (a b : Fin N) : Integrable
      (fun x : EuclideanSpace ℝ (GUECoord ι N) => x (i, (a, b)) * x (j, (a, b)))
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
    (memLp_coord (i, (a, b))).integrable_mul (memLp_coord (j, (a, b)))
  unfold gueNormalizedMixedTrace
  rw [integral_const_mul,
    integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hInt a b))]
  simp_rw [integral_finsetSum _ (fun b _ => hInt _ b)]
  simp only [integral_coord_mul_coord, Prod.mk.injEq, and_true]
  by_cases hij : i = j
  · simp only [hij, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
    field_simp
  · simp [hij]

end

end GUEStrongConvergence
