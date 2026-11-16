/-
# The second normalized GUE trace as an empirical Gaussian square sum

The identity `tr_N(G²) = N⁻² ∑_{a,b} x_{ab}²` exposes the elementary Gaussian
law behind the second word moment, with the correct operator-matrix multiplication
and the existing complex GUE normalization. No spectral or convergence conclusion
is assumed.
-/
import GUEStrongConvergence.Probability.GUEModel

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace GUEStrongConvergence

noncomputable section

variable {ι : Type*} {N : ℕ}

/-- Sum of the `N²` squared real Gaussian coordinates belonging to one matrix. -/
def gueSquareSum (x : GUECoord ι N → ℝ) (i : ι) : ℝ :=
  ∑ a : Fin N, ∑ b : Fin N, (x (i, (a, b))) ^ 2

/-- Real normalized trace of the square of a normalized GUE matrix. -/
def gueNormalizedSquareTrace (x : GUECoord ι N → ℝ) (i : ι) : ℝ :=
  (N : ℝ)⁻¹ ^ 2 * gueSquareSum x i

lemma gueUnscaled_mul_swap (x : GUECoord ι N → ℝ) (i : ι) (a b : Fin N) :
    gueUnscaled x i a b * gueUnscaled x i b a =
      (((x (i, (a, b)) : ℝ) : ℂ) ^ 2 + (((x (i, (b, a)) : ℝ) : ℂ)) ^ 2) / 2 := by
  calc
    _ = (gueAlpha * gueBeta) *
          ((((x (i, (a, b)) : ℝ) : ℂ)) ^ 2 + (((x (i, (b, a)) : ℝ) : ℂ)) ^ 2) +
        (gueAlpha * gueAlpha + gueBeta * gueBeta) *
          (((x (i, (a, b)) : ℝ) : ℂ) * ((x (i, (b, a)) : ℝ) : ℂ)) := by
      unfold gueUnscaled
      ring
    _ = _ := by rw [gueAlpha_mul_gueBeta, gueAlpha_mul_self_add_gueBeta_mul_self]; ring

lemma trace_gueUnscaled_mul_self (x : GUECoord ι N → ℝ) (i : ι) :
    Matrix.trace (gueUnscaled x i * gueUnscaled x i) = (gueSquareSum x i : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, gueUnscaled_mul_swap]
  simp only [add_div, Finset.sum_add_distrib]
  have hswap : (∑ a : Fin N, ∑ b : Fin N, (((x (i, (b, a)) : ℝ) : ℂ)) ^ 2 / 2) =
      ∑ a : Fin N, ∑ b : Fin N, (((x (i, (a, b)) : ℝ) : ℂ)) ^ 2 / 2 :=
    Finset.sum_comm
  rw [hswap]
  simp only [gueSquareSum, Complex.ofReal_sum, Complex.ofReal_pow]
  simp_rw [← Finset.sum_div]
  ring

lemma trace_gueMatrix_mul_self (x : GUECoord ι N → ℝ) (i : ι) :
    Matrix.trace (gueMatrix x i * gueMatrix x i) =
      ((N : ℝ)⁻¹ : ℂ) * (gueSquareSum x i : ℂ) := by
  have hpt (a b : Fin N) : gueMatrix x i a b * gueMatrix x i b a =
      ((N : ℝ)⁻¹ : ℂ) * (gueUnscaled x i a b * gueUnscaled x i b a) := by
    simp only [gueMatrix]
    calc
      _ = ((gueScale N : ℂ) * (gueScale N : ℂ)) *
          (gueUnscaled x i a b * gueUnscaled x i b a) := by ring
      _ = _ := by rw [gueScale_mul_self_complex]
  calc
    _ = ∑ a : Fin N, ∑ b : Fin N, gueMatrix x i a b * gueMatrix x i b a := by
      simp [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    _ = ((N : ℝ)⁻¹ : ℂ) * Matrix.trace (gueUnscaled x i * gueUnscaled x i) := by
      simp_rw [hpt]
      simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.mul_sum]
    _ = _ := by rw [trace_gueUnscaled_mul_self]

lemma gueNormalizedSquareTrace_eq_matrix_trace (x : GUECoord ι N → ℝ) (i : ι) :
    (gueNormalizedSquareTrace x i : ℂ) =
      (N : ℂ)⁻¹ * Matrix.trace (gueMatrix x i * gueMatrix x i) := by
  rw [trace_gueMatrix_mul_self]
  simp [gueNormalizedSquareTrace, pow_two, mul_assoc]

lemma measurable_gueNormalizedSquareTrace [Fintype ι] (i : ι) :
    Measurable (fun x : EuclideanSpace ℝ (GUECoord ι N) => gueNormalizedSquareTrace x i) := by
  have h : Continuous (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      gueNormalizedSquareTrace x i) := by
    unfold gueNormalizedSquareTrace gueSquareSum
    fun_prop
  exact h.measurable

lemma integrable_gueSquareSum [Fintype ι] (i : ι) :
    Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) => gueSquareSum x i)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  apply integrable_finsetSum
  intro a _
  apply integrable_finsetSum
  intro b _
  have h : Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      x (i, (a, b)) * x (i, (a, b)))
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
    (memLp_coord (i, (a, b))).integrable_mul (memLp_coord (i, (a, b)))
  exact h.congr (ae_of_all _ fun x => (pow_two _).symm)

lemma integral_gueSquareSum [Fintype ι] [DecidableEq ι] (i : ι) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), gueSquareSum x i
      ∂stdGaussian (EuclideanSpace ℝ (GUECoord ι N)) = (N : ℝ) ^ 2 := by
  have hInt (a b : Fin N) : Integrable
      (fun x : EuclideanSpace ℝ (GUECoord ι N) => x (i, (a, b)) ^ 2)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    have h : Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        x (i, (a, b)) * x (i, (a, b)))
        (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
      (memLp_coord (i, (a, b))).integrable_mul (memLp_coord (i, (a, b)))
    exact h.congr (ae_of_all _ fun x => (pow_two _).symm)
  unfold gueSquareSum
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hInt a b))]
  simp_rw [integral_finsetSum _ (fun b _ => hInt _ b)]
  simp only [pow_two, integral_coord_mul_coord, ite_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- Exact expectation of the second normalized word moment. -/
theorem integral_gueNormalizedSquareTrace [Fintype ι] [DecidableEq ι] (i : ι) (hN : 0 < N) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), gueNormalizedSquareTrace x i
      ∂stdGaussian (EuclideanSpace ℝ (GUECoord ι N)) = 1 := by
  simp only [gueNormalizedSquareTrace, integral_const_mul, integral_gueSquareSum]
  have h : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  field_simp

end

end GUEStrongConvergence
