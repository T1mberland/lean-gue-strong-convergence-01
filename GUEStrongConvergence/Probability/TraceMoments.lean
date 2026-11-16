/-
# First normalized trace moment of the concrete GUE

The normalized trace is real because the diagonal coordinates are real.  We compute
its mean and its exact second moment, including the harmless zero-dimensional case.
These estimates are the first input to almost-sure moment convergence.
-/
import GUEStrongConvergence.Probability.GUEModel

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace GUEStrongConvergence

noncomputable section

variable {ι : Type*} {N : ℕ}

/-- Sum of the diagonal real Gaussian coordinates for one matrix label. -/
def gueDiagonalSum (x : GUECoord ι N → ℝ) (i : ι) : ℝ :=
  ∑ a : Fin N, x (i, (a, a))

/-- Real normalized trace of a normalized GUE matrix. At dimension zero this is zero. -/
def gueNormalizedTrace (x : GUECoord ι N → ℝ) (i : ι) : ℝ :=
  (N : ℝ)⁻¹ * gueScale N * gueDiagonalSum x i

lemma gueNormalizedTrace_eq_matrix_trace (x : GUECoord ι N → ℝ) (i : ι) :
    (gueNormalizedTrace x i : ℂ) = (N : ℂ)⁻¹ * Matrix.trace (gueMatrix x i) := by
  simp [gueNormalizedTrace, gueDiagonalSum, Matrix.trace, Matrix.diag, gueMatrix_diag,
    Finset.mul_sum, Complex.ofReal_sum, Complex.ofReal_mul, mul_assoc]

lemma measurable_gueNormalizedTrace [Fintype ι] (i : ι) :
    Measurable (fun x : EuclideanSpace ℝ (GUECoord ι N) => gueNormalizedTrace x i) := by
  have h : Continuous (fun x : EuclideanSpace ℝ (GUECoord ι N) => gueNormalizedTrace x i) := by
    unfold gueNormalizedTrace gueDiagonalSum
    fun_prop
  exact h.measurable

lemma integral_gaussian_coord {κ : Type*} [Fintype κ] (p : κ) :
    ∫ x : EuclideanSpace ℝ κ, x p ∂stdGaussian (EuclideanSpace ℝ κ) = 0 := by
  simpa [EuclideanSpace.basisFun_inner] using
    (integral_strongDual_stdGaussian (innerSL ℝ (EuclideanSpace.basisFun κ ℝ p)))

lemma memLp_gueDiagonalSum [Fintype ι] (i : ι) :
    MemLp (fun x : EuclideanSpace ℝ (GUECoord ι N) => gueDiagonalSum x i) 2
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  exact memLp_finsetSum _ (fun a _ => memLp_coord (i, (a, a)))

lemma memLp_gueNormalizedTrace [Fintype ι] (i : ι) :
    MemLp (fun x : EuclideanSpace ℝ (GUECoord ι N) => gueNormalizedTrace x i) 2
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
  (memLp_gueDiagonalSum i).const_mul _

lemma integral_gueDiagonalSum [Fintype ι] (i : ι) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), gueDiagonalSum x i
      ∂stdGaussian (EuclideanSpace ℝ (GUECoord ι N)) = 0 := by
  unfold gueDiagonalSum
  rw [integral_finsetSum _ (fun a _ => (memLp_coord (i, (a, a))).integrable (by norm_num))]
  simp [integral_gaussian_coord]

/-- The normalized GUE trace is centered. -/
theorem integral_gueNormalizedTrace [Fintype ι] (i : ι) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), gueNormalizedTrace x i
      ∂stdGaussian (EuclideanSpace ℝ (GUECoord ι N)) = 0 := by
  simp [gueNormalizedTrace, integral_const_mul, integral_gueDiagonalSum]

lemma integrable_gueDiagonalSum_mul [Fintype ι] (i j : ι) :
    Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      gueDiagonalSum x i * gueDiagonalSum x j)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
  (memLp_gueDiagonalSum i).integrable_mul (memLp_gueDiagonalSum j)

lemma integral_gueDiagonalSum_mul [Fintype ι] [DecidableEq ι] (i j : ι) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), gueDiagonalSum x i * gueDiagonalSum x j
      ∂stdGaussian (EuclideanSpace ℝ (GUECoord ι N)) =
        if i = j then (N : ℝ) else 0 := by
  have hInt (a b : Fin N) : Integrable
      (fun x : EuclideanSpace ℝ (GUECoord ι N) => x (i, (a, a)) * x (j, (b, b)))
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
    (memLp_coord (i, (a, a))).integrable_mul (memLp_coord (j, (b, b)))
  simp only [gueDiagonalSum]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hInt a b))]
  simp_rw [integral_finsetSum _ (fun b _ => hInt _ b)]
  simp only [integral_coord_mul_coord, Prod.mk.injEq, and_self]
  by_cases h : i = j
  · subst j
    simp
  · simp [h]

/-- Exact covariance of the real normalized traces. The diagonal value is `N⁻²`.
No assertion of asymptotic convergence is assumed in this computation. -/
theorem integral_gueNormalizedTrace_mul [Fintype ι] [DecidableEq ι] (i j : ι) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N),
      gueNormalizedTrace x i * gueNormalizedTrace x j
      ∂stdGaussian (EuclideanSpace ℝ (GUECoord ι N)) =
        if i = j then ((N : ℝ)⁻¹) ^ 2 else 0 := by
  have hpt : ∀ x : EuclideanSpace ℝ (GUECoord ι N),
      gueNormalizedTrace x i * gueNormalizedTrace x j =
        ((N : ℝ)⁻¹ ^ 2 * gueScale N ^ 2) * (gueDiagonalSum x i * gueDiagonalSum x j) := by
    intro x
    unfold gueNormalizedTrace
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_gueDiagonalSum_mul, gueScale_sq]
  split_ifs
  · by_cases hN : (N : ℝ) = 0
    · simp [hN]
    · field_simp
  · ring

/-- Exact second moment, the summable `N⁻²` estimate needed for the first word moment. -/
theorem integral_gueNormalizedTrace_sq [Fintype ι] [DecidableEq ι] (i : ι) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), (gueNormalizedTrace x i) ^ 2
      ∂stdGaussian (EuclideanSpace ℝ (GUECoord ι N)) = ((N : ℝ)⁻¹) ^ 2 := by
  simpa only [pow_two, ite_true] using integral_gueNormalizedTrace_mul (N := N) i i

/-- The square of the normalized trace is integrable. -/
lemma integrable_gueNormalizedTrace_sq [Fintype ι] (i : ι) :
    Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) => (gueNormalizedTrace x i) ^ 2)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  have h : Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      gueNormalizedTrace x i * gueNormalizedTrace x i)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
    (memLp_gueNormalizedTrace (N := N) i).integrable_mul (memLp_gueNormalizedTrace i)
  exact h.congr (ae_of_all _ fun x => (pow_two (gueNormalizedTrace x i)).symm)

/-- A dimension-explicit Chebyshev bound for the normalized trace. -/
theorem measure_gueNormalizedTrace_deviation_le [Fintype ι] [DecidableEq ι]
    (i : ι) {ε : ℝ} (hε : 0 < ε) :
    stdGaussian (EuclideanSpace ℝ (GUECoord ι N))
      {x | ε ≤ |gueNormalizedTrace x i|} ≤
        ENNReal.ofReal (ε⁻¹ ^ 2 * (N : ℝ)⁻¹ ^ 2) := by
  have hInt := (integrable_gueNormalizedTrace_sq (N := N) i).const_mul (ε⁻¹ ^ 2)
  have h := hInt.measure_le_integral
    (ae_of_all _ (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
    (s := {x | ε ≤ |gueNormalizedTrace x i|}) ?_
  · simpa only [integral_const_mul, integral_gueNormalizedTrace_sq] using h
  · intro x hx
    change ε ≤ |gueNormalizedTrace x i| at hx
    have hs : ε ^ 2 ≤ (gueNormalizedTrace x i) ^ 2 := by
      nlinarith [sq_abs (gueNormalizedTrace x i), abs_nonneg (gueNormalizedTrace x i)]
    have he : ε ≠ 0 := ne_of_gt hε
    calc
      1 = ε⁻¹ ^ 2 * ε ^ 2 := by field_simp
      _ ≤ ε⁻¹ ^ 2 * (gueNormalizedTrace x i) ^ 2 :=
        mul_le_mul_of_nonneg_left hs (sq_nonneg _)

end

end GUEStrongConvergence
