/-
# Variance of every two-letter normalized GUE trace

Wick's four-coordinate formula and the coordinate-inner-product representation of
`tr_N(G_i G_j)` give variance `N⁻²` for distinct labels, and `2N⁻²` for equal labels.
The bound includes dimension zero explicitly and is summable in dimension.
-/
import GUEStrongConvergence.Probability.QuadraticConvergence
import GUEStrongConvergence.Probability.MixedTrace

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace GUEStrongConvergence

noncomputable section

variable {ι : Type*} {N : ℕ} [Fintype ι] [DecidableEq ι]

/-- Coordinate inner product of the two matrix-label blocks. -/
def gueMixedCoordSum (x : GUECoord ι N → ℝ) (i j : ι) : ℝ :=
  ∑ p : Fin N × Fin N, x (i, p) * x (j, p)

omit [Fintype ι] [DecidableEq ι] in
lemma gueNormalizedMixedTrace_eq_coordSum (x : GUECoord ι N → ℝ) (i j : ι) :
    gueNormalizedMixedTrace x i j = (N : ℝ)⁻¹ ^ 2 * gueMixedCoordSum x i j := by
  simp [gueNormalizedMixedTrace, gueMixedCoordSum, Fintype.sum_prod_type]

omit [DecidableEq ι] in
lemma measurable_gueNormalizedMixedTrace (i j : ι) :
    Measurable (fun x : EuclideanSpace ℝ (GUECoord ι N) => gueNormalizedMixedTrace x i j) := by
  have h : Continuous (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      gueNormalizedMixedTrace x i j) := by
    unfold gueNormalizedMixedTrace
    fun_prop
  exact h.measurable

lemma integrable_gueMixedCoordSum_sq (i j : ι) :
    Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) => gueMixedCoordSum x i j ^ 2)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  have hInt (p q : Fin N × Fin N) : Integrable
      (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        (x (i, p) * x (j, p)) * (x (i, q) * x (j, q)))
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    have h := integrable_coordProd_stdGaussian [(i, p), (j, p), (i, q), (j, q)]
    refine h.congr (ae_of_all _ fun x => ?_)
    simp [coordProd]
    ring
  have h := integrable_finsetSum Finset.univ (fun p _ =>
    integrable_finsetSum Finset.univ (fun q _ => hInt p q))
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only [gueMixedCoordSum, pow_two]
  rw [Finset.sum_mul_sum]

lemma integral_gueMixedCoordSum_sq_of_ne (i j : ι) (hij : i ≠ j) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), gueMixedCoordSum x i j ^ 2
      ∂stdGaussian (EuclideanSpace ℝ (GUECoord ι N)) = (N : ℝ) ^ 2 := by
  have hInt (p q : Fin N × Fin N) : Integrable
      (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        (x (i, p) * x (j, p)) * (x (i, q) * x (j, q)))
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    have h := integrable_coordProd_stdGaussian [(i, p), (j, p), (i, q), (j, q)]
    refine h.congr (ae_of_all _ fun x => ?_)
    simp [coordProd]
    ring
  have hmom (p q : Fin N × Fin N) :
      (∫ x : EuclideanSpace ℝ (GUECoord ι N),
        (x (i, p) * x (j, p)) * (x (i, q) * x (j, q))
        ∂stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) = if p = q then 1 else 0 := by
    have h := integral_coord_four (i, p) (j, p) (i, q) (j, q)
    have hpt : ∀ x : EuclideanSpace ℝ (GUECoord ι N),
        (x (i, p) * x (j, p)) * (x (i, q) * x (j, q)) =
          x (i, p) * x (j, p) * x (i, q) * x (j, q) := by intro x; ring
    simp_rw [hpt]
    rw [h]
    by_cases hpq : p = q <;> simp [Prod.mk.injEq, hij, hpq]
  have hpt : ∀ x : EuclideanSpace ℝ (GUECoord ι N),
      gueMixedCoordSum x i j ^ 2 = ∑ p : Fin N × Fin N, ∑ q : Fin N × Fin N,
        (x (i, p) * x (j, p)) * (x (i, q) * x (j, q)) := by
    intro x
    simp only [gueMixedCoordSum, pow_two]
    rw [Finset.sum_mul_sum]
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ => hInt p q))]
  simp_rw [integral_finsetSum _ (fun q _ => hInt _ q), hmom]
  simp [Fintype.card_prod, pow_two]

lemma integrable_gueNormalizedMixedTrace_centered_sq (i j : ι) :
    Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      (gueNormalizedMixedTrace x i j - if i = j then 1 else 0) ^ 2)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  by_cases hij : i = j
  · subst j
    simpa only [ite_true, gueNormalizedMixedTrace_self] using
      integrable_gueNormalizedSquareTrace_centered_sq (N := N) i
  · have h := (integrable_gueMixedCoordSum_sq (N := N) i j).const_mul ((N : ℝ)⁻¹ ^ 4)
    refine h.congr (ae_of_all _ fun x => ?_)
    simp only [gueNormalizedMixedTrace_eq_coordSum, ite_eq_right hij, sub_zero]
    ring

/-- Exact centered second moment for every pair of labels, with dimension zero explicit. -/
theorem integral_gueNormalizedMixedTrace_centered_sq (i j : ι) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N),
      (gueNormalizedMixedTrace x i j - if i = j then 1 else 0) ^ 2
      ∂stdGaussian (EuclideanSpace ℝ (GUECoord ι N)) =
        if i = j then gueSquareTraceVarianceBound N else (N : ℝ)⁻¹ ^ 2 := by
  by_cases hij : i = j
  · subst j
    simpa only [ite_true, gueNormalizedMixedTrace_self, gueSquareTraceVarianceBound] using
      integral_gueNormalizedSquareTrace_centered_sq (N := N) i
  · simp only [ite_eq_right hij, sub_zero]
    have hpt : ∀ x : EuclideanSpace ℝ (GUECoord ι N),
        gueNormalizedMixedTrace x i j ^ 2 = (N : ℝ)⁻¹ ^ 4 * gueMixedCoordSum x i j ^ 2 := by
      intro x
      rw [gueNormalizedMixedTrace_eq_coordSum]
      ring
    simp_rw [hpt]
    rw [integral_const_mul, integral_gueMixedCoordSum_sq_of_ne i j hij]
    by_cases hN : (N : ℝ) = 0
    · simp [hN]
    · field_simp

lemma integral_gueNormalizedMixedTrace_centered_sq_le (i j : ι) :
    (∫ x : EuclideanSpace ℝ (GUECoord ι N),
      (gueNormalizedMixedTrace x i j - if i = j then 1 else 0) ^ 2
      ∂stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) ≤ gueSquareTraceVarianceBound N := by
  rw [integral_gueNormalizedMixedTrace_centered_sq]
  by_cases hij : i = j
  · simp [hij]
  · simp only [ite_eq_right hij, gueSquareTraceVarianceBound]
    by_cases hN : N = 0
    · simp [hN]
    · rw [ite_eq_right hN]
      nlinarith [sq_nonneg ((N : ℝ)⁻¹)]

end

end GUEStrongConvergence
