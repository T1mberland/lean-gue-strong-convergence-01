/-
# Exact second moment of a finite sum of Gaussian squares

For `m` distinct standard Gaussian coordinates, `E[(∑ x_p²)²] = m² + 2m`.
This follows from the verified two-coordinate fourth moment, with no assumed
independence or covariance bound in the theorem statement.
-/
import GUEStrongConvergence.Probability.GaussianWick
import GUEStrongConvergence.Probability.QuadraticTrace

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace GUEStrongConvergence

noncomputable section

variable {κ τ : Type*} [Fintype κ] [DecidableEq κ] [Fintype τ]

lemma integrable_sum_coord_sq_sq (f : τ → κ) :
    Integrable (fun x : EuclideanSpace ℝ κ => (∑ a : τ, x (f a) ^ 2) ^ 2)
      (stdGaussian (EuclideanSpace ℝ κ)) := by
  have hInt (a b : τ) : Integrable
      (fun x : EuclideanSpace ℝ κ => x (f a) ^ 2 * x (f b) ^ 2)
      (stdGaussian (EuclideanSpace ℝ κ)) := by
    simpa only [pow_two] using integrable_coord_sq_mul_coord_sq (f a) (f b)
  have h := integrable_finsetSum Finset.univ (fun a _ =>
    integrable_finsetSum Finset.univ (fun b _ => hInt a b))
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only [pow_two]
  rw [Finset.sum_mul_sum]

/-- Exact second moment for a sum of squares of distinct Gaussian coordinates. -/
theorem integral_sum_coord_sq_sq [DecidableEq τ] (f : τ → κ) (hf : Function.Injective f) :
    ∫ x : EuclideanSpace ℝ κ, (∑ a : τ, x (f a) ^ 2) ^ 2
      ∂stdGaussian (EuclideanSpace ℝ κ) =
        (Fintype.card τ : ℝ) ^ 2 + 2 * Fintype.card τ := by
  have hInt (a b : τ) : Integrable
      (fun x : EuclideanSpace ℝ κ => x (f a) ^ 2 * x (f b) ^ 2)
      (stdGaussian (EuclideanSpace ℝ κ)) := by
    simpa only [pow_two] using integrable_coord_sq_mul_coord_sq (f a) (f b)
  have hpt : ∀ x : EuclideanSpace ℝ κ,
      (∑ a : τ, x (f a) ^ 2) ^ 2 = ∑ a : τ, ∑ b : τ, x (f a) ^ 2 * x (f b) ^ 2 := by
    intro x
    rw [pow_two, Finset.sum_mul_sum]
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hInt a b))]
  simp_rw [integral_finsetSum _ (fun b _ => hInt _ b)]
  simp only [pow_two, integral_coord_sq_mul_coord_sq, hf.eq_iff]
  have hite (a b : τ) : (if a = b then (3:ℝ) else 1) = 1 + if a = b then 2 else 0 := by
    split_ifs <;> norm_num
  simp_rw [hite, Finset.sum_add_distrib]
  simp
  ring

variable {ι : Type*} {N : ℕ} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma gueSquareSum_eq_sum_prod (x : GUECoord ι N → ℝ) (i : ι) :
    gueSquareSum x i = ∑ p : Fin N × Fin N, x (i, p) ^ 2 := by
  simp [gueSquareSum, Fintype.sum_prod_type]

lemma integrable_gueSquareSum_sq (i : ι) :
    Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) => gueSquareSum x i ^ 2)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  simpa only [gueSquareSum_eq_sum_prod] using
    integrable_sum_coord_sq_sq (κ := GUECoord ι N) (fun p : Fin N × Fin N => (i, p))

lemma integral_gueSquareSum_sq (i : ι) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), gueSquareSum x i ^ 2
      ∂stdGaussian (EuclideanSpace ℝ (GUECoord ι N)) = (N : ℝ) ^ 4 + 2 * (N : ℝ) ^ 2 := by
  have hf : Function.Injective (fun p : Fin N × Fin N => (i, p)) := by
    intro p q h
    exact (Prod.mk.inj h).2
  have h := integral_sum_coord_sq_sq (κ := GUECoord ι N) _ hf
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] at h
  simp_rw [gueSquareSum_eq_sum_prod]
  rw [h]
  ring

lemma integrable_gueNormalizedSquareTrace_centered_sq (i : ι) :
    Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      (gueNormalizedSquareTrace x i - 1) ^ 2)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  have hS2 := (integrable_gueSquareSum_sq (N := N) i).const_mul ((N : ℝ)⁻¹ ^ 4)
  have hS := (integrable_gueSquareSum (N := N) i).const_mul (2 * (N : ℝ)⁻¹ ^ 2)
  have h := (hS2.sub hS).add (integrable_const (1:ℝ))
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only [gueNormalizedSquareTrace, Pi.add_apply, Pi.sub_apply]
  ring

/-- Exact centered second moment of the normalized trace of `G²`.
The exceptional dimension zero is included explicitly rather than silently excluded. -/
theorem integral_gueNormalizedSquareTrace_centered_sq (i : ι) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), (gueNormalizedSquareTrace x i - 1) ^ 2
      ∂stdGaussian (EuclideanSpace ℝ (GUECoord ι N)) =
        if N = 0 then 1 else 2 * (N : ℝ)⁻¹ ^ 2 := by
  by_cases hN : N = 0
  · subst N
    simp [gueNormalizedSquareTrace]
  · rw [ite_eq_right hN]
    have hS2 := (integrable_gueSquareSum_sq (N := N) i).const_mul ((N : ℝ)⁻¹ ^ 4)
    have hS := (integrable_gueSquareSum (N := N) i).const_mul (2 * (N : ℝ)⁻¹ ^ 2)
    have hpt : ∀ x : EuclideanSpace ℝ (GUECoord ι N),
        (gueNormalizedSquareTrace x i - 1) ^ 2 =
          ((N : ℝ)⁻¹ ^ 4 * gueSquareSum x i ^ 2 -
            (2 * (N : ℝ)⁻¹ ^ 2) * gueSquareSum x i) + 1 := by
      intro x
      simp only [gueNormalizedSquareTrace]
      ring
    have hSub : Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        (N : ℝ)⁻¹ ^ 4 * gueSquareSum x i ^ 2 -
          (2 * (N : ℝ)⁻¹ ^ 2) * gueSquareSum x i)
        (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := hS2.sub hS
    simp_rw [hpt]
    rw [integral_add hSub (integrable_const _), integral_sub hS2 hS,
      integral_const_mul, integral_const_mul, integral_gueSquareSum_sq, integral_gueSquareSum]
    simp only [integral_const, MeasureTheory.probReal_univ, smul_eq_mul, one_mul]
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    field_simp
    <;> ring

end

end GUEStrongConvergence
