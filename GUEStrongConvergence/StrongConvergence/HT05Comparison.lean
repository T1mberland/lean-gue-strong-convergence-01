/-
# HT05 comparison of the finite-`N` mean with the free matrix-argument Cauchy transform

This file contains the analytic core of the HT05 good/bad region comparison
(Haagerup--Thorbjørnsen 2005, Theorem 5.7, eqs. (5.21)--(5.24)).

## Contents

1. **Exact resolvent identity for the matrix-argument Cauchy transform.**  For a coefficient
   family `C : I → Matrix d d ℂ` and two deterministic matrix arguments `B₁ B₂ : Matrix d d ℂ`
   at which the operator difference is invertible,
   `operatorMatrixArgumentResolvent C B₁ - operatorMatrixArgumentResolvent C B₂
      = operatorMatrixArgumentResolvent C B₂ * scalarMatrixEmbedding (B₂ - B₁)
        * operatorMatrixArgumentResolvent C B₁`
   (the operator identity `A₁⁻¹ - A₂⁻¹ = A₂⁻¹ (A₂ - A₁) A₁⁻¹`), together with the difference
   identity `operatorMatrixDifference C B₁ - operatorMatrixDifference C B₂
      = scalarMatrixEmbedding (B₁ - B₂)`.
   Averaging with `matrixExpectation` and using that scalar matrix coefficients pass through
   the entrywise expectation, this gives the **exact matrix identity**
   `operatorMatrixArgumentCauchy C B₁ - operatorMatrixArgumentCauchy C B₂
      = operatorMatrixArgumentCauchy C B₂ * (B₂ - B₁) * operatorMatrixArgumentCauchy C B₁`.

2. **The Frobenius comparison bound.**  From the exact identity and the entrywise resolvent
   bound `‖operatorMatrixArgumentResolvent C B‖ ≤ η⁻¹` one gets
   `frob (operatorMatrixArgumentCauchy C B₁ - operatorMatrixArgumentCauchy C B₂)
      ≤ (card d)² * frob (B₁ - B₂) * η₂⁻¹ * η₁⁻¹`.

3. **The pencil identification** `operatorMatrixPencilCauchy C₀ C z
   = operatorMatrixArgumentCauchy C (z • 1 - C₀)` is the dependency's
   `operatorMatrixArgumentCauchy_pencil`; the resolvent norm bound at pencil arguments is
   Mathlib's `norm_resolvent_le_inv_abs_im` transported through `operatorMatrixDifference_pencil`.

Everything is stated with *explicit* hypotheses; the comparison lemmas of the second part take
the finite-`N` mean identification (Worker B) and the self-energy bound (Worker A) as explicit
hypotheses so that integration is a pure substitution.

No `sorry`, no new axioms.
-/
import GUEStrongConvergence.Probability.DysonLimit
import GUEStrongConvergence.Analysis.ResolventBounds
import GUEStrongConvergence.StrongConvergence.WeightedStripRepair
import GUEStrongConvergence.Probability.ResolventConj

open MeasureTheory ProbabilityTheory Matrix Filter
open FreeProbability FreeProbability.Fock
open scoped ComplexOrder ENNReal NNReal Topology

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace FreeProbability.Fock

variable {I d : Type*} [Fintype I] [Fintype d] [DecidableEq d]

/-! ## 1. The exact resolvent identity at the operator level -/

/-- **Difference of the operator arguments.**  The operator matrix pencil differences at two
deterministic matrix arguments differ by the embedded difference of the arguments. -/
theorem operatorMatrixDifference_sub (C : I → Matrix d d ℂ) (B₁ B₂ : Matrix d d ℂ) :
    operatorMatrixDifference C B₁ - operatorMatrixDifference C B₂ =
      scalarMatrixEmbedding (B₁ - B₂) := by
  unfold operatorMatrixDifference
  have key : (scalarMatrixEmbedding B₁ - matrixLinearCombination semicircular C) -
      (scalarMatrixEmbedding B₂ - matrixLinearCombination semicircular C) =
      scalarMatrixEmbedding (B₁ - B₂) := by
    rw [map_sub]
    abel
  change CStarMatrix.ofMatrix
      ((scalarMatrixEmbedding B₁ - matrixLinearCombination semicircular C) -
        (scalarMatrixEmbedding B₂ - matrixLinearCombination semicircular C)) =
    CStarMatrix.ofMatrix (scalarMatrixEmbedding (B₁ - B₂))
  rw [key]

/-- **The second resolvent identity for the matrix-argument resolvent**
`A₁⁻¹ - A₂⁻¹ = A₂⁻¹ (A₂ - A₁) A₁⁻¹`. -/
theorem operatorMatrixArgumentResolvent_sub (C : I → Matrix d d ℂ) (B₁ B₂ : Matrix d d ℂ)
    (h₁ : IsUnit (operatorMatrixDifference C B₁))
    (h₂ : IsUnit (operatorMatrixDifference C B₂)) :
    operatorMatrixArgumentResolvent C B₁ - operatorMatrixArgumentResolvent C B₂ =
      operatorMatrixArgumentResolvent C B₂ * scalarMatrixEmbedding (B₂ - B₁) *
        operatorMatrixArgumentResolvent C B₁ := by
  have hD : operatorMatrixDifference C B₂ - operatorMatrixDifference C B₁ =
      scalarMatrixEmbedding (B₂ - B₁) := operatorMatrixDifference_sub C B₂ B₁
  unfold operatorMatrixArgumentResolvent
  rw [← hD]
  have e₂ : Ring.inverse (operatorMatrixDifference C B₂) * operatorMatrixDifference C B₂ = 1 :=
    Ring.inverse_mul_cancel _ h₂
  have e₁ : operatorMatrixDifference C B₁ * Ring.inverse (operatorMatrixDifference C B₁) = 1 :=
    Ring.mul_inverse_cancel _ h₁
  have key : Ring.inverse (operatorMatrixDifference C B₁) -
      Ring.inverse (operatorMatrixDifference C B₂) =
      Ring.inverse (operatorMatrixDifference C B₂) *
        (operatorMatrixDifference C B₂ - operatorMatrixDifference C B₁) *
        Ring.inverse (operatorMatrixDifference C B₁) := by
    symm
    rw [mul_sub, sub_mul, e₂, one_mul, mul_assoc, e₁, mul_one]
  exact key

end FreeProbability.Fock

namespace GUEStrongConvergence

variable {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d] [DecidableEq ι] {N : ℕ}

open FreeProbability.Fock
open WithCStarModule
open scoped InnerProductSpace

noncomputable local instance ht05CPartialOrder : PartialOrder (WordSpace ι →L[ℂ] WordSpace ι) :=
  CStarAlgebra.spectralOrder _
noncomputable local instance ht05CStarOrderedRing : StarOrderedRing (WordSpace ι →L[ℂ] WordSpace ι) :=
  CStarAlgebra.spectralOrderedRing _

/-! ## 2. Norm bounds for the matrix-argument Cauchy transform -/

/-- **Frobenius norm of an entrywise expectation.**  The Frobenius norm of
`matrixExpectation φ X` is bounded by `card d` times the operator norm of `X`. -/
theorem frob_matrixExpectation_le (X : Matrix d d (WordSpace ι →L[ℂ] WordSpace ι)) :
    frob (matrixExpectation (vacuumState ι).toProbabilitySpace X) ≤
      (Fintype.card d : ℝ) * ‖CStarMatrix.ofMatrix X‖ := by
  refine frob_le_card_mul_of_entry_le _ (fun u v => ?_) (by positivity)
  rw [matrixExpectation_apply]
  exact (norm_vacuumExpectation_le (X u v)).trans
    (CStarMatrix.norm_entry_le_norm (M := CStarMatrix.ofMatrix X) (i := u) (j := v))

/-- The operator norm of a `C⋆`-matrix is bounded by the sum of the norms of its entries. -/
theorem cstarMatrix_norm_le_sum_entries
    {M : CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι)} :
    ‖M‖ ≤ ∑ j, ∑ i, ‖M i j‖ := by
  rw [CStarMatrix.norm_def]
  refine (CStarMatrix.toCLM M).opNorm_le_bound (by positivity) fun v => ?_
  calc ‖CStarMatrix.toCLM M v‖ ≤ ∑ x, ‖(CStarMatrix.toCLM M v) x‖ := pi_norm_le_sum_norm _
    _ = ∑ x, ‖∑ i, v i * M i x‖ := by simp [CStarMatrix.toCLM_apply_eq_sum]
    _ ≤ ∑ x, ∑ i, ‖v i‖ * ‖M i x‖ := by
        refine Finset.sum_le_sum fun x _ => ?_
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        exact norm_mul_le _ _
    _ ≤ ∑ x, ∑ i, ‖v‖ * ‖M i x‖ := by
        refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun i _ => ?_
        exact mul_le_mul_of_nonneg_right (norm_apply_le_norm v i) (norm_nonneg _)
    _ = (∑ j, ∑ i, ‖M i j‖) * ‖v‖ := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The sum of the absolute values of the entries of a complex matrix is bounded by
`card d` times its Frobenius norm. -/
theorem sum_norm_entries_le_card_mul_frob (M : Matrix d d ℂ) :
    ∑ j, ∑ i, ‖M i j‖ ≤ (Fintype.card d : ℝ) * frob M := by
  have hsum_eq : (∑ p : d × d, ‖M p.2 p.1‖) = ∑ j, ∑ i, ‖M i j‖ := by
    rw [Fintype.sum_prod_type]
  have hsq_eq : (∑ p : d × d, ‖M p.2 p.1‖ ^ 2) = (frob M) ^ 2 := by
    rw [frob_sq, Fintype.sum_prod_type, Finset.sum_comm]
  have hcard : (∑ _ : d × d, (1 : ℝ)) = (Fintype.card d : ℝ) ^ 2 := by
    simp [Finset.sum_const, Fintype.card_prod]
    ring
  suffices h : (∑ p : d × d, ‖M p.2 p.1‖) ≤ (Fintype.card d : ℝ) * frob M by
    rwa [hsum_eq] at h
  have key : (∑ p : d × d, ‖M p.2 p.1‖) ^ 2 ≤
      (Fintype.card d : ℝ) ^ 2 * (frob M) ^ 2 := by
    have hle := Finset.sum_mul_sq_le_sq_mul_sq (s := (Finset.univ : Finset (d × d)))
      (f := fun _ : d × d => (1 : ℝ)) (g := fun p : d × d => ‖M p.2 p.1‖)
    simpa only [one_mul, one_pow, hcard, hsq_eq] using hle
  have hS0 : 0 ≤ ∑ p : d × d, ‖M p.2 p.1‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h2 : ∑ p : d × d, ‖M p.2 p.1‖ ≤
      Real.sqrt ((Fintype.card d : ℝ) ^ 2 * (frob M) ^ 2) := by
    rw [← Real.sqrt_sq hS0]
    exact Real.sqrt_le_sqrt key
  rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity),
    Real.sqrt_sq (frob_nonneg M)] at h2

/-- The unit of the coefficient algebra has norm at most one (it is `0` for the degenerate
zero algebra and `1` otherwise). -/
theorem cstar_norm_one_le_one :
    ‖(1 : WordSpace ι →L[ℂ] WordSpace ι)‖ ≤ 1 := by
  have h : ‖(1 : WordSpace ι →L[ℂ] WordSpace ι)‖ =
      ‖(1 : WordSpace ι →L[ℂ] WordSpace ι)‖ * ‖(1 : WordSpace ι →L[ℂ] WordSpace ι)‖ := by
    rw [← CStarRing.norm_star_mul_self (x := (1 : WordSpace ι →L[ℂ] WordSpace ι)),
      star_one, one_mul]
  nlinarith [norm_nonneg (1 : WordSpace ι →L[ℂ] WordSpace ι)]

/-- **The embedded difference of the matrix arguments, in the operator norm**, is bounded by
`card d` times the Frobenius norm of the difference. -/
theorem norm_scalarMatrixEmbedding_le_card_mul_frob (D : Matrix d d ℂ) :
    ‖CStarMatrix.ofMatrix (scalarMatrixEmbedding (A := WordSpace ι →L[ℂ] WordSpace ι) D)‖ ≤
      (Fintype.card d : ℝ) * frob D := by
  refine (cstarMatrix_norm_le_sum_entries (M :=
    CStarMatrix.ofMatrix (scalarMatrixEmbedding (A := WordSpace ι →L[ℂ] WordSpace ι) D))).trans ?_
  have hentry : ∀ i j : d,
      ‖(CStarMatrix.ofMatrix (scalarMatrixEmbedding (A := WordSpace ι →L[ℂ] WordSpace ι) D)) i j‖
        ≤ ‖D i j‖ := by
    intro i j
    change ‖scalarMatrixEmbedding (A := WordSpace ι →L[ℂ] WordSpace ι) D i j‖ ≤ ‖D i j‖
    rw [scalarMatrixEmbedding_apply, norm_algebraMap]
    exact mul_le_of_le_one_right (norm_nonneg _) cstar_norm_one_le_one
  refine (Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => hentry i j).trans ?_
  exact sum_norm_entries_le_card_mul_frob D

/-- Negation preserves the Frobenius norm. -/
theorem frob_neg (M : Matrix d d ℂ) : frob (-M) = frob M := by
  have h : (frob (-M)) ^ 2 = (frob M) ^ 2 := by
    rw [frob_sq, frob_sq]
    simp only [Matrix.neg_apply, norm_neg]
  nlinarith [frob_nonneg M, frob_nonneg (-M)]

/-- **Frobenius bound for the difference of two matrix-argument Cauchy transforms.**

The resolvent identity `A₁⁻¹ - A₂⁻¹ = A₂⁻¹ (A₂ - A₁) A₁⁻¹` together with the contractivity of
the vacuum expectation and the entrywise bound on the operator norm gives
`frob (C(B₁) - C(B₂)) ≤ (card d)² frob(B₁ - B₂) ‖res B₂‖ ‖res B₁‖`. -/
theorem frob_operatorMatrixArgumentCauchy_sub_le (C : ι → Matrix d d ℂ)
    (B₁ B₂ : Matrix d d ℂ)
    (h₁ : IsUnit (operatorMatrixDifference C B₁))
    (h₂ : IsUnit (operatorMatrixDifference C B₂))
    {η₁ η₂ : ℝ} (hη₁ : 0 < η₁) (hη₂ : 0 < η₂)
    (hn₁ : ‖CStarMatrix.ofMatrix (operatorMatrixArgumentResolvent C B₁)‖ ≤ η₁⁻¹)
    (hn₂ : ‖CStarMatrix.ofMatrix (operatorMatrixArgumentResolvent C B₂)‖ ≤ η₂⁻¹) :
    frob (operatorMatrixArgumentCauchy C B₁ - operatorMatrixArgumentCauchy C B₂) ≤
      (Fintype.card d : ℝ) ^ 2 * frob (B₁ - B₂) * η₂⁻¹ * η₁⁻¹ := by
  have hres : operatorMatrixArgumentResolvent C B₁ - operatorMatrixArgumentResolvent C B₂ =
      operatorMatrixArgumentResolvent C B₂ * scalarMatrixEmbedding (B₂ - B₁) *
        operatorMatrixArgumentResolvent C B₁ :=
    operatorMatrixArgumentResolvent_sub C B₁ B₂ h₁ h₂
  have hdiff : operatorMatrixArgumentCauchy C B₁ - operatorMatrixArgumentCauchy C B₂ =
      matrixExpectation (vacuumState ι).toProbabilitySpace
        (operatorMatrixArgumentResolvent C B₂ * scalarMatrixEmbedding (B₂ - B₁) *
          operatorMatrixArgumentResolvent C B₁) := by
    unfold operatorMatrixArgumentCauchy
    rw [← map_sub, hres]
  rw [hdiff]
  refine (frob_matrixExpectation_le _).trans ?_
  have hneg : frob (B₂ - B₁) = frob (B₁ - B₂) := by
    rw [← neg_sub, frob_neg]
  have hprod : ‖CStarMatrix.ofMatrix (operatorMatrixArgumentResolvent C B₂ *
        scalarMatrixEmbedding (B₂ - B₁) * operatorMatrixArgumentResolvent C B₁)‖ ≤
      η₂⁻¹ * ((Fintype.card d : ℝ) * frob (B₁ - B₂)) * η₁⁻¹ := by
    have hfac : CStarMatrix.ofMatrix (operatorMatrixArgumentResolvent C B₂ *
          scalarMatrixEmbedding (B₂ - B₁) * operatorMatrixArgumentResolvent C B₁) =
        CStarMatrix.ofMatrix (operatorMatrixArgumentResolvent C B₂) *
          CStarMatrix.ofMatrix (scalarMatrixEmbedding (B₂ - B₁)) *
          CStarMatrix.ofMatrix (operatorMatrixArgumentResolvent C B₁) := rfl
    rw [hfac]
    have h1 : ‖CStarMatrix.ofMatrix (operatorMatrixArgumentResolvent C B₂) *
        CStarMatrix.ofMatrix (scalarMatrixEmbedding (B₂ - B₁))‖ ≤
        η₂⁻¹ * ((Fintype.card d : ℝ) * frob (B₂ - B₁)) :=
      (norm_mul_le _ _).trans
        (mul_le_mul hn₂ (norm_scalarMatrixEmbedding_le_card_mul_frob (ι := ι) (B₂ - B₁))
          (norm_nonneg _) (by positivity))
    calc ‖CStarMatrix.ofMatrix (operatorMatrixArgumentResolvent C B₂) *
          CStarMatrix.ofMatrix (scalarMatrixEmbedding (B₂ - B₁)) *
          CStarMatrix.ofMatrix (operatorMatrixArgumentResolvent C B₁)‖
        ≤ ‖CStarMatrix.ofMatrix (operatorMatrixArgumentResolvent C B₂) *
            CStarMatrix.ofMatrix (scalarMatrixEmbedding (B₂ - B₁))‖ *
            ‖CStarMatrix.ofMatrix (operatorMatrixArgumentResolvent C B₁)‖ :=
          norm_mul_le _ _
      _ ≤ η₂⁻¹ * ((Fintype.card d : ℝ) * frob (B₂ - B₁)) * η₁⁻¹ :=
          mul_le_mul h1 hn₁ (norm_nonneg _)
            (mul_nonneg (by positivity) (mul_nonneg (by positivity) (frob_nonneg _)))
      _ = η₂⁻¹ * ((Fintype.card d : ℝ) * frob (B₁ - B₂)) * η₁⁻¹ := by rw [hneg]
  calc (Fintype.card d : ℝ) *
        ‖CStarMatrix.ofMatrix (operatorMatrixArgumentResolvent C B₂ *
          scalarMatrixEmbedding (B₂ - B₁) * operatorMatrixArgumentResolvent C B₁)‖
      ≤ (Fintype.card d : ℝ) * (η₂⁻¹ * ((Fintype.card d : ℝ) * frob (B₁ - B₂)) * η₁⁻¹) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = (Fintype.card d : ℝ) ^ 2 * frob (B₁ - B₂) * η₂⁻¹ * η₁⁻¹ := by ring

/-! ## 3. The pencil-argument resolvent norm bound -/

/-- At a pencil argument the matrix-argument resolvent is the genuine resolvent of the
self-adjoint affine pencil, hence bounded by `|Im z|⁻¹`. -/
theorem norm_operatorMatrixArgumentResolvent_pencil (C₀ : Matrix d d ℂ)
    (C : ι → Matrix d d ℂ) (hC₀ : C₀.IsHermitian) (hC : ∀ i, (C i).IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) :
    ‖CStarMatrix.ofMatrix
      (operatorMatrixArgumentResolvent C (z • (1 : Matrix d d ℂ) - C₀))‖ ≤ |z.im|⁻¹ := by
  have hdiff : operatorMatrixDifference C (z • (1 : Matrix d d ℂ) - C₀) =
      algebraMap ℂ (CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι)) z -
        operatorMatrixPencil C₀ C :=
    operatorMatrixDifference_pencil C₀ C z
  have hsa : IsSelfAdjoint (operatorMatrixPencil C₀ C) :=
    operatorMatrixPencil_isSelfAdjoint C₀ C hC₀ hC
  have hres : ‖resolvent (operatorMatrixPencil C₀ C) z‖ ≤ |z.im|⁻¹ :=
    norm_resolvent_le_inv_abs_im hsa hz
  have hval : CStarMatrix.ofMatrix
      (operatorMatrixArgumentResolvent C (z • (1 : Matrix d d ℂ) - C₀)) =
      resolvent (operatorMatrixPencil C₀ C) z := by
    unfold operatorMatrixArgumentResolvent
    rw [hdiff]
    rfl
  rw [hval]
  exact hres

/-! ## 4. The trivial deterministic bound -/

/-- **Trivial bound.**  Both Cauchy transforms are bounded by `card d / Im z` in the upper
half-plane, so their difference is bounded by `2 card d / Im z`. -/
theorem frob_mean_sub_limit_trivial_le (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) {z : ℂ} (hz : 0 < z.im)
    (hN : 0 < N) :
    frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z) ≤
      2 * (Fintype.card d : ℝ) * (z.im)⁻¹ := by
  refine (frob_sub_le _ _).trans ?_
  have h1 := frob_gueResolventMean_le A₀ A hA₀ hA z hz hN
  have h2 := frob_operatorMatrixPencilCauchy_le A₀ A hA₀ hA z hz.ne'
  rw [abs_of_pos hz] at h2
  linarith

/-! ## 5. Elementary power algebra for the strip exponents -/

/-- `y^(-5) * y⁻¹ * y⁻¹ = y^(-7)`. -/
theorem rpow_neg_five_mul_inv_sq {y : ℝ} (hy : 0 < y) :
    y ^ (-(5 : ℝ)) * (y⁻¹ * y⁻¹) = y ^ (-(7 : ℝ)) := by
  have h2 : y⁻¹ * y⁻¹ = y ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg hy.le, Real.rpow_ofNat]
    norm_num
    field_simp
  rw [h2, ← Real.rpow_add hy]
  norm_num

/-- `y^(-7) = y^(-6) * y⁻¹`. -/
theorem rpow_neg_seven_eq_six_mul_inv {y : ℝ} (hy : 0 < y) :
    y ^ (-(7 : ℝ)) = y ^ (-(6 : ℝ)) * y⁻¹ := by
  have h1 : y⁻¹ = y ^ (-(1 : ℝ)) := by
    rw [Real.rpow_neg_one]
  rw [h1, ← Real.rpow_add hy]
  norm_num

/-! ## 6. The good-region comparison -/

/-- **Good-region comparison** (HT05 (5.21)–(5.22)).

On the region where the argument Cauchy transform is identified with the finite-`N` mean
(Worker B) and the self-energy is `O(N⁻² |Im z|⁻⁵)` (Worker A), the second resolvent identity
gives
`frob (m - g) ≤ 2 (card d)² C N⁻² |Im z|⁻⁷`. -/
theorem frob_mean_sub_limit_le_good (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) {N : ℕ} {Λ : Matrix d d ℂ}
    {Cst : ℝ} (hCst : 0 ≤ Cst) {z : ℂ} (hz : 0 < z.im) (hN : 0 < N)
    (hΛ : frob (Λ - z • (1 : Matrix d d ℂ)) ≤
      Cst * z.im ^ (-(5 : ℝ)) / (N : ℝ) ^ 2)
    (hunit : IsUnit (operatorMatrixDifference A (Λ - A₀)))
    (hn : ‖CStarMatrix.ofMatrix (operatorMatrixArgumentResolvent A (Λ - A₀))‖ ≤ 2 / z.im)
    (hident : gueResolventMean (N := N) A₀ A z = operatorMatrixArgumentCauchy A (Λ - A₀)) :
    frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z) ≤
      4 * (Fintype.card d : ℝ) ^ 2 * Cst * z.im ^ (-(7 : ℝ)) / (N : ℝ) ^ 2 := by
  have hbridge : operatorMatrixPencilCauchy A₀ A z =
      operatorMatrixArgumentCauchy A (z • (1 : Matrix d d ℂ) - A₀) :=
    (operatorMatrixArgumentCauchy_pencil A₀ A z).symm
  rw [hident, hbridge]
  have hunit₂ : IsUnit (operatorMatrixDifference A (z • (1 : Matrix d d ℂ) - A₀)) := by
    rw [operatorMatrixDifference_pencil]
    exact operatorMatrixPencil_mem_resolventSet A₀ A hA₀ hA z hz.ne'
  have hn₂ : ‖CStarMatrix.ofMatrix
      (operatorMatrixArgumentResolvent A (z • (1 : Matrix d d ℂ) - A₀))‖ ≤ (z.im)⁻¹ := by
    have h := norm_operatorMatrixArgumentResolvent_pencil (C₀ := A₀) (C := A) hA₀ hA z hz.ne'
    rwa [abs_of_pos hz] at h
  have hn₁ : ‖CStarMatrix.ofMatrix (operatorMatrixArgumentResolvent A (Λ - A₀))‖ ≤
      (z.im / 2)⁻¹ := by
    refine hn.trans_eq ?_
    field_simp
  have hmain := frob_operatorMatrixArgumentCauchy_sub_le (C := A) (B₁ := Λ - A₀)
    (B₂ := z • (1 : Matrix d d ℂ) - A₀) hunit hunit₂
    (η₁ := z.im / 2) (η₂ := z.im) (by positivity) hz hn₁ hn₂
  have hsub : (Λ - A₀) - (z • (1 : Matrix d d ℂ) - A₀) = Λ - z • (1 : Matrix d d ℂ) := by
    abel
  rw [hsub] at hmain
  refine hmain.trans ?_
  have h2inv : (z.im / 2)⁻¹ = 2 * (z.im)⁻¹ := by field_simp
  rw [h2inv]
  have hstep : (Fintype.card d : ℝ) ^ 2 * frob (Λ - z • (1 : Matrix d d ℂ)) * (z.im)⁻¹ *
        (2 * (z.im)⁻¹) =
      2 * (Fintype.card d : ℝ) ^ 2 * frob (Λ - z • (1 : Matrix d d ℂ)) *
        ((z.im)⁻¹ * (z.im)⁻¹) := by ring
  rw [hstep]
  have hfr0 : 0 ≤ frob (Λ - z • (1 : Matrix d d ℂ)) := frob_nonneg _
  have hcoef0 : 0 ≤ 2 * (Fintype.card d : ℝ) ^ 2 := by positivity
  have hbound : 2 * (Fintype.card d : ℝ) ^ 2 * frob (Λ - z • (1 : Matrix d d ℂ)) *
        ((z.im)⁻¹ * (z.im)⁻¹) ≤
      2 * (Fintype.card d : ℝ) ^ 2 *
        (Cst * z.im ^ (-(5 : ℝ)) / (N : ℝ) ^ 2) * ((z.im)⁻¹ * (z.im)⁻¹) := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact mul_le_mul_of_nonneg_left hΛ hcoef0
  refine hbound.trans ?_
  have hy7 : 0 < z.im ^ (-(7 : ℝ)) := Real.rpow_pos_of_pos hz _
  calc 2 * (Fintype.card d : ℝ) ^ 2 * (Cst * z.im ^ (-(5 : ℝ)) / (N : ℝ) ^ 2) *
        ((z.im)⁻¹ * (z.im)⁻¹)
      = 2 * (Fintype.card d : ℝ) ^ 2 * Cst *
          (z.im ^ (-(5 : ℝ)) * ((z.im)⁻¹ * (z.im)⁻¹)) / (N : ℝ) ^ 2 := by ring
    _ = 2 * (Fintype.card d : ℝ) ^ 2 * Cst * z.im ^ (-(7 : ℝ)) / (N : ℝ) ^ 2 := by
        rw [rpow_neg_five_mul_inv_sq hz]
    _ ≤ 4 * (Fintype.card d : ℝ) ^ 2 * Cst * z.im ^ (-(7 : ℝ)) / (N : ℝ) ^ 2 := by
        have h0 : 0 ≤ (Fintype.card d : ℝ) ^ 2 * Cst * z.im ^ (-(7 : ℝ)) / (N : ℝ) ^ 2 := by
          have hcard : (0:ℝ) ≤ (Fintype.card d : ℝ) ^ 2 := by positivity
          have hN0 : (0:ℝ) < (N : ℝ) ^ 2 := by positivity
          exact div_nonneg (mul_nonneg (mul_nonneg hcard hCst) hy7.le) hN0.le
        have hrw : 2 * (Fintype.card d : ℝ) ^ 2 * Cst * z.im ^ (-(7 : ℝ)) / (N : ℝ) ^ 2 =
            2 * ((Fintype.card d : ℝ) ^ 2 * Cst * z.im ^ (-(7 : ℝ)) / (N : ℝ) ^ 2) := by ring
        have hrw4 : 4 * (Fintype.card d : ℝ) ^ 2 * Cst * z.im ^ (-(7 : ℝ)) / (N : ℝ) ^ 2 =
            4 * ((Fintype.card d : ℝ) ^ 2 * Cst * z.im ^ (-(7 : ℝ)) / (N : ℝ) ^ 2) := by ring
        rw [hrw, hrw4]
        linarith

/-! ## 7. The bad-region comparison -/

/-- **Bad-region comparison.**  Off the good region the failed inequality
`C N⁻² |Im z|⁻⁶ < 1/2` combines with the trivial deterministic bound to give the same
`|Im z|⁻⁷` rate, with the polynomial weight `(1 + ‖z‖)²`. -/
theorem frob_mean_sub_limit_le_bad [Nonempty d] (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) {N : ℕ} {Cst : ℝ}
    (hCst : 0 ≤ Cst) {z : ℂ} (hz : 0 < z.im) (hN : 0 < N)
    (hbad : (1 : ℝ) / 2 ≤ Cst * z.im ^ (-(6 : ℝ)) / (N : ℝ) ^ 2) :
    frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z) ≤
      4 * (Fintype.card d : ℝ) ^ 2 * Cst * (1 + ‖z‖) ^ 2 * z.im ^ (-(7 : ℝ)) /
        (N : ℝ) ^ 2 := by
  refine (frob_mean_sub_limit_trivial_le A₀ A hA₀ hA hz hN).trans ?_
  have hcard1 : (1 : ℝ) ≤ (Fintype.card d : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty d›
  have hz0 : (0 : ℝ) ≤ z.im := hz.le
  have hw1 : (1 : ℝ) ≤ (1 + ‖z‖) ^ 2 := by
    have := norm_nonneg z
    nlinarith
  have hcardw : (2 * (Fintype.card d : ℝ) * (z.im)⁻¹) ≤
      2 * (Fintype.card d : ℝ) ^ 2 * (1 + ‖z‖) ^ 2 * (z.im)⁻¹ := by
    have hinv : (0 : ℝ) ≤ (z.im)⁻¹ := by positivity
    have hcw : (1 : ℝ) ≤ (Fintype.card d : ℝ) * (1 + ‖z‖) ^ 2 := by nlinarith
    nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ 2 * (Fintype.card d : ℝ)) hinv]
  refine hcardw.trans ?_
  have hR : 4 * (Fintype.card d : ℝ) ^ 2 * Cst * (1 + ‖z‖) ^ 2 *
        z.im ^ (-(7 : ℝ)) / (N : ℝ) ^ 2 =
      4 * (Fintype.card d : ℝ) ^ 2 * (1 + ‖z‖) ^ 2 * (z.im)⁻¹ *
        (Cst * z.im ^ (-(6 : ℝ)) / (N : ℝ) ^ 2) := by
    rw [rpow_neg_seven_eq_six_mul_inv hz]
    field_simp
  rw [hR]
  have hbase : 2 * (Fintype.card d : ℝ) ^ 2 * (1 + ‖z‖) ^ 2 * (z.im)⁻¹ ≤
      4 * (Fintype.card d : ℝ) ^ 2 * (1 + ‖z‖) ^ 2 * (z.im)⁻¹ *
        (Cst * z.im ^ (-(6 : ℝ)) / (N : ℝ) ^ 2) := by
    have hpos : (0 : ℝ) ≤ 4 * (Fintype.card d : ℝ) ^ 2 * (1 + ‖z‖) ^ 2 * (z.im)⁻¹ := by
      positivity
    nlinarith [hbad, hpos]
  exact hbase

/-! ## 8. The uniform upper-half-plane comparison -/

/-- **Unconditional upper-half-plane comparison** (given Worker A's self-energy bound and
Worker B's physical-branch identification on the good region): for every `z` in the upper
half-plane,
`frob (m - g) ≤ 4 (card d)² C N⁻² (1 + ‖z‖)² |Im z|⁻⁷`. -/
theorem frob_mean_sub_limit_le_uniform [Nonempty d] (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    {N : ℕ} (hN : 0 < N) {η₀ Cst : ℝ} (hCst : 0 ≤ Cst) (Λ : ℂ → Matrix d d ℂ)
    (hΛ : ∀ z : ℂ, 0 < z.im → |z.im| < η₀ → frob (Λ z - z • (1 : Matrix d d ℂ)) ≤
      Cst * z.im ^ (-(5 : ℝ)) / (N : ℝ) ^ 2)
    (hgood : ∀ z : ℂ, 0 < z.im → |z.im| < η₀ →
      Cst * z.im ^ (-(6 : ℝ)) / (N : ℝ) ^ 2 < 1 / 2 →
      gueResolventMean (N := N) A₀ A z = operatorMatrixArgumentCauchy A (Λ z - A₀) ∧
        IsUnit (operatorMatrixDifference A (Λ z - A₀)) ∧
        ‖CStarMatrix.ofMatrix (operatorMatrixArgumentResolvent A (Λ z - A₀))‖ ≤ 2 / z.im)
    {z : ℂ} (hz : 0 < z.im) (hlt : |z.im| < η₀) :
    frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z) ≤
      4 * (Fintype.card d : ℝ) ^ 2 * Cst * (1 + ‖z‖) ^ 2 * z.im ^ (-(7 : ℝ)) /
        (N : ℝ) ^ 2 := by
  by_cases hgc : Cst * z.im ^ (-(6 : ℝ)) / (N : ℝ) ^ 2 < 1 / 2
  · obtain ⟨hident, hunit, hn⟩ := hgood z hz hlt hgc
    refine (frob_mean_sub_limit_le_good A₀ A hA₀ hA hCst hz hN (hΛ z hz hlt) hunit hn
      hident).trans ?_
    have hw1 : (1 : ℝ) ≤ (1 + ‖z‖) ^ 2 := by
      have := norm_nonneg z
      nlinarith
    have hy7 : 0 < z.im ^ (-(7 : ℝ)) := Real.rpow_pos_of_pos hz _
    have h0 : 0 ≤ 4 * (Fintype.card d : ℝ) ^ 2 * Cst * z.im ^ (-(7 : ℝ)) / (N : ℝ) ^ 2 := by
      have hc : (0 : ℝ) ≤ (Fintype.card d : ℝ) ^ 2 := by positivity
      have hNn : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
      exact div_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hc) hCst) hy7.le) hNn
    calc 4 * (Fintype.card d : ℝ) ^ 2 * Cst * z.im ^ (-(7 : ℝ)) / (N : ℝ) ^ 2
        = (4 * (Fintype.card d : ℝ) ^ 2 * Cst * z.im ^ (-(7 : ℝ)) / (N : ℝ) ^ 2) * 1 := by
          ring
      _ ≤ (4 * (Fintype.card d : ℝ) ^ 2 * Cst * z.im ^ (-(7 : ℝ)) / (N : ℝ) ^ 2) *
            (1 + ‖z‖) ^ 2 := mul_le_mul_of_nonneg_left hw1 h0
      _ = 4 * (Fintype.card d : ℝ) ^ 2 * Cst * (1 + ‖z‖) ^ 2 * z.im ^ (-(7 : ℝ)) /
            (N : ℝ) ^ 2 := by ring
  · exact frob_mean_sub_limit_le_bad A₀ A hA₀ hA hCst hz hN (le_of_not_gt hgc)

/-! ## 9. The honest weighted strip bound from the comparison -/

/-- **The honest weighted strip bound** `frob (g_N - g) ≤ C_s (1 + ‖z‖)² |Im z|⁻⁷ / N²`
follows from the comparison inputs, with `C_s = 4 (card d)² C`, on both half-planes.

The lower half-plane uses the mean-side conjugation symmetry
(`frob_gueResolventMean_sub_limit_star_of_limit`) and therefore the limit-side symmetry `hG`;
the latter is the known dependency gap recorded in `Probability/ResolventConj.lean`. -/
theorem weightedStripBoundProven_of_comparison [Nonempty d] (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    {η₀ Cst : ℝ} (hCst : 0 ≤ Cst) (hη₀ : 0 < η₀) (Λ : ℕ → ℂ → Matrix d d ℂ)
    (hΛ : ∀ᶠ N : ℕ in Filter.atTop, ∀ z : ℂ, 0 < z.im → |z.im| < η₀ →
      frob (Λ N z - z • (1 : Matrix d d ℂ)) ≤
        Cst * z.im ^ (-(5 : ℝ)) / (N : ℝ) ^ 2)
    (hgood : ∀ᶠ N : ℕ in Filter.atTop, ∀ z : ℂ, 0 < z.im → |z.im| < η₀ →
      Cst * z.im ^ (-(6 : ℝ)) / (N : ℝ) ^ 2 < 1 / 2 →
      gueResolventMean (N := N) A₀ A z = operatorMatrixArgumentCauchy A (Λ N z - A₀) ∧
        IsUnit (operatorMatrixDifference A (Λ N z - A₀)) ∧
        ‖CStarMatrix.ofMatrix (operatorMatrixArgumentResolvent A (Λ N z - A₀))‖ ≤ 2 / z.im)
    (hG : ∀ z : ℂ, star (operatorMatrixPencilCauchy A₀ A z) =
      operatorMatrixPencilCauchy A₀ A (star z)) :
    WeightedStripBoundProven A₀ A η₀ 1 (4 * (Fintype.card d : ℝ) ^ 2 * Cst) := by
  have hupper : ∀ᶠ N : ℕ in Filter.atTop, ∀ z : ℂ, 0 < z.im → |z.im| < η₀ →
      frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z) ≤
        4 * (Fintype.card d : ℝ) ^ 2 * Cst * (1 + ‖z‖) ^ 2 * |z.im| ^ (-(7 : ℝ)) /
          (N : ℝ) ^ 2 := by
    filter_upwards [hΛ, hgood, eventually_gt_atTop (0 : ℕ)] with N hΛN hgoodN hN z hz hlt
    have h := frob_mean_sub_limit_le_uniform A₀ A hA₀ hA (N := N) hN hCst
      (Λ N) hΛN hgoodN hz hlt
    simpa only [abs_of_pos hz] using h
  have hlower : ∀ᶠ N : ℕ in Filter.atTop, ∀ z : ℂ, z.im < 0 → |z.im| < η₀ →
      frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z) ≤
        4 * (Fintype.card d : ℝ) ^ 2 * Cst * (1 + ‖z‖) ^ 2 * |z.im| ^ (-(7 : ℝ)) /
          (N : ℝ) ^ 2 := by
    filter_upwards [hupper] with N hN z hzneg hlt
    have hzpos : 0 < (star z).im := by simpa [Complex.star_def] using hzneg
    have hlt' : |(star z).im| < η₀ := by simpa [Complex.star_def] using hlt
    have h := hN (star z) hzpos hlt'
    rw [frob_gueResolventMean_sub_limit_star_of_limit A₀ A hA₀ hA hG z] at h
    simpa [Complex.star_def] using h
  filter_upwards [hupper, hlower] with N hn hl
  intro z hz hlt
  rcases lt_trichotomy z.im 0 with h | h | h
  · exact hl z h hlt
  · exact absurd h hz
  · exact hn z h hlt

end GUEStrongConvergence
