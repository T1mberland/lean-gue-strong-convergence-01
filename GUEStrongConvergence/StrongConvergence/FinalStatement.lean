/-
# The project target reduced to `hWords`, `hEdge`, `hH1`, `hB`

This file performs the last packaging step of the conditional strong-convergence proof:

* `ae_tendsto_norm_allD` lifts the fixed-`d` conclusion of `DenseFamily.lean` to all
  coefficient dimensions simultaneously, using `MeasureTheory.ae_all_iff` over `ℕ`
  (indexing `d = k + 1` to avoid the degenerate `d = 0` case);
* `GUEStrongConvergenceStatement_conditional` states the project target
  `GUEStrongConvergenceStatement r` (Target.lean) under exactly the analytic inputs.

The conclusion uses the target's `limitNorm P`; the bridge
`limitNorm P = ‖evalMatrixPoly P (semicircularFamily r)‖` is definitional
(`limitNorm_eq`).

## The only remaining analytic inputs

* `hWords` — convergence of all scalar GUE word traces to the free joint moments
  (target part II.B);
* `hEdge` — the scalar `ℓ¹` edge bound `∀ᶠ N, tupleNorm (gueFamily r N x) ≤ R`;
* `hH1` — the one-sided spectral family inclusion for the canonical dilated data of
  every member of the countable Gaussian-rational family (target part II.A);
* `hB` — the uniform bound on the evaluated dilated block polynomial for every member.

Nothing about norm convergence of the target polynomials is assumed.
-/
import GUEStrongConvergence.StrongConvergence.DenseFamily

noncomputable section

namespace GUEStrongConvergence

open Filter MeasureTheory FreeProbability FreeProbability.Fock Matrix
open scoped ComplexOrder Topology BigOperators

variable {r : ℕ}

section Final

local instance : Nontrivial (closedSemicircularAlgebra (Fin r)) :=
  (closedGeneratedVacuumState (Fin r)).toProbabilitySpace.nontrivial

local instance : PartialOrder (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrder _

local instance : StarOrderedRing (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrderedRing _

/-- `limitNorm` is definitionally the norm of the evaluation at the semicircular family. -/
lemma limitNorm_eq {d : ℕ} (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r))) :
    limitNorm P = ‖evalMatrixPoly P (semicircularFamily r)‖ := rfl

/-- **Bundled `∀ d` lifting**, with the per-`d` hypotheses stated as single a.e. events
quantifying over all `d = k + 1` and all members of the countable family. -/
theorem ae_tendsto_norm_allD
    {R : ℝ}
    (hWords : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      ∀ w : List (Fin r),
        Tendsto (fun N : ℕ => gueNormTrace (N := N) w (x N)) atTop (𝓝 (tau r w)))
    (hEdge : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      ∀ᶠ (N : ℕ) in atTop, tupleNorm (gueFamily r N x) ≤ R)
    (Rb : ∀ k : ℕ, RatPolyIdx r (k + 1) → ℝ)
    (hH1 : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ k : ℕ, ∀ F : RatPolyIdx r (k + 1),
      SpectralFamilyInclusion (B := fun n => BlockAlg ((k + 1) + (k + 1)) n)
        (Binf := BlockLimit r ((k + 1) + (k + 1)))
        (blockSemicircular r ((k + 1) + (k + 1))) (blockGUE r ((k + 1) + (k + 1)) x)
        (polyW (dilationPolyFin (denseFamily r (k + 1) F)))
        (fun n j => (1 / 2 : ℂ) •
          polyCoeff (A := CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
            (dilationPolyFin (denseFamily r (k + 1) F)) j)
        (fun j => (1 / 2 : ℂ) •
          polyCoeff (A := closedSemicircularAlgebra (Fin r))
            (dilationPolyFin (denseFamily r (k + 1) F)) j)
        (fun _ => 0) 0)
    (hB : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ k : ℕ, ∀ F : RatPolyIdx r (k + 1),
      ∀ᶠ n in atTop,
        ‖wordPolyEvalC (0 : BlockAlg ((k + 1) + (k + 1)) n)
          (blockGUE r ((k + 1) + (k + 1)) x n)
          (polyW (dilationPolyFin (denseFamily r (k + 1) F)))
          (fun j => (1 / 2 : ℂ) •
            polyCoeff (A := CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
              (dilationPolyFin (denseFamily r (k + 1) F)) j)‖ ≤ Rb k F) :
    ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      ∀ (d : ℕ) (_ : 0 < d),
        ∀ P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r)),
          Tendsto (fun N : ℕ => ‖evalMatrixPoly P (gueFamily r N x)‖) atTop
            (𝓝 (limitNorm P)) := by
  have hH1' : ∀ (k : ℕ) (F : RatPolyIdx r (k + 1)),
      ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
        SpectralFamilyInclusion (B := fun n => BlockAlg ((k + 1) + (k + 1)) n)
          (Binf := BlockLimit r ((k + 1) + (k + 1)))
          (blockSemicircular r ((k + 1) + (k + 1))) (blockGUE r ((k + 1) + (k + 1)) x)
          (polyW (dilationPolyFin (denseFamily r (k + 1) F)))
          (fun n j => (1 / 2 : ℂ) •
            polyCoeff (A := CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
              (dilationPolyFin (denseFamily r (k + 1) F)) j)
          (fun j => (1 / 2 : ℂ) •
            polyCoeff (A := closedSemicircularAlgebra (Fin r))
              (dilationPolyFin (denseFamily r (k + 1) F)) j)
          (fun _ => 0) 0 :=
    fun k F => ae_all_iff.1 (ae_all_iff.1 hH1 k) F
  have hB' : ∀ (k : ℕ) (F : RatPolyIdx r (k + 1)),
      ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
        ∀ᶠ n in atTop,
          ‖wordPolyEvalC (0 : BlockAlg ((k + 1) + (k + 1)) n)
            (blockGUE r ((k + 1) + (k + 1)) x n)
            (polyW (dilationPolyFin (denseFamily r (k + 1) F)))
            (fun j => (1 / 2 : ℂ) •
              polyCoeff (A := CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
                (dilationPolyFin (denseFamily r (k + 1) F)) j)‖ ≤ Rb k F :=
    fun k F => ae_all_iff.1 (ae_all_iff.1 hB k) F
  have hk : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ k : ℕ,
      ∀ P : Matrix (Fin (k + 1)) (Fin (k + 1)) (WordPolynomial ℂ (Fin r)),
        Tendsto (fun N : ℕ => ‖evalMatrixPoly P (gueFamily r N x)‖) atTop
          (𝓝 ‖evalMatrixPoly P (semicircularFamily r)‖) := by
    rw [ae_all_iff]
    intro k
    haveI : Nonempty (Fin (k + 1)) := ⟨⟨0, Nat.succ_pos k⟩⟩
    haveI : Nonempty (Fin ((k + 1) + (k + 1))) := ⟨⟨0, by positivity⟩⟩
    exact ae_tendsto_norm_allPolynomials (r := r) (d := k + 1) (R := R) hWords hEdge
      (Rb k) (hH1' k) (hB' k)
  filter_upwards [hk] with x hx d hd P
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  simpa [limitNorm_eq] using hx k P

/-- Variant of `ae_tendsto_norm_allD` with the per-`d` hypotheses given member by member. -/
theorem ae_tendsto_norm_allD_of_perD
    {R : ℝ}
    (hWords : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      ∀ w : List (Fin r),
        Tendsto (fun N : ℕ => gueNormTrace (N := N) w (x N)) atTop (𝓝 (tau r w)))
    (hEdge : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      ∀ᶠ (N : ℕ) in atTop, tupleNorm (gueFamily r N x) ≤ R)
    (Rb : ∀ k : ℕ, RatPolyIdx r (k + 1) → ℝ)
    (hH1 : ∀ (k : ℕ) (F : RatPolyIdx r (k + 1)),
      ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
        SpectralFamilyInclusion (B := fun n => BlockAlg ((k + 1) + (k + 1)) n)
          (Binf := BlockLimit r ((k + 1) + (k + 1)))
          (blockSemicircular r ((k + 1) + (k + 1))) (blockGUE r ((k + 1) + (k + 1)) x)
          (polyW (dilationPolyFin (denseFamily r (k + 1) F)))
          (fun n j => (1 / 2 : ℂ) •
            polyCoeff (A := CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
              (dilationPolyFin (denseFamily r (k + 1) F)) j)
          (fun j => (1 / 2 : ℂ) •
            polyCoeff (A := closedSemicircularAlgebra (Fin r))
              (dilationPolyFin (denseFamily r (k + 1) F)) j)
          (fun _ => 0) 0)
    (hB : ∀ (k : ℕ) (F : RatPolyIdx r (k + 1)),
      ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
        ∀ᶠ n in atTop,
          ‖wordPolyEvalC (0 : BlockAlg ((k + 1) + (k + 1)) n)
            (blockGUE r ((k + 1) + (k + 1)) x n)
            (polyW (dilationPolyFin (denseFamily r (k + 1) F)))
            (fun j => (1 / 2 : ℂ) •
              polyCoeff (A := CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
                (dilationPolyFin (denseFamily r (k + 1) F)) j)‖ ≤ Rb k F) :
    ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      ∀ (d : ℕ) (_ : 0 < d),
        ∀ P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r)),
          Tendsto (fun N : ℕ => ‖evalMatrixPoly P (gueFamily r N x)‖) atTop
            (𝓝 (limitNorm P)) :=
  ae_tendsto_norm_allD hWords hEdge Rb
    (ae_all_iff.2 fun k => ae_all_iff.2 fun F => hH1 k F)
    (ae_all_iff.2 fun k => ae_all_iff.2 fun F => hB k F)

/-- **The project target, reduced to the analytic inputs.**  The conclusion is exactly
`GUEStrongConvergenceStatement r` from `Target.lean`. -/
theorem GUEStrongConvergenceStatement_conditional
    {R : ℝ}
    (hWords : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      ∀ w : List (Fin r),
        Tendsto (fun N : ℕ => gueNormTrace (N := N) w (x N)) atTop (𝓝 (tau r w)))
    (hEdge : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      ∀ᶠ (N : ℕ) in atTop, tupleNorm (gueFamily r N x) ≤ R)
    (Rb : ∀ k : ℕ, RatPolyIdx r (k + 1) → ℝ)
    (hH1 : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ k : ℕ, ∀ F : RatPolyIdx r (k + 1),
      SpectralFamilyInclusion (B := fun n => BlockAlg ((k + 1) + (k + 1)) n)
        (Binf := BlockLimit r ((k + 1) + (k + 1)))
        (blockSemicircular r ((k + 1) + (k + 1))) (blockGUE r ((k + 1) + (k + 1)) x)
        (polyW (dilationPolyFin (denseFamily r (k + 1) F)))
        (fun n j => (1 / 2 : ℂ) •
          polyCoeff (A := CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
            (dilationPolyFin (denseFamily r (k + 1) F)) j)
        (fun j => (1 / 2 : ℂ) •
          polyCoeff (A := closedSemicircularAlgebra (Fin r))
            (dilationPolyFin (denseFamily r (k + 1) F)) j)
        (fun _ => 0) 0)
    (hB : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ k : ℕ, ∀ F : RatPolyIdx r (k + 1),
      ∀ᶠ n in atTop,
        ‖wordPolyEvalC (0 : BlockAlg ((k + 1) + (k + 1)) n)
          (blockGUE r ((k + 1) + (k + 1)) x n)
          (polyW (dilationPolyFin (denseFamily r (k + 1) F)))
          (fun j => (1 / 2 : ℂ) •
            polyCoeff (A := CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
              (dilationPolyFin (denseFamily r (k + 1) F)) j)‖ ≤ Rb k F) :
    GUEStrongConvergenceStatement r := by
  simpa [GUEStrongConvergenceStatement] using
    ae_tendsto_norm_allD hWords hEdge Rb hH1 hB

end Final

end GUEStrongConvergence
