/-
# An explicit countable dense family of matrix polynomials

The reduction `ae_tendsto_norm_of_dense_family` needs a countable family of matrix
polynomials that is dense in the coefficient distance `coeffDist`, with degree control.
This file constructs such a family explicitly: polynomials whose coefficients are
Gaussian rationals `a + b i` with `a b : ℚ`, represented as `MonoidAlgebra (ℚ × ℚ)`.

We prove that the coefficient-extension map `ratMatrixToComplex` from this countable index
type onto the `ℚ[i]`-valued complex matrix polynomials is surjective, so the density
theorem `exists_ratApproxPoly_coeffDist_deg` gives the `hDense` hypothesis.  Combining
this with `ae_tendsto_norm_countableFamily` (per-member convergence from `hWords`,
`hH1`, `hB`) and the scalar edge bound `hEdge`, we obtain almost-sure norm convergence
simultaneously for **all** complex matrix polynomials at fixed coefficient dimension `d`.

The remaining analytic inputs are exactly:

* `hEdge` — the scalar `ℓ¹` edge bound `∀ᶠ N, tupleNorm (gueFamily r N x) ≤ R`, and
* `hH1`/`hB` — the spectral family inclusion and uniform bound for the canonical dilated
  data of each member of the countable family.

No convergence of `‖evalMatrixPoly P (G_N)‖` for the target polynomials is assumed.

## Relation to the target statement

`ae_tendsto_norm_allPolynomials` is the fixed-`d` form of
`GUEStrongConvergenceStatement` (Target.lean), which additionally quantifies over all
`d > 0`.  Since `ℕ` is countable, the `∀ d` lifting is one more application of
`MeasureTheory.ae_all_iff`: instantiate the fixed-`d` theorem for each `d > 0`
(or for `d = k + 1` to avoid the `d = 0` instance issue) and intersect the resulting
a.e. events.  The hypotheses `hH1`/`hB` then have to be provided uniformly in `d`,
which is the only structural difference from the target statement.
-/
import GUEStrongConvergence.StrongConvergence.PolynomialApproximation
import GUEStrongConvergence.StrongConvergence.AllPolynomials

noncomputable section

namespace GUEStrongConvergence

open Filter MeasureTheory FreeProbability FreeProbability.Fock Matrix
open scoped ComplexOrder Topology BigOperators

variable {r d : ℕ}

/-! ## Gaussian-rational coefficients -/

/-- Coefficients in `ℚ[i]`, represented as a pair of rationals. -/
abbrev RatCoeff : Type := ℚ × ℚ

/-- The embedding `ℚ[i] → ℂ`, `(a, b) ↦ a + b i`. -/
def ratCoeffToComplex (c : RatCoeff) : ℂ := (c.1 : ℂ) + (c.2 : ℂ) * Complex.I

@[simp]
lemma ratCoeffToComplex_zero : ratCoeffToComplex 0 = 0 := by
  simp [ratCoeffToComplex]

/-- Map the coefficients of a word polynomial along a zero-preserving map. -/
def mapCoeffsGen {R S I : Type*} [Semiring R] [Semiring S] (f : R → S) (hf : f 0 = 0)
    (p : WordPolynomial R I) : WordPolynomial S I :=
  ⟨Finsupp.mapRange f hf p.coeff⟩

@[simp]
lemma coeff_mapCoeffsGen {R S I : Type*} [Semiring R] [Semiring S]
    (f : R → S) (hf : f 0 = 0) (p : WordPolynomial R I) (w : FreeMonoid I) :
    (mapCoeffsGen f hf p).coeff w = f (p.coeff w) := by
  simp [mapCoeffsGen, Finsupp.mapRange_apply]

/-- Coefficient extension of a Gaussian-rational word polynomial to a complex one. -/
def ratPolyToComplex {I : Type*} (p : WordPolynomial RatCoeff I) : WordPolynomial ℂ I :=
  mapCoeffsGen ratCoeffToComplex ratCoeffToComplex_zero p

@[simp]
lemma coeff_ratPolyToComplex {I : Type*} (p : WordPolynomial RatCoeff I) (w : FreeMonoid I) :
    (ratPolyToComplex p).coeff w = ratCoeffToComplex (p.coeff w) := by
  simp [ratPolyToComplex]

/-- Coefficient extension of a Gaussian-rational matrix polynomial. -/
def ratMatrixToComplex (P : Matrix (Fin d) (Fin d) (WordPolynomial RatCoeff (Fin r))) :
    Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r)) :=
  fun i j => ratPolyToComplex (P i j)

/-- The countable index type of Gaussian-rational matrix polynomials. -/
abbrev RatPolyIdx (r d : ℕ) := Matrix (Fin d) (Fin d) (WordPolynomial RatCoeff (Fin r))

/-- The family of complex matrix polynomials with Gaussian-rational coefficients. -/
def denseFamily (r d : ℕ) : RatPolyIdx r d → Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r)) :=
  ratMatrixToComplex

instance countableRatPolyIdx (r d : ℕ) : Countable (RatPolyIdx r d) :=
  countable_matrixPoly (K := RatCoeff) (I := Fin r) d

/-! ## Approximation of a complex number by Gaussian rationals -/

/-- The Gaussian rational representing a complex number in `ℚ[i]` (with `0 ↦ 0`). -/
noncomputable def ratCoeffOfComplex (c : ℂ) : RatCoeff := by
  classical
  exact if c = 0 then 0
    else if h : ∃ a b : ℚ, c = (a : ℂ) + (b : ℂ) * Complex.I then
      (Classical.choose h, Classical.choose (Classical.choose_spec h))
    else 0

@[simp]
lemma ratCoeffOfComplex_zero : ratCoeffOfComplex 0 = 0 := by
  simp [ratCoeffOfComplex]

lemma ratCoeffToComplex_ratCoeffOfComplex (c : ℂ)
    (h : ∃ a b : ℚ, c = (a : ℂ) + (b : ℂ) * Complex.I) :
    ratCoeffToComplex (ratCoeffOfComplex c) = c := by
  unfold ratCoeffOfComplex
  by_cases hc : c = 0
  · simp [hc]
  · rw [if_neg hc, dif_pos h]
    exact (Classical.choose_spec (Classical.choose_spec h)).symm

end GUEStrongConvergence

namespace GUEStrongConvergence

open Filter MeasureTheory FreeProbability FreeProbability.Fock Matrix
open scoped ComplexOrder Topology BigOperators

variable {r d : ℕ}

/-- **Surjectivity onto `ℚ[i]`-valued matrix polynomials.**  Every complex matrix
polynomial whose coefficients lie in `ℚ[i]` is the image of a Gaussian-rational one. -/
lemma ratMatrixToComplex_surjective
    (Q : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r)))
    (hQ : ∀ i j w, ∃ a b : ℚ, (Q i j).coeff w = (a : ℂ) + (b : ℂ) * Complex.I) :
    ∃ F : RatPolyIdx r d, ratMatrixToComplex F = Q := by
  classical
  refine ⟨fun i j => mapCoeffsGen ratCoeffOfComplex ratCoeffOfComplex_zero (Q i j), ?_⟩
  funext i j
  refine MonoidAlgebra.coeff_injective ?_
  ext w
  simp [ratMatrixToComplex, ratPolyToComplex, coeff_ratPolyToComplex,
    ratCoeffToComplex_ratCoeffOfComplex _ (hQ i j w)]

/-- **Density of the explicit countable family** in the coefficient distance, with degree
control.  This is the `hDense` hypothesis of `ae_tendsto_norm_of_dense_family`. -/
theorem denseFamily_hDense [Nonempty (Fin d)] [Nonempty (Fin (d + d))] :
    ∀ (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r))) (ε : ℝ), 0 < ε →
      ∃ i : RatPolyIdx r d, coeffDist P (denseFamily r d i) < ε ∧
        polyDeg (denseFamily r d i) ≤ polyDeg P := by
  intro P ε hε
  obtain ⟨Q, hdist, hdeg, hQ⟩ := exists_ratApproxPoly_coeffDist_deg P hε
  obtain ⟨F, hF⟩ := ratMatrixToComplex_surjective Q hQ
  refine ⟨F, ?_, ?_⟩
  · show coeffDist P (ratMatrixToComplex F) < ε
    rw [hF]; exact hdist
  · show polyDeg (ratMatrixToComplex F) ≤ polyDeg P
    rw [hF]; exact hdeg

end GUEStrongConvergence

namespace GUEStrongConvergence

open Filter MeasureTheory FreeProbability FreeProbability.Fock Matrix
open scoped ComplexOrder Topology BigOperators

variable {r d : ℕ} [Nonempty (Fin d)] [Nonempty (Fin (d + d))]

local instance : Nontrivial (closedSemicircularAlgebra (Fin r)) :=
  (closedGeneratedVacuumState (Fin r)).toProbabilitySpace.nontrivial

local instance : PartialOrder (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrder _

local instance : StarOrderedRing (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrderedRing _

/-- **Conditional almost-sure strong convergence for all complex matrix polynomials.**

Inputs:

* `hWords` — convergence of all scalar GUE word traces to the free joint moments;
* `hEdge` — the scalar `ℓ¹` edge bound on the GUE generators;
* `hH1`, `hB` — spectral family inclusion and uniform bound for the canonical dilated
  data of every member of the countable Gaussian-rational family `denseFamily r d`.

The conclusion is the simultaneous statement over *all* complex matrix polynomials, at
fixed coefficient dimension `d`.  The approximation argument is
`ae_tendsto_norm_of_dense_family`; the per-member convergence comes from
`ae_tendsto_norm_countableFamily`. -/
theorem ae_tendsto_norm_allPolynomials
    {R : ℝ}
    (hWords : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      ∀ w : List (Fin r),
        Tendsto (fun N : ℕ => gueNormTrace (N := N) w (x N)) atTop (𝓝 (tau r w)))
    (hEdge : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      ∀ᶠ (N : ℕ) in atTop, tupleNorm (gueFamily r N x) ≤ R)
    (Rb : RatPolyIdx r d → ℝ)
    (hH1 : ∀ F : RatPolyIdx r d, ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      SpectralFamilyInclusion (B := fun n => BlockAlg (d + d) n)
        (Binf := BlockLimit r (d + d))
        (blockSemicircular r (d + d)) (blockGUE r (d + d) x)
        (polyW (dilationPolyFin (denseFamily r d F)))
        (fun n k => (1 / 2 : ℂ) •
          polyCoeff (A := CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
            (dilationPolyFin (denseFamily r d F)) k)
        (fun k => (1 / 2 : ℂ) •
          polyCoeff (A := closedSemicircularAlgebra (Fin r))
            (dilationPolyFin (denseFamily r d F)) k)
        (fun _ => 0) 0)
    (hB : ∀ F : RatPolyIdx r d, ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      ∀ᶠ n in atTop,
        ‖wordPolyEvalC (0 : BlockAlg (d + d) n) (blockGUE r (d + d) x n)
          (polyW (dilationPolyFin (denseFamily r d F)))
          (fun k => (1 / 2 : ℂ) •
            polyCoeff (A := CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
              (dilationPolyFin (denseFamily r d F)) k)‖ ≤ Rb F) :
    ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      ∀ P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r)),
        Tendsto (fun N : ℕ => ‖evalMatrixPoly P (gueFamily r N x)‖) atTop
          (𝓝 ‖evalMatrixPoly P (semicircularFamily r)‖) := by
  have hfam : ∀ F : RatPolyIdx r d, ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      Tendsto (fun N : ℕ => ‖evalMatrixPoly (denseFamily r d F) (gueFamily r N x)‖) atTop
        (𝓝 ‖evalMatrixPoly (denseFamily r d F) (semicircularFamily r)‖) :=
    ae_all_iff.1 (ae_tendsto_norm_countableFamily (r := r) (d := d)
      (Ps := denseFamily r d) (Rb := Rb) hWords hH1 hB)
  exact ae_tendsto_norm_of_dense_family (r := r) (d := d) (Ps := denseFamily r d)
    (denseFamily_hDense (r := r) (d := d)) hEdge hfam

/-- Same as `ae_tendsto_norm_allPolynomials`, with the spectral-inclusion and uniform-bound
hypotheses stated as single a.e. events quantifying over the whole countable family. -/
theorem ae_tendsto_norm_allPolynomials_of_uniform
    {R : ℝ}
    (hWords : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      ∀ w : List (Fin r),
        Tendsto (fun N : ℕ => gueNormTrace (N := N) w (x N)) atTop (𝓝 (tau r w)))
    (hEdge : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      ∀ᶠ (N : ℕ) in atTop, tupleNorm (gueFamily r N x) ≤ R)
    (Rb : RatPolyIdx r d → ℝ)
    (hH1 : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ F : RatPolyIdx r d,
      SpectralFamilyInclusion (B := fun n => BlockAlg (d + d) n)
        (Binf := BlockLimit r (d + d))
        (blockSemicircular r (d + d)) (blockGUE r (d + d) x)
        (polyW (dilationPolyFin (denseFamily r d F)))
        (fun n k => (1 / 2 : ℂ) •
          polyCoeff (A := CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
            (dilationPolyFin (denseFamily r d F)) k)
        (fun k => (1 / 2 : ℂ) •
          polyCoeff (A := closedSemicircularAlgebra (Fin r))
            (dilationPolyFin (denseFamily r d F)) k)
        (fun _ => 0) 0)
    (hB : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ F : RatPolyIdx r d,
      ∀ᶠ n in atTop,
        ‖wordPolyEvalC (0 : BlockAlg (d + d) n) (blockGUE r (d + d) x n)
          (polyW (dilationPolyFin (denseFamily r d F)))
          (fun k => (1 / 2 : ℂ) •
            polyCoeff (A := CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
              (dilationPolyFin (denseFamily r d F)) k)‖ ≤ Rb F) :
    ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      ∀ P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r)),
        Tendsto (fun N : ℕ => ‖evalMatrixPoly P (gueFamily r N x)‖) atTop
          (𝓝 ‖evalMatrixPoly P (semicircularFamily r)‖) :=
  ae_tendsto_norm_allPolynomials hWords hEdge Rb
    (fun F => ae_all_iff.1 hH1 F) (fun F => ae_all_iff.1 hB F)

end GUEStrongConvergence
