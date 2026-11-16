/-
# Simultaneous convergence over a countable family of matrix polynomials

The final statement of the project quantifies over matrix-coefficient noncommutative
polynomials.  This file isolates the measure-theoretic part of passing from
"for each polynomial, almost surely" to "almost surely, for all polynomials", and
records precisely which countability assumptions are needed.

## An honest countability restriction

`WordPolynomial ℂ (Fin r) = MonoidAlgebra ℂ (FreeMonoid (Fin r))` has coefficients in `ℂ`,
which is **uncountable**; consequently the type of complex matrix polynomials is
uncountable (for `r = 0` it is a copy of `ℂ`).  `MeasureTheory.ae_all_iff` requires a
countable index type, so `∀ P, ∀ᵐ x, …` cannot be upgraded to `∀ᵐ x, ∀ P, …` when `P`
ranges over all complex polynomials.

Accordingly, the simultaneous lifting is stated for an arbitrary *countable family*
`Ps : ι → Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r))`.  This covers, for example,
the countable family of polynomials with Gaussian-rational coefficients viewed in `ℂ`
(for which we prove the relevant `Countable` instances when the coefficient semiring is
countable).  Passing from such a countable family to *all* complex polynomials needs an
additional approximation/continuity argument with uniform-in-`N` control; that is an
analytic input beyond the countable intersection and is not assumed here.
-/
import GUEStrongConvergence.StrongConvergence.BlockDiagonalNorm
import Mathlib.SetTheory.Cardinal.Free
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Analysis.Complex.Cardinality

noncomputable section

namespace GUEStrongConvergence

open Filter MeasureTheory FreeProbability FreeProbability.Fock Matrix
open scoped ComplexOrder Topology

/-! ## Countability of polynomial and matrix types -/

/-- Monoid algebras over countable coefficient semirings and countable monoids are
countable. -/
instance countableMonoidAlgebra {K M : Type*} [Semiring K] [Countable K] [Countable M] :
    Countable (MonoidAlgebra K M) :=
  Countable.of_equiv (M →₀ K) (MonoidAlgebra.coeffEquiv (R := K) (M := M)).symm

/-- Word polynomials with coefficients in a countable semiring are countable. -/
theorem countable_wordPolynomial {K I : Type*} [Semiring K] [Countable K] [Countable I] :
    Countable (WordPolynomial K I) := inferInstance

/-- A noncomputable `DecidableEq` instance for the coefficient index type `polyIdx P`
(needed because the support subtype's decidability is not found by instance search). -/
noncomputable instance instDecidableEqPolyIdx {𝕜 D I : Type*} [Field 𝕜] [DecidableEq D]
    (P : Matrix D D (WordPolynomial 𝕜 I)) : DecidableEq (polyIdx P) :=
  Classical.decEq _

/-- Matrices of word polynomials with countable coefficients are countable. -/
theorem countable_matrixPoly {K I : Type*} [Semiring K] [Countable K] [Countable I]
    (d : ℕ) :
    Countable (Matrix (Fin d) (Fin d) (WordPolynomial K I)) :=
  Countable.of_equiv (Fin d → Fin d → WordPolynomial K I)
    (Equiv.refl (Matrix (Fin d) (Fin d) (WordPolynomial K I)))

/-- Concrete countable coefficient case: matrices of rational-coefficient word polynomials
are countable (the family to which the simultaneous lifting can be applied). -/
theorem countable_ratMatrixPoly (r d : ℕ) :
    Countable (Matrix (Fin d) (Fin d) (WordPolynomial ℚ (Fin r))) :=
  countable_matrixPoly d

/-- The complex-coefficient word polynomial type is **not** countable.  This is why the
simultaneous lifting below is stated for an arbitrary countable family rather than for all
complex polynomials. -/
theorem not_countable_complex_wordPolynomial :
    ¬ Countable (WordPolynomial ℂ (Fin 0)) := by
  intro h
  have hinj : Function.Injective
      (fun c : ℂ =>
        (MonoidAlgebra.single (1 : FreeMonoid (Fin 0)) c : WordPolynomial ℂ (Fin 0))) :=
    MonoidAlgebra.single_right_injective
  have hrange : Countable (Set.range (fun c : ℂ =>
      (MonoidAlgebra.single (1 : FreeMonoid (Fin 0)) c : WordPolynomial ℂ (Fin 0)))) :=
    inferInstance
  exact not_countable_complex
    (Set.countable_univ_iff.mpr
      (Countable.of_equiv (Set.range (fun c : ℂ =>
        (MonoidAlgebra.single (1 : FreeMonoid (Fin 0)) c : WordPolynomial ℂ (Fin 0))))
        (Equiv.ofInjective _ hinj).symm))

/-! ## The measure-theoretic lifting -/

/-- **Countable-family a.e. lifting.**  For a countable index type, a family of
almost-sure statements can be intersected. -/
theorem ae_forall_of_countable {α β : Type*} [MeasurableSpace α] {μ : Measure α}
    [Countable β] {p : α → β → Prop} (h : ∀ i, ∀ᵐ a ∂μ, p a i) :
    ∀ᵐ a ∂μ, ∀ i, p a i :=
  ae_all_iff.2 h

/-- The reverse direction, for completeness. -/
theorem forall_ae_of_ae_forall {α β : Type*} [MeasurableSpace α] {μ : Measure α}
    [Countable β] {p : α → β → Prop} (h : ∀ᵐ a ∂μ, ∀ i, p a i) :
    ∀ i, ∀ᵐ a ∂μ, p a i :=
  ae_all_iff.1 h

section Simultaneous

variable {r d : ℕ} [Nonempty (Fin d)] [Nonempty (Fin (d + d))]

local instance : Nontrivial (closedSemicircularAlgebra (Fin r)) :=
  (closedGeneratedVacuumState (Fin r)).toProbabilitySpace.nontrivial

local instance : PartialOrder (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrder _

local instance : StarOrderedRing (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrderedRing _

/-- **Simultaneous convergence over a countable family of matrix polynomials**, with the
per-polynomial spectral-inclusion and uniform-bound hypotheses.

`Ps : ι → Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r))` is an arbitrary countable
family (for instance the rational-coefficient polynomials viewed in `ℂ`); `hH1 i` and
`hB i` are the spectral family inclusion and the uniform bound for the canonical dilated
data of `Ps i`.  The conclusion is simultaneous in the family. -/
theorem ae_tendsto_norm_countableFamily
    {ι : Type*} [Countable ι]
    (Ps : ι → Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r)))
    (Rb : ι → ℝ)
    (hWords : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      ∀ w : List (Fin r),
        Tendsto (fun N : ℕ => gueNormTrace (N := N) w (x N)) atTop (𝓝 (tau r w)))
    (hH1 : ∀ i, ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      SpectralFamilyInclusion (B := fun n => BlockAlg (d + d) n)
        (Binf := BlockLimit r (d + d))
        (blockSemicircular r (d + d)) (blockGUE r (d + d) x)
        (polyW (dilationPolyFin (Ps i)))
        (fun n k => (1 / 2 : ℂ) •
          polyCoeff (A := CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
            (dilationPolyFin (Ps i)) k)
        (fun k => (1 / 2 : ℂ) •
          polyCoeff (A := closedSemicircularAlgebra (Fin r)) (dilationPolyFin (Ps i)) k)
        (fun _ => 0) 0)
    (hB : ∀ i, ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      ∀ᶠ n in atTop,
        ‖wordPolyEvalC (0 : BlockAlg (d + d) n) (blockGUE r (d + d) x n)
          (polyW (dilationPolyFin (Ps i)))
          (fun k => (1 / 2 : ℂ) •
            polyCoeff (A := CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
              (dilationPolyFin (Ps i)) k)‖ ≤ Rb i) :
    ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ i,
      Tendsto (fun N : ℕ => ‖evalMatrixPoly (Ps i) (gueFamily r N x)‖) atTop
        (𝓝 ‖evalMatrixPoly (Ps i) (semicircularFamily r)‖) := by
  classical
  rw [ae_all_iff]
  intro i
  exact ae_tendsto_norm_evalMatrixPoly_general (r := r) (d := d) (P := Ps i) (Rb := Rb i)
    hWords (hH1 i) (hB i)

/-- **Simultaneous convergence over a countable family**, with the spectral-inclusion and
uniform-bound hypotheses stated uniformly (a single a.e. event quantifying over the whole
family).  This is the form in which the deterministic/probabilistic inputs are naturally
proved for all polynomials at once. -/
theorem ae_tendsto_norm_countableFamily_of_uniform
    {ι : Type*} [Countable ι]
    (Ps : ι → Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r)))
    (Rb : ι → ℝ)
    (hWords : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      ∀ w : List (Fin r),
        Tendsto (fun N : ℕ => gueNormTrace (N := N) w (x N)) atTop (𝓝 (tau r w)))
    (hH1 : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ i,
      SpectralFamilyInclusion (B := fun n => BlockAlg (d + d) n)
        (Binf := BlockLimit r (d + d))
        (blockSemicircular r (d + d)) (blockGUE r (d + d) x)
        (polyW (dilationPolyFin (Ps i)))
        (fun n k => (1 / 2 : ℂ) •
          polyCoeff (A := CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
            (dilationPolyFin (Ps i)) k)
        (fun k => (1 / 2 : ℂ) •
          polyCoeff (A := closedSemicircularAlgebra (Fin r)) (dilationPolyFin (Ps i)) k)
        (fun _ => 0) 0)
    (hB : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ i,
      ∀ᶠ n in atTop,
        ‖wordPolyEvalC (0 : BlockAlg (d + d) n) (blockGUE r (d + d) x n)
          (polyW (dilationPolyFin (Ps i)))
          (fun k => (1 / 2 : ℂ) •
            polyCoeff (A := CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
              (dilationPolyFin (Ps i)) k)‖ ≤ Rb i) :
    ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ i,
      Tendsto (fun N : ℕ => ‖evalMatrixPoly (Ps i) (gueFamily r N x)‖) atTop
        (𝓝 ‖evalMatrixPoly (Ps i) (semicircularFamily r)‖) :=
  ae_tendsto_norm_countableFamily (r := r) (d := d) Ps Rb hWords
    (fun i => ae_all_iff.1 hH1 i) (fun i => ae_all_iff.1 hB i)

end Simultaneous

end GUEStrongConvergence
