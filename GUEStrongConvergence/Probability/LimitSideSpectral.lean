/-
# Limit-side plumbing for the smooth trace comparison (Lemma M)

This file makes precise the deterministic limit side of the smooth trace comparison
(Lemma M): the operator-valued Cauchy transform `operatorMatrixPencilCauchy`, the limit
trace `τ` on the closed semicircular algebra, and the limit spectral statistic
`τ_d(τ(f(h)))`.

## Main definitions and results

* `idTensorTauResolvent` — `(id_d ⊗ τ)((z - h)⁻¹)` for the affine Fock matrix pencil
  `h = operatorMatrixPencil C₀ C`, i.e. the entrywise vacuum expectation of the genuine
  bounded-operator resolvent;
* `operatorMatrixPencilCauchy_eq_idTensorTauResolvent` — the dependency's Cauchy transform
  is *definitionally* this object (no hypotheses, no resolvent-set condition);
* `trace_operatorMatrixPencilCauchy` — its matrix trace is
  `τ(Tr_d((z - h)⁻¹))`, the scalar trace of the limit resolvent.  Together with
  `operatorMatrixPencilCauchy_eq_idTensorTauResolvent` this is the exact bridge between
  the `Matrix.trace` normalization of the project and the operator-valued `τ` of the
  dependency;
* `limitResolventTrace` — the scalar limit resolvent trace `Tr_d((z - h)⁻¹)` applied to
  `τ` (equal to `Matrix.trace (operatorMatrixPencilCauchy …)`);
* `blockLimitState` — the matrix-amplified limit state `τ_d ⊗ τ` on
  `BlockLimit r d = M_d(A_r)`;
* `limitTraceCfcC` / `limitTraceCfc` — the limit spectral statistic
  `τ_d(τ(f(h))) ∈ ℂ` and its real form, defined through the continuous functional
  calculus of the closed semicircular algebra;
* `limitTraceCfcC_eq_trace` — `τ_d(τ(f(h))) = (card d)⁻¹ · τ(Tr_d(f(h)))`;
* `trace_cfc_eq_card_mul_limitTraceCfcC` — `τ(Tr_d(f(h))) = card d · τ_d(τ(f(h)))`,
  the limit-side analogue of `Tr(f(H_N)) = (card d · N) · τ_N(f(H_N))`;
* `limitTraceCfcC_im_eq_zero` / `limitTraceCfcC_eq_ofReal` — the statistic is real;
* `limitTraceCfcPoly` and `limitTraceCfcPoly_eq_canonical` — specialization to the
  matrix-polynomial (dilated `denseFamily`) data of `StrongConvergence/FinalStatement`,
  identifying the canonical pencil data `C = 0`, `q = (1/2) P(g)`.

## The comparison shape (Lemma M)

`comparison_shape_of_trace_representations` records the exact identity that the
Helffer–Sjöstrand representation yields for the difference of the finite and limit
statistics, with the project's normalization
`f λ = (I / (2π)) ∫∫ (I • fderiv F z 1 - fderiv F z I) / (z - λ)`
(equivalently `-(1/π) ∫∫ ∂̄F / (z - λ)`, see `Probability/HelfferSjostrand.lean`).
The two representation hypotheses are the precise remaining input: the scalar (finite
matrix) and operator-valued (limit) Cauchy–Pompeiu representations are not yet available
in the repository.  The theorem proves that, *given* those two identities, the comparison
shape holds with exactly the stated constant.
-/
import GUEStrongConvergence.StrongConvergence.FinalStatement
import GUEStrongConvergence.Probability.HelfferSjostrand
import GUEStrongConvergence.Probability.LemmaVSmooth
import GUEStrongConvergence.Probability.DysonLimit

noncomputable section

namespace GUEStrongConvergence

open Filter MeasureTheory Matrix Complex FreeProbability FreeProbability.Fock
open scoped ComplexOrder Topology BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The limit resolvent and the operator-valued trace -/

section LimitResolvent

variable {I n : Type*} [Fintype I] [Fintype n] [DecidableEq n]

/-- **`(id_d ⊗ τ)` of the limit resolvent.**  The entrywise vacuum expectation of the
genuine bounded-operator resolvent of the affine Fock pencil
`h = operatorMatrixPencil C₀ C`.  No resolvent-set hypothesis is needed: `resolvent` is
the totalized inverse, and this is the object that the dependency's
`operatorMatrixPencilCauchy` is defined to be. -/
def idTensorTauResolvent (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ) (z : ℂ) :
    Matrix n n ℂ :=
  matrixExpectation (vacuumState I).toProbabilitySpace
    (CStarMatrix.ofMatrix.symm (resolvent (operatorMatrixPencil C₀ C) z))

/-- **Definitional identification.**  The dependency's `operatorMatrixPencilCauchy` *is*
`(id_n ⊗ τ)((z - h)⁻¹)`, with `h` the affine Fock matrix pencil and `τ` the vacuum state
of the operator algebra.  This is `rfl`. -/
theorem operatorMatrixPencilCauchy_eq_idTensorTauResolvent
    (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ) (z : ℂ) :
    operatorMatrixPencilCauchy C₀ C z = idTensorTauResolvent C₀ C z := rfl

/-- **Trace of the limit resolvent.**  The matrix trace of the operator-valued Cauchy
transform is the vacuum expectation of the (operator-valued) trace of the genuine
resolvent:
`Tr(operatorMatrixPencilCauchy C₀ C z) = τ(Tr_d((z - h)⁻¹))`.

This is unconditional: it is the linearity of `τ` and the definition of the trace. -/
theorem trace_operatorMatrixPencilCauchy
    (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ) (z : ℂ) :
    Matrix.trace (operatorMatrixPencilCauchy C₀ C z) =
      (vacuumState I).expectation
        (Matrix.trace (CStarMatrix.ofMatrix.symm
          (resolvent (operatorMatrixPencil C₀ C) z))) := by
  rw [operatorMatrixPencilCauchy, Matrix.trace, Matrix.trace, map_sum]
  rfl

/-- **Target form of the trace identity.**  The matrix trace of the limit Cauchy transform
is the trace of `(id_d ⊗ τ)((z - h)⁻¹)`, with `h = operatorMatrixPencil C₀ C`. -/
theorem trace_operatorMatrixPencilCauchy_eq_trace_idTensorTauResolvent
    (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ) (z : ℂ) :
    Matrix.trace (operatorMatrixPencilCauchy C₀ C z) =
      Matrix.trace (idTensorTauResolvent C₀ C z) := rfl

/-- Entrywise form of the definitional identification: each matrix entry of the limit
resolvent is the vacuum expectation of the corresponding entry of the genuine resolvent. -/
@[simp] theorem operatorMatrixPencilCauchy_apply
    (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ) (z : ℂ) (i j : n) :
    operatorMatrixPencilCauchy C₀ C z i j =
      (vacuumState I).expectation
        (CStarMatrix.ofMatrix.symm
          (resolvent (operatorMatrixPencil C₀ C) z) i j) := rfl

/-- The scalar limit resolvent trace `τ(Tr_d((z - h)⁻¹))`, equal to the matrix trace of
the dependency's Cauchy transform by `trace_operatorMatrixPencilCauchy`. -/
def limitResolventTrace (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ) (z : ℂ) : ℂ :=
  (vacuumState I).expectation
    (Matrix.trace (CStarMatrix.ofMatrix.symm (resolvent (operatorMatrixPencil C₀ C) z)))

/-- The scalar limit resolvent trace is the matrix trace of `operatorMatrixPencilCauchy`. -/
theorem limitResolventTrace_eq_trace
    (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ) (z : ℂ) :
    limitResolventTrace C₀ C z = Matrix.trace (operatorMatrixPencilCauchy C₀ C z) :=
  (trace_operatorMatrixPencilCauchy C₀ C z).symm

end LimitResolvent

/-! ## 2. The limit spectral statistic `τ_d(τ(f(h)))` -/

section LimitSpectral

variable {r d : ℕ} [Nonempty (Fin d)]

local instance limitSideNontrivial : Nontrivial (closedSemicircularAlgebra (Fin r)) :=
  (closedGeneratedVacuumState (Fin r)).toProbabilitySpace.nontrivial

local instance limitSidePartialOrder : PartialOrder (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrder _

local instance limitSideStarOrderedRing : StarOrderedRing (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrderedRing _

/-- The continuous functional calculus of the block limit algebra.  Mathlib activates the
generic normal-element calculus only locally for abstract C⋆-algebras, so we install it for
`BlockLimit r d = M_d(A_r)`; the self-adjoint calculus `ContinuousFunctionalCalculus ℝ _ _`
then follows from the global `IsSelfAdjoint.instContinuousFunctionalCalculus`. -/
local instance limitSideCfcComplex : ContinuousFunctionalCalculus ℂ (BlockLimit r d) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

/-- The self-adjoint (real) continuous functional calculus on `BlockLimit r d`. -/
local instance limitSideCfcReal : ContinuousFunctionalCalculus ℝ (BlockLimit r d) IsSelfAdjoint :=
  @IsSelfAdjoint.instContinuousFunctionalCalculus (BlockLimit r d) _ _ _ _ _

/-- The matrix-amplified limit state `τ_d ⊗ τ` on `BlockLimit r d = M_d(A_r)`. -/
def blockLimitState (r d : ℕ) [Nonempty (Fin d)] : StarProbabilitySpace (BlockLimit r d) :=
  matrixStarState (D := Fin d) (closedGeneratedVacuumState (Fin r))

/-- The continuous functional calculus of the limit block algebra, with the block-limit type
made explicit so that the (locally installed) real functional-calculus instance is used. -/
def limitCfc (f : ℝ → ℝ) (h : BlockLimit r d) : BlockLimit r d := cfc f h

/-- **The limit spectral statistic** `τ_d(τ(f(h)))`, as a complex number: the matrix-amplified
vacuum state of the continuous functional calculus of `h`. -/
def limitTraceCfcC (f : ℝ → ℝ) (h : BlockLimit r d) : ℂ :=
  (blockLimitState r d).expectation (limitCfc f h)

/-- **The real limit spectral statistic** `τ_d(τ(f(h)))`, analogous to the finite
`τ_N(f(H_N)) = guePencilNormTrace (cfc f H_N)`. -/
def limitTraceCfc (f : ℝ → ℝ) (h : BlockLimit r d) : ℝ := (limitTraceCfcC f h).re

/-- **The amplified-state trace formula.**  `τ_d(τ(f(h)))` is `(card d)⁻¹` times the vacuum
expectation of the operator-valued trace `Tr_d(f(h))`. -/
theorem limitTraceCfcC_eq_trace (f : ℝ → ℝ) (h : BlockLimit r d) :
    limitTraceCfcC f h =
      ((Fintype.card (Fin d) : ℂ))⁻¹ *
        (closedGeneratedVacuumState (Fin r)).expectation (Matrix.trace (limitCfc f h)) := by
  unfold limitTraceCfcC limitCfc blockLimitState
  exact matrixStarState_expectation_eq_trace _ _

/-- **Limit-side trace identity.**  The `τ`-trace of `Tr_d(f(h))` is `card d` times the
normalized limit statistic, the exact limit-side analogue of
`Tr(f(H_N)) = (card d · N) · τ_N(f(H_N))`. -/
theorem trace_cfc_eq_card_mul_limitTraceCfcC (f : ℝ → ℝ) (h : BlockLimit r d) :
    (closedGeneratedVacuumState (Fin r)).expectation (Matrix.trace (limitCfc f h)) =
      (Fintype.card (Fin d) : ℂ) * limitTraceCfcC f h := by
  rw [limitTraceCfcC_eq_trace]
  have hcard : (Fintype.card (Fin d) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [← mul_assoc, mul_inv_cancel₀ hcard, one_mul]

/-- The limit spectral statistic is real: the continuous functional calculus of `h` is
self-adjoint, and the vacuum state of a self-adjoint element is real. -/
theorem limitTraceCfcC_im_eq_zero (f : ℝ → ℝ) (h : BlockLimit r d) :
    (limitTraceCfcC f h).im = 0 := by
  unfold limitTraceCfcC limitCfc blockLimitState
  exact StarProbabilitySpace.expectation_selfAdjoint_im_eq_zero _
    (cfc_predicate f h).star_eq

/-- The complex statistic is the complexification of the real statistic. -/
theorem limitTraceCfcC_eq_ofReal (f : ℝ → ℝ) (h : BlockLimit r d) :
    limitTraceCfcC f h = (limitTraceCfc f h : ℂ) := by
  apply Complex.ext
  · simp [limitTraceCfc]
  · simpa [limitTraceCfc] using limitTraceCfcC_im_eq_zero f h

section PolynomialData

variable (f : ℝ → ℝ)

/-- **Limit statistic on the dilated polynomial data.**  For a matrix-coefficient polynomial
`P` (in the application `P = dilationPolyFin (denseFamily r (k+1) F)`, `d = (k+1)+(k+1)`),
the limit spectral statistic is `τ_d(τ(f(P(s))))` with
`P(s) = evalMatrixPoly P (semicircularFamily r)`. -/
def limitTraceCfcPoly (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r))) : ℂ :=
  limitTraceCfcC f (evalMatrixPoly P (semicircularFamily r))

/-- **Identification with the canonical pencil data.**  For a matrix polynomial whose
evaluation at the semicircular family is self-adjoint, the limit statistic is the one of the
canonical pencil polynomial `wordPolyEvalC 0 (blockSemicircular r d) (polyW P) ((1/2) •
polyCoeff P)` used in `StrongConvergence/FinalStatement`. -/
theorem limitTraceCfcPoly_eq_canonical
    (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r)))
    (hsa : IsSelfAdjoint (evalMatrixPoly P (semicircularFamily r))) :
    limitTraceCfcPoly f P =
      limitTraceCfcC f
        (wordPolyEvalC (0 : BlockLimit r d) (blockSemicircular r d) (polyW P)
          (fun k => (1 / 2 : ℂ) •
            polyCoeff (A := closedSemicircularAlgebra (Fin r)) P k)) := by
  unfold limitTraceCfcPoly
  have h := wordPolyEvalC_zero_half_eq (A := closedSemicircularAlgebra (Fin r)) P
    (semicircularFamily r) hsa
  change limitTraceCfcC f (evalMatrixPoly P (semicircularFamily r)) =
    limitTraceCfcC f (wordPolyEvalC (0 : BlockLimit r d)
      (fun i => blockDiag (d := d) (semicircularFamily r i)) (polyW P)
      (fun k => (1 / 2 : ℂ) • polyCoeff (A := closedSemicircularAlgebra (Fin r)) P k))
  rw [h]

end PolynomialData

end LimitSpectral

/-! ## 3. The comparison shape implied by the Helffer--Sjöstrand representation -/

section Comparison

variable {r d : ℕ} [Nonempty (Fin d)]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The `∂̄` weight `2 I ∂̄F` of the cut-off almost-analytic extension of `f`:
`I • fderiv F z 1 - fderiv F z I`.  This is the first factor of the project's
`pompeiuIntegrand`. -/
def hsDbarWeight (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  I • fderiv ℝ (almostAnalyticExtCut f) z 1 - fderiv ℝ (almostAnalyticExtCut f) z I

/-- The weight is definitionally the first factor of `pompeiuIntegrand`. -/
theorem pompeiuIntegrand_eq_hsDbarWeight (f : ℝ → ℝ) (lam z : ℂ) :
    pompeiuIntegrand (almostAnalyticExtCut f) lam z =
      hsDbarWeight f z * (z - lam)⁻¹ := rfl

/-- The scalar resolvent trace `Tr((z - H)⁻¹)` of a finite matrix. -/
def finiteResolventTrace (H : Matrix n n ℂ) (z : ℂ) : ℂ :=
  Matrix.trace (resolvent H z)

/-- The limit resolvent trace `τ(Tr_d((z - h)⁻¹))` on the closed semicircular algebra, the
operator-valued analogue of `finiteResolventTrace`.  The corresponding Fock-pencil object is
`limitResolventTrace`, identified with `Matrix.trace (operatorMatrixPencilCauchy …)` by
`trace_operatorMatrixPencilCauchy`. -/
def blockLimitResolventTrace (h : BlockLimit r d) (z : ℂ) : ℂ :=
  (closedGeneratedVacuumState (Fin r)).expectation (Matrix.trace (resolvent h z))

/-- **The finite-matrix trace Helffer–Sjöstrand representation**, in the normalization of
`Probability/HelfferSjostrand.lean`:
`f λ = (I / 2π) ∫∫ (I • fderiv F z 1 - fderiv F z I) / (z - λ)`.
This is the precise remaining scalar input for the finite side. -/
def FiniteHSTraceRepresentation (f : ℝ → ℝ) (H : Matrix n n ℂ) (hH : H.IsHermitian) : Prop :=
  Matrix.trace (cfc f H) =
    (I / (2 * (Real.pi : ℂ))) *
      ∫ z : ℂ, hsDbarWeight f z * finiteResolventTrace H z ∂volume

/-- **The operator-valued trace Helffer–Sjöstrand representation** on the limit block
algebra: the same `∂̄` integral against the limit resolvent trace
`τ(Tr_d((z - h)⁻¹))`.  This is the precise remaining operator-valued input. -/
def LimitHSTraceRepresentation (f : ℝ → ℝ) (h : BlockLimit r d) (hh : IsSelfAdjoint h) : Prop :=
  (closedGeneratedVacuumState (Fin r)).expectation (Matrix.trace (limitCfc f h)) =
    (I / (2 * (Real.pi : ℂ))) *
      ∫ z : ℂ, hsDbarWeight f z * blockLimitResolventTrace h z ∂volume

/-- **The comparison shape.**  Given the finite and the limit Helffer–Sjöstrand trace
representations, the difference of the two traces is the `∂̄` double integral of the
difference of the two resolvent traces, with the exact constant `I / 2π` of
`Probability/HelfferSjostrand.lean` (equivalently `-(1/π) ∫∫ ∂̄F · …`).

The two integrability hypotheses are exactly what is needed to split the integral; the two
representation hypotheses are the only remaining analytic input. -/
theorem comparison_shape_of_trace_representations
    (f : ℝ → ℝ) (H : Matrix n n ℂ) (h : BlockLimit r d)
    (hH : H.IsHermitian) (hh : IsSelfAdjoint h)
    (hfin : FiniteHSTraceRepresentation f H hH)
    (hlim : LimitHSTraceRepresentation f h hh)
    (hIntFin : Integrable (fun z : ℂ => hsDbarWeight f z * finiteResolventTrace H z) volume)
    (hIntLim : Integrable (fun z : ℂ => hsDbarWeight f z * blockLimitResolventTrace h z) volume) :
    Matrix.trace (cfc f H) - (closedGeneratedVacuumState (Fin r)).expectation
        (Matrix.trace (limitCfc f h)) =
      (I / (2 * (Real.pi : ℂ))) *
        ∫ z : ℂ, hsDbarWeight f z *
          (finiteResolventTrace H z - blockLimitResolventTrace h z) ∂volume := by
  unfold FiniteHSTraceRepresentation at hfin
  unfold LimitHSTraceRepresentation at hlim
  rw [hfin, hlim, ← mul_sub, ← integral_sub hIntFin hIntLim]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  ring

/-- **Absolute-value form of the comparison shape**, matching
`|E[τ_N(f(H_N))] − τ(f(h))| = |E[∫∫ ∂̄F (Tr((z−H_N)⁻¹) − Tr_d((z−h)⁻¹))]|/π`
(up to the exact normalization `I / 2π` of `Probability/HelfferSjostrand.lean`). -/
theorem comparison_shape_abs
    (f : ℝ → ℝ) (H : Matrix n n ℂ) (h : BlockLimit r d)
    (hH : H.IsHermitian) (hh : IsSelfAdjoint h)
    (hfin : FiniteHSTraceRepresentation f H hH)
    (hlim : LimitHSTraceRepresentation f h hh)
    (hIntFin : Integrable (fun z : ℂ => hsDbarWeight f z * finiteResolventTrace H z) volume)
    (hIntLim : Integrable (fun z : ℂ => hsDbarWeight f z * blockLimitResolventTrace h z) volume) :
    ‖Matrix.trace (cfc f H) - (closedGeneratedVacuumState (Fin r)).expectation
        (Matrix.trace (limitCfc f h))‖ =
      ‖(I / (2 * (Real.pi : ℂ))) *
        ∫ z : ℂ, hsDbarWeight f z *
          (finiteResolventTrace H z - blockLimitResolventTrace h z) ∂volume‖ := by
  rw [comparison_shape_of_trace_representations f H h hH hh hfin hlim hIntFin hIntLim]

end Comparison

end GUEStrongConvergence
