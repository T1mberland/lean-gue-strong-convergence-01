/-
# From scalar word expectations to matrix-polynomial state moments

`MatrixMomentExpansion` expresses the state applied to the trace of `(P(g))^m` as a finite
linear combination of scalar word expectations with fixed complex coefficients. This module
turns that identity into a genuine convergence statement: convergence of the states on the
finitely many word products appearing in `P^m` implies convergence of the matrix-polynomial
moment, both for the bare states and for the `tr_D ⊗ φ` amplification used in the transfer.

This is the interface step that discharges the `hmom` hypothesis of
`StrongConvergence/Transfer.lean` from scalar trace-word convergence.
-/
import GUEStrongConvergence.StrongConvergence.MatrixMomentExpansion
import GUEStrongConvergence.StrongConvergence.HmomFromWords

noncomputable section

namespace GUEStrongConvergence

open Filter FreeProbability
open scoped Topology

/-- **State moments from word expectations.** If the states converge on the finitely many
word products appearing in `P ^ m`, then the state applied to the trace of the `m`-th power
of the matrix-polynomial evaluation converges. -/
theorem tendsto_state_trace_pow_evalMatrixPoly
    {A : ℕ → Type*} [∀ n, Ring (A n)] [∀ n, Algebra ℂ (A n)] [∀ n, StarRing (A n)]
    {Ainf : Type*} [Ring Ainf] [Algebra ℂ Ainf] [StarRing Ainf]
    {d : ℕ} {I : Type*}
    (φn : ∀ n, StarProbabilitySpace (A n)) (φ : StarProbabilitySpace Ainf)
    (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ I))
    (g : ∀ n, I → A n) (ginf : I → Ainf) (m : ℕ)
    (hwords : ∀ k : polyIdx (P ^ m),
      Tendsto (fun n => (φn n).expectation (wordProd (g n) (polyW (P ^ m) k))) atTop
        (𝓝 (φ.expectation (wordProd ginf (polyW (P ^ m) k))))) :
    Tendsto (fun n => (φn n).expectation (Matrix.trace ((evalMatrixPoly P (g n)) ^ m)))
      atTop (𝓝 (φ.expectation (Matrix.trace ((evalMatrixPoly P ginf) ^ m)))) := by
  simp only [expectation_trace_pow_evalMatrixPoly]
  exact tendsto_finset_sum _ fun k _ => Tendsto.const_mul _ (hwords k)

/-- **Amplified state moments from word expectations.** The same statement for the
normalized matrix state `tr_D ⊗ φ` on `CStarMatrix D D A`. -/
theorem tendsto_matrixStarState_moment
    {A : ℕ → Type*} [∀ n, CStarAlgebra (A n)] [∀ n, PartialOrder (A n)]
    [∀ n, StarOrderedRing (A n)]
    {Ainf : Type*} [CStarAlgebra Ainf] [PartialOrder Ainf] [StarOrderedRing Ainf]
    {d : ℕ} [Nonempty (Fin d)] {I : Type*}
    (φn : ∀ n, StarProbabilitySpace (A n)) (φ : StarProbabilitySpace Ainf)
    (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ I))
    (g : ∀ n, I → A n) (ginf : I → Ainf) (m : ℕ)
    (hwords : ∀ k : polyIdx (P ^ m),
      Tendsto (fun n => (φn n).expectation (wordProd (g n) (polyW (P ^ m) k))) atTop
        (𝓝 (φ.expectation (wordProd ginf (polyW (P ^ m) k))))) :
    Tendsto (fun n => (matrixStarState (D := Fin d) (φn n)).expectation
        ((evalMatrixPoly P (g n)) ^ m)) atTop
      (𝓝 ((matrixStarState (D := Fin d) φ).expectation
        ((evalMatrixPoly P ginf) ^ m))) := by
  have hbase := tendsto_state_trace_pow_evalMatrixPoly φn φ P g ginf m hwords
  have hfun : (fun n => (matrixStarState (D := Fin d) (φn n)).expectation
        ((evalMatrixPoly P (g n)) ^ m))
      = fun n => ((Fintype.card (Fin d) : ℂ))⁻¹ *
          (φn n).expectation (Matrix.trace ((evalMatrixPoly P (g n)) ^ m)) := by
    funext n
    exact matrixStarState_expectation_eq_trace (φn n) _
  rw [hfun]
  have hlim : ((matrixStarState (D := Fin d) φ).expectation
        ((evalMatrixPoly P ginf) ^ m))
      = ((Fintype.card (Fin d) : ℂ))⁻¹ *
          φ.expectation (Matrix.trace ((evalMatrixPoly P ginf) ^ m)) :=
    matrixStarState_expectation_eq_trace φ _
  rw [hlim]
  exact Tendsto.const_mul _ hbase

end GUEStrongConvergence
