/-
# Concrete states and word identification for the GUE/semicircle model

The transfer theorem works with abstract states `ψ n` on `B n` and `φ` on `Binf`. This
module identifies the concrete instances needed for GUE:

* the GUE side is the normalized matrix state `matrixStarProbabilitySpace` on
  `Matrix (Fin N) (Fin N) ℂ`, and its value on `wordProd` of the normalized GUE tuple is
  exactly the project's `gueNormTrace`;
* the limit side is the vacuum state on the closed semicircular algebra, and its value on
  `wordProd` of the semicircular family is the free joint word moment.

Consequently the moment hypothesis of the transfer reduces to scalar word convergence of
`gueNormTrace`.
-/
import GUEStrongConvergence.StrongConvergence.Target
import GUEStrongConvergence.Linearization.NilpotentShift
import GUEStrongConvergence.Probability.GUETraceWords
import FreeProbability.Matrix.NormalizedTrace

noncomputable section

namespace GUEStrongConvergence

open Filter MeasureTheory FreeProbability FreeProbability.Fock
open scoped ComplexOrder Topology

/-- The GUE word product is the project's `gueWord`. -/
lemma wordProd_gueMatrixOn_eq_gueWord (r N : ℕ) (x : CommonSpace (Fin r)) (w : List (Fin r)) :
    wordProd (fun i => gueMatrixOn x N i) w = gueWord w (x N) := rfl

/-- **GUE-side identification.** The normalized matrix state evaluated on a word product of
the GUE tuple is exactly the normalized trace word. -/
theorem matrixStarProbabilitySpace_expectation_wordProd_gueFamily
    (r N : ℕ) [Nonempty (Fin N)] (x : CommonSpace (Fin r)) (w : List (Fin r)) :
    (matrixStarProbabilitySpace (Fin N)).expectation
        (wordProd (gueFamily r N x) w)
      = gueNormTrace (N := N) w (x N) := by
  change (matrixStarProbabilitySpace (Fin N)).expectation
      (wordProd (fun i => gueMatrixOn x N i) w) = gueNormTrace (N := N) w (x N)
  rw [wordProd_gueMatrixOn_eq_gueWord]
  simp [matrixStarProbabilitySpace, matrixProbabilitySpace, normalizedTrace_apply, gueNormTrace,
    Fintype.card_fin]

/-- **Limit-side identification.** The vacuum state evaluated on a word product of the free
semicircular family is the free joint word moment. -/
theorem closedGeneratedVacuumState_expectation_wordProd_semicircularFamily
    (r : ℕ) (w : List (Fin r)) :
    (closedGeneratedVacuumState (Fin r)).expectation
        (wordProd (semicircularFamily r) w)
      = (closedGeneratedVacuumState (Fin r)).expectation
          ((w.map (fun i => closedSemicircular i)).prod) := by
  rfl

end GUEStrongConvergence
