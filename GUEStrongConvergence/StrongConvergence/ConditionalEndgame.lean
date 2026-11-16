/-
# The single-hypothesis conditional endgame: the near-axis annulus

`StrongConvergence/PencilStripAbove.lean` proves that the pencil field of the corrected endgame
bundle follows from the near-axis annulus alone (`weightedStripDataAtRepair_of_annulus`), and
`Probability/ScalarPencilStrip.lean` proves the scalar field unconditionally
(`scalarWeightedStripDataAtRepair_unconditional`).  This file assembles the resulting
single-hypothesis conditional endgame:

* hypothesis: for every canonical linearization pencil `(pencilConstCoeff k F z,
  pencilDirCoeff k F)`, the averaged resolvent differs from its limit by `O(N⁻² |Im w|⁻⁷)` on the
  near-axis annulus `|Im w| < dysonThreshold (pencilDirCoeff k F)`;
* conclusion: `GUEStrongConvergenceStatement r`.

This is the *entire* remaining analytic content of the project as far as the endgame is
concerned.  No `sorry`, no new axioms.
-/
import GUEStrongConvergence.StrongConvergence.PencilStripAbove
import GUEStrongConvergence.Probability.ScalarPencilStrip

open Filter MeasureTheory ProbabilityTheory Matrix
open FreeProbability FreeProbability.Fock
open scoped Matrix.Norms.Frobenius ComplexOrder ENNReal NNReal Topology BigOperators

namespace GUEStrongConvergence

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

variable {r : ℕ}

/-- The pencil coefficient dimension is positive, as a local instance so that the annulus
threshold `dysonThreshold (pencilDirCoeff k F)` elaborates. -/
local instance conditionalPencilCoeffNonempty (k : ℕ) (F : RatPolyIdx r (k + 1)) :
    Nonempty (Fin (pencilCoeffDim k F)) :=
  ⟨⟨0, pencilCoeffDim_pos r k F⟩⟩

/-- **The project target from the near-axis annulus hypothesis alone.**

The scalar field is a theorem; the pencil field is `weightedStripDataAtRepair_of_annulus`; the two
are combined by `weightedStripInputsRepair_of_pencilField` and the corrected endgame
`GUEStrongConvergenceStatement_of_weightedStripInputsRepair`. -/
theorem GUEStrongConvergenceStatement_of_annulus (r : ℕ)
    (hann : ∀ (k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ), ∃ Cn : ℝ, 0 ≤ Cn ∧
      ∀ᶠ N : ℕ in atTop, ∀ w : ℂ, w.im ≠ 0 →
        |w.im| < dysonThreshold (pencilDirCoeff k F) →
        frob (gueResolventMean (N := N) (pencilConstCoeff k F z) (pencilDirCoeff k F) w -
              operatorMatrixPencilCauchy (pencilConstCoeff k F z) (pencilDirCoeff k F) w)
          ≤ Cn * (0 + ‖w‖) ^ 2 * |w.im| ^ (-(7 : ℝ)) / (N : ℝ) ^ 2) :
    GUEStrongConvergenceStatement r := by
  refine GUEStrongConvergenceStatement_of_weightedStripInputsRepair (r := r)
    (weightedStripInputsRepair_of_pencilField r ?_)
  intro k F z ε hε
  obtain ⟨Cn, hCn, hnear⟩ := hann k F z
  exact weightedStripDataAtRepair_of_annulus (r := r) hε hCn hnear

end

end GUEStrongConvergence
