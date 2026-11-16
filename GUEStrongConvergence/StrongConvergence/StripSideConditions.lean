/-
# The weighted-strip chain with the deterministic hypotheses discharged

`FlatLemmaM r k F z g C` is the `O(N⁻²)` mean-comparison input of the flat side.  Its only
non-deterministic input is the weighted strip bound; `flatLemmaM_of_weightedStrip_order`
(`StrongConvergence/FinalReduction.lean`) reduces it to the strip bound plus four deterministic
hypotheses (`hstat`, `hlim0`, `hIntN`, `hIntLim`).

This file removes those four for the canonical pencil `(pencilConstCoeff k F z,
pencilDirCoeff k F)`:

* `hstat` is `integral_flatStat_eq_gueStatisticCfc_canonical`
  (`Probability/KroneckerIdentity.lean`), unconditional for continuous `g`;
* `hlim0` is `guePlaneLimitOrder_eq_zero_of_isSmoothCutoffZeroOn`
  (`Probability/LimitSideIdentifications.lean`), i.e. the cutoff vanishing plus the spectral
  inclusion;
* `hIntN` is `eventually_integrable_dbarNumOrder_mul_trace_gueResolventMean`
  (`Probability/LimitBridge.lean`), unconditional;
* `hIntLim` is `integrable_dbarNumOrder_mul_trace_operatorMatrixPencilCauchy_fin`
  (`Probability/LimitSideIdentifications.lean`), unconditional.

**Main result**: `flatLemmaM_of_weightedStrip_of_spectralInclusion`, whose only hypotheses
besides the strip bound are the cutoff data and the single spectral inclusion
`spectrum ℝ (closedPencil (pencilCoeffDim k F) …) ⊆ specC (h1PencilLimit r k F z)`.
-/
import GUEStrongConvergence.Probability.LimitSideIdentifications
import GUEStrongConvergence.StrongConvergence.FinalReduction

open Filter MeasureTheory ProbabilityTheory FreeProbability FreeProbability.Fock Matrix
open scoped BigOperators ComplexOrder ENNReal NNReal Pointwise Topology

namespace GUEStrongConvergence

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

variable {r : ℕ}

local instance stripSideNontrivial : Nontrivial (closedSemicircularAlgebra (Fin r)) :=
  (closedGeneratedVacuumState (Fin r)).toProbabilitySpace.nontrivial

local instance stripSidePartialOrder : PartialOrder (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrder _

local instance stripSideStarOrderedRing : StarOrderedRing (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrderedRing _

/-- **`FlatLemmaM` from the weighted strip bound and the spectral inclusion only.**

All four deterministic hypotheses of `flatLemmaM_of_weightedStrip_order` are derived.  The
cutoff `g` is a smooth cutoff vanishing on `specC (h1PencilLimit r k F z)`, and the single
remaining geometric input is that this set contains the spectrum of the canonical limit element
`closedPencil (pencilConstCoeff k F z) (pencilDirCoeff k F)`. -/
theorem flatLemmaM_of_weightedStrip_of_spectralInclusion {k : ℕ} {F : RatPolyIdx r (k + 1)}
    {z : ℝ} {g : ℝ → ℝ} {m : ℕ} (hm : 1 ≤ m) {η₀ C_s β ε : ℝ} (hη₀2 : 2 < η₀)
    (hC_s : 0 ≤ C_s) (hβ0 : 0 ≤ β) (hβm : β < m) (hg : ContDiff ℝ (m + 1) g)
    (hgc : HasCompactSupport g)
    (hstrip : WeightedStripBound (pencilConstCoeff k F z) (pencilDirCoeff k F) m η₀ C_s β)
    (hcut : IsSmoothCutoffZeroOn (specC (h1PencilLimit r k F z)) ε g)
    (hsub : spectrum ℝ (closedPencil (n := Fin (pencilCoeffDim k F))
        (pencilConstCoeff k F z) (pencilDirCoeff k F)) ⊆ specC (h1PencilLimit r k F z)) :
    FlatLemmaM r k F z g (weightedStripConstant g m C_s β) := by
  haveI : NeZero (pencilCoeffDim k F) := ⟨Nat.ne_of_gt (pencilCoeffDim_pos r k F)⟩
  refine flatLemmaM_of_weightedStrip_order (pencilConstCoeff k F z) (pencilDirCoeff k F)
    (pencilConstCoeff_isHermitian k F z) (pencilDirCoeff_isHermitian k F) hm hη₀2 hC_s hβ0
    hβm hg hgc hstrip ?_ ?_ ?_ ?_
  · intro N
    exact integral_flatStat_eq_gueStatisticCfc_canonical k F N z hg.continuous
  · exact guePlaneLimitOrder_eq_zero_of_isSmoothCutoffZeroOn hm
      (pencilConstCoeff_isHermitian k F z) (pencilDirCoeff_isHermitian k F) hcut hsub hg le_rfl hgc
  · exact eventually_integrable_dbarNumOrder_mul_trace_gueResolventMean
      (pencilConstCoeff k F z) (pencilDirCoeff k F)
      (pencilConstCoeff_isHermitian k F z) (pencilDirCoeff_isHermitian k F) hm hg le_rfl hgc
  · exact integrable_dbarNumOrder_mul_trace_operatorMatrixPencilCauchy_fin (pencilCoeffDim k F)
      (pencilConstCoeff k F z) (pencilDirCoeff k F)
      (pencilConstCoeff_isHermitian k F z) (pencilDirCoeff_isHermitian k F) hm hg le_rfl hgc

/-- **The `(W)`-form for the derivative square.**  The same reduction for the test function
`(g')²`, which is the other cutoff consumed by the smooth Lemma M chain. -/
theorem flatLemmaM_deriv_of_weightedStrip_of_spectralInclusion {k : ℕ}
    {F : RatPolyIdx r (k + 1)} {z : ℝ} {g : ℝ → ℝ} {m : ℕ} (hm : 1 ≤ m)
    {η₀ C_s β ε : ℝ} (hη₀2 : 2 < η₀) (hC_s : 0 ≤ C_s) (hβ0 : 0 ≤ β) (hβm : β < m)
    (hgw : ContDiff ℝ (m + 1) (fun y => (deriv g y) ^ 2))
    (hgcw : HasCompactSupport (fun y => (deriv g y) ^ 2))
    (hstrip : WeightedStripBound (pencilConstCoeff k F z) (pencilDirCoeff k F) m η₀ C_s β)
    (hcutw : IsSmoothCutoffZeroOn (specC (h1PencilLimit r k F z)) ε
      (fun y => (deriv g y) ^ 2))
    (hsub : spectrum ℝ (closedPencil (n := Fin (pencilCoeffDim k F))
        (pencilConstCoeff k F z) (pencilDirCoeff k F)) ⊆ specC (h1PencilLimit r k F z)) :
    FlatLemmaM r k F z (fun y => (deriv g y) ^ 2)
      (weightedStripConstant (fun y => (deriv g y) ^ 2) m C_s β) :=
  flatLemmaM_of_weightedStrip_of_spectralInclusion hm hη₀2 hC_s hβ0 hβm hgw hgcw hstrip hcutw hsub

end

end GUEStrongConvergence
