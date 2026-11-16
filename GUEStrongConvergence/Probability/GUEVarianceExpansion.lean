/-
# R2 for the two-trace graph: eliminating the closed-walk conditions

This file applies Worker C's R2 reindexing (`sum_closedWalk_eq_sum_vertex`) to both walks of the
two-trace delta moment `gueTwoTraceDelta`.  The result

`gueTwoTraceDelta N w₁ w₂ =
  ∑ u₁ : Fin k₁ → Fin N, ∑ u₂ : Fin k₂ → Fin N,
    ∑ p : GUEPairing (guePairEntries w₁ w₂ (u₁ last) (u₂ last) u₁ u₂), gueDeltaWeight _ p`

removes the explicit start/destination sums and the two closing conditions, leaving a sum over two
cyclic vertex functions and pairings of the induced entry list.  This is the input for the
positional slot description (`guePairEntries_eq_ofFn`) and the label/index factorization.

The remaining steps to the full expansion are:
* reindex `(u₁, u₂) ↦ V = twoWalkVertex (u₁ last) (u₂ last) u₁ u₂` (a cyclic shift bijection);
* transport pairings of the `V`-dependent entry list to a canonical list (`GUEPairing.castLength`),
  and use `gueIndexWeight_eq_prod_partner` + `sum_slotEntry_gueIndexCov_eq_pow` for the index sum;
* split the pairings into block-diagonal and cross parts (`twoWalkLoopCount_sumCongr`) and use
  `twoWalkLoopCount_cross_le` for the cross bound.
-/
import GUEStrongConvergence.Probability.GUEWordSecondMoment
import GUEStrongConvergence.Probability.GUEWalkVertices
import GUEStrongConvergence.Probability.GUEWordVarianceReindex

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Matrix ENNReal Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

namespace GUEStrongConvergence

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- **R2 for the two-trace graph**: the two-trace delta moment is a sum over two cyclic vertex
functions and pairings of the induced entry list, with no closing conditions. -/
theorem gueTwoTraceDelta_eq_sum_vertex (w₁ w₂ : List ι)
    (h₁ : 1 ≤ w₁.length) (h₂ : 1 ≤ w₂.length) :
    gueTwoTraceDelta N w₁ w₂ =
      ∑ u₁ : Fin w₁.length → Fin N, ∑ u₂ : Fin w₂.length → Fin N,
        ∑ p : GUEPairing (guePairEntries w₁ w₂ (u₁ (cyclicLastIdx h₁))
          (u₂ (cyclicLastIdx h₂)) u₁ u₂), gueDeltaWeight _ p := by
  classical
  -- split the conjunction of the two closing conditions
  have hsplit : ∀ (a b : Fin N) (d : Fin w₁.length → Fin N) (e : Fin w₂.length → Fin N),
      (if (guePathLast a w₁ d = a ∧ guePathLast b w₂ e = b) then
        ∑ p : GUEPairing (guePairEntries w₁ w₂ a b d e), gueDeltaWeight _ p else 0) =
      (if guePathLast a w₁ d = a then
        (if guePathLast b w₂ e = b then
          ∑ p : GUEPairing (guePairEntries w₁ w₂ a b d e), gueDeltaWeight _ p else 0)
        else 0) := by
    intro a b d e
    by_cases h1 : guePathLast a w₁ d = a <;> by_cases h2 : guePathLast b w₂ e = b <;>
      simp [h1, h2]
  simp only [gueTwoTraceDelta]
  simp_rw [hsplit]
  -- swap the `b` and `d` sums so that the `(a, d)` walk sums are adjacent
  have hswap : (∑ a : Fin N, ∑ b : Fin N, ∑ d : (Fin w₁.length → Fin N),
        ∑ e : (Fin w₂.length → Fin N),
        (if guePathLast a w₁ d = a then
          (if guePathLast b w₂ e = b then
            ∑ p : GUEPairing (guePairEntries w₁ w₂ a b d e), gueDeltaWeight _ p else 0)
          else 0)) =
      ∑ a : Fin N, ∑ d : (Fin w₁.length → Fin N), ∑ b : Fin N,
        ∑ e : (Fin w₂.length → Fin N),
        (if guePathLast a w₁ d = a then
          (if guePathLast b w₂ e = b then
            ∑ p : GUEPairing (guePairEntries w₁ w₂ a b d e), gueDeltaWeight _ p else 0)
          else 0) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    exact Finset.sum_comm
  rw [hswap]
  -- pull the `a`-closing condition out of the `(b, e)` sums
  have hpull : ∀ (a : Fin N) (d : Fin w₁.length → Fin N),
      (∑ b : Fin N, ∑ e : (Fin w₂.length → Fin N),
        (if guePathLast a w₁ d = a then
          (if guePathLast b w₂ e = b then
            ∑ p : GUEPairing (guePairEntries w₁ w₂ a b d e), gueDeltaWeight _ p else 0)
          else 0)) =
      (if guePathLast a w₁ d = a then
        (∑ b : Fin N, ∑ e : (Fin w₂.length → Fin N),
          (if guePathLast b w₂ e = b then
            ∑ p : GUEPairing (guePairEntries w₁ w₂ a b d e), gueDeltaWeight _ p else 0))
        else 0) := by
    intro a d
    by_cases h1 : guePathLast a w₁ d = a <;> simp [h1]
  simp_rw [hpull]
  -- apply R2 to the first walk
  rw [sum_closedWalk_eq_sum_vertex w₁ h₁
    (fun a d => ∑ b : Fin N, ∑ e : (Fin w₂.length → Fin N),
      (if guePathLast b w₂ e = b then
        ∑ p : GUEPairing (guePairEntries w₁ w₂ a b d e), gueDeltaWeight _ p else 0))]
  -- apply R2 to the second walk
  refine Finset.sum_congr rfl fun u₁ _ => ?_
  exact sum_closedWalk_eq_sum_vertex w₂ h₂
    (fun b e => ∑ p : GUEPairing (guePairEntries w₁ w₂ (u₁ (cyclicLastIdx h₁)) b u₁ e),
      gueDeltaWeight _ p)

end

end GUEStrongConvergence
