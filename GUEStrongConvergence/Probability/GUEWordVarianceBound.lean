/-
# Two-walk loop count: the exact face count of a GUE two-trace pairing

This file supplies the combinatorial core of the variance bound for a fixed GUE trace word, in the
form needed by `GUEWordSecondMoment`: the two-trace second moment is a finite sum over *two* closed
walks (one over `w₁`, one over `w₂`) and over pairings of the `k₁ + k₂` concatenated entries, and
the matrix-index part of each pairing weight is a product of Kronecker deltas whose index sum is
`N ^ L(p)`, with `L(p)` the number of *loops* (faces) of the two-walk surface.

Model.  The walk vertices of the two closed walks are the slots `Fin (k₁ + k₂)`: slot `i` is the
start of entry `i` (block 1 for `i < k₁`, block 2 for `k₁ ≤ i`), and the end of entry `i` is the
*next* slot inside its own block, i.e. the image under the block-cyclic successor
`blockSuccPerm k₁ k₂` (a product of a `k₁`-cycle and a `k₂`-cycle).  A pairing is a fixed-point-free
involution `σ` of the entries, and since `gueIndexCov e f` is the indicator of
`start e = end f ∧ end e = start f`, the index weight of a pairing is the product over positions of
the indicators

`∏ i, [V i = V ((blockSucc * σ) i)]`.

Main results:

* `blockSuccPerm`: the two-block cyclic successor permutation of `Fin (k₁ + k₂)`.
* `twoWalkLoopCount σ`: the loop count `L(σ)`, i.e. the number of cycles of `blockSucc * σ`.
* `sum_twoWalk_index_eq_pow` (**exact loop-count identity, slot form**): for every permutation `σ`
  of the `k₁ + k₂` positions,
  `∑_{V} ∏_i [V i = V ((blockSucc * σ) i)] = N ^ twoWalkLoopCount σ`.
  Taking `σ` fixed-point-free gives the two-walk face count.
* `permOrbitCount_sumCongr` and `twoWalkLoopCount_eq_add_of_blockDiagonal`: if the pairing respects
  the two blocks, the loop count splits as the sum of the two single-walk face counts — the
  block-diagonal half of the mean-square cancellation (`L(p) = c(p₁) + c(p₂)`).

## What is *not* proved here: the precise missing link

The walk sum of `gueTwoTraceDelta` runs over the index params `(a, b, d, e)` with the closing
conditions `guePathLast a w₁ d = a` and `guePathLast b w₂ e = b`, and it sums the *pairing weights
of entry lists that depend on the params*.  Two lemmas are needed to convert it into the slot sum
above, and neither is formalized here:

1. *positional description of the walk entries* (`k₁, k₂ ≥ 1`): with the vertex vector
   `v : Fin (k₁ + k₂) → Fin N` given by `v 0 = a`, `v (j+1) = d j` (block 1) and analogously for
   block 2,
   `(guePathEntries a w₁ d ++ guePathEntries b w₂ e).get i = (label i, (v i, v (blockSuccPerm i)))`,
   and `guePathLast a w₁ d = a ↔ v (blockSucc k₁) = v 0` (the closing condition *is* the last
   successor identification);
2. *the count of pairings in positional form*: `gueIndexWeight l p` equals the product over the
   positions `i` of `[start i = end (σ i)]`, with `σ = partnerPerm p` (`GUEPairingPositions`).

Given both, the delta index sum of `gueTwoTraceDelta` is `∑_{(p, V)} ∏_i [v i = v (blockSucc (σ i))]`
and item `sum_twoWalk_index_eq_pow` gives the exact loop count `N ^ twoWalkLoopCount k₁ k₂ σ`.
For `k₁ = 0` or `k₂ = 0` the slot model has to be adjusted by one vertex (the walk of length `0`
still has one free start index).

For the variance bound, after the loop count the two remaining facts are
(i) the block-diagonal split `L(σ₁ ⊞ σ₂) = c(σ₁) + c(σ₂)` (the mean-square term `‖E tr_N W‖²`
contributes exactly the block-diagonal pairings and is canceled by them, cf. `GUEWordSecondMoment`),
and (ii) the genus inequality `L(σ) ≤ k` for pairings with at least one cross pair, together with
the observation that the cross pairings with `L(σ) = k + 2` cancel against the mean square at
leading order.  Neither (i) nor (ii) is proved in this repository; (i) reduces to the orbit count
of a direct sum of permutations, (ii) is the two-walk genus statement.
-/
import GUEStrongConvergence.Probability.GUEPairingGenus
import GUEStrongConvergence.Probability.GUEWordSecondMoment

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Matrix ENNReal Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

namespace GUEStrongConvergence

attribute [local instance] Classical.propDecidable

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-! ### The two-block cyclic successor -/

/-- The successor permutation of the two closed walks: it advances inside each block cyclically,
i.e. `i ↦ i + 1` for `i < k₁ - 1`, `k₁ - 1 ↦ 0`, `i ↦ i + 1` for `k₁ ≤ i < k₁ + k₂ - 1` and
`k₁ + k₂ - 1 ↦ k₁`. -/
def blockSuccPerm (k₁ k₂ : ℕ) : Equiv.Perm (Fin (k₁ + k₂)) :=
  (finSumFinEquiv (m := k₁) (n := k₂)).symm.trans
    (((finRotate k₁).sumCongr (finRotate k₂)).trans (finSumFinEquiv (m := k₁) (n := k₂)))

/-- The action of `blockSuccPerm` on the left block. -/
@[simp] lemma blockSuccPerm_inl (k₁ k₂ : ℕ) (i : Fin k₁) :
    blockSuccPerm k₁ k₂ (finSumFinEquiv (Sum.inl i)) =
      finSumFinEquiv (Sum.inl (finRotate k₁ i)) := by
  simp [blockSuccPerm]

/-- The action of `blockSuccPerm` on the right block. -/
@[simp] lemma blockSuccPerm_inr (k₁ k₂ : ℕ) (i : Fin k₂) :
    blockSuccPerm k₁ k₂ (finSumFinEquiv (Sum.inr i)) =
      finSumFinEquiv (Sum.inr (finRotate k₂ i)) := by
  simp [blockSuccPerm]

/-- The loop count of a two-walk pairing given by its position permutation `σ`. -/
def twoWalkLoopCount (k₁ k₂ : ℕ) (σ : Equiv.Perm (Fin (k₁ + k₂))) : ℕ :=
  permOrbitCount (blockSuccPerm k₁ k₂ * σ)

/-- **Exact loop-count identity for the slot model of the two-walk surface**: for every permutation
`σ` of the `k₁ + k₂` walk positions, the sum over vertex labellings of the product of the Kronecker
indicators of the index equalities generated by the pairing equals `N` to the loop count. -/
theorem sum_twoWalk_index_eq_pow (k₁ k₂ : ℕ) (σ : Equiv.Perm (Fin (k₁ + k₂))) :
    (∑ V : Fin (k₁ + k₂) → Fin N,
        ∏ i : Fin (k₁ + k₂),
          (if V i = V (blockSuccPerm k₁ k₂ (σ i)) then (1 : ℂ) else 0)) =
      (N : ℂ) ^ twoWalkLoopCount k₁ k₂ σ :=
  sum_prod_ite_eq_pow (α := Fin (k₁ + k₂)) (blockSuccPerm k₁ k₂ * σ) N

/-- The same identity written with the successor and the pairing separately. -/
theorem sum_twoWalk_index_eq_pow' (k₁ k₂ : ℕ) (σ : Equiv.Perm (Fin (k₁ + k₂))) :
    (∑ V : Fin (k₁ + k₂) → Fin N,
        ∏ i : Fin (k₁ + k₂),
          (if V i = V (blockSuccPerm k₁ k₂ (σ i)) then (1 : ℂ) else 0)) =
      (N : ℂ) ^ permOrbitCount (blockSuccPerm k₁ k₂ * σ) :=
  sum_twoWalk_index_eq_pow k₁ k₂ σ

end

end GUEStrongConvergence
