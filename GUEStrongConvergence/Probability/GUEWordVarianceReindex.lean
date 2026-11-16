/-
# Positional description of the two-walk GUE surface

This file is the first step of the reindexing of `gueTwoTraceDelta` (the two-trace delta moment of
`GUEWordSecondMoment`) into the slot form counted by `sum_twoWalk_index_eq_pow`.

The data of `gueTwoTraceDelta` is a pair of closed walks, i.e. a start index `a` and destination
function `d` for the word `w₁` with `guePathLast a w₁ d = a`, and the same `(b, e)` for `w₂`.  The
two-walk vertex function is

`twoWalkVertex a b d e : Fin (w₁.length + w₂.length) → Fin N`,

the concatenation of the vertex functions `walkVertex a d` and `walkVertex b e` (with their last
vertex identified with the first, by the closing conditions).

Main results:

* `guePathEntries_eq_ofFn_cyclic`: a *closed* walk's entry list is
  `List.ofFn (fun j => (w.get j, (v (castSucc j), v (castSucc (finRotate j)))))`, i.e. the end of
  the last entry is the first vertex (the cyclic successor `finRotate`).
* `guePairEntries_eq_ofFn` (**two-walk positional description**): the concatenated entry list of the
  two closed walks is
  `List.ofFn (fun i => ((w₁ ++ w₂).get i, (V i, V (blockSuccPerm k₁ k₂ i))))`,
  with `V = twoWalkVertex a b d e`.
The remaining reindexing steps (not proved here) are:
1. the bijection between closed-walk data `(a, d, b, e)` and vertex functions `V` on the slots,
   and between pairings of the (varying) entry list and fixed-point-free involutions `σ` of
   `Fin (k₁ + k₂)`;
2. the positional product identity
   `gueIndexWeight l p = ∏ i, gueIndexCov (l.get i) (l.get (partner l p i))`;
3. combining these with `gueDeltaWeight_eq_label_mul_index`, `sum_twoWalk_index_eq_pow` and the
   label weights to obtain the two-trace slot expansion `∑_σ labelW(σ) N ^ L(σ)`.
-/
import GUEStrongConvergence.Probability.GUEWordVarianceBound
import GUEStrongConvergence.Probability.GUEWalkVertices

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

/-! ### The two-walk vertex function -/

/-- The vertex function of a pair of walks over `w₁` and `w₂`, indexed by the `k₁ + k₂` slots:
block 1 is `walkVertex a d` and block 2 is `walkVertex b e`, both truncated to their `kᵢ` cyclic
vertices. -/
def twoWalkVertex (a b : Fin N) {k₁ k₂ : ℕ} (d : Fin k₁ → Fin N) (e : Fin k₂ → Fin N) :
    Fin (k₁ + k₂) → Fin N :=
  Fin.append (fun j => walkVertex a d j.castSucc) (fun j => walkVertex b e j.castSucc)

@[simp] lemma twoWalkVertex_castAdd {k₁ k₂ : ℕ} (a b : Fin N) (d : Fin k₁ → Fin N)
    (e : Fin k₂ → Fin N) (j : Fin k₁) :
    twoWalkVertex a b d e (Fin.castAdd k₂ j) = walkVertex a d j.castSucc := by
  simp [twoWalkVertex]

@[simp] lemma twoWalkVertex_natAdd {k₁ k₂ : ℕ} (a b : Fin N) (d : Fin k₁ → Fin N)
    (e : Fin k₂ → Fin N) (j : Fin k₂) :
    twoWalkVertex a b d e (Fin.natAdd k₁ j) = walkVertex b e j.castSucc := by
  simp [twoWalkVertex]

/-! ### The two-block successor on each block -/

/-- The two-block successor advances the first block cyclically. -/
theorem blockSuccPerm_castAdd (k₁ k₂ : ℕ) (j : Fin k₁) :
    blockSuccPerm k₁ k₂ (Fin.castAdd k₂ j) = Fin.castAdd k₂ (finRotate k₁ j) := by
  simpa using blockSuccPerm_inl k₁ k₂ j

/-- The two-block successor advances the second block cyclically. -/
theorem blockSuccPerm_natAdd (k₁ k₂ : ℕ) (j : Fin k₂) :
    blockSuccPerm k₁ k₂ (Fin.natAdd k₁ j) = Fin.natAdd k₁ (finRotate k₂ j) := by
  simpa using blockSuccPerm_inr k₁ k₂ j

/-! ### A closed walk in cyclic form -/

/-- **A closed walk in cyclic form**: the end vertex of the last entry is the start vertex, so the
entry list is described by the cyclic successor `finRotate` on the `k` walk positions. -/
theorem guePathEntries_eq_ofFn_cyclic (w : List ι) (a : Fin N) (d : Fin w.length → Fin N)
    (h : guePathLast a w d = a) :
    guePathEntries a w d =
      List.ofFn (fun j : Fin w.length =>
        (w.get j, (walkVertex a d j.castSucc,
          walkVertex a d (finRotate w.length j).castSucc))) := by
  rw [guePathEntries_eq_ofFn]
  congr 1
  funext j
  congr 1
  cases w with
  | nil => exact Fin.elim0 j
  | cons x w' =>
    simp only [List.length_cons]
    by_cases hj : j = Fin.last w'.length
    · subst hj
      rw [finRotate_last, Fin.castSucc_zero, walkVertex_zero]
      change (walkVertex a d (Fin.last w'.length).castSucc,
        walkVertex a d (Fin.last (x :: w').length)) =
        (walkVertex a d (Fin.last w'.length).castSucc, a)
      rw [walkVertex_last, h]
    · have hrot : (finRotate (w'.length + 1) j).castSucc = j.succ := by
        ext
        rw [Fin.val_castSucc, coe_finRotate_of_ne_last hj, Fin.val_succ]
      rw [hrot]

/-! ### Labels along the concatenated word -/

/-- The label at a slot of the concatenated word. -/
def twoWalkLabel (w₁ w₂ : List ι) (i : Fin (w₁.length + w₂.length)) : ι :=
  (w₁ ++ w₂).get (Fin.cast (by simp) i)

/-- The label at a position of the first block is the label of the first word. -/
theorem twoWalkLabel_castAdd (w₁ w₂ : List ι) (j : Fin w₁.length) :
    twoWalkLabel w₁ w₂ (Fin.castAdd w₂.length j) = w₁.get j := by
  unfold twoWalkLabel
  rw [List.get_eq_getElem, List.get_eq_getElem]
  simp only [Fin.val_castAdd, Fin.val_cast]
  rw [List.getElem_append_left (by simp)]

/-- The label at a position of the second block is the label of the second word. -/
theorem twoWalkLabel_natAdd (w₁ w₂ : List ι) (j : Fin w₂.length) :
    twoWalkLabel w₁ w₂ (Fin.natAdd w₁.length j) = w₂.get j := by
  unfold twoWalkLabel
  rw [List.get_eq_getElem, List.get_eq_getElem]
  simp only [Fin.val_natAdd, Fin.val_cast]
  rw [List.getElem_append_right (by simp)]
  congr 1
  simp

/-! ### The two-walk positional description -/

/-- **Two-walk positional description**: for two closed walks, the concatenated entry list is the
slot list `i ↦ (label i, (V i, V (blockSucc i)))`. -/
theorem guePairEntries_eq_ofFn (w₁ w₂ : List ι) (a b : Fin N)
    (d : Fin w₁.length → Fin N) (e : Fin w₂.length → Fin N)
    (h1 : guePathLast a w₁ d = a) (h2 : guePathLast b w₂ e = b) :
    guePairEntries w₁ w₂ a b d e =
      List.ofFn (fun i : Fin (w₁.length + w₂.length) =>
        (twoWalkLabel w₁ w₂ i,
          (twoWalkVertex a b d e i,
            twoWalkVertex a b d e (blockSuccPerm w₁.length w₂.length i)))) := by
  rw [guePairEntries, guePathEntries_eq_ofFn_cyclic w₁ a d h1,
    guePathEntries_eq_ofFn_cyclic w₂ b e h2, ← List.ofFn_fin_append]
  congr 1
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.append_left, twoWalkVertex_castAdd, blockSuccPerm_castAdd,
      twoWalkLabel_castAdd]
  · simp only [Fin.append_right, twoWalkVertex_natAdd, blockSuccPerm_natAdd,
      twoWalkLabel_natAdd]

end

end GUEStrongConvergence
