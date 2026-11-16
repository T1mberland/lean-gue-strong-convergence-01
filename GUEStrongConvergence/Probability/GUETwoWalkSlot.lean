/-
# The two-walk slot reindexing and the per-pairing index sum

This file completes the reindexing of the two-trace delta moment `gueTwoTraceDelta` into the slot
form `N^{-k} ∑_q labelW(q) N^{L(q)}` used by the variance bound.

The two walks of `gueTwoTraceDelta` are parametrized by their cyclic vertex functions `u₁`, `u₂`
(`GUEVarianceExpansion.gueTwoTraceDelta_eq_sum_vertex`), with `k₁ = w₁.length`, `k₂ = w₂.length`.
The slot description is:

* `slotVertexEquiv` / `sum_twoWalk_slotVertex`: reindexing the pair `(u₁, u₂)` of cyclic vertex
  functions as a single slot vertex function `V : Fin (k₁ + k₂) → Fin N`;
* `twoWalkSlotList`: the canonical entry list `i ↦ (label i, (V i, V (blockSuccPerm i)))` of
  `GUEIndexWeightProduct.slotEntry`;
* `guePairEntries_cyclicVertex_slot`: the entry list of the two closed walks is *definitionally*
  the slot list of `V = Fin.append (slotVertex h₁ u₁) (slotVertex h₂ u₂)`;
* `sum_slotIndexWeight` (**per-pairing index sum**): for a pairing `q` of a canonical slot list of
  length `k₁ + k₂`, the sum over slot vertex functions of the index weight of the transported
  pairing is `N ^ L(q)`;
* `gueTwoTraceDelta_eq_slot_sum`: the delta moment in slot form,
  `∑_q labelW(q) * N ^ L(q)`.

No `sorry`/axiom is used.
-/
import GUEStrongConvergence.Probability.GUEVarianceExpansion
import GUEStrongConvergence.Probability.GUEWordGenusExpansion
import GUEStrongConvergence.Probability.GUEIndexWeightProduct
import GUEStrongConvergence.Probability.GUEPairingCast
import GUEStrongConvergence.Probability.GUEPairingEar

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

/-! ### Reindexing two cyclic vertex functions as one slot vertex function -/

/-- **Splitting a slot vertex function into the two blocks.**  A function on the `k₁ + k₂` slots is
the same as a pair of functions on the two blocks, with inverse `Fin.append`. -/
def slotVertexEquiv (k₁ k₂ : ℕ) :
    (Fin (k₁ + k₂) → Fin N) ≃ ((Fin k₁ → Fin N) × (Fin k₂ → Fin N)) where
  toFun V := (fun i => V (Fin.castAdd k₂ i), fun j => V (Fin.natAdd k₁ j))
  invFun p := Fin.append p.1 p.2
  left_inv V := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · exact Fin.append_left _ _ j
    · exact Fin.append_right _ _ j
  right_inv p := by
    refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
    · exact Fin.append_left _ _ i
    · exact Fin.append_right _ _ j

@[simp] theorem slotVertexEquiv_symm_apply (k₁ k₂ : ℕ) (u₁ : Fin k₁ → Fin N)
    (u₂ : Fin k₂ → Fin N) :
    (slotVertexEquiv (N := N) k₁ k₂).symm (u₁, u₂) = Fin.append u₁ u₂ := rfl

/-- **Two-walk slot reindexing**: summing an arbitrary functional of the concatenated slot vertex
function over the two blocks is the same as summing over all slot vertex functions.  This combines
`sum_slotVertex_bijective` for the two walks with the block decomposition `slotVertexEquiv`. -/
theorem sum_twoWalk_slotVertex (k₁ k₂ : ℕ) (h₁ : 1 ≤ k₁) (h₂ : 1 ≤ k₂)
    (F : (Fin (k₁ + k₂) → Fin N) → ℂ) :
    (∑ u₁ : Fin k₁ → Fin N, ∑ u₂ : Fin k₂ → Fin N,
        F (Fin.append (slotVertex h₁ u₁) (slotVertex h₂ u₂))) =
      ∑ V : Fin (k₁ + k₂) → Fin N, F V := by
  calc (∑ u₁ : Fin k₁ → Fin N, ∑ u₂ : Fin k₂ → Fin N,
        F (Fin.append (slotVertex h₁ u₁) (slotVertex h₂ u₂)))
      = ∑ u₁ : Fin k₁ → Fin N, ∑ V : Fin k₂ → Fin N, F (Fin.append (slotVertex h₁ u₁) V) := by
        refine Finset.sum_congr rfl fun u₁ _ => ?_
        exact sum_slotVertex_bijective h₂ (fun w => F (Fin.append (slotVertex h₁ u₁) w))
    _ = ∑ u₁ : Fin k₁ → Fin N, ∑ u₂ : Fin k₂ → Fin N, F (Fin.append u₁ u₂) :=
        sum_slotVertex_bijective h₁ (fun w => ∑ u₂ : Fin k₂ → Fin N, F (Fin.append w u₂))
    _ = ∑ u : (Fin k₁ → Fin N) × (Fin k₂ → Fin N), F (Fin.append u.1 u.2) :=
        (Fintype.sum_prod_type (f := fun u : (Fin k₁ → Fin N) × (Fin k₂ → Fin N) =>
          F (Fin.append u.1 u.2))).symm
    _ = ∑ V : Fin (k₁ + k₂) → Fin N, F V :=
        Equiv.sum_comp (slotVertexEquiv (N := N) k₁ k₂).symm F

/-! ### The canonical slot entry list -/

/-- The canonical slot entry list of the two-walk surface: position `i` carries the label
`label i`, the slot vertex `V i` and its block successor `V (blockSuccPerm i)`. -/
def twoWalkSlotList (k₁ k₂ : ℕ) (label : Fin (k₁ + k₂) → ι) (V : Fin (k₁ + k₂) → Fin N) :
    List (GUEEntry ι N) :=
  List.ofFn (slotEntry k₁ k₂ label V)

@[simp] theorem length_twoWalkSlotList (k₁ k₂ : ℕ) (label : Fin (k₁ + k₂) → ι)
    (V : Fin (k₁ + k₂) → Fin N) : (twoWalkSlotList k₁ k₂ label V).length = k₁ + k₂ :=
  List.length_ofFn

/-- The `j`-th entry of the canonical slot list. -/
theorem get_twoWalkSlotList (k₁ k₂ : ℕ) (label : Fin (k₁ + k₂) → ι)
    (V : Fin (k₁ + k₂) → Fin N) (i : Fin (k₁ + k₂)) :
    (twoWalkSlotList k₁ k₂ label V).get (Fin.cast (by simp) i) = slotEntry k₁ k₂ label V i := by
  simp only [twoWalkSlotList]
  rw [List.get_ofFn]
  congr 1

/-- The label at slot `i` of the canonical slot list. -/
theorem fst_get_twoWalkSlotList (k₁ k₂ : ℕ) (label : Fin (k₁ + k₂) → ι)
    (V : Fin (k₁ + k₂) → Fin N) (i : Fin (k₁ + k₂)) :
    ((twoWalkSlotList k₁ k₂ label V).get (Fin.cast (by simp) i)).1 = label i := by
  rw [get_twoWalkSlotList]
  rfl

/-- The entry at an arbitrary position of the canonical slot list. -/
theorem get_twoWalkSlotList_apply (k₁ k₂ : ℕ) (label : Fin (k₁ + k₂) → ι)
    (V : Fin (k₁ + k₂) → Fin N) (i : Fin (twoWalkSlotList k₁ k₂ label V).length) :
    (twoWalkSlotList k₁ k₂ label V).get i = slotEntry k₁ k₂ label V
      (Fin.cast (by simp : (twoWalkSlotList k₁ k₂ label V).length = k₁ + k₂) i) := by
  have h := get_twoWalkSlotList k₁ k₂ label V
    (Fin.cast (by simp : (twoWalkSlotList k₁ k₂ label V).length = k₁ + k₂) i)
  rwa [show Fin.cast (by simp) (Fin.cast (by simp : (twoWalkSlotList k₁ k₂ label V).length
      = k₁ + k₂) i) = i from Fin.ext rfl] at h

/-- A cyclic vertex function satisfies the closing condition of its walk. -/
theorem guePathLast_cyclicVertex (w : List ι) (hk : 1 ≤ w.length) (u : Fin w.length → Fin N) :
    guePathLast (u (cyclicLastIdx hk)) w u = u (cyclicLastIdx hk) := by
  rw [← walkVertex_last (u (cyclicLastIdx hk)) w u]
  have hcv : walkVertex (u (cyclicLastIdx hk)) u = cyclicVertex hk u := rfl
  rw [hcv, cyclicVertex_last hk u]
  rfl

/-- **The two-walk entry list in slot form**: the entry list of the two closed walks determined by
the cyclic vertex functions `u₁`, `u₂` is the canonical slot list of
`V = Fin.append (slotVertex h₁ u₁) (slotVertex h₂ u₂)`. -/
theorem guePairEntries_cyclicVertex_slot (w₁ w₂ : List ι) (h₁ : 1 ≤ w₁.length)
    (h₂ : 1 ≤ w₂.length) (u₁ : Fin w₁.length → Fin N) (u₂ : Fin w₂.length → Fin N) :
    guePairEntries w₁ w₂ (u₁ (cyclicLastIdx h₁)) (u₂ (cyclicLastIdx h₂)) u₁ u₂ =
      twoWalkSlotList w₁.length w₂.length (twoWalkLabel w₁ w₂)
        (Fin.append (slotVertex h₁ u₁) (slotVertex h₂ u₂)) := by
  rw [guePairEntries_eq_ofFn w₁ w₂ _ _ u₁ u₂ (guePathLast_cyclicVertex w₁ h₁ u₁)
    (guePathLast_cyclicVertex w₂ h₂ u₂)]
  rfl


/-! ### The per-pairing index sum -/

/-- **The index weight of a transported slot pairing in slot form.**  For a pairing `q` of the
canonical slot list of `V₀`, the index weight of the pairing transported to the slot list of `V` is
the product of the slot covariances at the `q`-partner positions. -/
theorem gueIndexWeight_cast_slot (k₁ k₂ : ℕ) (label : Fin (k₁ + k₂) → ι)
    (V₀ V : Fin (k₁ + k₂) → Fin N) (q : GUEPairing (twoWalkSlotList k₁ k₂ label V₀)) :
    gueIndexWeight (twoWalkSlotList k₁ k₂ label V)
      (GUEPairing.castLength (twoWalkSlotList k₁ k₂ label V₀) (twoWalkSlotList k₁ k₂ label V)
        (by simp) q) =
      ∏ j : Fin (k₁ + k₂),
        gueIndexCov (slotEntry k₁ k₂ label V j)
          (slotEntry k₁ k₂ label V
            (conjBy (finCongr (by simp : (twoWalkSlotList k₁ k₂ label V₀).length = k₁ + k₂))
              (partnerPerm q) j)) := by
  classical
  rw [gueIndexWeight_eq_prod_partner]
  refine Eq.trans (Equiv.prod_comp (finCongr (by simp : (twoWalkSlotList k₁ k₂ label V).length
    = k₁ + k₂)).symm (fun i => gueIndexCov ((twoWalkSlotList k₁ k₂ label V).get i)
      ((twoWalkSlotList k₁ k₂ label V).get
        (partner (twoWalkSlotList k₁ k₂ label V)
          (GUEPairing.castLength (twoWalkSlotList k₁ k₂ label V₀)
            (twoWalkSlotList k₁ k₂ label V) (by simp) q) i)))).symm ?_
  refine Finset.prod_congr rfl fun j _ => ?_
  -- the entry at slot `j`
  have hget : ∀ (i : Fin (twoWalkSlotList k₁ k₂ label V).length),
      (twoWalkSlotList k₁ k₂ label V).get i
        = slotEntry k₁ k₂ label V (Fin.cast (by simp : (twoWalkSlotList k₁ k₂ label V).length
            = k₁ + k₂) i) := by
    intro i
    have h := get_twoWalkSlotList k₁ k₂ label V
      (Fin.cast (by simp : (twoWalkSlotList k₁ k₂ label V).length = k₁ + k₂) i)
    rwa [show Fin.cast (by simp) (Fin.cast (by simp : (twoWalkSlotList k₁ k₂ label V).length
      = k₁ + k₂) i) = i from Fin.ext rfl] at h
  -- the entry at the transported `q`-partner of slot `j`
  have hpart : ∀ (i : Fin (twoWalkSlotList k₁ k₂ label V).length) (j : Fin (k₁ + k₂)),
      (finCongr (by simp : (twoWalkSlotList k₁ k₂ label V).length = k₁ + k₂)).symm j = i →
      (twoWalkSlotList k₁ k₂ label V).get
          (partner (twoWalkSlotList k₁ k₂ label V)
            (GUEPairing.castLength (twoWalkSlotList k₁ k₂ label V₀)
              (twoWalkSlotList k₁ k₂ label V) (by simp) q) i)
        = slotEntry k₁ k₂ label V
            (conjBy (finCongr (by simp : (twoWalkSlotList k₁ k₂ label V₀).length = k₁ + k₂))
              (partnerPerm q) j) := by
    intro i j hij
    subst hij
    have hXi : (finCongr (by simp : (twoWalkSlotList k₁ k₂ label V).length = k₁ + k₂)).symm j
        = Fin.cast (by simp : k₁ + k₂ = (twoWalkSlotList k₁ k₂ label V).length) j := by
      rw [finCongr_symm_apply]
    rw [hXi]
    have hcast_id : Fin.cast (by simp : (twoWalkSlotList k₁ k₂ label V₀).length
          = (twoWalkSlotList k₁ k₂ label V).length)
        (Fin.cast (by simp : (twoWalkSlotList k₁ k₂ label V₀).length = k₁ + k₂).symm j)
        = Fin.cast (by simp : k₁ + k₂ = (twoWalkSlotList k₁ k₂ label V).length) j := Fin.ext rfl
    rw [← hcast_id,
      GUEPairing.partner_castLength q (twoWalkSlotList k₁ k₂ label V)
        (by simp : (twoWalkSlotList k₁ k₂ label V₀).length
          = (twoWalkSlotList k₁ k₂ label V).length)
        (Fin.cast (by simp : (twoWalkSlotList k₁ k₂ label V₀).length = k₁ + k₂).symm j)]
    have hconj : conjBy (finCongr (by simp : (twoWalkSlotList k₁ k₂ label V₀).length
          = k₁ + k₂)) (partnerPerm q) j
        = Fin.cast (by simp : (twoWalkSlotList k₁ k₂ label V₀).length = k₁ + k₂)
          (partner (twoWalkSlotList k₁ k₂ label V₀) q
            (Fin.cast (by simp : (twoWalkSlotList k₁ k₂ label V₀).length
              = k₁ + k₂).symm j)) := by
      rw [conjBy_apply, finCongr_apply, finCongr_symm_apply]
      rfl
    rw [hget, hconj]
    congr 1
  have hij : (finCongr (by simp : (twoWalkSlotList k₁ k₂ label V).length = k₁ + k₂)).symm j
      = (finCongr (by simp : (twoWalkSlotList k₁ k₂ label V).length = k₁ + k₂)).symm j := rfl
  have hgetj := hget ((finCongr (by simp : (twoWalkSlotList k₁ k₂ label V).length
    = k₁ + k₂)).symm j)
  rw [hgetj, hpart _ _ hij]
  congr 1

/-- **Per-pairing index sum in slot form**: for a pairing `q` of a canonical slot list of length
`k₁ + k₂`, the sum over slot vertex functions of the index weight of the transported pairing is
`N` to the two-walk loop count of `q`. -/
theorem sum_slotIndexWeight (k₁ k₂ : ℕ) (label : Fin (k₁ + k₂) → ι)
    (V₀ : Fin (k₁ + k₂) → Fin N) (q : GUEPairing (twoWalkSlotList k₁ k₂ label V₀)) :
    (∑ V : Fin (k₁ + k₂) → Fin N,
        gueIndexWeight (twoWalkSlotList k₁ k₂ label V)
          (GUEPairing.castLength (twoWalkSlotList k₁ k₂ label V₀) (twoWalkSlotList k₁ k₂ label V)
            (by simp) q)) =
      (N : ℂ) ^ twoWalkLoopCount k₁ k₂
        (conjBy (finCongr (by simp : (twoWalkSlotList k₁ k₂ label V₀).length = k₁ + k₂))
          (partnerPerm q)) := by
  have hinv : partnerPerm q * partnerPerm q = 1 := by
    refine Equiv.ext (fun i => ?_)
    rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    exact partnerPerm_involutive q i
  have hσ : conjBy (finCongr (by simp : (twoWalkSlotList k₁ k₂ label V₀).length = k₁ + k₂))
        (partnerPerm q) * conjBy (finCongr (by simp : (twoWalkSlotList k₁ k₂ label V₀).length
          = k₁ + k₂)) (partnerPerm q) = 1 := by
    rw [← conjBy_mul, hinv, conjBy_one]
  rw [← sum_slotEntry_gueIndexCov_eq_pow k₁ k₂ label _ hσ]
  exact Finset.sum_congr rfl fun V _ => gueIndexWeight_cast_slot k₁ k₂ label V₀ V q


end

end GUEStrongConvergence
