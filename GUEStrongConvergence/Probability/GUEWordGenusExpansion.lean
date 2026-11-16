/-
# The exact genus expansion of a GUE trace-word moment, step 1: walk sum in vertex form

`integral_gueNormTrace_eq_delta_sum` (GUEWordMoments) writes the normalized moment of a trace word
as `N^{-(k/2+1)}` times a closed-walk sum of the delta weights over all pairings.  The R2
reindexing `sum_closedWalk_entries` (GUEWalkVertices) replaces the closed-walk sum by a sum over
cyclic vertex functions, which is the form in which the face count applies.
-/
import GUEStrongConvergence.Probability.GUEDeltaWeightProduct
import GUEStrongConvergence.Probability.GUEWordSecondMoment
import GUEStrongConvergence.Probability.GUEWordMoments
import GUEStrongConvergence.Probability.GUEWalkVertices
import GUEStrongConvergence.Probability.CyclicVertexSuccessor

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Matrix ENNReal Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GUEStrongConvergence

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- The vertex entry list of a cyclic vertex function of a nonempty word. -/
def gueVertexEntries (w : List ι) (hpos : 1 ≤ w.length) (u : Fin w.length → Fin N) :
    List (GUEEntry ι N) :=
  List.ofFn (fun i : Fin w.length =>
    (w.get i, (cyclicVertex hpos u i.castSucc, cyclicVertex hpos u i.succ)))

/-- **Genus expansion, step 1**: the normalized trace-word moment is `N^{-(k/2+1)}` times the sum
over cyclic vertex functions and pairings of the delta weights. -/
theorem integral_gueNormTrace_eq_sum_vertex (w : List ι) (hpos : 1 ≤ w.length) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), gueNormTrace w x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) =
      ((N : ℂ)⁻¹) ^ (w.length / 2 + 1) *
        ∑ u : Fin w.length → Fin N,
          ∑ p : GUEPairing (gueVertexEntries w hpos u),
            gueDeltaWeight (gueVertexEntries w hpos u) p := by
  rw [integral_gueNormTrace_eq_delta_sum,
    sum_closedWalk_entries w hpos
      (fun l => ∑ p : GUEPairing l, gueDeltaWeight l p)]
  rfl


/-- The label covariance is symmetric. -/
lemma gueLabelCov_comm (e f : GUEEntry ι N) : gueLabelCov e f = gueLabelCov f e := by
  simp only [gueLabelCov, eq_comm]

/-- The label covariance is idempotent. -/
lemma gueLabelCov_mul_self (e f : GUEEntry ι N) :
    gueLabelCov e f * gueLabelCov e f = gueLabelCov e f := by
  simp only [gueLabelCov]
  split_ifs <;> simp

/-- **Label/index product form of the delta weight**: the delta weight is the product of the label
product and the index product over the partner positions. -/
theorem gueDeltaWeight_eq_label_prod_index_prod (l : List (GUEEntry ι N)) (p : GUEPairing l) :
    gueDeltaWeight l p =
      (∏ i : Fin l.length, gueLabelCov (l.get i) (l.get (partner l p i))) *
        ∏ i : Fin l.length, gueIndexCov (l.get i) (l.get (partner l p i)) := by
  calc gueDeltaWeight l p
      = ∏ i : Fin l.length, gueDeltaCov (l.get i) (l.get (partner l p i)) :=
        gueDeltaWeight_eq_prod_partner l p
    _ = ∏ i : Fin l.length, (gueLabelCov (l.get i) (l.get (partner l p i)) *
          gueIndexCov (l.get i) (l.get (partner l p i))) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        exact gueDeltaCov_eq_label_mul_index _ _
    _ = _ := Finset.prod_mul_distrib

/-- **The label weight is the product of the label covariances over the partner positions**
(same proof as `gueDeltaWeight_eq_prod_partner`). -/
theorem gueLabelWeight_eq_prod_partner (l : List (GUEEntry ι N)) (p : GUEPairing l) :
    gueLabelWeight l p =
      ∏ i : Fin l.length, gueLabelCov (l.get i) (l.get (partner l p i)) := by
  induction p with
  | nil => simp [gueLabelWeight]
  | cons e l k p ih =>
    cases l with
    | nil => exact absurd k.isLt (by simp)
    | cons x l' =>
      rw [gueLabelWeight_cons, ih]
      have hlen : ((x :: l').eraseIdx k).length = l'.length := by
        rw [List.length_eraseIdx, ite_eq_left k.isLt]
        simp
      change gueLabelCov e ((x :: l').get k) *
          (∏ j : Fin ((x :: l').eraseIdx k).length,
            gueLabelCov (((x :: l').eraseIdx k).get j)
              (((x :: l').eraseIdx k).get (partner ((x :: l').eraseIdx k) p j))) =
        ∏ i : Fin (l'.length + 2),
          gueLabelCov ((e :: x :: l').get i)
            ((e :: x :: l').get (partner (e :: x :: l')
              (GUEPairing.cons e (x :: l') k p) i))
      rw [Fin.prod_univ_succ]
      have hF0 : gueLabelCov ((e :: x :: l').get 0)
            ((e :: x :: l').get (partner (e :: x :: l')
              (GUEPairing.cons e (x :: l') k p) 0)) =
          gueLabelCov e ((x :: l').get k) := by
        rw [partner_cons_zero]
        simp
      have hFks : gueLabelCov ((e :: x :: l').get k.succ)
            ((e :: x :: l').get (partner (e :: x :: l')
              (GUEPairing.cons e (x :: l') k p) k.succ)) =
          gueLabelCov e ((x :: l').get k) := by
        rw [partner_cons_head _ _ _ _ _ _ rfl]
        simp only [List.get_cons_zero]
        exact gueLabelCov_comm _ _
      rw [hF0, Finset.prod_eq_prod_sdiff_singleton_mul
        (s := (Finset.univ : Finset (Fin (l'.length + 1))))
        (i := (k : Fin (l'.length + 1))) (Finset.mem_univ _), hFks]
      -- the product identity over the erased positions
      have hPG : (∏ j : Fin ((x :: l').eraseIdx k).length,
            gueLabelCov (((x :: l').eraseIdx k).get j)
              (((x :: l').eraseIdx k).get (partner ((x :: l').eraseIdx k) p j))) =
          ∏ i ∈ ((Finset.univ : Finset (Fin (l'.length + 1))) \ {k}),
            gueLabelCov ((e :: x :: l').get i.succ)
              ((e :: x :: l').get (partner (e :: x :: l')
                (GUEPairing.cons e (x :: l') k p) i.succ)) := by
        refine Finset.prod_bij (fun (j : Fin ((x :: l').eraseIdx k).length) _ =>
          k.succAbove (Fin.cast hlen j)) ?_ ?_ ?_ ?_
        · intro j _
          simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and]
          exact Fin.succAbove_ne k (Fin.cast hlen j)
        · intro j _ j' _ h
          have h1 : k.succAbove (Fin.cast hlen j) = k.succAbove (Fin.cast hlen j') := h
          exact Fin.cast_injective hlen (Fin.succAbove_right_injective h1)
        · intro i hi
          simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and] at hi
          refine ⟨Fin.cast hlen.symm (eraseIndex l'.length k i (by simpa using hi)),
            Finset.mem_univ _, ?_⟩
          rw [Fin.cast_cast, Fin.cast_eq_self, succAbove_eraseIndex]
        · intro j _
          simp only [succAbove_get_eraseIdx x l' k hlen, partner_cons_succAbove k p hlen]
          congr 1
      rw [hPG]
      generalize hX : (∏ i ∈ (Finset.univ : Finset (Fin (l'.length + 1))) \ {k},
        gueLabelCov ((e :: x :: l').get i.succ)
          ((e :: x :: l').get (partner (e :: x :: l')
            (GUEPairing.cons e (x :: l') k p) i.succ))) = X
      rw [mul_comm X (gueLabelCov e ((x :: l').get k)), ← mul_assoc, gueLabelCov_mul_self]


/-- **Genus expansion, steps 1–2**: the normalized trace-word moment is `N^{-(k/2+1)}` times the sum
over cyclic vertex functions and pairings of the label weight times the index product over the
partner positions. -/
theorem integral_gueNormTrace_eq_sum_vertex_label_index (w : List ι) (hpos : 1 ≤ w.length) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), gueNormTrace w x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) =
      ((N : ℂ)⁻¹) ^ (w.length / 2 + 1) *
        ∑ u : Fin w.length → Fin N,
          ∑ p : GUEPairing (gueVertexEntries w hpos u),
            (∏ i : Fin (gueVertexEntries w hpos u).length,
                gueLabelCov ((gueVertexEntries w hpos u).get i)
                  ((gueVertexEntries w hpos u).get (partner _ p i))) *
              ∏ i : Fin (gueVertexEntries w hpos u).length,
                gueIndexCov ((gueVertexEntries w hpos u).get i)
                  ((gueVertexEntries w hpos u).get (partner _ p i)) := by
  rw [integral_gueNormTrace_eq_sum_vertex w hpos]
  refine congrArg _ (Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun p _ => ?_)
  exact gueDeltaWeight_eq_label_prod_index_prod _ p


/-- **Genus expansion, steps (iii)+(iv), k-generic form**: for a pairing given by an involution
`σ` of the `k` walk positions, the sum over vertex assignments of the product of the index
constraints of the pairing equals `N` to the loop count `pairOrbitCount`-style orbit number. -/
theorem sum_prod_indexConstraints (k : ℕ) (σ : Equiv.Perm (Fin k)) (hσ : σ * σ = 1) :
    (∑ V : Fin k → Fin N, ∏ i : Fin k,
        (if (V i = V (finRotate k (σ i)) ∧ V (finRotate k i) = V (σ i)) then (1 : ℂ) else 0))
      = (N : ℂ) ^ permOrbitCount (finRotate k * σ) := by
  have hss : ∀ i : Fin k, σ (σ i) = i := by
    intro i
    have h := congrArg (fun e : Equiv.Perm (Fin k) => e i) hσ
    simpa using h
  have hfac : ∀ V : Fin k → Fin N, ∏ i : Fin k,
        (if (V i = V (finRotate k (σ i)) ∧ V (finRotate k i) = V (σ i)) then (1 : ℂ) else 0) =
      (∏ i : Fin k, (if V i = V (finRotate k (σ i)) then (1 : ℂ) else 0)) := by
    intro V
    have h1 : ∀ i : Fin k,
        (if (V i = V (finRotate k (σ i)) ∧ V (finRotate k i) = V (σ i)) then (1 : ℂ) else 0) =
          (if V i = V (finRotate k (σ i)) then (1 : ℂ) else 0) *
            (if V (finRotate k i) = V (σ i) then (1 : ℂ) else 0) := by
      intro i
      split_ifs <;> simp_all
    rw [Finset.prod_congr rfl fun i _ => h1 i, Finset.prod_mul_distrib]
    have hB : (∏ i : Fin k, (if V (finRotate k i) = V (σ i) then (1 : ℂ) else 0)) =
        (∏ i : Fin k, (if V i = V (finRotate k (σ i)) then (1 : ℂ) else 0)) := by
      rw [← Equiv.prod_comp σ
        (fun j : Fin k => (if V j = V (finRotate k (σ j)) then (1 : ℂ) else 0))]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hss i]
      simp [eq_comm]
    rw [hB]
    have h2 := Finset.prod_boole (s := (Finset.univ : Finset (Fin k)))
      (p := fun i : Fin k => V i = V (finRotate k (σ i))) (M₀ := ℂ)
    rw [h2]
    by_cases hp : ∀ i ∈ (Finset.univ : Finset (Fin k)), V i = V (finRotate k (σ i))
    · rw [ite_eq_left hp]; norm_num
    · rw [ite_eq_right hp]; norm_num
  simp_rw [hfac]
  exact sum_prod_ite_eq_pow (α := Fin k) (finRotate k * σ) N

/-! ### The slot reindexing of the cyclic vertex parametrization -/

/-- The slot function: the values of the closed vertex function at the `castSucc` positions. -/
def slotVertex {k : ℕ} (hk : 1 ≤ k) (u : Fin k → Fin N) : Fin k → Fin N :=
  fun i => cyclicVertex hk u i.castSucc

/-- The slot function is the cyclic shift of the vertex function. -/
lemma slotVertex_finRotate {k : ℕ} (hk : 1 ≤ k) (u : Fin k → Fin N) (j : Fin k) :
    slotVertex hk u (finRotate k j) = u j := by
  rw [show slotVertex hk u (finRotate k j) =
      cyclicVertex hk u ((finRotate k j)).castSucc from rfl, ← cyclicVertex_succ_eq hk u j]
  exact Fin.cons_succ _ _ _

/-- The slot map is injective. -/
lemma slotVertex_injective {k : ℕ} (hk : 1 ≤ k) :
    Function.Injective (slotVertex (N := N) hk) := by
  intro u u' h
  funext j
  have h' := congrFun h (finRotate k j)
  rwa [slotVertex_finRotate hk u j, slotVertex_finRotate hk u' j] at h'

/-- Reindexing a sum over cyclic vertex functions as a sum over slot functions. -/
theorem sum_slotVertex_bijective {k : ℕ} (hk : 1 ≤ k) (F : (Fin k → Fin N) → ℂ) :
    (∑ u : Fin k → Fin N, F (slotVertex hk u)) = ∑ V : Fin k → Fin N, F V := by
  exact Fintype.sum_bijective (slotVertex (N := N) hk)
    ⟨slotVertex_injective hk, Finite.injective_iff_surjective.mp (slotVertex_injective hk)⟩
    (fun u => F (slotVertex hk u)) F (fun u => rfl)

/-- **Genus expansion, steps (iii)+(iv) in the cyclic-vertex form**: the sum over cyclic vertex
functions of the two-family index-constraint product equals `N` to the loop count. -/
theorem sum_prod_indexConstraints_cyclicVertex (k : ℕ) (hk : 1 ≤ k) (σ : Equiv.Perm (Fin k))
    (hσ : σ * σ = 1) :
    (∑ u : Fin k → Fin N, ∏ i : Fin k,
        (if (slotVertex hk u i = slotVertex hk u (finRotate k (σ i)) ∧
            slotVertex hk u (finRotate k i) = slotVertex hk u (σ i)) then (1 : ℂ) else 0))
      = (N : ℂ) ^ permOrbitCount (finRotate k * σ) := by
  rw [sum_slotVertex_bijective hk
    (fun V => ∏ i : Fin k,
      (if (V i = V (finRotate k (σ i)) ∧ V (finRotate k i) = V (σ i)) then (1 : ℂ) else 0))]
  exact sum_prod_indexConstraints k σ hσ
end

end GUEStrongConvergence
