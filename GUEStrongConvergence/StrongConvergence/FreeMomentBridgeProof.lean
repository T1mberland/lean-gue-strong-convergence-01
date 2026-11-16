/-
# The free-moment bridge: `ncSum = wickSum`

The project's non-crossing label sum `ncSum` (a sum over the recursive pairings `GUEPairing` that
satisfy `IsNonCrossing`, weighted by `gueLabelWeight`) is identified with the free Wick sum
`wickSum` of the dependency `lean-free-prob` (the pairing sum over `NoncrossingPairing`, weighted
by the label-indicator covariance).

Both sides satisfy the same first-partner recursion:

* `ncLabelSum_cons` (`Probability/GUEPairingNCRecursion.lean`): the non-crossing label sum of
  `e :: x :: l'` is the sum over the partner `k` of `e` of the label covariance of the pair
  `(e, (x::l').get k)` times the product of the interior and exterior non-crossing label sums;
* `NoncrossingPairing.pairingSum_succ_succ`: the dependency pairing sum satisfies the same
  recursion with the interior and exterior blocks embedded by `insideEmbedding`/`outsideEmbedding`.

`ncLabelSum_eq_wickSum_aux` matches these two recursions term by term (strong induction on the
length), which yields `FreeMomentBridge`, and hence the `hWords` theorem in its target shape.

No `sorry`/axiom is used.
-/
import GUEStrongConvergence.StrongConvergence.AllWordsUnconditional
import GUEStrongConvergence.Probability.GUEBlockSplitFinal
import GUEStrongConvergence.Probability.GUEPairingNCRecursion

open Filter MeasureTheory FreeProbability
open scoped BigOperators Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace GUEStrongConvergence

attribute [local instance] Classical.propDecidable

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The two forms of the sum agree definitionally -/

/-- The project's non-crossing label sum is the generic non-crossing label sum. -/
theorem ncSum_eq_ncLabelSum (K : List (GUEEntry ι 1)) : ncSum K = ncLabelSum K := rfl

/-! ### Matching the interior and exterior blocks -/

section Blocks

variable {e x : GUEEntry ι 1} {l' : List (GUEEntry ι 1)}

/-- The label-indicator covariance of a list of entries. -/
def labelCov (K : List (GUEEntry ι 1)) : Fin K.length → Fin K.length → ℂ :=
  fun i j => if (K.get i).1 = (K.get j).1 then (1 : ℂ) else 0

/-- The free Wick sum is the pairing sum of the label-indicator covariance. -/
theorem wickSum_eq_pairingSum (K : List (GUEEntry ι 1)) :
    wickSum K = NoncrossingPairing.pairingSum (labelCov K) := rfl

/-- The head of `e :: x :: l'`. -/
lemma get_zero_cons : (e :: x :: l').get (0 : Fin (l'.length + 2)) = e := rfl

/-- The label covariance of the head-partner pair is the head covariance. -/
lemma labelCov_zero_splitPartner (k : Fin (l'.length + 1)) :
    labelCov (e :: x :: l') 0 (NoncrossingPairing.splitPartner k) =
      gueLabelCov e ((x :: l').get k) := by
  have hidx : NoncrossingPairing.splitPartner k = (Fin.succ k : Fin (e :: x :: l').length) := by
    apply Fin.ext
    rw [NoncrossingPairing.splitPartner_val, Fin.val_succ]
  have h : ((e :: x :: l').get (NoncrossingPairing.splitPartner k)).1 = ((x :: l').get k).1 := by
    rw [hidx]
    rfl
  simp only [labelCov, gueLabelCov, get_zero_cons, h]

/-- The label of an interior position. -/
lemma get_inside_label (k : Fin (l'.length + 1)) (a : Fin k.val) :
    ((e :: x :: l').get (NoncrossingPairing.insideEmbedding k a)).1 =
      ((x :: l').get ⟨a.val, by
        have := a.isLt; have := k.isLt; simp only [List.length_cons]; omega⟩).1 := by
  simp only [List.get_eq_getElem, NoncrossingPairing.insideEmbedding_val,
    List.getElem_cons_succ]

/-- The label of an exterior position. -/
lemma get_outside_label (k : Fin (l'.length + 1)) (a : Fin (l'.length - k.val)) :
    ((e :: x :: l').get (NoncrossingPairing.outsideEmbedding k a)).1 =
      ((x :: l').get ⟨k.val + 1 + a.val, by
        have := a.isLt; have := k.isLt; simp only [List.length_cons]; omega⟩).1 := by
  have hidx : k.val + 2 + a.val = (k.val + 1 + a.val) + 1 := by omega
  simp only [List.get_eq_getElem, NoncrossingPairing.outsideEmbedding_val, hidx,
    List.getElem_cons_succ]

/-- The label of a position of the interior block `(x :: l').take k`. -/
lemma get_take_label (k : Fin (l'.length + 1)) (i : Fin ((x :: l').take k.val).length) :
    (((x :: l').take k.val).get i).1 =
      ((x :: l').get ⟨i.val, by
        have hi := i.isLt
        have hle : ((x :: l').take k.val).length ≤ (x :: l').length := by
          rw [List.length_take]; exact Nat.min_le_right _ _
        omega⟩).1 := by
  simp only [List.get_eq_getElem, List.getElem_take]

/-- The label of a position of the exterior block `(x :: l').drop (k+1)`. -/
lemma get_drop_label (k : Fin (l'.length + 1))
    (i : Fin ((x :: l').drop (k.val + 1)).length) :
    (((x :: l').drop (k.val + 1)).get i).1 =
      ((x :: l').get ⟨k.val + 1 + i.val, by
        have hi := i.isLt
        have hlen : ((x :: l').drop (k.val + 1)).length = (x :: l').length - (k.val + 1) :=
          List.length_drop
        simp only [List.length_cons] at hlen ⊢
        omega⟩).1 := by
  simp only [List.get_eq_getElem, List.getElem_drop]

/-- The interior label covariance matches the interior block. -/
lemma labelCov_inside_eq (k : Fin (l'.length + 1))
    (hA : ((x :: l').take k.val).length = k.val)
    (i j : Fin ((x :: l').take k.val).length) :
    labelCov ((x :: l').take k.val) i j =
      labelCov (e :: x :: l')
        (NoncrossingPairing.insideEmbedding k (Fin.cast hA i))
        (NoncrossingPairing.insideEmbedding k (Fin.cast hA j)) := by
  have hi : (((x :: l').take k.val).get i).1 =
      ((e :: x :: l').get (NoncrossingPairing.insideEmbedding k (Fin.cast hA i))).1 := by
    rw [get_inside_label, get_take_label]
    exact congrArg (fun z : GUEEntry ι 1 => z.1)
      (congrArg (fun idx => (x :: l').get idx) (Fin.ext rfl))
  have hj : (((x :: l').take k.val).get j).1 =
      ((e :: x :: l').get (NoncrossingPairing.insideEmbedding k (Fin.cast hA j))).1 := by
    rw [get_inside_label, get_take_label]
    exact congrArg (fun z : GUEEntry ι 1 => z.1)
      (congrArg (fun idx => (x :: l').get idx) (Fin.ext rfl))
  unfold labelCov
  rw [hi, hj]

/-- The exterior label covariance matches the exterior block. -/
lemma labelCov_outside_eq (k : Fin (l'.length + 1))
    (hB : ((x :: l').drop (k.val + 1)).length = l'.length - k.val)
    (i j : Fin ((x :: l').drop (k.val + 1)).length) :
    labelCov ((x :: l').drop (k.val + 1)) i j =
      labelCov (e :: x :: l')
        (NoncrossingPairing.outsideEmbedding k (Fin.cast hB i))
        (NoncrossingPairing.outsideEmbedding k (Fin.cast hB j)) := by
  have hi : (((x :: l').drop (k.val + 1)).get i).1 =
      ((e :: x :: l').get
        (NoncrossingPairing.outsideEmbedding k (Fin.cast hB i))).1 := by
    rw [get_outside_label, get_drop_label]
    exact congrArg (fun z : GUEEntry ι 1 => z.1)
      (congrArg (fun idx => (x :: l').get idx) (Fin.ext rfl))
  have hj : (((x :: l').drop (k.val + 1)).get j).1 =
      ((e :: x :: l').get
        (NoncrossingPairing.outsideEmbedding k (Fin.cast hB j))).1 := by
    rw [get_outside_label, get_drop_label]
    exact congrArg (fun z : GUEEntry ι 1 => z.1)
      (congrArg (fun idx => (x :: l').get idx) (Fin.ext rfl))
  unfold labelCov
  rw [hi, hj]

/-- **The interior Wick sum is the interior block pairing sum.** -/
theorem wickSum_take (k : Fin (l'.length + 1)) :
    wickSum ((x :: l').take k.val) =
      NoncrossingPairing.pairingSum (fun a b : Fin k.val =>
        labelCov (e :: x :: l') (NoncrossingPairing.insideEmbedding k a)
          (NoncrossingPairing.insideEmbedding k b)) := by
  have hA : ((x :: l').take k.val).length = k.val := by
    rw [List.length_take]
    exact Nat.min_eq_left (le_of_lt k.isLt)
  rw [wickSum_eq_pairingSum]
  exact (pairingSum_congr_len hA.symm _ _ (labelCov_inside_eq k hA)).symm

/-- **The exterior Wick sum is the exterior block pairing sum.** -/
theorem wickSum_drop (k : Fin (l'.length + 1)) :
    wickSum ((x :: l').drop (k.val + 1)) =
      NoncrossingPairing.pairingSum (fun a b : Fin (l'.length - k.val) =>
        labelCov (e :: x :: l') (NoncrossingPairing.outsideEmbedding k a)
          (NoncrossingPairing.outsideEmbedding k b)) := by
  have hB : ((x :: l').drop (k.val + 1)).length = l'.length - k.val := by
    rw [List.length_drop]
    simp only [List.length_cons]
    omega
  rw [wickSum_eq_pairingSum]
  exact (pairingSum_congr_len hB.symm _ _ (labelCov_outside_eq k hB)).symm

end Blocks

/-! ### The strong induction -/

/-- **The non-crossing label sum equals the free Wick sum** (strong induction on the length). -/
theorem ncLabelSum_eq_wickSum_aux :
    ∀ (n : ℕ) (K : List (GUEEntry ι 1)), K.length = n → ncLabelSum K = wickSum K := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro K hK
    match K with
    | [] =>
      have huniv : (Finset.univ : Finset (GUEPairing ([] : List (GUEEntry ι 1)))) =
          {GUEPairing.nil} := by
        ext p
        cases p
        simp
      have hnc : IsNonCrossing (GUEPairing.nil : GUEPairing ([] : List (GUEEntry ι 1))) := by
        intro a
        exact Fin.elim0 a
      rw [ncLabelSum, huniv]
      simp only [Finset.filter_singleton, if_pos hnc, gueLabelWeight_nil, Finset.sum_singleton]
      rw [wickSum_eq_pairingSum]
      exact (NoncrossingPairing.pairingSum_zero (M := ℂ) (labelCov [])).symm
    | [a] =>
      have hempty : ∀ p : GUEPairing ([a] : List (GUEEntry ι 1)), False := by
        intro p
        cases p with
        | cons e l k p' => exact Fin.elim0 k
      rw [ncLabelSum, Finset.sum_eq_zero (fun p _ => (hempty p).elim), wickSum_eq_pairingSum]
      exact (NoncrossingPairing.pairingSum_one (M := ℂ) (labelCov [a])).symm
    | e :: x :: l' =>
      have hn2 : n = l'.length + 2 := by
        rw [← hK]
        rfl
      rw [GUEPairing.ncLabelSum_cons e x l', wickSum_eq_pairingSum,
        NoncrossingPairing.pairingSum_succ_succ (n := l'.length) (labelCov (e :: x :: l'))]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hk := k.isLt
      simp only [List.length_cons] at hk
      have hxlen : (x :: l').length = l'.length + 1 := rfl
      have hA_lt : ((x :: l').take k.val).length < n := by
        rw [List.length_take, hn2]
        have := k.isLt
        have : k.val ≤ l'.length := by omega
        omega
      have hB_lt : ((x :: l').drop (k.val + 1)).length < n := by
        have hp : ((x :: l').drop (k.val + 1)).length = (x :: l').length - (k.val + 1) :=
          List.length_drop
        rw [hp, hn2]
        omega
      rw [ih ((x :: l').take k.val).length hA_lt _ rfl,
        ih ((x :: l').drop (k.val + 1)).length hB_lt _ rfl,
        wickSum_take k, wickSum_drop k, labelCov_zero_splitPartner k]
      ring

/-- **The non-crossing label sum equals the free Wick sum.** -/
theorem ncLabelSum_eq_wickSum (K : List (GUEEntry ι 1)) : ncLabelSum K = wickSum K :=
  ncLabelSum_eq_wickSum_aux K.length K rfl

/-- **The free-moment bridge.** -/
theorem freeMomentBridge : FreeMomentBridge (ι := ι) := fun K => by
  rw [ncSum_eq_ncLabelSum]
  exact ncLabelSum_eq_wickSum K

/-! ### `hWords` in its target shape -/

/-- **Unconditional `hWords`**: almost surely, every normalized GUE trace word converges to its
free moment `tau`. -/
theorem ae_all_words_gueNormTrace_tau_unconditional (r : ℕ) :
    ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ w : List (Fin r),
      Tendsto (fun N : ℕ => gueNormTrace (N := N) w (x N)) atTop (𝓝 (tau r w)) :=
  ae_all_words_tau_of_ncSum r
    (fun w m hl => freeMomentBridge (ι := Fin r) (gueCanonicalEntries w m hl (le_refl 1)))
    (ae_all_words_gueNormTrace_genusSum_unconditional (ι := Fin r))

end

end GUEStrongConvergence
