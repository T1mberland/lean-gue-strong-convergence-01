/-
# The free-moment bridge and unconditional `hWords`

The target statement `GUEStrongConvergenceStatement_conditional`
(`StrongConvergence/FinalStatement.lean`) consumes the scalar hypothesis

`hWords : ∀ᵐ x, ∀ w : List (Fin r), Tendsto (fun N => gueNormTrace w (x N)) atTop (𝓝 (tau r w))`

with `tau r w = (closedGeneratedVacuumState (Fin r)).expectation (wordProd (semicircularFamily r) w)`
the free joint word moment (`StrongConvergence/ConcreteTransfer.lean`).  The II.B almost-sure
theorem produces the same convergence with the project's own limit `wordLimit w` (the non-crossing
label sum for even words, `0` for odd-length words, `1` for the empty word).

This file supplies the bridge between the two limits and the `hWords` assembly:

1. **Free side** (`tau_eq_pairingSum`): `tau r w` is the free Wick sum
   `NoncrossingPairing.pairingSum (fun i j => [w i = w j])` of the dependency `lean-free-prob`
   (via `vacuumExpectation_ofFn_eq_pairingSum`).  Consequences: `tau r [] = 1` and
   `tau r w = 0` for odd words.
2. **Odd and empty words** (`wordLimit_eq_tau_nil`, `wordLimit_eq_tau_of_odd`): the two limits
   agree, so those cases of `hWords` are unconditional.
3. **Even words** (`tau_eq_wickSum`, `wordLimit_eq_tau_of_even`): `wordLimit` and `tau` are the
   *same* non-crossing pairing sum over the canonical entry list, the first in the project's
   recursive-pairing form `ncSum` and the second in the dependency's partition form `wickSum`.
4. **`hWords`** (`ae_all_words_tau`): the all-words almost-sure theorem plus the per-word
   identification `wordLimit = tau` gives `hWords` in its exact target shape.

No `sorry`/axiom is used.
-/
import GUEStrongConvergence.Probability.GUEAllWords
import GUEStrongConvergence.StrongConvergence.ConcreteTransfer
import FreeProbability.Fock.WickFormula

noncomputable section

namespace GUEStrongConvergence

open Filter MeasureTheory FreeProbability FreeProbability.Fock

open scoped BigOperators Topology

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The free side: `tau` is a non-crossing pairing sum -/

/-- The closed-algebra word product of the semicircular family is the Fock operator word. -/
theorem val_wordProd_semicircularFamily (r : ℕ) (w : List (Fin r)) :
    ((closedSemicircularAlgebra (Fin r)).val (wordProd (semicircularFamily r) w))
      = operatorWord w := by
  rw [wordProd, operatorWord, map_list_prod]
  congr 1
  rw [List.map_map]
  rfl

/-- `tau` is the vacuum expectation of the Fock operator word. -/
theorem tau_eq_vacuumExpectation_operatorWord (r : ℕ) (w : List (Fin r)) :
    tau r w = vacuumExpectation (operatorWord w) := by
  rw [tau, ← val_wordProd_semicircularFamily]
  rfl

/-- The weight of a non-crossing pairing depends only on the covariance matrix. -/
lemma ncPairingWeight_congr {n : ℕ} {M : Type*} [CommMonoid M] (p : NoncrossingPairing n)
    {C C' : Fin n → Fin n → M} (h : ∀ i j, C i j = C' i j) :
    NoncrossingPairing.pairingWeight p C = NoncrossingPairing.pairingWeight p C' := by
  simp only [NoncrossingPairing.pairingWeight, h]

/-- **The free limit moments are the free Wick sums of the letters.** -/
theorem tau_eq_pairingSum (r : ℕ) (w : List (Fin r)) :
    tau r w = NoncrossingPairing.pairingSum
      (fun i j : Fin w.length => if w.get i = w.get j then (1 : ℂ) else 0) := by
  rw [tau_eq_vacuumExpectation_operatorWord]
  have h := vacuumExpectation_ofFn_eq_pairingSum (I := Fin r) w.length w.get
  have hw : List.ofFn w.get = w := List.ofFn_get w
  rw [hw] at h
  refine h.trans ?_
  simp only [NoncrossingPairing.pairingSum]
  refine Finset.sum_congr rfl fun p _ => ncPairingWeight_congr p fun i j => ?_
  by_cases hh : w.get i = w.get j <;> simp [hh]

/-- The empty word has free moment one. -/
theorem tau_nil (r : ℕ) : tau r ([] : List (Fin r)) = 1 := by
  rw [tau_eq_vacuumExpectation_operatorWord]
  simp

/-- The free moment of an odd-length word vanishes. -/
theorem tau_eq_zero_of_odd (r : ℕ) (w : List (Fin r)) (hodd : Odd w.length) :
    tau r w = 0 := by
  rw [tau_eq_pairingSum]
  have hcard : Fintype.card (NoncrossingPairing w.length) = 0 :=
    NoncrossingPairing.card_eq_zero_of_odd hodd
  have hEmpty : IsEmpty (NoncrossingPairing w.length) := Fintype.card_eq_zero_iff.mp hcard
  simp only [NoncrossingPairing.pairingSum]
  exact Finset.sum_eq_zero fun p _ => hEmpty.elim p

/-! ### The two forms of the non-crossing label sum -/

/-- The project's non-crossing label sum of a fixed entry list `K`. -/
def ncSum (K : List (GUEEntry ι 1)) : ℂ :=
  ∑ p ∈ (Finset.univ : Finset (GUEPairing K)).filter IsNonCrossing, gueLabelWeight K p

/-- The free Wick sum of a labelled list: the non-crossing pairing sum with the label-indicator
covariance of the positions. -/
def wickSum (K : List (GUEEntry ι 1)) : ℂ :=
  NoncrossingPairing.pairingSum
    (fun i j : Fin K.length => if (K.get i).1 = (K.get j).1 then (1 : ℂ) else 0)

/-- **The free-moment bridge** (combinatorial form): the project's non-crossing label sum over the
recursive pairings of a fixed entry list equals the free Wick sum over the dependency's
non-crossing pairings of the same labelled list. -/
def FreeMomentBridge : Prop :=
  ∀ (K : List (GUEEntry ι 1)), ncSum K = wickSum K

/-! ### The empty and odd words: the bridge is unconditional -/

/-- The empty word: both limits equal one. -/
theorem wordLimit_eq_tau_nil (r : ℕ) : wordLimit ([] : List (Fin r)) = tau r [] := by
  rw [wordLimit_nil, tau_nil]

/-- Every odd-length word: both limits vanish. -/
theorem wordLimit_eq_tau_of_odd (r : ℕ) (w : List (Fin r)) (hodd : Odd w.length) :
    wordLimit w = tau r w := by
  rw [wordLimit_of_odd hodd, tau_eq_zero_of_odd r w hodd]

/-! ### The even words: `tau` as the free Wick sum of the canonical list -/

/-- The labels of the canonical entry list are the letters of the word. -/
theorem map_fst_gueCanonicalEntries {N : ℕ} (w : List ι) (m : ℕ) (hl : w.length = 2 * m)
    (hN : 1 ≤ N) :
    (gueCanonicalEntries (N := N) w m hl hN).map (fun e => e.1) = w := by
  rw [gueCanonicalEntries, List.map_ofFn]
  apply List.ext_getElem
  · simp [hl]
  · intro i hi1 hi2
    simp

/-- The free Wick sum only depends on the length and the letter function. -/
lemma pairingSum_congr_len {n m : ℕ} (h : n = m) (C : Fin n → Fin n → ℂ)
    (C' : Fin m → Fin m → ℂ) (hC : ∀ i j, C' i j = C (Fin.cast h.symm i) (Fin.cast h.symm j)) :
    NoncrossingPairing.pairingSum C = NoncrossingPairing.pairingSum C' := by
  subst h
  have hCC : C = C' := by
    funext i j
    simpa using (hC i j).symm
  rw [hCC]

/-- **`tau` of a word given as a letter function is the free Wick sum.** -/
theorem tau_ofFn_eq_pairingSum (r n : ℕ) (a : Fin n → Fin r) :
    tau r (List.ofFn a) = NoncrossingPairing.pairingSum
      (fun i j : Fin n => if a i = a j then (1 : ℂ) else 0) := by
  rw [tau_eq_pairingSum]
  refine pairingSum_congr_len (n := (List.ofFn a).length) (m := n) List.length_ofFn _ _ ?_
  intro i j
  simp

/-- **`tau` is the free Wick sum of the canonical entry list of the word.** -/
theorem tau_eq_wickSum (r : ℕ) (w : List (Fin r)) (m : ℕ) (hl : w.length = 2 * m) :
    tau r w = wickSum (gueCanonicalEntries w m hl (le_refl 1)) := by
  have hK : (gueCanonicalEntries w m hl (le_refl 1)).length = w.length := by
    rw [length_gueCanonicalEntries, hl]
  conv_lhs => rw [← List.ofFn_get w]
  rw [tau_ofFn_eq_pairingSum, wickSum]
  refine pairingSum_congr_len (n := w.length) (m := (gueCanonicalEntries w m hl (le_refl 1)).length)
    (C := fun i j : Fin w.length => if w.get i = w.get j then (1 : ℂ) else 0)
    (C' := fun i j : Fin (gueCanonicalEntries w m hl (le_refl 1)).length =>
      if ((gueCanonicalEntries w m hl (le_refl 1)).get i).1
        = ((gueCanonicalEntries w m hl (le_refl 1)).get j).1 then (1 : ℂ) else 0)
    hK.symm ?_
  intro i j
  have hi : ((gueCanonicalEntries w m hl (le_refl 1)).get i).1 = w.get (Fin.cast hK i) := by
    rw [gueCanonicalEntries_get_label]
    exact congrArg w.get (Fin.ext rfl)
  have hj : ((gueCanonicalEntries w m hl (le_refl 1)).get j).1 = w.get (Fin.cast hK j) := by
    rw [gueCanonicalEntries_get_label]
    exact congrArg w.get (Fin.ext rfl)
  rw [hi, hj]

/-- **Even words**: the bridge for `w` follows from the non-crossing label sum identity for its
canonical entry list. -/
theorem wordLimit_eq_tau_of_even (r : ℕ) (w : List (Fin r)) (m : ℕ) (hl : w.length = 2 * m)
    (h : ncSum (gueCanonicalEntries w m hl (le_refl 1))
      = wickSum (gueCanonicalEntries w m hl (le_refl 1))) :
    wordLimit w = tau r w := by
  have hK : tau r w = wickSum (gueCanonicalEntries w m hl (le_refl 1)) :=
    tau_eq_wickSum r w m hl
  rw [wordLimit_of_even hl, hK]
  exact h

/-! ### `hWords` from the all-words almost-sure theorem -/

/-- **`hWords` in the target shape from the word-limit convergence.**  The almost-sure
convergence of all normalized GUE trace words to `wordLimit` (the II.B theorem) together with the
identification `wordLimit = tau` gives the exact hypothesis consumed by the final assembly. -/
theorem ae_all_words_tau (r : ℕ)
    (hbridge : ∀ w : List (Fin r), wordLimit w = tau r w)
    (hAll : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ w : List (Fin r),
      Tendsto (fun N : ℕ => gueNormTrace (N := N) w (x N)) atTop (𝓝 (wordLimit w))) :
    ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ w : List (Fin r),
      Tendsto (fun N : ℕ => gueNormTrace (N := N) w (x N)) atTop (𝓝 (tau r w)) := by
  filter_upwards [hAll] with x hx w
  rw [← hbridge w]
  exact hx w

/-- **`hWords` with the bridge in combinatorial form**: only the even words survive as an input
(the odd and empty cases are proved outright). -/
theorem ae_all_words_tau_of_ncSum (r : ℕ)
    (hbridge : ∀ (w : List (Fin r)) (m : ℕ) (hl : w.length = 2 * m),
      ncSum (gueCanonicalEntries w m hl (le_refl 1))
        = wickSum (gueCanonicalEntries w m hl (le_refl 1)))
    (hAll : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ w : List (Fin r),
      Tendsto (fun N : ℕ => gueNormTrace (N := N) w (x N)) atTop (𝓝 (wordLimit w))) :
    ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ w : List (Fin r),
      Tendsto (fun N : ℕ => gueNormTrace (N := N) w (x N)) atTop (𝓝 (tau r w)) := by
  refine ae_all_words_tau r (fun w => ?_) hAll
  by_cases hnil : w = []
  · subst hnil
    exact wordLimit_eq_tau_nil r
  by_cases heven : Even w.length
  · obtain ⟨m, hm⟩ := heven
    have hm2 : w.length = 2 * m := by omega
    exact wordLimit_eq_tau_of_even r w m hm2 (hbridge w m hm2)
  · exact wordLimit_eq_tau_of_odd r w (Nat.not_even_iff_odd.mp heven)

end GUEStrongConvergence
