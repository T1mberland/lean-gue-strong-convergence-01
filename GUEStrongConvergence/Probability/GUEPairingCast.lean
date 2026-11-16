/-
# Length-preserving transport of GUE pairings

A recursive pairing `GUEPairing l` of a list of GUE entries only depends on the *positions* of
the entries, not on the entries themselves: the head `e` is paired with `l.get k`, and the
remaining pairing acts on `l.eraseIdx k`.  Consequently, two lists of the same length carry
isomorphic pairing types, and this file constructs the transport and proves that it is
compatible with the partner permutation, the label weight and the finite pairing sum.

The main definition is `GUEPairing.castLength`,

`castLength h : GUEPairing l₁ → GUEPairing l₂`   for   `h : l₁.length = l₂.length`,

defined by recursion on the pairing and mirroring the `cons` constructor: the same partner
position is chosen (cast along `h`) and the tail pairing is transported along the induced length
equality of the erased lists.  We then show:

* `castLengthEquiv`: the transport is an equivalence `GUEPairing l₁ ≃ GUEPairing l₂` with
  inverse the transport along `h.symm`;
* `partner_castLength` and `partnerPerm_castLength`: the partner map is transported,
  `partner l₂ (castLength h p) (Fin.cast h i) = Fin.cast h (partner l₁ p i)`, i.e. the partner
  permutations are conjugate under `finCongr h` (this is the compatibility needed for the mean
  limit and the variance);
* `gueLabelWeight_castLength`: a length-preserving cast between lists with the same labels
  positionwise preserves the label weight;
* `gueIndexWeight_castLength`: the honest *positional* statement for the index weight, which is
  **not** invariant under an arbitrary length-preserving cast (the matrix indices of `l₁` and
  `l₂` are unrelated): the transport preserves the index weight exactly when the matrix indices
  agree positionwise, i.e. only the combinatorial *pattern* of index constraints is transported.
  The walk-level instantiation therefore applies the cast to a canonical list with the same
  labels and the same index pattern;
* `gueDeltaWeight_castLength`: combining the two, the Kronecker weight is invariant under a cast
  between lists with the same labels and index pattern;
* `sum_castLength` and its weight corollaries: the finite sums over pairings are invariant under
  the transport.

No asymptotic statement is made, and no `sorry`/axiom is used.
-/
import GUEStrongConvergence.Probability.GUEWordSecondMoment
import GUEStrongConvergence.Probability.GUEDeltaWeightProduct
import GUEStrongConvergence.Probability.ListGetEraseIdx

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Matrix ENNReal Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace GUEStrongConvergence

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

namespace GUEPairing

/-! ### The transport -/

/-- **Length-preserving transport of a recursive pairing.**  A pairing of `l₁` is sent to the
pairing of `l₂` that chooses the same partner positions, recursively along the head-partner
decomposition. -/
def castLength : (l₁ l₂ : List (GUEEntry ι N)) → l₁.length = l₂.length →
    GUEPairing l₁ → GUEPairing l₂
  | [], [], _, .nil => .nil
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | e :: l, e₂ :: l₂, h, .cons _ _ k p =>
      GUEPairing.cons e₂ l₂ (Fin.cast (by simpa using h) k)
        (castLength (l.eraseIdx k) (l₂.eraseIdx (Fin.cast (by simpa using h) k)) (by
          rw [List.length_eraseIdx, List.length_eraseIdx]
          simp only [ite_eq_left (Fin.cast (by simpa using h) k).isLt, ite_eq_left k.isLt]
          have h' : l.length = l₂.length := by simpa using h
          omega) p)

/-- The transport of the empty pairing. -/
@[simp] lemma castLength_nil
    (h : ([] : List (GUEEntry ι N)).length = ([] : List (GUEEntry ι N)).length) :
    castLength [] [] h (nil : GUEPairing []) = nil := by
  cases h
  rfl

/-- The transport of a `cons` pairing, mirroring the constructor.  This is the computation rule
of `castLength` and the main rewriting principle for the transport. -/
@[simp] lemma castLength_cons (e : GUEEntry ι N) (l : List (GUEEntry ι N)) (e₂ : GUEEntry ι N)
    (l₂ : List (GUEEntry ι N)) (h : (e :: l).length = (e₂ :: l₂).length)
    (k : Fin l.length) (p : GUEPairing (l.eraseIdx k)) :
    castLength (e :: l) (e₂ :: l₂) h (GUEPairing.cons e l k p) =
      GUEPairing.cons e₂ l₂ (Fin.cast (by simpa using h) k)
        (castLength (l.eraseIdx k) (l₂.eraseIdx (Fin.cast (by simpa using h) k)) (by
          rw [List.length_eraseIdx, List.length_eraseIdx]
          simp only [ite_eq_left (Fin.cast (by simpa using h) k).isLt, ite_eq_left k.isLt]
          have h' : l.length = l₂.length := by simpa using h
          omega) p) := rfl

/-! ### The transport is an equivalence -/

/-- **The transport is inverse to the transport along the symmetric length equality.** -/
lemma castLength_castLength {l₁ : List (GUEEntry ι N)} (p : GUEPairing l₁) :
    ∀ (l₂ : List (GUEEntry ι N)) (h : l₁.length = l₂.length),
      castLength l₂ l₁ h.symm (castLength l₁ l₂ h p) = p := by
  induction p with
  | nil =>
      intro l₂ h
      cases l₂ with
      | nil => rw [castLength_nil]; rfl
      | cons a as => simp at h
  | cons e l k p ih =>
      intro l₂ h
      cases l₂ with
      | nil => simp at h
      | cons e₂ l₂ =>
          rw [castLength_cons, castLength_cons]
          simp only [Fin.cast_cast, Fin.cast_eq_self]
          exact congrArg (GUEPairing.cons e l k) (ih _ _)

/-- **Length-preserving transport of pairings is an equivalence.** -/
def castLengthEquiv {l₁ l₂ : List (GUEEntry ι N)} (h : l₁.length = l₂.length) :
    GUEPairing l₁ ≃ GUEPairing l₂ where
  toFun := castLength l₁ l₂ h
  invFun := castLength l₂ l₁ h.symm
  left_inv p := castLength_castLength p l₂ h
  right_inv q := castLength_castLength q l₁ h.symm

@[simp] lemma castLengthEquiv_apply {l₁ l₂ : List (GUEEntry ι N)} (h : l₁.length = l₂.length)
    (p : GUEPairing l₁) : castLengthEquiv h p = castLength l₁ l₂ h p := rfl

@[simp] lemma castLengthEquiv_symm_apply {l₁ l₂ : List (GUEEntry ι N)} (h : l₁.length = l₂.length)
    (q : GUEPairing l₂) : (castLengthEquiv h).symm q = castLength l₂ l₁ h.symm q := rfl

end GUEPairing

/-! ### Cast lemmas for `Fin`, `eraseIndex` and the partner map

The partner map of `GUEPairingPositions` is built from `Fin.succAbove`, `Fin.pred` and the
list-erasure index map `eraseIndex`.  To compare the partner maps of two pairings related by
`castLength` we need the compatibility of these operations with `Fin.cast`.  All of them are
positional (`Fin.cast` preserves the value), so the proofs are `Fin.ext rfl` after the relevant
length equality has been substituted. -/

section CastLemmas

/-- `Fin.cast` preserves zero. -/
lemma fin_cast_zero {n m : ℕ} (h : n = m) :
    Fin.cast (congrArg Nat.succ h) (0 : Fin (n + 1)) = 0 := Fin.ext rfl

/-- `Fin.cast` commutes with the successor embedding. -/
lemma fin_cast_succ {n m : ℕ} (h : n = m) (k : Fin n) :
    Fin.cast (congrArg Nat.succ h) k.succ = (Fin.cast h k).succ := Fin.ext rfl

/-- `Fin.cast` commutes with the predecessor (with the obvious side conditions). -/
lemma fin_cast_pred {n m : ℕ} (h : n = m) (k : Fin (n + 1)) (hk : k ≠ 0)
    (hk' : Fin.cast (congrArg Nat.succ h) k ≠ 0) :
    Fin.cast h (k.pred hk) = (Fin.cast (congrArg Nat.succ h) k).pred hk' := Fin.ext rfl

/-- `Fin.cast` commutes with `Fin.succAbove`.  Both the cast on `Fin (n+1)` and the cast on the
arguments are parameters (proofs are irrelevant). -/
lemma fin_cast_succAbove {n m : ℕ} (h : n + 1 = m + 1) (h' : n = m) (k : Fin (n + 1))
    (j : Fin n) :
    Fin.cast h (k.succAbove j) = (Fin.cast h k).succAbove (Fin.cast h' j) := by
  have hcond : (Fin.cast h' j).castSucc < Fin.cast h k ↔ j.castSucc < k := by
    simp [Fin.lt_def]
  apply Fin.ext
  simp only [Fin.succAbove]
  by_cases hc : j.castSucc < k
  · rw [ite_eq_left hc, ite_eq_left (hcond.mpr hc)]
    simp
  · rw [ite_eq_right hc, ite_eq_right (fun h2 => hc (hcond.mp h2))]
    simp

/-- The erasure index map is compatible with `Fin.cast`: the index of a position in the erased
list is transported positionally.  Both the cast on `Fin (n+1)` and the length equality of the
erased lists are parameters (they are anyway proofs, hence irrelevant). -/
lemma eraseIndex_cast {n m : ℕ} (h : n + 1 = m + 1) (h' : n = m) (k j : Fin (n + 1))
    (hjk : j ≠ k) (hjk' : Fin.cast h j ≠ Fin.cast h k) :
    eraseIndex m (Fin.cast h k) (Fin.cast h j) hjk' =
      Fin.cast h' (eraseIndex n k j hjk) := by
  subst h'
  rfl

end CastLemmas

/-! ### Compatibility with the partner permutation -/

namespace GUEPairing

theorem partner_castLength {l₁ : List (GUEEntry ι N)} (p : GUEPairing l₁) :
    ∀ (l₂ : List (GUEEntry ι N)) (h : l₁.length = l₂.length) (i : Fin l₁.length),
      partner l₂ (castLength l₁ l₂ h p) (Fin.cast h i) =
        Fin.cast h (partner l₁ p i) := by
  induction p with
  | nil =>
      intro l₂ h i
      exact Fin.elim0 i
  | cons e l k p₀ ih =>
      intro l₂ h i
      cases l with
      | nil => exact Fin.elim0 k
      | cons x l' =>
          cases l₂ with
          | nil => simp at h
          | cons e₂ l₂ =>
              cases l₂ with
              | nil =>
                  rw [castLength_cons]
                  exact Fin.elim0 (Fin.cast (by simpa [List.length_cons] using h) k)
              | cons y l₂' =>
                  rw [castLength_cons]
                  have hh : l'.length + 1 + 1 = l₂'.length + 1 + 1 := by
                    simpa [List.length_cons] using h
                  have hk₁ : (x :: l').length = (y :: l₂').length := by
                    simp only [List.length_cons]; omega
                  have hk₀ : l'.length = l₂'.length := by omega
                  have hlen : ((x :: l').eraseIdx k).length = l'.length := by
                    rw [List.length_eraseIdx, ite_eq_left k.isLt]
                    simp
                  have hlen₂ : ((y :: l₂').eraseIdx (Fin.cast hk₁ k)).length = l₂'.length := by
                    rw [List.length_eraseIdx, ite_eq_left (Fin.cast hk₁ k).isLt]
                    simp
                  have h₁ : ((x :: l').eraseIdx k).length
                      = ((y :: l₂').eraseIdx (Fin.cast hk₁ k)).length := by
                    rw [hlen, hlen₂, hk₀]
                  change partner (e₂ :: y :: l₂')
                      (GUEPairing.cons e₂ (y :: l₂') (Fin.cast hk₁ k)
                        (castLength ((x :: l').eraseIdx k)
                          ((y :: l₂').eraseIdx (Fin.cast hk₁ k)) h₁ p₀))
                      (Fin.cast h i) =
                    Fin.cast h (partner (e :: x :: l') (GUEPairing.cons e (x :: l') k p₀) i)
                  by_cases h0 : i = 0
                  · have hcast : Fin.cast h i = 0 := by
                      rw [h0]; exact fin_cast_zero hk₁
                    have hpart : partner (e :: x :: l') (cons e (x :: l') k p₀) i = k.succ := by
                      rw [h0]; exact partner_cons_zero e x l' k p₀
                    rw [hcast, hpart, partner_cons_zero, fin_cast_succ hk₁ k]
                  · by_cases hkc : i = k.succ
                    · have hcast : Fin.cast h i = (Fin.cast hk₁ k).succ := by
                        rw [hkc]; exact fin_cast_succ hk₁ k
                      have hpart : partner (e :: x :: l') (cons e (x :: l') k p₀) i = 0 := by
                        rw [hkc]; exact partner_cons_head e x l' k p₀ k.succ rfl
                      rw [hcast, hpart, partner_cons_head]
                      rw [show Fin.cast h (0 : Fin (e :: x :: l').length) = 0 from
                        fin_cast_zero hk₁]
                      rfl
                    · have h0' : Fin.cast h i ≠ 0 := by
                        intro hc
                        exact h0 (Fin.cast_injective h
                          (hc.trans (fin_cast_zero hk₁).symm))
                      have hkc' : Fin.cast h i ≠ (Fin.cast hk₁ k).succ := by
                        intro hc
                        refine hkc (Fin.cast_injective h ?_)
                        rw [hc]
                        exact fin_cast_succ hk₁ k
                      set qs : Fin ((x :: l').eraseIdx k).length :=
                        Fin.cast hlen.symm (eraseIndex l'.length k (i.pred h0)
                          (pred_ne_of_ne_succ h0 hkc)) with hqs
                      set qt : Fin ((y :: l₂').eraseIdx (Fin.cast hk₁ k)).length :=
                        Fin.cast hlen₂.symm (eraseIndex l₂'.length (Fin.cast hk₁ k)
                          ((Fin.cast h i).pred h0') (pred_ne_of_ne_succ h0' hkc')) with hqt
                      rw [partner_cons_other e₂ y l₂' (Fin.cast hk₁ k)
                        (castLength ((x :: l').eraseIdx k)
                          ((y :: l₂').eraseIdx (Fin.cast hk₁ k)) h₁ p₀)
                        hlen₂ (Fin.cast h i) h0' hkc']
                      rw [partner_cons_other e x l' k p₀ hlen i h0 hkc]
                      rw [← hqt, ← hqs]
                      rw [fin_cast_succ hk₁
                        (k.succAbove (Fin.cast hlen (partner ((x :: l').eraseIdx k) p₀ qs)))]
                      rw [fin_cast_succAbove hk₁ hk₀ k
                        (Fin.cast hlen (partner ((x :: l').eraseIdx k) p₀ qs))]
                      rw [Fin.succ_inj, Fin.succAbove_inj]
                      have hpred_eq : (Fin.cast h i).pred h0' = Fin.cast hk₁ (i.pred h0) :=
                        (fin_cast_pred hk₁ i h0 h0').symm
                      have hqt_eq : qt = Fin.cast h₁ qs := by
                        rw [hqt, hqs]
                        simp only [hpred_eq]
                        rw [eraseIndex_cast hk₁ hk₀ k (i.pred h0), Fin.cast_cast, Fin.cast_cast]
                      rw [hqt_eq,
                        ih ((y :: l₂').eraseIdx (Fin.cast hk₁ k)) h₁ qs,
                        Fin.cast_cast, Fin.cast_cast]

/-- **The partner permutation is transported by `castLength`.**  This is the conjugation
identity for the fixed-point-free permutations of the two pairings. -/
theorem partnerPerm_castLength {l₁ l₂ : List (GUEEntry ι N)} (h : l₁.length = l₂.length)
    (p : GUEPairing l₁) :
    partnerPerm (castLength l₁ l₂ h p) =
      (finCongr h).symm.trans ((partnerPerm p).trans (finCongr h)) := by
  apply Equiv.ext
  intro i
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply, partnerPerm_apply, castLengthEquiv_apply,
    finCongr_apply, finCongr_symm_apply, Equiv.coe_fn_mk]
  rw [← partner_castLength p l₂ h (Fin.cast h.symm i)]
  congr 1

/-! ### Label-weight invariance -/

/-- **The label weight is invariant under a length-preserving cast between lists whose labels
agree positionwise.**  Indeed `gueLabelCov` only inspects the label (first) component of an
entry, so the transported pairing pairs the same labels. -/
theorem gueLabelWeight_castLength {l₁ : List (GUEEntry ι N)} (p : GUEPairing l₁) :
    ∀ (l₂ : List (GUEEntry ι N)) (h : l₁.length = l₂.length)
      (hlabel : ∀ i : Fin l₁.length, (l₁.get i).1 = (l₂.get (Fin.cast h i)).1),
      gueLabelWeight l₁ p = gueLabelWeight l₂ (castLength l₁ l₂ h p) := by
  induction p with
  | nil =>
      intro l₂ h _
      cases l₂ with
      | nil => rw [castLength_nil]
      | cons a as => simp at h
  | cons e l k p₀ ih =>
      intro l₂ h hlabel
      cases l with
      | nil => exact absurd k.isLt (by simp)
      | cons x l' =>
          cases l₂ with
          | nil => simp at h
          | cons y l₂ =>
              cases l₂ with
              | nil => simp at h
              | cons z l₂' =>
                  have hkk : l'.length = l₂'.length := by
                    have h' := h
                    simp only [List.length_cons] at h'
                    omega
                  have hk₁ : (x :: l').length = (z :: l₂').length := by
                    simp only [List.length_cons]
                    omega
                  have hk₀ : l'.length = l₂'.length := hkk
                  have hlen : ((x :: l').eraseIdx k).length = l'.length := by
                    rw [List.length_eraseIdx, ite_eq_left k.isLt]
                    simp
                  have hlen₂ : ((z :: l₂').eraseIdx (Fin.cast hk₁ k)).length = l₂'.length := by
                    rw [List.length_eraseIdx, ite_eq_left (Fin.cast hk₁ k).isLt]
                    simp
                  have h₁ : ((x :: l').eraseIdx k).length
                      = ((z :: l₂').eraseIdx (Fin.cast hk₁ k)).length := by
                    rw [hlen, hlen₂, hk₀]
                  have hhead : e.1 = y.1 := by
                    have h0 := hlabel 0
                    rw [show Fin.cast h (0 : Fin (e :: x :: l').length) = 0 from Fin.ext rfl,
                      List.get_cons_zero, List.get_cons_zero] at h0
                    exact h0
                  have hpartner : ((x :: l').get k).1 = ((z :: l₂').get (Fin.cast hk₁ k)).1 := by
                    have hks := hlabel k.succ
                    rw [show Fin.cast h k.succ = (Fin.cast hk₁ k).succ from Fin.ext rfl] at hks
                    simpa using hks
                  have hlabel' : ∀ i : Fin ((x :: l').eraseIdx k).length,
                      (((x :: l').eraseIdx k).get i).1
                        = (((z :: l₂').eraseIdx (Fin.cast hk₁ k)).get (Fin.cast h₁ i)).1 := by
                    intro i
                    rw [succAbove_get_eraseIdx x l' k hlen i]
                    rw [succAbove_get_eraseIdx z l₂' (Fin.cast hk₁ k) hlen₂ (Fin.cast h₁ i)]
                    have hidx : Fin.cast hk₁ (k.succAbove (Fin.cast hlen i))
                        = (Fin.cast hk₁ k).succAbove (Fin.cast hlen₂ (Fin.cast h₁ i)) := by
                      rw [fin_cast_succAbove hk₁ hk₀ k (Fin.cast hlen i)]
                      rfl
                    rw [← hidx]
                    have hfin := hlabel (k.succAbove (Fin.cast hlen i)).succ
                    rw [show Fin.cast h ((k.succAbove (Fin.cast hlen i)).succ)
                        = (Fin.cast hk₁ (k.succAbove (Fin.cast hlen i))).succ from Fin.ext rfl] at hfin
                    simpa using hfin
                  rw [gueLabelWeight_cons, castLength_cons, gueLabelWeight_cons]
                  change gueLabelCov e ((x :: l').get k) *
                      gueLabelWeight ((x :: l').eraseIdx k) p₀ =
                    gueLabelCov y ((z :: l₂').get (Fin.cast hk₁ k)) *
                      gueLabelWeight ((z :: l₂').eraseIdx (Fin.cast hk₁ k))
                        (castLength ((x :: l').eraseIdx k)
                          ((z :: l₂').eraseIdx (Fin.cast hk₁ k)) h₁ p₀)
                  rw [ih ((z :: l₂').eraseIdx (Fin.cast hk₁ k)) h₁ hlabel']
                  have hfac : gueLabelCov e ((x :: l').get k)
                      = gueLabelCov y ((z :: l₂').get (Fin.cast hk₁ k)) := by
                    simp only [gueLabelCov, hhead, hpartner]
                  rw [hfac]

/-! ### Index-weight compatibility

The index weight `gueIndexWeight` is **not** invariant under an arbitrary length-preserving cast:
`gueIndexCov` inspects the matrix-index (second) components of the two entries, and the entries of
`l₁` and `l₂` are unrelated a priori.  What `castLength` transports is the *positional pattern* of
index constraints.  Accordingly the honest statement is the conditional one below: if the matrix
indices agree positionwise (in particular if `l₂` is any list with the same label *and* index
pattern), then the index weight is transported. -/

/-- **The index weight is transported when the matrix indices agree positionwise.** -/
theorem gueIndexWeight_castLength {l₁ : List (GUEEntry ι N)} (p : GUEPairing l₁) :
    ∀ (l₂ : List (GUEEntry ι N)) (h : l₁.length = l₂.length)
      (hidx : ∀ i : Fin l₁.length, (l₁.get i).2 = (l₂.get (Fin.cast h i)).2),
      gueIndexWeight l₁ p = gueIndexWeight l₂ (castLength l₁ l₂ h p) := by
  induction p with
  | nil =>
      intro l₂ h hidx
      cases l₂ with
      | nil => rw [castLength_nil]
      | cons a as => simp at h
  | cons e l k p₀ ih =>
      intro l₂ h hidx
      cases l with
      | nil => exact absurd k.isLt (by simp)
      | cons x l' =>
          cases l₂ with
          | nil => simp at h
          | cons y l₂ =>
              cases l₂ with
              | nil => simp at h
              | cons z l₂' =>
                  have hkk : l'.length = l₂'.length := by
                    have h' := h
                    simp only [List.length_cons] at h'
                    omega
                  have hk₁ : (x :: l').length = (z :: l₂').length := by
                    simp only [List.length_cons]
                    omega
                  have hk₀ : l'.length = l₂'.length := hkk
                  have hlen : ((x :: l').eraseIdx k).length = l'.length := by
                    rw [List.length_eraseIdx, ite_eq_left k.isLt]
                    simp
                  have hlen₂ : ((z :: l₂').eraseIdx (Fin.cast hk₁ k)).length = l₂'.length := by
                    rw [List.length_eraseIdx, ite_eq_left (Fin.cast hk₁ k).isLt]
                    simp
                  have h₁ : ((x :: l').eraseIdx k).length
                      = ((z :: l₂').eraseIdx (Fin.cast hk₁ k)).length := by
                    rw [hlen, hlen₂, hk₀]
                  have hhead : e.2 = y.2 := by
                    have h0 := hidx 0
                    rw [show Fin.cast h (0 : Fin (e :: x :: l').length) = 0 from Fin.ext rfl,
                      List.get_cons_zero, List.get_cons_zero] at h0
                    exact h0
                  have hpartner : ((x :: l').get k).2 = ((z :: l₂').get (Fin.cast hk₁ k)).2 := by
                    have hks := hidx k.succ
                    rw [show Fin.cast h k.succ = (Fin.cast hk₁ k).succ from Fin.ext rfl] at hks
                    simpa using hks
                  have hidx' : ∀ i : Fin ((x :: l').eraseIdx k).length,
                      (((x :: l').eraseIdx k).get i).2
                        = (((z :: l₂').eraseIdx (Fin.cast hk₁ k)).get (Fin.cast h₁ i)).2 := by
                    intro i
                    rw [succAbove_get_eraseIdx x l' k hlen i]
                    rw [succAbove_get_eraseIdx z l₂' (Fin.cast hk₁ k) hlen₂ (Fin.cast h₁ i)]
                    have hidxcast : Fin.cast hk₁ (k.succAbove (Fin.cast hlen i))
                        = (Fin.cast hk₁ k).succAbove (Fin.cast hlen₂ (Fin.cast h₁ i)) := by
                      rw [fin_cast_succAbove hk₁ hk₀ k (Fin.cast hlen i)]
                      rfl
                    rw [← hidxcast]
                    have hfin := hidx (k.succAbove (Fin.cast hlen i)).succ
                    rw [show Fin.cast h ((k.succAbove (Fin.cast hlen i)).succ)
                        = (Fin.cast hk₁ (k.succAbove (Fin.cast hlen i))).succ from Fin.ext rfl] at hfin
                    simpa using hfin
                  rw [gueIndexWeight_cons, castLength_cons, gueIndexWeight_cons]
                  change gueIndexCov e ((x :: l').get k) *
                      gueIndexWeight ((x :: l').eraseIdx k) p₀ =
                    gueIndexCov y ((z :: l₂').get (Fin.cast hk₁ k)) *
                      gueIndexWeight ((z :: l₂').eraseIdx (Fin.cast hk₁ k))
                        (castLength ((x :: l').eraseIdx k)
                          ((z :: l₂').eraseIdx (Fin.cast hk₁ k)) h₁ p₀)
                  rw [ih ((z :: l₂').eraseIdx (Fin.cast hk₁ k)) h₁ hidx']
                  have hfac : gueIndexCov e ((x :: l').get k)
                      = gueIndexCov y ((z :: l₂').get (Fin.cast hk₁ k)) := by
                    simp only [gueIndexCov, hhead, hpartner]
                  rw [hfac]

/-- **The Kronecker weight is transported when both labels and matrix indices agree
positionwise.** -/
theorem gueDeltaWeight_castLength {l₁ : List (GUEEntry ι N)} (p : GUEPairing l₁) :
    ∀ (l₂ : List (GUEEntry ι N)) (h : l₁.length = l₂.length)
      (hlabel : ∀ i : Fin l₁.length, (l₁.get i).1 = (l₂.get (Fin.cast h i)).1)
      (hidx : ∀ i : Fin l₁.length, (l₁.get i).2 = (l₂.get (Fin.cast h i)).2),
      gueDeltaWeight l₁ p = gueDeltaWeight l₂ (castLength l₁ l₂ h p) := by
  intro l₂ h hlabel hidx
  rw [gueDeltaWeight_eq_label_mul_index, gueDeltaWeight_eq_label_mul_index,
    gueLabelWeight_castLength p l₂ h hlabel, gueIndexWeight_castLength p l₂ h hidx]

/-! ### The finite pairing sums -/

/-- **Transport of a finite sum over pairings along a length-preserving cast.** -/
theorem sum_castLength {M : Type*} [AddCommMonoid M] {l₁ l₂ : List (GUEEntry ι N)}
    (h : l₁.length = l₂.length) (F : GUEPairing l₂ → M) :
    (∑ p : GUEPairing l₁, F (castLength l₁ l₂ h p)) = ∑ p : GUEPairing l₂, F p :=
  Equiv.sum_comp (castLengthEquiv h) F

/-- The number of pairings depends only on the length of the list. -/
theorem card_castLength {l₁ l₂ : List (GUEEntry ι N)} (h : l₁.length = l₂.length) :
    Fintype.card (GUEPairing l₁) = Fintype.card (GUEPairing l₂) :=
  Fintype.card_congr (castLengthEquiv h)

/-- The sum of the label weights is invariant under a length-preserving cast with equal labels. -/
theorem sum_gueLabelWeight_castLength {l₁ l₂ : List (GUEEntry ι N)} (h : l₁.length = l₂.length)
    (hlabel : ∀ i : Fin l₁.length, (l₁.get i).1 = (l₂.get (Fin.cast h i)).1) :
    (∑ p : GUEPairing l₁, gueLabelWeight l₁ p) = ∑ p : GUEPairing l₂, gueLabelWeight l₂ p := by
  rw [← sum_castLength (M := ℂ) h (fun p => gueLabelWeight l₂ p)]
  exact Finset.sum_congr rfl fun p _ => gueLabelWeight_castLength p l₂ h hlabel

/-- The sum of the index weights is invariant under a length-preserving cast with equal index
pattern. -/
theorem sum_gueIndexWeight_castLength {l₁ l₂ : List (GUEEntry ι N)} (h : l₁.length = l₂.length)
    (hidx : ∀ i : Fin l₁.length, (l₁.get i).2 = (l₂.get (Fin.cast h i)).2) :
    (∑ p : GUEPairing l₁, gueIndexWeight l₁ p) = ∑ p : GUEPairing l₂, gueIndexWeight l₂ p := by
  rw [← sum_castLength (M := ℂ) h (fun p => gueIndexWeight l₂ p)]
  exact Finset.sum_congr rfl fun p _ => gueIndexWeight_castLength p l₂ h hidx

/-- The sum of the Kronecker weights is invariant under a length-preserving cast with equal labels
and index pattern. -/
theorem sum_gueDeltaWeight_castLength {l₁ l₂ : List (GUEEntry ι N)} (h : l₁.length = l₂.length)
    (hlabel : ∀ i : Fin l₁.length, (l₁.get i).1 = (l₂.get (Fin.cast h i)).1)
    (hidx : ∀ i : Fin l₁.length, (l₁.get i).2 = (l₂.get (Fin.cast h i)).2) :
    (∑ p : GUEPairing l₁, gueDeltaWeight l₁ p) = ∑ p : GUEPairing l₂, gueDeltaWeight l₂ p := by
  rw [← sum_castLength (M := ℂ) h (fun p => gueDeltaWeight l₂ p)]
  exact Finset.sum_congr rfl fun p _ => gueDeltaWeight_castLength p l₂ h hlabel hidx

end GUEPairing

end

end GUEStrongConvergence
