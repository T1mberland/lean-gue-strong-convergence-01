/-
# Positional partner permutation of a GUE pairing

Given a recursive pairing `GUEPairing l`, this file constructs the actual partner permutation of
`Fin l.length`.  The construction tracks the `eraseIdx` reinsertion: the head is paired with
position `k+1`, and the remaining pairing acts on the erased list, reinserted through
`Fin.succAbove` / `Fin.predAbove`.

The main results are that the partner map has no fixed points and is an involution, hence a
genuine fixed-point-free permutation.  No asymptotic statement is made.
-/
import GUEStrongConvergence.Probability.GUEPairingFormula

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Matrix ENNReal Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace GUEStrongConvergence

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- Map a position of `Fin (n+1)` other than `k` to the corresponding position in `Fin n`
after deleting `k`. -/
def eraseIndex : (n : ℕ) → (k j : Fin (n + 1)) → j ≠ k → Fin n
  | 0, k, j, h => False.elim (h (by ext; omega))
  | n + 1, k, j, h =>
    if hk : k = Fin.last (n + 1) then
      Fin.castLT j (by
        have hj : j.val ≠ n + 1 := by
          intro hh
          exact h (by ext <;> simp [hk, hh])
        omega)
    else
      let p : Fin (n + 1) := Fin.castLT k (by
        have hk' : k.val ≠ n + 1 := by
          intro hh
          exact hk (by ext; simpa using hh)
        omega)
      p.predAbove j

/-- The deletion map is a left inverse of the reinsertion embedding. -/
lemma succAbove_eraseIndex (n : ℕ) (k j : Fin (n + 1)) (h : j ≠ k) :
    k.succAbove (eraseIndex n k j h) = j := by
  cases n with
  | zero => exact (h (by ext; omega)).elim
  | succ n =>
    by_cases hk : k = Fin.last (n + 1)
    · subst hk
      simp only [eraseIndex, dif_pos rfl, Fin.succAbove_last]
      exact Fin.castSucc_castLT j _
    · have hlt : k.val < n + 1 := by
        have hk' : k.val ≠ n + 1 := by
          intro hh
          exact hk (by ext; simpa using hh)
        omega
      let p : Fin (n + 1) := Fin.castLT k hlt
      have hp : p.castSucc = k := Fin.castSucc_castLT k hlt
      simp only [eraseIndex, dif_neg hk]
      change k.succAbove (p.predAbove j) = j
      rw [← hp]
      exact Fin.succAbove_predAbove (p := p) (by simpa [hp] using h)

/-- The deletion map is a right inverse of the reinsertion embedding. -/
lemma eraseIndex_succAbove (n : ℕ) (k : Fin (n + 1)) (q : Fin n) :
    eraseIndex n k (k.succAbove q) (Fin.succAbove_ne k q) = q := by
  cases n with
  | zero => exact Fin.elim0 q
  | succ n =>
    by_cases hk : k = Fin.last (n + 1)
    · subst hk
      simp only [eraseIndex, dif_pos rfl, Fin.succAbove_last]
      exact Fin.castLT_castSucc q _
    · have hlt : k.val < n + 1 := by
        have hk' : k.val ≠ n + 1 := by
          intro hh
          exact hk (by ext; simpa using hh)
        omega
      let p : Fin (n + 1) := Fin.castLT k hlt
      have hp : p.castSucc = k := Fin.castSucc_castLT k hlt
      simp only [eraseIndex, dif_neg hk]
      change p.predAbove (k.succAbove q) = q
      rw [← hp]
      exact Fin.predAbove_succAbove p q

/-- The partner permutation of `Fin l.length` induced by a recursive pairing. -/
def partner : (l : List (GUEEntry ι N)) → GUEPairing l → Fin l.length → Fin l.length
  | _, .nil, i => Fin.elim0 i
  | _, .cons e [] k p, i => False.elim (Fin.elim0 k)
  | _, .cons e (x :: l) k p, i =>
    if h0 : i = 0 then k.succ
    else if hk : i = k.succ then 0
    else
      let j : Fin ((x :: l).length) := i.pred h0
      have hlen : ((x :: l).eraseIdx k).length = l.length := by
        rw [List.length_eraseIdx, ite_eq_left k.isLt]
        simp
      let q : Fin ((x :: l).eraseIdx k).length :=
        partner ((x :: l).eraseIdx k) p (Fin.cast hlen.symm
          (eraseIndex l.length k j (by
            intro hjk
            exact hk (by
              calc i = j.succ := (Fin.succ_pred i h0).symm
                _ = k.succ := by rw [hjk]))))
      (k.succAbove (Fin.cast hlen q)).succ

@[simp] lemma partner_cons_zero (e x : GUEEntry ι N) (l : List (GUEEntry ι N))
    (k : Fin (x :: l).length) (p : GUEPairing ((x :: l).eraseIdx k)) :
    partner (e :: x :: l) (GUEPairing.cons e (x :: l) k p)
        (0 : Fin (e :: x :: l).length) = k.succ := by
  simp [partner]

@[simp] lemma partner_cons_head (e x : GUEEntry ι N) (l : List (GUEEntry ι N))
    (k : Fin (x :: l).length) (p : GUEPairing ((x :: l).eraseIdx k))
    (i : Fin (e :: x :: l).length) (h : i = k.succ) :
    partner (e :: x :: l) (GUEPairing.cons e (x :: l) k p) i = 0 := by
  subst h
  simp [partner]

/-- If `i` is not a successor of `k`, then its predecessor is not `k`. -/
lemma pred_ne_of_ne_succ {n : ℕ} {i : Fin (n + 1)} (h0 : i ≠ 0) {k : Fin n}
    (hk : i ≠ k.succ) : i.pred h0 ≠ k := by
  intro h
  apply hk
  calc i = (i.pred h0).succ := (Fin.succ_pred i h0).symm
    _ = k.succ := by rw [h]

lemma partner_cons_other (e x : GUEEntry ι N) (l : List (GUEEntry ι N))
    (k : Fin (x :: l).length) (p : GUEPairing ((x :: l).eraseIdx k))
    (hlen : ((x :: l).eraseIdx k).length = l.length)
    (i : Fin (e :: x :: l).length) (h0 : i ≠ 0) (hk : i ≠ k.succ) :
    partner (e :: x :: l) (GUEPairing.cons e (x :: l) k p) i =
      (k.succAbove (Fin.cast hlen
        (partner ((x :: l).eraseIdx k) p
          (Fin.cast hlen.symm
            (eraseIndex l.length k (i.pred h0) (pred_ne_of_ne_succ h0 hk)))))).succ := by
  simp [partner, h0, hk]

/-- The partner map has no fixed points. -/
lemma partner_ne_self {l : List (GUEEntry ι N)} (p : GUEPairing l) (i : Fin l.length) :
    partner l p i ≠ i := by
  induction p with
  | nil => exact Fin.elim0 i
  | cons e l k p ih =>
    cases l with
    | nil => exact Fin.elim0 k
    | cons x l' =>
      by_cases h0 : i = 0
      · subst h0
        simp [partner]
      · by_cases hk : i = k.succ
        · subst hk
          simpa [partner, eq_comm] using Fin.succ_ne_zero k
        · have hpred : i.pred h0 ≠ k := pred_ne_of_ne_succ h0 hk
          have hlen : ((x :: l').eraseIdx k).length = l'.length := by
            rw [List.length_eraseIdx, ite_eq_left k.isLt]
            simp
          simp only [partner, dif_neg h0, dif_neg hk]
          intro hEq
          have hi : i = (i.pred h0).succ := (Fin.succ_pred i h0).symm
          have hs : k.succAbove (Fin.cast hlen
              (partner ((x :: l').eraseIdx k) p
                (Fin.cast hlen.symm (eraseIndex l'.length k (i.pred h0) hpred)))) =
              i.pred h0 := by
            apply Fin.succ_inj.mp
            exact hEq.trans hi
          have hq : Fin.cast hlen
              (partner ((x :: l').eraseIdx k) p
                (Fin.cast hlen.symm (eraseIndex l'.length k (i.pred h0) hpred))) =
              eraseIndex l'.length k (i.pred h0) hpred := by
            apply Fin.succAbove_right_injective
            rw [hs, succAbove_eraseIndex]
          have hq' : partner ((x :: l').eraseIdx k) p
                (Fin.cast hlen.symm (eraseIndex l'.length k (i.pred h0) hpred)) =
              Fin.cast hlen.symm (eraseIndex l'.length k (i.pred h0) hpred) := by
            simpa using Fin.cast_injective hlen hq
          exact ih (Fin.cast hlen.symm (eraseIndex l'.length k (i.pred h0) hpred)) hq'

/-- The partner map is an involution. -/
lemma partner_involutive {l : List (GUEEntry ι N)} (p : GUEPairing l) :
    Function.Involutive (partner l p) := by
  induction p with
  | nil => intro i; exact Fin.elim0 i
  | cons e l k p ih =>
    cases l with
    | nil => intro i; exact Fin.elim0 k
    | cons x l' =>
      intro i
      by_cases h0 : i = 0
      · subst h0
        simpa using partner_cons_zero e x l' k p
      · by_cases hk : i = k.succ
        · subst hk
          simpa using partner_cons_head e x l' k p k.succ rfl
        · have hpred : i.pred h0 ≠ k := pred_ne_of_ne_succ h0 hk
          let hlen : ((x :: l').eraseIdx k).length = l'.length := by
            rw [List.length_eraseIdx, ite_eq_left k.isLt]
            simp
          rw [partner_cons_other e x l' k p hlen i h0 hk]
          let q : Fin ((x :: l').eraseIdx k).length :=
            partner ((x :: l').eraseIdx k) p
              (Fin.cast hlen.symm (eraseIndex l'.length k (i.pred h0) hpred))
          change partner (e :: x :: l') (GUEPairing.cons e (x :: l') k p)
            (k.succAbove (Fin.cast hlen q)).succ = i
          have h0' : (k.succAbove (Fin.cast hlen q)).succ ≠ 0 :=
            Fin.succ_ne_zero _
          have hk' : (k.succAbove (Fin.cast hlen q)).succ ≠ k.succ := by
            intro h
            exact Fin.succAbove_ne k (Fin.cast hlen q) (Fin.succ_inj.mp h)
          rw [partner_cons_other e x l' k p hlen
            ((k.succAbove (Fin.cast hlen q)).succ) h0' hk']
          rw [← Fin.succ_pred i h0]
          congr 1
          simp only [Fin.pred_succ, eraseIndex_succAbove, Fin.cast_cast, Fin.cast_eq_self]
          rw [ih (Fin.cast hlen.symm (eraseIndex l'.length k (i.pred h0) hpred))]
          simp only [Fin.cast_cast, Fin.cast_eq_self]
          exact succAbove_eraseIndex l'.length k (i.pred h0) hpred

/-- The fixed-point-free partner permutation of a recursive pairing. -/
def partnerPerm {l : List (GUEEntry ι N)} (p : GUEPairing l) :
    Equiv.Perm (Fin l.length) where
  toFun := partner l p
  invFun := partner l p
  left_inv := partner_involutive p
  right_inv := partner_involutive p

@[simp] lemma partnerPerm_apply {l : List (GUEEntry ι N)} (p : GUEPairing l)
    (i : Fin l.length) : partnerPerm p i = partner l p i := rfl

lemma partnerPerm_involutive {l : List (GUEEntry ι N)} (p : GUEPairing l) :
    Function.Involutive (partnerPerm p) := partner_involutive p

lemma partnerPerm_ne_self {l : List (GUEEntry ι N)} (p : GUEPairing l)
    (i : Fin l.length) : partnerPerm p i ≠ i := partner_ne_self p i

lemma partnerPerm_bijective {l : List (GUEEntry ι N)} (p : GUEPairing l) :
    Function.Bijective (partnerPerm p) := (partnerPerm p).bijective

end

end GUEStrongConvergence
