import GUEStrongConvergence.Probability.GUEBlockSplit
import GUEStrongConvergence.Probability.GUEPairingCastSelf

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

theorem partner_append_aux : ∀ (n : ℕ) (l₁ : List (GUEEntry ι N)), l₁.length = n →
    ∀ (l₂ : List (GUEEntry ι N)) (p₁ : GUEPairing l₁) (p₂ : GUEPairing l₂),
      (∀ i : Fin l₁.length,
        (partner (l₁ ++ l₂) (append l₁ l₂ p₁ p₂)
          ⟨i.val, by rw [List.length_append]; exact Nat.lt_add_right _ i.isLt⟩).val =
            (partner l₁ p₁ i).val) ∧
      (∀ j : Fin l₂.length,
        (partner (l₁ ++ l₂) (append l₁ l₂ p₁ p₂)
          ⟨l₁.length + j.val, by rw [List.length_append]; omega⟩).val =
            l₁.length + (partner l₂ p₂ j).val) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro l₁ hl l₂ p₁ p₂
    cases l₁ with
    | nil =>
      constructor
      · intro i; exact Fin.elim0 i
      · intro j
        cases p₁ with
        | nil =>
          have hidx : (⟨(0 : ℕ) + j.val, by simpa using j.isLt⟩ : Fin l₂.length) = j :=
            Fin.ext (by simp)
          show (partner ([] ++ l₂) (append [] l₂ nil p₂) ⟨0 + j.val, _⟩).val =
            0 + (partner l₂ p₂ j).val
          rw [hidx]
          simp
    | cons e l =>
      cases p₁ with
      | cons _ _ k p =>
        cases l with
        | nil => exact Fin.elim0 k
        | cons x l' =>
          let K : Fin (x :: (l' ++ l₂)).length :=
            ⟨k.val, by
              have h := k.isLt
              simp only [List.length_cons, List.length_append] at h ⊢
              omega⟩
          let P : GUEPairing ((x :: (l' ++ l₂)).eraseIdx K.val) :=
            (eraseIdx_append_left (x :: l') l₂ k).symm ▸ append ((x :: l').eraseIdx k) l₂ p p₂
          have hApp' : append (e :: x :: l') l₂ (cons e (x :: l') k p) p₂
              = cons e (x :: (l' ++ l₂)) K P := by
            rw [append_cons]
            rfl

          rw [hApp']
          simp only [List.cons_append]
          let E : List (GUEEntry ι N) := (x :: l').eraseIdx k.val
          have hEdef : E = (x :: l').eraseIdx k.val := rfl
          have hlen : E.length = l'.length := by
            rw [hEdef, List.length_eraseIdx, ite_eq_left k.isLt]
            simp
          have hKval : K.val = k.val := rfl
          have hlenM : ((x :: (l' ++ l₂)).eraseIdx K.val).length = (l' ++ l₂).length := by
            rw [List.length_eraseIdx, ite_eq_left K.isLt]
            simp
          have hElt : E.length < n := by
            have h1 : E.length = l'.length := hlen
            have h2 : (e :: x :: l').length = n := hl
            simp only [List.length_cons] at h2
            omega
          constructor
          · intro i
            by_cases h0 : i = 0
            · subst h0
              simp only [partner_cons_zero]
              rfl
            · by_cases hk : i = k.succ
              · subst hk
                have hidx : (⟨(k.succ : Fin (e :: x :: l').length).val,
                      by
                        simp only [Fin.val_succ, List.length_cons, List.length_append]
                        have h := k.isLt
                        simp only [List.length_cons] at h
                        omega⟩
                    : Fin (e :: x :: (l' ++ l₂)).length) = K.succ := rfl
                rw [hidx]
                rw [partner_cons_head e x (l' ++ l₂) K P K.succ rfl]
                rw [partner_cons_head e x l' k p k.succ rfl]
                rfl
              · -- generic index
                let I : Fin (e :: x :: (l' ++ l₂)).length :=
                  ⟨i.val, by
                    have h := i.isLt
                    simp only [List.length_cons, List.length_append] at h ⊢
                    omega⟩
                have hIeq : (⟨i.val, by
                      have h := i.isLt
                      simp only [List.length_cons, List.length_append] at h ⊢
                      omega⟩ : Fin (e :: x :: (l' ++ l₂)).length) = I := rfl
                rw [hIeq]
                have hIval : I.val = i.val := rfl
                have hI0 : I ≠ 0 := by
                  intro h
                  apply h0
                  have hv : i.val = 0 := by
                    have hh := congrArg Fin.val h
                    simp only [Fin.val_zero] at hh
                    rwa [hIval] at hh
                  exact Fin.ext hv
                have hIK : I ≠ K.succ := by
                  intro h
                  apply hk
                  have hv : i.val = (k.succ).val := by
                    have hh := congrArg Fin.val h
                    rw [Fin.val_succ, hKval, hIval] at hh
                    exact hh
                  exact Fin.ext hv
                rw [partner_cons_other e x (l' ++ l₂) K P hlenM I hI0 hIK]
                rw [partner_cons_other e x l' k p hlen i h0 hk]
                let qR : Fin ((x :: (l' ++ l₂)).eraseIdx K.val).length :=
                  Fin.cast hlenM.symm (eraseIndex (l' ++ l₂).length K (I.pred hI0)
                    (pred_ne_of_ne_succ hI0 hIK))
                let qL : Fin E.length :=
                  Fin.cast hlen.symm (eraseIndex l'.length k (i.pred h0)
                    (pred_ne_of_ne_succ h0 hk))
                change (K.succAbove (Fin.cast hlenM (partner ((x :: (l' ++ l₂)).eraseIdx K.val) P qR))).succ.val
                    = ((k.succAbove (Fin.cast hlen (partner E p qL))).succ).val
                have hqval : (partner ((x :: (l' ++ l₂)).eraseIdx K.val) P qR).val
                    = (partner E p qL).val := by
                  have hEA : ((x :: (l' ++ l₂)).eraseIdx K.val) = E ++ l₂ :=
                    eraseIdx_append_left (x :: l') l₂ k
                  have hAB : (E ++ l₂).length = ((x :: (l' ++ l₂)).eraseIdx K.val).length :=
                    congrArg List.length hEA.symm
                  have hP' : P = castLength (E ++ l₂)
                      ((x :: (l' ++ l₂)).eraseIdx K.val) hAB (append E l₂ p p₂) := by
                    show (eraseIdx_append_left (x :: l') l₂ k).symm ▸ append ((x :: l').eraseIdx k) l₂ p p₂
                        = castLength (E ++ l₂) ((x :: (l' ++ l₂)).eraseIdx K.val) hAB
                          (append E l₂ p p₂)
                    exact eqRec_eq_castLength hEA.symm _
                  rw [hP']
                  let u : Fin (E ++ l₂).length :=
                    ⟨qL.val, by
                      have := qL.isLt
                      simp only [List.length_append]
                      omega⟩
                  have hqRu : qR = Fin.cast hAB u := by
                    apply Fin.ext
                    show qR.val = u.val
                    show (Fin.cast hlenM.symm (eraseIndex (l' ++ l₂).length K (I.pred hI0)
                      (pred_ne_of_ne_succ hI0 hIK))).val = u.val
                    rw [Fin.val_cast]
                    show (eraseIndex (l' ++ l₂).length K (I.pred hI0)
                      (pred_ne_of_ne_succ hI0 hIK)).val = qL.val
                    show (eraseIndex (l' ++ l₂).length K (I.pred hI0)
                      (pred_ne_of_ne_succ hI0 hIK)).val
                        = (Fin.cast hlen.symm (eraseIndex l'.length k (i.pred h0)
                          (pred_ne_of_ne_succ h0 hk))).val
                    rw [Fin.val_cast, eraseIndex_val, eraseIndex_val]
                    have hpv : (I.pred hI0).val = (i.pred h0).val := by
                      rw [Fin.val_pred, Fin.val_pred, hIval]
                    rw [hpv, hKval]
                  rw [hqRu, partner_castLength (append E l₂ p p₂)
                    ((x :: (l' ++ l₂)).eraseIdx K.val) hAB u]
                  have hIH := (ih E.length hElt E rfl l₂ p p₂).1 qL
                  have hu : u = (⟨qL.val, by
                      rw [List.length_append]
                      exact Nat.lt_add_right _ qL.isLt⟩ : Fin (E ++ l₂).length) := rfl
                  rw [hu, Fin.val_cast, hIH]
                have hsuccval : (K.succAbove
                      (Fin.cast hlenM (partner ((x :: (l' ++ l₂)).eraseIdx K.val) P qR))).val
                    = (k.succAbove (Fin.cast hlen (partner E p qL))).val := by
                  rw [val_succAbove, val_succAbove]
                  simp only [Fin.val_cast]
                  rw [hqval, hKval]
                simp only [Fin.val_succ]
                rw [hsuccval]
          · intro j
            let I : Fin (e :: x :: (l' ++ l₂)).length :=
              ⟨(e :: x :: l').length + j.val, by
                simp only [List.length_cons, List.length_append]
                have := j.isLt
                omega⟩
            have hIeq : (⟨(e :: x :: l').length + j.val, by
                  simp only [List.length_cons, List.length_append]
                  have := j.isLt
                  omega⟩ : Fin (e :: x :: (l' ++ l₂)).length) = I := rfl
            rw [hIeq]
            have hI0 : I ≠ 0 := by
              intro h
              have hh := congrArg Fin.val h
              simp only [Fin.val_zero] at hh
              have h2 : I.val = (e :: x :: l').length + j.val := rfl
              simp only [List.length_cons] at h2
              omega
            have hIK : I ≠ K.succ := by
              intro h
              have hh := congrArg Fin.val h
              rw [Fin.val_succ, hKval] at hh
              have h2 : I.val = (e :: x :: l').length + j.val := rfl
              have hk := k.isLt
              simp only [List.length_cons] at h2 hk
              omega
            rw [partner_cons_other e x (l' ++ l₂) K P hlenM I hI0 hIK]
            let qR : Fin ((x :: (l' ++ l₂)).eraseIdx K.val).length :=
              Fin.cast hlenM.symm (eraseIndex (l' ++ l₂).length K (I.pred hI0)
                (pred_ne_of_ne_succ hI0 hIK))
            change ((K.succAbove (Fin.cast hlenM (partner ((x :: (l' ++ l₂)).eraseIdx K.val) P qR))).succ).val
                = (e :: x :: l').length + (partner l₂ p₂ j).val
            have hqval : (partner ((x :: (l' ++ l₂)).eraseIdx K.val) P qR).val
                = E.length + (partner l₂ p₂ j).val := by
              have hEA : ((x :: (l' ++ l₂)).eraseIdx K.val) = E ++ l₂ :=
                eraseIdx_append_left (x :: l') l₂ k
              have hAB : (E ++ l₂).length = ((x :: (l' ++ l₂)).eraseIdx K.val).length :=
                congrArg List.length hEA.symm
              have hP' : P = castLength (E ++ l₂)
                  ((x :: (l' ++ l₂)).eraseIdx K.val) hAB (append E l₂ p p₂) := by
                show (eraseIdx_append_left (x :: l') l₂ k).symm ▸ append ((x :: l').eraseIdx k) l₂ p p₂
                    = castLength (E ++ l₂) ((x :: (l' ++ l₂)).eraseIdx K.val) hAB
                      (append E l₂ p p₂)
                exact eqRec_eq_castLength hEA.symm _
              rw [hP']
              let u : Fin (E ++ l₂).length :=
                ⟨E.length + j.val, by
                  have := j.isLt
                  simp only [List.length_append]
                  omega⟩
              have hqRu : qR = Fin.cast hAB u := by
                apply Fin.ext
                show qR.val = u.val
                show (Fin.cast hlenM.symm (eraseIndex (l' ++ l₂).length K (I.pred hI0)
                  (pred_ne_of_ne_succ hI0 hIK))).val = E.length + j.val
                rw [Fin.val_cast, eraseIndex_val]
                have hpv : (I.pred hI0).val = l'.length + 1 + j.val := by
                  rw [Fin.val_pred]
                  show (e :: x :: l').length + j.val - 1 = l'.length + 1 + j.val
                  simp only [List.length_cons]
                  omega
                rw [hpv, hKval]
                have hklt : ¬ (l'.length + 1 + j.val < k.val) := by
                  have hk := k.isLt
                  simp only [List.length_cons] at hk
                  omega
                rw [ite_eq_right hklt, hlen]
                omega
              rw [hqRu, partner_castLength (append E l₂ p p₂)
                ((x :: (l' ++ l₂)).eraseIdx K.val) hAB u]
              rw [Fin.val_cast]
              have hIH := (ih E.length hElt E rfl l₂ p p₂).2 j
              rw [hIH]
            have hle : ¬ (Fin.cast hlenM (partner ((x :: (l' ++ l₂)).eraseIdx K.val) P qR)).val < K.val := by
              rw [Fin.val_cast, hqval, hKval, hlen]
              have hk := k.isLt
              simp only [List.length_cons] at hk
              have := j.isLt
              omega
            rw [Fin.val_succ, val_succAbove]
            simp only [Fin.val_cast]
            have hle' : ¬ (partner ((x :: (l' ++ l₂)).eraseIdx ↑K) P qR).val < k.val := by
              simpa only [Fin.val_cast] using hle
            rw [ite_eq_right hle', hqval]
            simp only [List.length_cons]
            omega

end GUEPairing
end
end GUEStrongConvergence
