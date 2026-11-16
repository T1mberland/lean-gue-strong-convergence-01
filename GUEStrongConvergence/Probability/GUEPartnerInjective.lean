/-
# Injectivity of the partner permutation of a GUE pairing

The recursive pairing `GUEPairing l` records, for the head, the partner position `k` and then
recurses on `l.eraseIdx k`.  The partner permutation `partner l p` (and its bundled version
`partnerPerm p`) therefore determines the recursive pairing: the partner of `0` is `k.succ`, and
the partner of every inserted position `(k.succAbove j).succ` is the insertion of the recursive
partner (`partner_cons_succAbove`).  This file proves

`partner_injective : Function.Injective (partner l)` and
`partnerPerm_injective : Function.Injective (partnerPerm (l := l))`.

This is used to reindex sums over pairings by their partner permutations (the pairing type itself
depends on the entry list, so injectivity of the partner map is the transport-free substitute for
an inverse).
-/
import GUEStrongConvergence.Probability.GUEPairingPositions
import GUEStrongConvergence.Probability.GUEDeltaWeightProduct

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

/-- **Injectivity of the partner map**: a pairing is determined by its partner function. -/
theorem partner_injective : ∀ (l : List (GUEEntry ι N)) (p q : GUEPairing l),
    partner l p = partner l q → p = q := by
  intro l
  suffices H : ∀ n : ℕ, ∀ (l : List (GUEEntry ι N)), l.length = n →
      ∀ (p q : GUEPairing l), partner l p = partner l q → p = q from
    H l.length l rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro l hl p q h
    cases l with
    | nil => cases p; cases q; rfl
    | cons e l' =>
      cases p with
      | cons e l' k p' =>
        cases q with
        | cons _ _ k' q' =>
          cases l' with
          | nil => exact Fin.elim0 k
          | cons x xs =>
            have h0 : k = k' := by
              have hh := congrFun h 0
              rw [partner_cons_zero, partner_cons_zero] at hh
              exact Fin.succ_inj.mp hh
            subst h0
            have hlen : ((x :: xs).eraseIdx k).length = xs.length := by
              rw [List.length_eraseIdx, ite_eq_left k.isLt]
              simp
            have hp : partner ((x :: xs).eraseIdx k) p' =
                partner ((x :: xs).eraseIdx k) q' := by
              funext j
              have hh := congrFun h ((k.succAbove (Fin.cast hlen j)).succ)
              rw [partner_cons_succAbove k p' hlen j, partner_cons_succAbove k q' hlen j] at hh
              exact Fin.cast_injective hlen
                (Fin.succAbove_right_injective (p := k) (Fin.succ_inj.mp hh))
            have hlt : xs.length < n := by
              have h2 : (e :: x :: xs).length = n := hl
              simp only [List.length_cons] at h2
              omega
            rw [ih xs.length hlt ((x :: xs).eraseIdx k) hlen p' q' hp]

/-- **Injectivity of the bundled partner permutation**. -/
theorem partnerPerm_injective {l : List (GUEEntry ι N)} :
    Function.Injective (partnerPerm (l := l)) := by
  intro p q h
  apply partner_injective l p q
  exact congrArg (fun e : Equiv.Perm (Fin l.length) => (e : Fin l.length → Fin l.length)) h

end

end GUEStrongConvergence
