/-
# R3 for the GUE two-trace moment: the index weight as a product over partner positions

For a pairing `p` of a list `l` of GUE entries, the recursive index weight `gueIndexWeight l p`
(the Kronecker part of the pairing weight, `GUEWordSecondMoment`) is the product of the
transpose matchings over the partner positions:

`gueIndexWeight l p = ∏ i : Fin l.length, gueIndexCov (l.get i) (l.get (partner l p i))`.

This is the index half of `gueDeltaWeight_eq_label_mul_index` in positional form.  The proof is
the erasing induction of Worker A's `gueDeltaWeight_eq_prod_partner`, with `gueIndexCov` in place
of `gueDeltaCov`: split the product over `Fin (n+2)` into the head position `0`, the paired
position `k.succ`, and the remaining positions `(k.succAbove j).succ`, read the erased list
through `succAbove_get_eraseIdx`, use `partner_cons_succAbove` for the recursive partner, and
collapse the two copies of the head covariance with idempotence (`gueIndexCov_mul_self`).

The main result is `gueIndexWeight_eq_prod_partner`.  It is the last combinatorial input of the
two-walk slot expansion: with the positional description
`GUEWordVarianceReindex.guePairEntries_eq_ofFn`, the covariance factors become the slot indicators
`[V i = V (blockSuccPerm (σ i))]` counted by `sum_twoWalk_index_eq_pow`.
-/
import GUEStrongConvergence.Probability.GUEWordSecondMoment
import GUEStrongConvergence.Probability.GUEDeltaWeightProduct
import GUEStrongConvergence.Probability.GUEWordVarianceBound

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

/-! ### The matrix-index covariance -/

/-- The matrix-index covariance takes the values `0` and `1`. -/
lemma gueIndexCov_eq_zero_or_one (e f : GUEEntry ι N) :
    gueIndexCov e f = 0 ∨ gueIndexCov e f = 1 := by
  simp only [gueIndexCov]
  split_ifs <;> simp

/-- The matrix-index covariance is symmetric. -/
lemma gueIndexCov_comm (e f : GUEEntry ι N) : gueIndexCov e f = gueIndexCov f e := by
  simp only [gueIndexCov, and_comm, eq_comm]

/-- The matrix-index covariance is idempotent. -/
lemma gueIndexCov_mul_self (e f : GUEEntry ι N) :
    gueIndexCov e f * gueIndexCov e f = gueIndexCov e f := by
  rcases gueIndexCov_eq_zero_or_one e f with h | h <;> simp [h]

/-! ### The product identity -/

/-- **Index weight as a product over partner positions**: the recursive Kronecker weight of a
pairing is the product of the transpose matchings over all entry positions paired with their
partner. -/
theorem gueIndexWeight_eq_prod_partner (l : List (GUEEntry ι N)) (p : GUEPairing l) :
    gueIndexWeight l p =
      ∏ i : Fin l.length, gueIndexCov (l.get i) (l.get (partner l p i)) := by
  induction p with
  | nil => simp [gueIndexWeight]
  | cons e l k p ih =>
    cases l with
    | nil => exact absurd k.isLt (by simp)
    | cons x l' =>
      rw [gueIndexWeight_cons, ih]
      have hlen : ((x :: l').eraseIdx k).length = l'.length := by
        rw [List.length_eraseIdx, ite_eq_left k.isLt]
        simp
      change gueIndexCov e ((x :: l').get k) *
          (∏ j : Fin ((x :: l').eraseIdx k).length,
            gueIndexCov (((x :: l').eraseIdx k).get j)
              (((x :: l').eraseIdx k).get (partner ((x :: l').eraseIdx k) p j))) =
        ∏ i : Fin (l'.length + 2),
          gueIndexCov ((e :: x :: l').get i)
            ((e :: x :: l').get (partner (e :: x :: l')
              (GUEPairing.cons e (x :: l') k p) i))
      rw [Fin.prod_univ_succ]
      have hF0 : gueIndexCov ((e :: x :: l').get 0)
            ((e :: x :: l').get (partner (e :: x :: l')
              (GUEPairing.cons e (x :: l') k p) 0)) =
          gueIndexCov e ((x :: l').get k) := by
        rw [partner_cons_zero]
        simp
      have hFks : gueIndexCov ((e :: x :: l').get k.succ)
            ((e :: x :: l').get (partner (e :: x :: l')
              (GUEPairing.cons e (x :: l') k p) k.succ)) =
          gueIndexCov e ((x :: l').get k) := by
        rw [partner_cons_head _ _ _ _ _ _ rfl]
        simp only [List.get_cons_zero]
        exact gueIndexCov_comm _ _
      rw [hF0, Finset.prod_eq_prod_sdiff_singleton_mul
        (s := (Finset.univ : Finset (Fin (l'.length + 1))))
        (i := (k : Fin (l'.length + 1))) (Finset.mem_univ _), hFks]
      -- the product identity over the erased positions
      have hPG : (∏ j : Fin ((x :: l').eraseIdx k).length,
            gueIndexCov (((x :: l').eraseIdx k).get j)
              (((x :: l').eraseIdx k).get (partner ((x :: l').eraseIdx k) p j))) =
          ∏ i ∈ ((Finset.univ : Finset (Fin (l'.length + 1))) \ {k}),
            gueIndexCov ((e :: x :: l').get i.succ)
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
        gueIndexCov ((e :: x :: l').get i.succ)
          ((e :: x :: l').get (partner (e :: x :: l')
            (GUEPairing.cons e (x :: l') k p) i.succ))) = X
      rw [mul_comm X (gueIndexCov e ((x :: l').get k)), ← mul_assoc, gueIndexCov_mul_self]

/-! ### The two-walk index sum in slot form -/

/-- The slot entry at position `i`: label `label i`, start vertex `V i`, end vertex
`V (blockSuccPerm i)`. -/
def slotEntry (k₁ k₂ : ℕ) (label : Fin (k₁ + k₂) → ι)
    (V : Fin (k₁ + k₂) → Fin N) (i : Fin (k₁ + k₂)) : GUEEntry ι N :=
  (label i, (V i, V (blockSuccPerm k₁ k₂ i)))

/-- **Two-walk index sum in slot form**: for a fixed involution `σ` of the slots and any labelling
of the entries, the sum over vertex functions of the product of the index covariances over the
`σ`-partner positions is `N` to the two-walk loop count.  This is the two-walk analogue of
`sum_pairing_indicator_eq_pow`: the covariance `gueIndexCov` imposes both
`V i = V (blockSucc (σ i))` and `V (blockSucc i) = V (σ i)`, and the second condition is the
first one at `σ i`, so the product collapses to `∏ i, [V i = V (blockSucc (σ i))]`. -/
theorem sum_slotEntry_gueIndexCov_eq_pow (k₁ k₂ : ℕ) (label : Fin (k₁ + k₂) → ι)
    (σ : Equiv.Perm (Fin (k₁ + k₂))) (hσ : σ * σ = 1) :
    (∑ V : Fin (k₁ + k₂) → Fin N,
        ∏ i : Fin (k₁ + k₂),
          gueIndexCov (slotEntry k₁ k₂ label V i) (slotEntry k₁ k₂ label V (σ i))) =
      (N : ℂ) ^ twoWalkLoopCount k₁ k₂ σ := by
  have hσσ : ∀ i, σ (σ i) = i := by
    intro i
    have h := congrArg (fun f : Equiv.Perm (Fin (k₁ + k₂)) => f i) hσ
    simpa [Equiv.Perm.mul_apply] using h
  have hterm : ∀ (V : Fin (k₁ + k₂) → Fin N) (i : Fin (k₁ + k₂)),
      gueIndexCov (slotEntry k₁ k₂ label V i) (slotEntry k₁ k₂ label V (σ i)) =
        (if V i = V (blockSuccPerm k₁ k₂ (σ i)) then (1 : ℂ) else 0) *
          (if V (σ i) = V (blockSuccPerm k₁ k₂ (σ (σ i))) then (1 : ℂ) else 0) := by
    intro V i
    rw [hσσ i]
    have hiff : (V i = V (blockSuccPerm k₁ k₂ (σ i)) ∧
        V (blockSuccPerm k₁ k₂ i) = V (σ i)) ↔
        (V i = V (blockSuccPerm k₁ k₂ (σ i)) ∧
          V (σ i) = V (blockSuccPerm k₁ k₂ i)) := by
      rw [and_congr_right_iff]
      intro h
      exact eq_comm
    simp only [slotEntry, gueIndexCov, hiff]
    by_cases h1 : V i = V (blockSuccPerm k₁ k₂ (σ i)) <;>
      by_cases h2 : V (σ i) = V (blockSuccPerm k₁ k₂ i) <;>
      simp [h1, h2]
  have hprod : ∀ V : Fin (k₁ + k₂) → Fin N,
      (∏ i : Fin (k₁ + k₂),
          gueIndexCov (slotEntry k₁ k₂ label V i) (slotEntry k₁ k₂ label V (σ i))) =
        ∏ i : Fin (k₁ + k₂),
          (if V i = V (blockSuccPerm k₁ k₂ (σ i)) then (1 : ℂ) else 0) := by
    intro V
    simp only [hterm V]
    rw [Finset.prod_mul_distrib, Equiv.prod_comp σ
      (fun i : Fin (k₁ + k₂) =>
        if V i = V (blockSuccPerm k₁ k₂ (σ i)) then (1 : ℂ) else 0)]
    have h01 : (∏ i : Fin (k₁ + k₂),
        (if V i = V (blockSuccPerm k₁ k₂ (σ i)) then (1 : ℂ) else 0)) = 0 ∨
        (∏ i : Fin (k₁ + k₂),
          (if V i = V (blockSuccPerm k₁ k₂ (σ i)) then (1 : ℂ) else 0)) = 1 := by
      rw [Finset.prod_boole]
      split_ifs <;> simp
    rcases h01 with h | h <;> simp [h]
  rw [Finset.sum_congr rfl fun V _ => hprod V]
  exact sum_twoWalk_index_eq_pow k₁ k₂ σ

end

end GUEStrongConvergence
