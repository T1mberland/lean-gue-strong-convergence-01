/-
# R3: the delta weight as a product over the partner positions

The product identity `gueDeltaWeight l p = ∏ i, gueDeltaCov (l.get i) (l.get (partner l p i))`
is the remaining step that converts the walk sums of `GUEWordSecondMoment` into vertex counts.
The two delicate technical ingredients are proved here:

* `succAbove_get_eraseIdx`: reading `(x :: l).eraseIdx k` at `j` is reading `x :: l` at the
  insertion `k.succAbove j` (this is `List.get_eraseIdx` plus `Fin.succAbove` bookkeeping);
* `partner_cons_succAbove`: the partner of the inserted position `(k.succAbove j).succ` in
  `e :: x :: l` is the insertion of the partner from the erased list (this is
  `partner_cons_other` after `Fin.pred_succ`, `eraseIndex_succAbove` and the `Fin.cast` sandwich);
* `gueDeltaCov_mul_self`: the Kronecker covariance is idempotent, which collapses the two copies
  of the head covariance produced by `Fin.prod_univ_succ`.

With these, the remaining assembly is the product reindexing
`∏ i ∈ univ \ {k}, f i.succ = ∏ j, g j` along `Fin.succAbove` (a `Finset.prod_bij`), which is
not formalized here.
-/
import GUEStrongConvergence.Probability.ListGetEraseIdx
import GUEStrongConvergence.Probability.GUEPairingGenus
import GUEStrongConvergence.Probability.GUEWalkVertices

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Matrix ENNReal Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GUEStrongConvergence

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}


/-- The Kronecker covariance is idempotent. -/
lemma gueDeltaCov_mul_self (e f : GUEEntry ι N) :
    gueDeltaCov e f * gueDeltaCov e f = gueDeltaCov e f := by
  rcases gueDeltaCov_eq_zero_or_one e f with h | h <;> simp [h]

/-- The positional lemma: reading `(x :: l).eraseIdx k` at `j` is reading `x :: l` at the
insertion of `j`. -/
lemma succAbove_get_eraseIdx {α : Type*} (x : α) (l : List α) (k : Fin (x :: l).length)
    (hlen : ((x :: l).eraseIdx k).length = l.length)
    (j : Fin ((x :: l).eraseIdx k).length) :
    ((x :: l).eraseIdx k).get j = (x :: l).get (k.succAbove (Fin.cast hlen j)) := by
  rw [List.get_eraseIdx]
  congr 1
  ext
  by_cases h : (j : ℕ) < (k : ℕ) <;>
    simp [Fin.succAbove, Fin.lt_def, Fin.castSucc, Fin.val_succ, h]


/-- **Partner compatibility with the insertion reindexing**: the partner of the inserted position
`(k.succAbove j).succ` in `e :: x :: l` is the inserted partner from the erased list. -/
lemma partner_cons_succAbove {e x : GUEEntry ι N} {l : List (GUEEntry ι N)}
    (k : Fin (x :: l).length) (p : GUEPairing ((x :: l).eraseIdx k))
    (hlen : ((x :: l).eraseIdx k).length = l.length)
    (j : Fin ((x :: l).eraseIdx k).length) :
    partner (e :: x :: l) (GUEPairing.cons e (x :: l) k p)
        ((k.succAbove (Fin.cast hlen j)).succ) =
      (k.succAbove (Fin.cast hlen
        (partner ((x :: l).eraseIdx k) p j))).succ := by
  have h0 : ((k.succAbove (Fin.cast hlen j)).succ : Fin (e :: x :: l).length) ≠ 0 :=
    Fin.succ_ne_zero _
  have hk : ((k.succAbove (Fin.cast hlen j)).succ : Fin (e :: x :: l).length) ≠ k.succ := by
    intro h
    exact Fin.succAbove_ne k (Fin.cast hlen j) (Fin.succ_inj.mp h)
  rw [partner_cons_other e x l k p hlen _ h0 hk]
  simp only [Fin.pred_succ, eraseIndex_succAbove, Fin.cast_cast, Fin.cast_eq_self]


/-- **R3: the delta weight is the product of the covariances over the partner positions.** -/
theorem gueDeltaWeight_eq_prod_partner (l : List (GUEEntry ι N)) (p : GUEPairing l) :
    gueDeltaWeight l p =
      ∏ i : Fin l.length, gueDeltaCov (l.get i) (l.get (partner l p i)) := by
  induction p with
  | nil => simp [gueDeltaWeight]
  | cons e l k p ih =>
    cases l with
    | nil => exact absurd k.isLt (by simp)
    | cons x l' =>
      rw [gueDeltaWeight_cons, ih]
      have hlen : ((x :: l').eraseIdx k).length = l'.length := by
        rw [List.length_eraseIdx, ite_eq_left k.isLt]
        simp
      change gueDeltaCov e ((x :: l').get k) *
          (∏ j : Fin ((x :: l').eraseIdx k).length,
            gueDeltaCov (((x :: l').eraseIdx k).get j)
              (((x :: l').eraseIdx k).get (partner ((x :: l').eraseIdx k) p j))) =
        ∏ i : Fin (l'.length + 2),
          gueDeltaCov ((e :: x :: l').get i)
            ((e :: x :: l').get (partner (e :: x :: l')
              (GUEPairing.cons e (x :: l') k p) i))
      rw [Fin.prod_univ_succ]
      have hF0 : gueDeltaCov ((e :: x :: l').get 0)
            ((e :: x :: l').get (partner (e :: x :: l')
              (GUEPairing.cons e (x :: l') k p) 0)) =
          gueDeltaCov e ((x :: l').get k) := by
        rw [partner_cons_zero]
        simp
      have hFks : gueDeltaCov ((e :: x :: l').get k.succ)
            ((e :: x :: l').get (partner (e :: x :: l')
              (GUEPairing.cons e (x :: l') k p) k.succ)) =
          gueDeltaCov e ((x :: l').get k) := by
        rw [partner_cons_head _ _ _ _ _ _ rfl]
        simp only [List.get_cons_zero]
        exact gueDeltaCov_comm _ _
      rw [hF0, Finset.prod_eq_prod_sdiff_singleton_mul
        (s := (Finset.univ : Finset (Fin (l'.length + 1))))
        (i := (k : Fin (l'.length + 1))) (Finset.mem_univ _), hFks]
      -- the product identity over the erased positions
      have hPG : (∏ j : Fin ((x :: l').eraseIdx k).length,
            gueDeltaCov (((x :: l').eraseIdx k).get j)
              (((x :: l').eraseIdx k).get (partner ((x :: l').eraseIdx k) p j))) =
          ∏ i ∈ ((Finset.univ : Finset (Fin (l'.length + 1))) \ {k}),
            gueDeltaCov ((e :: x :: l').get i.succ)
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
        gueDeltaCov ((e :: x :: l').get i.succ)
          ((e :: x :: l').get (partner (e :: x :: l')
            (GUEPairing.cons e (x :: l') k p) i.succ))) = X
      rw [mul_comm X (gueDeltaCov e ((x :: l').get k)), ← mul_assoc, gueDeltaCov_mul_self]

end

end GUEStrongConvergence
