/-
# Getting an element of a list after `eraseIdx`

Mathlib provides `List.getElem_eraseIdx` in `getElem` form. The `Fin`-indexed form below is
needed when reindexing products after removing the partner position of a pairing.
-/
import Mathlib.Data.List.Basic

namespace List

/-- The `j`-th element of `l.eraseIdx k` is the `j`-th element of `l` if `j < k`, and the
`(j+1)`-th element otherwise. -/
lemma get_eraseIdx {α : Type*} (l : List α) (k : Fin l.length)
    (j : Fin (l.eraseIdx k).length) :
    (l.eraseIdx k).get j =
      l.get ⟨if (j : ℕ) < (k : ℕ) then (j : ℕ) else (j : ℕ) + 1, by
        have hlen : (l.eraseIdx (k : ℕ)).length = l.length - 1 := by
          rw [List.length_eraseIdx, ite_eq_left k.isLt]
        have h : (j : ℕ) < l.length - 1 := by simpa [hlen] using j.isLt
        split <;> omega⟩ := by
  rw [List.get_eq_getElem, List.getElem_eraseIdx, List.get_eq_getElem]
  split <;> simp_all

end List

namespace GUEStrongConvergence

/-- Project-namespace wrapper so the rejecting integrity audit covers this lemma. -/
theorem get_eraseIdx {α : Type*} (l : List α) (k : Fin l.length)
    (j : Fin (l.eraseIdx k).length) :
    (l.eraseIdx k).get j =
      l.get ⟨if (j : ℕ) < (k : ℕ) then (j : ℕ) else (j : ℕ) + 1, by
        have hlen : (l.eraseIdx (k : ℕ)).length = l.length - 1 := by
          rw [List.length_eraseIdx, ite_eq_left k.isLt]
        have h : (j : ℕ) < l.length - 1 := by simpa [hlen] using j.isLt
        split <;> omega⟩ :=
  List.get_eraseIdx l k j

end GUEStrongConvergence
