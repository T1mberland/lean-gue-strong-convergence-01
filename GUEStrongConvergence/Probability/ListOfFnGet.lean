/-
# `List.ofFn` entry access without dependent casts

`List.getElem_ofFn` is stated with the index as a natural number bounded by the list length.
Downstream product reindexings prefer a `Fin`-indexed, cast-free form; the two lemmas below
provide it, for a general `List.ofFn` and for the GUE vertex entry list.
-/
import GUEStrongConvergence.Probability.GUEWordGenusExpansionInstance
import GUEStrongConvergence.Probability.CyclicVertexSuccessor

namespace GUEStrongConvergence

/-- Cast-free `Fin`-indexed access to `List.ofFn`. -/
lemma list_ofFn_get_val {n : ℕ} {α : Type*} (f : Fin n → α)
    (i : Fin (List.ofFn f).length) :
    (List.ofFn f).get i = f ⟨i.val, by simpa using i.isLt⟩ := by
  conv_lhs => rw [List.get_eq_getElem]
  rw [List.getElem_ofFn]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- Cast-free access to the GUE vertex entry list at an arbitrary position. -/
theorem gueVertexEntries_get_apply (w : List ι) (hpos : 1 ≤ w.length)
    (u : Fin w.length → Fin N) (i : Fin (gueVertexEntries w hpos u).length) :
    (gueVertexEntries w hpos u).get i =
      (w.get (Fin.cast (length_gueVertexEntries w hpos u) i),
        (cyclicVertex hpos u (Fin.cast (length_gueVertexEntries w hpos u) i).castSucc,
         cyclicVertex hpos u (Fin.cast (length_gueVertexEntries w hpos u) i).succ)) := by
  let j : Fin w.length := Fin.cast (length_gueVertexEntries w hpos u) i
  have hji : i = Fin.cast (length_gueVertexEntries w hpos u).symm j := by
    apply Fin.ext; rfl
  have hcast : ∀ x : Fin w.length,
      Fin.cast (length_gueVertexEntries w hpos u)
        (Fin.cast (length_gueVertexEntries w hpos u).symm x) = x := by
    intro x; exact Fin.ext rfl
  rw [hji, hcast j]
  exact gueVertexEntries_get w hpos u j

end GUEStrongConvergence
