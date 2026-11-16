import GUEStrongConvergence.Probability.GUEWalkVertices

namespace GUEStrongConvergence

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

lemma Fin.cons_val_eq {n : ℕ} {α : Type*} (x : α) (p : Fin n → α) (y : Fin (n+1)) :
    Fin.cons (α := fun _ => α) x p y = if h : y.val = 0 then x else p ⟨y.val - 1, by
      have := y.isLt; omega⟩ := by
  cases y using Fin.cases with
  | zero => simp
  | succ i =>
    rw [Fin.cons_succ]
    have h : (i.succ : Fin (n+1)).val ≠ 0 := Nat.succ_ne_zero i.val
    rw [dif_neg h]
    exact congrArg p (Fin.ext (by simp))

lemma cyclicVertex_succ_eq {k : ℕ} (hk : 1 ≤ k) (u : Fin k → Fin N) (j : Fin k) :
    cyclicVertex hk u j.succ = cyclicVertex hk u ((finRotate k j)).castSucc := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rw [show cyclicVertex hk u j.succ = u j from Fin.cons_succ _ _ _]
  show u j = Fin.cons (α := fun _ => Fin N) (u (cyclicLastIdx hk)) u ((finRotate (n+1) j)).castSucc
  rw [Fin.cons_val_eq]
  have hcoe : (finRotate (n+1) j).val = if j = Fin.last n then 0 else j.val + 1 := coe_finRotate j
  have hval : ((finRotate (n+1) j).castSucc).val = (finRotate (n+1) j).val := rfl
  split
  · rename_i h
    rw [hval] at h
    have hlast : j = Fin.last n := by
      by_contra hne
      rw [hcoe, if_neg hne] at h
      omega
    subst hlast
    rfl
  · rename_i h
    rw [hval] at h
    congr 1
    apply Fin.ext
    have hpos : (finRotate (n+1) j).val = j.val + 1 := by
      rw [hcoe]
      by_cases hlast : j = Fin.last n
      · rw [if_pos hlast]
        have hzero : (finRotate (n+1) j).val = 0 := by rw [hcoe, if_pos hlast]
        exact absurd hzero h
      · rw [if_neg hlast]
    show j.val = ((finRotate (n+1) j).castSucc).val - 1
    rw [hval, hpos]
    omega

end GUEStrongConvergence
