import GUEStrongConvergence.Probability.LemmaMWeighted
open Function Bornology Pointwise
namespace GUEStrongConvergence
noncomputable section

lemma hasCompactSupport_sub_one_of_isSmoothCutoffZeroOn
    {S : Set ℝ} {ε : ℝ} {f : ℝ → ℝ} (hS : IsCompact S)
    (h : IsSmoothCutoffZeroOn S ε f) : HasCompactSupport (fun x => f x - 1) := by
  have hbdd : Bornology.IsBounded (S + Set.Ioo (-ε) ε) :=
    (IsCompact.isBounded hS).add (Metric.isBounded_Ioo (-ε) ε)
  have hK : IsCompact (closure (S + Set.Ioo (-ε) ε)) := by
    rw [Metric.isCompact_iff_isClosed_bounded]
    exact ⟨isClosed_closure, hbdd.closure⟩
  refine HasCompactSupport.of_support_subset_isCompact hK ?_
  intro x hx
  rw [Function.mem_support] at hx
  exact subset_closure (by
    by_contra hmem
    exact hx (by simp [h.smooth.eq_one x hmem]))

end
end GUEStrongConvergence
