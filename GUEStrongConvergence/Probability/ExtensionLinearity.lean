import GUEStrongConvergence.Probability.HigherExtension
set_option linter.unusedSectionVars false
namespace GUEStrongConvergence
noncomputable section

theorem extOrderTerm_sub (j : ℕ) {f g : ℝ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ j f z.re) (hg : ContDiffAt ℝ j g z.re) :
    extOrderTerm j (fun y => f y - g y) z = extOrderTerm j f z - extOrderTerm j g z := by
  unfold extOrderTerm
  have hP : (fun y => f y - g y) = (f - g : ℝ → ℝ) := rfl
  rw [hP, iteratedDeriv_sub hf hg]
  push_cast
  ring

theorem almostAnalyticExtOrder_sub (k : ℕ) {f g : ℝ → ℝ} {z : ℂ}
    (hf : ∀ j, j < k → ContDiffAt ℝ j f z.re)
    (hg : ∀ j, j < k → ContDiffAt ℝ j g z.re) :
    almostAnalyticExtOrder k (fun y => f y - g y) z
      = almostAnalyticExtOrder k f z - almostAnalyticExtOrder k g z := by
  unfold almostAnalyticExtOrder
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  exact extOrderTerm_sub j (hf j (Finset.mem_range.mp hj)) (hg j (Finset.mem_range.mp hj))

theorem almostAnalyticExtOrderCut_sub (k : ℕ) {f g : ℝ → ℝ} {z : ℂ}
    (hf : ∀ j, j < k → ContDiffAt ℝ j f z.re)
    (hg : ∀ j, j < k → ContDiffAt ℝ j g z.re) :
    almostAnalyticExtOrderCut k (fun y => f y - g y) z
      = almostAnalyticExtOrderCut k f z - almostAnalyticExtOrderCut k g z := by
  unfold almostAnalyticExtOrderCut
  rw [almostAnalyticExtOrder_sub k hf hg]
  ring

end
end GUEStrongConvergence
