import GUEStrongConvergence.StrongConvergence.FlatSideConditions
import GUEStrongConvergence.StrongConvergence.CutoffCancellation
import GUEStrongConvergence.Probability.FlatContraction
open Matrix MeasureTheory ProbabilityTheory
set_option linter.unusedSectionVars false
namespace GUEStrongConvergence
noncomputable section
variable {r : ℕ}

lemma flatStat_sub_one (k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ) (N : ℕ) (f : ℝ → ℝ)
    (x : CommonSpace (Fin r)) :
    flatStat r k F z N (fun y => f y - 1) x + 1 = flatStat r k F z N f x := by
  unfold flatStat normTrace
  rw [hermCfc_eq, hermCfc_eq]
  set M := h1PencilApproxFlat r k F x N z
  set hM := h1PencilApproxFlat_isHermitian r k F x N z
  have htr : (hM.cfc (fun y => f y - 1)).trace
      = (hM.cfc f).trace - (Fintype.card (Fin (pencilFlatDim r k F N)) : ℂ) := by
    rw [trace_cfc_eq_sum_eigenvalues_general M hM (fun y => f y - 1),
        trace_cfc_eq_sum_eigenvalues_general M hM f]
    have hterm : ∀ i, ((f (hM.eigenvalues i) - 1 : ℝ) : ℂ)
        = ((f (hM.eigenvalues i) : ℝ) : ℂ) - 1 := by
      intro i; push_cast; ring
    simp only [hterm, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Nat.smul_one_eq_cast]
  rw [htr, Complex.sub_re]
  have hm : (0:ℝ) < (pencilFlatDim r k F N : ℝ) := pencilFlatDim_pos_real k F N
  have hcast : ((Fintype.card (Fin (pencilFlatDim r k F N)) : ℕ) : ℂ)
      = ((pencilFlatDim r k F N : ℕ) : ℂ) := by simp
  rw [hcast]
  have hre : (((pencilFlatDim r k F N : ℕ) : ℂ)).re = ((pencilFlatDim r k F N : ℕ) : ℝ) :=
    Complex.natCast_re _
  rw [hre]
  have hmne : ((pencilFlatDim r k F N : ℕ) : ℝ) ≠ 0 := ne_of_gt hm
  field_simp
  ring

end
end GUEStrongConvergence
