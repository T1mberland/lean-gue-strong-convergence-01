import GUEStrongConvergence.Probability.LemmaVSmooth
open Matrix
set_option linter.unusedSectionVars false

namespace GUEStrongConvergence
noncomputable section
variable {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d] [Nonempty d] {N : ℕ}

lemma trace_cfc_sub_one (f : ℝ → ℝ) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (x : EuclideanSpace ℝ (GUECoord ι N)) :
    (guePencilCfc (fun y => f y - 1) A₀ A hA₀ hA x).trace
      = (guePencilCfc f A₀ A hA₀ hA x).trace - (Fintype.card (d × Fin N) : ℂ) := by
  unfold guePencilCfc
  set M := guePencilMatrix A₀ A (WithLp.ofLp x)
  set hM := guePencilMatrix_isHermitian A₀ A hA₀ hA (WithLp.ofLp x)
  rw [trace_cfc_eq_sum_eigenvalues_general M hM (fun y => f y - 1),
      trace_cfc_eq_sum_eigenvalues_general M hM f]
  have hterm : ∀ i, ((f (hM.eigenvalues i) - 1 : ℝ) : ℂ)
      = ((f (hM.eigenvalues i) : ℝ) : ℂ) - 1 := by
    intro i; push_cast; ring
  simp only [hterm, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Nat.smul_one_eq_cast]

lemma gueStatisticCfc_sub_one (f : ℝ → ℝ) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (x : EuclideanSpace ℝ (GUECoord ι N)) (hN : 0 < N) :
    gueStatisticCfc (fun y => f y - 1) A₀ A hA₀ hA x + 1
      = gueStatisticCfc f A₀ A hA₀ hA x := by
  unfold gueStatisticCfc guePencilNormTrace gueNormConst
  rw [trace_cfc_sub_one]
  have hcast : (Fintype.card (d × Fin N) : ℂ) = ((Fintype.card d * N : ℕ) : ℂ) := by
    simp [Fintype.card_prod]
  rw [hcast]
  have hN' : (0:ℝ) < (Fintype.card d * N : ℕ) := by
    have : 0 < Fintype.card d * N := Nat.mul_pos Fintype.card_pos hN
    exact_mod_cast this
  have : ((Fintype.card d * N : ℕ) : ℂ).re = ((Fintype.card d * N : ℕ) : ℝ) := by simp
  rw [Complex.sub_re, this]
  field_simp
  ring

end
end GUEStrongConvergence
