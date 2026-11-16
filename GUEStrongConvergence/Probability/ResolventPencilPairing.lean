/-
# Sparse pairing against a coordinate direction

For `p = (i,(a,b))`, the pairing `∑_{k,l} W k (D_p)_{k l} Z l` against the
coordinate direction matrix only sees the two slices `a` and `b`, with the
coefficient matrix `A i` acting between them.  This is the algebraic input for
the sharp `1/N` variance proxy of GUE resolvent pairings.
-/
import GUEStrongConvergence.Probability.ResolventPencilAlgebra

open MeasureTheory Matrix Kronecker
open scoped Matrix.Norms.Elementwise ComplexOrder

namespace GUEStrongConvergence

noncomputable section

variable {ι d : Type*} {N : ℕ} [Fintype ι] [Fintype d] [DecidableEq d] [DecidableEq ι]

/-- Pairing against a coordinate direction splits into the two slices. -/
theorem direction_pairing_eq (A : ι → Matrix d d ℂ) (W Z : d × Fin N → ℂ)
    (p : GUECoord ι N) :
    (∑ k : d × Fin N, ∑ l : d × Fin N, W k * guePencilDirection A p k l * Z l)
      = (∑ x : d, ∑ x_2 : d,
          (gueScale N : ℂ) * gueAlpha *
            (W (x, p.2.1) * A p.1 x x_2 * Z (x_2, p.2.2)))
        + (∑ x : d, ∑ x_2 : d,
          (gueScale N : ℂ) * gueBeta *
            (W (x, p.2.2) * A p.1 x x_2 * Z (x_2, p.2.1))) := by
  obtain ⟨i, q⟩ := p
  obtain ⟨a, b⟩ := q
  simp only [Fintype.sum_prod_type]
  simp only [guePencilDirection_apply]
  have hα : (∑ x : d, ∑ x_1 : Fin N, ∑ x_2 : d, ∑ x_3 : Fin N,
      (if (a, b) = (x_1, x_3) then
        W (x, x_1) * (A i x x_2 * (gueScale N : ℂ) * (gueAlpha * 1)) else 0) * Z (x_2, x_3))
      = ∑ x : d, ∑ x_2 : d,
        (gueScale N : ℂ) * gueAlpha * (W (x, a) * A i x x_2 * Z (x_2, b)) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [show (∑ x_1 : Fin N, ∑ x_2 : d, ∑ x_3 : Fin N,
        (if (a, b) = (x_1, x_3) then
          W (x, x_1) * (A i x x_2 * (gueScale N : ℂ) * (gueAlpha * 1)) else 0) * Z (x_2, x_3))
        = ∑ x_1 : Fin N, ∑ x_3 : Fin N, ∑ x_2 : d,
        (if (a, b) = (x_1, x_3) then
          W (x, x_1) * (A i x x_2 * (gueScale N : ℂ) * (gueAlpha * 1)) else 0) * Z (x_2, x_3) from by
      apply Finset.sum_congr rfl
      intro x_1 _
      exact Finset.sum_comm]
    rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single b]
      · simp only [ite_true]
        apply Finset.sum_congr rfl
        intro x_2 _
        ring
      · intro x_3 _ hx3
        have hb : ¬ (b = x_3) := fun h => hx3 h.symm
        simp [hb]
      · intro h; simp at h
    · intro x_1 _ hx1
      apply Finset.sum_eq_zero
      intro x_3 _
      have h : (a, b) ≠ (x_1, x_3) := by
        intro h; exact hx1 (congrArg Prod.fst h).symm
      simp [h]
    · intro h; simp at h
  have hβ : (∑ x : d, ∑ x_1 : Fin N, ∑ x_2 : d, ∑ x_3 : Fin N,
      (if (a, b) = (x_3, x_1) then
        W (x, x_1) * (A i x x_2 * (gueScale N : ℂ) * (gueBeta * 1)) else 0) * Z (x_2, x_3))
      = ∑ x : d, ∑ x_2 : d,
        (gueScale N : ℂ) * gueBeta * (W (x, b) * A i x x_2 * Z (x_2, a)) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [show (∑ x_1 : Fin N, ∑ x_2 : d, ∑ x_3 : Fin N,
        (if (a, b) = (x_3, x_1) then
          W (x, x_1) * (A i x x_2 * (gueScale N : ℂ) * (gueBeta * 1)) else 0) * Z (x_2, x_3))
        = ∑ x_1 : Fin N, ∑ x_3 : Fin N, ∑ x_2 : d,
        (if (a, b) = (x_3, x_1) then
          W (x, x_1) * (A i x x_2 * (gueScale N : ℂ) * (gueBeta * 1)) else 0) * Z (x_2, x_3) from by
      apply Finset.sum_congr rfl
      intro x_1 _
      exact Finset.sum_comm]
    rw [Finset.sum_eq_single b]
    · rw [Finset.sum_eq_single a]
      · simp only [ite_true]
        apply Finset.sum_congr rfl
        intro x_2 _
        ring
      · intro x_3 _ hx3
        have ha : ¬ (a = x_3) := fun h => hx3 h.symm
        simp [ha]
      · intro h; simp at h
    · intro x_1 _ hx1
      apply Finset.sum_eq_zero
      intro x_3 _
      have h : (a, b) ≠ (x_3, x_1) := by
        intro h; exact hx1 (congrArg Prod.snd h).symm
      simp [h]
    · intro h; simp at h
  have hterm : ∀ x x_1 x_2 x_3,
      W (x, x_1) * (A i x x_2 * (gueScale N : ℂ) *
        ((gueAlpha * if (a, b) = (x_1, x_3) then 1 else 0) +
         (gueBeta * if (a, b) = (x_3, x_1) then 1 else 0))) * Z (x_2, x_3)
      = (if (a, b) = (x_1, x_3) then
            W (x, x_1) * (A i x x_2 * (gueScale N : ℂ) * (gueAlpha * 1)) else 0) * Z (x_2, x_3) +
        (if (a, b) = (x_3, x_1) then
            W (x, x_1) * (A i x x_2 * (gueScale N : ℂ) * (gueBeta * 1)) else 0) * Z (x_2, x_3) := by
    intro x x_1 x_2 x_3
    by_cases h1 : (a, b) = (x_1, x_3)
    · have hx1 : x_1 = a := (congrArg Prod.fst h1).symm
      have hx3 : x_3 = b := (congrArg Prod.snd h1).symm
      rw [hx1, hx3]
      by_cases h2 : (a, b) = (b, a)
      · rw [if_pos rfl, if_pos rfl, if_pos h2, if_pos h2]
        ring
      · rw [if_pos rfl, if_pos rfl, if_neg h2, if_neg h2]
        ring
    · by_cases h2 : (a, b) = (x_3, x_1)
      · have hx3 : x_3 = a := (congrArg Prod.fst h2).symm
        have hx1 : x_1 = b := (congrArg Prod.snd h2).symm
        rw [hx3, hx1]
        by_cases h12 : (a, b) = (b, a)
        · rw [if_pos h12, if_pos h12, if_pos rfl, if_pos rfl]
          ring
        · rw [if_neg h12, if_neg h12, if_pos rfl, if_pos rfl]
          ring
      · rw [if_neg h1, if_neg h1, if_neg h2, if_neg h2]
        ring
  rw [show (∑ x : d, ∑ x_1 : Fin N, ∑ x_2 : d, ∑ x_3 : Fin N,
      W (x, x_1) * (A i x x_2 * (gueScale N : ℂ) *
        ((gueAlpha * if (a, b) = (x_1, x_3) then 1 else 0) +
         (gueBeta * if (a, b) = (x_3, x_1) then 1 else 0))) * Z (x_2, x_3))
      = ∑ x : d, ∑ x_1 : Fin N, ∑ x_2 : d, ∑ x_3 : Fin N,
        ((if (a, b) = (x_1, x_3) then
            W (x, x_1) * (A i x x_2 * (gueScale N : ℂ) * (gueAlpha * 1)) else 0) * Z (x_2, x_3) +
         (if (a, b) = (x_3, x_1) then
            W (x, x_1) * (A i x x_2 * (gueScale N : ℂ) * (gueBeta * 1)) else 0) * Z (x_2, x_3)) from by
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro x_1 _
    apply Finset.sum_congr rfl
    intro x_2 _
    apply Finset.sum_congr rfl
    intro x_3 _
    exact hterm x x_1 x_2 x_3]
  simp only [Finset.sum_add_distrib]
  rw [hα, hβ]
  repeat rw [Finset.sum_add_distrib]

end

end GUEStrongConvergence
