/-
# Algebraic identities for the GUE pencil resolvent

Two identities underlie the Lipschitz concentration of resolvent pairings:

* the pencil is affine in the coordinates, with derivative matrices
  `guePencilDirection`;
* the resolvent obeys the second resolvent identity.
-/
import GUEStrongConvergence.Probability.GUEPencil

open MeasureTheory Matrix Kronecker
open scoped Matrix.Norms.Elementwise ComplexOrder

namespace GUEStrongConvergence

noncomputable section

variable {ι d : Type*} {N : ℕ} [Fintype ι] [Fintype d] [DecidableEq d] [DecidableEq ι]

/-- Entry formula for the coordinate derivative of the pencil. -/
theorem guePencilDirection_apply (A : ι → Matrix d d ℂ) (p : GUECoord ι N)
    (a b : d × Fin N) :
    guePencilDirection A p a b =
      A p.1 a.1 b.1 * (gueScale N : ℂ) *
        (gueAlpha * (if p.2 = (a.2, b.2) then 1 else 0) +
          gueBeta * (if p.2 = (b.2, a.2) then 1 else 0)) := by
  change (∑ i, A i a.1 b.1 *
      ((gueScale N : ℂ) * (gueAlpha * (if p = (i, a.2, b.2) then (1:ℂ) else 0) +
        gueBeta * (if p = (i, b.2, a.2) then (1:ℂ) else 0)))) = _
  rw [Finset.sum_eq_single p.1]
  · have h1 : (p = (p.1, (a.2, b.2))) ↔ (p.2 = (a.2, b.2)) := by
      constructor
      · intro h; exact congrArg Prod.snd h
      · intro h; ext <;> simp [h]
    have h2 : (p = (p.1, (b.2, a.2))) ↔ (p.2 = (b.2, a.2)) := by
      constructor
      · intro h; exact congrArg Prod.snd h
      · intro h; ext <;> simp [h]
    rw [if_congr h1 rfl rfl, if_congr h2 rfl rfl]
    ring
  · intro i _ hi
    have h1 : p ≠ (i, a.2, b.2) := by
      intro h; exact hi (congrArg Prod.fst h).symm
    have h2 : p ≠ (i, b.2, a.2) := by
      intro h; exact hi (congrArg Prod.fst h).symm
    simp [h1, h2]
  · intro h; simp at h

/-- Real scalar multiplication of a `CStarMatrix` evaluated entrywise. -/
theorem real_smul_cstar_apply {m n : Type*} (r : ℝ) (M : CStarMatrix m n ℂ) (a : m) (b : n) :
    (r • M) a b = (r : ℂ) * M a b := by
  rw [CStarMatrix.smul_apply, RCLike.real_smul_eq_coe_mul]
  rfl

/-- Pointwise evaluation of a finite sum of `CStarMatrix`s. -/
theorem cstar_sum_apply {α m n : Type*} (s : Finset α)
    (f : α → CStarMatrix m n ℂ) (a : m) (b : n) :
    (∑ x ∈ s, f x) a b = ∑ x ∈ s, f x a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx, CStarMatrix.add_apply, ih]

/-- The affine pencil is an affine function of the Gaussian coordinates: its
increment is the sum of the coordinate increments times the direction matrices. -/
theorem guePencil_sub_eq_sum_smul (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (x y : GUECoord ι N → ℝ) :
    guePencil A₀ A x - guePencil A₀ A y =
      ∑ p : GUECoord ι N, (x p - y p) • guePencilDirection A p := by
  have hRHS : ∀ a b : d × Fin N,
      (∑ p : GUECoord ι N, (x p - y p) • guePencilDirection A p) a b
        = ∑ i, ∑ q : Fin N × Fin N,
            ((x (i, q) : ℂ) - (y (i, q) : ℂ)) *
              (A i a.1 b.1 * (gueScale N : ℂ) *
                (gueAlpha * (if q = (a.2, b.2) then 1 else 0) +
                 gueBeta * (if q = (b.2, a.2) then 1 else 0))) := by
    intro a b
    rw [cstar_sum_apply]
    have hstep : ∀ p : GUECoord ι N, ((x p - y p) • guePencilDirection A p) a b
        = (x p - y p) * guePencilDirection A p a b := by
      intro p
      rw [real_smul_cstar_apply]
      congr 1
      exact Complex.ofReal_sub _ _
    simp only [hstep]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro q _
    rw [guePencilDirection_apply]
    try ring
  have hinner : ∀ (a b : d × Fin N) (i : ι),
      (∑ q : Fin N × Fin N,
            ((x (i, q) : ℂ) - (y (i, q) : ℂ)) *
              (A i a.1 b.1 * (gueScale N : ℂ) *
                (gueAlpha * (if q = (a.2, b.2) then 1 else 0) +
                 gueBeta * (if q = (b.2, a.2) then 1 else 0))))
        = A i a.1 b.1 * (gueScale N : ℂ) *
            (gueAlpha * ((x (i, (a.2, b.2)) : ℂ) - (y (i, (a.2, b.2)) : ℂ)) +
             gueBeta * ((x (i, (b.2, a.2)) : ℂ) - (y (i, (b.2, a.2)) : ℂ))) := by
    intro a b i
    have hα : (∑ q : Fin N × Fin N,
          ((x (i, q) : ℂ) - (y (i, q) : ℂ)) *
            ((A i a.1 b.1 * (gueScale N : ℂ)) *
              (gueAlpha * (if q = (a.2, b.2) then (1:ℂ) else 0))))
        = (A i a.1 b.1 * (gueScale N : ℂ)) * gueAlpha *
            ((x (i, (a.2, b.2)) : ℂ) - (y (i, (a.2, b.2)) : ℂ)) := by
      rw [Finset.sum_eq_single (a.2, b.2)]
      · simp only [ite_true]
        ring
      · intro q _ hq; simp [hq]
      · intro h; simp at h
    have hβ : (∑ q : Fin N × Fin N,
          ((x (i, q) : ℂ) - (y (i, q) : ℂ)) *
            ((A i a.1 b.1 * (gueScale N : ℂ)) *
              (gueBeta * (if q = (b.2, a.2) then (1:ℂ) else 0))))
        = (A i a.1 b.1 * (gueScale N : ℂ)) * gueBeta *
            ((x (i, (b.2, a.2)) : ℂ) - (y (i, (b.2, a.2)) : ℂ)) := by
      rw [Finset.sum_eq_single (b.2, a.2)]
      · simp only [ite_true]
        ring
      · intro q _ hq; simp [hq]
      · intro h; simp at h
    have hsplit : (∑ q : Fin N × Fin N,
          ((x (i, q) : ℂ) - (y (i, q) : ℂ)) *
            ((A i a.1 b.1 * (gueScale N : ℂ)) *
              (gueAlpha * (if q = (a.2, b.2) then (1:ℂ) else 0) +
               gueBeta * (if q = (b.2, a.2) then (1:ℂ) else 0))))
        = (∑ q : Fin N × Fin N, ((x (i, q) : ℂ) - (y (i, q) : ℂ)) *
              ((A i a.1 b.1 * (gueScale N : ℂ)) *
                (gueAlpha * (if q = (a.2, b.2) then (1:ℂ) else 0)))) +
          (∑ q : Fin N × Fin N, ((x (i, q) : ℂ) - (y (i, q) : ℂ)) *
              ((A i a.1 b.1 * (gueScale N : ℂ)) *
                (gueBeta * (if q = (b.2, a.2) then (1:ℂ) else 0)))) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro q _
      ring
    rw [hsplit, hα, hβ]
    ring

  ext a b
  change guePencilMatrix A₀ A x a b - guePencilMatrix A₀ A y a b =
    (∑ p : GUECoord ι N, (x p - y p) • guePencilDirection A p) a b
  rw [hRHS a b]
  rw [guePencilMatrix_apply, guePencilMatrix_apply]
  simp only [Matrix.one_apply, gueMatrix, gueUnscaled]
  rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [hinner a b i]
  ring

/-- Second resolvent identity for the finite pencil. -/
theorem guePencilResolvent_sub (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (x y : GUECoord ι N → ℝ) (z : ℂ) (hz : z.im ≠ 0) :
    guePencilResolvent A₀ A x z - guePencilResolvent A₀ A y z =
      guePencilResolvent A₀ A x z * (guePencil A₀ A x - guePencil A₀ A y) *
        guePencilResolvent A₀ A y z := by
  have hx : IsUnit (algebraMap ℂ (CStarMatrix (d × Fin N) (d × Fin N) ℂ) z - guePencil A₀ A x) :=
    guePencil_mem_resolventSet A₀ A hA₀ hA x z hz
  have hy : IsUnit (algebraMap ℂ (CStarMatrix (d × Fin N) (d × Fin N) ℂ) z - guePencil A₀ A y) :=
    guePencil_mem_resolventSet A₀ A hA₀ hA y z hz
  simp only [guePencilResolvent, resolvent]
  rw [Ring.inverse_sub_inverse (show IsUnit (algebraMap ℂ (CStarMatrix (d × Fin N) (d × Fin N) ℂ) z - guePencil A₀ A x) ↔
      IsUnit (algebraMap ℂ (CStarMatrix (d × Fin N) (d × Fin N) ℂ) z - guePencil A₀ A y) from
      ⟨fun _ => hy, fun _ => hx⟩)]
  congr 2
  abel

end

end GUEStrongConvergence
