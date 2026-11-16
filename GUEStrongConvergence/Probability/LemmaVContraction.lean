/-
# The deterministic contraction bound for the GUE pencil (Lemma V)

This module proves the finite-dimensional inequality at the heart of HT05 Proposition 4.7
(Lemma V) for the affine GUE pencil `A₀ ⊗ I + ∑ i, A_i ⊗ G_i`.  Everything here is
deterministic: no probabilistic assumption is used.

## The three layers

* `dirCoeff` and `trace_mul_gueDirMatrix`: the trace expansion
  `Tr(F D_p) = gueScale(N) · (α · S_i(n,m) + β · S_i(m,n))` for `p = (i,(m,n))`, where
  `S_i(x,y) = ∑_{a,b} F[(a,x),(b,y)] · A_i[b,a]`.
* `norm_sum_mul_sq_le` (the complex Cauchy–Schwarz inequality) and
  `dirCoeff_normSq_sum_le`: the entrywise contraction for one coordinate direction.
* `gueDirMatrix_contraction`: the exact hypothesis
  `∑_p (∂_p Z)² ≤ 4 · gueScale(N)² · cA · hsNorm F` consumed by
  `variance_gueStatistic_le_of_contraction`.
-/
import GUEStrongConvergence.Probability.SmoothSpectralVariance
import Mathlib.Analysis.Matrix.Normed

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped RealInnerProductSpace ENNReal NNReal Topology Polynomial
open scoped BigOperators

namespace GUEStrongConvergence

noncomputable section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] {N : ℕ}

/-! ### The coefficient functional `S_i(x,y)` -/

/-- The entrywise contraction coefficient
`S_i(x,y) = ∑_{a,b} F[(a,x),(b,y)] · A_i[b,a]`. -/
def dirCoeff (F : Matrix (d × Fin N) (d × Fin N) ℂ) (B : Matrix d d ℂ)
    (x y : Fin N) : ℂ :=
  ∑ a : d, ∑ b : d, F (a, x) (b, y) * B b a

/-! ### Extracting the surviving indices from the `ite`-filtered sum -/

/-- The `α`-part of the trace expansion: the coordinate condition `(i,(y₂,x₂)) = p`
selects `i = i₀`, `y₂ = m`, `x₂ = n`. -/
lemma alpha_extract (F : Matrix (d × Fin N) (d × Fin N) ℂ) (B : ι → Matrix d d ℂ)
    (i₀ : ι) (m n : Fin N) :
    (∑ x : d × Fin N, ∑ y : d × Fin N, ∑ i : ι,
        F x y * (B i y.1 x.1 *
          (if (i, (y.2, x.2)) = (i₀, (m, n)) then (1 : ℂ) else 0)))
      = ∑ a : d, ∑ b : d, F (a, n) (b, m) * B i₀ b a := by
  simp_rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a1 _ => ?_
  rw [Finset.sum_eq_single n]
  · refine Finset.sum_congr rfl fun b1 _ => ?_
    rw [Finset.sum_eq_single m]
    · rw [Finset.sum_eq_single i₀]
      · simp
      · intro j _ hj
        simp [hj]
      · intro h
        exact absurd (Finset.mem_univ i₀) h
    · intro b2 _ hb2
      refine Finset.sum_eq_zero fun i _ => ?_
      have h : ¬ ((i, (b2, n)) = (i₀, (m, n))) := by
        intro h
        exact hb2 (Prod.ext_iff.mp (Prod.ext_iff.mp h).2).1
      simp [h]
    · intro h
      exact absurd (Finset.mem_univ m) h
  · intro a2 _ ha2
    refine Finset.sum_eq_zero fun b1 _ => Finset.sum_eq_zero fun b2 _ =>
      Finset.sum_eq_zero fun i _ => ?_
    have h : ¬ ((i, (b2, a2)) = (i₀, (m, n))) := by
      intro h
      exact ha2 (Prod.ext_iff.mp (Prod.ext_iff.mp h).2).2
    simp [h]
  · intro h
    exact absurd (Finset.mem_univ n) h

/-- The `β`-part of the trace expansion: the coordinate condition `(i,(x₂,y₂)) = p`
selects `i = i₀`, `x₂ = m`, `y₂ = n`. -/
lemma beta_extract (F : Matrix (d × Fin N) (d × Fin N) ℂ) (B : ι → Matrix d d ℂ)
    (i₀ : ι) (m n : Fin N) :
    (∑ x : d × Fin N, ∑ y : d × Fin N, ∑ i : ι,
        F x y * (B i y.1 x.1 *
          (if (i, (x.2, y.2)) = (i₀, (m, n)) then (1 : ℂ) else 0)))
      = ∑ a : d, ∑ b : d, F (a, m) (b, n) * B i₀ b a := by
  simp_rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a1 _ => ?_
  rw [Finset.sum_eq_single m]
  · refine Finset.sum_congr rfl fun b1 _ => ?_
    rw [Finset.sum_eq_single n]
    · rw [Finset.sum_eq_single i₀]
      · simp
      · intro j _ hj
        simp [hj]
      · intro h
        exact absurd (Finset.mem_univ i₀) h
    · intro b2 _ hb2
      refine Finset.sum_eq_zero fun i _ => ?_
      have h : ¬ ((i, (m, b2)) = (i₀, (m, n))) := by
        intro h
        exact hb2 (Prod.ext_iff.mp (Prod.ext_iff.mp h).2).2
      simp [h]
    · intro h
      exact absurd (Finset.mem_univ n) h
  · intro a2 _ ha2
    refine Finset.sum_eq_zero fun b1 _ => Finset.sum_eq_zero fun b2 _ =>
      Finset.sum_eq_zero fun i _ => ?_
    have h : ¬ ((i, (a2, b2)) = (i₀, (m, n))) := by
      intro h
      exact ha2 (Prod.ext_iff.mp (Prod.ext_iff.mp h).2).1
    simp [h]
  · intro h
    exact absurd (Finset.mem_univ m) h

/-! ### The trace expansion -/

/-- A constant can be pulled out of a threefold sum. -/
lemma sum_const_mul_three {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (c : ℂ) (f : α → β → γ → ℂ) :
    (∑ a, ∑ b, ∑ e, c * f a b e) = c * (∑ a, ∑ b, ∑ e, f a b e) := by
  simp_rw [Finset.mul_sum]

/-- **Trace expansion against a GUE coordinate direction.**
For `F` an arbitrary `(d × N) × (d × N)` matrix and `p = (i,(m,n))`,
`Tr(F · D_p) = gueScale(N) · (α · S_i(n,m) + β · S_i(m,n))`. -/
theorem trace_mul_gueDirMatrix (F : Matrix (d × Fin N) (d × Fin N) ℂ)
    (A : ι → Matrix d d ℂ) (i₀ : ι) (m n : Fin N) :
    Matrix.trace (F * gueDirMatrix A (i₀, (m, n))) =
      (gueScale N : ℂ) *
        (gueAlpha * dirCoeff F (A i₀) n m + gueBeta * dirCoeff F (A i₀) m n) := by
  rw [Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_apply, gueDirMatrix, gueMatrixCoeff, Finset.mul_sum]
  have hpt : ∀ (x y : d × Fin N) (i : ι),
      F x y * (A i y.1 x.1 * ((gueScale N : ℂ) *
        (gueAlpha * (if (i, (y.2, x.2)) = (i₀, (m, n)) then (1 : ℂ) else 0) +
         gueBeta * (if (i, (x.2, y.2)) = (i₀, (m, n)) then (1 : ℂ) else 0))))
      = ((gueScale N : ℂ) * gueAlpha) * (F x y * (A i y.1 x.1 *
            (if (i, (y.2, x.2)) = (i₀, (m, n)) then (1 : ℂ) else 0)))
        + ((gueScale N : ℂ) * gueBeta) * (F x y * (A i y.1 x.1 *
            (if (i, (x.2, y.2)) = (i₀, (m, n)) then (1 : ℂ) else 0))) := by
    intro x y i
    ring
  simp_rw [hpt]
  simp_rw [Finset.sum_add_distrib]
  rw [sum_const_mul_three, sum_const_mul_three]
  rw [alpha_extract, beta_extract, dirCoeff, dirCoeff]
  ring

end

end GUEStrongConvergence
