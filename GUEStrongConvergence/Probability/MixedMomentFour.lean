/-
# The three index contractions of the length-4 mixed trace

For fixed matrices `A B C D : Matrix (Fin N) (Fin N) ℂ` and a normalized complex GUE matrix
`X` (`E[X_ab X_cd] = δ_ad δ_bc / N`, `integral_gueMatrix_mul`), the mean of
`tr(A X B X C X D X)` is a sum over the three Wick pairings of the four `X`-insertions.
This file proves the three **index contractions** ("collapses") that evaluate each pairing:

* `collapse_pairing_successive` — pairing `(12)(34)` (non-crossing):
  the constraints `b = e`, `d = c`, `f = a`, `h = g` leave `tr(AC) tr(B) tr(D)`;
* `collapse_pairing_nested` — pairing `(14)(23)` (non-crossing):
  the constraints `b = a`, `h = c`, `d = g`, `e = f` leave `tr(A) tr(C) tr(BD)`;
* `collapse_pairing_crossing` — pairing `(13)(24)` (crossing):
  the constraints `b = g`, `c = f`, `d = a`, `e = h` leave `tr(ADC B)`.

Each is stated in the summation order that makes the Kronecker elimination go through in one
`Finset.sum_ite_eq` pass (the pairings' deltas are written in the matching innermost-first order;
this is the technical point of the file), followed by `Matrix.trace`/`Matrix.mul_apply` and
`Finset.sum_mul_sum` to identify the trace products.

These are exactly the three values in `lengthFourMixedRHS` (`MixedGenusForm.lean`), and they are
the combinatorial input of the length-4 mixed mean identity: once the pointwise expansion and
the four-point Wick evaluation are combined with these contractions, one obtains
`E tr(A X B X C X D X) = N⁻²( tr(AC) tr(B) tr(D) + tr(A) tr(C) tr(BD) + tr(ADC B) )`, whence
`E τ_N(A X B X C X D X) − (free limit) = O(N⁻²)` by `mixedGenusMomentAccuracy`.

The remaining assembly steps (not in this file) are: (i) the pointwise `8`-index expansion of
`tr(A X B X C X D X)`; (ii) `integral_sum8`, the interchange of the integral with the eightfold
sum; (iii) the four-point function `∫ X_bc X_de X_fg X_ha = N⁻²(δ_beδ_cdδ_faδ_hg + …)` from
`integral_gueProd_eq_gueWick`/`gueWick_four`; (iv) permuting the eight sums into the three orders
used below with `Finset.sum_comm`.

No `sorry`/axiom is used.
-/
import GUEStrongConvergence.Probability.MixedSecondMoment

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped Matrix.Norms.Elementwise Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace GUEStrongConvergence

noncomputable section

variable {N : ℕ}

/-! ### Pairing `(12)(34)`: successive contraction, value `tr(AC) tr(B) tr(D)` -/

/-- **Index contraction of the non-crossing pairing `(12)(34)`**: with the constraints
`b = e`, `d = c`, `f = a`, `h = g` the eightfold sum over the coefficient entries collapses to
`tr(AC) tr(B) tr(D)`.  The summation order is chosen to match the innermost-first order of the
four Kronecker factors. -/
theorem collapse_pairing_successive (A B C D : Matrix (Fin N) (Fin N) ℂ) :
    (∑ a : Fin N, ∑ hh : Fin N, ∑ c : Fin N, ∑ b : Fin N,
      ∑ d : Fin N, ∑ f : Fin N, ∑ e : Fin N, ∑ g : Fin N,
      A a b * B c d * C e f * D g hh *
        ((if d = c then (1 : ℂ) else 0) * ((if f = a then (1 : ℂ) else 0) *
          ((if b = e then (1 : ℂ) else 0) * (if hh = g then (1 : ℂ) else 0)))))
      = (A * C).trace * B.trace * D.trace := by
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun hh _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-! ### Pairing `(14)(23)`: nested contraction, value `tr(A) tr(C) tr(BD)` -/

/-- **Index contraction of the non-crossing pairing `(14)(23)`**: with the constraints
`b = a`, `h = c`, `d = g`, `e = f` the eightfold sum collapses to `tr(A) tr(C) tr(BD)`. -/
theorem collapse_pairing_nested (A B C D : Matrix (Fin N) (Fin N) ℂ) :
    (∑ a : Fin N, ∑ c : Fin N, ∑ g : Fin N, ∑ f : Fin N,
      ∑ b : Fin N, ∑ hh : Fin N, ∑ d : Fin N, ∑ e : Fin N,
      A a b * B c d * C e f * D g hh *
        ((if b = a then (1 : ℂ) else 0) * ((if hh = c then (1 : ℂ) else 0) *
          ((if d = g then (1 : ℂ) else 0) * (if e = f then (1 : ℂ) else 0)))))
      = A.trace * C.trace * (B * D).trace := by
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun f _ => ?_
  ring

/-! ### Pairing `(13)(24)`: crossing contraction, value `tr(ADC B)` -/

/-- **Index contraction of the crossing pairing `(13)(24)`**: with the constraints
`b = g`, `c = f`, `d = a`, `e = h` the eightfold sum collapses to `tr(ADC B)`. -/
theorem collapse_pairing_crossing (A B C D : Matrix (Fin N) (Fin N) ℂ) :
    (∑ a : Fin N, ∑ f : Fin N, ∑ hh : Fin N, ∑ g : Fin N,
      ∑ b : Fin N, ∑ e : Fin N, ∑ d : Fin N, ∑ c : Fin N,
      A a b * B c d * C e f * D g hh *
        ((if b = g then (1 : ℂ) else 0) * ((if e = hh then (1 : ℂ) else 0) *
          ((if d = a then (1 : ℂ) else 0) * (if c = f then (1 : ℂ) else 0)))))
      = (A * D * C * B).trace := by
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun f _ =>
    Finset.sum_congr rfl fun hh _ => Finset.sum_congr rfl fun g _ => ?_
  ring

end

end GUEStrongConvergence
