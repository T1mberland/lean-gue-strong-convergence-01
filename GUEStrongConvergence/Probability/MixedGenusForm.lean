/-
# The genus form for mixed (matrix-coefficient) trace words

For a word of even length `2m` in the GUE matrices, the *scalar* mean has the exact genus
expansion `E τ_N(w) = N^{-(m+1)} Σ_p label(p) N^{c(p)}` (`integral_eq_genusSum`), and the face
count `c(p) = pairOrbitCount p` is `m + 1` exactly on non-crossing pairings and at most `m - 1`
otherwise.  This file records what happens when fixed matrix coefficients are inserted between
the generators.

## The length-4 case, computed exactly

With `E[X_ab X_cd] = δ_ad δ_bc / N` (`integral_gueMatrix_mul`), the three Wick pairings of the
four `X`-insertions in `tr(A X B X C X D X)` contract to

* `(12)(34)`: the constraints `b = e`, `d = c`, `f = a`, `h = g` give `tr(AC) tr(B) tr(D)`;
* `(14)(23)`: the constraints `b = a`, `h = c`, `d = g`, `e = f` give `tr(A) tr(C) tr(BD)`;
* `(13)(24)`: the constraints `b = g`, `c = f`, `d = a`, `e = h` give `tr(ADCB)`,

so that

  `E tr(A X B X C X D X)
     = N⁻² ( tr(AC) tr(B) tr(D) + tr(A) tr(C) tr(BD) + tr(ADCB) )`.

The first two pairings are the non-crossing ones (`m + 1 = 3` faces, exponent `N³`, hence `N`
after the `N⁻²`), the last is the crossing one (`c(p) ≤ m - 1 = 1`, hence `O(1/N)`): **the
`pairOrbitCount` exponent is exactly the scalar one, and the label of a pairing is the product of
the traces of the coefficient products around its faces.**  The RHS is
`lengthFourMixedRHS` below; the formula is the target `LengthFourMixedMomentFormula`, whose full
formalization needs the three index-contraction collapses (see `docs/handoffs/STATUS_MOMENTS.md`).

## What is proved here

* `mixedGenusMomentAccuracy`: **once** the exact genus expansion of a mixed word is available
  (as a hypothesis `hgenus`, exactly as in `genus_limit`/`tendsto_of_genus_expansion`), the
  `N⁻²` mean accuracy follows from the abstract lemma `norm_genus_sum_sub_limit_le` with **no
  further input**.  So the analysis side of the pencil mean input is done; the remaining
  obligation is the exact expansion itself.
* `lengthFourMixedRHS_one`: the formula evaluated at `A = B = C = D = 1` gives
  `2N + 1/N`, i.e. `E τ(X⁴) = 2 + 1/N²`, matching the scalar genus expansion (Catalan `2`).

No `sorry`/axiom is used.
-/
import GUEStrongConvergence.Probability.MixedSecondMoment
import GUEStrongConvergence.Probability.GenusSecondOrder

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped Matrix.Norms.Elementwise Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GUEStrongConvergence

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-! ### The analysis step: exact genus expansion ⇒ `N⁻²` mean accuracy -/

/-- **`N⁻²` mean accuracy from the exact genus expansion, for any word (scalar or mixed).**

If the mean `u` of a trace word with `2m` generators has the exact genus expansion
`u M = M^{-(m+1)} ∑_p label(p) M^{c(p)}` where `c = pairOrbitCount` is maximal (`m+1`) on
non-crossing pairings and at most `m-1` on the others, then `u` is within
`(∑_p ‖label(p)‖)/N²` of the non-crossing label sum for every `N ≥ 1`.

This is the pencil-side analogue of `abs_integral_gueNormTrace_sub_wordLimit_le_inv_sq`: the
combinatorial input is isolated in `hgenus`, and no further analysis is needed. -/
theorem mixedGenusMomentAccuracy {P : Type*} [Fintype P]
    (c : P → ℕ) (label : P → ℂ) (NC : P → Prop) [DecidablePred NC] {m : ℕ} (hm : 1 ≤ m)
    (hc_nc : ∀ p, NC p → c p = m + 1)
    (hc_notnc : ∀ p, ¬ NC p → c p ≤ m - 1)
    (u : ℕ → ℂ)
    (hgenus : ∀ M : ℕ, u M = ((M : ℂ) ^ (m + 1))⁻¹ *
      ∑ p : P, label p * (M : ℂ) ^ (c p))
    (N : ℕ) (hN : 1 ≤ N) :
    ‖u N - (∑ p ∈ (Finset.univ : Finset P).filter NC, label p)‖
      ≤ (∑ p : P, ‖label p‖) / (N : ℝ) ^ 2 := by
  rw [hgenus N]
  exact norm_genus_sum_sub_limit_le c label NC hm hc_nc hc_notnc N hN

/-! ### The length-4 formula -/

/-- **The explicit RHS of the length-4 mixed mean**:
`N⁻² (tr(AC) tr(B) tr(D) + tr(A) tr(C) tr(BD) + tr(ADCB))`.  The three summands are the three
Wick pairings of the four `X`-insertions in `tr(A X B X C X D X)`; the first two are the
non-crossing ones (three faces, `O(N)` before the `N⁻²`), the third the crossing one. -/
def lengthFourMixedRHS (A B C D : Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  ((N : ℂ)⁻¹) ^ 2 *
    ((A * C).trace * B.trace * D.trace + A.trace * C.trace * (B * D).trace +
      (A * D * C * B).trace)

/-- **Target: the exact length-4 mixed mean.**  This is the precise statement whose
formalization requires the three index-contraction collapses (the combinatorial content); it is
recorded as a `def` (a proposition) and is *not* asserted here. -/
def LengthFourMixedMomentFormula : Prop :=
  ∀ (A B C D : Matrix (Fin N) (Fin N) ℂ) (i : ι),
    ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        Matrix.trace (A * gueMatrix x i * B * gueMatrix x i * C * gueMatrix x i *
          D * gueMatrix x i)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      = lengthFourMixedRHS A B C D

/-- **Consistency check of the length-4 formula at `A = B = C = D = 1`:** it gives
`2N + 1/N`, i.e. `E τ(X⁴) = 2 + 1/N²`, the scalar genus value (Catalan `2` plus the
`O(N⁻²)` correction).  This pins the normalization of the formula. -/
theorem lengthFourMixedRHS_one (hN : 0 < N) :
    lengthFourMixedRHS (1 : Matrix (Fin N) (Fin N) ℂ) 1 1 1
      = 2 * (N : ℂ) + (N : ℂ)⁻¹ := by
  have hN0 : (N : ℂ) ≠ 0 := by
    have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    exact_mod_cast this.ne'
  have htr : (1 : Matrix (Fin N) (Fin N) ℂ).trace = (N : ℂ) := by
    rw [Matrix.trace_one]
    simp
  simp only [lengthFourMixedRHS, Matrix.mul_one, htr]
  field_simp
  ring

end

end GUEStrongConvergence
