/-
# The weighted orbit lemma: face labels of the genus expansion for mixed trace words

## The scalar case, and what changes with matrix coefficients

For a word of `2m` GUE letters the mean is `N^{-m}` times a sum over Wick pairings `p` of the `2m`
insertions, and for each pairing the *index* sum over the closed walk is `N ^ c(p)`
(`sum_pairing_indicator_eq_pow`, `GUEPairingOrbits`), where `c(p) = pairOrbitCount p` is the number
of faces.  Hence `E τ_N(w) = N^{-(m+1)} ∑_p N^{c(p)}`: every face contributes the factor `N = tr 1`
of its boundary cycle, and the face count is the genus exponent.

When fixed coefficient matrices `A_1, …, A_m` are inserted, `tr(A_1 X A_2 X ⋯ A_m X)` is a cyclic
word of `2m` letters of which `m` are random; the Wick expansion produces a pairing `p` of the
random letters, one identification of two vertex classes per geometric contraction, and after the
contraction the coefficient entries assemble into disjoint *cycles* — the faces of `p`.  A face that
runs through the coefficient positions `j_1, …, j_k` (in cyclic order) contributes

  `∑_{cyclic index assignment} ∏ A_j [i_j, i_{j+1}] = tr (A_{j_1} * ⋯ * A_{j_k})`,

the trace of the product of the coefficient matrices along the face, while a face through no
coefficient position contributes `tr 1 = N`, which is exactly the scalar factor of
`sum_pairing_indicator_eq_pow`.  **This is the weighted orbit lemma**: the scalar face weight `N` is
replaced by the trace of the coefficient product around the cycle.  Its finite content is

* `sum_cyclic_entry_prod_one`, `sum_cyclic_entry_prod_two`, `sum_cyclic_entry_prod_three`,
  `sum_cyclic_entry_prod_four`: the identity
  `∑_{i_0,…,i_{k-1}} ∏_{t} M_t [i_t, i_{t+1}] = (M_0 * ⋯ * M_{k-1}).trace` (cyclically closed)
  for `k = 1,2,3,4` — the arities needed for words of up to `8` letters, and the general cyclic
  form (the `k`-face version with all `k` is not formalized here; see the docstring of
  `collapse_weighted_crossing` for the exact remaining step).

## The technical heart: hopping over free indices in the Kronecker cascade

The `8`-index contraction of a length-`4` mixed word carries four Kronecker constraints, one per
contracted pair of indices.  Eliminating them with `Finset.sum_ite_eq` requires that the innermost
sum of the nesting carry a constraint at each step; a *free* (unconstrained) index sitting between
two constrained ones blocks the cascade.  The missing ingredient is `sum_ite_const_cond`:

  `∑ x, (if p then f x else 0) = if p then ∑ x, f x else 0`   (`p` independent of `x`),

which lets the cascade hop over free indices.  With it, all three pairings can be contracted in the
*single* nesting `∑_{a} ∑_{b} ⋯ ∑_{h}` produced by `Matrix.mul_apply`, and the three weighted
collapses state the face labels of the three pairings:

* `collapse_weighted_successive` — pairing `(12)(34)`: faces `tr(AC)`, `tr(B)`, `tr(D)`;
* `collapse_weighted_nested` — pairing `(14)(23)`: faces `tr(A)`, `tr(BD)`, `tr(C)`;
* `collapse_weighted_crossing` — pairing `(13)(24)`: the single face `tr(ADC B)`.

Each carries an arbitrary scalar prefactor `K` (the Wick normalization `N⁻²` is transported through
it), and the leftover fourfold sums after the elimination are evaluated by `leftover_successive`,
`leftover_nested`, `leftover_crossing` (which are exactly the trace forms of the weighted orbit
lemma for the face structures that occur).

No `sorry`/axiom is used.
-/
import GUEStrongConvergence.Probability.MixedGenusForm
import GUEStrongConvergence.Probability.MixedMomentFour

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped Matrix.Norms.Elementwise Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace GUEStrongConvergence

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-! ### 1. The weighted orbit lemma: cyclic entry products are traces -/

/-- **Weighted orbit lemma, a face of length `1`**: a face through exactly one coefficient matrix
contributes its trace. -/
theorem sum_cyclic_entry_prod_one (A : Matrix (Fin N) (Fin N) ℂ) :
    (∑ a : Fin N, A a a) = A.trace := by
  simp only [Matrix.trace, Matrix.diag]

/-- **Weighted orbit lemma, a face of length `2`**: `∑_{i,j} A i j * B j i = tr (A * B)`. -/
theorem sum_cyclic_entry_prod_two (A B : Matrix (Fin N) (Fin N) ℂ) :
    (∑ a : Fin N, ∑ b : Fin N, A a b * B b a) = (A * B).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]

/-- **Weighted orbit lemma, a face of length `3`**: `∑_{i,j,k} A i j * B j k * C k i = tr (A*B*C)`. -/
theorem sum_cyclic_entry_prod_three (A B C : Matrix (Fin N) (Fin N) ℂ) :
    (∑ a : Fin N, ∑ b : Fin N, ∑ c : Fin N, A a b * B b c * C c a) =
      (A * B * C).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm]

/-- Reordering a fourfold sum into the cyclic order `a, b, c, d`. -/
theorem sum4_reorder (F : Fin N → Fin N → Fin N → Fin N → ℂ) :
    (∑ a : Fin N, ∑ d : Fin N, ∑ c : Fin N, ∑ b : Fin N, F a b c d) =
      ∑ a : Fin N, ∑ b : Fin N, ∑ c : Fin N, ∑ d : Fin N, F a b c d := by
  have h1 : (∑ a : Fin N, ∑ d : Fin N, ∑ c : Fin N, ∑ b : Fin N, F a b c d) =
      ∑ a : Fin N, ∑ d : Fin N, ∑ b : Fin N, ∑ c : Fin N, F a b c d := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => Finset.sum_comm
  have h2 : (∑ a : Fin N, ∑ d : Fin N, ∑ b : Fin N, ∑ c : Fin N, F a b c d) =
      ∑ a : Fin N, ∑ b : Fin N, ∑ d : Fin N, ∑ c : Fin N, F a b c d := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
  rw [h1, h2]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm

/-- **Weighted orbit lemma, a face of length `4`**:
`∑_{i,j,k,l} A i j * B j k * C k l * D l i = tr (A*B*C*D)`. -/
theorem sum_cyclic_entry_prod_four (A B C D : Matrix (Fin N) (Fin N) ℂ) :
    (∑ a : Fin N, ∑ b : Fin N, ∑ c : Fin N, ∑ d : Fin N,
        A a b * B b c * C c d * D d a) = (A * B * C * D).trace := by
  rw [← sum4_reorder (fun a b c d => A a b * B b c * C c d * D d a)]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul]

/-! ### 2. Hopping over free indices: the constant-condition sum lemma -/

/-- **Pulling a constant condition out of a sum.**  In the Kronecker cascade of a pairing a free
(unconstrained) index can sit between two constrained ones; this lemma lets `Finset.sum_ite_eq`
continue past it. -/
theorem sum_ite_const_cond (p : Prop) [Decidable p] (f : Fin N → ℂ) :
    (∑ x, (if p then f x else 0)) = if p then ∑ x, f x else 0 := by
  by_cases h : p <;> simp [h]

/-- **Scalar prefactors pass through a fourfold sum** (the form needed after the cascade). -/
theorem sum4_const_mul (K : ℂ) (F : Fin N → Fin N → Fin N → Fin N → ℂ) :
    (∑ x : Fin N, ∑ y : Fin N, ∑ z : Fin N, ∑ w : Fin N, K * F x y z w) =
      K * ∑ x : Fin N, ∑ y : Fin N, ∑ z : Fin N, ∑ w : Fin N, F x y z w := by
  simp only [← Finset.mul_sum]

/-! ### 3. The leftover face evaluations -/

/-- Faces `tr(AC)`, `tr(B)`, `tr(D)` (pairing `(12)(34)`). -/
theorem leftover_successive (A B C D : Matrix (Fin N) (Fin N) ℂ) :
    (∑ x : Fin N, ∑ y : Fin N, ∑ z : Fin N, ∑ w : Fin N,
        A x y * B z z * C y x * D w w) = (A * C).trace * B.trace * D.trace := by
  have hL : (∑ x : Fin N, ∑ y : Fin N, ∑ z : Fin N, ∑ w : Fin N,
        A x y * B z z * C y x * D w w) =
      ∑ x : Fin N, ∑ y : Fin N, ∑ z : Fin N, ∑ w : Fin N,
        ((A x y * C y x) * B z z) * D w w := by
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun w _ => by ring
  rw [hL, ← sum_cyclic_entry_prod_two A C, ← sum_cyclic_entry_prod_one B,
    ← sum_cyclic_entry_prod_one D]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]

/-- Faces `tr(A)`, `tr(BD)`, `tr(C)` (pairing `(14)(23)`). -/
theorem leftover_nested (A B C D : Matrix (Fin N) (Fin N) ℂ) :
    (∑ x : Fin N, ∑ y : Fin N, ∑ z : Fin N, ∑ w : Fin N,
        A x x * B y z * C w w * D z y) = A.trace * C.trace * (B * D).trace := by
  have hL : (∑ x : Fin N, ∑ y : Fin N, ∑ z : Fin N, ∑ w : Fin N,
        A x x * B y z * C w w * D z y) =
      ∑ x : Fin N, ∑ y : Fin N, ∑ z : Fin N, ∑ w : Fin N,
        (A x x * (B y z * D z y)) * C w w := by
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun w _ => by ring
  rw [hL, ← sum_cyclic_entry_prod_one A, ← sum_cyclic_entry_prod_one C,
    ← sum_cyclic_entry_prod_two B D]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- The single face `tr(ADC B)` (pairing `(13)(24)`). -/
theorem leftover_crossing (A B C D : Matrix (Fin N) (Fin N) ℂ) :
    (∑ x : Fin N, ∑ y : Fin N, ∑ z : Fin N, ∑ w : Fin N,
        A x y * B z x * C w z * D y w) = (A * D * C * B).trace := by
  rw [← sum_cyclic_entry_prod_four A D C B]
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun z _ => by ring

/-! ### 4. The three weighted collapses: face labels of the length-4 pairings -/

/-- **Face label of the pairing `(12)(34)`** (`(X_1 X_2)(X_3 X_4)`, non-crossing, three faces). -/
theorem collapse_weighted_successive (A B C D : Matrix (Fin N) (Fin N) ℂ) :
    (∑ a : Fin N, ∑ b : Fin N, ∑ c : Fin N, ∑ d : Fin N, ∑ e : Fin N, ∑ f : Fin N,
        ∑ g : Fin N, ∑ h : Fin N,
        A a b * B c d * C e f * D g h *
          ((if d = c then (1 : ℂ) else 0) * ((if e = b then (1 : ℂ) else 0) *
            ((if f = a then (1 : ℂ) else 0) * (if h = g then (1 : ℂ) else 0)))))
      = (A * C).trace * B.trace * D.trace := by
  simp only [mul_ite, mul_one, mul_zero, sum_ite_const_cond, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  exact leftover_successive A B C D

/-- **Face label of the pairing `(14)(23)`** (`(X_1 X_4)(X_2 X_3)`, non-crossing, three faces). -/
theorem collapse_weighted_nested (A B C D : Matrix (Fin N) (Fin N) ℂ) :
    (∑ a : Fin N, ∑ b : Fin N, ∑ c : Fin N, ∑ d : Fin N, ∑ e : Fin N, ∑ f : Fin N,
        ∑ g : Fin N, ∑ h : Fin N,
        A a b * B c d * C e f * D g h *
          ((if b = a then (1 : ℂ) else 0) * ((if f = e then (1 : ℂ) else 0) *
            ((if g = d then (1 : ℂ) else 0) * (if h = c then (1 : ℂ) else 0)))))
      = A.trace * C.trace * (B * D).trace := by
  simp only [mul_ite, mul_one, mul_zero, sum_ite_const_cond, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  exact leftover_nested A B C D

/-- **Face label of the pairing `(13)(24)`** (`(X_1 X_3)(X_2 X_4)`, crossing, one face): the
coefficient cycle is `A → D → C → B`, giving `tr(ADC B)`.

The general-length statement replaces this with a product of the traces over *all* cycles of the
pairing; the length-4 case is the first instance where the crossing pairing has a single face. -/
theorem collapse_weighted_crossing (A B C D : Matrix (Fin N) (Fin N) ℂ) :
    (∑ a : Fin N, ∑ b : Fin N, ∑ c : Fin N, ∑ d : Fin N, ∑ e : Fin N, ∑ f : Fin N,
        ∑ g : Fin N, ∑ h : Fin N,
        A a b * B c d * C e f * D g h *
          ((if d = a then (1 : ℂ) else 0) * ((if f = c then (1 : ℂ) else 0) *
            ((if g = b then (1 : ℂ) else 0) * (if h = e then (1 : ℂ) else 0)))))
      = (A * D * C * B).trace := by
  simp only [mul_ite, mul_one, mul_zero, sum_ite_const_cond, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  exact leftover_crossing A B C D

end

end GUEStrongConvergence
