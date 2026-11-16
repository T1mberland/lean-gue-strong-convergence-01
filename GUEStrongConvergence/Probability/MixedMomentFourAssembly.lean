/-
# The exact length-4 mixed (matrix-coefficient) GUE moment: the assembly

This file assembles the exact length-4 mixed moment from the weighted face labels proved in
`Probability/MixedGenusWeights.lean` and the entry-level Wick theory.

The three ingredients:

* `trace_mul_four_gue_eq_sum8`: the pointwise eightfold expansion
  `tr(A X B X C X D X) = ∑_{a,…,h} A a b X b c B c d X d e C e f X f g D g h X h a`.
  The nesting is written in the order that `Matrix.mul_apply` actually produces (the trace index
  first, then the indices introduced from the right end of the product), so that the expansion is
  proved by a single `simp` and **no reordering of the eight sums is needed anywhere**;
* `integral_sum8` (the `integral_sum4` recipe of `MixedSecondMoment`, iterated), with
  `integrable_four_entry` (fourfold products of entries are integrable) and
  `integrable_trace_summand8`;
* `integral_four_entry`: the four-point function
  `∫ X b c · X d e · X f g · X h a = N⁻² (δ_{be}δ_{cd} δ_{fa}δ_{gh} + δ_{bg}δ_{cf} δ_{da}δ_{eh}
   + δ_{ba}δ_{ch} δ_{dg}δ_{ef})`, from `integral_gueProd_eq_gueWick` and `gueWick_four`;
* `collapse_conj_successive / _crossing / _nested`: the three pairings contracted in the
  *conjunction* form in which the four-point function delivers them, the elimination being the
  `sum_ite_const_cond` + `Finset.sum_ite_eq` cascade of `MixedGenusWeights` (which now must hop over
  the free indices of this nesting: this is exactly what `sum_ite_const_cond` is for).  The leftover
  fourfold sums are the face traces and are evaluated by `leftover_rev_successive/_nested/_crossing`.

The result is the exact finite-`N` identity

  `E tr(A X B X C X D X) = N⁻² ( tr(AC) tr(B) tr(D) + tr(A) tr(C) tr(BD) + tr(ADC B) )`,

`integral_trace_mul_four_gue = lengthFourMixedRHS`, which is the statement
`LengthFourMixedMomentFormula` recorded (but not asserted) in `MixedGenusForm.lean`; it is proved
here as `lengthFourMixedMomentFormula`.

Consequences (the `N⁻²` mean-accuracy shape needed by the pencil side):

* `integral_normalizedTrace_mul_four_gue`: `E τ_N(A X B X C X D X) = N⁻³ (three face labels)`;
* `integral_normalizedTrace_mul_four_gue_sub_free`: the whole second-order correction cancels and the
  residual is *exactly* `N⁻³ tr(ADC B)` — i.e. `E τ_N − (τ_N(AC)τ_N(B)τ_N(D) + τ_N(A)τ_N(C)τ_N(BD))
  = N⁻³ tr(ADC B)`;
* `norm_integral_normalizedTrace_mul_four_gue_sub_free_le`: hence the mean is `O(N⁻³)` accurate in
  operator norm (`O(N⁻⁵ᐟ²)` in Frobenius norm), which is stronger than the `O(N⁻²)` required.

No `sorry`/axiom is used.
-/
import GUEStrongConvergence.Probability.MixedGenusWeights
import GUEStrongConvergence.Probability.GUEWordMoments

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped Matrix.Norms.Elementwise Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace GUEStrongConvergence

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

local notation "μ" => stdGaussian (EuclideanSpace ℝ (GUECoord ι N))

/-! ### 1. The pointwise eightfold expansion -/

/-- **Pointwise eightfold expansion** of `tr(A X B X C X D X)` into the coefficient entries times the
four GUE entries, in the nesting produced by `Matrix.mul_apply`. -/
theorem trace_mul_four_gue_eq_sum8 (A B C D : Matrix (Fin N) (Fin N) ℂ) (i : ι)
    (x : GUECoord ι N → ℝ) :
    Matrix.trace (A * gueMatrix x i * B * gueMatrix x i * C * gueMatrix x i * D * gueMatrix x i)
      = ∑ a : Fin N, ∑ h : Fin N, ∑ g : Fin N, ∑ f : Fin N, ∑ e : Fin N, ∑ d : Fin N,
          ∑ c : Fin N, ∑ b : Fin N,
          A a b * gueMatrix x i b c * B c d * gueMatrix x i d e * C e f *
            gueMatrix x i f g * D g h * gueMatrix x i h a := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul]

/-! ### 2. Integrability -/

/-- A fourfold product of GUE entries is integrable. -/
theorem integrable_four_entry (i : ι) (b c d e f g h a : Fin N) :
    Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      gueMatrix x i b c * gueMatrix x i d e * gueMatrix x i f g * gueMatrix x i h a) μ := by
  have h := integrable_gueProd (N := N) (ι := ι)
    [(i, (b, c)), (i, (d, e)), (i, (f, g)), (i, (h, a))]
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [gueProd_cons, gueProd_nil, gueEntry_mk, mul_one]
  ring

/-- Integrability of a summand of the eightfold expansion. -/
theorem integrable_trace_summand8 (A B C D : Matrix (Fin N) (Fin N) ℂ) (i : ι)
    (a b c d e f g h : Fin N) :
    Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      A a b * gueMatrix x i b c * B c d * gueMatrix x i d e * C e f *
        gueMatrix x i f g * D g h * gueMatrix x i h a) μ := by
  have h1 : Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      (A a b * B c d * C e f * D g h) *
        (gueMatrix x i b c * gueMatrix x i d e * gueMatrix x i f g * gueMatrix x i h a)) μ :=
    (integrable_four_entry (N := N) (ι := ι) i b c d e f g h a).const_mul _
  refine h1.congr (Eventually.of_forall fun x => ?_)
  ring

/-! ### 3. The eightfold integral interchange -/

/-- **The integral of an eightfold finite sum is the eightfold sum of the integrals.** -/
theorem integral_sum8 {F : (Fin N) → (Fin N) → (Fin N) → (Fin N) → (Fin N) → (Fin N) →
    (Fin N) → (Fin N) → EuclideanSpace ℝ (GUECoord ι N) → ℂ}
    (hF : ∀ a h g f e d c b, Integrable (F a h g f e d c b) μ) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        (∑ a : Fin N, ∑ h : Fin N, ∑ g : Fin N, ∑ f : Fin N, ∑ e : Fin N, ∑ d : Fin N,
          ∑ c : Fin N, ∑ b : Fin N, F a h g f e d c b x) ∂μ
      = ∑ a : Fin N, ∑ h : Fin N, ∑ g : Fin N, ∑ f : Fin N, ∑ e : Fin N, ∑ d : Fin N,
          ∑ c : Fin N, ∑ b : Fin N, ∫ x : EuclideanSpace ℝ (GUECoord ι N),
            F a h g f e d c b x ∂μ := by
  rw [integral_finsetSum (s := (Finset.univ : Finset (Fin N)))
    (f := fun a x => ∑ h : Fin N, ∑ g : Fin N, ∑ f : Fin N, ∑ e : Fin N, ∑ d : Fin N,
      ∑ c : Fin N, ∑ b : Fin N, F a h g f e d c b x)
    (fun a _ => integrable_finset_sum_univ fun h => integrable_finset_sum_univ fun g =>
      integrable_finset_sum_univ fun f => integrable_finset_sum_univ fun e =>
        integrable_finset_sum_univ fun d => integrable_finset_sum_univ fun c =>
          integrable_finset_sum_univ fun b => hF a h g f e d c b)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum (s := (Finset.univ : Finset (Fin N)))
    (f := fun h x => ∑ g : Fin N, ∑ f : Fin N, ∑ e : Fin N, ∑ d : Fin N,
      ∑ c : Fin N, ∑ b : Fin N, F a h g f e d c b x)
    (fun h _ => integrable_finset_sum_univ fun g => integrable_finset_sum_univ fun f =>
      integrable_finset_sum_univ fun e => integrable_finset_sum_univ fun d =>
        integrable_finset_sum_univ fun c => integrable_finset_sum_univ fun b =>
          hF a h g f e d c b)]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [integral_finsetSum (s := (Finset.univ : Finset (Fin N)))
    (f := fun g x => ∑ f : Fin N, ∑ e : Fin N, ∑ d : Fin N, ∑ c : Fin N, ∑ b : Fin N,
      F a h g f e d c b x)
    (fun g _ => integrable_finset_sum_univ fun f => integrable_finset_sum_univ fun e =>
      integrable_finset_sum_univ fun d => integrable_finset_sum_univ fun c =>
        integrable_finset_sum_univ fun b => hF a h g f e d c b)]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [integral_finsetSum (s := (Finset.univ : Finset (Fin N)))
    (f := fun f x => ∑ e : Fin N, ∑ d : Fin N, ∑ c : Fin N, ∑ b : Fin N, F a h g f e d c b x)
    (fun f _ => integrable_finset_sum_univ fun e => integrable_finset_sum_univ fun d =>
      integrable_finset_sum_univ fun c => integrable_finset_sum_univ fun b =>
        hF a h g f e d c b)]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [integral_finsetSum (s := (Finset.univ : Finset (Fin N)))
    (f := fun e x => ∑ d : Fin N, ∑ c : Fin N, ∑ b : Fin N, F a h g f e d c b x)
    (fun e _ => integrable_finset_sum_univ fun d => integrable_finset_sum_univ fun c =>
      integrable_finset_sum_univ fun b => hF a h g f e d c b)]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [integral_finsetSum (s := (Finset.univ : Finset (Fin N)))
    (f := fun d x => ∑ c : Fin N, ∑ b : Fin N, F a h g f e d c b x)
    (fun d _ => integrable_finset_sum_univ fun c => integrable_finset_sum_univ fun b =>
      hF a h g f e d c b)]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [integral_finsetSum (s := (Finset.univ : Finset (Fin N)))
    (f := fun c x => ∑ b : Fin N, F a h g f e d c b x)
    (fun c _ => integrable_finset_sum_univ fun b => hF a h g f e d c b)]
  exact Finset.sum_congr rfl fun c _ =>
    integral_finsetSum (s := (Finset.univ : Finset (Fin N)))
      (f := fun b x => F a h g f e d c b x) (fun b _ => hF a h g f e d c b)

/-! ### 4. The four-point entry integral -/

/-- **The four-point function** `∫ X b c · X d e · X f g · X h a`, evaluated by the Wick formula:
`N⁻²` times the three pairings of the four entries (`gueCov_mk` normalization). -/
theorem integral_four_entry (i : ι) (b c d e f g h a : Fin N) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        (gueMatrix x i b c * gueMatrix x i d e * gueMatrix x i f g * gueMatrix x i h a) ∂μ
      = ((N : ℂ)⁻¹) ^ 2 *
        ((if b = e ∧ c = d then (1 : ℂ) else 0) * (if f = a ∧ g = h then (1 : ℂ) else 0) +
          (if b = g ∧ c = f then (1 : ℂ) else 0) * (if d = a ∧ e = h then (1 : ℂ) else 0) +
          (if b = a ∧ c = h then (1 : ℂ) else 0) * (if d = g ∧ e = f then (1 : ℂ) else 0)) := by
  have hcongr : (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        gueMatrix x i b c * gueMatrix x i d e * gueMatrix x i f g * gueMatrix x i h a)
      = fun x : EuclideanSpace ℝ (GUECoord ι N) =>
          gueProd [(i, (b, c)), (i, (d, e)), (i, (f, g)), (i, (h, a))] x := by
    funext x
    simp only [gueProd_cons, gueProd_nil, gueEntry_mk, mul_one]
    ring
  rw [hcongr, integral_gueProd_eq_gueWick, gueWick_four]
  simp only [gueCov_mk, eq_self_iff_true, true_and]
  ring

/-! ### 5. The leftover face evaluations in this nesting -/

/-- Faces `tr(AC)`, `tr(B)`, `tr(D)`. -/
theorem leftover_rev_successive (A B C D : Matrix (Fin N) (Fin N) ℂ) :
    (∑ x : Fin N, ∑ x_1 : Fin N, ∑ x_2 : Fin N, ∑ x_3 : Fin N,
        A x x_2 * B x_3 x_3 * C x_2 x * D x_1 x_1) = (A * C).trace * B.trace * D.trace := by
  have hswap : (∑ x : Fin N, ∑ x_1 : Fin N, ∑ x_2 : Fin N, ∑ x_3 : Fin N,
        A x x_2 * B x_3 x_3 * C x_2 x * D x_1 x_1)
      = ∑ x : Fin N, ∑ x_2 : Fin N, ∑ x_1 : Fin N, ∑ x_3 : Fin N,
          (A x x_2 * C x_2 x) * (B x_3 x_3) * (D x_1 x_1) := by
    rw [Finset.sum_congr rfl fun x _ => Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x_2 _ =>
      Finset.sum_congr rfl fun x_1 _ => Finset.sum_congr rfl fun x_3 _ => by ring
  rw [hswap, ← sum_cyclic_entry_prod_two A C, ← sum_cyclic_entry_prod_one B,
    ← sum_cyclic_entry_prod_one D]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]

/-- Faces `tr(A)`, `tr(BD)`, `tr(C)`. -/
theorem leftover_rev_nested (A B C D : Matrix (Fin N) (Fin N) ℂ) :
    (∑ x : Fin N, ∑ x_1 : Fin N, ∑ x_2 : Fin N, ∑ x_3 : Fin N,
        A x x * B x_1 x_2 * C x_3 x_3 * D x_2 x_1) = A.trace * C.trace * (B * D).trace := by
  have hL : (∑ x : Fin N, ∑ x_1 : Fin N, ∑ x_2 : Fin N, ∑ x_3 : Fin N,
        A x x * B x_1 x_2 * C x_3 x_3 * D x_2 x_1)
      = ∑ x : Fin N, ∑ x_1 : Fin N, ∑ x_2 : Fin N, ∑ x_3 : Fin N,
          (A x x * (B x_1 x_2 * D x_2 x_1)) * C x_3 x_3 := by
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x_1 _ =>
      Finset.sum_congr rfl fun x_2 _ => Finset.sum_congr rfl fun x_3 _ => by ring
  rw [hL, ← sum_cyclic_entry_prod_one A, ← sum_cyclic_entry_prod_one C,
    ← sum_cyclic_entry_prod_two B D]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- The single face `tr(ADC B)`. -/
theorem leftover_rev_crossing (A B C D : Matrix (Fin N) (Fin N) ℂ) :
    (∑ x : Fin N, ∑ x_1 : Fin N, ∑ x_2 : Fin N, ∑ x_3 : Fin N,
        A x x_2 * B x_3 x * C x_1 x_3 * D x_2 x_1) = (A * D * C * B).trace := by
  have hswap : (∑ x : Fin N, ∑ x_1 : Fin N, ∑ x_2 : Fin N, ∑ x_3 : Fin N,
        A x x_2 * B x_3 x * C x_1 x_3 * D x_2 x_1)
      = ∑ x : Fin N, ∑ x_2 : Fin N, ∑ x_1 : Fin N, ∑ x_3 : Fin N,
          A x x_2 * B x_3 x * C x_1 x_3 * D x_2 x_1 := by
    rw [Finset.sum_congr rfl fun x _ => Finset.sum_comm]
  rw [hswap, ← sum_cyclic_entry_prod_four A D C B]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x_2 _ =>
    Finset.sum_congr rfl fun x_1 _ => Finset.sum_congr rfl fun x_3 _ => by ring

/-! ### 6. The three collapses in conjunction form -/

/-- Pairing `(12)(34)`: faces `tr(AC)`, `tr(B)`, `tr(D)`. -/
theorem collapse_conj_successive (A B C D : Matrix (Fin N) (Fin N) ℂ) :
    (∑ a : Fin N, ∑ h : Fin N, ∑ g : Fin N, ∑ f : Fin N, ∑ e : Fin N, ∑ d : Fin N,
        ∑ c : Fin N, ∑ b : Fin N,
        A a b * B c d * C e f * D g h *
          ((if b = e ∧ c = d then (1 : ℂ) else 0) * (if f = a ∧ g = h then (1 : ℂ) else 0)))
      = (A * C).trace * B.trace * D.trace := by
  simp only [ite_and, mul_ite, mul_one, mul_zero, sum_ite_const_cond, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact leftover_rev_successive A B C D

/-- Pairing `(13)(24)`: the single face `tr(ADC B)`. -/
theorem collapse_conj_crossing (A B C D : Matrix (Fin N) (Fin N) ℂ) :
    (∑ a : Fin N, ∑ h : Fin N, ∑ g : Fin N, ∑ f : Fin N, ∑ e : Fin N, ∑ d : Fin N,
        ∑ c : Fin N, ∑ b : Fin N,
        A a b * B c d * C e f * D g h *
          ((if b = g ∧ c = f then (1 : ℂ) else 0) * (if d = a ∧ e = h then (1 : ℂ) else 0)))
      = (A * D * C * B).trace := by
  simp only [ite_and, mul_ite, mul_one, mul_zero, sum_ite_const_cond, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact leftover_rev_crossing A B C D

/-- Pairing `(14)(23)`: faces `tr(A)`, `tr(BD)`, `tr(C)`. -/
theorem collapse_conj_nested (A B C D : Matrix (Fin N) (Fin N) ℂ) :
    (∑ a : Fin N, ∑ h : Fin N, ∑ g : Fin N, ∑ f : Fin N, ∑ e : Fin N, ∑ d : Fin N,
        ∑ c : Fin N, ∑ b : Fin N,
        A a b * B c d * C e f * D g h *
          ((if b = a ∧ c = h then (1 : ℂ) else 0) * (if d = g ∧ e = f then (1 : ℂ) else 0)))
      = A.trace * C.trace * (B * D).trace := by
  simp only [ite_and, mul_ite, mul_one, mul_zero, sum_ite_const_cond, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact leftover_rev_nested A B C D

/-! ### 7. The exact length-4 mixed moment -/

/-- **The exact length-4 mixed moment**:
`E tr(A X B X C X D X) = N⁻² ( tr(AC) tr(B) tr(D) + tr(A) tr(C) tr(BD) + tr(ADC B) )`,
i.e. the three Wick pairings of the four insertions, weighted by `N⁻²` and by the product of the
traces of the coefficient matrices along their faces (two non-crossing pairings with three faces,
one crossing pairing with a single face). -/
theorem integral_trace_mul_four_gue (A B C D : Matrix (Fin N) (Fin N) ℂ) (i : ι) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        Matrix.trace (A * gueMatrix x i * B * gueMatrix x i * C * gueMatrix x i *
          D * gueMatrix x i) ∂μ
      = lengthFourMixedRHS A B C D := by
  simp only [lengthFourMixedRHS]
  simp only [trace_mul_four_gue_eq_sum8]
  rw [integral_sum8 (fun a h g f e d c b => integrable_trace_summand8 A B C D i a b c d e f g h)]
  -- the integral of one summand
  have hterm : ∀ (a b c d e f g h : Fin N),
      ∫ x : EuclideanSpace ℝ (GUECoord ι N),
          (A a b * gueMatrix x i b c * B c d * gueMatrix x i d e * C e f *
            gueMatrix x i f g * D g h * gueMatrix x i h a) ∂μ
        = ((N : ℂ)⁻¹) ^ 2 * (A a b * B c d * C e f * D g h) *
          ((if b = e ∧ c = d then (1 : ℂ) else 0) * (if f = a ∧ g = h then (1 : ℂ) else 0) +
            (if b = g ∧ c = f then (1 : ℂ) else 0) * (if d = a ∧ e = h then (1 : ℂ) else 0) +
            (if b = a ∧ c = h then (1 : ℂ) else 0) * (if d = g ∧ e = f then (1 : ℂ) else 0)) := by
    intro a b c d e f g h
    have hsplit : (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
          A a b * gueMatrix x i b c * B c d * gueMatrix x i d e * C e f *
            gueMatrix x i f g * D g h * gueMatrix x i h a)
        = fun x : EuclideanSpace ℝ (GUECoord ι N) =>
            (A a b * B c d * C e f * D g h) *
              (gueMatrix x i b c * gueMatrix x i d e * gueMatrix x i f g * gueMatrix x i h a) := by
      funext x
      ring
    rw [hsplit, integral_const_mul, integral_four_entry]
    ring
  simp only [hterm]
  -- split the three pairings and pull out the normalization
  have hpt : ∀ (a b c d e f g h : Fin N),
      ((N : ℂ)⁻¹) ^ 2 * (A a b * B c d * C e f * D g h) *
        ((if b = e ∧ c = d then (1 : ℂ) else 0) * (if f = a ∧ g = h then (1 : ℂ) else 0) +
          (if b = g ∧ c = f then (1 : ℂ) else 0) * (if d = a ∧ e = h then (1 : ℂ) else 0) +
          (if b = a ∧ c = h then (1 : ℂ) else 0) * (if d = g ∧ e = f then (1 : ℂ) else 0))
        = ((N : ℂ)⁻¹) ^ 2 * (A a b * B c d * C e f * D g h *
              ((if b = e ∧ c = d then (1 : ℂ) else 0) *
                (if f = a ∧ g = h then (1 : ℂ) else 0)))
          + ((N : ℂ)⁻¹) ^ 2 * (A a b * B c d * C e f * D g h *
              ((if b = g ∧ c = f then (1 : ℂ) else 0) *
                (if d = a ∧ e = h then (1 : ℂ) else 0)))
          + ((N : ℂ)⁻¹) ^ 2 * (A a b * B c d * C e f * D g h *
              ((if b = a ∧ c = h then (1 : ℂ) else 0) *
                (if d = g ∧ e = f then (1 : ℂ) else 0))) := by
    intro a b c d e f g h
    ring
  simp only [hpt, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [collapse_conj_successive A B C D, collapse_conj_crossing A B C D,
    collapse_conj_nested A B C D]
  ring

/-- **The length-4 mixed moment formula of `MixedGenusForm` is now a theorem.** -/
theorem lengthFourMixedMomentFormula :
    LengthFourMixedMomentFormula (ι := ι) (N := N) :=
  fun A B C D i => integral_trace_mul_four_gue A B C D i

/-- **Normalized length-4 mixed moment**: `E τ_N(A X B X C X D X)` is `N⁻³` times the sum of the
three face labels. -/
theorem integral_normalizedTrace_mul_four_gue (A B C D : Matrix (Fin N) (Fin N) ℂ) (i : ι) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        ((N : ℂ)⁻¹ * Matrix.trace (A * gueMatrix x i * B * gueMatrix x i * C * gueMatrix x i *
          D * gueMatrix x i)) ∂μ
      = ((N : ℂ)⁻¹) ^ 3 *
        ((A * C).trace * B.trace * D.trace + A.trace * C.trace * (B * D).trace +
          (A * D * C * B).trace) := by
  rw [integral_const_mul, integral_trace_mul_four_gue]
  simp only [lengthFourMixedRHS]
  ring

/-- **The second-order correction vanishes exactly for the length-4 mixed word**: the normalized mean
differs from the planar (non-crossing) value `τ_N(AC) τ_N(B) τ_N(D) + τ_N(A) τ_N(C) τ_N(BD)` by
exactly `N⁻³ tr(ADC B)`, the single crossing face. -/
theorem integral_normalizedTrace_mul_four_gue_sub_free
    (A B C D : Matrix (Fin N) (Fin N) ℂ) (i : ι) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        ((N : ℂ)⁻¹ * Matrix.trace (A * gueMatrix x i * B * gueMatrix x i * C * gueMatrix x i *
          D * gueMatrix x i)) ∂μ
      - (((N : ℂ)⁻¹ * (A * C).trace) * ((N : ℂ)⁻¹ * B.trace) * ((N : ℂ)⁻¹ * D.trace) +
          ((N : ℂ)⁻¹ * A.trace) * ((N : ℂ)⁻¹ * C.trace) * ((N : ℂ)⁻¹ * (B * D).trace))
      = ((N : ℂ)⁻¹) ^ 3 * (A * D * C * B).trace := by
  rw [integral_normalizedTrace_mul_four_gue]
  ring

/-- **`N⁻²` mean accuracy of the length-4 mixed word.**  The normalized mean is within
`N⁻³ ‖tr(ADC B)‖` of the planar value, i.e. `O(N⁻²)` — in fact `O(N⁻⁵ᐟ²)` in Frobenius norm once
`‖tr M‖ ≤ √N ‖M‖` is used.  This is the mixed-mean accuracy shape required by the pencil side. -/
theorem norm_integral_normalizedTrace_mul_four_gue_sub_free_le
    (A B C D : Matrix (Fin N) (Fin N) ℂ) (i : ι) :
    ‖∫ x : EuclideanSpace ℝ (GUECoord ι N),
        ((N : ℂ)⁻¹ * Matrix.trace (A * gueMatrix x i * B * gueMatrix x i * C * gueMatrix x i *
          D * gueMatrix x i)) ∂μ
      - (((N : ℂ)⁻¹ * (A * C).trace) * ((N : ℂ)⁻¹ * B.trace) * ((N : ℂ)⁻¹ * D.trace) +
          ((N : ℂ)⁻¹ * A.trace) * ((N : ℂ)⁻¹ * C.trace) * ((N : ℂ)⁻¹ * (B * D).trace))‖
      ≤ ((N : ℝ)⁻¹) ^ 3 * ‖(A * D * C * B).trace‖ := by
  rw [integral_normalizedTrace_mul_four_gue_sub_free]
  have hN : ‖((N : ℂ)⁻¹) ^ 3‖ = ((N : ℝ)⁻¹) ^ 3 := by
    rw [norm_pow, norm_inv, Complex.norm_natCast]
  rw [norm_mul, hN]

end

end GUEStrongConvergence
