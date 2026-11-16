/-
# The sharp two-point correlation for the scalar single-GUE resolvent

This file closes the last analytic gap of Part II.A **for the scalar single-GUE case**: the
sharp `O(N⁻²)` two-point (variance) bound for the resolvent partial trace
`T_N(z) = tr_N (z • 1 - G)⁻¹`, which is the input behind HT05 Proposition 4.7.

## Main results

* `sum_sq_guePartialTraceDir_scalar_le` — the **sharp gradient bound**

  `∑_p ‖∂_p T_N(z)‖² ≤ 2 N⁻² (im z)⁻⁴`

  for the scalar model (`d = Unit`, `ι = Unit`, `A₀ = 0`, `A = 1`).

* `variance_scalar_re_le`, `variance_scalar_im_le` — the sharp entrywise variance bounds
  `Var(Re T_N(z)) ≤ 2 N⁻² (im z)⁻⁴`, `Var(Im T_N(z)) ≤ 2 N⁻² (im z)⁻⁴`.

* `integral_norm_sq_fluctuation_scalar_le` — the **sharp two-point correlation**

  `∫ ‖T_N(z) − E T_N(z)‖² ≤ 4 N⁻² (im z)⁻⁴`.

* `variance_partialTrace_re_le_of_grad`, `variance_partialTrace_im_le_of_grad`,
  `integral_norm_sq_fluctuation_le_of_var` — reusable *generic* forms for an arbitrary
  GUE pencil: any bound `∑_p ‖∂_p T_N(z)_{uv}‖² ≤ C` yields `Var ≤ C` and
  `∫ ‖T − ET‖² ≤ 2 C` by the Gaussian Poincaré inequality.

## Where the missing factor `N` was

`DysonVariance.sum_sq_guePartialTraceDir_le` bounds `∑_p ‖∂_p T_N(z)_{uv}‖²` by
`2 gueScale(N)² (∑_i frob(A_i)²) (im z)⁻⁴ = O(N⁻¹)`.  That bound is **not sharp**: it splits
the partial trace `∑_k` with Cauchy–Schwarz over the `N` indices `k` (`(∑_k a_k)² ≤ N ∑_k a_k²`)
and then bounds each `k`-term by the *same* uniform constant, losing a factor `N` twice while
gaining it back only once.  The sharp treatment keeps the `k`-sum intact:

`∑_k (R B_p R)_{(u,k),(v,k)} = tr(B_p · S)`,  `S = R P R`,  `P = ∑_k |(v,k)⟩⟨(u,k)|`,

so that the exact direction contraction `∑_p ‖tr(B_p X)‖² = ‖X‖_F² / N` (the statement that
`√N · B_p` is an orthonormal basis of the Hermitian matrices for the Hilbert–Schmidt inner
product) applies.  Together with `‖S‖_F² ≤ N (im z)⁻⁴` this gives `O(N⁻²)`.

Consequently the sharp rate does **not** require a second-order integration-by-parts identity
or a three-point correlation bound: the first-order Gaussian Poincaré inequality
(`gaussian_poincare_stdGaussian`) applied to the *sharp* gradient bound already gives `N⁻²`.
The corresponding second-loop-equation route would give
`(z − 2 m(z)) Var(T) = W₃ + E[tr(R³)]/N³`, i.e. `Var ≤ C(|W₃| + N⁻²)/|z − 2m|`, which is
*weaker* (it needs a bound on the connected three-point function `W₃` and degenerates where
`z = 2m(z)`, i.e. near the spectral edge).

## The general pencil

The same argument is carried out for an arbitrary pencil (`d`, `ι` arbitrary, arbitrary
Hermitian `A_i`).  The new ingredients are:

* `guePartialTraceDir_sum_eq_kernel`: the exact identification
  `∑_k (R B_p R)_{(u,k),(v,k)} = ∑_{l,m} (B_p)_{lm} S_{lm}` with the partial-trace kernel
  `S_{lm} = ∑_k R_{(u,k),l} R_{m,(v,k)}` (no Cauchy–Schwarz over `k`!);
* `guePencil_trace_contraction`: the Hilbert–Schmidt orthonormality of the direction family
  `∑_p ‖tr(B_p X)‖² ≤ 2 gueScale(N)² (∑_i frob(A_i)²) ‖X‖_F²`;
* `guePartialTraceKernel_frob_le`: `‖S‖_F² ≤ N (im z)⁻⁴`, proved column by column with
  `sum_sq_matVec_le` (the ℓ² action bound) and `sum_sq_rowComb_le` — this is where the sharp
  `N` (rather than `N²`) enters.

These yield

* `sum_sq_guePartialTraceDir_le_sharp`:
  `∑_p ‖∂_p T_N(z)_{uv}‖² ≤ 2 gueScale(N)² (∑_i frob(A_i)²) (im z)⁻⁴ / N`,
* `variance_partialTrace_{re,im}_le_sharp`: the same bound for the variances,
* `integral_norm_sq_fluctuation_le_sharp`:
  `∫ ‖T_N(z)_{uv} − E T_N(z)_{uv}‖² ≤ 4 gueScale(N)² (∑_i frob(A_i)²) (im z)⁻⁴ / N`,

i.e. exactly the `O(N⁻²)` rate (since `gueScale(N)² = 1/N`), improving
`DysonVariance.variance_partialTrace_re_le` / `integral_norm_sq_fluctuation_le` by a factor `N`.

* `covariance_partialTrace_mul_le_sharp`:
  `frob (E[T B T] − E[T] B E[T]) ≤ 2 (card d)² frob B · (2 gueScale(N)² (∑_i frob(A_i)²)
  (im z)⁻⁴ / N)` — a factor `N` better than `covariance_partialTrace_mul_le`;
* `approximate_dyson_entry_le_sharp`: every entry of
  `(z • 1 − A₀) g_N − 1 − ∑_i A_i g_N A_i g_N` is bounded by
  `2 (card d)² √(card d) (∑_i frob(A_i)²) · (2 gueScale(N)² (∑_i frob(A_i)²) (im z)⁻⁴ / N)`,
  i.e. `O(N⁻²)` — the sharp approximate Dyson equation.

## What is not proved here

The final stability comparison `frob (g_N − g) = O(N⁻²)` in `DysonLimit`: it is the
stability lemma of `DysonLimit` re-run with `approximate_dyson_entry_le_sharp` as input
(the same `frob(g'−g) ≤ 2Cη⁻¹ frob D` argument, with `D` now of order `N⁻²`).  That step is
purely mechanical given the sharp approximate Dyson equation proved here.
-/
import GUEStrongConvergence.Probability.DysonVariance

open MeasureTheory ProbabilityTheory Matrix Kronecker Filter
open scoped Matrix.Norms.Elementwise ComplexOrder ENNReal NNReal Topology

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace GUEStrongConvergence
noncomputable section

variable {ι d : Type*} {N : ℕ} [Fintype ι] [Fintype d] [DecidableEq d] [DecidableEq ι]

/-- The scalar single-GUE coefficient family. -/
abbrev gueScalarA : Unit → Matrix Unit Unit ℂ := fun _ => 1

/-- The scalar single-GUE base matrix. -/
abbrev gueScalarA₀ : Matrix Unit Unit ℂ := 0

lemma gueScalarDirection_apply (p : GUECoord Unit N) (a b : Unit × Fin N) :
    guePencilDirection gueScalarA p a b
      = (gueScale N : ℂ) * (gueAlpha * (if p.2 = (a.2, b.2) then 1 else 0)
          + gueBeta * (if p.2 = (b.2, a.2) then 1 else 0)) := by
  rw [guePencilDirection_apply]
  simp

/-- Pointwise: the scalar direction entry is a two-delta kernel on `Fin N` indices. -/
lemma gueScalarDirection_delta (a b : Fin N) (k l : Unit × Fin N) :
    guePencilDirection gueScalarA ((), (a, b)) k l
      = (gueScale N : ℂ) * (gueAlpha * (if k = ((), a) ∧ l = ((), b) then 1 else 0)
          + gueBeta * (if k = ((), b) ∧ l = ((), a) then 1 else 0)) := by
  rw [gueScalarDirection_apply]
  have hk : ∀ c : Fin N, k = ((), c) ↔ k.2 = c := by
    intro c
    constructor
    · intro h; rw [h]
    · intro h; exact Prod.ext (Subsingleton.elim _ _) h
  have hl : ∀ c : Fin N, l = ((), c) ↔ l.2 = c := by
    intro c
    constructor
    · intro h; rw [h]
    · intro h; exact Prod.ext (Subsingleton.elim _ _) h
  have e1 : (((a, b) : Fin N × Fin N) = (k.2, l.2)) ↔ (k = ((), a) ∧ l = ((), b)) := by
    rw [Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨(hk a).mpr h1.symm, (hl b).mpr h2.symm⟩
    · rintro ⟨h1, h2⟩; exact ⟨((hk a).mp h1).symm, ((hl b).mp h2).symm⟩
  have e2 : (((a, b) : Fin N × Fin N) = (l.2, k.2)) ↔ (k = ((), b) ∧ l = ((), a)) := by
    rw [Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨(hk b).mpr h2.symm, (hl a).mpr h1.symm⟩
    · rintro ⟨h1, h2⟩; exact ⟨((hl a).mp h2).symm, ((hk b).mp h1).symm⟩
  rw [if_congr e1 rfl rfl, if_congr e2 rfl rfl]

/-- Trace pairing against a scalar direction: `tr (B_p X) = gueScale * (α X_{ba} + β X_{ab})`. -/
lemma gueScalar_trace_direction (X : CStarMatrix (Unit × Fin N) (Unit × Fin N) ℂ)
    (a b : Fin N) :
    (∑ k : Unit × Fin N, ∑ l : Unit × Fin N,
        guePencilDirection gueScalarA ((), (a, b)) k l * X l k)
      = (gueScale N : ℂ) * (gueAlpha * X ((), b) ((), a) + gueBeta * X ((), a) ((), b)) := by
  have hpt : ∀ k l : Unit × Fin N,
      guePencilDirection gueScalarA ((), (a, b)) k l * X l k
        = (gueScale N : ℂ) * gueAlpha * (if k = ((), a) ∧ l = ((), b) then X l k else 0)
          + (gueScale N : ℂ) * gueBeta * (if k = ((), b) ∧ l = ((), a) then X l k else 0) := by
    intro k l
    rw [gueScalarDirection_delta]
    split_ifs <;> ring
  have hS1 : (∑ k : Unit × Fin N, ∑ l : Unit × Fin N,
      (if k = ((), a) ∧ l = ((), b) then X l k else 0)) = X ((), b) ((), a) := by
    rw [Finset.sum_eq_single ((), a)]
    · rw [Finset.sum_eq_single ((), b)]
      · simp
      · intro l _ hl; simp [hl]
      · intro h; simp at h
    · intro k _ hk
      refine Finset.sum_eq_zero fun l _ => ?_
      simp [hk]
    · intro h; simp at h
  have hS2 : (∑ k : Unit × Fin N, ∑ l : Unit × Fin N,
      (if k = ((), b) ∧ l = ((), a) then X l k else 0)) = X ((), a) ((), b) := by
    rw [Finset.sum_eq_single ((), b)]
    · rw [Finset.sum_eq_single ((), a)]
      · simp
      · intro l _ hl; simp [hl]
      · intro h; simp at h
    · intro k _ hk
      refine Finset.sum_eq_zero fun l _ => ?_
      simp [hk]
    · intro h; simp at h
  calc (∑ k : Unit × Fin N, ∑ l : Unit × Fin N,
        guePencilDirection gueScalarA ((), (a, b)) k l * X l k)
      = ∑ k : Unit × Fin N, ∑ l : Unit × Fin N,
          ((gueScale N : ℂ) * gueAlpha * (if k = ((), a) ∧ l = ((), b) then X l k else 0)
            + (gueScale N : ℂ) * gueBeta * (if k = ((), b) ∧ l = ((), a) then X l k else 0)) :=
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => hpt k l
    _ = (gueScale N : ℂ) * gueAlpha * (∑ k : Unit × Fin N, ∑ l : Unit × Fin N,
            (if k = ((), a) ∧ l = ((), b) then X l k else 0))
          + (gueScale N : ℂ) * gueBeta * (∑ k : Unit × Fin N, ∑ l : Unit × Fin N,
            (if k = ((), b) ∧ l = ((), a) then X l k else 0)) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ = (gueScale N : ℂ) * (gueAlpha * X ((), b) ((), a) + gueBeta * X ((), a) ((), b)) := by
        rw [hS1, hS2]; ring

/-- Permutation of a triple sum. -/
lemma sum_triple_perm {α : Type*} [Fintype α] (f : α → α → α → ℂ) :
    (∑ c, ∑ a, ∑ b, f c a b) = ∑ b, ∑ a, ∑ c, f c a b := by
  calc (∑ c, ∑ a, ∑ b, f c a b)
      = ∑ c, ∑ b, ∑ a, f c a b := by
        refine Finset.sum_congr rfl fun c _ => ?_
        exact Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ a, f c a b := Finset.sum_comm
    _ = ∑ b, ∑ a, ∑ c, f c a b := by
        refine Finset.sum_congr rfl fun b _ => ?_
        exact Finset.sum_comm

/-- The `k`-sum of the resolvent sandwich diagonal is the trace against `R * R`. -/
lemma gueScalar_dir_sum_eq_trace (x : GUECoord Unit N → ℝ) (z : ℂ) (p : GUECoord Unit N) :
    (∑ k : Fin N, (guePencilResolvent gueScalarA₀ gueScalarA x z *
        guePencilDirection gueScalarA p *
        guePencilResolvent gueScalarA₀ gueScalarA x z) ((), k) ((), k))
      = ∑ l : Unit × Fin N, ∑ m : Unit × Fin N,
          guePencilDirection gueScalarA p l m *
            (guePencilResolvent gueScalarA₀ gueScalarA x z *
              guePencilResolvent gueScalarA₀ gueScalarA x z) m l := by
  have h1 : (∑ k : Fin N, (guePencilResolvent gueScalarA₀ gueScalarA x z *
        guePencilDirection gueScalarA p *
        guePencilResolvent gueScalarA₀ gueScalarA x z) ((), k) ((), k))
      = ∑ c : Unit × Fin N, (guePencilResolvent gueScalarA₀ gueScalarA x z *
          guePencilDirection gueScalarA p *
          guePencilResolvent gueScalarA₀ gueScalarA x z) c c := by
    rw [Fintype.sum_equiv (Equiv.uniqueProd (Fin N) Unit)]
    intro c
    rfl
  rw [h1]
  calc (∑ c : Unit × Fin N, (guePencilResolvent gueScalarA₀ gueScalarA x z *
          guePencilDirection gueScalarA p *
          guePencilResolvent gueScalarA₀ gueScalarA x z) c c)
      = ∑ c : Unit × Fin N, ∑ a : Unit × Fin N, ∑ b : Unit × Fin N,
          guePencilResolvent gueScalarA₀ gueScalarA x z c b *
            guePencilDirection gueScalarA p b a *
            guePencilResolvent gueScalarA₀ gueScalarA x z a c := by
        simp only [CStarMatrix.mul_apply, Finset.sum_mul]
    _ = ∑ b : Unit × Fin N, ∑ a : Unit × Fin N, ∑ c : Unit × Fin N,
          guePencilResolvent gueScalarA₀ gueScalarA x z c b *
            guePencilDirection gueScalarA p b a *
            guePencilResolvent gueScalarA₀ gueScalarA x z a c := sum_triple_perm _
    _ = ∑ l : Unit × Fin N, ∑ m : Unit × Fin N, ∑ a : Unit × Fin N,
          guePencilDirection gueScalarA p l m *
            (guePencilResolvent gueScalarA₀ gueScalarA x z m a *
              guePencilResolvent gueScalarA₀ gueScalarA x z a l) := by
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun c _ => ?_
        ring
    _ = ∑ l : Unit × Fin N, ∑ m : Unit × Fin N,
          guePencilDirection gueScalarA p l m *
            (guePencilResolvent gueScalarA₀ gueScalarA x z *
              guePencilResolvent gueScalarA₀ gueScalarA x z) m l := by
        simp only [CStarMatrix.mul_apply, Finset.mul_sum]

/-- Reindexing `Unit × Fin N` to `Fin N`. -/
lemma sum_unit_fin_eq {M : Type*} [AddCommMonoid M] (f : Unit × Fin N → M) :
    (∑ l : Unit × Fin N, f l) = ∑ a : Fin N, f ((), a) := by
  rw [Fintype.sum_equiv (Equiv.uniqueProd (Fin N) Unit)]
  intro c
  rfl

/-- Reindexing a double sum over `Unit × Fin N`. -/
lemma sum_unit_fin_pair {M : Type*} [AddCommMonoid M]
    (g : (Unit × Fin N) → (Unit × Fin N) → M) :
    (∑ l : Unit × Fin N, ∑ m : Unit × Fin N, g l m)
      = ∑ a : Fin N, ∑ b : Fin N, g ((), a) ((), b) := by
  rw [sum_unit_fin_eq (fun l => ∑ m : Unit × Fin N, g l m)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [sum_unit_fin_eq]

/-- Reverse reindexing of a double sum over `Unit × Fin N`. -/
lemma sum_fin_pair_unit {M : Type*} [AddCommMonoid M]
    (h : Fin N → Fin N → M) :
    (∑ a : Fin N, ∑ b : Fin N, h a b)
      = ∑ l : Unit × Fin N, ∑ m : Unit × Fin N, h l.2 m.2 := by
  rw [sum_unit_fin_pair (fun l m => h l.2 m.2)]

lemma gueAlpha_norm_sq_add_gueBeta_norm_sq :
    ‖(gueAlpha : ℂ)‖ ^ 2 + ‖(gueBeta : ℂ)‖ ^ 2 = 1 := by
  have h1 : ‖(gueAlpha : ℂ)‖ ^ 2 = 1 / 2 := by
    rw [Complex.sq_norm]
    simp only [gueAlpha, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.div_re, Complex.div_im, Complex.one_re, Complex.one_im, Complex.I_re,
      Complex.I_im]
    norm_num
  have h2 : ‖(gueBeta : ℂ)‖ ^ 2 = 1 / 2 := by
    rw [Complex.sq_norm]
    simp only [gueBeta, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.div_re, Complex.div_im, Complex.one_re, Complex.one_im, Complex.I_re,
      Complex.I_im]
    norm_num
  rw [h1, h2]
  norm_num

/-- Reindexing a sum over the Gaussian coordinates of the scalar model. -/
lemma sum_gueCoord_eq {M : Type*} [AddCommMonoid M] (f : GUECoord Unit N → M) :
    (∑ p : GUECoord Unit N, f p) = ∑ a : Fin N, ∑ b : Fin N, f ((), (a, b)) := by
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_unique]
  rw [Fintype.sum_prod_type]

/-- The `α`/`β` combination bound: `‖α u + β v‖² ≤ ‖u‖² + ‖v‖²` (Cauchy–Schwarz, since
`‖α‖² + ‖β‖² = 1`). -/
lemma gueAlpha_beta_combination_norm_sq_le (u v : ℂ) :
    ‖(gueAlpha : ℂ) * u + (gueBeta : ℂ) * v‖ ^ 2 ≤ ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  have h4 : ‖(gueAlpha : ℂ)‖ ^ 2 + ‖(gueBeta : ℂ)‖ ^ 2 = 1 :=
    gueAlpha_norm_sq_add_gueBeta_norm_sq
  have hCS : (‖(gueAlpha : ℂ)‖ * ‖u‖ + ‖(gueBeta : ℂ)‖ * ‖v‖) ^ 2
      ≤ (‖(gueAlpha : ℂ)‖ ^ 2 + ‖(gueBeta : ℂ)‖ ^ 2) * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
    nlinarith [sq_nonneg (‖(gueAlpha : ℂ)‖ * ‖v‖ - ‖(gueBeta : ℂ)‖ * ‖u‖)]
  rw [h4, one_mul] at hCS
  calc ‖(gueAlpha : ℂ) * u + (gueBeta : ℂ) * v‖ ^ 2
      ≤ (‖(gueAlpha : ℂ)‖ * ‖u‖ + ‖(gueBeta : ℂ)‖ * ‖v‖) ^ 2 := by
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
        calc ‖(gueAlpha : ℂ) * u + (gueBeta : ℂ) * v‖
            ≤ ‖(gueAlpha : ℂ) * u‖ + ‖(gueBeta : ℂ) * v‖ := norm_add_le _ _
          _ = ‖(gueAlpha : ℂ)‖ * ‖u‖ + ‖(gueBeta : ℂ)‖ * ‖v‖ := by rw [norm_mul, norm_mul]
    _ ≤ ‖u‖ ^ 2 + ‖v‖ ^ 2 := hCS

/-- The scalar direction trace contraction: the squared trace pairing summed over all
coordinates is bounded by twice the Frobenius square of the test matrix. -/
lemma gueScalar_trace_contraction (X : CStarMatrix (Unit × Fin N) (Unit × Fin N) ℂ) :
    (∑ p : GUECoord Unit N,
        ‖∑ l : Unit × Fin N, ∑ m : Unit × Fin N,
          guePencilDirection gueScalarA p l m * X m l‖ ^ 2)
      ≤ 2 * (gueScale N) ^ 2 *
          (∑ a : Fin N, ∑ b : Fin N, ‖X ((), a) ((), b)‖ ^ 2) := by
  have hcs : ∀ u v : ℂ, ‖(gueAlpha : ℂ) * u + (gueBeta : ℂ) * v‖ ^ 2
      ≤ ‖u‖ ^ 2 + ‖v‖ ^ 2 := gueAlpha_beta_combination_norm_sq_le
  have hstep : ∀ a b : Fin N,
      ‖∑ l : Unit × Fin N, ∑ m : Unit × Fin N,
          guePencilDirection gueScalarA ((), (a, b)) l m * X m l‖ ^ 2
        ≤ (gueScale N) ^ 2 * (‖X ((), b) ((), a)‖ ^ 2 + ‖X ((), a) ((), b)‖ ^ 2) := by
    intro a b
    rw [gueScalar_trace_direction X a b, norm_mul, mul_pow]
    calc ‖(gueScale N : ℂ)‖ ^ 2 *
          ‖(gueAlpha : ℂ) * X ((), b) ((), a) + (gueBeta : ℂ) * X ((), a) ((), b)‖ ^ 2
        ≤ ‖(gueScale N : ℂ)‖ ^ 2 *
            (‖X ((), b) ((), a)‖ ^ 2 + ‖X ((), a) ((), b)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hcs _ _) (by positivity)
      _ = (gueScale N) ^ 2 *
            (‖X ((), b) ((), a)‖ ^ 2 + ‖X ((), a) ((), b)‖ ^ 2) := by
          rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hswap : (∑ a : Fin N, ∑ b : Fin N, ‖X ((), b) ((), a)‖ ^ 2)
      = ∑ a : Fin N, ∑ b : Fin N, ‖X ((), a) ((), b)‖ ^ 2 := Finset.sum_comm
  rw [sum_gueCoord_eq (fun p => ‖∑ l : Unit × Fin N, ∑ m : Unit × Fin N,
    guePencilDirection gueScalarA p l m * X m l‖ ^ 2)]
  calc (∑ a : Fin N, ∑ b : Fin N,
        ‖∑ l : Unit × Fin N, ∑ m : Unit × Fin N,
          guePencilDirection gueScalarA ((), (a, b)) l m * X m l‖ ^ 2)
      ≤ ∑ a : Fin N, ∑ b : Fin N, (gueScale N) ^ 2 *
          (‖X ((), b) ((), a)‖ ^ 2 + ‖X ((), a) ((), b)‖ ^ 2) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hstep a b
    _ = (gueScale N) ^ 2 * ∑ a : Fin N, ∑ b : Fin N,
          (‖X ((), b) ((), a)‖ ^ 2 + ‖X ((), a) ((), b)‖ ^ 2) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
    _ = (gueScale N) ^ 2 * (2 * ∑ a : Fin N, ∑ b : Fin N, ‖X ((), a) ((), b)‖ ^ 2) := by
        rw [show (∑ a : Fin N, ∑ b : Fin N,
              (‖X ((), b) ((), a)‖ ^ 2 + ‖X ((), a) ((), b)‖ ^ 2))
            = 2 * ∑ a : Fin N, ∑ b : Fin N, ‖X ((), a) ((), b)‖ ^ 2 from by
          have hsplit : (∑ a : Fin N, ∑ b : Fin N,
                (‖X ((), b) ((), a)‖ ^ 2 + ‖X ((), a) ((), b)‖ ^ 2))
              = (∑ a : Fin N, ∑ b : Fin N, ‖X ((), b) ((), a)‖ ^ 2)
                + (∑ a : Fin N, ∑ b : Fin N, ‖X ((), a) ((), b)‖ ^ 2) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.sum_add_distrib]
          rw [hsplit, hswap, two_mul]]
    _ = 2 * (gueScale N) ^ 2 *
          (∑ a : Fin N, ∑ b : Fin N, ‖X ((), a) ((), b)‖ ^ 2) := by ring


/-- `matVec` against a unit vector is the corresponding column. -/
lemma matVec_unitVec (R : CStarMatrix (Unit × Fin N) (Unit × Fin N) ℂ) (a m : Unit × Fin N) :
    matVec R (unitVec a) m = R m a := by
  rw [matVec, Finset.sum_eq_single a]
  · simp [unitVec]
  · intro b _ hb; simp [unitVec, hb]
  · intro h; simp at h

/-- Frobenius-type bound for the square of the scalar GUE resolvent on the `u = v = ()` block. -/
lemma gueScalar_RR_entry_sum_le (x : GUECoord Unit N → ℝ) (z : ℂ) (hz : 0 < z.im)
    (_hN : 0 < N) :
    (∑ a : Fin N, ∑ b : Fin N,
        ‖(guePencilResolvent gueScalarA₀ gueScalarA x z *
          guePencilResolvent gueScalarA₀ gueScalarA x z) ((), a) ((), b)‖ ^ 2)
      ≤ (N : ℝ) * ((z.im)⁻¹) ^ 4 := by
  classical
  set R := guePencilResolvent gueScalarA₀ gueScalarA x z with hR
  have hη : (0:ℝ) ≤ (z.im)⁻¹ := by positivity
  -- each column of `R` has squared norm at most `η⁻²`
  have hcolnorm : ∀ b : Fin N, (∑ m : Unit × Fin N, ‖R m ((), b)‖ ^ 2) ≤ (z.im)⁻¹ ^ 2 := by
    intro b
    have h := sum_sq_matVec_le gueScalarA₀ gueScalarA (isHermitian_zero)
      (fun _ => isHermitian_one) z hz (unitVec ((), b)) x
    have h1 : (∑ k : Unit × Fin N, ‖unitVec ((), b) k‖ ^ 2) = 1 := sum_unitVec_norm_sq ((), b)
    have h2 : (∑ m : Unit × Fin N, ‖matVec R (unitVec ((), b)) m‖ ^ 2)
        = ∑ m : Unit × Fin N, ‖R m ((), b)‖ ^ 2 := by
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [matVec_unitVec]
    rw [h2, h1, mul_one] at h
    exact h
  -- the `b`-th column action
  have hcol : ∀ b : Fin N, (∑ m : Unit × Fin N, ‖matVec R (fun l => R l ((), b)) m‖ ^ 2)
      ≤ (z.im)⁻¹ ^ 2 * (∑ m : Unit × Fin N, ‖R m ((), b)‖ ^ 2) :=
    fun b => sum_sq_matVec_le gueScalarA₀ gueScalarA (isHermitian_zero)
      (fun _ => isHermitian_one) z hz (fun l => R l ((), b)) x
  have hentry : ∀ a b : Fin N,
      (R * R) ((), a) ((), b) = matVec R (fun l => R l ((), b)) ((), a) := by
    intro a b
    rw [CStarMatrix.mul_apply]
    rfl
  calc (∑ a : Fin N, ∑ b : Fin N, ‖(R * R) ((), a) ((), b)‖ ^ 2)
      = ∑ b : Fin N, ∑ a : Fin N, ‖matVec R (fun l => R l ((), b)) ((), a)‖ ^ 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
        rw [hentry]
    _ = ∑ b : Fin N, ∑ m : Unit × Fin N, ‖matVec R (fun l => R l ((), b)) m‖ ^ 2 := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [← sum_unit_fin_eq (fun m => ‖matVec R (fun l => R l ((), b)) m‖ ^ 2)]
    _ ≤ ∑ b : Fin N, (z.im)⁻¹ ^ 2 * (∑ m : Unit × Fin N, ‖R m ((), b)‖ ^ 2) :=
        Finset.sum_le_sum fun b _ => hcol b
    _ = (z.im)⁻¹ ^ 2 * ∑ b : Fin N, (∑ m : Unit × Fin N, ‖R m ((), b)‖ ^ 2) := by
        rw [Finset.mul_sum]
    _ ≤ (z.im)⁻¹ ^ 2 * ∑ _b : Fin N, (z.im)⁻¹ ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => hcolnorm b) (sq_nonneg _)
    _ = (z.im)⁻¹ ^ 2 * ((N : ℝ) * (z.im)⁻¹ ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (N : ℝ) * ((z.im)⁻¹) ^ 4 := by ring

/-- **Sharp gradient bound for the scalar single GUE.**  The squared Euclidean norm of the
coordinate gradient of `T_N(z) = tr_N (z - G)^{-1}` is `O(N⁻²)`, not `O(N⁻¹)`:
`∑_p ‖∂_p T‖² ≤ 2 N⁻² (im z)⁻⁴`.  The gain over `sum_sq_guePartialTraceDir_le` is a factor `N`,
obtained by contracting the whole partial-trace sum against the direction matrix instead of
splitting it with Cauchy--Schwarz over the `N` partial-trace indices. -/
theorem sum_sq_guePartialTraceDir_scalar_le (x : GUECoord Unit N → ℝ) (z : ℂ)
    (hz : 0 < z.im) (hN : 0 < N) :
    (∑ p : GUECoord Unit N, ‖guePartialTraceDir gueScalarA₀ gueScalarA z () () p x‖ ^ 2)
      ≤ 2 * ((N : ℝ)⁻¹) ^ 2 * ((z.im)⁻¹) ^ 4 := by
  classical
  have hη : (0:ℝ) ≤ (z.im)⁻¹ := by positivity
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hD : ∀ p : GUECoord Unit N,
      guePartialTraceDir gueScalarA₀ gueScalarA z () () p x
        = (N : ℂ)⁻¹ * ∑ l : Unit × Fin N, ∑ m : Unit × Fin N,
            guePencilDirection gueScalarA p l m *
              (guePencilResolvent gueScalarA₀ gueScalarA x z *
                guePencilResolvent gueScalarA₀ gueScalarA x z) m l := by
    intro p
    rw [guePartialTraceDir]
    rw [gueScalar_dir_sum_eq_trace x z p]
  have hcontr := gueScalar_trace_contraction (N := N)
    (guePencilResolvent gueScalarA₀ gueScalarA x z *
      guePencilResolvent gueScalarA₀ gueScalarA x z)
  have hFrob := gueScalar_RR_entry_sum_le x z hz hN
  have hnorm : ‖(N : ℂ)⁻¹‖ ^ 2 = ((N : ℝ)⁻¹) ^ 2 := by
    rw [norm_inv, Complex.norm_natCast]
  calc (∑ p : GUECoord Unit N, ‖guePartialTraceDir gueScalarA₀ gueScalarA z () () p x‖ ^ 2)
      = ∑ p : GUECoord Unit N, ‖(N : ℂ)⁻¹ * ∑ l : Unit × Fin N, ∑ m : Unit × Fin N,
          guePencilDirection gueScalarA p l m *
            (guePencilResolvent gueScalarA₀ gueScalarA x z *
              guePencilResolvent gueScalarA₀ gueScalarA x z) m l‖ ^ 2 :=
        Finset.sum_congr rfl fun p _ => by rw [hD p]
    _ = ‖(N : ℂ)⁻¹‖ ^ 2 * ∑ p : GUECoord Unit N,
          ‖∑ l : Unit × Fin N, ∑ m : Unit × Fin N,
            guePencilDirection gueScalarA p l m *
              (guePencilResolvent gueScalarA₀ gueScalarA x z *
                guePencilResolvent gueScalarA₀ gueScalarA x z) m l‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [norm_mul, mul_pow]
    _ ≤ ‖(N : ℂ)⁻¹‖ ^ 2 * (2 * (gueScale N) ^ 2 *
          (∑ a : Fin N, ∑ b : Fin N,
            ‖(guePencilResolvent gueScalarA₀ gueScalarA x z *
              guePencilResolvent gueScalarA₀ gueScalarA x z) ((), a) ((), b)‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hcontr (sq_nonneg _)
    _ ≤ ‖(N : ℂ)⁻¹‖ ^ 2 * (2 * (gueScale N) ^ 2 * ((N : ℝ) * ((z.im)⁻¹) ^ 4)) := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        exact mul_le_mul_of_nonneg_left hFrob (mul_nonneg (by norm_num) (sq_nonneg _))
    _ = 2 * ((N : ℝ)⁻¹) ^ 2 * ((z.im)⁻¹) ^ 4 := by
        rw [hnorm, gueScale_sq]
        have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
        field_simp

theorem variance_partialTrace_re_le_of_grad (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (hN : 0 < N) (u v : d) (C : ℝ)
    (hgrad : ∀ x : GUECoord ι N → ℝ,
      (∑ p : GUECoord ι N, ‖guePartialTraceDir A₀ A z u v p x‖ ^ 2) ≤ C) :
    variance (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        (guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v).re)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) ≤ C := by
  classical
  set μ := stdGaussian (EuclideanSpace ℝ (GUECoord ι N))
  set F : EuclideanSpace ℝ (GUECoord ι N) → ℝ := fun x =>
    (guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v).re with hFdef
  set D : GUECoord ι N → EuclideanSpace ℝ (GUECoord ι N) → ℝ := fun p x =>
    (guePartialTraceDir A₀ A z u v p (x : GUECoord ι N → ℝ)).re with hDdef
  have hz' : z.im ≠ 0 := ne_of_gt hz
  have hFcont : Continuous F := by
    rw [hFdef]
    exact Complex.continuous_re.comp (continuous_guePartialTrace_entry A₀ A hA₀ hA z hz' u v)
  have hFmem : MemLp F 2 μ := by
    refine MemLp.of_bound hFcont.aestronglyMeasurable ((z.im)⁻¹) ?_
    filter_upwards with x
    calc ‖F x‖ = |(guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v).re| := rfl
      _ ≤ ‖guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v‖ := Complex.abs_re_le_norm _
      _ ≤ |z.im|⁻¹ := norm_guePartialTrace_entry_le A₀ A hA₀ hA _ z hz' hN u v
      _ = (z.im)⁻¹ := by rw [abs_of_pos hz]
  have hDcont : ∀ p : GUECoord ι N, Continuous (D p) := by
    intro p
    rw [hDdef]
    exact Complex.continuous_re.comp
      (continuous_guePartialTraceDir_entry A₀ A hA₀ hA z hz' u v p)
  have hDmem : ∀ p : GUECoord ι N, MemLp (D p) 2 μ := by
    intro p
    refine MemLp.of_bound (hDcont p).aestronglyMeasurable
      ((z.im)⁻¹ ^ 2 * ‖guePencilDirection A p‖) ?_
    filter_upwards with x
    calc ‖D p x‖ = |(guePartialTraceDir A₀ A z u v p (x : GUECoord ι N → ℝ)).re| := rfl
      _ ≤ ‖guePartialTraceDir A₀ A z u v p (x : GUECoord ι N → ℝ)‖ :=
          Complex.abs_re_le_norm _
      _ ≤ |z.im|⁻¹ ^ 2 * ‖guePencilDirection A p‖ :=
          norm_guePartialTraceDir_le A₀ A hA₀ hA _ z hz' hN u v p
      _ = (z.im)⁻¹ ^ 2 * ‖guePencilDirection A p‖ := by rw [abs_of_pos hz]
  have hderiv : ∀ p : GUECoord ι N, ∀ᵐ x ∂μ, ∀ t : ℝ,
      HasDerivAt (fun u : ℝ => F (WithLp.toLp 2 (Function.update (WithLp.ofLp x) p u)))
        (D p (WithLp.toLp 2 (Function.update (WithLp.ofLp x) p t))) t := by
    intro p
    filter_upwards with x t
    have h := hasDerivAt_guePartialTrace_entry_update A₀ A hA₀ hA
      (WithLp.ofLp x) p z hz' t u v
    have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h
    have hfun : (fun s : ℝ => F (WithLp.toLp 2 (Function.update (WithLp.ofLp x) p s)))
        = fun s : ℝ =>
            (guePartialTrace A₀ A z (Function.update (WithLp.ofLp x) p s) u v).re := by
      funext s
      simp [F]
    have hDval : D p (WithLp.toLp 2 (Function.update (WithLp.ofLp x) p t))
        = (guePartialTraceDir A₀ A z u v p (Function.update (WithLp.ofLp x) p t)).re := by
      simp [D, hDdef]
    rw [hfun, hDval]
    exact hre
  have hpoly : ∀ p : GUECoord ι N, ∀ᵐ x ∂μ,
      PolyGrowth (fun u : ℝ => F (WithLp.toLp 2 (Function.update (WithLp.ofLp x) p u))) ∧
        PolyGrowth (fun u : ℝ => D p (WithLp.toLp 2 (Function.update (WithLp.ofLp x) p u))) := by
    intro p
    filter_upwards with x
    constructor
    · apply polyGrowth_of_bound (C := (z.im)⁻¹)
      intro t
      calc |F (WithLp.toLp 2 (Function.update (WithLp.ofLp x) p t))|
          ≤ ‖guePartialTrace A₀ A z
              (Function.update (WithLp.ofLp x) p t) u v‖ := by
            simp only [F]
            exact Complex.abs_re_le_norm _
        _ ≤ |z.im|⁻¹ := norm_guePartialTrace_entry_le A₀ A hA₀ hA _ z hz' hN u v
        _ = (z.im)⁻¹ := by rw [abs_of_pos hz]
    · apply polyGrowth_of_bound (C := (z.im)⁻¹ ^ 2 * ‖guePencilDirection A p‖)
      intro t
      calc |D p (WithLp.toLp 2 (Function.update (WithLp.ofLp x) p t))|
          ≤ ‖guePartialTraceDir A₀ A z u v p
              (Function.update (WithLp.ofLp x) p t)‖ := by
            simp only [D]
            exact Complex.abs_re_le_norm _
        _ ≤ |z.im|⁻¹ ^ 2 * ‖guePencilDirection A p‖ :=
            norm_guePartialTraceDir_le A₀ A hA₀ hA _ z hz' hN u v p
        _ = (z.im)⁻¹ ^ 2 * ‖guePencilDirection A p‖ := by rw [abs_of_pos hz]
  have hpoincare := gaussian_poincare_stdGaussian (F := F) (D := D)
    hFmem hDmem hderiv hpoly
  refine hpoincare.trans ?_
  have hcontr : ∀ x : EuclideanSpace ℝ (GUECoord ι N), ∑ p : GUECoord ι N, (D p x) ^ 2 ≤ C := by
    intro x
    refine (Finset.sum_le_sum fun p _ => ?_).trans (hgrad (x : GUECoord ι N → ℝ))
    have h := Complex.abs_re_le_norm (guePartialTraceDir A₀ A z u v p (x : GUECoord ι N → ℝ))
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    simpa [D, hDdef, sq_abs] using h2
  have hle : (∑ p : GUECoord ι N, ∫ x, (D p x) ^ 2 ∂μ) ≤ C := by
    rw [← integral_finsetSum]
    · calc ∫ x, ∑ p : GUECoord ι N, (D p x) ^ 2 ∂μ
          ≤ ∫ _x, C ∂μ :=
            integral_mono (integrable_finsetSum _ fun p _ => (hDmem p).integrable_sq)
              (integrable_const C) (fun x => hcontr x)
        _ = C := by
            rw [integral_const]
            simp [μ]
    · intro p _
      exact (hDmem p).integrable_sq
  simpa using hle

/-- **Variance bound for the imaginary part of a partial-trace entry.**  For `0 < im z`,

`Var(Im T_N(z)_{uv}) ≤ 2 * gueScale(N)^2 * (∑ i, frob(A_i)^2) * (im z)⁻⁴`.

Since `gueScale(N)^2 = 1/N`, the right-hand side is `O(1/N)`; no concentration or comparison
with the limit Dyson equation is assumed. -/
theorem variance_partialTrace_im_le_of_grad (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (hN : 0 < N) (u v : d) (C : ℝ)
    (hgrad : ∀ x : GUECoord ι N → ℝ,
      (∑ p : GUECoord ι N, ‖guePartialTraceDir A₀ A z u v p x‖ ^ 2) ≤ C) :
    variance (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        (guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v).im)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) ≤ C := by
  classical
  set μ := stdGaussian (EuclideanSpace ℝ (GUECoord ι N))
  set F : EuclideanSpace ℝ (GUECoord ι N) → ℝ := fun x =>
    (guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v).im with hFdef
  set D : GUECoord ι N → EuclideanSpace ℝ (GUECoord ι N) → ℝ := fun p x =>
    (guePartialTraceDir A₀ A z u v p (x : GUECoord ι N → ℝ)).im with hDdef
  have hz' : z.im ≠ 0 := ne_of_gt hz
  have hFcont : Continuous F := by
    rw [hFdef]
    exact Complex.continuous_im.comp (continuous_guePartialTrace_entry A₀ A hA₀ hA z hz' u v)
  have hFmem : MemLp F 2 μ := by
    refine MemLp.of_bound hFcont.aestronglyMeasurable ((z.im)⁻¹) ?_
    filter_upwards with x
    calc ‖F x‖ = |(guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v).im| := rfl
      _ ≤ ‖guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v‖ := Complex.abs_im_le_norm _
      _ ≤ |z.im|⁻¹ := norm_guePartialTrace_entry_le A₀ A hA₀ hA _ z hz' hN u v
      _ = (z.im)⁻¹ := by rw [abs_of_pos hz]
  have hDcont : ∀ p : GUECoord ι N, Continuous (D p) := by
    intro p
    rw [hDdef]
    exact Complex.continuous_im.comp
      (continuous_guePartialTraceDir_entry A₀ A hA₀ hA z hz' u v p)
  have hDmem : ∀ p : GUECoord ι N, MemLp (D p) 2 μ := by
    intro p
    refine MemLp.of_bound (hDcont p).aestronglyMeasurable
      ((z.im)⁻¹ ^ 2 * ‖guePencilDirection A p‖) ?_
    filter_upwards with x
    calc ‖D p x‖ = |(guePartialTraceDir A₀ A z u v p (x : GUECoord ι N → ℝ)).im| := rfl
      _ ≤ ‖guePartialTraceDir A₀ A z u v p (x : GUECoord ι N → ℝ)‖ :=
          Complex.abs_im_le_norm _
      _ ≤ |z.im|⁻¹ ^ 2 * ‖guePencilDirection A p‖ :=
          norm_guePartialTraceDir_le A₀ A hA₀ hA _ z hz' hN u v p
      _ = (z.im)⁻¹ ^ 2 * ‖guePencilDirection A p‖ := by rw [abs_of_pos hz]
  have hderiv : ∀ p : GUECoord ι N, ∀ᵐ x ∂μ, ∀ t : ℝ,
      HasDerivAt (fun u : ℝ => F (WithLp.toLp 2 (Function.update (WithLp.ofLp x) p u)))
        (D p (WithLp.toLp 2 (Function.update (WithLp.ofLp x) p t))) t := by
    intro p
    filter_upwards with x t
    have h := hasDerivAt_guePartialTrace_entry_update A₀ A hA₀ hA
      (WithLp.ofLp x) p z hz' t u v
    have hre := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t h
    have hfun : (fun s : ℝ => F (WithLp.toLp 2 (Function.update (WithLp.ofLp x) p s)))
        = fun s : ℝ =>
            (guePartialTrace A₀ A z (Function.update (WithLp.ofLp x) p s) u v).im := by
      funext s
      simp [F, hFdef]
    have hDval : D p (WithLp.toLp 2 (Function.update (WithLp.ofLp x) p t))
        = (guePartialTraceDir A₀ A z u v p (Function.update (WithLp.ofLp x) p t)).im := by
      simp [D, hDdef]
    rw [hfun, hDval]
    exact hre
  have hpoly : ∀ p : GUECoord ι N, ∀ᵐ x ∂μ,
      PolyGrowth (fun u : ℝ => F (WithLp.toLp 2 (Function.update (WithLp.ofLp x) p u))) ∧
        PolyGrowth (fun u : ℝ => D p (WithLp.toLp 2 (Function.update (WithLp.ofLp x) p u))) := by
    intro p
    filter_upwards with x
    constructor
    · apply polyGrowth_of_bound (C := (z.im)⁻¹)
      intro t
      calc |F (WithLp.toLp 2 (Function.update (WithLp.ofLp x) p t))|
          ≤ ‖guePartialTrace A₀ A z
              (Function.update (WithLp.ofLp x) p t) u v‖ := by
            simp only [F]
            exact Complex.abs_im_le_norm _
        _ ≤ |z.im|⁻¹ := norm_guePartialTrace_entry_le A₀ A hA₀ hA _ z hz' hN u v
        _ = (z.im)⁻¹ := by rw [abs_of_pos hz]
    · apply polyGrowth_of_bound (C := (z.im)⁻¹ ^ 2 * ‖guePencilDirection A p‖)
      intro t
      calc |D p (WithLp.toLp 2 (Function.update (WithLp.ofLp x) p t))|
          ≤ ‖guePartialTraceDir A₀ A z u v p
              (Function.update (WithLp.ofLp x) p t)‖ := by
            simp only [D]
            exact Complex.abs_im_le_norm _
        _ ≤ |z.im|⁻¹ ^ 2 * ‖guePencilDirection A p‖ :=
            norm_guePartialTraceDir_le A₀ A hA₀ hA _ z hz' hN u v p
        _ = (z.im)⁻¹ ^ 2 * ‖guePencilDirection A p‖ := by rw [abs_of_pos hz]
  have hpoincare := gaussian_poincare_stdGaussian (F := F) (D := D)
    hFmem hDmem hderiv hpoly
  refine hpoincare.trans ?_
  have hcontr : ∀ x : EuclideanSpace ℝ (GUECoord ι N), ∑ p : GUECoord ι N, (D p x) ^ 2 ≤ C := by
    intro x
    refine (Finset.sum_le_sum fun p _ => ?_).trans (hgrad (x : GUECoord ι N → ℝ))
    have h := Complex.abs_im_le_norm (guePartialTraceDir A₀ A z u v p (x : GUECoord ι N → ℝ))
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    simpa [D, hDdef, sq_abs] using h2
  have hle : (∑ p : GUECoord ι N, ∫ x, (D p x) ^ 2 ∂μ) ≤ C := by
    rw [← integral_finsetSum]
    · calc ∫ x, ∑ p : GUECoord ι N, (D p x) ^ 2 ∂μ
          ≤ ∫ _x, C ∂μ :=
            integral_mono (integrable_finsetSum _ fun p _ => (hDmem p).integrable_sq)
              (integrable_const C) (fun x => hcontr x)
        _ = C := by
            rw [integral_const]
            simp [μ]
    · intro p _
      exact (hDmem p).integrable_sq
  simpa using hle


/-! ### The complex `L²` fluctuation of a partial-trace entry -/

/-- **Sharp two-point bound for the scalar single GUE (real part).** -/
theorem variance_scalar_re_le (z : ℂ) (hz : 0 < z.im) (hN : 0 < N) :
    variance (fun x : EuclideanSpace ℝ (GUECoord Unit N) =>
        (guePartialTrace gueScalarA₀ gueScalarA z (x : GUECoord Unit N → ℝ) () ()).re)
      (stdGaussian (EuclideanSpace ℝ (GUECoord Unit N)))
      ≤ 2 * ((N : ℝ)⁻¹) ^ 2 * ((z.im)⁻¹) ^ 4 :=
  variance_partialTrace_re_le_of_grad gueScalarA₀ gueScalarA isHermitian_zero
    (fun _ => isHermitian_one) z hz hN () () _
    (fun x => sum_sq_guePartialTraceDir_scalar_le x z hz hN)

/-- **Sharp two-point bound for the scalar single GUE (imaginary part).** -/
theorem variance_scalar_im_le (z : ℂ) (hz : 0 < z.im) (hN : 0 < N) :
    variance (fun x : EuclideanSpace ℝ (GUECoord Unit N) =>
        (guePartialTrace gueScalarA₀ gueScalarA z (x : GUECoord Unit N → ℝ) () ()).im)
      (stdGaussian (EuclideanSpace ℝ (GUECoord Unit N)))
      ≤ 2 * ((N : ℝ)⁻¹) ^ 2 * ((z.im)⁻¹) ^ 4 :=
  variance_partialTrace_im_le_of_grad gueScalarA₀ gueScalarA isHermitian_zero
    (fun _ => isHermitian_one) z hz hN () () _
    (fun x => sum_sq_guePartialTraceDir_scalar_le x z hz hN)

lemma integral_norm_sq_fluctuation_le_of_var (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (hN : 0 < N) (u v : d) (C : ℝ)
    (hvarre : variance (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        (guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v).re)
        (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) ≤ C)
    (hvarim : variance (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        (guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v).im)
        (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) ≤ C) :
    ∫ x, ‖guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v -
        gueResolventMean (N := N) A₀ A z u v‖ ^ 2
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) ≤ 2 * C := by
  classical
  set μ := stdGaussian (EuclideanSpace ℝ (GUECoord ι N))
  set T : EuclideanSpace ℝ (GUECoord ι N) → ℂ := fun x =>
    guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v with hT
  set m : ℂ := gueResolventMean (N := N) A₀ A z u v with hm
  have hz' : z.im ≠ 0 := ne_of_gt hz
  have hTcont : Continuous T := by
    rw [hT]
    exact continuous_guePartialTrace_entry A₀ A hA₀ hA z hz' u v
  have hTint : Integrable T μ := by
    rw [hT]
    exact integrable_guePartialTrace_entry A₀ A hA₀ hA z hz hN u v
  have hre : m.re = ∫ x, (T x).re ∂μ := by
    rw [hm, hT]
    exact integral_re_guePartialTrace_entry A₀ A hA₀ hA z hz hN u v
  have him : m.im = ∫ x, (T x).im ∂μ := by
    rw [hm, hT]
    exact integral_im_guePartialTrace_entry A₀ A hA₀ hA z hz hN u v
  have hm_bound : ‖m‖ ≤ (z.im)⁻¹ := by
    rw [hm]
    exact norm_gueResolventMean_entry_le A₀ A hA₀ hA z hz hN u v
  have hT_bound : ∀ x, ‖T x‖ ≤ (z.im)⁻¹ := by
    intro x
    rw [hT]
    calc ‖guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v‖ ≤ |z.im|⁻¹ :=
          norm_guePartialTrace_entry_le A₀ A hA₀ hA _ z hz' hN u v
      _ = (z.im)⁻¹ := by rw [abs_of_pos hz]
  -- integrability of the two squared fluctuation pieces
  have hcont_re : Continuous (fun x => (T x).re - m.re) :=
    (Complex.continuous_re.comp hTcont).sub continuous_const
  have hcont_im : Continuous (fun x => (T x).im - m.im) :=
    (Complex.continuous_im.comp hTcont).sub continuous_const
  have hbound_re : ∀ x, ‖((T x).re - m.re) ^ 2‖ ≤ (2 * (z.im)⁻¹) ^ 2 := by
    intro x
    have h1 : |(T x).re - m.re| ≤ ‖T x‖ + ‖m‖ := by
      calc |(T x).re - m.re| = |(T x - m).re| := by simp
        _ ≤ ‖T x - m‖ := Complex.abs_re_le_norm _
        _ ≤ ‖T x‖ + ‖m‖ := norm_sub_le _ _
    have h2 : |(T x).re - m.re| ≤ 2 * (z.im)⁻¹ := by
      linarith [hT_bound x, hm_bound]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hh := pow_le_pow_left₀ (abs_nonneg ((T x).re - m.re)) h2 2
    rwa [sq_abs] at hh
  have hbound_im : ∀ x, ‖((T x).im - m.im) ^ 2‖ ≤ (2 * (z.im)⁻¹) ^ 2 := by
    intro x
    have h1 : |(T x).im - m.im| ≤ ‖T x‖ + ‖m‖ := by
      calc |(T x).im - m.im| = |(T x - m).im| := by simp
        _ ≤ ‖T x - m‖ := Complex.abs_im_le_norm _
        _ ≤ ‖T x‖ + ‖m‖ := norm_sub_le _ _
    have h2 : |(T x).im - m.im| ≤ 2 * (z.im)⁻¹ := by
      linarith [hT_bound x, hm_bound]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hh := pow_le_pow_left₀ (abs_nonneg ((T x).im - m.im)) h2 2
    rwa [sq_abs] at hh
  have hint_re : Integrable (fun x => ((T x).re - m.re) ^ 2) μ :=
    Integrable.of_bound (hcont_re.pow 2).aestronglyMeasurable ((2 * (z.im)⁻¹) ^ 2)
      (ae_of_all _ hbound_re)
  have hint_im : Integrable (fun x => ((T x).im - m.im) ^ 2) μ :=
    Integrable.of_bound (hcont_im.pow 2).aestronglyMeasurable ((2 * (z.im)⁻¹) ^ 2)
      (ae_of_all _ hbound_im)
  have hvar_re : (∫ x, ((T x).re - m.re) ^ 2 ∂μ) = variance (fun x => (T x).re) μ := by
    rw [variance_eq_integral (X := fun x => (T x).re) (μ := μ)
      (Complex.continuous_re.comp hTcont).aemeasurable]
    rw [← hre]
  have hvar_im : (∫ x, ((T x).im - m.im) ^ 2 ∂μ) = variance (fun x => (T x).im) μ := by
    rw [variance_eq_integral (X := fun x => (T x).im) (μ := μ)
      (Complex.continuous_im.comp hTcont).aemeasurable]
    rw [← him]
  calc ∫ x, ‖T x - m‖ ^ 2 ∂μ
      = ∫ x, ((T x - m).re ^ 2 + (T x - m).im ^ 2) ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        show ‖T x - m‖ ^ 2 = (T x - m).re ^ 2 + (T x - m).im ^ 2
        rw [Complex.sq_norm, Complex.normSq_apply]
        ring
    _ = ∫ x, (((T x).re - m.re) ^ 2 + ((T x).im - m.im) ^ 2) ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        show (T x - m).re ^ 2 + (T x - m).im ^ 2 =
          ((T x).re - m.re) ^ 2 + ((T x).im - m.im) ^ 2
        simp
    _ = ∫ x, ((T x).re - m.re) ^ 2 ∂μ + ∫ x, ((T x).im - m.im) ^ 2 ∂μ := by
        rw [integral_add hint_re hint_im]
    _ = variance (fun x => (T x).re) μ + variance (fun x => (T x).im) μ := by
        rw [hvar_re, hvar_im]
    _ ≤ C + C := by
        refine add_le_add ?_ ?_
        · simpa [hT, hre] using hvarre
        · simpa [hT, him] using hvarim
    _ = 2 * C := by ring

/-- **Sharp two-point correlation for the scalar single GUE.**  The complex `L²` fluctuation of
`T_N(z) = tr_N (z - G)⁻¹` is `O(N⁻²)` with the explicit constant `4 N⁻² (im z)⁻⁴`. -/
theorem integral_norm_sq_fluctuation_scalar_le (z : ℂ) (hz : 0 < z.im) (hN : 0 < N) :
    ∫ x, ‖guePartialTrace gueScalarA₀ gueScalarA z (x : GUECoord Unit N → ℝ) () () -
        gueResolventMean (N := N) gueScalarA₀ gueScalarA z () ()‖ ^ 2
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord Unit N)))
      ≤ 4 * ((N : ℝ)⁻¹) ^ 2 * ((z.im)⁻¹) ^ 4 := by
  have h := integral_norm_sq_fluctuation_le_of_var gueScalarA₀ gueScalarA isHermitian_zero
    (fun _ => isHermitian_one) z hz hN () () (2 * ((N : ℝ)⁻¹) ^ 2 * ((z.im)⁻¹) ^ 4)
    (variance_scalar_re_le z hz hN) (variance_scalar_im_le z hz hN)
  calc ∫ x, ‖guePartialTrace gueScalarA₀ gueScalarA z (x : GUECoord Unit N → ℝ) () () -
        gueResolventMean (N := N) gueScalarA₀ gueScalarA z () ()‖ ^ 2
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord Unit N)))
      ≤ 2 * (2 * ((N : ℝ)⁻¹) ^ 2 * ((z.im)⁻¹) ^ 4) := h
    _ = 4 * ((N : ℝ)⁻¹) ^ 2 * ((z.im)⁻¹) ^ 4 := by ring

/-! ### The general GUE pencil: trace contraction for the sharp gradient bound -/

lemma sum_fin_pair_delta_fst {M : Type*} [AddCommMonoid M] (f : Fin N → Fin N → M)
    (a b : Fin N) :
    (∑ y : Fin N, ∑ y2 : Fin N, (if (a, b) = (y, y2) then f y y2 else 0)) = f a b := by
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro y2 _ hy2
      have h : ¬ ((a, b) = (a, y2)) := by
        intro hh
        exact hy2 (Prod.ext_iff.mp hh).2.symm
      simp [h]
    · intro h; simp at h
  · intro y _ hy
    refine Finset.sum_eq_zero fun y2 _ => ?_
    have h : ¬ ((a, b) = (y, y2)) := by
      intro hh
      exact hy (Prod.ext_iff.mp hh).1.symm
    simp [h]
  · intro h; simp at h

lemma sum_fin_pair_delta_snd {M : Type*} [AddCommMonoid M] (f : Fin N → Fin N → M)
    (a b : Fin N) :
    (∑ y : Fin N, ∑ y2 : Fin N, (if (a, b) = (y2, y) then f y y2 else 0)) = f b a := by
  rw [Finset.sum_comm]
  have := sum_fin_pair_delta_fst (fun y y2 => f y2 y) a b
  simpa using this

lemma sum_four_reorder {M : Type*} [AddCommMonoid M] (F : d → Fin N → d → Fin N → M) :
    (∑ x : d, ∑ y : Fin N, ∑ x2 : d, ∑ y2 : Fin N, F x y x2 y2)
      = ∑ x : d, ∑ x2 : d, ∑ y : Fin N, ∑ y2 : Fin N, F x y x2 y2 := by
  refine Finset.sum_congr rfl fun x _ => ?_
  exact Finset.sum_comm

lemma sum_four_add {M : Type*} [AddCommMonoid M]
    (F G : d → Fin N → d → Fin N → M) :
    (∑ x : d, ∑ y : Fin N, ∑ x2 : d, ∑ y2 : Fin N, (F x y x2 y2 + G x y x2 y2))
      = (∑ x : d, ∑ y : Fin N, ∑ x2 : d, ∑ y2 : Fin N, F x y x2 y2)
        + (∑ x : d, ∑ y : Fin N, ∑ x2 : d, ∑ y2 : Fin N, G x y x2 y2) := by
  simp only [Finset.sum_add_distrib]

/-- Trace pairing against a pencil direction, in slice form. -/
lemma guePencil_trace_direction (A : ι → Matrix d d ℂ)
    (X : CStarMatrix (d × Fin N) (d × Fin N) ℂ) (p : GUECoord ι N) :
    (∑ k : d × Fin N, ∑ l : d × Fin N, guePencilDirection A p k l * X l k)
      = (gueScale N : ℂ) * ∑ x : d, ∑ x2 : d,
          (A p.1 x x2 : ℂ) * (gueAlpha * X (x2, p.2.2) (x, p.2.1)
            + gueBeta * X (x2, p.2.1) (x, p.2.2)) := by
  have hsplit : (∑ k : d × Fin N, ∑ l : d × Fin N, guePencilDirection A p k l * X l k)
      = ∑ x : d, ∑ y : Fin N, ∑ x2 : d, ∑ y2 : Fin N,
          guePencilDirection A p (x, y) (x2, y2) * X (x2, y2) (x, y) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Fintype.sum_prod_type]
  rw [hsplit]
  have hpt : ∀ x y x2 y2,
      guePencilDirection A p (x, y) (x2, y2) * X (x2, y2) (x, y)
        = (gueScale N : ℂ) * gueAlpha *
            (if p.2 = (y, y2) then (A p.1 x x2 : ℂ) * X (x2, y2) (x, y) else 0)
          + (gueScale N : ℂ) * gueBeta *
            (if p.2 = (y2, y) then (A p.1 x x2 : ℂ) * X (x2, y2) (x, y) else 0) := by
    intro x y x2 y2
    rw [guePencilDirection_apply]
    split_ifs <;> ring
  have hA : (∑ x : d, ∑ y : Fin N, ∑ x2 : d, ∑ y2 : Fin N,
        (gueScale N : ℂ) * gueAlpha *
          (if p.2 = (y, y2) then (A p.1 x x2 : ℂ) * X (x2, y2) (x, y) else 0))
      = (gueScale N : ℂ) * gueAlpha * ∑ x : d, ∑ x2 : d,
          (A p.1 x x2 : ℂ) * X (x2, p.2.2) (x, p.2.1) := by
    rw [sum_four_reorder]
    rw [show (∑ x : d, ∑ x2 : d, ∑ y : Fin N, ∑ y2 : Fin N,
          (gueScale N : ℂ) * gueAlpha *
            (if p.2 = (y, y2) then (A p.1 x x2 : ℂ) * X (x2, y2) (x, y) else 0))
        = (gueScale N : ℂ) * gueAlpha * ∑ x : d, ∑ x2 : d, ∑ y : Fin N, ∑ y2 : Fin N,
            (if p.2 = (y, y2) then (A p.1 x x2 : ℂ) * X (x2, y2) (x, y) else 0) from by
      simp only [Finset.mul_sum]]
    congr 1
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x2 _ => ?_
    exact sum_fin_pair_delta_fst
      (fun y y2 => (A p.1 x x2 : ℂ) * X (x2, y2) (x, y)) p.2.1 p.2.2
  have hB : (∑ x : d, ∑ y : Fin N, ∑ x2 : d, ∑ y2 : Fin N,
        (gueScale N : ℂ) * gueBeta *
          (if p.2 = (y2, y) then (A p.1 x x2 : ℂ) * X (x2, y2) (x, y) else 0))
      = (gueScale N : ℂ) * gueBeta * ∑ x : d, ∑ x2 : d,
          (A p.1 x x2 : ℂ) * X (x2, p.2.1) (x, p.2.2) := by
    rw [sum_four_reorder]
    rw [show (∑ x : d, ∑ x2 : d, ∑ y : Fin N, ∑ y2 : Fin N,
          (gueScale N : ℂ) * gueBeta *
            (if p.2 = (y2, y) then (A p.1 x x2 : ℂ) * X (x2, y2) (x, y) else 0))
        = (gueScale N : ℂ) * gueBeta * ∑ x : d, ∑ x2 : d, ∑ y : Fin N, ∑ y2 : Fin N,
            (if p.2 = (y2, y) then (A p.1 x x2 : ℂ) * X (x2, y2) (x, y) else 0) from by
      simp only [Finset.mul_sum]]
    congr 1
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x2 _ => ?_
    exact sum_fin_pair_delta_snd
      (fun y y2 => (A p.1 x x2 : ℂ) * X (x2, y2) (x, y)) p.2.1 p.2.2
  calc (∑ x : d, ∑ y : Fin N, ∑ x2 : d, ∑ y2 : Fin N,
        guePencilDirection A p (x, y) (x2, y2) * X (x2, y2) (x, y))
      = ∑ x : d, ∑ y : Fin N, ∑ x2 : d, ∑ y2 : Fin N,
          ((gueScale N : ℂ) * gueAlpha *
              (if p.2 = (y, y2) then (A p.1 x x2 : ℂ) * X (x2, y2) (x, y) else 0)
            + (gueScale N : ℂ) * gueBeta *
              (if p.2 = (y2, y) then (A p.1 x x2 : ℂ) * X (x2, y2) (x, y) else 0)) := by
        exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
          Finset.sum_congr rfl fun x2 _ => Finset.sum_congr rfl fun y2 _ => hpt x y x2 y2

    _ = (gueScale N : ℂ) * gueAlpha * (∑ x : d, ∑ x2 : d,
          (A p.1 x x2 : ℂ) * X (x2, p.2.2) (x, p.2.1))
        + (gueScale N : ℂ) * gueBeta * (∑ x : d, ∑ x2 : d,
          (A p.1 x x2 : ℂ) * X (x2, p.2.1) (x, p.2.2)) := by
        rw [sum_four_add
          (F := fun x y x2 y2 => (gueScale N : ℂ) * gueAlpha *
            (if p.2 = (y, y2) then (A p.1 x x2 : ℂ) * X (x2, y2) (x, y) else 0))
          (G := fun x y x2 y2 => (gueScale N : ℂ) * gueBeta *
            (if p.2 = (y2, y) then (A p.1 x x2 : ℂ) * X (x2, y2) (x, y) else 0))]
        rw [hA, hB]
    _ = (gueScale N : ℂ) * ∑ x : d, ∑ x2 : d,
          (A p.1 x x2 : ℂ) * (gueAlpha * X (x2, p.2.2) (x, p.2.1)
            + gueBeta * X (x2, p.2.1) (x, p.2.2)) := by
        have hlin : (∑ x : d, ∑ x2 : d, (A p.1 x x2 : ℂ) *
              (gueAlpha * X (x2, p.2.2) (x, p.2.1)
                + gueBeta * X (x2, p.2.1) (x, p.2.2)))
            = gueAlpha * (∑ x : d, ∑ x2 : d,
                (A p.1 x x2 : ℂ) * X (x2, p.2.2) (x, p.2.1))
              + gueBeta * (∑ x : d, ∑ x2 : d,
                (A p.1 x x2 : ℂ) * X (x2, p.2.1) (x, p.2.2)) := by
          simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
          congr 1
          · refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x2 _ => ?_
            ring
          · refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x2 _ => ?_
            ring
        rw [hlin]
        ring

/-- Cauchy–Schwarz for a complex finite sum. -/
lemma norm_sum_mul_le_complex {α : Type*} [Fintype α] (f g : α → ℂ) :
    ‖∑ k, f k * g k‖ ≤ Real.sqrt (∑ k, ‖f k‖ ^ 2) * Real.sqrt (∑ k, ‖g k‖ ^ 2) := by
  have h1 : ‖∑ k, f k * g k‖ ≤ ∑ k, ‖f k‖ * ‖g k‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul]
  have h2 : (∑ k, ‖f k‖ * ‖g k‖) ^ 2 ≤ (∑ k, ‖f k‖ ^ 2) * (∑ k, ‖g k‖ ^ 2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖f k‖) (fun k => ‖g k‖)
    simpa using h
  have h3 : ∑ k, ‖f k‖ * ‖g k‖ ≤ Real.sqrt ((∑ k, ‖f k‖ ^ 2) * (∑ k, ‖g k‖ ^ 2)) :=
    Real.le_sqrt_of_sq_le h2
  have h4 : Real.sqrt ((∑ k, ‖f k‖ ^ 2) * (∑ k, ‖g k‖ ^ 2))
      = Real.sqrt (∑ k, ‖f k‖ ^ 2) * Real.sqrt (∑ k, ‖g k‖ ^ 2) :=
    Real.sqrt_mul (Finset.sum_nonneg fun k _ => sq_nonneg _) _
  exact h1.trans (h3.trans (le_of_eq h4))

/-- Cauchy–Schwarz against a matrix, in Frobenius form. -/
lemma norm_sum_sum_mul_le_frob (A : Matrix d d ℂ) (M : d → d → ℂ) :
    ‖∑ x : d, ∑ x2 : d, (A x x2 : ℂ) * M x x2‖
      ≤ frob A * Real.sqrt (∑ x : d, ∑ x2 : d, ‖M x x2‖ ^ 2) := by
  have hEq : (∑ x : d, ∑ x2 : d, (A x x2 : ℂ) * M x x2)
      = ∑ q : d × d, (A q.1 q.2 : ℂ) * M q.1 q.2 := by
    rw [Fintype.sum_prod_type]
  have hEq2 : (∑ x : d, ∑ x2 : d, ‖M x x2‖ ^ 2)
      = ∑ q : d × d, ‖M q.1 q.2‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
  rw [hEq, hEq2]
  have h := norm_sum_mul_le_complex (fun q : d × d => (A q.1 q.2 : ℂ))
    (fun q : d × d => M q.1 q.2)
  have h1 : (∑ q : d × d, ‖(A q.1 q.2 : ℂ)‖ ^ 2) = (frob A) ^ 2 := by
    rw [frob_sq, Fintype.sum_prod_type]
  rw [h1, Real.sqrt_sq (frob_nonneg A)] at h
  exact h

/-- Reindexing a sum over the Gaussian coordinates of a general pencil. -/
lemma sum_gueCoord_eq' {M : Type*} [AddCommMonoid M] (f : GUECoord ι N → M) :
    (∑ p : GUECoord ι N, f p) = ∑ i : ι, ∑ a : Fin N, ∑ b : Fin N, f (i, (a, b)) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]

/-- Four-fold sum reindexing for the trace contraction. -/
lemma sum_four_trace_reindex (g : (d × Fin N) → (d × Fin N) → ℝ) :
    (∑ a : Fin N, ∑ b : Fin N, ∑ x : d, ∑ x2 : d, g (x2, b) (x, a))
      = ∑ k : d × Fin N, ∑ l : d × Fin N, g l k := by
  have hR : (∑ k : d × Fin N, ∑ l : d × Fin N, g l k)
      = ∑ x : d, ∑ a : Fin N, ∑ x2 : d, ∑ b : Fin N, g (x2, b) (x, a) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type]
  have hL : (∑ a : Fin N, ∑ b : Fin N, ∑ x : d, ∑ x2 : d, g (x2, b) (x, a))
      = ∑ x : d, ∑ a : Fin N, ∑ x2 : d, ∑ b : Fin N, g (x2, b) (x, a) := by
    rw [show (∑ a : Fin N, ∑ b : Fin N, ∑ x : d, ∑ x2 : d, g (x2, b) (x, a))
        = ∑ a : Fin N, ∑ x : d, ∑ b : Fin N, ∑ x2 : d, g (x2, b) (x, a) from by
      refine Finset.sum_congr rfl fun a _ => ?_
      exact Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun a _ => ?_
    exact Finset.sum_comm
  rw [hL, hR]

/-- **Pencil trace contraction.**  The squared trace pairing against the pencil directions,
summed over all Gaussian coordinates, is bounded by the Frobenius square of the test matrix,
weighted by the coefficient Frobenius norms. -/
lemma guePencil_trace_contraction (A : ι → Matrix d d ℂ)
    (X : CStarMatrix (d × Fin N) (d × Fin N) ℂ) :
    (∑ p : GUECoord ι N, ‖∑ k : d × Fin N, ∑ l : d × Fin N,
        guePencilDirection A p k l * X l k‖ ^ 2)
      ≤ 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2)
          * (∑ k : d × Fin N, ∑ l : d × Fin N, ‖X l k‖ ^ 2) := by
  have hstep : ∀ (i : ι) (a b : Fin N),
      ‖∑ k : d × Fin N, ∑ l : d × Fin N,
          guePencilDirection A (i, (a, b)) k l * X l k‖ ^ 2
        ≤ (gueScale N) ^ 2 * (frob (A i)) ^ 2 *
            ((∑ x : d, ∑ x2 : d, ‖X (x2, b) (x, a)‖ ^ 2)
              + (∑ x : d, ∑ x2 : d, ‖X (x2, a) (x, b)‖ ^ 2)) := by
    intro i a b
    rw [guePencil_trace_direction A X (i, (a, b))]
    set U : ℂ := ∑ x : d, ∑ x2 : d, (A i x x2 : ℂ) * X (x2, b) (x, a) with hUdef
    set V : ℂ := ∑ x : d, ∑ x2 : d, (A i x x2 : ℂ) * X (x2, a) (x, b) with hVdef
    set S1 : ℝ := ∑ x : d, ∑ x2 : d, ‖X (x2, b) (x, a)‖ ^ 2 with hS1def
    set S2 : ℝ := ∑ x : d, ∑ x2 : d, ‖X (x2, a) (x, b)‖ ^ 2 with hS2def
    have hlin : (∑ x : d, ∑ x2 : d, (A i x x2 : ℂ) *
          (gueAlpha * X (x2, b) (x, a) + gueBeta * X (x2, a) (x, b)))
        = (gueAlpha : ℂ) * U + (gueBeta : ℂ) * V := by
      simp only [hUdef, hVdef]
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x2 _ => ?_
        ring
      · refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x2 _ => ?_
        ring
    rw [hlin, norm_mul, mul_pow]
    have hS1nn : (0:ℝ) ≤ S1 := by
      rw [hS1def]; exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun x2 _ => sq_nonneg _
    have hS2nn : (0:ℝ) ≤ S2 := by
      rw [hS2def]; exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun x2 _ => sq_nonneg _
    have hU2 : ‖U‖ ^ 2 ≤ (frob (A i)) ^ 2 * S1 := by
      have h := norm_sum_sum_mul_le_frob (A i) (fun x x2 => X (x2, b) (x, a))
      have h' : ‖U‖ ≤ frob (A i) * Real.sqrt S1 := by rw [hUdef, hS1def]; exact h
      calc ‖U‖ ^ 2 ≤ (frob (A i) * Real.sqrt S1) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h' 2
        _ = (frob (A i)) ^ 2 * S1 := by rw [mul_pow, Real.sq_sqrt hS1nn]
    have hV2 : ‖V‖ ^ 2 ≤ (frob (A i)) ^ 2 * S2 := by
      have h := norm_sum_sum_mul_le_frob (A i) (fun x x2 => X (x2, a) (x, b))
      have h' : ‖V‖ ≤ frob (A i) * Real.sqrt S2 := by rw [hVdef, hS2def]; exact h
      calc ‖V‖ ^ 2 ≤ (frob (A i) * Real.sqrt S2) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h' 2
        _ = (frob (A i)) ^ 2 * S2 := by rw [mul_pow, Real.sq_sqrt hS2nn]
    have hcomb : ‖(gueAlpha : ℂ) * U + (gueBeta : ℂ) * V‖ ^ 2
        ≤ (frob (A i)) ^ 2 * (S1 + S2) := by
      calc ‖(gueAlpha : ℂ) * U + (gueBeta : ℂ) * V‖ ^ 2 ≤ ‖U‖ ^ 2 + ‖V‖ ^ 2 :=
            gueAlpha_beta_combination_norm_sq_le U V
        _ ≤ (frob (A i)) ^ 2 * S1 + (frob (A i)) ^ 2 * S2 := add_le_add hU2 hV2
        _ = (frob (A i)) ^ 2 * (S1 + S2) := by ring
    calc ‖(gueScale N : ℂ)‖ ^ 2 * ‖(gueAlpha : ℂ) * U + (gueBeta : ℂ) * V‖ ^ 2
        ≤ ‖(gueScale N : ℂ)‖ ^ 2 * ((frob (A i)) ^ 2 * (S1 + S2)) :=
          mul_le_mul_of_nonneg_left hcomb (by positivity)
      _ = (gueScale N) ^ 2 * (frob (A i)) ^ 2 * (S1 + S2) := by
          rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
          ring
  have hS : (∑ a : Fin N, ∑ b : Fin N,
        ((∑ x : d, ∑ x2 : d, ‖X (x2, b) (x, a)‖ ^ 2)
          + (∑ x : d, ∑ x2 : d, ‖X (x2, a) (x, b)‖ ^ 2)))
      = 2 * (∑ k : d × Fin N, ∑ l : d × Fin N, ‖X l k‖ ^ 2) := by
    have h1 : (∑ a : Fin N, ∑ b : Fin N, (∑ x : d, ∑ x2 : d, ‖X (x2, b) (x, a)‖ ^ 2))
        = ∑ k : d × Fin N, ∑ l : d × Fin N, ‖X l k‖ ^ 2 :=
      sum_four_trace_reindex (fun l k => ‖X l k‖ ^ 2)
    have h2 : (∑ a : Fin N, ∑ b : Fin N, (∑ x : d, ∑ x2 : d, ‖X (x2, a) (x, b)‖ ^ 2))
        = ∑ k : d × Fin N, ∑ l : d × Fin N, ‖X l k‖ ^ 2 := by
      rw [Finset.sum_comm]
      exact sum_four_trace_reindex (fun l k => ‖X l k‖ ^ 2)
    rw [show (∑ a : Fin N, ∑ b : Fin N,
          ((∑ x : d, ∑ x2 : d, ‖X (x2, b) (x, a)‖ ^ 2)
            + (∑ x : d, ∑ x2 : d, ‖X (x2, a) (x, b)‖ ^ 2)))
        = (∑ a : Fin N, ∑ b : Fin N, (∑ x : d, ∑ x2 : d, ‖X (x2, b) (x, a)‖ ^ 2))
          + (∑ a : Fin N, ∑ b : Fin N, (∑ x : d, ∑ x2 : d, ‖X (x2, a) (x, b)‖ ^ 2)) from by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_add_distrib]]
    rw [h1, h2]
    ring
  set f : Fin N → Fin N → ℝ := fun a b =>
    (∑ x : d, ∑ x2 : d, ‖X (x2, b) (x, a)‖ ^ 2)
      + (∑ x : d, ∑ x2 : d, ‖X (x2, a) (x, b)‖ ^ 2) with hfdef
  have hfac : (∑ a : Fin N, ∑ i : ι, ∑ b : Fin N, (frob (A i)) ^ 2 * f a b)
      = (∑ i : ι, (frob (A i)) ^ 2) * (∑ a : Fin N, ∑ b : Fin N, f a b) := by
    rw [show (∑ a : Fin N, ∑ i : ι, ∑ b : Fin N, (frob (A i)) ^ 2 * f a b)
        = ∑ i : ι, ∑ a : Fin N, ∑ b : Fin N, (frob (A i)) ^ 2 * f a b from
      Finset.sum_comm]
    rw [show (∑ i : ι, ∑ a : Fin N, ∑ b : Fin N, (frob (A i)) ^ 2 * f a b)
        = ∑ i : ι, ∑ q : Fin N × Fin N, (frob (A i)) ^ 2 * f q.1 q.2 from by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fintype.sum_prod_type]]
    rw [show (∑ i : ι, ∑ q : Fin N × Fin N, (frob (A i)) ^ 2 * f q.1 q.2)
        = (∑ i : ι, (frob (A i)) ^ 2) * (∑ q : Fin N × Fin N, f q.1 q.2) from
      (Finset.sum_mul_sum ..).symm]
    rw [show (∑ q : Fin N × Fin N, f q.1 q.2) = ∑ a : Fin N, ∑ b : Fin N, f a b from
      Fintype.sum_prod_type (fun q : Fin N × Fin N => f q.1 q.2)]
  calc (∑ p : GUECoord ι N, ‖∑ k : d × Fin N, ∑ l : d × Fin N,
        guePencilDirection A p k l * X l k‖ ^ 2)
      = ∑ i : ι, ∑ a : Fin N, ∑ b : Fin N,
          ‖∑ k : d × Fin N, ∑ l : d × Fin N,
            guePencilDirection A (i, (a, b)) k l * X l k‖ ^ 2 :=
        sum_gueCoord_eq' (fun p => ‖∑ k : d × Fin N, ∑ l : d × Fin N,
          guePencilDirection A p k l * X l k‖ ^ 2)
    _ ≤ ∑ i : ι, ∑ a : Fin N, ∑ b : Fin N,
          (gueScale N) ^ 2 * (frob (A i)) ^ 2 * f a b :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ =>
          Finset.sum_le_sum fun b _ => hstep i a b
    _ = (gueScale N) ^ 2 * ∑ i : ι, ∑ a : Fin N, ∑ b : Fin N,
          (frob (A i)) ^ 2 * f a b := by
        rw [show (∑ i : ι, ∑ a : Fin N, ∑ b : Fin N,
              (gueScale N) ^ 2 * (frob (A i)) ^ 2 * f a b)
            = ∑ i : ι, ∑ a : Fin N, ∑ b : Fin N,
              (gueScale N) ^ 2 * ((frob (A i)) ^ 2 * f a b) from by
          simp only [mul_assoc]]
        simp only [Finset.mul_sum]
    _ = (gueScale N) ^ 2 * (∑ i : ι, (frob (A i)) ^ 2) *
          (∑ a : Fin N, ∑ b : Fin N, f a b) := by
        rw [show (∑ i : ι, ∑ a : Fin N, ∑ b : Fin N, (frob (A i)) ^ 2 * f a b)
            = (∑ a : Fin N, ∑ i : ι, ∑ b : Fin N, (frob (A i)) ^ 2 * f a b) from
          Finset.sum_comm]
        rw [hfac]
        ring
    _ = (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) *
          (2 * (∑ k : d × Fin N, ∑ l : d × Fin N, ‖X l k‖ ^ 2)) := by rw [hS]
    _ = 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) *
          (∑ k : d × Fin N, ∑ l : d × Fin N, ‖X l k‖ ^ 2) := by ring

/-- Mixed-type triple-sum permutation. -/
lemma sum_three_perm {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℂ) :
    (∑ a : α, ∑ b : β, ∑ c : γ, f a b c) = ∑ b : β, ∑ c : γ, ∑ a : α, f a b c := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]

/-- The partial-trace kernel `S_{lm} = ∑_k R_{(u,k),l} R_{m,(v,k)}`. -/
def guePartialTraceKernel (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (x : GUECoord ι N → ℝ)
    (z : ℂ) (u v : d) : CStarMatrix (d × Fin N) (d × Fin N) ℂ :=
  fun l m => ∑ k : Fin N,
    guePencilResolvent A₀ A x z (u, k) l * guePencilResolvent A₀ A x z m (v, k)

/-- The partial-trace `k`-sum of the resolvent sandwich is the trace pairing of the direction
matrix against the partial-trace kernel. -/
lemma guePartialTraceDir_sum_eq_kernel (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (x : GUECoord ι N → ℝ) (z : ℂ) (u v : d) (p : GUECoord ι N) :
    (∑ k : Fin N, (guePencilResolvent A₀ A x z * guePencilDirection A p *
        guePencilResolvent A₀ A x z) (u, k) (v, k))
      = ∑ l : d × Fin N, ∑ m : d × Fin N,
          guePencilDirection A p l m * guePartialTraceKernel A₀ A x z u v l m := by
  have hL : (∑ k : Fin N, (guePencilResolvent A₀ A x z * guePencilDirection A p *
        guePencilResolvent A₀ A x z) (u, k) (v, k))
      = ∑ k : Fin N, ∑ b : d × Fin N, ∑ a : d × Fin N,
          guePencilResolvent A₀ A x z (u, k) b * guePencilDirection A p b a *
            guePencilResolvent A₀ A x z a (v, k) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [CStarMatrix.mul_apply, Finset.sum_mul]
    exact Finset.sum_comm
  have hR : (∑ l : d × Fin N, ∑ m : d × Fin N,
        guePencilDirection A p l m * guePartialTraceKernel A₀ A x z u v l m)
      = ∑ b : d × Fin N, ∑ a : d × Fin N, ∑ k : Fin N,
          guePencilDirection A p b a *
            (guePencilResolvent A₀ A x z (u, k) b * guePencilResolvent A₀ A x z a (v, k)) := by
    simp only [guePartialTraceKernel, Finset.mul_sum]
  rw [hL, hR, sum_three_perm (fun k b a =>
    guePencilResolvent A₀ A x z (u, k) b * guePencilDirection A p b a *
      guePencilResolvent A₀ A x z a (v, k))]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun k _ => ?_
  ring

/-- The kernel row is a matrix-vector product with a sparse vector. -/
lemma guePartialTraceKernel_eq_matVec (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (x : GUECoord ι N → ℝ) (z : ℂ) (u v : d) (l : d × Fin N) :
    (∑ m : d × Fin N, ‖guePartialTraceKernel A₀ A x z u v l m‖ ^ 2)
      = ∑ m : d × Fin N, ‖matVec (guePencilResolvent A₀ A x z)
          (fun a : d × Fin N => if a.1 = v then
            guePencilResolvent A₀ A x z (u, a.2) l else 0) m‖ ^ 2 := by
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  rw [guePartialTraceKernel, matVec, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single v]
  · simp [mul_comm]
  · intro x' _ hx'
    refine Finset.sum_eq_zero fun y _ => ?_
    simp [hx']
  · intro h; simp at h

/-- Squared row norms of the resolvent. -/
lemma sum_sq_resolvent_row_le (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (x : GUECoord ι N → ℝ) (z : ℂ) (hz : 0 < z.im) (a : d × Fin N) :
    (∑ l : d × Fin N, ‖guePencilResolvent A₀ A x z a l‖ ^ 2) ≤ (z.im)⁻¹ ^ 2 := by
  have h := sum_sq_rowComb_le A₀ A hA₀ hA z hz (unitVec a) x
  have h1 : (∑ k : d × Fin N, ‖unitVec a k‖ ^ 2) = 1 := sum_unitVec_norm_sq a
  have h2 : ∀ l, rowComb (guePencilResolvent A₀ A x z) (unitVec a) l
      = guePencilResolvent A₀ A x z a l := by
    intro l
    rw [rowComb, Finset.sum_eq_single a]
    · simp [unitVec]
    · intro b _ hb; simp [unitVec, hb]
    · intro h; simp at h
  rw [h1, mul_one] at h
  simpa only [h2] using h

/-- Frobenius bound for the partial-trace kernel. -/
lemma guePartialTraceKernel_frob_le (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (x : GUECoord ι N → ℝ) (z : ℂ) (hz : 0 < z.im) (hN : 0 < N) (u v : d) :
    (∑ l : d × Fin N, ∑ m : d × Fin N,
        ‖guePartialTraceKernel A₀ A x z u v l m‖ ^ 2)
      ≤ (N : ℝ) * ((z.im)⁻¹) ^ 4 := by
  classical
  set R := guePencilResolvent A₀ A x z with hR
  have hη : (0:ℝ) ≤ (z.im)⁻¹ := by positivity
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hcol : ∀ l : d × Fin N,
      (∑ m : d × Fin N, ‖guePartialTraceKernel A₀ A x z u v l m‖ ^ 2)
        ≤ (z.im)⁻¹ ^ 2 *
            (∑ m : d × Fin N, ‖(fun a : d × Fin N => if a.1 = v then R (u, a.2) l else 0) m‖ ^ 2) := by
    intro l
    rw [guePartialTraceKernel_eq_matVec A₀ A x z u v l]
    exact sum_sq_matVec_le A₀ A hA₀ hA z hz _ x
  have hinner : ∀ l : d × Fin N,
      (∑ m : d × Fin N, ‖(fun a : d × Fin N => if a.1 = v then R (u, a.2) l else 0) m‖ ^ 2)
        = ∑ k : Fin N, ‖R (u, k) l‖ ^ 2 := by
    intro l
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single v]
    · simp
    · intro x' _ hx'
      refine Finset.sum_eq_zero fun y _ => ?_
      simp [hx']
    · intro h; simp at h
  have hrow : (∑ l : d × Fin N, ∑ k : Fin N, ‖R (u, k) l‖ ^ 2)
      ≤ (N : ℝ) * (z.im)⁻¹ ^ 2 := by
    have h1 : ∀ k : Fin N, (∑ l : d × Fin N, ‖R (u, k) l‖ ^ 2) ≤ (z.im)⁻¹ ^ 2 :=
      fun k => sum_sq_resolvent_row_le A₀ A hA₀ hA x z hz (u, k)
    calc (∑ l : d × Fin N, ∑ k : Fin N, ‖R (u, k) l‖ ^ 2)
        = ∑ k : Fin N, ∑ l : d × Fin N, ‖R (u, k) l‖ ^ 2 := Finset.sum_comm
      _ ≤ ∑ _k : Fin N, (z.im)⁻¹ ^ 2 := Finset.sum_le_sum fun k _ => h1 k
      _ = (N : ℝ) * (z.im)⁻¹ ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc (∑ l : d × Fin N, ∑ m : d × Fin N,
        ‖guePartialTraceKernel A₀ A x z u v l m‖ ^ 2)
      ≤ ∑ l : d × Fin N, (z.im)⁻¹ ^ 2 *
          (∑ m : d × Fin N,
            ‖(fun a : d × Fin N => if a.1 = v then R (u, a.2) l else 0) m‖ ^ 2) :=
        Finset.sum_le_sum fun l _ => hcol l
    _ = (z.im)⁻¹ ^ 2 * ∑ l : d × Fin N, ∑ m : d × Fin N,
          ‖(fun a : d × Fin N => if a.1 = v then R (u, a.2) l else 0) m‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ = (z.im)⁻¹ ^ 2 * ∑ l : d × Fin N, ∑ k : Fin N, ‖R (u, k) l‖ ^ 2 := by
        rw [show (∑ l : d × Fin N, ∑ m : d × Fin N,
              ‖(fun a : d × Fin N => if a.1 = v then R (u, a.2) l else 0) m‖ ^ 2)
            = ∑ l : d × Fin N, ∑ k : Fin N, ‖R (u, k) l‖ ^ 2 from
          Finset.sum_congr rfl fun l _ => hinner l]
    _ ≤ (z.im)⁻¹ ^ 2 * ((N : ℝ) * (z.im)⁻¹ ^ 2) :=
        mul_le_mul_of_nonneg_left hrow (sq_nonneg _)
    _ = (N : ℝ) * ((z.im)⁻¹) ^ 4 := by ring

/-- **Sharp gradient bound for a general GUE pencil.**  A factor `N` better than
`sum_sq_guePartialTraceDir_le`:

`∑_p ‖∂_p T_N(z)_{uv}‖² ≤ 2 gueScale(N)² (∑_i frob(A_i)²) (im z)⁻⁴ / N = O(N⁻²)`. -/
theorem sum_sq_guePartialTraceDir_le_sharp (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (x : GUECoord ι N → ℝ) (z : ℂ) (hz : 0 < z.im) (hN : 0 < N) (u v : d) :
    (∑ p : GUECoord ι N, ‖guePartialTraceDir A₀ A z u v p x‖ ^ 2)
      ≤ 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4 / (N : ℝ) := by
  classical
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hη : (0:ℝ) ≤ (z.im)⁻¹ := by positivity
  have hD : ∀ p : GUECoord ι N,
      guePartialTraceDir A₀ A z u v p x
        = (N : ℂ)⁻¹ * ∑ l : d × Fin N, ∑ m : d × Fin N,
            guePencilDirection A p l m * guePartialTraceKernel A₀ A x z u v l m := by
    intro p
    rw [guePartialTraceDir, guePartialTraceDir_sum_eq_kernel]
  have hcontr := guePencil_trace_contraction A
    (fun m l : d × Fin N => guePartialTraceKernel A₀ A x z u v l m)
  have hfrob := guePartialTraceKernel_frob_le A₀ A hA₀ hA x z hz hN u v
  have hnorm : ‖(N : ℂ)⁻¹‖ ^ 2 = ((N : ℝ)⁻¹) ^ 2 := by
    rw [norm_inv, Complex.norm_natCast]
  have hfrobnn : (0:ℝ) ≤ ∑ i, (frob (A i)) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  calc (∑ p : GUECoord ι N, ‖guePartialTraceDir A₀ A z u v p x‖ ^ 2)
      = ∑ p : GUECoord ι N, ‖(N : ℂ)⁻¹ * ∑ l : d × Fin N, ∑ m : d × Fin N,
          guePencilDirection A p l m * guePartialTraceKernel A₀ A x z u v l m‖ ^ 2 :=
        Finset.sum_congr rfl fun p _ => by rw [hD p]
    _ = ‖(N : ℂ)⁻¹‖ ^ 2 * ∑ p : GUECoord ι N,
          ‖∑ l : d × Fin N, ∑ m : d × Fin N,
            guePencilDirection A p l m * guePartialTraceKernel A₀ A x z u v l m‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [norm_mul, mul_pow]
    _ ≤ ‖(N : ℂ)⁻¹‖ ^ 2 * (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) *
          (∑ k : d × Fin N, ∑ l : d × Fin N,
            ‖(fun m l : d × Fin N => guePartialTraceKernel A₀ A x z u v l m) l k‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hcontr (sq_nonneg _)
    _ ≤ ‖(N : ℂ)⁻¹‖ ^ 2 * (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) *
          ((N : ℝ) * ((z.im)⁻¹) ^ 4)) := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        have hfac : (0:ℝ) ≤ 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) :=
          mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg (gueScale N))) hfrobnn
        exact mul_le_mul_of_nonneg_left hfrob hfac
    _ = 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4 / (N : ℝ) := by
        rw [hnorm]
        have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
        field_simp

/-- **Sharp entrywise variance bound for a general GUE pencil (real part).** -/
theorem variance_partialTrace_re_le_sharp (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (hN : 0 < N) (u v : d) :
    variance (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        (guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v).re)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      ≤ 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4 / (N : ℝ) :=
  variance_partialTrace_re_le_of_grad A₀ A hA₀ hA z hz hN u v _
    (fun x => sum_sq_guePartialTraceDir_le_sharp A₀ A hA₀ hA x z hz hN u v)

/-- **Sharp entrywise variance bound for a general GUE pencil (imaginary part).** -/
theorem variance_partialTrace_im_le_sharp (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (hN : 0 < N) (u v : d) :
    variance (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        (guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v).im)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      ≤ 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4 / (N : ℝ) :=
  variance_partialTrace_im_le_of_grad A₀ A hA₀ hA z hz hN u v _
    (fun x => sum_sq_guePartialTraceDir_le_sharp A₀ A hA₀ hA x z hz hN u v)

/-- **Sharp complex `L²` fluctuation bound for a general GUE pencil.** -/
theorem integral_norm_sq_fluctuation_le_sharp (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (hN : 0 < N) (u v : d) :
    ∫ x, ‖guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v -
        gueResolventMean (N := N) A₀ A z u v‖ ^ 2
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      ≤ 4 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4 / (N : ℝ) := by
  have h := integral_norm_sq_fluctuation_le_of_var A₀ A hA₀ hA z hz hN u v
    (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4 / (N : ℝ))
    (variance_partialTrace_re_le_sharp A₀ A hA₀ hA z hz hN u v)
    (variance_partialTrace_im_le_sharp A₀ A hA₀ hA z hz hN u v)
  calc ∫ x, ‖guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v -
        gueResolventMean (N := N) A₀ A z u v‖ ^ 2
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      ≤ 2 * (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4 / (N : ℝ)) := h
    _ = 4 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4 / (N : ℝ) := by ring

/-- The mean-multiplication matrix in `E[T B T] - E[T] B E[T]` (public copy of the private
lemma in `DysonVariance`). -/
lemma mul_mean_entry' (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (z : ℂ)
    (B : Matrix d d ℂ) (u v : d) :
    (gueResolventMean (N := N) A₀ A z * B * gueResolventMean (N := N) A₀ A z) u v
      = ∑ a : d, ∑ b : d, B a b *
          (gueResolventMean (N := N) A₀ A z u a *
            gueResolventMean (N := N) A₀ A z b v) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem covariance_partialTrace_mul_le_sharp (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (hN : 0 < N)
    (B : Matrix d d ℂ) (_hB : B.IsHermitian) :
    frob (Matrix.of (fun u v =>
        ∫ x, (guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) * B *
            guePartialTrace A₀ A z (x : GUECoord ι N → ℝ)) u v
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
      - gueResolventMean (N := N) A₀ A z * B * gueResolventMean (N := N) A₀ A z)
      ≤ 2 * (Fintype.card d : ℝ) ^ 2 * frob B *
          (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4 / (N : ℝ)) := by
  classical
  set μ := stdGaussian (EuclideanSpace ℝ (GUECoord ι N))
  set T : EuclideanSpace ℝ (GUECoord ι N) → Matrix d d ℂ := fun x =>
    guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) with hT
  set m : Matrix d d ℂ := gueResolventMean (N := N) A₀ A z with hm
  set vc : ℝ := 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4 / (N : ℝ) with hvc
  have hz' : z.im ≠ 0 := ne_of_gt hz
  have hvc0 : 0 ≤ vc := by
    rw [hvc]
    positivity
  have hTbdd : ∀ (x : EuclideanSpace ℝ (GUECoord ι N)) (a b : d), ‖T x a b‖ ≤ (z.im)⁻¹ := by
    intro x a b
    rw [hT]
    calc ‖guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) a b‖ ≤ |z.im|⁻¹ :=
          norm_guePartialTrace_entry_le A₀ A hA₀ hA _ z hz' hN a b
      _ = (z.im)⁻¹ := by rw [abs_of_pos hz]
  have hTcont : ∀ a b : d, Continuous (fun x => T x a b) := by
    intro a b
    rw [hT]
    exact continuous_guePartialTrace_entry A₀ A hA₀ hA z hz' a b
  have hTint : ∀ a b : d, Integrable (fun x => T x a b) μ := by
    intro a b
    simpa [hT] using integrable_guePartialTrace_entry A₀ A hA₀ hA z hz hN a b
  have hTprod : ∀ a b c e : d, Integrable (fun x => T x a b * T x c e) μ := by
    intro a b c e
    exact (hTint a b).mul_bdd ((hTcont c e).aestronglyMeasurable)
      (ae_of_all _ fun x => hTbdd x c e)
  -- pointwise expansion of the matrix product
  have hpt : ∀ (u v : d) (x : EuclideanSpace ℝ (GUECoord ι N)),
      (T x * B * T x) u v = ∑ a : d, ∑ b : d, B a b * (T x u a * T x b v) := by
    intro u v x
    simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  -- expansion of the integral of `T B T`
  have h1 : ∀ u v : d, (∫ x, (T x * B * T x) u v ∂μ)
      = ∑ a : d, ∑ b : d, B a b * ∫ x, T x u a * T x b v ∂μ := by
    intro u v
    rw [show (∫ x, (T x * B * T x) u v ∂μ)
        = ∫ x, ∑ a : d, ∑ b : d, B a b * (T x u a * T x b v) ∂μ from
      integral_congr_ae (ae_of_all _ (hpt u v))]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro a _
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro b _
        rw [integral_const_mul]
      · intro b _
        exact (hTprod u a b v).const_mul (B a b)
    · intro a _
      exact integrable_finsetSum _ fun b _ => (hTprod u a b v).const_mul (B a b)
  -- expansion of `m B m`
  have h2 : ∀ u v : d, (m * B * m) u v
      = ∑ a : d, ∑ b : d, B a b * (m u a * m b v) := by
    intro u v
    rw [hm]
    exact mul_mean_entry' A₀ A z B u v
  -- the fluctuation bracket identity
  have h3 : ∀ (u v a b : d), (∫ x, T x u a * T x b v ∂μ) - m u a * m b v
      = ∫ x, (T x u a - m u a) * (T x b v - m b v) ∂μ := by
    intro u v a b
    have hma : m u a = ∫ x, T x u a ∂μ := rfl
    have hmb : m b v = ∫ x, T x b v ∂μ := rfl
    have hA1 : Integrable (fun x => T x u a * T x b v) μ := hTprod u a b v
    have hA2 : Integrable (fun x => m u a * T x b v) μ := (hTint b v).const_mul (m u a)
    have hA3 : Integrable (fun x => T x u a * m b v) μ :=
      ((hTint u a).const_mul (m b v)).congr (ae_of_all _ fun x => mul_comm _ _)
    have hA4 : Integrable (fun x => m u a * m b v) μ := integrable_const _
    have hpt' : ∀ x : EuclideanSpace ℝ (GUECoord ι N),
        (T x u a - m u a) * (T x b v - m b v)
          = (T x u a * T x b v - m u a * T x b v) -
              (T x u a * m b v - m u a * m b v) := by
      intro x
      ring
    have hcalc : (∫ x, (T x u a - m u a) * (T x b v - m b v) ∂μ)
        = (∫ x, T x u a * T x b v ∂μ) - m u a * m b v := by
      calc ∫ x, (T x u a - m u a) * (T x b v - m b v) ∂μ
          = ∫ x, ((T x u a * T x b v - m u a * T x b v) -
              (T x u a * m b v - m u a * m b v)) ∂μ :=
            integral_congr_ae (ae_of_all _ hpt')
        _ = (∫ x, (T x u a * T x b v - m u a * T x b v) ∂μ) -
              ∫ x, (T x u a * m b v - m u a * m b v) ∂μ :=
            integral_sub (hA1.sub hA2) (hA3.sub hA4)
        _ = ((∫ x, T x u a * T x b v ∂μ) - ∫ x, m u a * T x b v ∂μ) -
              ((∫ x, T x u a * m b v ∂μ) - ∫ x, m u a * m b v ∂μ) := by
            rw [integral_sub hA1 hA2, integral_sub hA3 hA4]
        _ = (∫ x, T x u a * T x b v ∂μ) - m u a * m b v := by
            rw [integral_const_mul, integral_mul_const, integral_const]
            rw [hma, hmb]
            simp
    exact hcalc.symm
  -- entrywise bound
  have hcov : ∀ (u v a b : d),
      ‖∫ x, (T x u a - m u a) * (T x b v - m b v) ∂μ‖ ≤ 2 * vc := by
    intro u v a b
    have hf : MemLp (fun x => T x u a - m u a) 2 μ := by
      refine MemLp.of_bound ((hTcont u a).sub continuous_const).aestronglyMeasurable
        (2 * (z.im)⁻¹) ?_
      filter_upwards with x
      calc ‖T x u a - m u a‖ ≤ ‖T x u a‖ + ‖m u a‖ := norm_sub_le _ _
        _ ≤ (z.im)⁻¹ + (z.im)⁻¹ := by
            refine add_le_add (hTbdd x u a) ?_
            rw [hm]
            exact norm_gueResolventMean_entry_le A₀ A hA₀ hA z hz hN u a
        _ = 2 * (z.im)⁻¹ := by ring
    have hg : MemLp (fun x => T x b v - m b v) 2 μ := by
      refine MemLp.of_bound ((hTcont b v).sub continuous_const).aestronglyMeasurable
        (2 * (z.im)⁻¹) ?_
      filter_upwards with x
      calc ‖T x b v - m b v‖ ≤ ‖T x b v‖ + ‖m b v‖ := norm_sub_le _ _
        _ ≤ (z.im)⁻¹ + (z.im)⁻¹ := by
            refine add_le_add (hTbdd x b v) ?_
            rw [hm]
            exact norm_gueResolventMean_entry_le A₀ A hA₀ hA z hz hN b v
        _ = 2 * (z.im)⁻¹ := by ring
    have hCS := norm_integral_mul_le_sqrt hf hg
    have hfint : (∫ x, ‖T x u a - m u a‖ ^ 2 ∂μ) ≤ 2 * vc := by
      rw [hm, hT, hvc]
      refine (integral_norm_sq_fluctuation_le_sharp A₀ A hA₀ hA z hz hN u a).trans ?_
      exact le_of_eq (by ring)
    have hgint : (∫ x, ‖T x b v - m b v‖ ^ 2 ∂μ) ≤ 2 * vc := by
      rw [hm, hT, hvc]
      refine (integral_norm_sq_fluctuation_le_sharp A₀ A hA₀ hA z hz hN b v).trans ?_
      exact le_of_eq (by ring)
    refine hCS.trans ?_
    have h2vc : 0 ≤ 2 * vc := by positivity
    calc Real.sqrt (∫ x, ‖T x u a - m u a‖ ^ 2 ∂μ) *
          Real.sqrt (∫ x, ‖T x b v - m b v‖ ^ 2 ∂μ)
        ≤ Real.sqrt (2 * vc) * Real.sqrt (2 * vc) := by
          refine mul_le_mul (Real.sqrt_le_sqrt hfint) (Real.sqrt_le_sqrt hgint)
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = 2 * vc := by
          rw [Real.mul_self_sqrt h2vc]
  -- entry bound of the covariance matrix
  have hentry : ∀ u v : d,
      ‖(Matrix.of (fun u v => ∫ x, (T x * B * T x) u v ∂μ) - m * B * m) u v‖
        ≤ (Fintype.card d : ℝ) * frob B * (2 * vc) := by
    intro u v
    have hid : (Matrix.of (fun u v => ∫ x, (T x * B * T x) u v ∂μ) - m * B * m) u v
        = ∑ a : d, ∑ b : d, B a b * ∫ x,
            (T x u a - m u a) * (T x b v - m b v) ∂μ := by
      rw [Matrix.sub_apply, Matrix.of_apply, h1 u v, h2 u v]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro b _
      rw [← mul_sub, h3 u v a b]
    rw [hid]
    calc ‖∑ a : d, ∑ b : d, B a b * ∫ x,
          (T x u a - m u a) * (T x b v - m b v) ∂μ‖
        ≤ ∑ a : d, ∑ b : d, ‖B a b * ∫ x,
            (T x u a - m u a) * (T x b v - m b v) ∂μ‖ := by
          refine (norm_sum_le _ _).trans ?_
          exact Finset.sum_le_sum fun a _ => norm_sum_le _ _
      _ ≤ ∑ a : d, ∑ b : d, ‖B a b‖ * (2 * vc) := by
          refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hcov u v a b) (norm_nonneg _)
      _ = (∑ a : d, ∑ b : d, ‖B a b‖) * (2 * vc) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_mul]
      _ ≤ ((Fintype.card d : ℝ) * frob B) * (2 * vc) := by
          exact mul_le_mul_of_nonneg_right (sum_norm_entry_le_card_mul_frob B) (by positivity)
  -- Frobenius norm bound from the entrywise one
  have hfrob : frob (Matrix.of (fun u v => ∫ x, (T x * B * T x) u v ∂μ) - m * B * m)
      ≤ (Fintype.card d : ℝ) * ((Fintype.card d : ℝ) * frob B * (2 * vc)) := by
    set X : ℝ := (Fintype.card d : ℝ) * frob B * (2 * vc) with hXdef
    have hX0 : 0 ≤ X := by
      rw [hXdef]
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (frob_nonneg B)) (by positivity)
    have hsq : (∑ u : d, ∑ v : d,
          ‖(Matrix.of (fun u v => ∫ x, (T x * B * T x) u v ∂μ) - m * B * m) u v‖ ^ 2)
        ≤ (Fintype.card d : ℝ) ^ 2 * X ^ 2 := by
      calc (∑ u : d, ∑ v : d,
            ‖(Matrix.of (fun u v => ∫ x, (T x * B * T x) u v ∂μ) - m * B * m) u v‖ ^ 2)
          ≤ ∑ u : d, ∑ v : d, X ^ 2 := by
            refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => ?_
            exact pow_le_pow_left₀ (norm_nonneg _) (hentry u v) 2
        _ = (Fintype.card d : ℝ) * (Fintype.card d : ℝ) * X ^ 2 := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            ring
        _ = (Fintype.card d : ℝ) ^ 2 * X ^ 2 := by ring
    rw [frob]
    calc Real.sqrt (∑ u : d, ∑ v : d,
          ‖(Matrix.of (fun u v => ∫ x, (T x * B * T x) u v ∂μ) - m * B * m) u v‖ ^ 2)
        ≤ Real.sqrt ((Fintype.card d : ℝ) ^ 2 * X ^ 2) := Real.sqrt_le_sqrt hsq
      _ = (Fintype.card d : ℝ) * X := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), Real.sqrt_sq hX0]
      _ = (Fintype.card d : ℝ) * ((Fintype.card d : ℝ) * frob B * (2 * vc)) := by
          rw [hXdef]

  calc frob (Matrix.of (fun u v => ∫ x, (T x * B * T x) u v ∂μ) - m * B * m)
      ≤ (Fintype.card d : ℝ) * ((Fintype.card d : ℝ) * frob B * (2 * vc)) := hfrob
    _ = 2 * (Fintype.card d : ℝ) ^ 2 * frob B * vc := by ring


theorem approximate_dyson_entry_le_sharp (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (hN : 0 < N) (u v : d) :
    ‖((z • (1 : Matrix d d ℂ) - A₀) * gueResolventMean (N := N) A₀ A z - 1
        - ∑ i, A i * (gueResolventMean (N := N) A₀ A z * A i *
            gueResolventMean (N := N) A₀ A z)) u v‖
      ≤ 2 * (Fintype.card d : ℝ) ^ 2 * Real.sqrt (Fintype.card d : ℝ) *
          (∑ i, (frob (A i)) ^ 2) *
          (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4 / (N : ℝ)) := by
  classical
  set μ := stdGaussian (EuclideanSpace ℝ (GUECoord ι N))
  set g : Matrix d d ℂ := gueResolventMean (N := N) A₀ A z with hg
  set vc : ℝ := 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4 / (N : ℝ) with hvc
  set Mi : ι → Matrix d d ℂ := fun i => Matrix.of (fun u v =>
      ∫ x, (guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) * A i *
          guePartialTrace A₀ A z (x : GUECoord ι N → ℝ)) u v ∂μ)
      - g * A i * g with hMidef
  have hvc0 : 0 ≤ vc := by
    rw [hvc]
    positivity
  have hMi : ∀ i : ι, frob (Mi i) ≤ 2 * (Fintype.card d : ℝ) ^ 2 * frob (A i) * vc := by
    intro i
    rw [hMidef, hvc, hg]
    exact covariance_partialTrace_mul_le_sharp A₀ A hA₀ hA z hz hN (A i) (hA i)
  have hexpr : ((z • (1 : Matrix d d ℂ) - A₀) * g - 1
        - ∑ i, A i * (g * A i * g)) u v
      = ∑ i, ∑ a, A i u a * (Mi i) a v := by
    have hm := gue_dyson_master_identity A₀ A hA₀ hA z (ne_of_gt hz)
      (by exact_mod_cast hN.ne')
    have h1 : ((z • (1 : Matrix d d ℂ) - A₀) * g - 1) u v
        = ∑ i, ∑ a, A i u a * (Matrix.of (fun u v =>
            ∫ x, (guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) * A i *
                guePartialTrace A₀ A z (x : GUECoord ι N → ℝ)) u v ∂μ)) a v := by
      rw [hg]
      rw [show ((z • (1 : Matrix d d ℂ) - A₀) * gueResolventMean (N := N) A₀ A z - 1)
          = ∑ i, A i * (Matrix.of (fun u v =>
              ∫ x, (guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) * A i *
                  guePartialTrace A₀ A z (x : GUECoord ι N → ℝ)) u v ∂μ)) from hm]
      simp only [Matrix.sum_apply, Matrix.mul_apply]
    have h2 : (∑ i, A i * (g * A i * g)) u v
        = ∑ i, ∑ a, A i u a * (g * A i * g) a v := by
      simp only [Matrix.sum_apply, Matrix.mul_apply]
    rw [Matrix.sub_apply, h1, h2]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    simp only [hMidef, Matrix.sub_apply, Matrix.of_apply]
    ring
  rw [hexpr]
  have hK : ∀ i : ι, 0 ≤ 2 * (Fintype.card d : ℝ) ^ 2 * frob (A i) * vc := by
    intro i
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (frob_nonneg _)) hvc0
  calc ‖∑ i : ι, ∑ a : d, A i u a * (Mi i) a v‖
      ≤ ∑ i : ι, ∑ a : d, ‖A i u a‖ * ‖(Mi i) a v‖ := by
        refine (norm_sum_le _ _).trans ?_
        exact Finset.sum_le_sum fun i _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => by rw [norm_mul])
    _ ≤ ∑ i : ι, ∑ a : d, ‖A i u a‖ *
          (2 * (Fintype.card d : ℝ) ^ 2 * frob (A i) * vc) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ => ?_
        exact mul_le_mul_of_nonneg_left
          ((norm_entry_le_frob (Mi i) a v).trans (hMi i)) (norm_nonneg _)
    _ = ∑ i : ι, (∑ a : d, ‖A i u a‖) *
          (2 * (Fintype.card d : ℝ) ^ 2 * frob (A i) * vc) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_mul]
    _ ≤ ∑ i : ι, (Real.sqrt (Fintype.card d : ℝ) * frob (A i)) *
          (2 * (Fintype.card d : ℝ) ^ 2 * frob (A i) * vc) := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact mul_le_mul_of_nonneg_right (sum_norm_row_le_sqrt_card_mul_frob (A i) u) (hK i)
    _ = 2 * (Fintype.card d : ℝ) ^ 2 * Real.sqrt (Fintype.card d : ℝ) *
          (∑ i, (frob (A i)) ^ 2) * vc := by
        calc ∑ i : ι, (Real.sqrt (Fintype.card d : ℝ) * frob (A i)) *
              (2 * (Fintype.card d : ℝ) ^ 2 * frob (A i) * vc)
            = ∑ i : ι, (Real.sqrt (Fintype.card d : ℝ) *
                (2 * (Fintype.card d : ℝ) ^ 2)) * ((frob (A i)) ^ 2) * vc := by
              apply Finset.sum_congr rfl
              intro i _
              ring
          _ = (∑ i : ι, (Real.sqrt (Fintype.card d : ℝ) *
                (2 * (Fintype.card d : ℝ) ^ 2)) * ((frob (A i)) ^ 2)) * vc := by
              rw [Finset.sum_mul]
          _ = (Real.sqrt (Fintype.card d : ℝ) * (2 * (Fintype.card d : ℝ) ^ 2)) *
                (∑ i, (frob (A i)) ^ 2) * vc := by
              rw [Finset.mul_sum]
          _ = 2 * (Fintype.card d : ℝ) ^ 2 * Real.sqrt (Fintype.card d : ℝ) *
                (∑ i, (frob (A i)) ^ 2) * vc := by
              ring
    _ = 2 * (Fintype.card d : ℝ) ^ 2 * Real.sqrt (Fintype.card d : ℝ) *
          (∑ i, (frob (A i)) ^ 2) *
          (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4 / (N : ℝ)) := by
        rw [hvc]

end
end GUEStrongConvergence
