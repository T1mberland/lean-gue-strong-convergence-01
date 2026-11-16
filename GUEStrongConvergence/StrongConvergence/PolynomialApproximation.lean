/-
# Approximation of matrix polynomials by rational-coefficient polynomials

The simultaneous lifting of the strong-convergence statement from a countable family to
*all* complex matrix polynomials needs a density/continuity argument: the complex
polynomials are uncountable, but those with Gaussian-rational coefficients are countable
and dense in an explicit coefficient norm.

This file provides:

* `ratApproxCoeff` — coefficientwise approximation of complex numbers by `ℚ[i]`;
* `mapCoeffs` / `ratApproxPoly` — the induced approximation of word polynomials and
  matrix polynomials, together with the coefficient distance
  `coeffDist P Q = ∑_{i,j} ∑_{w ∈ supp P ∪ supp Q} ‖P i j w - Q i j w‖`
  and the density estimate `coeffDist P (ratApproxPoly δ P) < ε`;
* the evaluation Lipschitz estimate
  `‖evalMatrixPoly P G - evalMatrixPoly Q G‖ ≤ C * (1 + tupleNorm G)^D * coeffDist P Q`;
* the reduction theorem `ae_tendsto_norm_of_dense_family`, which passes from a countable
  dense family to all complex matrix polynomials under an explicit scalar edge bound
  `∀ᶠ N, ‖G_N(x)‖ ≤ R` (and no assumption on the conclusion).
-/
import GUEStrongConvergence.StrongConvergence.BlockDiagonalNorm
import GUEStrongConvergence.Linearization.PolynomialBridge
import Mathlib.SetTheory.Cardinal.Free
import Mathlib.Data.Finsupp.Encodable

noncomputable section

namespace GUEStrongConvergence

open Filter MeasureTheory FreeProbability FreeProbability.Fock Matrix
open scoped ComplexOrder Topology BigOperators

variable {I : Type*}

/-- `FreeMonoid` inherits decidable equality from `List`. -/
instance freeMonoidDecidableEq {I : Type*} [DecidableEq I] : DecidableEq (FreeMonoid I) :=
  inferInstanceAs (DecidableEq (List I))

/-! ## Coefficientwise approximation by `ℚ[i]` -/

lemma exists_rat_abs_sub_lt (x : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ q : ℚ, |x - (q : ℝ)| < δ := by
  obtain ⟨q, h1, h2⟩ := exists_rat_btwn (show x - δ < x + δ by linarith)
  exact ⟨q, by rw [abs_lt]; constructor <;> linarith⟩

/-- Approximation of a complex number by an element of `ℚ[i]` within `δ`. -/
noncomputable def ratApproxCoeff (δ : ℝ) (c : ℂ) : ℂ :=
  if h : 0 < δ then
    if c = 0 then 0
    else
      ((Classical.choose (exists_rat_abs_sub_lt c.re (half_pos h)) : ℚ) : ℂ)
        + ((Classical.choose (exists_rat_abs_sub_lt c.im (half_pos h)) : ℚ) : ℂ) * Complex.I
  else 0

@[simp]
lemma ratApproxCoeff_zero (δ : ℝ) : ratApproxCoeff δ 0 = 0 := by
  unfold ratApproxCoeff
  by_cases h : 0 < δ <;> simp [h]

lemma ratApproxCoeff_mem_rat (δ : ℝ) (c : ℂ) :
    ∃ a b : ℚ, ratApproxCoeff δ c = (a : ℂ) + (b : ℂ) * Complex.I := by
  unfold ratApproxCoeff
  by_cases h : 0 < δ
  · rw [dif_pos h]
    by_cases hc : c = 0
    · exact ⟨0, 0, by rw [if_pos hc]; simp⟩
    · rw [if_neg hc]
      exact ⟨_, _, rfl⟩
  · rw [dif_neg h]
    exact ⟨0, 0, by simp⟩

lemma norm_sub_ratApproxCoeff_lt {δ : ℝ} (hδ : 0 < δ) (c : ℂ) :
    ‖c - ratApproxCoeff δ c‖ < δ := by
  unfold ratApproxCoeff
  rw [dif_pos hδ]
  by_cases hc : c = 0
  · rw [if_pos hc]
    simpa [hc] using hδ
  · rw [if_neg hc]
    set a : ℚ := Classical.choose (exists_rat_abs_sub_lt c.re (half_pos hδ))
    set b : ℚ := Classical.choose (exists_rat_abs_sub_lt c.im (half_pos hδ))
    have ha : |c.re - (a : ℝ)| < δ / 2 :=
      Classical.choose_spec (exists_rat_abs_sub_lt c.re (half_pos hδ))
    have hb : |c.im - (b : ℝ)| < δ / 2 :=
      Classical.choose_spec (exists_rat_abs_sub_lt c.im (half_pos hδ))
    have hdecomp : c - ((a : ℂ) + (b : ℂ) * Complex.I)
        = ((c.re - (a : ℝ) : ℝ) : ℂ) + ((c.im - (b : ℝ) : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [hdecomp]
    calc ‖((c.re - (a : ℝ) : ℝ) : ℂ) + ((c.im - (b : ℝ) : ℝ) : ℂ) * Complex.I‖
        ≤ |Complex.re (((c.re - (a : ℝ) : ℝ) : ℂ)
              + ((c.im - (b : ℝ) : ℝ) : ℂ) * Complex.I)|
            + |Complex.im (((c.re - (a : ℝ) : ℝ) : ℂ)
              + ((c.im - (b : ℝ) : ℝ) : ℂ) * Complex.I)| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ = |(c.re - (a : ℝ) : ℝ)| + |(c.im - (b : ℝ) : ℝ)| := by simp
      _ < δ := by linarith

/-! ## Coefficient maps on word polynomials -/

/-- Map the coefficients of a word polynomial by a zero-preserving function. -/
def mapCoeffs (f : ℂ → ℂ) (hf : f 0 = 0) (p : WordPolynomial ℂ I) : WordPolynomial ℂ I :=
  ⟨Finsupp.mapRange f hf p.coeff⟩

@[simp]
lemma coeff_mapCoeffs (f : ℂ → ℂ) (hf : f 0 = 0) (p : WordPolynomial ℂ I) (w : FreeMonoid I) :
    (mapCoeffs f hf p).coeff w = f (p.coeff w) := by
  simp [mapCoeffs, Finsupp.mapRange_apply]

lemma support_mapCoeffs_subset (f : ℂ → ℂ) (hf : f 0 = 0) (p : WordPolynomial ℂ I) :
    (mapCoeffs f hf p).coeff.support ⊆ p.coeff.support :=
  Finsupp.support_mapRange (f := f) (hf := hf) (g := p.coeff)

end GUEStrongConvergence

namespace GUEStrongConvergence

open Filter MeasureTheory FreeProbability FreeProbability.Fock Matrix
open scoped ComplexOrder Topology BigOperators

variable {r d : ℕ}

/-- Coefficientwise approximation of a matrix polynomial. -/
noncomputable def ratApproxPoly (δ : ℝ)
    (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r))) :
    Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r)) :=
  fun i j => mapCoeffs (ratApproxCoeff δ) (ratApproxCoeff_zero δ) (P i j)

/-- Every coefficient of `ratApproxPoly δ P` lies in `ℚ[i]`. -/
lemma ratApproxPoly_coeff_mem (δ : ℝ)
    (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r))) :
    ∀ i j w, ∃ a b : ℚ,
      (ratApproxPoly δ P i j).coeff w = (a : ℂ) + (b : ℂ) * Complex.I := by
  intro i j w
  rw [ratApproxPoly, coeff_mapCoeffs]
  exact ratApproxCoeff_mem_rat δ _

/-- The number of coefficients of a matrix polynomial, as a real number. -/
noncomputable def coeffCard (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r))) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d, ((P i j).coeff.support.card : ℝ)

/-- Explicit coefficient distance: the `ℓ¹` distance of all coefficients over the union of
the supports. -/
noncomputable def coeffDist (P Q : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r))) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d,
    ∑ w ∈ (P i j).coeff.support ∪ (Q i j).coeff.support,
      ‖(P i j).coeff w - (Q i j).coeff w‖

lemma coeffCard_nonneg (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r))) :
    0 ≤ coeffCard P := by
  unfold coeffCard
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity

/-- **Density of `ℚ[i]`-coefficient polynomials** in the coefficient distance. -/
theorem coeffDist_ratApproxPoly_lt
    (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r))) {ε : ℝ} (hε : 0 < ε) :
    coeffDist P (ratApproxPoly (ε / (2 * (coeffCard P + 1))) P) < ε := by
  set M : ℝ := coeffCard P with hM
  set δ : ℝ := ε / (2 * (M + 1)) with hδdef
  have hMnn : 0 ≤ M := coeffCard_nonneg P
  have hδpos : 0 < δ := by
    rw [hδdef]; positivity
  have hsupp : ∀ i j,
      (ratApproxPoly δ P i j).coeff.support ⊆ (P i j).coeff.support := by
    intro i j
    exact support_mapCoeffs_subset (ratApproxCoeff δ) (ratApproxCoeff_zero δ) (P i j)
  have hterm : ∀ i j w, w ∈ (P i j).coeff.support →
      ‖(P i j).coeff w - (ratApproxPoly δ P i j).coeff w‖ < δ := by
    intro i j w _
    rw [ratApproxPoly, coeff_mapCoeffs]
    exact norm_sub_ratApproxCoeff_lt hδpos _
  have hbound : coeffDist P (ratApproxPoly δ P) ≤ M * δ := by
    unfold coeffDist
    calc ∑ i : Fin d, ∑ j : Fin d,
          ∑ w ∈ (P i j).coeff.support ∪ (ratApproxPoly δ P i j).coeff.support,
            ‖(P i j).coeff w - (ratApproxPoly δ P i j).coeff w‖
        ≤ ∑ i : Fin d, ∑ j : Fin d,
            ∑ w ∈ (P i j).coeff.support ∪ (ratApproxPoly δ P i j).coeff.support, δ := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          apply Finset.sum_le_sum
          intro w _
          by_cases hmem : w ∈ (P i j).coeff.support
          · exact le_of_lt (hterm i j w hmem)
          · have hwP : (P i j).coeff w = 0 := Finsupp.notMem_support_iff.mp hmem
            have hwQ : (ratApproxPoly δ P i j).coeff w = 0 := by
              show (mapCoeffs (ratApproxCoeff δ) (ratApproxCoeff_zero δ) (P i j)).coeff w = 0
              rw [coeff_mapCoeffs, hwP, ratApproxCoeff_zero]
            rw [hwP, hwQ, sub_zero, norm_zero]
            exact le_of_lt hδpos
      _ = ∑ i : Fin d, ∑ j : Fin d, ((P i j).coeff.support.card : ℝ) * δ := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.union_eq_left.mpr (hsupp i j), Finset.sum_const, nsmul_eq_mul]
      _ = M * δ := by
          rw [hM]
          unfold coeffCard
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_mul]
  have hlt : M * δ < ε := by
    rw [hδdef, ← mul_div_assoc, div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

end GUEStrongConvergence

namespace GUEStrongConvergence

open Filter MeasureTheory FreeProbability FreeProbability.Fock Matrix
open scoped ComplexOrder Topology BigOperators

variable {r : ℕ}

/-- The `ℓ¹` norm of a family of generators. -/
noncomputable def tupleNorm {A : Type*} [SeminormedAddGroup A] (G : Fin r → A) : ℝ :=
  ∑ i, ‖G i‖

lemma tupleNorm_nonneg {A : Type*} [SeminormedAddGroup A] (G : Fin r → A) :
    0 ≤ tupleNorm G :=
  Finset.sum_nonneg fun i _ => norm_nonneg _

lemma norm_le_tupleNorm {A : Type*} [SeminormedAddGroup A] (G : Fin r → A) (i : Fin r) :
    ‖G i‖ ≤ tupleNorm G :=
  Finset.single_le_sum (fun j _ => norm_nonneg (G j)) (Finset.mem_univ i)

lemma norm_wordProd_le {A : Type*} [CStarAlgebra A] [Nontrivial A]
    (G : Fin r → A) (w : List (Fin r)) :
    ‖wordProd G w‖ ≤ (tupleNorm G) ^ w.length := by
  induction w with
  | nil =>
      rw [wordProd, List.map_nil, List.prod_nil, List.length_nil, pow_zero]
      exact le_of_eq (CStarRing.norm_one (E := A))
  | cons a l ih =>
      rw [wordProd, List.map_cons, List.prod_cons]
      calc ‖G a * wordProd G l‖ ≤ ‖G a‖ * ‖wordProd G l‖ := norm_mul_le _ _
        _ ≤ tupleNorm G * (tupleNorm G) ^ l.length :=
            mul_le_mul (norm_le_tupleNorm G a) ih (norm_nonneg _) (tupleNorm_nonneg G)
        _ = (tupleNorm G) ^ (a :: l).length := by
            rw [List.length_cons, pow_succ]
            ring

/-- The operator norm of a matrix is bounded by the sum of the norms of its entries. -/
lemma norm_le_sum_norm_entries {d : ℕ} {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (M : CStarMatrix (Fin d) (Fin d) A) :
    ‖M‖ ≤ ∑ i : Fin d, ∑ j : Fin d, ‖M i j‖ := by
  rw [CStarMatrix.norm_def]
  refine (CStarMatrix.toCLM M).opNorm_le_bound (by positivity) fun v => ?_
  rw [CStarMatrix.toCLM_apply_eq_sum]
  set w : Fin d → A := fun j => ∑ i, v i * M i j with hw
  have h1 : ‖(WithCStarModule.equiv A (Fin d → A)).symm w‖ ≤ ∑ j, ‖w j‖ :=
    WithCStarModule.pi_norm_le_sum_norm _
  have h2 : ∑ j : Fin d, ‖w j‖ ≤ ∑ j : Fin d, ∑ i : Fin d, ‖v i‖ * ‖M i j‖ := by
    apply Finset.sum_le_sum
    intro j _
    calc ‖∑ i, v i * M i j‖ ≤ ∑ i, ‖v i * M i j‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖v i‖ * ‖M i j‖ :=
          Finset.sum_le_sum fun i _ => norm_mul_le _ _
  have h3 : ∑ j : Fin d, ∑ i : Fin d, ‖v i‖ * ‖M i j‖
      ≤ (∑ j : Fin d, ∑ i : Fin d, ‖M i j‖) * ‖v‖ := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    calc ‖v i‖ * ‖M i j‖ ≤ ‖v‖ * ‖M i j‖ :=
          mul_le_mul_of_nonneg_right (WithCStarModule.norm_apply_le_norm v i) (norm_nonneg _)
      _ = ‖M i j‖ * ‖v‖ := mul_comm _ _
  calc ‖(WithCStarModule.equiv A (Fin d → A)).symm w‖ ≤ ∑ j, ‖w j‖ := h1
    _ ≤ ∑ j : Fin d, ∑ i : Fin d, ‖v i‖ * ‖M i j‖ := h2
    _ ≤ (∑ j : Fin d, ∑ i : Fin d, ‖M i j‖) * ‖v‖ := h3
    _ = (∑ i : Fin d, ∑ j : Fin d, ‖M i j‖) * ‖v‖ := by rw [Finset.sum_comm]

end GUEStrongConvergence

namespace GUEStrongConvergence

open Filter MeasureTheory FreeProbability FreeProbability.Fock Matrix
open scoped ComplexOrder Topology BigOperators

variable {r d : ℕ}

/-- A degree bound for the words occurring in a matrix polynomial. -/
noncomputable def polyDeg (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r))) : ℕ :=
  ∑ i : Fin d, ∑ j : Fin d,
    (P i j).coeff.support.sup (fun w => (FreeMonoid.toList w).length)

lemma le_polyDeg (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r)))
    {i j : Fin d} {w : FreeMonoid (Fin r)} (hw : w ∈ (P i j).coeff.support) :
    (FreeMonoid.toList w).length ≤ polyDeg P := by
  have hinner : (P i j).coeff.support.sup (fun w => (FreeMonoid.toList w).length) ≤
      ∑ j' : Fin d, (P i j').coeff.support.sup (fun w => (FreeMonoid.toList w).length) :=
    Finset.single_le_sum
      (f := fun j' => (P i j').coeff.support.sup (fun w => (FreeMonoid.toList w).length))
      (fun j' _ => Nat.zero_le _) (Finset.mem_univ j)
  have houter : (∑ j' : Fin d, (P i j').coeff.support.sup
        (fun w => (FreeMonoid.toList w).length)) ≤ polyDeg P :=
    Finset.single_le_sum
      (f := fun i' => ∑ j' : Fin d, (P i' j').coeff.support.sup
        (fun w => (FreeMonoid.toList w).length))
      (fun i' _ => Nat.zero_le _) (Finset.mem_univ i)
  exact (Finset.le_sup hw).trans (hinner.trans houter)

/-- **Lipschitz continuity of matrix-polynomial evaluation** in the coefficient distance,
with the explicit factor `(1 + tupleNorm G) ^ D`. -/
theorem norm_evalMatrixPoly_sub_le {A : Type*} [CStarAlgebra A] [Nontrivial A]
    [PartialOrder A] [StarOrderedRing A]
    (P Q : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r)))
    (G : Fin r → A) {D : ℕ}
    (hD : ∀ i j w, w ∈ (P i j).coeff.support ∪ (Q i j).coeff.support →
      (FreeMonoid.toList w).length ≤ D) :
    ‖evalMatrixPoly P G - evalMatrixPoly Q G‖
      ≤ (1 + tupleNorm G) ^ D * coeffDist P Q := by
  have hsub : evalMatrixPoly P G - evalMatrixPoly Q G = evalMatrixPoly (P - Q) G := by
    ext i j
    change evaluate G (P i j) - evaluate G (Q i j) = evaluate G ((P - Q) i j)
    rw [Matrix.sub_apply, map_sub]
  have ht : 0 ≤ tupleNorm G := tupleNorm_nonneg G
  have hsupp : ∀ i j, ((P - Q) i j).coeff.support
      ⊆ (P i j).coeff.support ∪ (Q i j).coeff.support := by
    intro i j w hw
    rw [Finsupp.mem_support_iff] at hw
    by_contra hmem
    rw [Finset.mem_union, not_or] at hmem
    have hP : (P i j).coeff w = 0 := Finsupp.notMem_support_iff.mp hmem.1
    have hQ : (Q i j).coeff w = 0 := Finsupp.notMem_support_iff.mp hmem.2
    exact hw (by rw [Matrix.sub_apply, MonoidAlgebra.coeff_sub, Finsupp.sub_apply, hP, hQ,
      sub_zero])
  have hterm : ∀ (i j : Fin d) (w : FreeMonoid (Fin r)),
      w ∈ ((P - Q) i j).coeff.support →
      ‖((P - Q) i j).coeff w‖ * (tupleNorm G) ^ (FreeMonoid.toList w).length
        ≤ ‖((P - Q) i j).coeff w‖ * (1 + tupleNorm G) ^ D := by
    intro i j w hw
    have hlen : (FreeMonoid.toList w).length ≤ D := hD i j w (hsupp i j hw)
    have hpow1 : (tupleNorm G) ^ (FreeMonoid.toList w).length
        ≤ (1 + tupleNorm G) ^ (FreeMonoid.toList w).length :=
      pow_le_pow_left₀ ht (by linarith) _
    have hpow2 : (1 + tupleNorm G) ^ (FreeMonoid.toList w).length
        ≤ (1 + tupleNorm G) ^ D :=
      pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + tupleNorm G) hlen
    exact mul_le_mul_of_nonneg_left (hpow1.trans hpow2) (norm_nonneg _)
  rw [hsub]
  calc ‖evalMatrixPoly (P - Q) G‖
      ≤ ∑ i : Fin d, ∑ j : Fin d, ‖evalMatrixPoly (P - Q) G i j‖ :=
        norm_le_sum_norm_entries _
    _ = ∑ i : Fin d, ∑ j : Fin d, ‖evaluate G ((P - Q) i j)‖ := rfl
    _ ≤ ∑ i : Fin d, ∑ j : Fin d, ∑ w ∈ ((P - Q) i j).coeff.support,
          ‖((P - Q) i j).coeff w‖ * (1 + tupleNorm G) ^ D := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        rw [evaluate_eq_support_sum]
        calc ‖∑ w ∈ ((P - Q) i j).coeff.support,
              ((P - Q) i j).coeff w • wordProd G (FreeMonoid.toList w)‖
            ≤ ∑ w ∈ ((P - Q) i j).coeff.support,
                ‖((P - Q) i j).coeff w • wordProd G (FreeMonoid.toList w)‖ :=
              norm_sum_le _ _
          _ ≤ ∑ w ∈ ((P - Q) i j).coeff.support,
                ‖((P - Q) i j).coeff w‖ * (tupleNorm G) ^ (FreeMonoid.toList w).length := by
              apply Finset.sum_le_sum
              intro w _
              rw [norm_smul]
              exact mul_le_mul_of_nonneg_left (norm_wordProd_le G _) (norm_nonneg _)
          _ ≤ ∑ w ∈ ((P - Q) i j).coeff.support,
                ‖((P - Q) i j).coeff w‖ * (1 + tupleNorm G) ^ D := by
              apply Finset.sum_le_sum
              intro w hw
              exact hterm i j w hw
    _ ≤ ∑ i : Fin d, ∑ j : Fin d,
          ∑ w ∈ (P i j).coeff.support ∪ (Q i j).coeff.support,
            ‖((P - Q) i j).coeff w‖ * (1 + tupleNorm G) ^ D := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        apply Finset.sum_le_sum_of_subset_of_nonneg (hsupp i j)
        intro w _ _
        positivity
    _ = ∑ i : Fin d, ∑ j : Fin d,
          ∑ w ∈ (P i j).coeff.support ∪ (Q i j).coeff.support,
            ‖(P i j).coeff w - (Q i j).coeff w‖ * (1 + tupleNorm G) ^ D := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro w _
        rw [Matrix.sub_apply, MonoidAlgebra.coeff_sub, Finsupp.sub_apply]
    _ = (1 + tupleNorm G) ^ D * coeffDist P Q := by
        unfold coeffDist
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w _
        ring

end GUEStrongConvergence

namespace GUEStrongConvergence

open Filter MeasureTheory FreeProbability FreeProbability.Fock Matrix
open scoped ComplexOrder Topology BigOperators

variable {r d : ℕ} [Nonempty (Fin d)] [Nonempty (Fin (d + d))]

local instance polyApproxNontrivial : Nontrivial (closedSemicircularAlgebra (Fin r)) :=
  (closedGeneratedVacuumState (Fin r)).toProbabilitySpace.nontrivial

local instance polyApproxPartialOrder : PartialOrder (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrder _

local instance polyApproxStarOrderedRing : StarOrderedRing (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrderedRing _

lemma polyDeg_ratApproxPoly_le (δ : ℝ)
    (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r))) :
    polyDeg (ratApproxPoly δ P) ≤ polyDeg P := by
  unfold polyDeg
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sup_mono
  exact support_mapCoeffs_subset (ratApproxCoeff δ) (ratApproxCoeff_zero δ) (P i j)

/-- Combined density statement: for every matrix polynomial `P` and every `ε > 0` there
is a `ℚ[i]`-coefficient matrix polynomial `Q` with `coeffDist P Q < ε` and with no larger
degree bound (`polyDeg Q ≤ polyDeg P`). -/
theorem exists_ratApproxPoly_coeffDist_deg
    (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r))) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r)),
      coeffDist P Q < ε ∧ polyDeg Q ≤ polyDeg P ∧
        (∀ i j w, ∃ a b : ℚ, (Q i j).coeff w = (a : ℂ) + (b : ℂ) * Complex.I) := by
  refine ⟨ratApproxPoly (ε / (2 * (coeffCard P + 1))) P,
    coeffDist_ratApproxPoly_lt P hε, ?_, ratApproxPoly_coeff_mem _ P⟩
  exact polyDeg_ratApproxPoly_le _ P

lemma coeffDist_nonneg
    (P Q : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r))) : 0 ≤ coeffDist P Q := by
  unfold coeffDist
  positivity

/-- The semicircular family has `ℓ¹` norm `2 * r`. -/
lemma tupleNorm_semicircularFamily :
    tupleNorm (semicircularFamily r) = 2 * r := by
  unfold tupleNorm semicircularFamily
  simp [FreeProbability.Fock.norm_closedSemicircular]
  ring

/-- **Reduction from a dense countable family to all complex matrix polynomials.**

`Ps` is a countable family of matrix polynomials, dense in the coefficient distance
`coeffDist` *with degree control* (`polyDeg (Ps i) ≤ polyDeg P`).  Assuming

* the scalar edge bound `∀ᶠ N, tupleNorm (G_N(x)) ≤ R` almost surely, and
* a.s. norm convergence for each member of the family,

we obtain a.s. norm convergence simultaneously for *all* complex matrix polynomials.
The proof is the `3ε` argument: for each `P`, approximate it by some `Ps i`, use the
Lipschitz estimate on the GUE side (via the edge bound) and on the semicircular side
(a fixed element), and transfer the convergence. -/
theorem ae_tendsto_norm_of_dense_family
    {ι : Type*} [Countable ι]
    (Ps : ι → Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r)))
    (hDense : ∀ (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r))) (ε : ℝ), 0 < ε →
      ∃ i, coeffDist P (Ps i) < ε ∧ polyDeg (Ps i) ≤ polyDeg P)
    {R : ℝ}
    (hEdge : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      ∀ᶠ (N : ℕ) in atTop, tupleNorm (gueFamily r N x) ≤ R)
    (hconv : ∀ i, ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      Tendsto (fun N : ℕ => ‖evalMatrixPoly (Ps i) (gueFamily r N x)‖) atTop
        (𝓝 ‖evalMatrixPoly (Ps i) (semicircularFamily r)‖)) :
    ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      ∀ P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r)),
        Tendsto (fun N : ℕ => ‖evalMatrixPoly P (gueFamily r N x)‖) atTop
          (𝓝 ‖evalMatrixPoly P (semicircularFamily r)‖) := by
  have hfam : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ i,
      Tendsto (fun N : ℕ => ‖evalMatrixPoly (Ps i) (gueFamily r N x)‖) atTop
        (𝓝 ‖evalMatrixPoly (Ps i) (semicircularFamily r)‖) :=
    ae_all_iff.2 hconv
  filter_upwards [hfam, hEdge] with x hx hR
  intro P
  set t : ℝ := tupleNorm (semicircularFamily r) with htdef
  have ht : 0 ≤ t := tupleNorm_nonneg _
  set B : ℝ := 1 + |R| + t with hBdef
  have hB1 : 1 ≤ B := by
    rw [hBdef]; have := abs_nonneg R; linarith
  set D : ℕ := 2 * polyDeg P with hDdef
  set C : ℝ := B ^ D with hCdef
  have hCn : 0 ≤ C := by positivity
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hδpos : 0 < ε / (3 * (C + 1)) := by positivity
  obtain ⟨i, hdist, hdeg⟩ := hDense P _ hδpos
  have hdegD : ∀ (a b : Fin d) (w : FreeMonoid (Fin r)),
      w ∈ (P a b).coeff.support ∪ (Ps i a b).coeff.support →
        (FreeMonoid.toList w).length ≤ D := by
    intro a b w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · have h1 : (FreeMonoid.toList w).length ≤ polyDeg P := le_polyDeg P hw
      have : polyDeg P ≤ D := by rw [hDdef]; omega
      exact h1.trans this
    · have h1 : (FreeMonoid.toList w).length ≤ polyDeg (Ps i) := le_polyDeg (Ps i) hw
      have h2 : polyDeg (Ps i) ≤ polyDeg P := hdeg
      have : polyDeg P ≤ D := by rw [hDdef]; omega
      exact h1.trans (h2.trans this)
  have hlipN : ∀ N : ℕ, 1 ≤ N → tupleNorm (gueFamily r N x) ≤ R →
      ‖evalMatrixPoly P (gueFamily r N x) - evalMatrixPoly (Ps i) (gueFamily r N x)‖
        ≤ C * coeffDist P (Ps i) := by
    intro N hN hRN
    haveI : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
    have hbase : 1 + tupleNorm (gueFamily r N x) ≤ B := by
      rw [hBdef]
      have hle : tupleNorm (gueFamily r N x) ≤ |R| := hRN.trans (le_abs_self R)
      linarith
    calc ‖evalMatrixPoly P (gueFamily r N x) - evalMatrixPoly (Ps i) (gueFamily r N x)‖
        ≤ (1 + tupleNorm (gueFamily r N x)) ^ D * coeffDist P (Ps i) :=
          norm_evalMatrixPoly_sub_le P (Ps i) _ hdegD
      _ ≤ B ^ D * coeffDist P (Ps i) :=
          mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 + tupleNorm (gueFamily r N x) by
              have := tupleNorm_nonneg (gueFamily r N x); linarith) hbase D)
            (coeffDist_nonneg _ _)
      _ = C * coeffDist P (Ps i) := by rw [hCdef]
  have hlipInf :
      ‖evalMatrixPoly P (semicircularFamily r) - evalMatrixPoly (Ps i) (semicircularFamily r)‖
        ≤ C * coeffDist P (Ps i) := by
    have hbase : 1 + tupleNorm (semicircularFamily r) ≤ B := by
      rw [hBdef]; have := abs_nonneg R; linarith
    calc ‖evalMatrixPoly P (semicircularFamily r) - evalMatrixPoly (Ps i) (semicircularFamily r)‖
        ≤ (1 + tupleNorm (semicircularFamily r)) ^ D * coeffDist P (Ps i) :=
          norm_evalMatrixPoly_sub_le P (Ps i) _ hdegD
      _ ≤ B ^ D * coeffDist P (Ps i) :=
          mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 + tupleNorm (semicircularFamily r) by
              have := tupleNorm_nonneg (semicircularFamily r); linarith) hbase D)
            (coeffDist_nonneg _ _)
      _ = C * coeffDist P (Ps i) := by rw [hCdef]
  have hCeps : C * coeffDist P (Ps i) < ε / 3 := by
    rcases eq_or_lt_of_le hCn with hC0 | hCpos
    · rw [← hC0, zero_mul]; positivity
    · have hstep : C * coeffDist P (Ps i) < C * (ε / (3 * (C + 1))) :=
        mul_lt_mul_of_pos_left hdist hCpos
      have hfinal : C * (ε / (3 * (C + 1))) < ε / 3 := by
        rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
        nlinarith [hCn, hCpos, hε]
      exact hstep.trans hfinal
  have hconvε : ∀ᶠ N : ℕ in atTop,
      dist (‖evalMatrixPoly (Ps i) (gueFamily r N x)‖)
        (‖evalMatrixPoly (Ps i) (semicircularFamily r)‖) < ε / 3 := by
    rcases Metric.tendsto_atTop.1 (hx i) (ε / 3) (by linarith) with ⟨N0, hN0⟩
    exact eventually_atTop.2 ⟨N0, fun n hn => hN0 n hn⟩
  rcases eventually_atTop.1 hR with ⟨NR, hNR⟩
  rcases eventually_atTop.1 hconvε with ⟨NC, hNC⟩
  refine ⟨max (max NR NC) 1, fun N hN => ?_⟩
  have hNR' : NR ≤ N := le_trans (le_trans (le_max_left NR NC) (le_max_left _ _)) hN
  have hNC' : NC ≤ N := le_trans (le_trans (le_max_right NR NC) (le_max_left _ _)) hN
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hRN : tupleNorm (gueFamily r N x) ≤ R := hNR N hNR'
  have hcN : dist (‖evalMatrixPoly (Ps i) (gueFamily r N x)‖)
      (‖evalMatrixPoly (Ps i) (semicircularFamily r)‖) < ε / 3 := hNC N hNC'
  rw [Real.dist_eq]
  have hA : |‖evalMatrixPoly P (gueFamily r N x)‖
        - ‖evalMatrixPoly (Ps i) (gueFamily r N x)‖| < ε / 3 := by
    have hlip := hlipN N hN1 hRN
    exact lt_of_le_of_lt (abs_norm_sub_norm_le _ _) (lt_of_le_of_lt hlip hCeps)
  have hB' : |‖evalMatrixPoly (Ps i) (semicircularFamily r)‖
        - ‖evalMatrixPoly P (semicircularFamily r)‖| < ε / 3 := by
    refine lt_of_le_of_lt ?_ (lt_of_le_of_lt hlipInf hCeps)
    rw [abs_sub_comm]
    exact abs_norm_sub_norm_le _ _
  have hC' : |‖evalMatrixPoly (Ps i) (gueFamily r N x)‖
        - ‖evalMatrixPoly (Ps i) (semicircularFamily r)‖| < ε / 3 := by
    rw [← Real.dist_eq]
    exact hcN
  calc |‖evalMatrixPoly P (gueFamily r N x)‖
        - ‖evalMatrixPoly P (semicircularFamily r)‖|
      ≤ |‖evalMatrixPoly P (gueFamily r N x)‖
          - ‖evalMatrixPoly (Ps i) (gueFamily r N x)‖|
        + |‖evalMatrixPoly (Ps i) (gueFamily r N x)‖
          - ‖evalMatrixPoly P (semicircularFamily r)‖| := abs_sub_le _ _ _
    _ ≤ |‖evalMatrixPoly P (gueFamily r N x)‖
          - ‖evalMatrixPoly (Ps i) (gueFamily r N x)‖|
        + (|‖evalMatrixPoly (Ps i) (gueFamily r N x)‖
            - ‖evalMatrixPoly (Ps i) (semicircularFamily r)‖|
          + |‖evalMatrixPoly (Ps i) (semicircularFamily r)‖
            - ‖evalMatrixPoly P (semicircularFamily r)‖|) := by
        gcongr
        exact abs_sub_le _ _ _
    _ < ε := by linarith

end GUEStrongConvergence
