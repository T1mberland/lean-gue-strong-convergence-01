/-
# The matrix-amplified faithful state `tr_D ⊗ φ`

For a state `φ` on a unital C\*-algebra `A`, the normalized matrix state
`M ↦ |D|⁻¹ ∑ i, φ(M i i)` on `CStarMatrix D D A` is again a state, and it is faithful
whenever `φ` is. This supplies the state needed to apply the faithful moment-norm formula
`‖a‖ = lim_k ψ(a ^ (2k)) ^ (1 / (2k))` to matrix-coefficient polynomial evaluations
`P(x) ∈ M_D(A)`.
-/
import FreeProbability.Algebraic.PositiveExpectation
import GUEStrongConvergence.Analysis.FaithfulMomentNorm
import Mathlib.Analysis.CStarAlgebra.CStarMatrix

noncomputable section

open Filter MeasureTheory Topology FreeProbability
open scoped ComplexOrder ENNReal NNReal Matrix

namespace GUEStrongConvergence

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Multiplying a nonnegative complex number by a nonnegative real scalar stays nonnegative. -/
lemma ofReal_mul_nonneg {c : ℝ} (hc : 0 ≤ c) {z : ℂ} (hz : 0 ≤ z) : 0 ≤ (c : ℂ) * z := by
  obtain ⟨hzre, hzim⟩ := hz
  have hzre' : 0 ≤ z.re := by simpa using hzre
  have hzim' : z.im = 0 := by simpa using hzim.symm
  rw [Complex.nonneg_iff]
  constructor
  · have h : ((c : ℂ) * z).re = c * z.re := by simp [Complex.mul_re, hzim']
    rw [h]
    exact mul_nonneg hc hzre'
  · have h : ((c : ℂ) * z).im = c * z.im := by simp [Complex.mul_im]
    rw [h, hzim', mul_zero]

variable {D : Type*} [Fintype D] [DecidableEq D] [Nonempty D]

/-- The scalar `(card D)⁻¹` is a nonnegative real number. -/
lemma inv_card_eq_ofReal : ((Fintype.card D : ℂ))⁻¹ = ((((Fintype.card D : ℝ))⁻¹ : ℝ) : ℂ) := by
  rw [← Complex.ofReal_natCast (Fintype.card D), ← Complex.ofReal_inv]

/-- The normalized matrix state `tr_D ⊗ φ`: `M ↦ (card D)⁻¹ ∑ i, φ(M i i)`. -/
noncomputable def matrixStarState (φ : StarProbabilitySpace A) :
    StarProbabilitySpace (CStarMatrix D D A) where
  expectation :=
    { toFun := fun M => ((Fintype.card D : ℂ))⁻¹ * ∑ i, φ.expectation (M i i)
      map_add' := by
        intro M N
        simp only [CStarMatrix.add_apply, map_add, Finset.sum_add_distrib, mul_add]
      map_smul' := by
        intro c M
        simp only [CStarMatrix.smul_apply, map_smul, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
        ring }
  map_one := by
    have hcard : ((Fintype.card D : ℂ)) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    change ((Fintype.card D : ℂ))⁻¹ * ∑ i : D, φ.expectation ((1 : Matrix D D A) i i) = 1
    simp only [Matrix.one_apply_eq, φ.expectation_one, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ hcard
  map_star := by
    intro M
    change ((Fintype.card D : ℂ))⁻¹ * ∑ i, φ.expectation (star (M i i))
      = star (((Fintype.card D : ℂ))⁻¹ * ∑ i, φ.expectation (M i i))
    have hstar : star (((Fintype.card D : ℂ))⁻¹) = ((Fintype.card D : ℂ))⁻¹ := by
      rw [inv_card_eq_ofReal]
      simp
    rw [star_mul, star_sum, hstar, mul_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => φ.map_star (M i i)
  positive := by
    intro M
    change 0 ≤ ((Fintype.card D : ℂ))⁻¹ * ∑ i, φ.expectation ((star M * M) i i)
    have hterm : ∀ i : D, 0 ≤ φ.expectation ((star M * M) i i) := by
      intro i
      have hii : (star M * M) i i = ∑ j : D, star (M j i) * M j i := by
        rw [CStarMatrix.mul_apply]
        simp only [CStarMatrix.star_apply]
      rw [hii]
      exact StarProbabilitySpace.expectation_nonneg φ
        (Finset.sum_nonneg fun j _ => star_mul_self_nonneg (M j i))
    have hsum : 0 ≤ ∑ i : D, φ.expectation ((star M * M) i i) :=
      Finset.sum_nonneg fun i _ => hterm i
    rw [inv_card_eq_ofReal]
    exact ofReal_mul_nonneg (by positivity) hsum

/-- The matrix-amplified state is faithful whenever the original state is. -/
theorem matrixStarState_isFaithful (φ : StarProbabilitySpace A)
    (hfaith : IsFaithful φ.toProbabilitySpace) :
    IsFaithful (matrixStarState (D := D) φ).toProbabilitySpace := by
  intro M hM
  have hcard : ((Fintype.card D : ℂ)) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hsum : ∑ i : D, φ.expectation ((star M * M) i i) = 0 := by
    rcases mul_eq_zero.mp hM with h | h
    · exact absurd h (inv_ne_zero hcard)
    · exact h
  -- expand every diagonal entry into a sum of star-squares
  have hexp : ∀ i : D, (∑ j : D, φ.expectation (star (M j i) * M j i))
      = φ.expectation ((star M * M) i i) := by
    intro i
    have hii : (star M * M) i i = ∑ j : D, star (M j i) * M j i := by
      rw [CStarMatrix.mul_apply]
      simp only [CStarMatrix.star_apply]
    rw [hii, map_sum]
  -- all terms are nonnegative, hence each vanishes
  have hnonneg : ∀ i j : D, 0 ≤ φ.expectation (star (M j i) * M j i) := fun i j =>
    φ.positive (M j i)
  have hz : ∀ i j : D, φ.expectation (star (M j i) * M j i) = 0 := by
    intro i j
    have houter : ∀ i : D, (∑ j : D, φ.expectation (star (M j i) * M j i)) = 0 := by
      have hre : (∑ i : D, (∑ j : D, φ.expectation (star (M j i) * M j i)).re) = 0 := by
        have hc : ∀ i : D,
            (∑ j : D, φ.expectation (star (M j i) * M j i)) = φ.expectation ((star M * M) i i) :=
          hexp
        simp only [hc]
        rw [← Complex.re_sum, hsum]
        simp
      have hterm : ∀ i : D, 0 ≤ (∑ j : D, φ.expectation (star (M j i) * M j i)).re := by
        intro i
        rw [Complex.re_sum]
        exact Finset.sum_nonneg fun j _ => (hnonneg i j).1
      have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hterm i)).mp hre
      intro i
      have hri := hall i (Finset.mem_univ i)
      have him : (∑ j : D, φ.expectation (star (M j i) * M j i)).im = 0 := by
        rw [Complex.im_sum]
        exact Finset.sum_eq_zero fun j _ => (hnonneg i j).2.symm
      exact Complex.ext hri him
    have hre : (∑ j : D, (φ.expectation (star (M j i) * M j i)).re) = 0 := by
      rw [← Complex.re_sum, houter i]
      simp
    have hterm : ∀ j : D, 0 ≤ (φ.expectation (star (M j i) * M j i)).re := fun j =>
      (hnonneg i j).1
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hterm j)).mp hre
    exact Complex.ext (hall j (Finset.mem_univ j)) (hnonneg i j).2.symm
  ext i j
  exact hfaith (M i j) (hz j i)

end GUEStrongConvergence
