/-
# Final wiring: deterministic `hB` from the generator bound

This file closes the last two inputs of the conditional assembly in
`StrongConvergence/FinalStatement.lean`:

* **`hB` is deterministic.**  For a fixed matrix word polynomial `P` and generators
  `G : Fin r → BlockAlg e n` with `‖G i‖ ≤ M`, the evaluated dilated block polynomial
  (with the `1/2` coefficients used by the Hermitian-dilation reduction) is bounded by

    `C(P, M) = ∑_{w} ‖coefficient(w)‖ · M^{|w|}`,

  a finite sum over the (finitely many) monomials of `Q`, uniformly in the matrix
  dimension `n`.  The only probabilistic input is the generator bound itself, which is
  supplied by the scalar spectral inclusion (`eventually_norm_gueFamily_le_three_...`,
  giving `M = 3`) or by the `ℓ¹` edge bound `hEdge` (`tupleNorm ≤ R`, giving
  `M = max R 0`).

* **The final conditional theorem.**  Combining

  - the unconditional scalar word-trace convergence
    `ae_all_words_gueNormTrace_tau_unconditional` (`hWords`),
  - the edge bound from scalar spectral inclusion (`hEdge`),
  - the deterministic bound above (`hB`),

  with `ae_tendsto_norm_allD`, we obtain `GUEStrongConvergenceStatement r` under
  **only**

  - `hScalar : ScalarSpectralInclusion r` (the scalar spectral inclusion for the
    individual GUE pencils, the only remaining probabilistic input of the edge bound),
  - `hH1` (the fixed-pencil spectral family inclusion for the canonical dilated data of
    every member of the countable Gaussian-rational family).

  In particular the entire project target is now reduced to `hH1` (target part II.A)
  plus `hScalar`, with no `hB` and no `hWords` left as hypotheses.

## Proof-integrity note

No `sorry`, `admit` or new axioms are used.  The analytic content is confined to the
explicit hypotheses `hScalar` and `hH1`; everything else is a deterministic estimate.
-/
import GUEStrongConvergence.StrongConvergence.FinalStatement
import GUEStrongConvergence.StrongConvergence.CutoffExclusion
import GUEStrongConvergence.StrongConvergence.BlockDiagonalNorm
import GUEStrongConvergence.StrongConvergence.FreeMomentBridgeProof

noncomputable section

namespace GUEStrongConvergence

open Filter MeasureTheory FreeProbability FreeProbability.Fock Matrix
open scoped ComplexOrder Topology BigOperators

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

variable {r : ℕ}

/-! ## Deterministic word-product estimates -/

section WordBounds

variable {B : Type*} [CStarAlgebra B] [Nontrivial B]
variable {I κ : Type*} [Fintype κ] [DecidableEq κ]

/-- A word product in generators bounded by `M` has norm at most `M ^ length`. -/
lemma norm_wordProd_le_of_bound (x : I → B) {M : ℝ} (hM0 : 0 ≤ M)
    (hx : ∀ i, ‖x i‖ ≤ M) (w : List I) :
    ‖wordProd x w‖ ≤ M ^ w.length := by
  induction w with
  | nil =>
      rw [wordProd_nil, List.length_nil, pow_zero]
      exact le_of_eq (CStarRing.norm_one (E := B))
  | cons i w ih =>
      rw [show wordProd x (i :: w) = x i * wordProd x w from rfl,
        List.length_cons, pow_succ']
      exact (norm_mul_le _ _).trans (mul_le_mul (hx i) ih (norm_nonneg _) hM0)

/-- Triangle-inequality bound for the evaluated word polynomial. -/
lemma norm_wordPolyEval_le (x : I → B) (wds : κ → List I) (coeff : κ → B)
    {M : ℝ} (hM0 : 0 ≤ M) (hx : ∀ i, ‖x i‖ ≤ M) :
    ‖wordPolyEval x wds coeff‖ ≤ ∑ k, ‖coeff k‖ * M ^ (wds k).length := by
  unfold wordPolyEval
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  exact (norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_left (norm_wordProd_le_of_bound x hM0 hx (wds k)) (norm_nonneg _))

/-- The self-adjoint polynomial `C + q + q*` at `C = 0` is bounded by twice the
evaluated polynomial. -/
lemma norm_wordPolyEvalC_zero_le (x : I → B) (wds : κ → List I) (coeff : κ → B)
    {M : ℝ} (hM0 : 0 ≤ M) (hx : ∀ i, ‖x i‖ ≤ M) :
    ‖wordPolyEvalC (0 : B) x wds coeff‖
      ≤ (2 : ℝ) * ∑ k, ‖coeff k‖ * M ^ (wds k).length := by
  have hq := norm_wordPolyEval_le x wds coeff hM0 hx
  unfold wordPolyEvalC
  calc ‖0 + wordPolyEval x wds coeff + star (wordPolyEval x wds coeff)‖
      = ‖wordPolyEval x wds coeff + star (wordPolyEval x wds coeff)‖ := by rw [zero_add]
    _ ≤ ‖wordPolyEval x wds coeff‖ + ‖star (wordPolyEval x wds coeff)‖ := norm_add_le _ _
    _ = 2 * ‖wordPolyEval x wds coeff‖ := by rw [norm_star]; ring
    _ ≤ (2 : ℝ) * ∑ k, ‖coeff k‖ * M ^ (wds k).length := by linarith

/-- The `1/2`-scaled coefficients absorb the factor `2` from `q + q*`. -/
lemma norm_wordPolyEvalC_zero_half_le (x : I → B) (wds : κ → List I) (coeff : κ → B)
    {M : ℝ} (hM0 : 0 ≤ M) (hx : ∀ i, ‖x i‖ ≤ M) :
    ‖wordPolyEvalC (0 : B) x wds (fun k => (1 / 2 : ℂ) • coeff k)‖
      ≤ ∑ k, ‖coeff k‖ * M ^ (wds k).length := by
  refine (norm_wordPolyEvalC_zero_le x wds _ hM0 hx).trans ?_
  have h2 : (2 : ℝ) * (∑ k : κ, ‖((1 / 2 : ℂ) • coeff k)‖ * M ^ (wds k).length)
      = ∑ k : κ, ‖coeff k‖ * M ^ (wds k).length := by
    calc (2 : ℝ) * (∑ k : κ, ‖((1 / 2 : ℂ) • coeff k)‖ * M ^ (wds k).length)
        = ∑ k : κ, (2 : ℝ) * (‖((1 / 2 : ℂ) • coeff k)‖ * M ^ (wds k).length) := by
          rw [Finset.mul_sum]
      _ = ∑ k : κ, ‖coeff k‖ * M ^ (wds k).length := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [norm_smul]
          have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
          rw [hhalf]
          ring
  rw [h2]

end WordBounds

/-! ## The norm of a scalar block matrix -/

section ScalarBlockDiag

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {d : ℕ}

/-- The scalar block-diagonal embedding `a ↦ 1_d ⊗ a` (`d` blocks) as a non-unital
star algebra homomorphism. -/
def scalarBlockDiagStarAlgHom : A →⋆ₙₐ[ℂ] CStarMatrix (Fin d) (Fin d) A where
  toFun a := Matrix.scalar (Fin d) a
  map_zero' := map_zero _
  map_add' := map_add _
  map_mul' := map_mul _
  map_smul' c a := by
    ext i j
    change (Matrix.scalar (Fin d) (c • a) : Matrix (Fin d) (Fin d) A) i j
      = (c • (Matrix.scalar (Fin d) a : Matrix (Fin d) (Fin d) A)) i j
    rw [Matrix.smul_apply, Matrix.scalar_apply, Matrix.scalar_apply,
      Matrix.diagonal_apply, Matrix.diagonal_apply]
    by_cases h : i = j <;> simp [h]
  map_star' a := by
    show (Matrix.scalar (Fin d) (star a) : Matrix (Fin d) (Fin d) A)
      = (Matrix.scalar (Fin d) a : Matrix (Fin d) (Fin d) A)ᴴ
    ext i j
    rw [Matrix.conjTranspose_apply, Matrix.scalar_apply, Matrix.scalar_apply,
      Matrix.diagonal_apply, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]

/-- The scalar block-diagonal embedding does not increase the norm. -/
lemma norm_blockDiag_le (a : A) :
    ‖blockDiag (d := d) a‖ ≤ ‖a‖ :=
  NonUnitalStarAlgHom.norm_apply_le
    (φ := scalarBlockDiagStarAlgHom (A := A) (d := d)) a

/-- The scalar block-diagonal embedding is isometric for `d > 0`. -/
lemma norm_blockDiag (hd : 0 < d) (a : A) :
    ‖blockDiag (d := d) a‖ = ‖a‖ := by
  refine le_antisymm (norm_blockDiag_le a) ?_
  let i : Fin d := ⟨0, hd⟩
  calc ‖a‖ = ‖blockDiag (d := d) a i i‖ := by
        rw [blockDiag_eq_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq]
    _ ≤ ‖blockDiag (d := d) a‖ := CStarMatrix.norm_entry_le_norm

end ScalarBlockDiag

/-! ## Coefficient masses of a matrix word polynomial -/

section CoeffMass

variable {d : ℕ}

/-- The `ℓ¹` mass of the coefficient matrix of one monomial, read off from the
scalar coefficients.  This does not depend on the matrix dimension of the ambient
`CStarMatrix`. -/
def polyCoeffMass (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r)))
    (k : polyIdx P) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d, ‖polyC P k i j‖

/-- The deterministic polynomial bound
`C(P, M) = ∑_w ‖coefficient(w)‖ M^{|w|}`, summed over the monomials of `P`. -/
def wordPolyBound (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r))) (M : ℝ) : ℝ :=
  ∑ k : polyIdx P, polyCoeffMass P k * M ^ (polyW P k).length

/-- Norm bound for a coefficient matrix of `polyCoeff`: it is bounded by the scalar
`ℓ¹` mass of the corresponding monomial, uniformly in the inner matrix dimension. -/
lemma norm_polyCoeff_le_mass {d n : ℕ}
    (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r))) (k : polyIdx P) :
    ‖(show CStarMatrix (Fin d) (Fin d)
        (CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ) from
      polyCoeff (A := CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ) P k)‖
      ≤ polyCoeffMass (r := r) P k := by
  refine (norm_le_sum_norm_entries (A := CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ) _).trans ?_
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  simp only [polyCoeff, Matrix.of_apply]
  rw [norm_algebraMap']

end CoeffMass


/-! ## The deterministic `hB` bound for the canonical dilated data -/

section HB

/-- **Deterministic bound for a matrix word polynomial.**  For a fixed matrix word
polynomial `Q`, block-scalar generators bounded by `M`, and the `1/2`-scaled
coefficients of the Hermitian-dilation reduction, the evaluated polynomial is bounded
by `C(Q, M) = ∑_w ‖coefficient(w)‖ M^{|w|}`. -/
theorem norm_wordPolyEvalC_le_bound {e n : ℕ}
    (Q : Matrix (Fin e) (Fin e) (WordPolynomial ℂ (Fin r)))
    (G : Fin r → BlockAlg e n)
    {M : ℝ} (hM0 : 0 ≤ M) (hG : ∀ i, ‖G i‖ ≤ M)
    [Nontrivial (BlockAlg e n)] :
    ‖wordPolyEvalC (0 : BlockAlg e n) G (polyW Q)
        (fun k => (1 / 2 : ℂ) •
          polyCoeff (A := CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ) Q k)‖
      ≤ wordPolyBound (r := r) Q M := by
  refine (norm_wordPolyEvalC_zero_half_le (B := BlockAlg e n) G _ _ hM0 hG).trans ?_
  refine Finset.sum_le_sum fun k _ => ?_
  gcongr
  exact norm_polyCoeff_le_mass (r := r) (d := e) (n := n) Q k

/-- The generator bound `‖G_i‖ ≤ 3` (supplied by the scalar spectral inclusion)
yields the `hB` input of `FinalStatement.lean` with `M = 3`. -/
theorem hB_of_generator_bound
    (hgen : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ᶠ N : ℕ in atTop,
      ∀ i : Fin r, ‖gueFamily r N x i‖ ≤ 3) :
    ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ k : ℕ, ∀ F : RatPolyIdx r (k + 1),
      ∀ᶠ n in atTop,
        ‖wordPolyEvalC (0 : BlockAlg ((k + 1) + (k + 1)) n)
          (blockGUE r ((k + 1) + (k + 1)) x n)
          (polyW (dilationPolyFin (denseFamily r (k + 1) F)))
          (fun j => (1 / 2 : ℂ) •
            polyCoeff (A := CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
              (dilationPolyFin (denseFamily r (k + 1) F)) j)‖
        ≤ wordPolyBound (r := r) (dilationPolyFin (denseFamily r (k + 1) F)) 3 := by
  filter_upwards [hgen] with x hx k F
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hx] with n hn
  refine norm_wordPolyEvalC_le_bound (r := r) (e := (k + 1) + (k + 1)) (n := n)
    (Q := dilationPolyFin (denseFamily r (k + 1) F))
    (G := blockGUE r ((k + 1) + (k + 1)) x n)
    (M := 3) (by norm_num) ?_
  intro i
  change ‖blockDiag (d := (k + 1) + (k + 1)) (gueFamily r (n + 1) x i)‖ ≤ 3
  rw [norm_blockDiag (by positivity : 0 < (k + 1) + (k + 1))]
  exact hn i

/-- **The `hB` input from scalar spectral inclusion**, with the uniform constant
`C(dilationPolyFin (denseFamily r (k+1) F), 3)`. -/
theorem hB_of_scalarSpectralInclusion (h : ScalarSpectralInclusion r) :
    ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ k : ℕ, ∀ F : RatPolyIdx r (k + 1),
      ∀ᶠ n in atTop,
        ‖wordPolyEvalC (0 : BlockAlg ((k + 1) + (k + 1)) n)
          (blockGUE r ((k + 1) + (k + 1)) x n)
          (polyW (dilationPolyFin (denseFamily r (k + 1) F)))
          (fun j => (1 / 2 : ℂ) •
            polyCoeff (A := CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
              (dilationPolyFin (denseFamily r (k + 1) F)) j)‖
        ≤ wordPolyBound (r := r) (dilationPolyFin (denseFamily r (k + 1) F)) 3 :=
  hB_of_generator_bound (r := r)
    (eventually_norm_gueFamily_le_three_of_scalarSpectralInclusion (r := r) h)

/-- **The `hB` input directly from the `ℓ¹` edge bound.**  If `tupleNorm (gueFamily) ≤ R`
eventually almost surely, then the deterministic bound holds with
`M = max R 0` and the same constant uniformly in `x`. -/
theorem hB_of_tupleNorm_le {R : ℝ}
    (hEdge : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      ∀ᶠ (N : ℕ) in atTop, tupleNorm (gueFamily r N x) ≤ R) :
    ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ k : ℕ, ∀ F : RatPolyIdx r (k + 1),
      ∀ᶠ n in atTop,
        ‖wordPolyEvalC (0 : BlockAlg ((k + 1) + (k + 1)) n)
          (blockGUE r ((k + 1) + (k + 1)) x n)
          (polyW (dilationPolyFin (denseFamily r (k + 1) F)))
          (fun j => (1 / 2 : ℂ) •
            polyCoeff (A := CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
              (dilationPolyFin (denseFamily r (k + 1) F)) j)‖
        ≤ wordPolyBound (r := r) (dilationPolyFin (denseFamily r (k + 1) F))
            (max R 0) := by
  filter_upwards [hEdge] with x hx k F
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hx] with n hn
  refine norm_wordPolyEvalC_le_bound (r := r) (e := (k + 1) + (k + 1)) (n := n)
    (Q := dilationPolyFin (denseFamily r (k + 1) F))
    (G := blockGUE r ((k + 1) + (k + 1)) x n)
    (M := max R 0) (le_max_right _ _) ?_
  intro i
  change ‖blockDiag (d := (k + 1) + (k + 1)) (gueFamily r (n + 1) x i)‖ ≤ max R 0
  rw [norm_blockDiag (by positivity : 0 < (k + 1) + (k + 1))]
  exact (norm_le_tupleNorm (gueFamily r (n + 1) x) i).trans (hn.trans (le_max_left _ _))

end HB

/-! ## The final conditional theorem: only `hH1` and scalar spectral inclusion -/

section Final

local instance : Nontrivial (closedSemicircularAlgebra (Fin r)) :=
  (closedGeneratedVacuumState (Fin r)).toProbabilitySpace.nontrivial

local instance : PartialOrder (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrder _

local instance : StarOrderedRing (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrderedRing _

/-- The canonical `hH1` hypothesis: the fixed-pencil spectral family inclusion for the
dilated data of every member of the countable Gaussian-rational family. -/
abbrev H1CanonicalDilated (r : ℕ) : Prop :=
  ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ k : ℕ, ∀ F : RatPolyIdx r (k + 1),
    SpectralFamilyInclusion (B := fun n => BlockAlg ((k + 1) + (k + 1)) n)
      (Binf := BlockLimit r ((k + 1) + (k + 1)))
      (blockSemicircular r ((k + 1) + (k + 1))) (blockGUE r ((k + 1) + (k + 1)) x)
      (polyW (dilationPolyFin (denseFamily r (k + 1) F)))
      (fun n j => (1 / 2 : ℂ) •
        polyCoeff (A := CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
          (dilationPolyFin (denseFamily r (k + 1) F)) j)
      (fun j => (1 / 2 : ℂ) •
        polyCoeff (A := closedSemicircularAlgebra (Fin r))
          (dilationPolyFin (denseFamily r (k + 1) F)) j)
      (fun _ => 0) 0

/-- **The project target from `hH1` and scalar spectral inclusion only.**

All other inputs are now theorems:

* `hWords` is `ae_all_words_gueNormTrace_tau_unconditional` (II.B, unconditional);
* `hEdge` is `eventually_tupleNorm_gueFamily_le_of_scalarSpectralInclusion`;
* `hB` is `hB_of_scalarSpectralInclusion` (deterministic, from the generator bound).

Thus the remaining analytic inputs are precisely `hScalar : ScalarSpectralInclusion r`
and `hH1 : H1CanonicalDilated r` (target part II.A for the canonical dilated data). -/
theorem GUEStrongConvergenceStatement_of_scalarSpectralInclusion
    (hScalar : ScalarSpectralInclusion r) (hH1 : H1CanonicalDilated r) :
    GUEStrongConvergenceStatement r :=
  GUEStrongConvergenceStatement_conditional (r := r)
    (ae_all_words_gueNormTrace_tau_unconditional r)
    (eventually_tupleNorm_gueFamily_le_of_scalarSpectralInclusion (r := r) hScalar)
    (fun k F => wordPolyBound (r := r) (dilationPolyFin (denseFamily r (k + 1) F)) 3)
    hH1
    (hB_of_scalarSpectralInclusion (r := r) hScalar)

/-- Variant of the final theorem taking the edge bound as a hypothesis instead of
scalar spectral inclusion; the deterministic `hB` is then supplied by
`hB_of_tupleNorm_le`. -/
theorem GUEStrongConvergenceStatement_of_hEdge
    {R : ℝ}
    (hEdge : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      ∀ᶠ (N : ℕ) in atTop, tupleNorm (gueFamily r N x) ≤ R)
    (hH1 : H1CanonicalDilated r) :
    GUEStrongConvergenceStatement r :=
  GUEStrongConvergenceStatement_conditional (r := r)
    (ae_all_words_gueNormTrace_tau_unconditional r)
    hEdge
    (fun k F => wordPolyBound (r := r) (dilationPolyFin (denseFamily r (k + 1) F))
      (max R 0))
    hH1
    (hB_of_tupleNorm_le (r := r) hEdge)

end Final

end GUEStrongConvergence
