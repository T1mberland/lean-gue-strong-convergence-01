/-
# Invertibility of the finite-`N` mean and the self-energy error bound

This file completes the finite-`N` half of the Haagerup--Thorbjørnsen self-energy argument: it
proves that the finite-`N` mean `m = gueResolventMean A₀ A z` is invertible, gives an explicit
bound for `frob (m⁻¹)`, and combines this with the mean-centred defect of `HT05FiniteMean` to
obtain the unconditional self-energy error bound

`frob (selfEnergy A₀ A z - z • 1) ≤ C_inv * (im z)⁻⁵ / N²`.

## What is proved here (all unconditional, kernel-checked, no extra axioms)

Write `m = gueResolventMean A₀ A z`, `y = im z > 0`, `K = frob A₀ + ∑ i, frob (A i)`.

1. **The slice identity** (`matVec_pencil_sliceVec`): the pencil applied to `v ⊗ e_k` has
   `(a,k')`-entry `δ_{k'k} ((z - A₀) v)_a - ∑ i, (G_i)_{k'k} ((A i) v)_a`.
2. **The slice second moment** (`integral_normSq_pencil_sliceVec_le`):
   `∫ ∑_j ‖(z - H)(x) (v ⊗ e_k)_j‖² ≤ 4 (‖z‖² + K²) ∑_a ‖v_a‖²`, from the exact GUE
   covariance `integral_normSq_sum_gueMatrix`; there is no loss in `N`.
3. **The per-slice Jensen/Cauchy--Schwarz bound** (`slice_vecNormSq_sq_le_integral_mul`):
   `‖v‖⁴ ≤ (∫ ‖R*(x) (v ⊗ e_k)‖²) · 4 (‖z‖² + K²) ‖v‖²`, from the exact pairing
   `⟨R* w, (z-H) w⟩ = ⟨w, w⟩` (`sum_star_matVec_mulVec_eq`), finite Cauchy--Schwarz and the
   integral Cauchy--Schwarz inequality (`integral_mul_le_sqrt_mul_sqrt_of_nonneg`).
4. **The lower bound on the mean's quadratic form** (`gueResolventMean_qform_im_le`):
   `Im ∑_{u w} conj(v_u) m_{u w} v_w ≤ -(y / (4 (‖z‖² + K²))) ∑_a ‖v_a‖²`.
5. **Invertibility and the inverse bound** (`gueResolventMean_isUnit`,
   `frob_inv_gueResolventMean_le`): `IsUnit m` and
   `frob m⁻¹ ≤ card d · 4 (‖z‖² + K²) / y`, together with the two-sided inverse identities
   `gueResolventMean_mul_inv`, `gueResolventMean_inv_mul` that
   `HT05FiniteMean.selfEnergy_sub_smul_one` needs.
6. **THE PAYOFF** (`frob_selfEnergy_sub_smul_one_le`): unconditionally,
   `frob (selfEnergy A₀ A z - z • 1) ≤ 16 (card d)³ (∑ i, frob(A i)²)² (‖z‖² + K²) N⁻² y⁻⁵`.

The constant is explicit: `C_inv = 16 (card d)³ (∑ i, frob(A i)²)² (‖z‖² + K²)`.  The only
dependence on `Re z` is through `‖z‖² + K²`; on a strip `0 < y < η₀` intersected with
`‖z‖ ≤ R` the bound is `C_inv(R) * y⁻⁵ / N²` with `C_inv(R) = 16 (card d)³ (∑ frob(A i)²)²
(R² + K²)`, which is exactly the hypothesis `hΛ` of
`weightedStripBoundProven_of_comparison_unconditional` (with `Λ N z = selfEnergy A₀ A z`).
-/
import GUEStrongConvergence.StrongConvergence.HT05FiniteMean

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped Matrix.Norms.Elementwise ComplexOrder ENNReal NNReal Topology

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

namespace GUEStrongConvergence

noncomputable section

variable {ι d : Type*} {N : ℕ} [Fintype ι] [Fintype d] [DecidableEq d] [DecidableEq ι]

/-! ## Vector norms indexed by `d` -/

/-- Squared Euclidean norm of a finite complex vector. -/
def vecNormSq {n : Type*} [Fintype n] (v : n → ℂ) : ℝ := ∑ a, ‖v a‖ ^ 2

lemma vecNormSq_nonneg (v : d → ℂ) : 0 ≤ vecNormSq v :=
  Finset.sum_nonneg fun a _ => sq_nonneg _

lemma vecNormSq_eq_zero_iff {v : d → ℂ} : vecNormSq v = 0 ↔ v = 0 := by
  rw [vecNormSq, Finset.sum_eq_zero_iff_of_nonneg (fun a _ => sq_nonneg (‖v a‖))]
  constructor
  · intro h
    funext a
    have h1 : ‖v a‖ ^ 2 = 0 := h a (Finset.mem_univ a)
    have h2 : ‖v a‖ = 0 := by nlinarith [norm_nonneg (v a)]
    exact norm_eq_zero.mp h2
  · intro h
    simp [h]

/-- Frobenius bound for the Euclidean norm of a matrix-vector product. -/
lemma vecNormSq_mulVec_le (M : Matrix d d ℂ) (v : d → ℂ) :
    vecNormSq (M *ᵥ v) ≤ (frob M) ^ 2 * vecNormSq v := by
  have hentry : ∀ a : d, ‖(M *ᵥ v) a‖ ≤ ∑ b, ‖M a b‖ * ‖v b‖ := by
    intro a
    rw [Matrix.mulVec_apply_eq_sum]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => by rw [norm_mul])
  have hcs : ∀ a : d, (∑ b, ‖M a b‖ * ‖v b‖) ^ 2 ≤ (∑ b, ‖M a b‖ ^ 2) * ∑ b, ‖v b‖ ^ 2 :=
    fun a => Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun b => ‖M a b‖) (fun b => ‖v b‖)
  rw [frob_sq, vecNormSq, Finset.sum_mul]
  refine (Finset.sum_le_sum fun a _ => ?_).trans (le_of_eq rfl)
  exact (pow_le_pow_left₀ (norm_nonneg _) (hentry a) 2).trans (hcs a)

/-! ## The slice identity -/

/-- The `d`-vector `(z • 1 - A₀) *ᵥ v`. -/
def blockVec (A₀ : Matrix d d ℂ) (z : ℂ) (v : d → ℂ) : d → ℂ :=
  ((z • (1 : Matrix d d ℂ) - A₀) *ᵥ v)

/-- The `d`-vector `(A i) *ᵥ v`. -/
def coefVec (A : ι → Matrix d d ℂ) (v : d → ℂ) (i : ι) : d → ℂ := ((A i) *ᵥ v)

@[simp] lemma blockVec_apply (A₀ : Matrix d d ℂ) (z : ℂ) (v : d → ℂ) (a : d) :
    blockVec A₀ z v a = z * v a - ∑ b, A₀ a b * v b := by
  rw [blockVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.mulVec_apply_eq_sum]

@[simp] lemma coefVec_apply (A : ι → Matrix d d ℂ) (v : d → ℂ) (i : ι) (a : d) :
    coefVec A v i a = ∑ b, A i a b * v b :=
  Matrix.mulVec_apply_eq_sum ..

/-- Entries of the finite pencil with the coefficient index first. -/
lemma pencil_apply_eq (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (z : ℂ)
    (x : GUECoord ι N → ℝ) (a b : d × Fin N) :
    (algebraMap ℂ (CStarMatrix (d × Fin N) (d × Fin N) ℂ) z - guePencil A₀ A x) a b
      = (if a = b then z else 0) - (A₀ a.1 b.1 * (if a.2 = b.2 then (1 : ℂ) else 0) +
          ∑ i, A i a.1 b.1 * gueMatrix x i a.2 b.2) := by
  rw [CStarMatrix.sub_apply, guePencil, CStarMatrix.ofMatrix_apply, guePencilMatrix_apply,
    Algebra.algebraMap_eq_smul_one, CStarMatrix.smul_apply, CStarMatrix.one_apply, smul_eq_mul,
    Matrix.one_apply]
  by_cases h : a = b <;> simp [h]

/-- **The slice identity**: the pencil applied to `v ⊗ e_k`. -/
theorem matVec_pencil_sliceVec (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (z : ℂ)
    (x : GUECoord ι N → ℝ) (v : d → ℂ) (k : Fin N) (a : d) (k' : Fin N) :
    matVec (algebraMap ℂ (CStarMatrix (d × Fin N) (d × Fin N) ℂ) z - guePencil A₀ A x)
        (sliceVec v k) (a, k')
      = (if k' = k then (1 : ℂ) else 0) * blockVec A₀ z v a
        - ∑ i, gueMatrix x i k' k * coefVec A v i a := by
  classical
  have hX : ∀ (b : d) (l : Fin N),
      (algebraMap ℂ (CStarMatrix (d × Fin N) (d × Fin N) ℂ) z - guePencil A₀ A x) (a, k') (b, l)
        = (if (a, k') = (b, l) then z else 0) - (A₀ a b * (if k' = l then (1 : ℂ) else 0) +
            ∑ i, A i a b * gueMatrix x i k' l) :=
    fun b l => pencil_apply_eq A₀ A z x (a, k') (b, l)
  rw [matVec, Fintype.sum_prod_type]
  have hcollapse : ∀ b : d,
      (∑ l : Fin N, (algebraMap ℂ (CStarMatrix (d × Fin N) (d × Fin N) ℂ) z - guePencil A₀ A x)
          (a, k') (b, l) * sliceVec v k (b, l))
        = (algebraMap ℂ (CStarMatrix (d × Fin N) (d × Fin N) ℂ) z - guePencil A₀ A x)
            (a, k') (b, k) * v b := by
    intro b
    refine (Finset.sum_eq_single k (fun l _ hl => ?_) (fun h => absurd (Finset.mem_univ k) h)).trans ?_
    · simp [sliceVec_apply, hl]
    · simp [sliceVec_apply]
  rw [Finset.sum_congr rfl fun b _ => hcollapse b]
  simp only [hX]
  have hp1 : (∑ b, (if (a, k') = (b, k) then z else 0) * v b)
      = (if k' = k then (1 : ℂ) else 0) * (z * v a) := by
    by_cases hk : k' = k
    · subst hk
      rw [Finset.sum_eq_single a (fun b _ hb => by
          rw [if_neg (fun h => hb (by simpa using (congrArg Prod.fst h).symm)), zero_mul])
        (fun h => absurd (Finset.mem_univ a) h)]
      simp
    · have hne : ∀ b : d, ¬ ((a, k') = (b, k)) := by
        intro b h
        exact hk (by simpa using congrArg Prod.snd h)
      rw [Finset.sum_eq_zero (fun b _ => by rw [if_neg (hne b), zero_mul])]
      simp [hk]
  have hp2 : (∑ b, (A₀ a b * (if k' = k then (1 : ℂ) else 0)) * v b)
      = (if k' = k then (1 : ℂ) else 0) * ∑ b, A₀ a b * v b := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  have hp3 : (∑ b, (∑ i, A i a b * gueMatrix x i k' k) * v b)
      = ∑ i, gueMatrix x i k' k * ∑ b, A i a b * v b := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  have hone : blockVec A₀ z v a = z * v a - ∑ b, A₀ a b * v b :=
    blockVec_apply A₀ z v a
  have hp3' : (∑ i, gueMatrix x i k' k * ∑ b, A i a b * v b)
      = ∑ i, gueMatrix x i k' k * coefVec A v i a := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coefVec_apply]
  have hsplit : ∀ b : d,
      ((if (a, k') = (b, k) then z else 0) -
          (A₀ a b * (if k' = k then (1 : ℂ) else 0) + ∑ i, A i a b * gueMatrix x i k' k)) * v b
        = (if (a, k') = (b, k) then z else 0) * v b
          - (A₀ a b * (if k' = k then (1 : ℂ) else 0)) * v b
          - (∑ i, A i a b * gueMatrix x i k' k) * v b := fun b => by ring
  rw [Finset.sum_congr rfl fun b _ => hsplit b, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, hp1, hp2, hp3, hp3', hone, mul_sub]

/-! ## The second moment of a slice -/

/-- Integrability of the squared norm of a weighted sum of GUE entries. -/
lemma integrable_normSq_sum_gueMatrix (w : ι → ℂ) (a b : Fin N) :
    Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      ‖∑ i, gueMatrix (x : GUECoord ι N → ℝ) i a b * w i‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  have hz : MemLp (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      ∑ i, gueMatrix (x : GUECoord ι N → ℝ) i a b * w i) 2
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
    memLp_finsetSum Finset.univ fun i _ => (memLp_gueMatrix_entry (N := N) i a b).mul_const (w i)
  have h1 : MemLp (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      ‖∑ i, gueMatrix (x : GUECoord ι N → ℝ) i a b * w i‖) 2
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := hz.norm
  have h2 : MemLp (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      ‖∑ i, gueMatrix (x : GUECoord ι N → ℝ) i a b * w i‖ *
      ‖∑ i, gueMatrix (x : GUECoord ι N → ℝ) i a b * w i‖) 1
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
    MemLp.mul (p := 2) (q := 2) (r := 1) h1 h1
  rw [← memLp_one_iff_integrable]
  convert h2 using 2
  simp [pow_two]

/-- The pointwise inequality `‖a - b‖² ≤ 2‖a‖² + 2‖b‖²`. -/
lemma norm_sub_sq_le_two (a b : ℂ) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  nlinarith [norm_sub_le a b, norm_nonneg (a - b), norm_nonneg a, norm_nonneg b,
    sq_nonneg (‖a‖ - ‖b‖)]

/-- **The second moment of one affine slice entry**: the mean of
`‖c - ∑ i, G_{i,ab} w_i‖²` is at most `2‖c‖² + 2 N⁻¹ ∑ i, ‖w_i‖²`. -/
lemma integral_normSq_sub_sum_gue_le (c : ℂ) (w : ι → ℂ) (a b : Fin N) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        ‖c - ∑ i, gueMatrix (x : GUECoord ι N → ℝ) i a b * w i‖ ^ 2
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      ≤ 2 * ‖c‖ ^ 2 + 2 * ((N : ℝ)⁻¹ * ∑ i, ‖w i‖ ^ 2) := by
  have hz : Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      ‖∑ i, gueMatrix (x : GUECoord ι N → ℝ) i a b * w i‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := integrable_normSq_sum_gueMatrix w a b
  have hg : Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      2 * ‖c‖ ^ 2 + 2 * ‖∑ i, gueMatrix (x : GUECoord ι N → ℝ) i a b * w i‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
    (integrable_const _).add (hz.const_mul 2)
  have hle : (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        ‖c - ∑ i, gueMatrix (x : GUECoord ι N → ℝ) i a b * w i‖ ^ 2)
      ≤ᵐ[stdGaussian (EuclideanSpace ℝ (GUECoord ι N))]
      (fun x => 2 * ‖c‖ ^ 2 + 2 * ‖∑ i, gueMatrix (x : GUECoord ι N → ℝ) i a b * w i‖ ^ 2) :=
    Eventually.of_forall fun _ => norm_sub_sq_le_two _ _
  refine (integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _) hg hle).trans ?_
  rw [integral_add (integrable_const _) (hz.const_mul 2), integral_const, probReal_univ,
    integral_const_mul, integral_normSq_sum_gueMatrix]
  simp

/-- **The slice second moment bound**: for `w = v ⊗ e_k`,
`∫ ∑ j, ‖(z - H)(x) w_j‖² ≤ (4‖z‖² + 4 (frob A₀)² + 2 (∑ i, frob (A i))²) ∑ a, ‖v a‖²`. -/
theorem integral_normSq_pencil_sliceVec_le_basic (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (z : ℂ) (v : d → ℂ) (k : Fin N) (hN : 0 < N) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        ∑ j, ‖matVec (algebraMap ℂ (CStarMatrix (d × Fin N) (d × Fin N) ℂ) z -
          guePencil A₀ A (x : GUECoord ι N → ℝ)) (sliceVec v k) j‖ ^ 2
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      ≤ (4 * ‖z‖ ^ 2 + 4 * (frob A₀) ^ 2 + 2 * (∑ i, frob (A i)) ^ 2) * vecNormSq v := by
  classical
  have hint : ∀ (a : d) (k' : Fin N), Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      ‖∑ i, gueMatrix (x : GUECoord ι N → ℝ) i k' k * coefVec A v i a‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
    fun a k' => integrable_normSq_sum_gueMatrix (fun i => coefVec A v i a) k' k
  have hg : Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) => ∑ a : d, ∑ k' : Fin N,
      (2 * ‖(if k' = k then (1 : ℂ) else 0) * blockVec A₀ z v a‖ ^ 2 +
        2 * ‖∑ i, gueMatrix (x : GUECoord ι N → ℝ) i k' k * coefVec A v i a‖ ^ 2))
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
    integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun k' _ =>
      (integrable_const _).add ((hint a k').const_mul 2)
  have hle : (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        ∑ j, ‖matVec (algebraMap ℂ (CStarMatrix (d × Fin N) (d × Fin N) ℂ) z -
          guePencil A₀ A (x : GUECoord ι N → ℝ)) (sliceVec v k) j‖ ^ 2)
      ≤ᵐ[stdGaussian (EuclideanSpace ℝ (GUECoord ι N))]
      (fun x => ∑ a : d, ∑ k' : Fin N,
        (2 * ‖(if k' = k then (1 : ℂ) else 0) * blockVec A₀ z v a‖ ^ 2 +
          2 * ‖∑ i, gueMatrix (x : GUECoord ι N → ℝ) i k' k * coefVec A v i a‖ ^ 2)) := by
    refine Eventually.of_forall fun x => ?_
    simp only
    rw [Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun k' _ => ?_
    rw [matVec_pencil_sliceVec]
    exact norm_sub_sq_le_two _ _
  -- evaluate the integral of the dominating function
  have hgeval : ∫ x : EuclideanSpace ℝ (GUECoord ι N), ∑ a : d, ∑ k' : Fin N,
        (2 * ‖(if k' = k then (1 : ℂ) else 0) * blockVec A₀ z v a‖ ^ 2 +
          2 * ‖∑ i, gueMatrix (x : GUECoord ι N → ℝ) i k' k * coefVec A v i a‖ ^ 2)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      = ∑ a : d, ∑ k' : Fin N,
        (2 * ‖(if k' = k then (1 : ℂ) else 0) * blockVec A₀ z v a‖ ^ 2 +
          2 * ((N : ℝ)⁻¹ * ∑ i, ‖coefVec A v i a‖ ^ 2)) := by
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [integral_finsetSum]
      · refine Finset.sum_congr rfl fun k' _ => ?_
        have hc : ∫ (y : EuclideanSpace ℝ (GUECoord ι N)),
              ‖∑ i, gueMatrix (y : GUECoord ι N → ℝ) i k' k * coefVec A v i a‖ ^ 2
              ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
            = (N : ℝ)⁻¹ * ∑ i, ‖coefVec A v i a‖ ^ 2 :=
          integral_normSq_sum_gueMatrix (fun i => coefVec A v i a) k' k
        rw [integral_add (integrable_const _) ((hint a k').const_mul 2)]
        simp only [integral_const_mul]
        rw [hc]
        simp [integral_const]
      · intro k' _
        exact (integrable_const _).add ((hint a k').const_mul 2)
    · intro a _
      exact integrable_finsetSum _ fun k' _ => (integrable_const _).add ((hint a k').const_mul 2)
  refine (integral_mono_of_nonneg (Eventually.of_forall fun x => ?_) hg hle).trans ?_
  · apply Finset.sum_nonneg
    intro j _
    positivity
  rw [hgeval]
  -- simplify the double sum
  have hdelta : ∀ a : d, (∑ k' : Fin N, 2 * ‖(if k' = k then (1 : ℂ) else 0) *
        blockVec A₀ z v a‖ ^ 2) = 2 * ‖blockVec A₀ z v a‖ ^ 2 := by
    intro a
    have hterm : ∀ k' : Fin N, 2 * ‖(if k' = k then (1 : ℂ) else 0) * blockVec A₀ z v a‖ ^ 2
        = if k' = k then 2 * ‖blockVec A₀ z v a‖ ^ 2 else 0 := by
      intro k'
      by_cases h : k' = k
      · simp [h]
      · simp [h]
    rw [Finset.sum_congr rfl fun k' _ => hterm k', Finset.sum_ite_eq', if_pos (Finset.mem_univ k)]
  have hsecond : ∀ a : d, (∑ _k' : Fin N, 2 * ((N : ℝ)⁻¹ * ∑ i, ‖coefVec A v i a‖ ^ 2))
      = (N : ℝ) * (2 * ((N : ℝ)⁻¹ * ∑ i, ‖coefVec A v i a‖ ^ 2)) := by
    intro a
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hsplit : ∀ a : d, (∑ k' : Fin N,
        (2 * ‖(if k' = k then (1 : ℂ) else 0) * blockVec A₀ z v a‖ ^ 2 +
          2 * ((N : ℝ)⁻¹ * ∑ i, ‖coefVec A v i a‖ ^ 2)))
      = 2 * ‖blockVec A₀ z v a‖ ^ 2 +
        (N : ℝ) * (2 * ((N : ℝ)⁻¹ * ∑ i, ‖coefVec A v i a‖ ^ 2)) := by
    intro a
    rw [Finset.sum_add_distrib, hdelta, hsecond]
  rw [Finset.sum_congr rfl fun a _ => hsplit a]
  -- the first group of terms
  have hblock : ∀ a : d, ‖blockVec A₀ z v a‖ ^ 2
      ≤ 2 * ‖z‖ ^ 2 * ‖v a‖ ^ 2 + 2 * ‖(A₀ *ᵥ v) a‖ ^ 2 := by
    intro a
    rw [blockVec_apply]
    refine (norm_sub_sq_le_two _ _).trans (le_of_eq ?_)
    rw [norm_mul, Matrix.mulVec_apply_eq_sum]
    ring
  have hgrp1 : (∑ a : d, 2 * ‖blockVec A₀ z v a‖ ^ 2)
      ≤ 4 * ‖z‖ ^ 2 * vecNormSq v + 4 * (frob A₀) ^ 2 * vecNormSq v := by
    have hstep : (∑ a : d, 2 * ‖blockVec A₀ z v a‖ ^ 2)
        ≤ ∑ a : d, 2 * (2 * ‖z‖ ^ 2 * ‖v a‖ ^ 2 + 2 * ‖(A₀ *ᵥ v) a‖ ^ 2) :=
      Finset.sum_le_sum fun a _ => by
        have := hblock a
        nlinarith
    refine hstep.trans ?_
    have hmul := vecNormSq_mulVec_le A₀ v
    unfold vecNormSq at hmul ⊢
    have heq : (∑ a : d, 2 * (2 * ‖z‖ ^ 2 * ‖v a‖ ^ 2 + 2 * ‖(A₀ *ᵥ v) a‖ ^ 2))
        = 4 * ‖z‖ ^ 2 * (∑ a : d, ‖v a‖ ^ 2) + 4 * ∑ a : d, ‖(A₀ *ᵥ v) a‖ ^ 2 := by
      rw [show (∑ a : d, 2 * (2 * ‖z‖ ^ 2 * ‖v a‖ ^ 2 + 2 * ‖(A₀ *ᵥ v) a‖ ^ 2))
          = ∑ a : d, (4 * ‖z‖ ^ 2 * ‖v a‖ ^ 2 + 4 * ‖(A₀ *ᵥ v) a‖ ^ 2) from
        Finset.sum_congr rfl fun a _ => by ring]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [heq]
    have h4 : (4 : ℝ) * ∑ a : d, ‖(A₀ *ᵥ v) a‖ ^ 2 ≤ 4 * ((frob A₀) ^ 2 * ∑ a : d, ‖v a‖ ^ 2) := by
      linarith
    linarith
  -- the second group of terms
  have hgrp2 : (∑ a : d, (N : ℝ) * (2 * ((N : ℝ)⁻¹ * ∑ i, ‖coefVec A v i a‖ ^ 2)))
      ≤ 2 * (∑ i, frob (A i)) ^ 2 * vecNormSq v := by
    have hNm : (N : ℝ) * (N : ℝ)⁻¹ = 1 := by
      rw [mul_comm, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN))]
    have hstep : ∀ a : d, (N : ℝ) * (2 * ((N : ℝ)⁻¹ * ∑ i, ‖coefVec A v i a‖ ^ 2))
        = 2 * ∑ i, ‖coefVec A v i a‖ ^ 2 := by
      intro a
      rw [show (N : ℝ) * (2 * ((N : ℝ)⁻¹ * ∑ i, ‖coefVec A v i a‖ ^ 2))
          = 2 * ((N : ℝ) * (N : ℝ)⁻¹) * ∑ i, ‖coefVec A v i a‖ ^ 2 from by ring, hNm]
      ring
    rw [Finset.sum_congr rfl fun a _ => hstep a]
    have hV := vecNormSq_nonneg v
    have hsum : ∀ i : ι, (∑ a : d, ‖coefVec A v i a‖ ^ 2) = vecNormSq (A i *ᵥ v) := by
      intro i
      rw [vecNormSq]
      rfl
    have hcomm : (∑ a : d, ∑ i, ‖coefVec A v i a‖ ^ 2) = ∑ i, ∑ a : d, ‖coefVec A v i a‖ ^ 2 :=
      Finset.sum_comm
    rw [← Finset.mul_sum, hcomm, Finset.sum_congr rfl fun i _ => hsum i]
    have hbound : (∑ i, vecNormSq (A i *ᵥ v)) ≤ ∑ i, (frob (A i)) ^ 2 * vecNormSq v :=
      Finset.sum_le_sum fun i _ => vecNormSq_mulVec_le (A i) v
    have hsq : (∑ i, (frob (A i)) ^ 2) ≤ (∑ i, frob (A i)) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => frob_nonneg (A i))
    have h2 : (∑ i, (frob (A i)) ^ 2 * vecNormSq v) = (∑ i, (frob (A i)) ^ 2) * vecNormSq v :=
      (Finset.sum_mul ..).symm
    rw [h2] at hbound
    nlinarith [hbound, hsq, hV]
  have hfin : (∑ a : d, 2 * ‖blockVec A₀ z v a‖ ^ 2 +
        ∑ a : d, (N : ℝ) * (2 * ((N : ℝ)⁻¹ * ∑ i, ‖coefVec A v i a‖ ^ 2)))
      ≤ (4 * ‖z‖ ^ 2 + 4 * (frob A₀) ^ 2 + 2 * (∑ i, frob (A i)) ^ 2) * vecNormSq v := by
    have hV := vecNormSq_nonneg v
    nlinarith [hgrp1, hgrp2]
  rw [Finset.sum_add_distrib]
  exact hfin

/-- The coefficient size `K = frob A₀ + ∑ i, frob (A i)` controlling the pencil. -/
def frobK (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) : ℝ := frob A₀ + ∑ i, frob (A i)

lemma frobK_nonneg (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) : 0 ≤ frobK A₀ A :=
  add_nonneg (frob_nonneg _) (Finset.sum_nonneg fun i _ => frob_nonneg _)

/-- **The slice second moment bound** in the coefficient-size form: for `w = v ⊗ e_k`,
`∫ ∑ j, ‖(z - H)(x) w_j‖² ≤ 4 (‖z‖² + K²) ∑ a, ‖v a‖²`. -/
theorem integral_normSq_pencil_sliceVec_le (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (z : ℂ) (v : d → ℂ) (k : Fin N) (hN : 0 < N) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        ∑ j, ‖matVec (algebraMap ℂ (CStarMatrix (d × Fin N) (d × Fin N) ℂ) z -
          guePencil A₀ A (x : GUECoord ι N → ℝ)) (sliceVec v k) j‖ ^ 2
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      ≤ 4 * (‖z‖ ^ 2 + (frobK A₀ A) ^ 2) * vecNormSq v := by
  refine (integral_normSq_pencil_sliceVec_le_basic A₀ A z v k hN).trans ?_
  have hA0 := frob_nonneg A₀
  have hB : (0 : ℝ) ≤ ∑ i, frob (A i) := Finset.sum_nonneg fun i _ => frob_nonneg (A i)
  have hV := vecNormSq_nonneg v
  have hkey : 4 * ‖z‖ ^ 2 + 4 * (frob A₀) ^ 2 + 2 * (∑ i, frob (A i)) ^ 2
      ≤ 4 * (‖z‖ ^ 2 + (frobK A₀ A) ^ 2) := by
    unfold frobK
    nlinarith [mul_nonneg hA0 hB, sq_nonneg (∑ i, frob (A i)), sq_nonneg (‖z‖)]
  calc (4 * ‖z‖ ^ 2 + 4 * (frob A₀) ^ 2 + 2 * (∑ i, frob (A i)) ^ 2) * vecNormSq v
      ≤ (4 * (‖z‖ ^ 2 + (frobK A₀ A) ^ 2)) * vecNormSq v :=
        mul_le_mul_of_nonneg_right hkey hV
    _ = 4 * (‖z‖ ^ 2 + (frobK A₀ A) ^ 2) * vecNormSq v := by ring

/-! ## Extraction: from the lower bound on the quadratic form to invertibility -/

/-- A single coordinate is bounded by the squared Euclidean norm. -/
lemma normSq_le_vecNormSq (v : d → ℂ) (a : d) : ‖v a‖ ^ 2 ≤ vecNormSq v :=
  Finset.single_le_sum (f := fun b => ‖v b‖ ^ 2) (fun b _ => sq_nonneg (‖v b‖))
    (Finset.mem_univ a)

/-- The quadratic form of a matrix is the pairing with the matrix-vector product. -/
lemma qform_eq_sum_star_mulVec (m : Matrix d d ℂ) (v : d → ℂ) :
    (∑ u, ∑ w, star (v u) * m u w * v w) = ∑ u, star (v u) * (m *ᵥ v) u := by
  simp only [Matrix.mulVec_apply_eq_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => by ring

/-- **Invertibility from the negative imaginary part of the quadratic form.** -/
theorem isUnit_of_qform_im_le (m : Matrix d d ℂ) {c : ℝ} (hc : 0 < c)
    (h : ∀ v : d → ℂ, (∑ u, ∑ w, star (v u) * m u w * v w).im ≤ -c * vecNormSq v) :
    IsUnit m := by
  have hdet : m.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hmv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    refine hv (vecNormSq_eq_zero_iff.mp (le_antisymm ?_ (vecNormSq_nonneg v)))
    have hq : (∑ u, ∑ w, star (v u) * m u w * v w) = 0 := by
      rw [qform_eq_sum_star_mulVec, hmv]
      simp
    have h1 := h v
    rw [hq] at h1
    simp only [Complex.zero_im] at h1
    nlinarith [vecNormSq_nonneg v]
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_iff_ne_zero.mpr hdet

/-- **Explicit inverse bound from the negative imaginary part of the quadratic form.** -/
theorem frob_inv_le_of_qform_im_le (m : Matrix d d ℂ) {c : ℝ} (hc : 0 < c)
    (h : ∀ v : d → ℂ, (∑ u, ∑ w, star (v u) * m u w * v w).im ≤ -c * vecNormSq v) :
    frob m⁻¹ ≤ (Fintype.card d : ℝ) / c := by
  classical
  have hu := isUnit_of_qform_im_le m hc h
  have hdet : IsUnit m.det := (Matrix.isUnit_iff_isUnit_det (A := m)).mp hu
  have hmul : m * m⁻¹ = 1 := Matrix.mul_nonsing_inv m hdet
  have hentry : ∀ u v : d, ‖m⁻¹ u v‖ ≤ c⁻¹ := by
    intro u v
    set wv : d → ℂ := m⁻¹ *ᵥ (Pi.single v 1) with hwv
    have hmw : m *ᵥ wv = Pi.single v 1 := by
      rw [hwv, Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]
    have hpairsum : (∑ p, star (wv p) * (m *ᵥ wv) p) = star (wv v) := by
      rw [hmw, Finset.sum_eq_single v]
      · simp
      · intro b _ hb
        rw [Pi.single_eq_of_ne hb, mul_zero]
      · intro hb
        exact absurd (Finset.mem_univ v) hb
    have hq : (∑ p, ∑ q, star (wv p) * m p q * wv q) = star (wv v) := by
      rw [qform_eq_sum_star_mulVec, hpairsum]
    have hmain := h wv
    rw [hq] at hmain
    have hstar : (star (wv v)).im = -(wv v).im := by simp
    rw [hstar] at hmain
    have hS : c * vecNormSq wv ≤ ‖wv v‖ := by
      have := Complex.im_le_norm (wv v)
      linarith
    have hSnn := vecNormSq_nonneg wv
    have hSbound : vecNormSq wv ≤ (c⁻¹) ^ 2 := by
      by_cases hS0 : vecNormSq wv = 0
      · rw [hS0]
        positivity
      · have hSpos : 0 < vecNormSq wv := lt_of_le_of_ne hSnn (Ne.symm hS0)
        have h3 : (c * vecNormSq wv) ^ 2 ≤ ‖wv v‖ ^ 2 := by
          nlinarith [hS, mul_nonneg hc.le hSnn, norm_nonneg (wv v)]
        have hsq : c ^ 2 * (vecNormSq wv) ^ 2 ≤ vecNormSq wv := by
          calc c ^ 2 * (vecNormSq wv) ^ 2 = (c * vecNormSq wv) ^ 2 := by ring
            _ ≤ ‖wv v‖ ^ 2 := h3
            _ ≤ vecNormSq wv := normSq_le_vecNormSq wv v
        have h4 : c ^ 2 * vecNormSq wv ≤ 1 := by
          nlinarith [hsq, hSpos]
        have hc2 : 0 < c ^ 2 := by positivity
        have h6 : vecNormSq wv ≤ 1 / c ^ 2 := by
          rw [le_div_iff₀ hc2]
          linarith
        have h7 : (1 : ℝ) / c ^ 2 = (c⁻¹) ^ 2 := by
          rw [inv_pow, one_div]
        rwa [h7] at h6
    have hcoord : m⁻¹ u v = wv u := by
      rw [hwv, Matrix.mulVec_single_one]
      rfl
    rw [hcoord]
    have h8 : ‖wv u‖ ^ 2 ≤ (c⁻¹) ^ 2 := (normSq_le_vecNormSq wv u).trans hSbound
    have h9 := Real.sqrt_le_sqrt h8
    rwa [Real.sqrt_sq (norm_nonneg (wv u)), Real.sqrt_sq (by positivity)] at h9
  have h := frob_le_card_mul_of_entry_le m⁻¹ (fun u v => hentry u v) (by positivity)
  rwa [div_eq_mul_inv]

/-- **Right inverse identity** for a matrix whose quadratic form has a negative imaginary part. -/
theorem mul_inv_eq_one_of_qform_im_le (m : Matrix d d ℂ) {c : ℝ} (hc : 0 < c)
    (h : ∀ v : d → ℂ, (∑ u, ∑ w, star (v u) * m u w * v w).im ≤ -c * vecNormSq v) :
    m * m⁻¹ = 1 :=
  Matrix.mul_nonsing_inv m
    ((Matrix.isUnit_iff_isUnit_det (A := m)).mp (isUnit_of_qform_im_le m hc h))

/-- **Left inverse identity** for a matrix whose quadratic form has a negative imaginary part. -/
theorem inv_mul_eq_one_of_qform_im_le (m : Matrix d d ℂ) {c : ℝ} (hc : 0 < c)
    (h : ∀ v : d → ℂ, (∑ u, ∑ w, star (v u) * m u w * v w).im ≤ -c * vecNormSq v) :
    m⁻¹ * m = 1 :=
  Matrix.nonsing_inv_mul m
    ((Matrix.isUnit_iff_isUnit_det (A := m)).mp (isUnit_of_qform_im_le m hc h))

/-! ## The per-slice Jensen/Cauchy--Schwarz lower bound -/

/-- Matrix-vector products compose. -/
lemma matVec_mul_matVec {n : Type*} [Fintype n] (R S : CStarMatrix n n ℂ) (w : n → ℂ) :
    matVec (R * S) w = matVec R (matVec S w) := by
  funext i
  simp only [matVec, CStarMatrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring

lemma matVec_one {n : Type*} [Fintype n] [DecidableEq n] (w : n → ℂ) :
    matVec (1 : CStarMatrix n n ℂ) w = w := by
  funext i
  simp [matVec, CStarMatrix.one_apply]

/-- Integrability of `‖c - ∑ i, G_{i,ab} w_i‖²`. -/
lemma integrable_normSq_sub_sum_gue (c : ℂ) (w : ι → ℂ) (a b : Fin N) :
    Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      ‖c - ∑ i, gueMatrix (x : GUECoord ι N → ℝ) i a b * w i‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  have hz : MemLp (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      c - ∑ i, gueMatrix (x : GUECoord ι N → ℝ) i a b * w i) 2
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
    MemLp.sub (memLp_const c) (memLp_finsetSum Finset.univ fun i _ =>
      (memLp_gueMatrix_entry (N := N) i a b).mul_const (w i))
  have h1 : MemLp (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      ‖c - ∑ i, gueMatrix (x : GUECoord ι N → ℝ) i a b * w i‖) 2
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := hz.norm
  have h2 : MemLp (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      ‖c - ∑ i, gueMatrix (x : GUECoord ι N → ℝ) i a b * w i‖ *
      ‖c - ∑ i, gueMatrix (x : GUECoord ι N → ℝ) i a b * w i‖) 1
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
    MemLp.mul (p := 2) (q := 2) (r := 1) h1 h1
  rw [← memLp_one_iff_integrable]
  convert h2 using 2
  simp [pow_two]

/-- Integrability of the squared norm of the pencil applied to a slice. -/
lemma integrable_normSq_pencil_sliceVec (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (z : ℂ)
    (v : d → ℂ) (k : Fin N) :
    Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      ∑ j : d × Fin N, ‖matVec (algebraMap ℂ (CStarMatrix (d × Fin N) (d × Fin N) ℂ) z -
        guePencil A₀ A (x : GUECoord ι N → ℝ)) (sliceVec v k) j‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  classical
  have hfun : (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        ∑ j : d × Fin N, ‖matVec (algebraMap ℂ (CStarMatrix (d × Fin N) (d × Fin N) ℂ) z -
          guePencil A₀ A (x : GUECoord ι N → ℝ)) (sliceVec v k) j‖ ^ 2)
      = fun x : EuclideanSpace ℝ (GUECoord ι N) => ∑ a : d, ∑ k' : Fin N,
          ‖(if k' = k then (1 : ℂ) else 0) * blockVec A₀ z v a -
            ∑ i, gueMatrix (x : GUECoord ι N → ℝ) i k' k * coefVec A v i a‖ ^ 2 := by
    funext x
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k' _ => by
      rw [matVec_pencil_sliceVec]
  rw [hfun]
  exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun k' _ =>
    integrable_normSq_sub_sum_gue _ _ _ _

/-- Continuity of an entry of the pencil. -/
lemma continuous_guePencil_entry_euclid (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (a b : d × Fin N) :
    Continuous (fun x : EuclideanSpace ℝ (GUECoord ι N) => guePencil A₀ A (x : GUECoord ι N → ℝ) a b) := by
  have h := (continuous_apply b).comp ((continuous_apply a).comp (continuous_guePencilMatrix (N := N) A₀ A))
  have heq : (fun x : EuclideanSpace ℝ (GUECoord ι N) => guePencil A₀ A (x : GUECoord ι N → ℝ) a b)
      = fun x : EuclideanSpace ℝ (GUECoord ι N) => guePencilMatrix A₀ A (x : GUECoord ι N → ℝ) a b := by
    funext x
    rw [guePencil, CStarMatrix.ofMatrix_apply]
  rw [heq]
  exact h

/-- Continuity of the squared Hilbert--Schmidt norm of the pencil applied to a slice. -/
lemma continuous_normSq_pencil_sliceVec (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (z : ℂ)
    (v : d → ℂ) (k : Fin N) :
    Continuous (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      ∑ j : d × Fin N, ‖matVec (algebraMap ℂ (CStarMatrix (d × Fin N) (d × Fin N) ℂ) z -
        guePencil A₀ A (x : GUECoord ι N → ℝ)) (sliceVec v k) j‖ ^ 2) := by
  classical
  have hcont_entry : ∀ j : d × Fin N, Continuous (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      matVec (algebraMap ℂ (CStarMatrix (d × Fin N) (d × Fin N) ℂ) z -
        guePencil A₀ A (x : GUECoord ι N → ℝ)) (sliceVec v k) j) := by
    intro j
    have hfun : (fun x : EuclideanSpace ℝ (GUECoord ι N) => matVec (algebraMap ℂ
          (CStarMatrix (d × Fin N) (d × Fin N) ℂ) z - guePencil A₀ A (x : GUECoord ι N → ℝ))
          (sliceVec v k) j)
        = fun x : EuclideanSpace ℝ (GUECoord ι N) => ∑ b, ((algebraMap ℂ (CStarMatrix (d × Fin N) (d × Fin N) ℂ) z) j b -
            guePencil A₀ A (x : GUECoord ι N → ℝ) j b) * sliceVec v k b := by
      funext x
      rw [matVec]
      exact Finset.sum_congr rfl fun b _ => by rw [CStarMatrix.sub_apply]
    rw [hfun]
    exact continuous_finsetSum _ fun b _ =>
      (continuous_const.sub (continuous_guePencil_entry_euclid A₀ A j b)).mul continuous_const
  exact continuous_finsetSum _ fun j _ => ((hcont_entry j).norm).pow 2

/-- Continuity of the squared Hilbert--Schmidt norm of the resolvent applied to a slice. -/
lemma continuous_normSq_matVec_star (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (z : ℂ) (hz : z.im ≠ 0)
    (w : d × Fin N → ℂ) :
    Continuous (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      ∑ j, ‖matVec (star (guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z)) w j‖ ^ 2) := by
  classical
  have hcont_entry : ∀ j : d × Fin N, Continuous (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      matVec (star (guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z)) w j) := by
    intro j
    have hfun : (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        matVec (star (guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z)) w j)
        = fun x : EuclideanSpace ℝ (GUECoord ι N) => ∑ b, star (guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z b j) * w b := by
      funext x
      rw [matVec]
      exact Finset.sum_congr rfl fun b _ => by rw [CStarMatrix.star_apply]
    rw [hfun]
    exact continuous_finsetSum _ fun b _ =>
      ((continuous_guePencilResolvent_entry_euclid A₀ A hA₀ hA z hz b j).star).mul continuous_const
  exact continuous_finsetSum _ fun j _ => ((hcont_entry j).norm).pow 2

/-- **The Stieltjes pairing for the finite resolvent**: `⟨R* w, (z - H) w⟩ = ⟨w, w⟩`. -/
theorem sum_star_matVec_mulVec_eq (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (x : GUECoord ι N → ℝ) (z : ℂ) (hz : z.im ≠ 0) (w : d × Fin N → ℂ) :
    (∑ p, star (matVec (star (guePencilResolvent A₀ A x z)) w p) *
        matVec (algebraMap ℂ (CStarMatrix (d × Fin N) (d × Fin N) ℂ) z - guePencil A₀ A x) w p)
      = ((∑ p, ‖w p‖ ^ 2 : ℝ) : ℂ) := by
  classical
  set R := guePencilResolvent A₀ A x z with hR
  set X := (algebraMap ℂ (CStarMatrix (d × Fin N) (d × Fin N) ℂ) z - guePencil A₀ A x) with hX
  have hRX : R * X = 1 := resolvent_mul_guePencil_sub A₀ A hA₀ hA x z hz
  -- step 1: conjugate of `R* w`
  have hstep1 : ∀ p, star (matVec (star R) w p) = ∑ b, R b p * star (w b) := by
    intro p
    rw [matVec, star_sum]
    exact Finset.sum_congr rfl fun b _ => by
      rw [star_mul, CStarMatrix.star_apply, star_star, mul_comm]
  calc (∑ p, star (matVec (star R) w p) * matVec X w p)
      = ∑ p, ∑ b, R b p * star (w b) * matVec X w p := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [hstep1 p, Finset.sum_mul]
    _ = ∑ b, star (w b) * ∑ p, R b p * matVec X w p := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => by ring
    _ = ∑ b, star (w b) * matVec R (matVec X w) b := by
        rfl
    _ = ∑ b, star (w b) * w b := by
        have hmat : matVec R (matVec X w) = w := by
          rw [← matVec_mul_matVec, hRX, matVec_one]
        rw [hmat]
    _ = ((∑ p, ‖w p‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.ofReal_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- **Pointwise Jensen form**: `‖w‖² ≤ ‖R* w‖ ‖(z - H) w‖` (with the squared Hilbert--Schmidt
norms `‖ · ‖` on the right). -/
theorem vecNormSq_le_sqrt_mul_sqrt (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (x : GUECoord ι N → ℝ) (z : ℂ) (hz : z.im ≠ 0) (w : d × Fin N → ℂ) :
    (∑ p, ‖w p‖ ^ 2 : ℝ) ≤ Real.sqrt (∑ j, ‖matVec (star (guePencilResolvent A₀ A x z)) w j‖ ^ 2) *
      Real.sqrt (∑ j, ‖matVec (algebraMap ℂ (CStarMatrix (d × Fin N) (d × Fin N) ℂ) z -
        guePencil A₀ A x) w j‖ ^ 2) := by
  have hid := sum_star_matVec_mulVec_eq A₀ A hA₀ hA x z hz w
  have hnorm : (∑ p, ‖w p‖ ^ 2 : ℝ)
      = ‖∑ p, star (matVec (star (guePencilResolvent A₀ A x z)) w p) *
          matVec (algebraMap ℂ (CStarMatrix (d × Fin N) (d × Fin N) ℂ) z - guePencil A₀ A x) w p‖ := by
    rw [hid, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact Finset.sum_nonneg fun p _ => sq_nonneg _
  rw [hnorm]
  refine (norm_sum_le _ _).trans ?_
  have h2 : (∑ p, ‖star (matVec (star (guePencilResolvent A₀ A x z)) w p) *
        matVec (algebraMap ℂ (CStarMatrix (d × Fin N) (d × Fin N) ℂ) z - guePencil A₀ A x) w p‖)
      = ∑ p, ‖matVec (star (guePencilResolvent A₀ A x z)) w p‖ *
          ‖matVec (algebraMap ℂ (CStarMatrix (d × Fin N) (d × Fin N) ℂ) z - guePencil A₀ A x) w p‖ := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [norm_mul, norm_star]
  rw [h2]
  exact Real.sum_mul_le_sqrt_mul_sqrt Finset.univ _ _

/-- **Cauchy--Schwarz for the Gaussian integral** of two nonnegative `L²` functions. -/
lemma integral_mul_le_sqrt_mul_sqrt_of_nonneg
    {f g : EuclideanSpace ℝ (GUECoord ι N) → ℝ} (hf0 : 0 ≤ᵐ[stdGaussian (EuclideanSpace ℝ (GUECoord ι N))] f)
    (hg0 : 0 ≤ᵐ[stdGaussian (EuclideanSpace ℝ (GUECoord ι N))] g)
    (hf : MemLp f 2 (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
    (hg : MemLp g 2 (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) :
    ∫ x, f x * g x ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      ≤ Real.sqrt (∫ x, f x ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) *
        Real.sqrt (∫ x, g x ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
    (p := 2) (q := 2) Real.HolderConjugate.two_two hf0 hg0 (by simpa using hf) (by simpa using hg)
  refine h.trans_eq ?_
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  norm_num

/-- The squared Hilbert--Schmidt norm of the resolvent applied to the slice `v ⊗ e_k`. -/
abbrev sliceResNormSq (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (z : ℂ) (v : d → ℂ) (k : Fin N)
    (x : EuclideanSpace ℝ (GUECoord ι N)) : ℝ :=
  ∑ j, ‖matVec (star (guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z)) (sliceVec v k) j‖ ^ 2

/-- The squared Hilbert--Schmidt norm of `(z - H(x))` applied to the slice `v ⊗ e_k`. -/
abbrev slicePencilNormSq (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (z : ℂ) (v : d → ℂ)
    (k : Fin N) (x : EuclideanSpace ℝ (GUECoord ι N)) : ℝ :=
  ∑ j, ‖matVec (algebraMap ℂ (CStarMatrix (d × Fin N) (d × Fin N) ℂ) z -
    guePencil A₀ A (x : GUECoord ι N → ℝ)) (sliceVec v k) j‖ ^ 2

/-- **The per-slice Jensen/Cauchy--Schwarz lower bound**:
`‖v‖⁴ ≤ (∫ ‖R* (v ⊗ e_k)‖²) · 4 (‖z‖² + K²) ‖v‖²`. -/
theorem slice_vecNormSq_sq_le_integral_mul (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (hN : 0 < N) (v : d → ℂ) (k : Fin N) :
    vecNormSq v ^ 2 ≤
      (∫ x, sliceResNormSq A₀ A z v k x ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) *
        (4 * (‖z‖ ^ 2 + (frobK A₀ A) ^ 2) * vecNormSq v) := by
  classical
  have hz' : z.im ≠ 0 := ne_of_gt hz
  have hSnn : 0 ≤ vecNormSq v := vecNormSq_nonneg v
  have hAnn : ∀ x, 0 ≤ sliceResNormSq A₀ A z v k x := fun x =>
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have hBnn : ∀ x, 0 ≤ slicePencilNormSq A₀ A z v k x := fun x =>
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have hintA : Integrable (sliceResNormSq A₀ A z v k)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    simpa [sliceResNormSq] using
      integrable_sum_normSq_matVec_star A₀ A hA₀ hA z hz hN (sliceVec v k)
  have hintB : Integrable (slicePencilNormSq A₀ A z v k)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    simpa [slicePencilNormSq] using integrable_normSq_pencil_sliceVec A₀ A z v k
  have hcontA : Continuous (sliceResNormSq A₀ A z v k) := by
    simpa [sliceResNormSq] using continuous_normSq_matVec_star A₀ A hA₀ hA z hz' (sliceVec v k)
  have hcontB : Continuous (slicePencilNormSq A₀ A z v k) := by
    simpa [slicePencilNormSq] using continuous_normSq_pencil_sliceVec A₀ A z v k
  have hmemA : MemLp (fun x => Real.sqrt (sliceResNormSq A₀ A z v k x)) 2
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    refine (memLp_two_iff_integrable_sq
      ((Real.continuous_sqrt.comp hcontA).aestronglyMeasurable)).mpr ?_
    convert hintA using 1
    funext x
    exact Real.sq_sqrt (hAnn x)
  have hmemB : MemLp (fun x => Real.sqrt (slicePencilNormSq A₀ A z v k x)) 2
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    refine (memLp_two_iff_integrable_sq
      ((Real.continuous_sqrt.comp hcontB).aestronglyMeasurable)).mpr ?_
    convert hintB using 1
    funext x
    exact Real.sq_sqrt (hBnn x)
  have hpt : ∀ x, vecNormSq v ≤ Real.sqrt (sliceResNormSq A₀ A z v k x) *
      Real.sqrt (slicePencilNormSq A₀ A z v k x) := by
    intro x
    have h := vecNormSq_le_sqrt_mul_sqrt A₀ A hA₀ hA (x : GUECoord ι N → ℝ) z hz' (sliceVec v k)
    rw [sum_normSq_sliceVec] at h
    simpa [sliceResNormSq, slicePencilNormSq, vecNormSq] using h
  have hCS := integral_mul_le_sqrt_mul_sqrt_of_nonneg
    (f := fun x => Real.sqrt (sliceResNormSq A₀ A z v k x))
    (g := fun x => Real.sqrt (slicePencilNormSq A₀ A z v k x))
    (Eventually.of_forall fun _ => Real.sqrt_nonneg _)
    (Eventually.of_forall fun _ => Real.sqrt_nonneg _) hmemA hmemB
  have hCS' : (∫ x, Real.sqrt (sliceResNormSq A₀ A z v k x) *
        Real.sqrt (slicePencilNormSq A₀ A z v k x)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
      ≤ Real.sqrt (∫ x, sliceResNormSq A₀ A z v k x
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) *
        Real.sqrt (∫ x, slicePencilNormSq A₀ A z v k x
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) := by
    refine hCS.trans (le_of_eq ?_)
    have e1 : (∫ x, Real.sqrt (sliceResNormSq A₀ A z v k x) ^ 2
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) =
        ∫ x, sliceResNormSq A₀ A z v k x ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
      integral_congr_ae (Eventually.of_forall fun x => Real.sq_sqrt (hAnn x))
    have e2 : (∫ x, Real.sqrt (slicePencilNormSq A₀ A z v k x) ^ 2
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) =
        ∫ x, slicePencilNormSq A₀ A z v k x ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
      integral_congr_ae (Eventually.of_forall fun x => Real.sq_sqrt (hBnn x))
    rw [e1, e2]
  have hstep1 : vecNormSq v ≤ ∫ x, Real.sqrt (sliceResNormSq A₀ A z v k x) *
      Real.sqrt (slicePencilNormSq A₀ A z v k x)
      ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    have hg : Integrable (fun x => Real.sqrt (sliceResNormSq A₀ A z v k x) *
        Real.sqrt (slicePencilNormSq A₀ A z v k x))
        (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
      rw [← memLp_one_iff_integrable]
      exact MemLp.mul (p := 2) (q := 2) (r := 1) hmemA hmemB
    have h := integral_mono_of_nonneg (f := fun _ => vecNormSq v)
      (g := fun x => Real.sqrt (sliceResNormSq A₀ A z v k x) *
        Real.sqrt (slicePencilNormSq A₀ A z v k x))
      (Eventually.of_forall fun _ => hSnn) hg (Eventually.of_forall hpt)
    rwa [integral_const, probReal_univ, one_smul] at h
  have hBle : (∫ x, slicePencilNormSq A₀ A z v k x
      ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
      ≤ 4 * (‖z‖ ^ 2 + (frobK A₀ A) ^ 2) * vecNormSq v := by
    simpa [slicePencilNormSq] using integral_normSq_pencil_sliceVec_le A₀ A z v k hN
  have hkey : vecNormSq v ≤ Real.sqrt (∫ x, sliceResNormSq A₀ A z v k x
      ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) *
        Real.sqrt (4 * (‖z‖ ^ 2 + (frobK A₀ A) ^ 2) * vecNormSq v) := by
    refine hstep1.trans (hCS'.trans ?_)
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hBle) (Real.sqrt_nonneg _)
  have hAint_nn : 0 ≤ ∫ x, sliceResNormSq A₀ A z v k x
      ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
    integral_nonneg fun x => hAnn x
  have hC_nn : 0 ≤ 4 * (‖z‖ ^ 2 + (frobK A₀ A) ^ 2) * vecNormSq v := by
    have := frobK_nonneg A₀ A
    positivity
  have hsq : vecNormSq v ^ 2 ≤ (Real.sqrt (∫ x, sliceResNormSq A₀ A z v k x
      ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) *
        Real.sqrt (4 * (‖z‖ ^ 2 + (frobK A₀ A) ^ 2) * vecNormSq v)) ^ 2 :=
    pow_le_pow_left₀ hSnn hkey 2
  rw [mul_pow, Real.sq_sqrt hAint_nn, Real.sq_sqrt hC_nn] at hsq
  exact hsq

/-- **The explicit lower bound on the negative imaginary part of the mean's quadratic form**:
`Im ∑_{u w} conj(v_u) m_{u w} v_w ≤ -(im z / (4 (‖z‖² + K²))) ∑_a ‖v_a‖²`. -/
theorem gueResolventMean_qform_im_le (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (hN : 0 < N) (v : d → ℂ) :
    (∑ u, ∑ w, star (v u) * gueResolventMean (N := N) A₀ A z u w * v w).im
      ≤ -(z.im / (4 * (‖z‖ ^ 2 + (frobK A₀ A) ^ 2))) * vecNormSq v := by
  classical
  have hCpos : 0 < 4 * (‖z‖ ^ 2 + (frobK A₀ A) ^ 2) := by
    have hK := frobK_nonneg A₀ A
    have hzpos : 0 < ‖z‖ := by
      refine norm_pos_iff.mpr ?_
      intro h
      rw [h] at hz
      simp at hz
    have : 0 < ‖z‖ ^ 2 := by positivity
    nlinarith
  have hSnn : 0 ≤ vecNormSq v := vecNormSq_nonneg v
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  rw [gueResolventMean_qform_im A₀ A hA₀ hA z hz hN v]
  by_cases hS0 : vecNormSq v = 0
  · have hv : v = 0 := vecNormSq_eq_zero_iff.mp hS0
    subst hv
    have h1 : 0 ≤ ∑ k : Fin N, ∫ x, sliceResNormSq A₀ A z (0 : d → ℂ) k x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
      Finset.sum_nonneg fun k _ => integral_nonneg fun _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    have h2 : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
    have h3 : vecNormSq (0 : d → ℂ) = 0 := by simp [vecNormSq]
    have h4 : (0 : ℝ) ≤ z.im * (N : ℝ)⁻¹ *
        ∑ k : Fin N, ∫ x, sliceResNormSq A₀ A z (0 : d → ℂ) k x
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
      have := mul_nonneg (mul_nonneg hz.le h2) h1
      linarith
    simp only [h3, mul_zero, neg_zero]
    linarith
  · have hSpos : 0 < vecNormSq v := lt_of_le_of_ne hSnn (Ne.symm hS0)
    have hint_nn : ∀ k : Fin N, 0 ≤ ∫ x, sliceResNormSq A₀ A z v k x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := fun k =>
      integral_nonneg fun _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    -- per-slice lower bound after division
    have hslice : ∀ k : Fin N,
        vecNormSq v / (4 * (‖z‖ ^ 2 + (frobK A₀ A) ^ 2))
          ≤ ∫ x, sliceResNormSq A₀ A z v k x ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
      intro k
      have hk := slice_vecNormSq_sq_le_integral_mul A₀ A hA₀ hA z hz hN v k
      have hIk := hint_nn k
      rw [div_le_iff₀ hCpos]
      nlinarith [hk, hSpos, hIk, mul_pos hSpos hSpos]
    have hsum_ge : (N : ℝ) * (vecNormSq v / (4 * (‖z‖ ^ 2 + (frobK A₀ A) ^ 2)))
        ≤ ∑ k : Fin N, ∫ x, sliceResNormSq A₀ A z v k x
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
      calc (N : ℝ) * (vecNormSq v / (4 * (‖z‖ ^ 2 + (frobK A₀ A) ^ 2)))
          = ∑ _k : Fin N, vecNormSq v / (4 * (‖z‖ ^ 2 + (frobK A₀ A) ^ 2)) := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum fun k _ => hslice k
    have hNin : ((N : ℝ)⁻¹) * (N : ℝ) = 1 := inv_mul_cancel₀ (ne_of_gt hNpos)
    have hstep : z.im * (vecNormSq v / (4 * (‖z‖ ^ 2 + (frobK A₀ A) ^ 2)))
        ≤ z.im * (N : ℝ)⁻¹ * ∑ k : Fin N, ∫ x, sliceResNormSq A₀ A z v k x
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
      have hA : vecNormSq v / (4 * (‖z‖ ^ 2 + (frobK A₀ A) ^ 2))
          ≤ ((N : ℝ)⁻¹) * ∑ k : Fin N, ∫ x, sliceResNormSq A₀ A z v k x
              ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
        have h := mul_le_mul_of_nonneg_left hsum_ge (show (0 : ℝ) ≤ (N : ℝ)⁻¹ by positivity)
        rw [← mul_assoc, hNin, one_mul] at h
        exact h
      calc z.im * (vecNormSq v / (4 * (‖z‖ ^ 2 + (frobK A₀ A) ^ 2)))
          ≤ z.im * (((N : ℝ)⁻¹) * ∑ k : Fin N, ∫ x, sliceResNormSq A₀ A z v k x
              ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) :=
            mul_le_mul_of_nonneg_left hA hz.le
        _ = z.im * (N : ℝ)⁻¹ * ∑ k : Fin N, ∫ x, sliceResNormSq A₀ A z v k x
              ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by ring
    have hfinal : -(z.im * (N : ℝ)⁻¹ * ∑ k : Fin N, ∫ x, sliceResNormSq A₀ A z v k x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
        ≤ -(z.im / (4 * (‖z‖ ^ 2 + (frobK A₀ A) ^ 2))) * vecNormSq v := by
      have h3 : (z.im / (4 * (‖z‖ ^ 2 + (frobK A₀ A) ^ 2))) * vecNormSq v
          ≤ z.im * (N : ℝ)⁻¹ * ∑ k : Fin N, ∫ x, sliceResNormSq A₀ A z v k x
              ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
        have h4 : z.im * (vecNormSq v / (4 * (‖z‖ ^ 2 + (frobK A₀ A) ^ 2)))
            = (z.im / (4 * (‖z‖ ^ 2 + (frobK A₀ A) ^ 2))) * vecNormSq v := by ring
        rw [← h4]
        exact hstep
      nlinarith [h3]
    linarith [hfinal]

/-- `frob (-M) = frob M`. -/
lemma frob_neg_eq (M : Matrix d d ℂ) : frob (-M) = frob M := by
  have h : (frob (-M)) ^ 2 = (frob M) ^ 2 := by
    rw [frob_sq, frob_sq]
    simp only [Matrix.neg_apply, norm_neg]
  nlinarith [frob_nonneg M, frob_nonneg (-M)]

/-- **The mean's invertibility**, unconditionally. -/
theorem gueResolventMean_isUnit (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (hN : 0 < N) :
    IsUnit (gueResolventMean (N := N) A₀ A z) := by
  have hK := frobK_nonneg A₀ A
  have hzpos : 0 < ‖z‖ := by
    refine norm_pos_iff.mpr ?_
    intro h
    rw [h] at hz
    simp at hz
  have hCpos : 0 < 4 * (‖z‖ ^ 2 + (frobK A₀ A) ^ 2) := by
    nlinarith [sq_nonneg ‖z‖, sq_nonneg (‖z‖ - frobK A₀ A), norm_nonneg z]
  have hc : 0 < z.im / (4 * (‖z‖ ^ 2 + (frobK A₀ A) ^ 2)) := div_pos hz hCpos
  exact isUnit_of_qform_im_le _ hc (gueResolventMean_qform_im_le A₀ A hA₀ hA z hz hN)

/-- **Explicit inverse bound for the finite mean**:
`frob m⁻¹ ≤ card d · 4 (‖z‖² + K²) / im z`. -/
theorem frob_inv_gueResolventMean_le (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (hN : 0 < N) :
    frob (gueResolventMean (N := N) A₀ A z)⁻¹
      ≤ (Fintype.card d : ℝ) * (4 * (‖z‖ ^ 2 + (frobK A₀ A) ^ 2)) * (z.im)⁻¹ := by
  have hK := frobK_nonneg A₀ A
  have hzpos : 0 < ‖z‖ := by
    refine norm_pos_iff.mpr ?_
    intro h
    rw [h] at hz
    simp at hz
  have hCpos : 0 < 4 * (‖z‖ ^ 2 + (frobK A₀ A) ^ 2) := by
    nlinarith [sq_nonneg ‖z‖, sq_nonneg (‖z‖ - frobK A₀ A), norm_nonneg z]
  have hc : 0 < z.im / (4 * (‖z‖ ^ 2 + (frobK A₀ A) ^ 2)) := div_pos hz hCpos
  refine (frob_inv_le_of_qform_im_le _ hc
    (gueResolventMean_qform_im_le A₀ A hA₀ hA z hz hN)).trans (le_of_eq ?_)
  rw [div_div_eq_mul_div, div_eq_mul_inv]

/-- **Right inverse identity for the finite mean**, unconditionally. -/
theorem gueResolventMean_mul_inv (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (hN : 0 < N) :
    gueResolventMean (N := N) A₀ A z * (gueResolventMean (N := N) A₀ A z)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det (A := gueResolventMean (N := N) A₀ A z)).mp
      (gueResolventMean_isUnit A₀ A hA₀ hA z hz hN))

/-- **Left inverse identity for the finite mean**, unconditionally. -/
theorem gueResolventMean_inv_mul (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (hN : 0 < N) :
    (gueResolventMean (N := N) A₀ A z)⁻¹ * gueResolventMean (N := N) A₀ A z = 1 :=
  Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det (A := gueResolventMean (N := N) A₀ A z)).mp
      (gueResolventMean_isUnit A₀ A hA₀ hA z hz hN))

/-- The final arithmetic of the self-energy bound. -/
private lemma selfEnergy_arith (cd S Nm yi ZK : ℝ) :
    (4 * cd ^ 2 * S ^ 2 * Nm ^ 2 * yi ^ 4) * (cd * (4 * ZK) * yi)
      = 16 * cd ^ 3 * S ^ 2 * ZK * Nm ^ 2 * yi ^ 5 := by
  ring

/-- **THE SELF-ENERGY ERROR BOUND** (the `hΛ` hypothesis of
`weightedStripBoundProven_of_comparison_unconditional`), unconditionally:

`frob (selfEnergy A₀ A z - z • 1) ≤ 16 (card d)³ (∑ i, frob(A i)²)² (‖z‖² + K²) N⁻² (im z)⁻⁵`,

where `K = frob A₀ + ∑ i, frob (A i)`.  The `(‖z‖² + K²)` factor comes from the inverse bound
`frob m⁻¹ ≤ card d · 4 (‖z‖² + K²) / im z`; on a strip `|im z| < η₀` it is the only dependence
on `Re z`, so a uniform constant is available on any region with `‖z‖ ≤ R`. -/
theorem frob_selfEnergy_sub_smul_one_le (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (hN : 0 < N) :
    frob (selfEnergy (N := N) A₀ A z - z • (1 : Matrix d d ℂ))
      ≤ 16 * (Fintype.card d : ℝ) ^ 3 * (∑ i, (frob (A i)) ^ 2) ^ 2 *
          (‖z‖ ^ 2 + (frobK A₀ A) ^ 2) * ((N : ℝ)⁻¹) ^ 2 * ((z.im)⁻¹) ^ 5 := by
  have hNc : (N : ℂ) ≠ 0 := by
    have h : ((N : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (Nat.cast_pos.mpr hN))
    simpa using h
  have hfac : selfEnergy (N := N) A₀ A z - z • (1 : Matrix d d ℂ)
      = -(meanCentredDefect (N := N) A₀ A z) * (gueResolventMean (N := N) A₀ A z)⁻¹ :=
    selfEnergy_sub_smul_one A₀ A hA₀ hA z (ne_of_gt hz) hNc
      (gueResolventMean_mul_inv A₀ A hA₀ hA z hz hN)
      (gueResolventMean_inv_mul A₀ A hA₀ hA z hz hN)
  rw [hfac]
  set D : Matrix d d ℂ := meanCentredDefect (N := N) A₀ A z with hDdef
  set mI : Matrix d d ℂ := (gueResolventMean (N := N) A₀ A z)⁻¹ with hmIdef
  have hDb : frob D ≤ 4 * (Fintype.card d : ℝ) ^ 2 * (∑ i, (frob (A i)) ^ 2) ^ 2 *
      ((N : ℝ)⁻¹) ^ 2 * ((z.im)⁻¹) ^ 4 := by
    rw [hDdef]
    exact frob_meanCentredDefect_le A₀ A hA₀ hA z hz hN
  have hIn : frob mI ≤ (Fintype.card d : ℝ) * (4 * (‖z‖ ^ 2 + (frobK A₀ A) ^ 2)) * (z.im)⁻¹ := by
    rw [hmIdef]
    exact frob_inv_gueResolventMean_le A₀ A hA₀ hA z hz hN
  have hstep : frob (-D * mI) ≤ frob D * frob mI := by
    rw [neg_mul, frob_neg_eq]
    exact frob_mul_le _ _
  refine hstep.trans ?_
  refine (mul_le_mul hDb hIn (frob_nonneg _) (by positivity)).trans (le_of_eq ?_)
  exact selfEnergy_arith _ _ _ _ _

end

end GUEStrongConvergence
