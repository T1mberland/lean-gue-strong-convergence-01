/-
# Gaussian Lipschitz concentration of GUE resolvent pairings

For fixed `z` with `0 < z.im` and vectors `u v`, the real pairing
`x ↦ Re ⟨u, R_N(z,x) v⟩` is Lipschitz with an explicit constant of order
`N^{-1/2}` in the Euclidean coordinate metric.  Consequently its Gaussian
fluctuations around the mean are concentrated at the sharp `1/N` variance
proxy, giving `exp(-c N)` tails at fixed `r`.

The only analytic input left for spectral inclusion — convergence of the mean
resolvent — is *not* used here and is recorded as a separate input in
`docs/handoffs/II_A_SPECTRAL_INCLUSION_PROGRESS.md`.
-/
import GUEStrongConvergence.Probability.ResolventSparseBound
import GUEStrongConvergence.Probability.GaussianTailTransport

open MeasureTheory ProbabilityTheory Matrix Kronecker
open scoped Matrix.Norms.Elementwise ComplexOrder ENNReal NNReal

namespace GUEStrongConvergence

noncomputable section

variable {ι d : Type*} {N : ℕ} [Fintype ι] [Fintype d] [DecidableEq d] [DecidableEq ι]

/-- Column combination of a matrix against a vector. -/
def rowComb {n : Type*} [Fintype n] (R : CStarMatrix n n ℂ) (u : n → ℂ) : n → ℂ :=
  fun k => ∑ a, star (u a) * R a k

/-- Matrix-vector product. -/
def matVec {n : Type*} [Fintype n] (R : CStarMatrix n n ℂ) (v : n → ℂ) : n → ℂ :=
  fun l => ∑ b, R l b * v b

/-- Pairing of a triple matrix product against vectors, expanded over the middle
matrix: `⟨u, R M S v⟩ = ∑_{k,l} (R⋆u)_k M_{k l} (S v)_l`. -/
theorem pairing_mul_eq {n : Type*} [Fintype n] [DecidableEq n]
    (R M S : CStarMatrix n n ℂ) (u v : n → ℂ) :
    (∑ a, ∑ b, star (u a) * (R * M * S) a b * v b)
      = ∑ k, ∑ l, rowComb R u l * M l k * matVec S v k := by
  have h1 : (∑ a, ∑ b, star (u a) * (R * M * S) a b * v b)
      = ∑ a, ∑ b, ∑ k, ∑ l, star (u a) * (R a l * M l k * S k b) * v b := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [CStarMatrix.mul_apply]
    rw [Finset.mul_sum]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [CStarMatrix.mul_apply]
    rw [Finset.sum_mul]
    rw [Finset.mul_sum]
    rw [Finset.sum_mul]
  have h2 : (∑ k, ∑ l, rowComb R u l * M l k * matVec S v k)
      = ∑ k, ∑ l, ∑ a, ∑ b, star (u a) * R a l * M l k * (S k b * v b) := by
    simp only [rowComb, matVec, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.sum_comm]
  rw [h1, h2]
  rw [show (∑ a, ∑ b, ∑ k, ∑ l, star (u a) * (R a l * M l k * S k b) * v b)
      = ∑ k, ∑ l, ∑ a, ∑ b, star (u a) * (R a l * M l k * S k b) * v b from by
    rw [show (∑ a, ∑ b, ∑ k, ∑ l, star (u a) * (R a l * M l k * S k b) * v b)
        = ∑ a, ∑ k, ∑ b, ∑ l, star (u a) * (R a l * M l k * S k b) * v b from by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm]
    rw [show (∑ a, ∑ k, ∑ b, ∑ l, star (u a) * (R a l * M l k * S k b) * v b)
        = ∑ k, ∑ a, ∑ b, ∑ l, star (u a) * (R a l * M l k * S k b) * v b from
      Finset.sum_comm]
    rw [show (∑ k, ∑ a, ∑ b, ∑ l, star (u a) * (R a l * M l k * S k b) * v b)
        = ∑ k, ∑ a, ∑ l, ∑ b, star (u a) * (R a l * M l k * S k b) * v b from by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm]
    rw [show (∑ k, ∑ a, ∑ l, ∑ b, star (u a) * (R a l * M l k * S k b) * v b)
        = ∑ k, ∑ l, ∑ a, ∑ b, star (u a) * (R a l * M l k * S k b) * v b from by
      apply Finset.sum_congr rfl
      intro k _
      exact Finset.sum_comm]]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Pairing against the resolvent. -/
def resolventPairing (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (z : ℂ)
    (u v : d × Fin N → ℂ) (x : GUECoord ι N → ℝ) : ℂ :=
  ∑ a, ∑ b, star (u a) * guePencilResolvent A₀ A x z a b * v b

/-- Linearity of the pairing in a finite weighted sum of middle matrices. -/
theorem pairing_sum_smul {α : Type*} [Fintype α]
    (R S : CStarMatrix (d × Fin N) (d × Fin N) ℂ)
    (c : α → ℂ) (D : α → CStarMatrix (d × Fin N) (d × Fin N) ℂ)
    (u v : d × Fin N → ℂ) :
    (∑ a, ∑ b, star (u a) * (R * (∑ p, c p • D p) * S) a b * v b)
      = ∑ p, c p * (∑ a, ∑ b, star (u a) * (R * D p * S) a b * v b) := by
  have hmul : R * (∑ p, c p • D p) * S = ∑ p, c p • (R * D p * S) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [CStarMatrix.mul_smul, CStarMatrix.smul_mul]
  rw [hmul]
  have hsplit : ∀ a b, star (u a) * (∑ p, c p • (R * D p * S)) a b * v b
      = ∑ p, c p * (star (u a) * (R * D p * S) a b * v b) := by
    intro a b
    rw [cstar_sum_apply]
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [CStarMatrix.smul_apply, smul_eq_mul]
    ring
  simp only [hsplit]
  rw [show (∑ a, ∑ b, ∑ p, c p * (star (u a) * (R * D p * S) a b * v b))
      = ∑ a, ∑ p, ∑ b, c p * (star (u a) * (R * D p * S) a b * v b) from by
    apply Finset.sum_congr rfl
    intro a _
    exact Finset.sum_comm]
  rw [show (∑ a, ∑ p, ∑ b, c p * (star (u a) * (R * D p * S) a b * v b))
      = ∑ p, ∑ a, ∑ b, c p * (star (u a) * (R * D p * S) a b * v b) from
    Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]


/-- Increment of the resolvent pairing as a linear combination of the coordinate
increments against the direction pairings. -/
theorem pairing_diff_eq (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (u v : d × Fin N → ℂ)
    (x y : GUECoord ι N → ℝ) :
    resolventPairing A₀ A z u v x - resolventPairing A₀ A z u v y
      = ∑ p : GUECoord ι N, ((x p - y p : ℝ) : ℂ) *
          (∑ k, ∑ l, rowComb (guePencilResolvent A₀ A x z) u l *
            guePencilDirection A p l k *
            matVec (guePencilResolvent A₀ A y z) v k) := by
  have h1 : resolventPairing A₀ A z u v x - resolventPairing A₀ A z u v y
      = ∑ a, ∑ b, star (u a) *
          (guePencilResolvent A₀ A x z - guePencilResolvent A₀ A y z) a b * v b := by
    simp only [resolventPairing, CStarMatrix.sub_apply, mul_sub, sub_mul,
      Finset.sum_sub_distrib]
  rw [h1]
  rw [guePencilResolvent_sub A₀ A hA₀ hA x y z hz]
  rw [guePencil_sub_eq_sum_smul A₀ A x y]
  rw [show (∑ p : GUECoord ι N, (x p - y p) • guePencilDirection A p)
      = ∑ p : GUECoord ι N, ((x p - y p : ℝ) : ℂ) • guePencilDirection A p from by
    apply Finset.sum_congr rfl
    intro p _
    exact RCLike.real_smul_eq_coe_smul (K := ℂ) (x p - y p) (guePencilDirection A p)]
  rw [pairing_sum_smul (guePencilResolvent A₀ A x z) (guePencilResolvent A₀ A y z)
    (fun p : GUECoord ι N => ((x p - y p : ℝ) : ℂ)) (guePencilDirection A) u v]
  apply Finset.sum_congr rfl
  intro p _
  rw [pairing_mul_eq]


/-- Cauchy–Schwarz for a finite complex linear combination. -/
theorem norm_sum_mul_le {α : Type*} [Fintype α] (c : α → ℝ) (g : α → ℂ) :
    ‖∑ p, (c p : ℂ) * g p‖ ≤ Real.sqrt (∑ p, (c p) ^ 2) * Real.sqrt (∑ p, ‖g p‖ ^ 2) := by
  have h1 : ‖∑ p, (c p : ℂ) * g p‖ ≤ ∑ p, |c p| * ‖g p‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h2 : (∑ p, |c p| * ‖g p‖) ^ 2 ≤ (∑ p, (c p) ^ 2) * (∑ p, ‖g p‖ ^ 2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun p => |c p|) (fun p => ‖g p‖)
    simpa only [sq_abs] using h
  have h3 : ∑ p, |c p| * ‖g p‖ ≤
      Real.sqrt ((∑ p, (c p) ^ 2) * (∑ p, ‖g p‖ ^ 2)) :=
    Real.le_sqrt_of_sq_le h2
  have h4 : Real.sqrt ((∑ p, (c p) ^ 2) * (∑ p, ‖g p‖ ^ 2))
      = Real.sqrt (∑ p, (c p) ^ 2) * Real.sqrt (∑ p, ‖g p‖ ^ 2) :=
    Real.sqrt_mul (Finset.sum_nonneg fun p _ => sq_nonneg _) (∑ p, ‖g p‖ ^ 2)
  exact h1.trans (h3.trans (le_of_eq h4))

/-- Swapped-index form of the sparse direction-pairing bound. -/
theorem sum_sq_direction_pairing_le_swap (A : ι → Matrix d d ℂ) (W Z : d × Fin N → ℂ) :
    ∑ p : GUECoord ι N,
        ‖∑ k : d × Fin N, ∑ l : d × Fin N,
          W l * guePencilDirection A p l k * Z k‖ ^ 2
      ≤ 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2)
          * (∑ k : d × Fin N, ‖W k‖ ^ 2) * (∑ k : d × Fin N, ‖Z k‖ ^ 2) := by
  have h := sum_sq_direction_pairing_le A W Z
  convert h using 2
  congr 1
  apply congrArg norm
  rw [Finset.sum_comm]

/-- Squared ℓ² norm of the column combination of a resolvent. -/
theorem sum_sq_rowComb_le (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (u : d × Fin N → ℂ) (x : GUECoord ι N → ℝ) :
    ∑ k, ‖rowComb (guePencilResolvent A₀ A x z) u k‖ ^ 2
      ≤ (z.im)⁻¹ ^ 2 * ∑ k, ‖u k‖ ^ 2 := by
  have hR : ‖guePencilResolvent A₀ A x z‖ ≤ |z.im|⁻¹ :=
    norm_guePencilResolvent_le A₀ A hA₀ hA x z (ne_of_gt hz)
  have hη : 0 ≤ (z.im)⁻¹ := by positivity
  have h := sum_sq_star_mul_le (R := guePencilResolvent A₀ A x z)
    (η := (z.im)⁻¹) (by simpa only [abs_of_pos hz] using hR) hη u
  simpa only [rowComb] using h

/-- Squared ℓ² norm of the matrix-vector product of a resolvent. -/
theorem sum_sq_matVec_le (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (v : d × Fin N → ℂ) (x : GUECoord ι N → ℝ) :
    ∑ k, ‖matVec (guePencilResolvent A₀ A x z) v k‖ ^ 2
      ≤ (z.im)⁻¹ ^ 2 * ∑ k, ‖v k‖ ^ 2 := by
  have hR : ‖guePencilResolvent A₀ A x z‖ ≤ |z.im|⁻¹ :=
    norm_guePencilResolvent_le A₀ A hA₀ hA x z (ne_of_gt hz)
  have hη : 0 ≤ (z.im)⁻¹ := by positivity
  have h := sum_sq_mul_le (R := guePencilResolvent A₀ A x z)
    (η := (z.im)⁻¹) (by simpa only [abs_of_pos hz] using hR) hη v
  simpa only [matVec] using h


/-- Explicit Lipschitz constant of a resolvent pairing. -/
def resolventLipschitzConst (A : ι → Matrix d d ℂ) (z : ℂ)
    (u v : d × Fin N → ℂ) : ℝ :=
  Real.sqrt (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) *
    ((z.im)⁻¹) ^ 4 * (∑ k, ‖u k‖ ^ 2) * (∑ k, ‖v k‖ ^ 2))

lemma resolventLipschitzConst_nonneg (A : ι → Matrix d d ℂ) (z : ℂ)
    (u v : d × Fin N → ℂ) : 0 ≤ resolventLipschitzConst A z u v :=
  Real.sqrt_nonneg _

/-- **Lipschitz concentration input.** The real part of a resolvent pairing is
Lipschitz on `EuclideanSpace ℝ (GUECoord ι N)` with the explicit `N^{-1/2}`-scale
constant `resolventLipschitzConst`. -/
theorem resolventPairing_lipschitz (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (u v : d × Fin N → ℂ) :
    LipschitzWith (Real.toNNReal (resolventLipschitzConst (N := N) A z u v))
      (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        (resolventPairing A₀ A z u v (fun p => x p)).re) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  rw [Real.dist_eq, dist_eq_norm]
  -- the complex increment
  have hre : |(resolventPairing A₀ A z u v (fun p => x p)).re -
      (resolventPairing A₀ A z u v (fun p => y p)).re|
      ≤ ‖resolventPairing A₀ A z u v (fun p => x p) -
          resolventPairing A₀ A z u v (fun p => y p)‖ := by
    rw [← Complex.sub_re]
    exact Complex.abs_re_le_norm _
  -- sum representation
  have hdiff := pairing_diff_eq A₀ A hA₀ hA z (ne_of_gt hz) u v
    (fun p => x p) (fun p => y p)
  -- Cauchy–Schwarz
  have hCS := norm_sum_mul_le (fun p : GUECoord ι N => x p - y p)
    (fun p : GUECoord ι N => ∑ k : d × Fin N, ∑ l : d × Fin N,
      rowComb (guePencilResolvent A₀ A (fun q => x q) z) u l *
        guePencilDirection A p l k *
        matVec (guePencilResolvent A₀ A (fun q => y q) z) v k)
  refine hre.trans ?_
  rw [hdiff]
  refine hCS.trans ?_
  -- bound the two factors
  have hsparse := sum_sq_direction_pairing_le_swap A
    (rowComb (guePencilResolvent A₀ A (fun q => x q) z) u)
    (matVec (guePencilResolvent A₀ A (fun q => y q) z) v)
  have hW := sum_sq_rowComb_le A₀ A hA₀ hA z hz u (fun q => x q)
  have hZ := sum_sq_matVec_le A₀ A hA₀ hA z hz v (fun q => y q)
  have hW0 : 0 ≤ ∑ k : d × Fin N,
      ‖rowComb (guePencilResolvent A₀ A (fun q => x q) z) u k‖ ^ 2 :=
    Finset.sum_nonneg fun k _ => sq_nonneg _
  have hZ0 : 0 ≤ ∑ k : d × Fin N,
      ‖matVec (guePencilResolvent A₀ A (fun q => y q) z) v k‖ ^ 2 :=
    Finset.sum_nonneg fun k _ => sq_nonneg _
  have hsparse' : ∑ p : GUECoord ι N,
        ‖∑ k : d × Fin N, ∑ l : d × Fin N,
          rowComb (guePencilResolvent A₀ A (fun q => x q) z) u l *
            guePencilDirection A p l k *
            matVec (guePencilResolvent A₀ A (fun q => y q) z) v k‖ ^ 2
      ≤ 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) *
          ((z.im)⁻¹ ^ 2 * ∑ k, ‖u k‖ ^ 2) * ((z.im)⁻¹ ^ 2 * ∑ k, ‖v k‖ ^ 2) := by
    refine hsparse.trans ?_
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hW (by positivity)
    · exact hZ
    · exact hZ0
    · positivity
  have hnorm : ∑ p : GUECoord ι N, (x p - y p) ^ 2 = ‖x - y‖ ^ 2 := by
    rw [show ‖x - y‖ ^ 2 = ∑ p : GUECoord ι N, (x - y) p ^ 2 from
      EuclideanSpace.real_norm_sq_eq (x - y)]
    rfl
  have hsqrt : Real.sqrt (∑ p : GUECoord ι N, (x p - y p) ^ 2) = ‖x - y‖ := by
    rw [hnorm, Real.sqrt_sq (norm_nonneg _)]
  have hK0 : resolventLipschitzConst (N := N) A z u v =
      Real.sqrt (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) *
        ((z.im)⁻¹) ^ 4 * (∑ k, ‖u k‖ ^ 2) * (∑ k, ‖v k‖ ^ 2)) := rfl
  calc Real.sqrt (∑ p : GUECoord ι N, (x p - y p) ^ 2) *
        Real.sqrt (∑ p : GUECoord ι N,
          ‖∑ k : d × Fin N, ∑ l : d × Fin N,
            rowComb (guePencilResolvent A₀ A (fun q => x q) z) u l *
              guePencilDirection A p l k *
              matVec (guePencilResolvent A₀ A (fun q => y q) z) v k‖ ^ 2)
      ≤ Real.sqrt (∑ p : GUECoord ι N, (x p - y p) ^ 2) *
          Real.sqrt (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) *
            ((z.im)⁻¹ ^ 2 * ∑ k, ‖u k‖ ^ 2) * ((z.im)⁻¹ ^ 2 * ∑ k, ‖v k‖ ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        exact Real.sqrt_le_sqrt hsparse'
    _ = ‖x - y‖ * resolventLipschitzConst (N := N) A z u v := by
        rw [hsqrt, hK0]
        congr 1
        ring
    _ = Real.toNNReal (resolventLipschitzConst (N := N) A z u v) * ‖x - y‖ := by
        rw [Real.coe_toNNReal _ (resolventLipschitzConst_nonneg A z u v)]
        ring


/-- **Gaussian tail bound for resolvent pairings.** At fixed `r`, the deviation
probability decays like `exp(-c N)` with
`c = r² / (2 K²)` and `K² = (im z)⁻⁴ · 2 · gueScale N² · ∑ frob(A i)² · ‖u‖² ‖v‖²`. -/
theorem resolventPairing_tail (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (u v : d × Fin N → ℂ) {r : ℝ} (hr : 0 ≤ r) :
    (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))).real
        {x | r ≤ |(resolventPairing A₀ A z u v (fun p => x p)).re -
          ∫ y, (resolventPairing A₀ A z u v (fun p => y p)).re
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))|} ≤
      2 * Real.exp (-r ^ 2 /
        (2 * ((Real.toNNReal (resolventLipschitzConst (N := N) A z u v) : ℝ) ^ 2))) :=
  gaussian_measure_abs_ge_le_stdGaussian
    (resolventPairing_lipschitz A₀ A hA₀ hA z hz u v) hr

end

end GUEStrongConvergence
