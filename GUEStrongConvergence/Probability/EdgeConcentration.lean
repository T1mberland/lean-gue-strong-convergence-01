/-
# The GUE edge tail from a single mean bound, by Gaussian concentration

`Verification/TerminalAudit.lean` reduces the GUE edge bound to

`GUEEdgeTail r = ∀ i ε > 0, ∑_N P (2 + ε < ‖G_i^(N)‖) < ∞`

and this file further reduces that tail statement to **one precise mean bound**:
the mean `∫ ‖G_i^(N)‖` being eventually at most `2 + ε/2` for every `ε > 0`.
The passage is the standard Gaussian-concentration argument

`P(‖X‖ > 2 + ε) ≤ P(|‖X‖ - E‖X‖| ≥ ε/2) ≤ 2 exp(-ε² N / 8)`,

whose second inequality is the dimension-free Lipschitz concentration of the pinned
dependency `lean-log-sobolev`, transported to Mathlib's basis-free `stdGaussian` by
`gaussian_measure_abs_ge_le_stdGaussian`.

Main declarations:

* `norm_ofMatrix_le_frob` — the operator norm of a `C⋆`-matrix is bounded by its
  Frobenius norm (via `CStarMatrix.norm_le_of_forall_inner_le`);
* `gueNorm_lipschitz` — **the Lipschitz bound**: `y ↦ ‖CStarMatrix.ofMatrix (gueMatrix y i)‖`
  is Lipschitz with constant `gueScale N = N^{-1/2}`, with no dimension factor
  (`(gueScale N)^2 = 1/N`, sharper than the crude `2/N` bound);
* `measurableSet_gueNorm_gt` — the corresponding superlevel sets are measurable;
* `gueNorm_deviation_tail` — `P(|‖X‖ - E‖X‖| ≥ ρ) ≤ 2 exp(-ρ² N / 2)`;
* `gueEdgeTail_of_mean_bound` — **the key reduction**: a mean bound gives `GUEEdgeTail`;
* `gueEdgeBound_of_mean_bound` — and hence `GUEEdgeBound`, by Borel--Cantelli.

The mean bound itself (`E ‖G_i^(N)‖ ≤ 2 + ε`) is **not** proved here: it is the remaining
genuine probabilistic input (Wigner's semicircle edge for the mean spectral norm).  Nothing
in this file assumes it; it appears only as the explicit hypothesis of the reduction.
-/
import GUEStrongConvergence.Probability.ResolventNetConcentration
import GUEStrongConvergence.Probability.GUEModel
import GUEStrongConvergence.Verification.TerminalAudit

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped Matrix.Norms.Elementwise ComplexOrder ENNReal NNReal Topology
open scoped WithCStarModule InnerProductSpace

set_option linter.unusedSectionVars false

namespace GUEStrongConvergence

noncomputable section

/-! ## The operator norm of a `C⋆`-matrix is bounded by its Frobenius norm -/

/-- The squared `C⋆`-module norm on `C⋆ᵐᵒᵈ(ℂ, κ → ℂ)` is the sum of the squared absolute
values of the coordinates. -/
theorem cstarModule_norm_sq_eq {κ : Type*} [Fintype κ] (v : C⋆ᵐᵒᵈ(ℂ, κ → ℂ)) :
    ‖v‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  rw [WithCStarModule.pi_norm_sq]
  have h1 : ∀ i, ⟪v i, v i⟫_ℂ = ((‖v i‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [WithCStarModule.inner_def]
    rw [show star (v i) = starRingEnd ℂ (v i) from rfl]
    push_cast
    exact Complex.mul_conj' (v i)
  simp only [h1]
  rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun i _ => by positivity)]

/-- The `C⋆`-module norm on `C⋆ᵐᵒᵈ(ℂ, κ → ℂ)` is the `ℓ²` norm of the coordinates. -/
theorem cstarModule_norm_eq_sqrt {κ : Type*} [Fintype κ] (v : C⋆ᵐᵒᵈ(ℂ, κ → ℂ)) :
    ‖v‖ = Real.sqrt (∑ i, ‖v i‖ ^ 2) := by
  rw [← cstarModule_norm_sq_eq v, Real.sqrt_sq (norm_nonneg v)]

/-- The Frobenius norm is invariant under transposition. -/
theorem frob_transpose {κ : Type*} [Fintype κ] [DecidableEq κ] (M : Matrix κ κ ℂ) :
    frob (Mᵀ : Matrix κ κ ℂ) = frob M := by
  unfold frob
  congr 1
  rw [Finset.sum_comm]
  rfl

/-- Auxiliary form of `norm_ofMatrix_le_frob`, with the Frobenius norm passed as an
explicit real number so that the `C⋆`-algebra norm comparison can be applied. -/
private theorem norm_ofMatrix_le_of_frob {κ : Type*} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ ℂ) (F : ℝ) (hF : F = frob (d := κ) M) :
    ‖CStarMatrix.ofMatrix M‖ ≤ F := by
  have hF0 : 0 ≤ F := hF ▸ frob_nonneg (d := κ) M
  have key : ‖CStarMatrix.ofMatrix M‖ ≤ (Real.toNNReal F : ℝ) := by
    refine CStarMatrix.norm_le_of_forall_inner_le (C := Real.toNNReal F) ?_
    intro v w
    rw [Real.coe_toNNReal _ hF0]
    rw [hF]
    have hpair : ⟪w, CStarMatrix.toCLM (CStarMatrix.ofMatrix M) v⟫_ℂ
        = ∑ a, ∑ b, star (w a) * M b a * v b := by
      rw [show CStarMatrix.toCLM (CStarMatrix.ofMatrix M) = CStarMatrix.toCLM M from rfl]
      exact inner_toCLM_eq_pairing M v w
    rw [hpair]
    have htr : (∑ a, ∑ b, star (w a) * M b a * v b)
        = ∑ a, ∑ b, star (w a) * (Mᵀ : Matrix κ κ ℂ) a b * v b := rfl
    rw [htr]
    have hbound := abs_inner_slice_le (Mᵀ : Matrix κ κ ℂ) w v
    rw [frob_transpose] at hbound
    rw [cstarModule_norm_eq_sqrt v, cstarModule_norm_eq_sqrt w]
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hbound
  rwa [Real.coe_toNNReal _ hF0] at key

/-- **Operator norm versus Frobenius norm.**  For a finite complex matrix, the `C⋆`-algebra
(operator) norm of the associated `C⋆`-matrix is bounded by the Frobenius norm.  This is the
only norm comparison needed for the edge concentration; it carries no dimension factor. -/
theorem norm_ofMatrix_le_frob {κ : Type*} [Fintype κ] [DecidableEq κ] (M : Matrix κ κ ℂ) :
    ‖CStarMatrix.ofMatrix M‖ ≤ frob (d := κ) M :=
  norm_ofMatrix_le_of_frob M _ rfl

/-! ## Lipschitz bound for the norm of a GUE block -/

section Lipschitz

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- Every entry of the unnormalized GUE matrix, written in real coordinates:
`α z₁ + β z₂ = (z₁ + z₂)/2 + i (z₂ - z₁)/2`. -/
theorem gueUnscaled_entry_eq (x : GUECoord ι N → ℝ) (i : ι) (a b : Fin N) :
    gueUnscaled x i a b
      = (((x (i, (a, b)) + x (i, (b, a))) / 2 : ℝ) : ℂ)
        + ((((x (i, (b, a)) - x (i, (a, b))) / 2 : ℝ)) : ℂ) * Complex.I := by
  simp only [gueUnscaled, gueAlpha, gueBeta]
  push_cast
  ring

/-- The squared absolute value of an entry of the unnormalized GUE matrix is half the sum of
the squares of its two real coordinates.  This is the exact constant behind the `N^{-1/2}`
Lipschitz scale of the block norm. -/
theorem norm_gueUnscaled_entry_sq (x : GUECoord ι N → ℝ) (i : ι) (a b : Fin N) :
    ‖gueUnscaled x i a b‖ ^ 2
      = ((x (i, (a, b))) ^ 2 + (x (i, (b, a))) ^ 2) / 2 := by
  rw [gueUnscaled_entry_eq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp
  ring

/-- The squared absolute value of an entry of the normalized GUE matrix. -/
theorem norm_gueMatrix_entry_sq (x : GUECoord ι N → ℝ) (i : ι) (a b : Fin N) :
    ‖gueMatrix x i a b‖ ^ 2
      = (gueScale N) ^ 2 * ((x (i, (a, b))) ^ 2 + (x (i, (b, a))) ^ 2) / 2 := by
  rw [gueMatrix, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (gueScale_nonneg N), norm_gueUnscaled_entry_sq]
  ring

/-- The squared coordinates of a single label are dominated by the full squared norm. -/
theorem sum_sq_label_le (z : EuclideanSpace ℝ (GUECoord ι N)) (i : ι) :
    ∑ a : Fin N, ∑ b : Fin N, (z (i, (a, b))) ^ 2 ≤ ‖z‖ ^ 2 := by
  rw [show ‖z‖ ^ 2 = ∑ p, (z p) ^ 2 from EuclideanSpace.real_norm_sq_eq z]
  have h1 : (∑ p ∈ (Finset.univ.image (fun q : Fin N × Fin N => (i, q))), (z p) ^ 2)
      = ∑ a : Fin N, ∑ b : Fin N, (z (i, (a, b))) ^ 2 := by
    rw [Finset.sum_image (fun x _ y _ h => by simpa using h)]
    simp [Fintype.sum_prod_type]
  rw [← h1]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun p _ _ => sq_nonneg _)

/-- **Frobenius norm of a GUE block.**  `‖G_i‖_F ≤ N^{-1/2} ‖x‖`; the constant is exactly
`gueScale N`, with no dimension factor. -/
theorem frob_gueMatrix_le (z : EuclideanSpace ℝ (GUECoord ι N)) (i : ι) :
    frob (gueMatrix z i) ≤ gueScale N * ‖z‖ := by
  have hswap : (∑ a : Fin N, ∑ b : Fin N, (z (i, (b, a))) ^ 2)
      = ∑ a : Fin N, ∑ b : Fin N, (z (i, (a, b))) ^ 2 := by
    rw [Finset.sum_comm]
  have hS := sum_sq_label_le z i
  have hsq : (frob (gueMatrix z i)) ^ 2 ≤ (gueScale N * ‖z‖) ^ 2 := by
    rw [frob_sq, mul_pow]
    have hstep : ∀ a b : Fin N, ‖gueMatrix z i a b‖ ^ 2
        = (gueScale N) ^ 2 / 2 * (z (i, (a, b))) ^ 2
          + (gueScale N) ^ 2 / 2 * (z (i, (b, a))) ^ 2 := by
      intro a b
      rw [norm_gueMatrix_entry_sq]
      ring
    have hX : (∑ a : Fin N, ∑ b : Fin N, (gueScale N) ^ 2 / 2 * (z (i, (a, b))) ^ 2)
        = (gueScale N) ^ 2 / 2 * ∑ a : Fin N, ∑ b : Fin N, (z (i, (a, b))) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
    have hY : (∑ a : Fin N, ∑ b : Fin N, (gueScale N) ^ 2 / 2 * (z (i, (b, a))) ^ 2)
        = (gueScale N) ^ 2 / 2 * ∑ a : Fin N, ∑ b : Fin N, (z (i, (b, a))) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
    have hsum : (∑ a : Fin N, ∑ b : Fin N,
          ((gueScale N) ^ 2 / 2 * (z (i, (a, b))) ^ 2
            + (gueScale N) ^ 2 / 2 * (z (i, (b, a))) ^ 2))
        = (gueScale N) ^ 2 * ∑ a : Fin N, ∑ b : Fin N, (z (i, (a, b))) ^ 2 := by
      simp only [Finset.sum_add_distrib]
      rw [hX, hY, hswap]
      ring
    simp only [hstep]
    rw [hsum]
    exact mul_le_mul_of_nonneg_left hS (sq_nonneg _)
  exact le_of_sq_le_sq hsq (mul_nonneg (gueScale_nonneg N) (norm_nonneg z))

/-- The GUE matrix is additive in the Gaussian coordinates. -/
theorem gueMatrix_sub (x y : EuclideanSpace ℝ (GUECoord ι N)) (i : ι) :
    gueMatrix x i - gueMatrix y i = gueMatrix (x - y) i := by
  ext a b
  simp only [Matrix.sub_apply, gueMatrix, gueUnscaled, WithLp.ofLp_sub, Pi.sub_apply]
  push_cast
  ring

/-- The squared Lipschitz constant of the GUE block norm is exactly `1/N`, i.e. `C = 1` in the
notation `K^2 = C/N`.  This is sharper than the crude entrywise bound
`2 (‖α‖^2 + ‖β‖^2)/N = 2/N`. -/
theorem gueNorm_lipschitz_const_sq (N : ℕ) :
    ((Real.toNNReal (gueScale N) : ℝ≥0) : ℝ) ^ 2 = (N : ℝ)⁻¹ := by
  rw [Real.coe_toNNReal _ (gueScale_nonneg N), gueScale_sq]

/-- **The Lipschitz bound.**  The operator norm of a GUE block is `gueScale N = N^{-1/2}`
Lipschitz in the Gaussian coordinates, with `(gueScale N)^2 = 1/N`. -/
theorem gueNorm_lipschitz (i : ι) :
    LipschitzWith (Real.toNNReal (gueScale N))
      (fun y : EuclideanSpace ℝ (GUECoord ι N) =>
        ‖CStarMatrix.ofMatrix (gueMatrix y i)‖) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  rw [Real.dist_eq, dist_eq_norm]
  have h1 : |‖CStarMatrix.ofMatrix (gueMatrix x i)‖ -
        ‖CStarMatrix.ofMatrix (gueMatrix y i)‖|
      ≤ ‖CStarMatrix.ofMatrix (gueMatrix x i) - CStarMatrix.ofMatrix (gueMatrix y i)‖ :=
    abs_norm_sub_norm_le _ _
  have h2 : CStarMatrix.ofMatrix (gueMatrix x i) - CStarMatrix.ofMatrix (gueMatrix y i)
      = CStarMatrix.ofMatrix (gueMatrix x i - gueMatrix y i) :=
    CStarMatrix.of_sub_of _ _
  rw [h2] at h1
  have h3 : ‖CStarMatrix.ofMatrix (gueMatrix x i - gueMatrix y i)‖
      ≤ frob (gueMatrix x i - gueMatrix y i) :=
    norm_ofMatrix_le_frob (gueMatrix x i - gueMatrix y i)
  have h4 : frob (gueMatrix x i - gueMatrix y i) ≤ gueScale N * ‖x - y‖ := by
    rw [gueMatrix_sub]
    exact frob_gueMatrix_le (x - y) i
  have h5 : ((Real.toNNReal (gueScale N) : ℝ≥0) : ℝ) = gueScale N :=
    Real.coe_toNNReal _ (gueScale_nonneg N)
  calc |‖CStarMatrix.ofMatrix (gueMatrix x i)‖ -
        ‖CStarMatrix.ofMatrix (gueMatrix y i)‖|
      ≤ ‖CStarMatrix.ofMatrix (gueMatrix x i) - CStarMatrix.ofMatrix (gueMatrix y i)‖ := h1
    _ = ‖CStarMatrix.ofMatrix (gueMatrix x i - gueMatrix y i)‖ := by rw [h2]
    _ ≤ frob (gueMatrix x i - gueMatrix y i) := h3
    _ ≤ gueScale N * ‖x - y‖ := h4
    _ = ((Real.toNNReal (gueScale N) : ℝ≥0) : ℝ) * ‖x - y‖ := by rw [h5]

/-- The superlevel sets of the GUE block norm are measurable. -/
theorem measurableSet_gueNorm_gt (i : ι) (ε : ℝ) :
    MeasurableSet {y : EuclideanSpace ℝ (GUECoord ι N) |
      2 + ε < ‖CStarMatrix.ofMatrix (gueMatrix y i)‖} :=
  measurableSet_lt measurable_const (gueNorm_lipschitz (N := N) i).continuous.measurable

end Lipschitz

/-! ## Concentration of the GUE block norm around its mean -/

section Concentration

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- **Gaussian concentration of the block norm.**  For every `ρ > 0`,
`P(|‖G_i‖ - E‖G_i‖| ≥ ρ) ≤ 2 exp(-ρ² N / 2)`.  The exponent is linear in `N` with the sharp
constant `1/2` coming from `(gueScale N)^2 = 1/N`. -/
theorem gueNorm_deviation_tail (i : ι) {ρ : ℝ} (hρ : 0 < ρ) :
    (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))).real
        {y | ρ ≤ |‖CStarMatrix.ofMatrix (gueMatrix y i)‖ -
          ∫ z, ‖CStarMatrix.ofMatrix (gueMatrix z i)‖
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))|} ≤
      2 * Real.exp (-(ρ ^ 2 * (N : ℝ) / 2)) := by
  have hB : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
  have hK : ((Real.toNNReal (gueScale N) : ℝ≥0) : ℝ) ^ 2 ≤ (N : ℝ)⁻¹ := by
    rw [Real.coe_toNNReal _ (gueScale_nonneg N), gueScale_sq]
  have hmain := gaussian_tail_le_of_lipschitz_sq_le (f := fun y : EuclideanSpace ℝ (GUECoord ι N) =>
      ‖CStarMatrix.ofMatrix (gueMatrix y i)‖) (gueNorm_lipschitz (N := N) i) hK hB hρ
  have hexp : -(ρ ^ 2 / (2 * (N : ℝ)⁻¹)) = -(ρ ^ 2 * (N : ℝ) / 2) := by
    rw [show (N : ℝ)⁻¹ = (1 : ℝ) / (N : ℝ) from (one_div _).symm,
      div_two_mul_div_eq (r := ρ) (c := 1) zero_le_one N]
    ring
  rw [hexp] at hmain
  exact hmain

end Concentration

/-! ## The edge tail from a mean bound -/

/-- **Key reduction: a mean bound gives the GUE edge tail.**

If for every `i` and every `ε > 0` the mean operator norm of the `N`-th GUE block is
eventually at most `2 + ε/2`, then the tail probabilities `P(2 + ε < ‖G_i‖)` are summable in
`N`.  The proof is the standard concentration chain

`P(‖X‖ > 2 + ε) ≤ P(|‖X‖ - E‖X‖| ≥ ε/2) ≤ 2 exp(-ε² N / 8)`.

The mean bound `E‖G_i‖ ≤ 2 + ε` is the remaining open probabilistic input; it is **not**
assumed anywhere else. -/
theorem gueEdgeTail_of_mean_bound {r : ℕ}
    (hmean : ∀ i : Fin r, ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      ∫ y, ‖CStarMatrix.ofMatrix (gueMatrix (ι := Fin r) y i)‖
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) N))) ≤ 2 + ε / 2) :
    GUEEdgeTail r := by
  intro i ε hε
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hmean i ε hε)
  have hgeo : Summable fun N : ℕ => 2 * Real.exp (-(ε ^ 2 / 8) * (N : ℝ)) := by
    have h := summable_two_exp_neg_mul (c := 4) (r := ε) (by norm_num) hε
    simpa [show ε ^ 2 / (2 * 4) = ε ^ 2 / 8 from by norm_num] using h
  refine Summable.of_norm_bounded_eventually_nat hgeo ?_
  filter_upwards [eventually_ge_atTop N₀, eventually_ge_atTop 1] with N hN hN1
  set F : EuclideanSpace ℝ (GUECoord (Fin r) N) → ℝ :=
    fun y => ‖CStarMatrix.ofMatrix (gueMatrix (ι := Fin r) y i)‖ with hF
  set m : ℝ := ∫ y, F y ∂(stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) N))) with hm
  have hmle : m ≤ 2 + ε / 2 := by simpa only [hm, hF] using hN₀ N hN
  have hsub : {y | 2 + ε < F y} ⊆ {y | ε / 2 ≤ |F y - m|} := by
    intro y hy
    have hy' : 2 + ε < F y := hy
    have hdev : ε / 2 < F y - m := by linarith
    exact le_trans (le_of_lt hdev) (le_abs_self _)
  have hmono : (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) N))).real {y | 2 + ε < F y}
      ≤ (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) N))).real
          {y | ε / 2 ≤ |F y - m|} :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  have htail := gueNorm_deviation_tail (N := N) (ι := Fin r) i (ρ := ε / 2) (by linarith)
  have htail' : (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) N))).real
        {y | ε / 2 ≤ |F y - m|} ≤ 2 * Real.exp (-((ε / 2) ^ 2 * (N : ℝ) / 2)) := by
    simpa only [hF, hm] using htail
  have hnn : 0 ≤ (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) N))).real {y | 2 + ε < F y} :=
    ENNReal.toReal_nonneg
  calc ‖(stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) N))).real {y | 2 + ε < F y}‖
      = (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) N))).real {y | 2 + ε < F y} := by
        rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    _ ≤ (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) N))).real
          {y | ε / 2 ≤ |F y - m|} := hmono
    _ ≤ 2 * Real.exp (-((ε / 2) ^ 2 * (N : ℝ) / 2)) := htail'
    _ = 2 * Real.exp (-(ε ^ 2 / 8) * (N : ℝ)) := by
        rw [show -((ε / 2) ^ 2 * (N : ℝ) / 2) = -(ε ^ 2 / 8) * (N : ℝ) by ring]

/-- **The edge bound from a mean bound.**  Combining `gueEdgeTail_of_mean_bound` with the
Borel--Cantelli step `gueEdgeBound_of_tailMeasures`, a mean bound on the operator norm of the
GUE blocks yields `GUEEdgeBound r` outright. -/
theorem gueEdgeBound_of_mean_bound {r : ℕ}
    (hmean : ∀ i : Fin r, ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      ∫ y, ‖CStarMatrix.ofMatrix (gueMatrix (ι := Fin r) y i)‖
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) N))) ≤ 2 + ε / 2) :
    GUEEdgeBound r :=
  gueEdgeBound_of_tailMeasures (gueEdgeTail_of_mean_bound hmean)
    (fun i ε N => measurableSet_gueNorm_gt (N := N) i ε)

end

end GUEStrongConvergence
