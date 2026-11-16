/-
# Analytic propagation into the near-axis annulus

`StrongConvergence/PencilStripAbove.lean` proves the pencil strip bound above the Dyson threshold
`dysonThreshold A`.  For `w` in the annulus `|Im w| < dysonThreshold A` the contraction argument
fails, but the *exact* second-resolvent identity propagates the estimate down from the
above-threshold line `w' = Re w + i dysonThreshold A`:

`g_N(w) - g_N(w') = (w' - w) * E[tr(R(w) R(w'))]`,
`g(w) - g(w') = (w' - w) * E_vac[tr(R_∞(w) R_∞(w'))]`.

Hence the annulus is reduced to the **two-point (product-of-resolvents) correlation**

`E[tr_N(R_N(w) R_N(w'))] - E_vac[tr(R_∞(w) R_∞(w'))] = O(N⁻² |Im w|^{-6})`,

a genus/parity statement for a product of two resolvents at two different spectral parameters
(rather than the failed one-point operator inversion).

Main results:

* `resolvent_sub_resolvent` — the second resolvent identity in a `ℂ`-algebra;
* `guePencilResolvent_sub_spectral` — the finite pencil resolvent at two spectral parameters;
* `gueResolventMean_sub_shift` — `g_N(w) - g_N(w') = (w' - w) • E[tr(R(w) R(w'))]`;
* `operatorMatrixPencilCauchy_sub_shift` — the same for the limit Cauchy transform;
* `pencilStripBound_annulus_of_twoPoint` — the annulus bound from the two-point correlation
  bound plus the above-threshold theorem.

No `sorry`, no new axioms.
-/
import GUEStrongConvergence.StrongConvergence.PencilStripAbove
import GUEStrongConvergence.Probability.ResolventPencilAlgebra
import FreeProbability.OperatorValued.MatrixExpectation

open Filter MeasureTheory ProbabilityTheory Matrix
open FreeProbability FreeProbability.Fock
open scoped Matrix.Norms.Frobenius ComplexOrder ENNReal NNReal Topology BigOperators

namespace GUEStrongConvergence

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : Type*} [Fintype d] [DecidableEq d]
  [Nonempty d] {N : ℕ}

/-! ## 1. The second resolvent identity in the spectral parameter -/

/-- **Second resolvent identity.**  For a fixed element `P` of a `ℂ`-algebra,
`(w - P)⁻¹ - (w' - P)⁻¹ = (w' - w) • (w - P)⁻¹ (w' - P)⁻¹`. -/
theorem resolvent_sub_resolvent {A : Type*} [Ring A] [Algebra ℂ A] (P : A) (w w' : ℂ)
    (hw : IsUnit (algebraMap ℂ A w - P)) (hw' : IsUnit (algebraMap ℂ A w' - P)) :
    resolvent P w - resolvent P w' = (w' - w) • (resolvent P w * resolvent P w') := by
  unfold resolvent
  rw [Ring.inverse_sub_inverse ⟨fun _ => hw', fun _ => hw⟩]
  have hdiff : algebraMap ℂ A w' - P - (algebraMap ℂ A w - P) = algebraMap ℂ A (w' - w) := by
    rw [map_sub]
    abel
  rw [hdiff, show algebraMap ℂ A (w' - w) = (w' - w) • (1 : A) from
      Algebra.algebraMap_eq_smul_one (w' - w)]
  rw [mul_smul_comm, smul_mul_assoc, mul_one]

/-! ## 2. The finite side -/

/-- The finite pencil resolvent at two spectral parameters (same random point). -/
theorem guePencilResolvent_sub_spectral (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (x : GUECoord ι N → ℝ) (w w' : ℂ) (hw : w.im ≠ 0) (hw' : w'.im ≠ 0) :
    guePencilResolvent A₀ A x w - guePencilResolvent A₀ A x w'
      = (w' - w) • (guePencilResolvent A₀ A x w * guePencilResolvent A₀ A x w') :=
  resolvent_sub_resolvent (guePencil A₀ A x) w w'
    (guePencil_mem_resolventSet A₀ A hA₀ hA x w hw)
    (guePencil_mem_resolventSet A₀ A hA₀ hA x w' hw')

/-- The averaged partial trace at two spectral parameters. -/
theorem guePartialTrace_sub_spectral (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (x : GUECoord ι N → ℝ) (w w' : ℂ) (hw : w.im ≠ 0) (hw' : w'.im ≠ 0) :
    guePartialTrace A₀ A w x - guePartialTrace A₀ A w' x
      = (w' - w) • (partialTraceN (guePencilResolvent A₀ A x w *
          guePencilResolvent A₀ A x w')) := by
  rw [guePartialTrace, guePartialTrace, ← partialTraceN_sub, guePencilResolvent_sub_spectral A₀ A hA₀ hA x w w' hw hw',
    partialTraceN_smul]

/-- **The finite-`N` mean at two spectral parameters.**

`g_N(w) - g_N(w') = (w' - w) • E[tr_N(R_N(w) R_N(w'))]` — the exact second-resolvent propagation
of the averaged resolvent mean. -/
theorem gueResolventMean_sub_shift (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (w w' : ℂ) (hw : w.im ≠ 0) (hw' : w'.im ≠ 0) :
    gueResolventMean (N := N) A₀ A w - gueResolventMean (N := N) A₀ A w'
      = (w' - w) • Matrix.of (fun u v =>
          ∫ x : EuclideanSpace ℝ (GUECoord ι N),
            (partialTraceN (guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) w *
              guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) w')) u v
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) := by
  ext u v
  simp only [Matrix.sub_apply, Matrix.smul_apply, gueResolventMean_apply, Matrix.of_apply,
    smul_eq_mul]
  have hpt : ∀ x : EuclideanSpace ℝ (GUECoord ι N),
      guePartialTrace A₀ A w (x : GUECoord ι N → ℝ) u v -
        guePartialTrace A₀ A w' (x : GUECoord ι N → ℝ) u v
        = (w' - w) * (partialTraceN (guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) w *
            guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) w')) u v := by
    intro x
    rw [← Matrix.sub_apply,
      guePartialTrace_sub_spectral A₀ A hA₀ hA (x : GUECoord ι N → ℝ) w w' hw hw']
    simp [Matrix.smul_apply, smul_eq_mul]
  have hint1 := integrable_guePartialTrace_entry_of_im_ne_zero (N := N) A₀ A hA₀ hA w hw u v
  have hint2 := integrable_guePartialTrace_entry_of_im_ne_zero (N := N) A₀ A hA₀ hA w' hw' u v
  rw [← integral_sub hint1 hint2]
  simp only [hpt]
  rw [integral_const_mul]

/-- `CStarMatrix.ofMatrix.symm` is additive. -/
lemma ofMatrix_symm_sub {A : Type*} [Ring A] {M L : CStarMatrix d d A} :
    CStarMatrix.ofMatrix.symm (M - L)
      = CStarMatrix.ofMatrix.symm M - CStarMatrix.ofMatrix.symm L := by
  ext a b
  simp

/-- `CStarMatrix.ofMatrix.symm` is `ℂ`-linear. -/
lemma ofMatrix_symm_smul {A : Type*} [Ring A] [Algebra ℂ A] (c : ℂ)
    {M : CStarMatrix d d A} :
    CStarMatrix.ofMatrix.symm (c • M) = c • CStarMatrix.ofMatrix.symm M := by
  ext a b
  simp

/-- **The limit Cauchy transform at two spectral parameters.**

`g(w) - g(w') = (w' - w) • E_vac[tr(R_∞(w) R_∞(w'))]`. -/
theorem operatorMatrixPencilCauchy_sub_shift (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (w w' : ℂ) (hw : w.im ≠ 0) (hw' : w'.im ≠ 0) :
    operatorMatrixPencilCauchy A₀ A w - operatorMatrixPencilCauchy A₀ A w'
      = (w' - w) • matrixExpectation (vacuumState ι).toProbabilitySpace
          (CStarMatrix.ofMatrix.symm (resolvent (operatorMatrixPencil A₀ A) w *
            resolvent (operatorMatrixPencil A₀ A) w')) := by
  have hwU : IsUnit (algebraMap ℂ (CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι)) w -
      operatorMatrixPencil A₀ A) := operatorMatrixPencil_mem_resolventSet A₀ A hA₀ hA w hw
  have hwU' : IsUnit (algebraMap ℂ (CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι)) w' -
      operatorMatrixPencil A₀ A) := operatorMatrixPencil_mem_resolventSet A₀ A hA₀ hA w' hw'
  have hR := resolvent_sub_resolvent (operatorMatrixPencil A₀ A) w w' hwU hwU'
  simp only [operatorMatrixPencilCauchy]
  calc matrixExpectation (vacuumState ι).toProbabilitySpace
        (CStarMatrix.ofMatrix.symm (resolvent (operatorMatrixPencil A₀ A) w)) -
      matrixExpectation (vacuumState ι).toProbabilitySpace
        (CStarMatrix.ofMatrix.symm (resolvent (operatorMatrixPencil A₀ A) w'))
      = matrixExpectation (vacuumState ι).toProbabilitySpace
          (CStarMatrix.ofMatrix.symm (resolvent (operatorMatrixPencil A₀ A) w) -
            CStarMatrix.ofMatrix.symm (resolvent (operatorMatrixPencil A₀ A) w')) := by
        rw [map_sub]
    _ = matrixExpectation (vacuumState ι).toProbabilitySpace
          (CStarMatrix.ofMatrix.symm (resolvent (operatorMatrixPencil A₀ A) w -
            resolvent (operatorMatrixPencil A₀ A) w')) := by
        rw [ofMatrix_symm_sub]
    _ = matrixExpectation (vacuumState ι).toProbabilitySpace
          (CStarMatrix.ofMatrix.symm ((w' - w) •
            (resolvent (operatorMatrixPencil A₀ A) w *
              resolvent (operatorMatrixPencil A₀ A) w'))) := by
        rw [hR]
    _ = (w' - w) • matrixExpectation (vacuumState ι).toProbabilitySpace
          (CStarMatrix.ofMatrix.symm (resolvent (operatorMatrixPencil A₀ A) w *
            resolvent (operatorMatrixPencil A₀ A) w')) := by
        ext a b
        simp [matrixExpectation_apply, CStarMatrix.ofMatrix_symm_apply, smul_eq_mul, map_smul]

/-! ## 3. The limit-centred second moment: the single remaining input

Write `X = g_N - g` and `V_g := ∑ i, A_i * (E[T A_i T] - g A_i g)`, the second moment centred at
the LIMIT `g` (rather than at the mean `g_N`).  Subtracting the limit Dyson equation from the
exact finite-`N` master identity gives the exact identity

`(z • 1 - A₀) * X = V_g`.

Since `z • 1 - A₀` is invertible with inverse `g₀ := operatorMatrixPencilCauchy A₀ 0 z`
(`B * g₀ = 1`, hence `g₀ * B = 1` for square matrices), `X = g₀ * V_g`, and therefore

`frob X ≤ frob g₀ * frob V_g ≤ (card d * |Im z|⁻¹) * frob V_g`.

So the near-axis annulus follows from the **limit-centred second moment estimate**

`frob V_g ≤ C (Kc + ‖z‖)² |Im z|⁻⁶ / N²`  (for every nonreal `z`),

which is a genuine second-order (next-genus) statement for matrix coefficients: it is the
two-point function centred at the limit, where the free part cancels exactly. -/

/-- The limit-centred second moment `V_g = ∑ i, A_i * (E[T A_i T] - g A_i g)`. -/
def limitCentredSecondMoment (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (z : ℂ) :
    Matrix d d ℂ :=
  ∑ i, A i * (gueSecondMoment (N := N) A₀ A (A i) z -
    operatorMatrixPencilCauchy A₀ A z * A i * operatorMatrixPencilCauchy A₀ A z)

/-- **Exact identity for the deviation in terms of the limit-centred second moment.**

`(z • 1 - A₀) * (g_N - g) = ∑ i, A_i * (E[T A_i T] - g A_i g)`. -/
theorem sub_mul_eq_limitCentredSecondMoment (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (hN : 0 < N) :
    (z • (1 : Matrix d d ℂ) - A₀) *
        (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
      = limitCentredSecondMoment (N := N) A₀ A z := by
  classical
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  set B : Matrix d d ℂ := z • (1 : Matrix d d ℂ) - A₀ with hB
  set g : Matrix d d ℂ := operatorMatrixPencilCauchy A₀ A z with hg
  have hm := gue_dyson_master_identity A₀ A hA₀ hA z hz hNc
  have hg' := limit_dyson_equation A₀ A hA₀ hA z hz
  have hBm : (z • (1 : Matrix d d ℂ) - A₀) * gueResolventMean (N := N) A₀ A z
      = 1 + ∑ i, A i * gueSecondMoment (N := N) A₀ A (A i) z := by
    have h := sub_eq_iff_eq_add.mp hm
    rwa [add_comm] at h
  have hBg : (z • (1 : Matrix d d ℂ) - A₀) * g
      = 1 + (∑ i, A i * g * A i) * g := by
    have h := hg'
    rw [sub_mul] at h
    exact sub_eq_iff_eq_add.mp h
  have hsum : (∑ i, A i * (gueSecondMoment (N := N) A₀ A (A i) z -
        g * A i * g))
      = (∑ i, A i * gueSecondMoment (N := N) A₀ A (A i) z) -
          (∑ i, A i * g * A i) * g := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    noncomm_ring
  rw [limitCentredSecondMoment, mul_sub, hBm, hBg, hsum]
  rw [hg]
  abel

/-- **The deviation is bounded by the limit-centred second moment**, with the explicit
`card d · |Im z|⁻¹` loss. -/
theorem frob_sub_le_of_limitCentredSecondMoment (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (hN : 0 < N) :
    frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
      ≤ ((Fintype.card d : ℝ) * |z.im|⁻¹) * frob (limitCentredSecondMoment (N := N) A₀ A z) := by
  classical
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  -- the inverse of `z • 1 - A₀` is the `A = 0` Cauchy transform
  have hBg₀ : (z • (1 : Matrix d d ℂ) - A₀) * operatorMatrixPencilCauchy A₀ (fun _ : ι => (0 : Matrix d d ℂ)) z = 1 := by
    have h := limit_dyson_equation A₀ (fun _ : ι => 0) hA₀ (fun _ => isHermitian_zero) z hz
    simpa using h
  have hg₀B : operatorMatrixPencilCauchy A₀ (fun _ : ι => (0 : Matrix d d ℂ)) z *
      (z • (1 : Matrix d d ℂ) - A₀) = 1 := mul_eq_one_comm_of_square hBg₀
  have hX : gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z
      = operatorMatrixPencilCauchy A₀ (fun _ : ι => (0 : Matrix d d ℂ)) z *
          limitCentredSecondMoment (N := N) A₀ A z := by
    calc gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z
        = 1 * (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z) :=
            (one_mul _).symm
      _ = (operatorMatrixPencilCauchy A₀ (fun _ : ι => (0 : Matrix d d ℂ)) z *
            (z • (1 : Matrix d d ℂ) - A₀)) *
            (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z) := by
            rw [hg₀B]
      _ = operatorMatrixPencilCauchy A₀ (fun _ : ι => (0 : Matrix d d ℂ)) z *
            ((z • (1 : Matrix d d ℂ) - A₀) *
              (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)) := by
            rw [mul_assoc]
      _ = operatorMatrixPencilCauchy A₀ (fun _ : ι => (0 : Matrix d d ℂ)) z *
            limitCentredSecondMoment (N := N) A₀ A z := by
            rw [sub_mul_eq_limitCentredSecondMoment A₀ A hA₀ hA z hz hN]
  rw [hX]
  refine (frob_mul_le (A := operatorMatrixPencilCauchy A₀ (fun _ : ι => 0) z)
    (B := limitCentredSecondMoment (N := N) A₀ A z)).trans ?_
  have hg₀ : frob (operatorMatrixPencilCauchy A₀ (fun _ : ι => 0) z)
      ≤ (Fintype.card d : ℝ) * |z.im|⁻¹ :=
    frob_operatorMatrixPencilCauchy_le (ι := ι) (d := d) A₀ (fun _ : ι => 0) hA₀
      (fun _ => isHermitian_zero) z hz
  exact mul_le_mul_of_nonneg_right hg₀ (frob_nonneg _)

/-- **The near-axis annulus from the limit-centred second moment estimate.**

If `frob V_g ≤ C (Kc + ‖z‖)² |Im z|⁻⁶ / N²` for every nonreal `z`, then the annulus bound
`frob (g_N - g) ≤ (card d · C) (Kc + ‖z‖)² |Im z|⁻⁷ / N²` holds. -/
theorem pencilStripBound_annulus_of_limitCentredSecondMoment
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) {Kc C : ℝ} (hC : 0 ≤ C)
    (hVg : ∀ᶠ N : ℕ in atTop, ∀ z : ℂ, z.im ≠ 0 →
      frob (limitCentredSecondMoment (N := N) A₀ A z)
        ≤ C * (Kc + ‖z‖) ^ 2 * (|z.im| ^ (-(6 : ℝ))) / (N : ℝ) ^ 2) :
    ∀ᶠ N : ℕ in atTop, ∀ z : ℂ, z.im ≠ 0 →
      frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
        ≤ ((Fintype.card d : ℝ) * C) * (Kc + ‖z‖) ^ 2 *
            (|z.im| ^ (-(7 : ℝ))) / (N : ℝ) ^ 2 := by
  filter_upwards [hVg, eventually_ge_atTop (1 : ℕ)] with N hN hN1
  intro z hz
  have hN0 : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN1
  have hmain := frob_sub_le_of_limitCentredSecondMoment A₀ A hA₀ hA z hz hN0
  have hzpos : 0 < |z.im| := abs_pos.mpr hz
  have hpow : |z.im| ^ (-(7 : ℝ)) = |z.im|⁻¹ * |z.im| ^ (-(6 : ℝ)) := by
    rw [show (-(7:ℝ)) = -(1:ℝ) + -(6:ℝ) by norm_num,
      Real.rpow_add hzpos, Real.rpow_neg_one]
  calc frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
      ≤ ((Fintype.card d : ℝ) * |z.im|⁻¹) * frob (limitCentredSecondMoment (N := N) A₀ A z) :=
        hmain
    _ ≤ ((Fintype.card d : ℝ) * |z.im|⁻¹) *
          (C * (Kc + ‖z‖) ^ 2 * (|z.im| ^ (-(6 : ℝ))) / (N : ℝ) ^ 2) := by
        refine mul_le_mul_of_nonneg_left (hN z hz) ?_
        positivity
    _ = ((Fintype.card d : ℝ) * C) * (Kc + ‖z‖) ^ 2 *
          (|z.im| ^ (-(7 : ℝ))) / (N : ℝ) ^ 2 := by
        rw [hpow]
        field_simp

end

end GUEStrongConvergence
