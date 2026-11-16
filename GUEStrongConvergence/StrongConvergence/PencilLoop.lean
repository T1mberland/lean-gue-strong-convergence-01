/-
# The matrix (pencil) loop identity, and the deterministic-coefficient case

`Probability/ScalarLoopCore.lean` isolates the exact scalar loop identity

`(m - g) * (z - m - g) = Var`,   `Var = E[(T_N - m)²]`,

which gives `|m - g| ≤ |Var| / |Im z|` with **no** threshold on `|Im z|` (the sign facts make
`|Im (z - m - g)| ≥ |Im z|`).  The scalar closed form is a consequence of two special features of
`d = 1`, `A = 1`:

* the exact finite-`N` identity is `z * m - 1 = E[T_N²]`, so subtracting the limit Dyson
  equation `(z - g) * g = 1` leaves `z (m - g) = E[T²] - g²`;
* `m² - g² = (m - g)(m + g)` because scalars commute.

For a general Hermitian pencil `(A₀, A)` the exact finite-`N` identity is the matrix master
identity `gue_dyson_master_identity` (`Probability/DysonMasterIdentity.lean`),

`(z • 1 - A₀) * g_N - 1 = ∑ i, A_i * E[T_N * A_i * T_N]`,

whose quadratic term couples the *random* partial trace through every direction coefficient.  This
file determines exactly what survives.

## Main results

* `mul_eq_one_comm_of_square` — for square complex matrices a right inverse is a left inverse;
* `gueResolventMean_eq_operatorMatrixPencilCauchy_of_noDirections` — **deterministic
  coefficients**: if `A = 0` then `g_N = g` *exactly* (both satisfy `(z • 1 - A₀) X = 1`);
* `weightedStripBoundProven_noDirections` — consequently the honest strip hypothesis
  `WeightedStripBoundProven A₀ 0 η₀ Kc 0` holds with `C_s = 0` for **every** `η₀`;
* `weightedStripDataAtRepairGen_noDirections` — the corrected bundle of
  `StrongConvergence/CorrectedEndgame.lean` is inhabited at **arbitrary coefficient dimension**
  and arbitrary Hermitian `A₀` in the deterministic case (a genuine, non-degenerate non-vacuity
  witness, improving the `d = 0` witness there);
* `gue_dyson_loop_identity` — **the matrix loop identity**:

  `g_N - g = g * (∑ i, A_i * (g_N - g) * A_i) * g_N + g * Var`,

  with `Var = ∑ i, A_i * E[T_N * A_i * T_N] - (∑ i, A_i * g_N * A_i) * g_N` the second-order
  fluctuation.  The first term is the genuine obstruction: it is linear in `g_N - g`, and the
  scalar case is exactly the one where it can be absorbed into the denominator
  (`(m - g)(1 - g²) = g Var`), which requires `∑ A_i X A_i = X`.

## What this means for the near-axis annulus — **the annulus is NOT closed**

The matrix identity shows that the threshold-free scalar bootstrap does **not** generalise: the
residual operator `X ↦ g (∑ A_i X A_i) g_N` is linear in `X` but must be inverted (or shown
contractive) to solve for `g_N − g`.  Its contraction constant is `‖g‖ ‖g_N‖ ∑ ‖A_i‖²`; with
`‖g‖, ‖g_N‖ ≤ card d / |Im z|` this is `(card d)² ∑‖A_i‖² / |Im z|² < 1`, **exactly the
threshold of `dyson_stability`**.  `loop_bootstrap_matrix` records this dependence.

The sign facts of `ScalarLoopSignComplete.lean` do not help here: they give information about
`Im g` and `Im g_N` (the imaginary parts of the *coefficients*), while the obstruction is an
*operator* norm.  Rewriting the identity in the scalar form `(m − g)(z − m − g) = Var` would
require `∑ i, A_i X A_i = X` for all `X`, which is the scalar (`d = 1`, `A = 1`) specialization.

What *is* available, and is proved here:

* the exact matrix identity (§4) and the explicit linearized bootstrap (§5);
* the variance side: the fluctuation term is `O(N⁻² |Im z|⁻⁴)` with the sharp constant (§6),
  via `covariance_partialTrace_mul_le_sharp`;
* the deterministic-coefficient case `A = 0` is exact: `g_N = g` for every `N ≥ 1` (§2–§3).

So the honest residual input for the near-axis annulus is precisely a bound on the inverse of
`1 − (X ↦ g (∑ A_i X A_i) g_N)` (equivalently the Neumann contraction above); it is *not* a
consequence of the sign facts.

No `sorry`, no new axioms.
-/
import GUEStrongConvergence.Probability.DysonLimit
import GUEStrongConvergence.Probability.DysonMasterIdentity
import GUEStrongConvergence.StrongConvergence.CorrectedEndgame

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
  {N : ℕ}

/-! ## 1. Square matrices: a right inverse is a left inverse -/

/-- For square complex matrices a right inverse is a left inverse (determinant argument). -/
theorem mul_eq_one_comm_of_square {A B : Matrix d d ℂ} (h : A * B = 1) : B * A = 1 := by
  have h1 : A.det * B.det = 1 := by
    have := congrArg Matrix.det h
    rwa [Matrix.det_mul, Matrix.det_one] at this
  have hB : B.det ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h1
    exact zero_ne_one h1
  have hunit : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  calc B * A = B * A * 1 := by rw [mul_one]
    _ = B * A * (B * B⁻¹) := by rw [Matrix.mul_nonsing_inv B hunit]
    _ = B * (A * B) * B⁻¹ := by noncomm_ring
    _ = B * 1 * B⁻¹ := by rw [h]
    _ = B * B⁻¹ := by rw [mul_one]
    _ = 1 := Matrix.mul_nonsing_inv B hunit

/-! ## 2. The deterministic-coefficient case: `A = 0` gives `g_N = g` exactly -/

/-- **If all direction coefficients vanish, the finite-`N` mean equals its limit exactly.**

With `A = 0` the master identity reads `(z • 1 - A₀) * g_N = 1` and the limit Dyson equation reads
`(z • 1 - A₀) * g = 1`; since `z • 1 - A₀` is invertible for nonreal `z`, `g_N = g`.  No
threshold and no variance input is used. -/
theorem gueResolventMean_eq_operatorMatrixPencilCauchy_of_noDirections
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) (hN : 0 < N) :
    gueResolventMean (N := N) A₀ (fun _ : ι => 0) z =
      operatorMatrixPencilCauchy A₀ (fun _ : ι => 0) z := by
  classical
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have h1 : (z • (1 : Matrix d d ℂ) - A₀) * gueResolventMean (N := N) A₀ (fun _ : ι => 0) z
      = 1 := by
    have h := gue_dyson_master_identity A₀ (fun _ : ι => 0) hA₀
      (fun _ => isHermitian_zero) z hz hNc
    have h0 : (z • (1 : Matrix d d ℂ) - A₀) *
        gueResolventMean (N := N) A₀ (fun _ : ι => 0) z - 1 = 0 := by
      simpa using h
    exact sub_eq_zero.mp h0
  have h2 : (z • (1 : Matrix d d ℂ) - A₀) * operatorMatrixPencilCauchy A₀ (fun _ : ι => 0) z
      = 1 := by
    have h := limit_dyson_equation A₀ (fun _ : ι => 0) hA₀ (fun _ => isHermitian_zero) z hz
    simpa using h
  have h3 : (z • (1 : Matrix d d ℂ) - A₀) *
      (gueResolventMean (N := N) A₀ (fun _ : ι => 0) z -
        operatorMatrixPencilCauchy A₀ (fun _ : ι => 0) z) = 0 := by
    rw [mul_sub, h1, h2, sub_self]
  -- invertibility of `z • 1 - A₀` from `h2`
  have hleft := mul_eq_one_comm_of_square h2
  have hzero : gueResolventMean (N := N) A₀ (fun _ : ι => 0) z -
      operatorMatrixPencilCauchy A₀ (fun _ : ι => 0) z = 0 := by
    calc gueResolventMean (N := N) A₀ (fun _ : ι => 0) z -
          operatorMatrixPencilCauchy A₀ (fun _ : ι => 0) z
        = 1 * (gueResolventMean (N := N) A₀ (fun _ : ι => 0) z -
            operatorMatrixPencilCauchy A₀ (fun _ : ι => 0) z) := (one_mul _).symm
      _ = (operatorMatrixPencilCauchy A₀ (fun _ : ι => 0) z *
            (z • (1 : Matrix d d ℂ) - A₀)) *
            (gueResolventMean (N := N) A₀ (fun _ : ι => 0) z -
              operatorMatrixPencilCauchy A₀ (fun _ : ι => 0) z) := by rw [hleft]
      _ = operatorMatrixPencilCauchy A₀ (fun _ : ι => 0) z *
            ((z • (1 : Matrix d d ℂ) - A₀) *
              (gueResolventMean (N := N) A₀ (fun _ : ι => 0) z -
                operatorMatrixPencilCauchy A₀ (fun _ : ι => 0) z)) := by
            rw [mul_assoc]
      _ = 0 := by rw [h3, mul_zero]
  exact sub_eq_zero.mp hzero

/-- The Frobenius norm of the averaged resolvent difference vanishes with vanishing directions. -/
theorem frob_gueResolventMean_sub_limit_eq_zero_of_noDirections
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) (hN : 0 < N) :
    frob (gueResolventMean (N := N) A₀ (fun _ : ι => 0) z -
      operatorMatrixPencilCauchy A₀ (fun _ : ι => 0) z) = 0 := by
  rw [gueResolventMean_eq_operatorMatrixPencilCauchy_of_noDirections (ι := ι) A₀ hA₀ z hz hN,
    sub_self]
  simp [frob]

/-! ## 3. The honest strip bound and the corrected bundle in the deterministic case -/

/-- **The honest weighted strip bound holds with `C_s = 0` for vanishing directions**, for every
`η₀` and every polynomial weight constant `Kc`. -/
theorem weightedStripBoundProven_noDirections (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    {η₀ Kc : ℝ} :
    WeightedStripBoundProven A₀ (fun _ : ι => 0) η₀ Kc 0 := by
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  intro z hz _
  have hzero := frob_gueResolventMean_sub_limit_eq_zero_of_noDirections
    (ι := ι) (N := n) A₀ hA₀ z hz (by omega)
  rw [hzero]
  simp

/-- **The corrected endgame bundle is inhabited with arbitrary coefficient dimension and
arbitrary Hermitian `A₀`** in the deterministic-coefficient case, for every compact target set
and every `ε > 0`.  This is a genuine (non-degenerate) non-vacuity witness for
`WeightedStripDataAtRepairGen`, improving the `d = 0` witness of `CorrectedEndgame.lean`. -/
theorem weightedStripDataAtRepairGen_noDirections {r n : ℕ} {S : Set ℝ} (hS : IsCompact S)
    {ε : ℝ} (hε : 0 < ε) (A₀ : Matrix (Fin n) (Fin n) ℂ) (hA₀ : A₀.IsHermitian) :
    WeightedStripDataAtRepairGen r n A₀ (fun _ : Fin r => 0) S ε := by
  obtain ⟨f, hcut, h9, h9w, hfc⟩ := shiftedCutoff_nonempty hS hε
  refine ⟨3, 0, 0, by norm_num, le_rfl, f, hcut, h9, h9w, hfc, ?_⟩
  exact weightedStripBoundProven_noDirections (ι := Fin r) (d := Fin n) A₀ hA₀

/-! ## 4. The exact matrix loop identity

Subtracting the limit Dyson equation from the exact finite-`N` master identity does not close into
the scalar form `(m - g)(z - m - g) = Var`: the coefficient quadratic form produces the residual
operator `X ↦ g (∑ i, A_i X A_i) g_N`.  The exact statement is the following. -/

/-- **The exact matrix loop identity.**

With `m = g_N(z)`, `g = g(z)` and `Var = ∑ i, A_i * E[T_N A_i T_N] - (∑ i, A_i m A_i) m` (the
second-order fluctuation), the difference `m - g` satisfies the exact linear fixed-point equation

`m - g = g * (∑ i, A_i * (m - g) * A_i) * m + g * Var`.

The scalar loop identity `(m - g)(z - m - g) = Var` (`loop_identity_of_dyson`) is the special case
in which the residual term can be absorbed, i.e. `∑ i, A_i X A_i = X` (true for `d = 1`, `A = 1`).
For a general pencil the residual term must be inverted (or shown contractive); its contraction
constant is `‖g‖ ‖m‖ ∑ ‖A_i‖²`, which is exactly the threshold of `dyson_stability`. -/
theorem gue_dyson_loop_identity
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (hN : 0 < N) :
    gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z
      = operatorMatrixPencilCauchy A₀ A z *
          (∑ i, A i * (gueResolventMean (N := N) A₀ A z -
            operatorMatrixPencilCauchy A₀ A z) * A i) *
          gueResolventMean (N := N) A₀ A z
        + operatorMatrixPencilCauchy A₀ A z *
          ((∑ i, A i * (Matrix.of fun u v =>
              ∫ x, (guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) * A i *
                guePartialTrace A₀ A z (x : GUECoord ι N → ℝ)) u v
              ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))))
            - (∑ i, A i * gueResolventMean (N := N) A₀ A z * A i) *
              gueResolventMean (N := N) A₀ A z) := by
  classical
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  set m : Matrix d d ℂ := gueResolventMean (N := N) A₀ A z with hm
  set g : Matrix d d ℂ := operatorMatrixPencilCauchy A₀ A z with hg
  set S1 : Matrix d d ℂ := ∑ i, A i * (Matrix.of fun u v =>
      ∫ x, (guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) * A i *
        guePartialTrace A₀ A z (x : GUECoord ι N → ℝ)) u v
      ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) with hS1
  set Sg : Matrix d d ℂ := ∑ i, A i * g * A i with hSg
  set Sm : Matrix d d ℂ := ∑ i, A i * m * A i with hSm
  have h1 : (z • (1 : Matrix d d ℂ) - A₀) * m - 1 = S1 := by
    rw [hS1, hm]
    exact gue_dyson_master_identity A₀ A hA₀ hA z hz hNc
  have h2 : (z • (1 : Matrix d d ℂ) - A₀ - Sg) * g = 1 := by
    rw [hSg, hg]
    exact limit_dyson_equation A₀ A hA₀ hA z hz
  have h2' : g * (z • (1 : Matrix d d ℂ) - A₀ - Sg) = 1 := mul_eq_one_comm_of_square h2
  have hBm : (z • (1 : Matrix d d ℂ) - A₀) * m = 1 + S1 := by
    have hh := sub_eq_iff_eq_add.mp h1
    rwa [add_comm] at hh
  have hBg : (z • (1 : Matrix d d ℂ) - A₀) * g = 1 + Sg * g := by
    rw [sub_mul] at h2
    exact sub_eq_iff_eq_add.mp h2
  have hBX : (z • (1 : Matrix d d ℂ) - A₀) * (m - g) = S1 - Sg * g := by
    rw [mul_sub, hBm, hBg]
    abel
  have hkey : (z • (1 : Matrix d d ℂ) - A₀ - Sg) * (m - g) = S1 - Sg * m := by
    rw [sub_mul, hBX, mul_sub]
    abel
  have hX : m - g = g * (S1 - Sg * m) := by
    calc m - g = 1 * (m - g) := (one_mul _).symm
      _ = (g * (z • (1 : Matrix d d ℂ) - A₀ - Sg)) * (m - g) := by rw [h2']
      _ = g * ((z • (1 : Matrix d d ℂ) - A₀ - Sg) * (m - g)) := mul_assoc _ _ _
      _ = g * (S1 - Sg * m) := by rw [hkey]
  have hD : Sm - Sg = ∑ i, A i * (m - g) * A i := by
    rw [hSm, hSg, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by noncomm_ring
  calc m - g = g * (S1 - Sg * m) := hX
    _ = g * (∑ i, A i * (m - g) * A i) * m + g * (S1 - Sm * m) := by
        rw [← hD]
        noncomm_ring

/-! ## 5. The linearized bootstrap: what the matrix loop identity really needs

The exact identity of §4 has the shape `X = g * D * m + g * Var` with `D = ∑ i, A_i X A_i`
linear in `X`.  The matrix analogue of `loop_bootstrap` must therefore solve for `X`, and this
*requires* a contraction hypothesis: this is exactly the threshold of `dyson_stability`.  The
lemma below makes the dependence explicit; it is the honest form of the matrix bootstrap. -/

/-- **Matrix linearized bootstrap.**  From `X = g * D * m + g * Var` with `frob D ≤ S * frob X`
(the coefficient quadratic form) and the contraction `‖g‖ S ‖m‖ < 1`,

`frob X ≤ ‖g‖ frob Var / (1 - ‖g‖ S ‖m‖)`.

With `‖g‖, ‖m‖ ≤ card d / |Im z|` the contraction is `(card d)² S / |Im z|² < 1`, i.e. precisely
the threshold of `dyson_stability`; there is no argument (and in particular none using the sign
facts, which only bound `Im g` and `Im m`) that removes it. -/
theorem loop_bootstrap_matrix {X g m Var D : Matrix d d ℂ} {S : ℝ}
    (hid : X = g * D * m + g * Var)
    (hD : frob D ≤ S * frob X)
    (hcontr : ‖g‖ * S * ‖m‖ < 1) :
    frob X ≤ ‖g‖ * frob Var / (1 - ‖g‖ * S * ‖m‖) := by
  have hx : frob X ≤ ‖g‖ * S * frob X * ‖m‖ + ‖g‖ * frob Var := by
    have h1 : frob (g * D * m) ≤ frob g * frob D * frob m := by
      calc frob (g * D * m) ≤ frob (g * D) * frob m := frob_mul_le _ _
        _ ≤ (frob g * frob D) * frob m :=
            mul_le_mul_of_nonneg_right (frob_mul_le g D) (frob_nonneg m)
    have h2 : frob (g * Var) ≤ frob g * frob Var := frob_mul_le _ _
    have h3 : frob g * frob D * frob m ≤ frob g * (S * frob X) * frob m := by
      refine mul_le_mul_of_nonneg_right ?_ (frob_nonneg m)
      exact mul_le_mul_of_nonneg_left hD (frob_nonneg g)
    calc frob X = frob (g * D * m + g * Var) := by rw [hid]
      _ ≤ frob (g * D * m) + frob (g * Var) := frob_add_le _ _
      _ ≤ frob g * frob D * frob m + frob g * frob Var := add_le_add h1 h2
      _ ≤ frob g * (S * frob X) * frob m + frob g * frob Var :=
          add_le_add h3 le_rfl
      _ = ‖g‖ * S * frob X * ‖m‖ + ‖g‖ * frob Var := by
          rw [frob_eq_norm g, frob_eq_norm m]
          ring
  have hpos : 0 < 1 - ‖g‖ * S * ‖m‖ := by linarith
  rw [le_div_iff₀ hpos]
  nlinarith [hx, frob_nonneg X]

/-! ## 6. The fluctuation term is `O(N⁻² |Im z|⁻⁴)`: the variance side is available -/

/-- The matrix second moment `E[T_N(z) * B * T_N(z)]` of the averaged partial trace. -/
def gueSecondMoment (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (B : Matrix d d ℂ) (z : ℂ) :
    Matrix d d ℂ :=
  Matrix.of fun u v =>
    ∫ x, (guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) * B *
      guePartialTrace A₀ A z (x : GUECoord ι N → ℝ)) u v
      ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))

/-- **The fluctuation term of the matrix loop identity is `O(N⁻² (Im z)⁻⁴)`.**

The `Var` of `gue_dyson_loop_identity` is the second-order fluctuation
`∑ i, A_i * (E[T_N A_i T_N] - g_N A_i g_N)` (the two expressions differ only by
`(∑ i, A_i g_N A_i) g_N = ∑ i, A_i g_N A_i g_N`, i.e. by distributivity).  Each summand is
bounded by the sharp covariance estimate `covariance_partialTrace_mul_le_sharp`, giving the
explicit `O(N⁻² (Im z)⁻⁴)` size.  Hence the *variance* side of the matrix bound is a theorem;
only the inversion of the linearized operator of §5 is missing. -/
theorem frob_fluctuation_le_sharp (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (hN : 0 < N) :
    frob (∑ i, A i * (gueSecondMoment (N := N) A₀ A (A i) z -
        gueResolventMean (N := N) A₀ A z * A i * gueResolventMean (N := N) A₀ A z))
      ≤ 2 * (Fintype.card d : ℝ) ^ 2 *
          (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4 / (N : ℝ)) *
          (∑ i, (frob (A i)) ^ 2) := by
  classical
  set vc : ℝ := 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4 / (N : ℝ)
    with hvc
  have hterm : ∀ i : ι,
      frob (gueSecondMoment (N := N) A₀ A (A i) z -
        gueResolventMean (N := N) A₀ A z * A i * gueResolventMean (N := N) A₀ A z)
        ≤ 2 * (Fintype.card d : ℝ) ^ 2 * frob (A i) * vc := by
    intro i
    exact covariance_partialTrace_mul_le_sharp A₀ A hA₀ hA z hz hN (A i) (hA i)
  calc frob (∑ i, A i * (gueSecondMoment (N := N) A₀ A (A i) z -
        gueResolventMean (N := N) A₀ A z * A i * gueResolventMean (N := N) A₀ A z))
      ≤ ∑ i, frob (A i * (gueSecondMoment (N := N) A₀ A (A i) z -
          gueResolventMean (N := N) A₀ A z * A i * gueResolventMean (N := N) A₀ A z)) := by
        simpa using frob_sum_le (Finset.univ : Finset ι) (fun i =>
          A i * (gueSecondMoment (N := N) A₀ A (A i) z -
            gueResolventMean (N := N) A₀ A z * A i * gueResolventMean (N := N) A₀ A z))
    _ ≤ ∑ i, frob (A i) * frob (gueSecondMoment (N := N) A₀ A (A i) z -
          gueResolventMean (N := N) A₀ A z * A i * gueResolventMean (N := N) A₀ A z) :=
        Finset.sum_le_sum fun i _ => frob_mul_le _ _
    _ ≤ ∑ i, frob (A i) * (2 * (Fintype.card d : ℝ) ^ 2 * frob (A i) * vc) :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hterm i) (frob_nonneg _)
    _ = 2 * (Fintype.card d : ℝ) ^ 2 * vc * ∑ i, (frob (A i)) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = 2 * (Fintype.card d : ℝ) ^ 2 *
          (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4 / (N : ℝ)) *
          (∑ i, (frob (A i)) ^ 2) := by rw [hvc]

end

end GUEStrongConvergence
