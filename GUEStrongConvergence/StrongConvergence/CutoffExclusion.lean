/-
# Spectral exclusion for smooth cutoffs (HT05 Lemma 6.3 / Theorem 6.4 skeleton)

This file isolates the **deterministic spectral-exclusion** step of the corrected
smooth-cutoff strategy of Haagerup--Thorbjørnsen (2005).  It does not attempt any of the
analytic estimates (mean convergence of `τ_N(f(H_N))` or the variance/Poincaré bound);
those enter as the explicit hypotheses `(M)` and `(V)` below.

## Structure

* `Matrix.IsHermitian.trace_cfc_eq_sum_eigenvalues` and
  `inv_card_le_normTrace_cfc_of_spectrum_escape`: the deterministic positivity input.
  An eigenvalue of a Hermitian matrix `a` outside `S + (-ε, ε)`, together with a smooth
  cutoff `0 ≤ f`, `f = 1` outside `S + (-ε, ε)`, forces the **normalized trace**
  `m⁻¹ * tr (f(a))` to be at least `1/m`.
* `meas_real_ge_le_integral_sq_div`: Markov's inequality for the square of a real random
  variable.
* `ae_eventually_lt_inv_mul_of_mean_variance`: the probabilistic core.  From
  `|E Z_N| = O(N⁻²)`, `Var Z_N ≤ C N⁻² E W_N` and `E W_N ≤ C' N⁻²` we derive
  `E Z_N² = O(N⁻⁴)`, Markov gives `P(Z_N ≥ 1/(mN)) = O(N⁻²)`, and Borel--Cantelli
  yields `Z_N < 1/(mN)` eventually almost surely.
* `ae_eventually_spectrum_subset`: **Lemma S**.  Almost surely, eventually every real
  spectral value of `H_N` lies in `S + (-ε, ε)`.

The hypotheses `(M)` and `(V)` are stated with `E` and `Var` expanded as Bochner integrals
and `ProbabilityTheory.variance`, matching the analytic inputs owned by the other workers.
-/
import GUEStrongConvergence.Analysis.FaithfulMomentNorm
import GUEStrongConvergence.Probability.CommonSpace
import GUEStrongConvergence.StrongConvergence.FromPencils
import GUEStrongConvergence.StrongConvergence.PolynomialApproximation
import GUEStrongConvergence.StrongConvergence.Target
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Moments.Variance

open Filter MeasureTheory ProbabilityTheory FreeProbability FreeProbability.Fock Matrix
open scoped BigOperators ComplexOrder ENNReal Pointwise Topology

namespace GUEStrongConvergence

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

/-! ## Deterministic part: the normalized trace of a cutoff is large at an escaping eigenvalue -/

/-- Conjugation by a unitary matrix preserves the trace. -/
lemma trace_unitary_conj {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
    (u : unitary (Matrix n n 𝕜)) (x : Matrix n n 𝕜) :
    (((u : Matrix n n 𝕜) * x * star (u : Matrix n n 𝕜))).trace = x.trace := by
  rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]

/-- The continuous functional calculus of a Hermitian matrix, with the Hermitian proof
made explicit (so that it can be passed around without relying on `cfc_tac`). -/
def hermCfc {m : ℕ} (a : Matrix (Fin m) (Fin m) ℂ) (f : ℝ → ℝ) (ha : a.IsHermitian) :
    Matrix (Fin m) (Fin m) ℂ := cfc f a

/-- `hermCfc` agrees with the matrix functional calculus `Matrix.IsHermitian.cfc`. -/
lemma hermCfc_eq {m : ℕ} {a : Matrix (Fin m) (Fin m) ℂ} (ha : a.IsHermitian) (f : ℝ → ℝ) :
    hermCfc a f ha = ha.cfc f := Matrix.IsHermitian.cfc_eq ha f

/-- The trace of `hermCfc a f`, for a Hermitian matrix `a`, is the sum of `f` applied to
its eigenvalues. -/
lemma trace_cfc_eq_sum_eigenvalues {m : ℕ}
    {a : Matrix (Fin m) (Fin m) ℂ} (ha : a.IsHermitian) (f : ℝ → ℝ) :
    (hermCfc a f ha).trace = ∑ i, ((f (ha.eigenvalues i) : ℝ) : ℂ) := by
  rw [hermCfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    trace_unitary_conj, trace_diagonal]
  rfl

/-- The normalized trace of a complex matrix, as a real number (`Re tr`). -/
def normTrace {m : ℕ} (a : Matrix (Fin m) (Fin m) ℂ) : ℝ := (m : ℝ)⁻¹ * a.trace.re

/-- **Deterministic spectral exclusion, one matrix.**  If `a` is Hermitian, `0 ≤ f`,
`f = 1` outside `S + (-ε, ε)`, and `a` has a real spectral value outside that set, then
the normalized trace of `f(a)` is at least `1/m`.

This is the pointwise inequality behind the Markov step: one escaping eigenvalue already
contributes `1` to the unnormalized trace, and positivity of `f` prevents cancellation. -/
theorem inv_card_le_normTrace_cfc_of_spectrum_escape
    {m : ℕ} (hm : 0 < m) {a : Matrix (Fin m) (Fin m) ℂ} (ha : a.IsHermitian)
    {S : Set ℝ} {ε : ℝ} (_hε : 0 < ε) {f : ℝ → ℝ}
    (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, x ∉ S + Set.Ioo (-ε) ε → f x = 1)
    {lam : ℝ} (hlam : lam ∈ spectrum ℝ a) (hesc : lam ∉ S + Set.Ioo (-ε) ε) :
    (m : ℝ)⁻¹ ≤ normTrace (hermCfc a f ha) := by
  have hmem : lam ∈ Set.range ha.eigenvalues := by
    rwa [← Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues ha]
  obtain ⟨i0, rfl⟩ := hmem
  have hsingle : f (ha.eigenvalues i0) = 1 := hf1 _ hesc
  have hsum : (1 : ℝ) ≤ ∑ i, f (ha.eigenvalues i) := by
    calc (1 : ℝ) = f (ha.eigenvalues i0) := hsingle.symm
      _ ≤ ∑ i, f (ha.eigenvalues i) :=
        Finset.single_le_sum (fun i _ => hf0 _) (Finset.mem_univ i0)
  have htrace : (hermCfc a f ha).trace = ((∑ i, f (ha.eigenvalues i) : ℝ) : ℂ) := by
    rw [trace_cfc_eq_sum_eigenvalues ha f, ← Complex.ofReal_sum]
  rw [normTrace, htrace, Complex.ofReal_re]
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  calc (m : ℝ)⁻¹ = (m : ℝ)⁻¹ * 1 := (mul_one _).symm
    _ ≤ (m : ℝ)⁻¹ * ∑ i, f (ha.eigenvalues i) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hmR.le)

/-! ## Markov's inequality for the square -/

/-- Markov's inequality applied to the nonnegative random variable `Z ^ 2`. -/
theorem meas_real_ge_le_integral_sq_div
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {Z : Ω → ℝ} {a : ℝ} (ha : 0 < a)
    (hZ : AEMeasurable Z μ) (hZ2 : Integrable (fun ω => Z ω ^ 2) μ) :
    μ.real {ω | a ≤ Z ω} ≤ (∫ ω, Z ω ^ 2 ∂μ) / a ^ 2 := by
  have hf : AEMeasurable (fun ω => ENNReal.ofReal (Z ω ^ 2)) μ :=
    (hZ.pow_const 2).ennreal_ofReal
  have hε0 : ENNReal.ofReal (a ^ 2) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]
    exact pow_pos ha 2
  have hεtop : ENNReal.ofReal (a ^ 2) ≠ ∞ := ENNReal.ofReal_ne_top
  have hsub : {ω | a ≤ Z ω}
      ⊆ {ω | ENNReal.ofReal (a ^ 2) ≤ ENNReal.ofReal (Z ω ^ 2)} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ ha.le hω 2)
  have hmarkov := meas_ge_le_lintegral_div hf hε0 hεtop (μ := μ)
    (f := fun ω => ENNReal.ofReal (Z ω ^ 2))
  have hlin : (∫⁻ ω, ENNReal.ofReal (Z ω ^ 2) ∂μ) ≠ ∞ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hZ2 (Eventually.of_forall fun ω => sq_nonneg _)]
    exact ENNReal.ofReal_ne_top
  have hdiv : ((∫⁻ ω, ENNReal.ofReal (Z ω ^ 2) ∂μ) / ENNReal.ofReal (a ^ 2)) ≠ ∞ :=
    ENNReal.div_ne_top hlin hε0
  calc μ.real {ω | a ≤ Z ω}
      = (μ {ω | a ≤ Z ω}).toReal := rfl
    _ ≤ (μ {ω | ENNReal.ofReal (a ^ 2) ≤ ENNReal.ofReal (Z ω ^ 2)}).toReal :=
        ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsub)
    _ ≤ ((∫⁻ ω, ENNReal.ofReal (Z ω ^ 2) ∂μ) / ENNReal.ofReal (a ^ 2)).toReal :=
        ENNReal.toReal_mono hdiv hmarkov
    _ = (∫ ω, Z ω ^ 2 ∂μ) / a ^ 2 := by
        rw [ENNReal.toReal_div, ENNReal.toReal_ofReal (sq_nonneg a),
          ← ofReal_integral_eq_lintegral_ofReal hZ2 (Eventually.of_forall fun ω => sq_nonneg _),
          ENNReal.toReal_ofReal (integral_nonneg fun ω => sq_nonneg (Z ω))]

/-! ## Probabilistic core: summability of the bad events -/

/-- **Spectral exclusion from mean and variance bounds.**

Let `Z_N` be real random variables and `W_N` nonnegative random variables with

* `(M)` `|E Z_N| ≤ C / N²` eventually,
* `(V)` `Var Z_N ≤ C / N² * E W_N` and `E W_N ≤ C' / N²`.

Then `Z_N < 1/(mN)` eventually almost surely. -/
theorem ae_eventually_lt_inv_mul_of_mean_variance
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : ℕ} (hm : 0 < m) {C C' : ℝ} (hC : 0 ≤ C) (_hC' : 0 ≤ C')
    (Z W : ℕ → Ω → ℝ)
    (hZ : ∀ N, MemLp (Z N) 2 μ)
    (_hWint : ∀ N, Integrable (W N) μ)
    (_hW0 : ∀ N, 0 ≤ ∫ ω, W N ω ∂μ)
    (hM : ∀ᶠ N in atTop, |∫ ω, Z N ω ∂μ| ≤ C / (N : ℝ) ^ 2)
    (hV : ∀ N, variance (Z N) μ
      ≤ C / (N : ℝ) ^ 2 * ∫ ω, W N ω ∂μ)
    (hWb : ∀ N, ∫ ω, W N ω ∂μ ≤ C' / (N : ℝ) ^ 2) :
    ∀ᵐ ω ∂μ, ∀ᶠ N : ℕ in atTop, Z N ω < ((m : ℝ) * (N : ℝ))⁻¹ := by
  classical
  -- the constant in the `E Z_N ^ 2` bound
  set K : ℝ := C * C' + C ^ 2 with hK
  -- `E Z_N ^ 2 = O(N⁻⁴)`
  have hEZsq : ∀ᶠ N : ℕ in atTop, ∫ ω, Z N ω ^ 2 ∂μ ≤ K / (N : ℝ) ^ 4 := by
    filter_upwards [hM, eventually_ge_atTop (1 : ℕ)] with N hMN hN1
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    have hN4pos : (0 : ℝ) < (N : ℝ) ^ 4 := by positivity
    have hvar : variance (Z N) μ ≤ C * C' / (N : ℝ) ^ 4 := by
      calc variance (Z N) μ
          ≤ C / (N : ℝ) ^ 2 * ∫ ω, W N ω ∂μ := hV N
        _ ≤ C / (N : ℝ) ^ 2 * (C' / (N : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left (hWb N) (by positivity)
        _ = C * C' / (N : ℝ) ^ 4 := by
            field_simp
    have hmean : (∫ ω, Z N ω ∂μ) ^ 2 ≤ C ^ 2 / (N : ℝ) ^ 4 := by
      have hnn : (0 : ℝ) ≤ C / (N : ℝ) ^ 2 := by positivity
      have habs : |∫ ω, Z N ω ∂μ| ≤ C / (N : ℝ) ^ 2 := hMN
      have hsq : (∫ ω, Z N ω ∂μ) ^ 2 ≤ (C / (N : ℝ) ^ 2) ^ 2 := by
        rw [sq_le_sq]
        rwa [abs_of_nonneg hnn]
      calc (∫ ω, Z N ω ∂μ) ^ 2 ≤ (C / (N : ℝ) ^ 2) ^ 2 := hsq
        _ = C ^ 2 / (N : ℝ) ^ 4 := by
            field_simp
    have hvar_eq := variance_eq_sub (hZ N)
    have hdecomp : ∫ ω, Z N ω ^ 2 ∂μ = variance (Z N) μ + (∫ ω, Z N ω ∂μ) ^ 2 := by
      rw [hvar_eq]
      simp only [Pi.pow_apply]
      ring
    calc ∫ ω, Z N ω ^ 2 ∂μ
        = variance (Z N) μ + (∫ ω, Z N ω ∂μ) ^ 2 := hdecomp
      _ ≤ C * C' / (N : ℝ) ^ 4 + C ^ 2 / (N : ℝ) ^ 4 := add_le_add hvar hmean
      _ = K / (N : ℝ) ^ 4 := by
          rw [hK]
          ring
  -- Markov: the bad event has probability `O(N⁻²)`
  have hprob : ∀ᶠ N : ℕ in atTop,
      μ.real {ω | ((m : ℝ) * (N : ℝ))⁻¹ ≤ Z N ω} ≤ K * (m : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
    filter_upwards [hEZsq, eventually_ge_atTop (1 : ℕ)] with N hEZ hN1
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    have hapos : (0 : ℝ) < ((m : ℝ) * (N : ℝ))⁻¹ := by positivity
    have hmarkov := meas_real_ge_le_integral_sq_div hapos (hZ N).aemeasurable
      (hZ N).integrable_sq
    have hN2pos : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
    have hcoef : K / (N : ℝ) ^ 4 / (((m : ℝ) * (N : ℝ))⁻¹) ^ 2
        = K * (m : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
      field_simp
    calc μ.real {ω | ((m : ℝ) * (N : ℝ))⁻¹ ≤ Z N ω}
        ≤ (∫ ω, Z N ω ^ 2 ∂μ) / (((m : ℝ) * (N : ℝ))⁻¹) ^ 2 := hmarkov
      _ ≤ (K / (N : ℝ) ^ 4) / (((m : ℝ) * (N : ℝ))⁻¹) ^ 2 := by
          gcongr
      _ = K * (m : ℝ) ^ 2 / (N : ℝ) ^ 2 := hcoef
  -- summability of the bad probabilities
  have hKsum : Summable (fun N : ℕ => K * (m : ℝ) ^ 2 / (N : ℝ) ^ 2) := by
    have hbase : Summable (fun N : ℕ => 1 / (N : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have hmul : Summable (fun N : ℕ => K * (m : ℝ) ^ 2 * (1 / (N : ℝ) ^ 2)) :=
      hbase.mul_left _
    refine hmul.congr fun N => ?_
    ring
  have hprob' : ∀ᶠ N : ℕ in atTop,
      ‖μ.real {ω | ((m : ℝ) * (N : ℝ))⁻¹ ≤ Z N ω}‖ ≤ K * (m : ℝ) ^ 2 / (N : ℝ) ^ 2 :=
    hprob.mono fun N hN => by
      have hnonneg : 0 ≤ μ.real {ω | ((m : ℝ) * (N : ℝ))⁻¹ ≤ Z N ω} :=
        ENNReal.toReal_nonneg
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      exact hN
  have hprob'' : ∀ᶠ N : ℕ in cofinite,
      ‖μ.real {ω | ((m : ℝ) * (N : ℝ))⁻¹ ≤ Z N ω}‖ ≤ K * (m : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
    simpa [Nat.cofinite_eq_atTop] using hprob'
  have hsumBad : Summable (fun N : ℕ => μ.real {ω | ((m : ℝ) * (N : ℝ))⁻¹ ≤ Z N ω}) :=
    Summable.of_norm_bounded_eventually hKsum hprob''
  -- convert summability of real probabilities into summability of the `ℝ≥0∞` measures
  have hENN : (∑' N : ℕ, μ {ω | ((m : ℝ) * (N : ℝ))⁻¹ ≤ Z N ω}) ≠ ∞ := by
    have hnonneg : ∀ N : ℕ, 0 ≤ μ.real {ω | ((m : ℝ) * (N : ℝ))⁻¹ ≤ Z N ω} := fun N =>
      ENNReal.toReal_nonneg
    have hconv : (∑' N : ℕ, μ {ω | ((m : ℝ) * (N : ℝ))⁻¹ ≤ Z N ω})
        = ∑' N : ℕ, ENNReal.ofReal (μ.real {ω | ((m : ℝ) * (N : ℝ))⁻¹ ≤ Z N ω}) := by
      apply tsum_congr
      intro N
      exact (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
    rw [hconv, ← ENNReal.ofReal_tsum_of_nonneg hnonneg hsumBad]
    exact ENNReal.ofReal_ne_top
  -- Borel--Cantelli
  filter_upwards [MeasureTheory.ae_eventually_notMem (μ := μ) (s := fun (N : ℕ) =>
    {ω | ((m : ℝ) * (N : ℝ))⁻¹ ≤ Z N ω}) hENN] with ω hω
  filter_upwards [hω] with N hN
  exact not_le.mp hN

/-! ## Lemma S: almost-sure spectral exclusion -/

/-- **Lemma S (spectral exclusion) for Hermitian matrices.**

Let `H_N` be random Hermitian `m × m` matrices, `S ⊆ ℝ`, `ε > 0`, and `f : ℝ → ℝ` a
nonnegative cutoff which equals `1` outside `S + (-ε, ε)`.  Assume the two analytic
inputs

* `(M)` the mean of `Z_N = τ_N(f(H_N))` is `O(N⁻²)` (the limit being `τ_∞(f(h)) = 0`),
* `(V)` `Var Z_N ≤ C N⁻² E W_N` with `W_N = τ_N((f')²(H_N))` and `E W_N ≤ C' N⁻²`,

and the `L²`/integrability side conditions.  Then almost surely, eventually no real
spectral value of `H_N` lies outside `S + (-ε, ε)`.

The normalization is the matrix dimension `m`: `τ_N(a) = m⁻¹ Re tr(a)`, and a single
escaping eigenvalue contributes at least `1/m` to `τ_N(f(H_N))`. -/
theorem ae_eventually_spectrum_subset
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : ℕ} (hm : 0 < m) {S : Set ℝ} {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, x ∉ S + Set.Ioo (-ε) ε → f x = 1)
    (H : ℕ → Ω → Matrix (Fin m) (Fin m) ℂ) (hH : ∀ N ω, (H N ω).IsHermitian)
    {C C' : ℝ} (hC : 0 ≤ C) (_hC' : 0 ≤ C')
    (hZ : ∀ N, MemLp (fun ω => normTrace (hermCfc (H N ω) f (hH N ω))) 2 μ)
    (_hWint : ∀ N, Integrable
      (fun ω => normTrace (hermCfc (H N ω) (fun x => (deriv f x) ^ 2) (hH N ω))) μ)
    (_hW0 : ∀ N, 0 ≤ ∫ ω,
      normTrace (hermCfc (H N ω) (fun x => (deriv f x) ^ 2) (hH N ω)) ∂μ)
    (hM : ∀ᶠ N : ℕ in atTop,
      |∫ ω, normTrace (hermCfc (H N ω) f (hH N ω)) ∂μ| ≤ C / (N : ℝ) ^ 2)
    (hV : ∀ N, variance (fun ω => normTrace (hermCfc (H N ω) f (hH N ω))) μ
      ≤ C / (N : ℝ) ^ 2 * ∫ ω,
          normTrace (hermCfc (H N ω) (fun x => (deriv f x) ^ 2) (hH N ω)) ∂μ)
    (hWb : ∀ N, ∫ ω,
        normTrace (hermCfc (H N ω) (fun x => (deriv f x) ^ 2) (hH N ω)) ∂μ
      ≤ C' / (N : ℝ) ^ 2) :
    ∀ᵐ ω ∂μ, ∀ᶠ N : ℕ in atTop,
      spectrum ℝ (H N ω) ⊆ S + Set.Ioo (-ε) ε := by
  have hsmall := ae_eventually_lt_inv_mul_of_mean_variance hm hC _hC'
    (fun N ω => normTrace (hermCfc (H N ω) f (hH N ω)))
    (fun N ω => normTrace (hermCfc (H N ω) (fun x => (deriv f x) ^ 2) (hH N ω)))
    hZ _hWint _hW0 hM hV hWb
  filter_upwards [hsmall] with ω hω
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  filter_upwards [hω, eventually_ge_atTop (1 : ℕ)] with N hNsmall hN1
  intro lam hlam
  by_contra hesc
  have hle : (m : ℝ)⁻¹ ≤ normTrace (hermCfc (H N ω) f (hH N ω)) :=
    inv_card_le_normTrace_cfc_of_spectrum_escape hm (hH N ω) hε hf0 hf1 hlam hesc
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hinv : ((m : ℝ) * (N : ℝ))⁻¹ ≤ (m : ℝ)⁻¹ := by
    rw [mul_inv]
    have hNinv : ((N : ℝ))⁻¹ ≤ 1 := by
      rw [← one_div, div_le_one (by positivity)]
      exact hNR
    calc (m : ℝ)⁻¹ * ((N : ℝ))⁻¹ ≤ (m : ℝ)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hNinv (inv_nonneg.mpr hmR.le)
      _ = (m : ℝ)⁻¹ := mul_one _
  linarith


/-! ## Edge bound from scalar spectral inclusion -/

/-- **Scalar spectral inclusion input.**  Almost surely, for every fixed generator `i`,
every fixed `ε > 0`, and all sufficiently large `N`, every real spectral value of the
individual GUE matrix `G_i` is within `ε` of a spectral value of the semicircular
element `s_i`.

This is the fixed-pencil inclusion specialized to the scalar pencils; it is an explicit
hypothesis (not proved here), exactly as required for the `hEdge` input of
`FinalStatement.lean`. -/
def ScalarSpectralInclusion (r : ℕ) : Prop :=
  ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ i : Fin r, ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
    ∀ a ∈ spectrum ℝ (gueFamily r N x i),
      ∃ b ∈ spectrum ℝ (semicircularFamily r i), |a - b| ≤ ε

/-- The individual GUE matrices are self-adjoint. -/
lemma isSelfAdjoint_gueFamily {r N : ℕ} (x : CommonSpace (Fin r)) (i : Fin r) :
    IsSelfAdjoint (gueFamily r N x i) := by
  change CStarMatrix.ofMatrix ((gueMatrixOn x N i)ᴴ) =
    CStarMatrix.ofMatrix (gueMatrixOn x N i)
  exact congrArg CStarMatrix.ofMatrix (gueMatrixOn_isHermitian x N i)

/-- A self-adjoint element whose real spectrum is contained in `[-R, R]` has norm at most
`R`. -/
lemma norm_le_of_abs_spectrum_le {A : Type*} [CStarAlgebra A] [Nontrivial A]
    [PartialOrder A] [StarOrderedRing A]
    {a : A} (ha : IsSelfAdjoint a) {R : ℝ}
    (h : ∀ x ∈ spectrum ℝ a, |x| ≤ R) : ‖a‖ ≤ R := by
  rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum a ha with hmem | hmem
  · have h' := h _ hmem
    rwa [abs_of_nonneg (norm_nonneg a)] at h'
  · have h' := h _ hmem
    rwa [abs_neg, abs_of_nonneg (norm_nonneg a)] at h'

/-- **Operator-norm edge bound.**  Scalar spectral inclusion and `‖s_i‖ = 2` bound every
GUE generator by `3` eventually, almost surely. -/
theorem eventually_norm_gueFamily_le_three_of_scalarSpectralInclusion {r : ℕ}
    (h : ScalarSpectralInclusion r) :
    ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ᶠ N : ℕ in atTop,
      ∀ i : Fin r, ‖gueFamily r N x i‖ ≤ 3 := by
  letI : Nontrivial (closedSemicircularAlgebra (Fin r)) :=
    (closedGeneratedVacuumState (Fin r)).toProbabilitySpace.nontrivial
  filter_upwards [h] with x hx
  have hN : ∀ i : Fin r, ∀ᶠ N : ℕ in atTop,
      ∀ a ∈ spectrum ℝ (gueFamily r N x i),
        ∃ b ∈ spectrum ℝ (semicircularFamily r i), |a - b| ≤ (1 : ℝ) :=
    fun i => hx i 1 one_pos
  have hall : ∀ᶠ N : ℕ in atTop, ∀ i : Fin r,
      ∀ a ∈ spectrum ℝ (gueFamily r N x i),
        ∃ b ∈ spectrum ℝ (semicircularFamily r i), |a - b| ≤ (1 : ℝ) :=
    eventually_all.2 hN
  filter_upwards [hall, eventually_ge_atTop (1 : ℕ)] with N hNle hN1
  intro i
  haveI : Nonempty (Fin N) := ⟨⟨0, lt_of_lt_of_le Nat.zero_lt_one hN1⟩⟩
  refine norm_le_of_abs_spectrum_le (isSelfAdjoint_gueFamily x i) ?_
  intro a ha
  obtain ⟨b, hb, hab⟩ := hNle i a ha
  have hb2 : |b| ≤ 2 := by
    have hb' := spectrum.norm_le_norm_of_mem hb
    simpa [semicircularFamily, Real.norm_eq_abs] using hb'
  calc |a| = |b + (a - b)| := by rw [show b + (a - b) = a by ring]
    _ ≤ |b| + |a - b| := abs_add_le _ _
    _ ≤ 2 + 1 := add_le_add hb2 hab
    _ = 3 := by norm_num

/-- **The `hEdge` input of `FinalStatement.lean`**, conditional on scalar spectral
inclusion: eventually `tupleNorm (gueFamily r N x) ≤ 3 * r` almost surely. -/
theorem eventually_tupleNorm_gueFamily_le_of_scalarSpectralInclusion {r : ℕ}
    (h : ScalarSpectralInclusion r) :
    ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ᶠ N : ℕ in atTop,
      tupleNorm (gueFamily r N x) ≤ 3 * r := by
  filter_upwards [eventually_norm_gueFamily_le_three_of_scalarSpectralInclusion h]
    with x hx
  filter_upwards [hx] with N hN
  calc tupleNorm (gueFamily r N x) = ∑ i, ‖gueFamily r N x i‖ := rfl
    _ ≤ ∑ _i : Fin r, (3 : ℝ) := Finset.sum_le_sum fun i _ => hN i
    _ = 3 * r := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_comm]


/-! ## Spectrum perturbation and parameter lifting

The fixed-pencil hypothesis `SpectralInclusion` quantifies over **all real** pencil
parameters `z`.  The deterministic inputs are only available for rational `z` (and for
countable coefficient data), so we lift from a countable dense set to all of `ℝ` using
the Lipschitz/Hausdorff continuity of the spectrum in operator norm.

The exact continuity statement used is `exists_spectrum_close_of_norm_sub_le`: for
self-adjoint `a`, `b`, every real spectral value of `a` is within `‖a - b‖` of a real
spectral value of `b`. -/

section SpectrumPerturbation

variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]

/-- **Hausdorff--Lipschitz continuity of the real spectrum.**  For self-adjoint `a`, `b`
and `lam ∈ spectrum ℝ a`, there is `mu ∈ spectrum ℝ b` with `|lam - mu| ≤ ‖a - b‖`.

Consequently the real spectra of self-adjoint elements are `1`-Lipschitz in Hausdorff
distance with respect to the operator norm. -/
theorem exists_spectrum_close_of_norm_sub_le {a b : A} (ha : IsSelfAdjoint a)
    (hb : IsSelfAdjoint b) {lam : ℝ} (hlam : lam ∈ spectrum ℝ a) :
    ∃ mu ∈ spectrum ℝ b, |lam - mu| ≤ ‖a - b‖ := by
  classical
  by_contra hcon
  push Not at hcon
  -- choose the closest point of `spectrum ℝ b` to `lam`
  obtain ⟨mu0, hmu0, hmin0⟩ :=
    (ContinuousFunctionalCalculus.isCompact_spectrum b).exists_isMinOn
      (ContinuousFunctionalCalculus.spectrum_nonempty b hb)
      (by fun_prop : ContinuousOn (fun mu : ℝ => |lam - mu|) (spectrum ℝ b))
  set δ : ℝ := ‖a - b‖ with hδ
  set d : ℝ := |lam - mu0| with hd
  have hdgt : δ < d := hcon mu0 hmu0
  have hdpos : 0 < d := lt_of_le_of_lt (norm_nonneg _) hdgt
  -- the intermediate gap
  set δ' : ℝ := (d + δ) / 2 with hδ'
  have hδlt : δ < δ' := by simp [hδ']; linarith
  have hδ'lt : δ' < d := by simp [hδ']; linarith
  have hδ'pos : 0 < δ' := lt_of_le_of_lt (norm_nonneg _) hδlt
  -- `lam` is not in the real spectrum of `b`
  have hlam_not : lam ∉ spectrum ℝ b := by
    intro hmem
    have hlt := hcon lam hmem
    simp only [sub_self, abs_zero] at hlt
    linarith [norm_nonneg (a - b)]
  -- `u = lam - b` is a unit
  let u : A := ((lam : ℂ) • (1 : A)) - b
  have hsmul : ((lam : ℂ) • (1 : A)) = algebraMap ℝ A lam := by
    symm
    rw [IsScalarTower.algebraMap_apply ℝ ℂ A, Algebra.algebraMap_eq_smul_one]
    norm_num
  have hnotC : algebraMap ℝ ℂ lam ∉ spectrum ℂ b := by
    rwa [spectrum.algebraMap_mem_iff ℂ]
  have hu : IsUnit u := by
    have hnotC' : (lam : ℂ) ∉ spectrum ℂ b := hnotC
    have hu' : IsUnit (algebraMap ℂ A ((lam : ℂ)) - b) := by
      by_contra hnu
      exact hnotC' (by
        rw [spectrum, Set.mem_compl_iff, spectrum.mem_resolventSet_iff]
        exact hnu)
    rwa [show u = algebraMap ℂ A ((lam : ℂ)) - b by
      unfold u; rw [Algebra.algebraMap_eq_smul_one]]
  -- self-adjointness of `u`
  have hsa_smul : IsSelfAdjoint ((lam : ℂ) • (1 : A)) := by
    rw [hsmul]
    exact IsSelfAdjoint.algebraMap A (.all lam)
  have hu_sa : IsSelfAdjoint u := hsa_smul.sub hb
  -- the spectral gap of `u`
  have hgap : ∀ w ∈ spectrum ℂ u, δ' ≤ ‖w‖ := by
    intro w hw
    have hw' : w ∈ ({((lam : ℂ))} - spectrum ℂ b) := by
      have hthis := hw
      rw [show u = algebraMap ℂ A ((lam : ℂ)) - b by
        unfold u; rw [Algebra.algebraMap_eq_smul_one]] at hthis
      rwa [← spectrum.singleton_sub_eq (a := b) (r := (lam : ℂ))] at hthis
    obtain ⟨c1, hc1, c, hc, hwc⟩ := hw'
    have hc1eq : c1 = (lam : ℂ) := Set.mem_singleton_iff.mp hc1
    -- `c` is the image of a real spectral value
    have hc' : algebraMap ℝ ℂ (Complex.reCLM c) = c :=
      (show SpectrumRestricts b Complex.reCLM from hb.spectrumRestricts).rightInvOn hc
    have hcμ : Complex.reCLM c ∈ spectrum ℝ b :=
      (spectrum.algebraMap_mem_iff ℂ).mp (hc' ▸ hc)
    have hdmin : d ≤ |lam - Complex.reCLM c| := hmin0 hcμ
    have hnorm : ‖w‖ = |lam - Complex.reCLM c| := by
      calc ‖w‖ = ‖((lam : ℂ) - c)‖ := by rw [← hwc, hc1eq]
        _ = ‖(((lam - Complex.reCLM c : ℝ)) : ℂ)‖ := by
            congr 1
            rw [← hc']
            simp
        _ = |lam - Complex.reCLM c| := Complex.norm_real _
    rw [hnorm]
    exact le_of_lt (lt_of_lt_of_le hδ'lt hdmin)
  have hinv : ‖Ring.inverse u‖ ≤ δ'⁻¹ :=
    norm_ringInverse_le_of_spectrum_gap hu_sa hδ'pos hu hgap
  -- Neumann perturbation of `u` by `b - a`
  have hsmall : ‖Ring.inverse u * (b - a)‖ < 1 := by
    calc ‖Ring.inverse u * (b - a)‖ ≤ ‖Ring.inverse u‖ * ‖b - a‖ := norm_mul_le _ _
      _ ≤ δ'⁻¹ * δ := by
          apply mul_le_mul hinv (le_of_eq ?_) (norm_nonneg _) (by positivity)
          rw [hδ, norm_sub_rev]
      _ < 1 := by
          rw [← div_eq_inv_mul, div_lt_one hδ'pos]
          exact hδlt
  have hunit : IsUnit (u + (b - a)) :=
    isUnit_add_of_isUnit_of_norm_mul_lt_one hu hsmall
  have hsum : u + (b - a) = ((lam : ℂ) • (1 : A)) - a := by
    simp only [u]; abel
  exact (not_isUnit_of_mem_spectrum_real hlam) (hsum ▸ hunit)

end SpectrumPerturbation

/-! ### Lifting the pencil parameter from `ℚ` to `ℝ` -/

section ParameterLifting

variable {An : ℕ → Type*} [∀ n, CStarAlgebra (An n)] [∀ n, Nontrivial (An n)]
  [∀ n, PartialOrder (An n)] [∀ n, StarOrderedRing (An n)]
variable {Alim : Type*} [CStarAlgebra Alim] [Nontrivial Alim] [PartialOrder Alim]
  [StarOrderedRing Alim]

/-- **Parameter lifting.**  Suppose the approximating and limit pencils are `1`-Lipschitz
in the real parameter `z` and self-adjoint for every `z`.  If one-sided spectral inclusion
holds at every *rational* parameter, then it holds at every real parameter. -/
theorem spectral_inclusion_of_rational_parameter
    (vn : ∀ n, ℝ → An n) (vlim : ℝ → Alim)
    (hsa_n : ∀ n z, IsSelfAdjoint (vn n z))
    (hsa_lim : ∀ z, IsSelfAdjoint (vlim z))
    (hlip_n : ∀ n z z', ‖vn n z - vn n z'‖ ≤ |z - z'|)
    (hlip_lim : ∀ z z', ‖vlim z - vlim z'‖ ≤ |z - z'|)
    (hinc : ∀ zq : ℚ, ∀ ε > 0, ∀ᶠ n in atTop,
      ∀ a ∈ spectrum ℝ (vn n (zq : ℝ)),
        ∃ b ∈ spectrum ℝ (vlim (zq : ℝ)), |a - b| ≤ ε) :
    ∀ z : ℝ, ∀ ε > 0, ∀ᶠ n in atTop,
      ∀ a ∈ spectrum ℝ (vn n z),
        ∃ b ∈ spectrum ℝ (vlim z), |a - b| ≤ ε := by
  intro z ε hε
  -- a rational point within `ε / 4`
  obtain ⟨zq, hzq1, hzq2⟩ := exists_rat_btwn (show z < z + ε / 4 by linarith)
  have hclose : |z - (zq : ℝ)| < ε / 4 := by
    rw [abs_sub_comm, abs_of_pos (by linarith : (0 : ℝ) < (zq : ℝ) - z)]
    linarith
  have hquarter : (0 : ℝ) < ε / 4 := by positivity
  filter_upwards [hinc zq (ε / 4) hquarter] with n hn
  intro a ha
  -- move `a` to the rational parameter
  obtain ⟨a', ha', haa'⟩ :=
    exists_spectrum_close_of_norm_sub_le (hsa_n n z) (hsa_n n (zq : ℝ)) ha
  have haa'' : |a - a'| ≤ ε / 4 :=
    haa'.trans (hlip_n n z (zq : ℝ) |>.trans hclose.le)
  -- inclusion at the rational parameter
  obtain ⟨b', hb', ha'b'⟩ := hn a' ha'
  -- move `b'` back to the real parameter
  obtain ⟨b, hb, hb'b⟩ :=
    exists_spectrum_close_of_norm_sub_le (hsa_lim (zq : ℝ)) (hsa_lim z) hb'
  have hb'b' : |b' - b| ≤ ε / 4 := by
    refine hb'b.trans ?_
    calc ‖vlim ((zq : ℝ)) - vlim z‖ = ‖vlim z - vlim ((zq : ℝ))‖ := norm_sub_rev _ _
      _ ≤ |z - (zq : ℝ)| := hlip_lim z (zq : ℝ)
      _ ≤ ε / 4 := hclose.le
  refine ⟨b, hb, ?_⟩
  calc |a - b| ≤ |a - a'| + |a' - b'| + |b' - b| := by
        rw [show a - b = (a - a') + (a' - b') + (b' - b) by ring]
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ ε / 4 + ε / 4 + ε / 4 := by linarith
    _ ≤ ε := by linarith

end ParameterLifting

/-! ### Countable intersection over the data -/

/-- **Countable-intersection lifting** (`ae_all_iff`).  If for each element of a countable
index type the property holds almost surely eventually, then almost surely all properties
hold eventually simultaneously.

Applied with `ι = Σ d, RatPolyIdx r d` (countable: `d` and the Gaussian-rational
polynomials), this is the step that produces a single a.e. event over all coefficient
dimensions and all rational coefficient tuples. -/
theorem ae_all_forall_eventually
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {ι : Type*} [Countable ι] (p : ι → Ω → ℕ → Prop)
    (h : ∀ i, ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, p i ω n) :
    ∀ᵐ ω ∂μ, ∀ i, ∀ᶠ n in atTop, p i ω n :=
  ae_all_iff.2 h


section PencilParameterLifting

variable {B : Type*} [CStarAlgebra B] [Nontrivial B] [PartialOrder B] [StarOrderedRing B]
  {I κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **Rational-to-real lifting for the concrete linearization pencils.**  For the pencils
`penLCS` of `FromPencils.lean`, the two Lipschitz hypotheses of
`spectral_inclusion_of_rational_parameter` are discharged by `penLCS_sub_norm_le` and the
self-adjointness hypothesis by `penLCS_isSelfAdjoint`.  Hence one-sided spectral inclusion
at every rational parameter upgrades to `SpectralInclusion`. -/
theorem spectralInclusion_of_rational_parameter_penLCS
    (x : I → B) (X : ℕ → I → B) (wds : κ → List I) (coeff : κ → B) {C : B}
    (hC : IsSelfAdjoint C)
    (hinc : ∀ zq : ℚ, ∀ ε > 0, ∀ᶠ n in atTop,
      ∀ a ∈ spectrum ℝ (penLCS (X n) wds coeff C (zq : ℝ)),
        ∃ b ∈ spectrum ℝ (penLCS x wds coeff C (zq : ℝ)), |a - b| ≤ ε) :
    SpectralInclusion x X wds coeff C := by
  intro z ε hε
  exact spectral_inclusion_of_rational_parameter
    (fun n z => penLCS (X n) wds coeff C z) (fun z => penLCS x wds coeff C z)
    (fun n z => penLCS_isSelfAdjoint (X n) wds coeff hC z)
    (fun z => penLCS_isSelfAdjoint x wds coeff hC z)
    (fun n z z' => penLCS_sub_norm_le (X n) wds coeff C z z')
    (fun z z' => penLCS_sub_norm_le x wds coeff C z z')
    hinc z ε hε

end PencilParameterLifting


end

end GUEStrongConvergence
