/-
# Spectral exclusion for smooth cutoffs with growing matrix dimension

This file generalizes `GUEStrongConvergence.StrongConvergence.CutoffExclusion` from a fixed
matrix dimension `m` to a dimension sequence `m : ℕ → ℕ`.  It is the variant needed by the
GUE pencil, whose matrix dimension is `m N = Fintype.card d * N`.

## What changes and what does not

The deterministic positivity input and the variance/mean estimates do not change: a single
escaping eigenvalue still contributes `1 / m N` to the normalized trace
`τ_N(f(H_N)) = (m N)⁻¹ Re tr (f(H_N))`, and the analytic hypotheses `(M)`, `(V)`, `(W)`
keep the same uniform bounds `C / N²`, `C' / N²` (uniform in `N`, not in `m N`).

What changes is the Markov/Borel--Cantelli step.  For fixed `m` the existing proof uses the
stronger threshold `1 / (m * N)`; for growing `m` that threshold is not summable as soon as
`m N` grows like `N^2` (the bad-event bound is then `K * (m N)^2 / N^2`).  The spectral
argument only ever consumes the threshold `1 / m N`, and the squared mean bound
`E[Z_N ^ 2] = O(N⁻⁴)` gives

`P(Z_N ≥ 1/(m N)) ≤ K * (m N)^2 / N^4`,

which is summable under the growth condition `m N ≤ D * N`.  This condition is automatic
for the pencil (`D = card d`).  We therefore prove the core with threshold `1 / m N` and
carry the growth constant `D` explicitly.

Without *some* growth condition the statement is false: for `m N = N^2` one can take
`H_N` equal to `0` or to `diag(2, 0, …, 0)` with probability `1/2` each, which satisfies all
the mean/variance bounds but escapes with probability `1/2` infinitely often.

## Main results

* `ae_eventually_lt_inv_of_mean_variance_growing`: the probabilistic core with threshold
  `1 / m N`.
* `ae_eventually_spectrum_subset_growing`: Lemma S with growing dimension.
* `ae_eventually_spectrum_subset_growing_of_forall_pos`: the same with the hypothesis
  `∀ N, 0 < m N` (the form of the fixed-dimension statement).
* `ae_eventually_spectrum_subset_pencil`: specialization to `m N = card d * N`.
-/
import GUEStrongConvergence.StrongConvergence.CutoffExclusion

open Filter MeasureTheory ProbabilityTheory FreeProbability FreeProbability.Fock Matrix
open scoped BigOperators ComplexOrder ENNReal Pointwise Topology

namespace GUEStrongConvergence

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

/-! ## Probabilistic core with growing dimension -/

/-- **Spectral exclusion from mean and variance bounds, growing dimension.**

Let `Z_N` be real random variables and `W_N` nonnegative random variables with

* `(M)` `|E Z_N| ≤ C / N²` eventually,
* `(V)` `Var Z_N ≤ C / N² * E W_N` and `E W_N ≤ C' / N²`,
* the dimension sequence is eventually positive and eventually grows at most linearly,
  `m N ≤ D * N`.

Then `Z_N < 1 / m N` eventually almost surely.

Compared with `ae_eventually_lt_inv_mul_of_mean_variance`, the threshold is `1 / m N`
instead of `1 / (m N * N)`; this is the form consumed by the spectral argument, and the
form whose Markov bound is summable for growing dimensions. -/
theorem ae_eventually_lt_inv_of_mean_variance_growing
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : ℕ → ℕ} (hm : ∀ᶠ N in atTop, 0 < m N)
    {C C' D : ℝ} (hC : 0 ≤ C) (_hC' : 0 ≤ C') (hD : 0 ≤ D)
    (hmD : ∀ᶠ N in atTop, (m N : ℝ) ≤ D * (N : ℝ))
    (Z W : ℕ → Ω → ℝ)
    (hZ : ∀ N, MemLp (Z N) 2 μ)
    (_hWint : ∀ N, Integrable (W N) μ)
    (_hW0 : ∀ N, 0 ≤ ∫ ω, W N ω ∂μ)
    (hM : ∀ᶠ N in atTop, |∫ ω, Z N ω ∂μ| ≤ C / (N : ℝ) ^ 2)
    (hV : ∀ᶠ N in atTop, variance (Z N) μ
      ≤ C / (N : ℝ) ^ 2 * ∫ ω, W N ω ∂μ)
    (hWb : ∀ᶠ N in atTop, ∫ ω, W N ω ∂μ ≤ C' / (N : ℝ) ^ 2) :
    ∀ᵐ ω ∂μ, ∀ᶠ N : ℕ in atTop, Z N ω < ((m N : ℝ))⁻¹ := by
  classical
  -- the constant in the `E Z_N ^ 2` bound
  set K : ℝ := C * C' + C ^ 2 with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  -- `E Z_N ^ 2 = O(N⁻⁴)` (unchanged from the fixed-dimension proof)
  have hEZsq : ∀ᶠ N : ℕ in atTop, ∫ ω, Z N ω ^ 2 ∂μ ≤ K / (N : ℝ) ^ 4 := by
    filter_upwards [hM, hV, hWb, eventually_ge_atTop (1 : ℕ)] with N hMN hVN hWbN hN1
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    have hN4pos : (0 : ℝ) < (N : ℝ) ^ 4 := by positivity
    have hvar : variance (Z N) μ ≤ C * C' / (N : ℝ) ^ 4 := by
      calc variance (Z N) μ
          ≤ C / (N : ℝ) ^ 2 * ∫ ω, W N ω ∂μ := hVN
        _ ≤ C / (N : ℝ) ^ 2 * (C' / (N : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hWbN (by positivity)
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
  -- Markov: the bad event has probability `O((m N)² / N⁴)`, hence `O(N⁻²)` by growth
  have hprob : ∀ᶠ N : ℕ in atTop,
      μ.real {ω | ((m N : ℝ))⁻¹ ≤ Z N ω} ≤ K * D ^ 2 / (N : ℝ) ^ 2 := by
    filter_upwards [hEZsq, hm, hmD, eventually_ge_atTop (1 : ℕ)] with N hEZ hmN hmDN hN1
    have hmR : (0 : ℝ) < (m N : ℝ) := by exact_mod_cast hmN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    have hapos : (0 : ℝ) < ((m N : ℝ))⁻¹ := by positivity
    have hmarkov := meas_real_ge_le_integral_sq_div hapos (hZ N).aemeasurable
      (hZ N).integrable_sq
    have hN4pos : (0 : ℝ) < (N : ℝ) ^ 4 := by positivity
    have hcoef : (K / (N : ℝ) ^ 4) / (((m N : ℝ))⁻¹) ^ 2
        = K * (m N : ℝ) ^ 2 / (N : ℝ) ^ 4 := by
      field_simp
    -- `(m N)² ≤ (D * N)²`
    have hgrowthN : (m N : ℝ) ^ 2 ≤ D ^ 2 * (N : ℝ) ^ 2 := by
      have hDN : (0 : ℝ) ≤ D * (N : ℝ) := mul_nonneg hD hNpos.le
      have hle := hmDN
      nlinarith [hmR.le, hDN, hle, sq_nonneg ((m N : ℝ) - D * (N : ℝ))]
    have hbound : K * (m N : ℝ) ^ 2 / (N : ℝ) ^ 4 ≤ K * D ^ 2 / (N : ℝ) ^ 2 := by
      have hN2pos : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
      have h1 : K * (m N : ℝ) ^ 2 ≤ K * (D ^ 2 * (N : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hgrowthN hK0
      have h2 : K * (m N : ℝ) ^ 2 * (N : ℝ) ^ 2
          ≤ K * (D ^ 2 * (N : ℝ) ^ 2) * (N : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right h1 hN2pos.le
      rw [div_le_div_iff₀ hN4pos hN2pos]
      nlinarith [h2]
    calc μ.real {ω | ((m N : ℝ))⁻¹ ≤ Z N ω}
        ≤ (∫ ω, Z N ω ^ 2 ∂μ) / (((m N : ℝ))⁻¹) ^ 2 := hmarkov
      _ ≤ (K / (N : ℝ) ^ 4) / (((m N : ℝ))⁻¹) ^ 2 := by
          gcongr
      _ = K * (m N : ℝ) ^ 2 / (N : ℝ) ^ 4 := hcoef
      _ ≤ K * D ^ 2 / (N : ℝ) ^ 2 := hbound
  -- summability of the bad probabilities
  have hKsum : Summable (fun N : ℕ => K * D ^ 2 / (N : ℝ) ^ 2) := by
    have hbase : Summable (fun N : ℕ => 1 / (N : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have hmul : Summable (fun N : ℕ => K * D ^ 2 * (1 / (N : ℝ) ^ 2)) :=
      hbase.mul_left _
    refine hmul.congr fun N => ?_
    ring
  have hprob' : ∀ᶠ N : ℕ in atTop,
      ‖μ.real {ω | ((m N : ℝ))⁻¹ ≤ Z N ω}‖ ≤ K * D ^ 2 / (N : ℝ) ^ 2 :=
    hprob.mono fun N hN => by
      have hnonneg : 0 ≤ μ.real {ω | ((m N : ℝ))⁻¹ ≤ Z N ω} := ENNReal.toReal_nonneg
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      exact hN
  have hprob'' : ∀ᶠ N : ℕ in cofinite,
      ‖μ.real {ω | ((m N : ℝ))⁻¹ ≤ Z N ω}‖ ≤ K * D ^ 2 / (N : ℝ) ^ 2 := by
    simpa [Nat.cofinite_eq_atTop] using hprob'
  have hsumBad : Summable (fun N : ℕ => μ.real {ω | ((m N : ℝ))⁻¹ ≤ Z N ω}) :=
    Summable.of_norm_bounded_eventually hKsum hprob''
  -- convert summability of real probabilities into summability of the `ℝ≥0∞` measures
  have hENN : (∑' N : ℕ, μ {ω | ((m N : ℝ))⁻¹ ≤ Z N ω}) ≠ ∞ := by
    have hnonneg : ∀ N : ℕ, 0 ≤ μ.real {ω | ((m N : ℝ))⁻¹ ≤ Z N ω} := fun N =>
      ENNReal.toReal_nonneg
    have hconv : (∑' N : ℕ, μ {ω | ((m N : ℝ))⁻¹ ≤ Z N ω})
        = ∑' N : ℕ, ENNReal.ofReal (μ.real {ω | ((m N : ℝ))⁻¹ ≤ Z N ω}) := by
      apply tsum_congr
      intro N
      exact (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
    rw [hconv, ← ENNReal.ofReal_tsum_of_nonneg hnonneg hsumBad]
    exact ENNReal.ofReal_ne_top
  -- Borel--Cantelli
  filter_upwards [MeasureTheory.ae_eventually_notMem (μ := μ) (s := fun (N : ℕ) =>
    {ω | ((m N : ℝ))⁻¹ ≤ Z N ω}) hENN] with ω hω
  filter_upwards [hω] with N hN
  exact not_le.mp hN

/-! ## Lemma S with growing dimension -/

/-- **Lemma S (spectral exclusion) for Hermitian matrices of growing dimension.**

Let `H_N` be random Hermitian `m N × m N` matrices, `S ⊆ ℝ`, `ε > 0`, and `f : ℝ → ℝ` a
nonnegative cutoff which equals `1` outside `S + (-ε, ε)`.  Assume the two analytic
inputs

* `(M)` the mean of `Z_N = τ_N(f(H_N))` is `O(N⁻²)`,
* `(V)` `Var Z_N ≤ C N⁻² E W_N` with `W_N = τ_N((f')²(H_N))` and `E W_N ≤ C' N⁻²`,

the `L²`/integrability side conditions, and that the dimension eventually grows at most
linearly, `m N ≤ D * N`.  Then almost surely, eventually no real spectral value of `H_N` lies
outside `S + (-ε, ε)`.

The normalization is the growing dimension: `τ_N(a) = (m N)⁻¹ Re tr(a)`, and a single
escaping eigenvalue contributes at least `1 / m N` to `τ_N(f(H_N))`. -/
theorem ae_eventually_spectrum_subset_growing
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : ℕ → ℕ} (hm : ∀ᶠ N in atTop, 0 < m N)
    {S : Set ℝ} {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, x ∉ S + Set.Ioo (-ε) ε → f x = 1)
    (H : (N : ℕ) → Ω → Matrix (Fin (m N)) (Fin (m N)) ℂ)
    (hH : ∀ N ω, (H N ω).IsHermitian)
    {C C' D : ℝ} (hC : 0 ≤ C) (hC' : 0 ≤ C') (hD : 0 ≤ D)
    (hmD : ∀ᶠ N in atTop, (m N : ℝ) ≤ D * (N : ℝ))
    (hZ : ∀ N, MemLp (fun ω => normTrace (hermCfc (H N ω) f (hH N ω))) 2 μ)
    (hWint : ∀ N, Integrable
      (fun ω => normTrace (hermCfc (H N ω) (fun x => (deriv f x) ^ 2) (hH N ω))) μ)
    (hW0 : ∀ N, 0 ≤ ∫ ω,
      normTrace (hermCfc (H N ω) (fun x => (deriv f x) ^ 2) (hH N ω)) ∂μ)
    (hM : ∀ᶠ N : ℕ in atTop,
      |∫ ω, normTrace (hermCfc (H N ω) f (hH N ω)) ∂μ| ≤ C / (N : ℝ) ^ 2)
    (hV : ∀ᶠ N in atTop, variance (fun ω => normTrace (hermCfc (H N ω) f (hH N ω))) μ
      ≤ C / (N : ℝ) ^ 2 * ∫ ω,
          normTrace (hermCfc (H N ω) (fun x => (deriv f x) ^ 2) (hH N ω)) ∂μ)
    (hWb : ∀ᶠ N in atTop, ∫ ω,
        normTrace (hermCfc (H N ω) (fun x => (deriv f x) ^ 2) (hH N ω)) ∂μ
      ≤ C' / (N : ℝ) ^ 2) :
    ∀ᵐ ω ∂μ, ∀ᶠ N : ℕ in atTop,
      spectrum ℝ (H N ω) ⊆ S + Set.Ioo (-ε) ε := by
  have hsmall := ae_eventually_lt_inv_of_mean_variance_growing hm hC hC' hD hmD
    (fun N ω => normTrace (hermCfc (H N ω) f (hH N ω)))
    (fun N ω => normTrace (hermCfc (H N ω) (fun x => (deriv f x) ^ 2) (hH N ω)))
    hZ hWint hW0 hM hV hWb
  filter_upwards [hsmall] with ω hω
  filter_upwards [hω, hm] with N hNsmall hNpos
  intro lam hlam
  by_contra hesc
  have hle : ((m N : ℝ))⁻¹ ≤ normTrace (hermCfc (H N ω) f (hH N ω)) :=
    inv_card_le_normTrace_cfc_of_spectrum_escape hNpos (hH N ω) hε hf0 hf1 hlam hesc
  linarith

/-- **Lemma S with the fixed-dimension shape `∀ N, 0 < m N`.**

This is `ae_eventually_spectrum_subset_growing` with eventual positivity upgraded to
positivity for every `N`, matching the hypothesis list of
`ae_eventually_spectrum_subset`.  The growth condition `m N ≤ D * N` is still needed
(without it the statement is false, as explained in the module docstring). -/
theorem ae_eventually_spectrum_subset_growing_of_forall_pos
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : ℕ → ℕ} (hm : ∀ N, 0 < m N)
    {S : Set ℝ} {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, x ∉ S + Set.Ioo (-ε) ε → f x = 1)
    (H : (N : ℕ) → Ω → Matrix (Fin (m N)) (Fin (m N)) ℂ)
    (hH : ∀ N ω, (H N ω).IsHermitian)
    {C C' D : ℝ} (hC : 0 ≤ C) (hC' : 0 ≤ C') (hD : 0 ≤ D)
    (hmD : ∀ᶠ N in atTop, (m N : ℝ) ≤ D * (N : ℝ))
    (hZ : ∀ N, MemLp (fun ω => normTrace (hermCfc (H N ω) f (hH N ω))) 2 μ)
    (hWint : ∀ N, Integrable
      (fun ω => normTrace (hermCfc (H N ω) (fun x => (deriv f x) ^ 2) (hH N ω))) μ)
    (hW0 : ∀ N, 0 ≤ ∫ ω,
      normTrace (hermCfc (H N ω) (fun x => (deriv f x) ^ 2) (hH N ω)) ∂μ)
    (hM : ∀ᶠ N : ℕ in atTop,
      |∫ ω, normTrace (hermCfc (H N ω) f (hH N ω)) ∂μ| ≤ C / (N : ℝ) ^ 2)
    (hV : ∀ᶠ N in atTop, variance (fun ω => normTrace (hermCfc (H N ω) f (hH N ω))) μ
      ≤ C / (N : ℝ) ^ 2 * ∫ ω,
          normTrace (hermCfc (H N ω) (fun x => (deriv f x) ^ 2) (hH N ω)) ∂μ)
    (hWb : ∀ᶠ N in atTop, ∫ ω,
        normTrace (hermCfc (H N ω) (fun x => (deriv f x) ^ 2) (hH N ω)) ∂μ
      ≤ C' / (N : ℝ) ^ 2) :
    ∀ᵐ ω ∂μ, ∀ᶠ N : ℕ in atTop,
      spectrum ℝ (H N ω) ⊆ S + Set.Ioo (-ε) ε :=
  ae_eventually_spectrum_subset_growing (Eventually.of_forall hm) hε hf0 hf1 H hH
    hC hC' hD hmD hZ hWint hW0 hM hV hWb

/-- **The fixed-dimension `ae_eventually_spectrum_subset` as a corollary.**

The original fixed-`m` theorem is the specialization `m N := m`, `D := m` of the
growing-dimension lemma: `m ≤ m * N` eventually, so the growth hypothesis holds with
constant `m`.  This shows that the generalization is faithful (no hypothesis beyond the
necessary growth condition is added). -/
theorem ae_eventually_spectrum_subset_fixed_dim
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : ℕ} (hm : 0 < m) {S : Set ℝ} {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, x ∉ S + Set.Ioo (-ε) ε → f x = 1)
    (H : ℕ → Ω → Matrix (Fin m) (Fin m) ℂ) (hH : ∀ N ω, (H N ω).IsHermitian)
    {C C' : ℝ} (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (hZ : ∀ N, MemLp (fun ω => normTrace (hermCfc (H N ω) f (hH N ω))) 2 μ)
    (hWint : ∀ N, Integrable
      (fun ω => normTrace (hermCfc (H N ω) (fun x => (deriv f x) ^ 2) (hH N ω))) μ)
    (hW0 : ∀ N, 0 ≤ ∫ ω,
      normTrace (hermCfc (H N ω) (fun x => (deriv f x) ^ 2) (hH N ω)) ∂μ)
    (hM : ∀ᶠ N : ℕ in atTop,
      |∫ ω, normTrace (hermCfc (H N ω) f (hH N ω)) ∂μ| ≤ C / (N : ℝ) ^ 2)
    (hV : ∀ᶠ N in atTop, variance (fun ω => normTrace (hermCfc (H N ω) f (hH N ω))) μ
      ≤ C / (N : ℝ) ^ 2 * ∫ ω,
          normTrace (hermCfc (H N ω) (fun x => (deriv f x) ^ 2) (hH N ω)) ∂μ)
    (hWb : ∀ᶠ N in atTop, ∫ ω,
        normTrace (hermCfc (H N ω) (fun x => (deriv f x) ^ 2) (hH N ω)) ∂μ
      ≤ C' / (N : ℝ) ^ 2) :
    ∀ᵐ ω ∂μ, ∀ᶠ N : ℕ in atTop,
      spectrum ℝ (H N ω) ⊆ S + Set.Ioo (-ε) ε := by
  have hmR : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hmD : ∀ᶠ N : ℕ in atTop, ((fun _ : ℕ => m) N : ℝ) ≤ (m : ℝ) * (N : ℝ) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith
  exact ae_eventually_spectrum_subset_growing_of_forall_pos (m := fun _ : ℕ => m)
    (fun _ => hm) hε hf0 hf1 H hH hC hC' hmR hmD hZ hWint hW0 hM hV hWb

/-! ## Specialization to the GUE pencil dimension `card d * N` -/

/-- **Lemma S for the GUE pencil.**  The matrix dimension is `m N = card d * N`, the
normalization used by `tau_N` in the pencil analysis.  The growth constant is
`D = card d`, and eventual positivity follows from `[Nonempty d]` and `N ≥ 1` (at `N = 0`
the dimension is `0`, but the conclusion is only eventual in `N`).

All analytic inputs keep their uniform `C / N²`, `C' / N²` bounds. -/
theorem ae_eventually_spectrum_subset_pencil
    {d : Type*} [Fintype d] [Nonempty d]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {S : Set ℝ} {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, x ∉ S + Set.Ioo (-ε) ε → f x = 1)
    (H : (N : ℕ) → Ω →
      Matrix (Fin (Fintype.card d * N)) (Fin (Fintype.card d * N)) ℂ)
    (hH : ∀ N ω, (H N ω).IsHermitian)
    {C C' : ℝ} (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (hZ : ∀ N, MemLp (fun ω => normTrace (hermCfc (H N ω) f (hH N ω))) 2 μ)
    (hWint : ∀ N, Integrable
      (fun ω => normTrace (hermCfc (H N ω) (fun x => (deriv f x) ^ 2) (hH N ω))) μ)
    (hW0 : ∀ N, 0 ≤ ∫ ω,
      normTrace (hermCfc (H N ω) (fun x => (deriv f x) ^ 2) (hH N ω)) ∂μ)
    (hM : ∀ᶠ N : ℕ in atTop,
      |∫ ω, normTrace (hermCfc (H N ω) f (hH N ω)) ∂μ| ≤ C / (N : ℝ) ^ 2)
    (hV : ∀ᶠ N in atTop, variance (fun ω => normTrace (hermCfc (H N ω) f (hH N ω))) μ
      ≤ C / (N : ℝ) ^ 2 * ∫ ω,
          normTrace (hermCfc (H N ω) (fun x => (deriv f x) ^ 2) (hH N ω)) ∂μ)
    (hWb : ∀ᶠ N in atTop, ∫ ω,
        normTrace (hermCfc (H N ω) (fun x => (deriv f x) ^ 2) (hH N ω)) ∂μ
      ≤ C' / (N : ℝ) ^ 2) :
    ∀ᵐ ω ∂μ, ∀ᶠ N : ℕ in atTop,
      spectrum ℝ (H N ω) ⊆ S + Set.Ioo (-ε) ε := by
  have hcard : 0 < Fintype.card d := Fintype.card_pos_iff.mpr inferInstance
  have hm : ∀ᶠ N : ℕ in atTop, 0 < Fintype.card d * N := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    exact Nat.mul_pos hcard hN
  have hmD : ∀ᶠ N : ℕ in atTop,
      ((Fintype.card d * N : ℕ) : ℝ) ≤ (Fintype.card d : ℝ) * (N : ℝ) := by
    filter_upwards with N
    push_cast
    rfl
  exact ae_eventually_spectrum_subset_growing hm hε hf0 hf1 H hH
    hC hC' (Nat.cast_nonneg _) hmD hZ hWint hW0 hM hV hWb

end

end GUEStrongConvergence
