/-
# Scalar spectral inclusion with the smooth cutoff

`StrongConvergence/ScalarInclusion.lean` proves `scalarSpectralInclusion_of_inputs` for the
*indicator* cutoff `0` inside `S + (-ε, ε)` and `1` outside.  That cutoff is not differentiable,
so the variance input `(V)` (`hV`) as well as the `L²`/integrability side conditions
`hZ`, `hWint`, `hW0` had to be assumed.  Now that the smooth cutoff `exists_contDiff_cutoff`
(`Probability/CutoffConstruction.lean`) and the **unconditional** smooth Lemma V
(`lemmaS_V_input_unconditional`, `Probability/CfcTraceDerivative.lean`) exist, all four can be
*proved*; only the two genuinely analytic estimates remain explicit:

* `hM` — the mean comparison (Lemma M), `|E τ_N(f(H_N))| = O(N⁻²)`;
* `hWb` — the `(W)` bound (Lemma W), `E τ_N((f')²(H_N)) = O(N⁻²)`.

## Structure

1. **The scalar matrix as a `Unit`-pencil.**  `guePencilMatrix_scalarCoeff` shows that
   `gueMatrix y i` is the pencil `A₀ = 0`, `A_i = 1`, `A_j = 0` (`j ≠ i`) up to the reindexing
   `Unit × Fin N ≃ Fin N`; `gueStatisticCfc_scalarCoeff_eq(_commonSpace)` then identifies the
   pencil statistic `gueStatisticCfc f 0 (scalarCoeff i)` with the scalar normalized trace
   `normTrace (hermCfc (gueMatrixOn x N i) f _)`.  This is the bridge that makes the
   unconditional Lemma V applicable to the scalar statistic.

2. **Measurability of the cfc.**  `measurable_cfc_of_hermitian`: for a matrix family with
   measurable entries and Hermitian values, `x ↦ cfc f (H x)` is measurable for every
   *continuous* `f`.  Mathlib has no continuity of the cfc in the matrix variable; we use
   Weierstrass approximation on the exhausting compact spectral sets `{hsNorm (H x) ≤ j}`
   (`norm_entry_polyMatrix_sub_cfc_le`) and a pointwise limit.

3. **Bounds and the `L²`/side conditions.**  `abs_normTrace_cfc_le` (`|τ(g(M))| ≤ sup |g|`),
   `normTrace_cfc_nonneg`, and `memLp_normTrace_cfc` / `integrable_normTrace_cfc` /
   `integral_normTrace_cfc_nonneg`.

4. **The smooth cutoff package.**  `IsSmoothCutoff` (`C¹`, `0 ≤ f ≤ 1`, `f = 1` outside
   `S + (-ε, ε)`, `(f')²` compactly supported), `exists_isSmoothCutoff` from
   `exists_contDiff_cutoff`, the global derivative bound `IsSmoothCutoff.exists_deriv_bound`, and
   the chosen cutoff `smoothCutoff i ε hε`.

5. **Assembly.**  `ae_eventually_spectrum_subset_scalar_smooth_of_hV` (with `hZ`, `hWint`, `hW0`
   discharged), the block-level and common-space variance bounds
   `variance_gueStatisticCfc_scalar_block` / `variance_scalarStatistic_le_two` (constant `2`),
   and the final results below.

## Main results

* `ae_eventually_spectrum_subset_scalar_smooth` — fixed `i`, `ε`: only `hM` and `hWb` explicit.
* `scalarSpectralInclusion_of_smoothCutoff` — the strengthened `ScalarSpectralInclusion r`,
  with only `hM` and `hWb` explicit.
-/
import GUEStrongConvergence.Probability.CutoffConstruction
import GUEStrongConvergence.Probability.CfcTraceDerivative
import GUEStrongConvergence.StrongConvergence.PencilSpectralInclusion
import GUEStrongConvergence.StrongConvergence.ScalarInclusion

open Filter MeasureTheory ProbabilityTheory FreeProbability FreeProbability.Fock Matrix
open scoped BigOperators ComplexOrder ENNReal Pointwise Topology Polynomial

namespace GUEStrongConvergence

noncomputable section

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## 1. The individual GUE matrix as a `Unit`-pencil -/

/-- The index identification `Unit × Fin N ≃ Fin N`. -/
def unitProdFinEquiv (N : ℕ) : Unit × Fin N ≃ Fin N where
  toFun p := p.2
  invFun a := ((), a)
  left_inv p := by obtain ⟨u, a⟩ := p; cases u; rfl
  right_inv _ := rfl

/-- The coefficient matrices of a scalar pencil: `A i = 1` and `A j = 0` for `j ≠ i`. -/
def scalarCoeff {r : ℕ} (i : Fin r) : Fin r → Matrix Unit Unit ℂ :=
  fun j => if j = i then 1 else 0

lemma scalarCoeff_isHermitian {r : ℕ} (i : Fin r) :
    ∀ j, (scalarCoeff i j).IsHermitian := by
  intro j
  by_cases h : j = i
  · rw [scalarCoeff, ite_eq_left h]; exact isHermitian_one
  · rw [scalarCoeff, ite_eq_right h]; exact isHermitian_zero

/-- The `Unit`-pencil with coefficients `A_i = 1`, `A_j = 0` is the individual GUE matrix
`gueMatrix y i`, up to the index identification `Unit × Fin N ≃ Fin N`. -/
lemma guePencilMatrix_scalarCoeff {r N : ℕ} (i : Fin r) (y : GUECoord (Fin r) N → ℝ) :
    guePencilMatrix (0 : Matrix Unit Unit ℂ) (scalarCoeff i) y =
      Matrix.reindex (unitProdFinEquiv N).symm (unitProdFinEquiv N).symm (gueMatrix y i) := by
  ext ⟨u, a⟩ ⟨v, b⟩
  cases u; cases v
  rw [guePencilMatrix_apply, Matrix.reindex_apply]
  simp only [Matrix.zero_apply, zero_mul, zero_add, Equiv.symm_symm, unitProdFinEquiv,
    Equiv.coe_fn_mk]
  rw [Finset.sum_eq_single i]
  · simp [scalarCoeff]
  · intro j _ hji
    simp [scalarCoeff, hji]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- **The pencil statistic of the scalar pencil is the scalar normalized trace.**  For the
`Unit`-pencil `A₀ = 0`, `A_i = 1`, `A_j = 0` (`j ≠ i`), the pencil statistic `gueStatisticCfc`
is literally the normalized trace `normTrace (hermCfc (gueMatrix y i) f ·)` of the individual
GUE matrix. -/
lemma gueStatisticCfc_scalarCoeff_eq {r N : ℕ} (f : ℝ → ℝ) (i : Fin r)
    (x : EuclideanSpace ℝ (GUECoord (Fin r) N))
    (hA₀ : (0 : Matrix Unit Unit ℂ).IsHermitian)
    (hA : ∀ j, (scalarCoeff i j).IsHermitian) :
    gueStatisticCfc (N := N) (ι := Fin r) (d := Unit) f
        (0 : Matrix Unit Unit ℂ) (scalarCoeff i) hA₀ hA x =
      normTrace (hermCfc (gueMatrix (WithLp.ofLp x) i) f
        (gueMatrix_isHermitian (WithLp.ofLp x) i)) := by
  simp only [gueStatisticCfc, guePencilCfc_eq_cfc, guePencilMatrix_scalarCoeff, cfc_reindex,
    guePencilNormTrace, gueNormConst, normTrace, hermCfc, trace_reindex, Fintype.card_unit,
    one_mul]

/-- The same identification on the common space. -/
lemma gueStatisticCfc_scalarCoeff_eq_commonSpace {r N : ℕ} (f : ℝ → ℝ) (i : Fin r)
    (x : CommonSpace (Fin r)) (hA₀ : (0 : Matrix Unit Unit ℂ).IsHermitian)
    (hA : ∀ j, (scalarCoeff i j).IsHermitian) :
    gueStatisticCfc (N := N) (ι := Fin r) (d := Unit) f
        (0 : Matrix Unit Unit ℂ) (scalarCoeff i) hA₀ hA (x N) =
      normTrace (hermCfc (gueMatrixOn x N i) f (gueMatrixOn_isHermitian x N i)) := by
  simpa [gueMatrixOn] using
    gueStatisticCfc_scalarCoeff_eq (f := f) (i := i) (x := x N) hA₀ hA

/-! ## 2. Measurability and bounds for the cfc statistic

The Lemma-S side conditions `hZ`, `hWint` (`MemLp`/`Integrable` of the statistics) need
measurability of `x ↦ cfc f (H(x))`.  Mathlib has no continuity of the cfc in the matrix
variable, so we obtain *measurability* by a polynomial approximation: on the closed set
`{x | hsNorm (H x) ≤ j}` the spectrum is contained in `[-(j+1), j+1]`, where a fixed polynomial
`q j` approximates `f` to accuracy `1/(j+1)`; the resulting sequence of *measurable* functions
converges pointwise (indeed entrywise) to `cfc f (H ·)`. -/

section Measurability

variable {Ω : Type*} [MeasurableSpace Ω]
variable {m : Type*} [Fintype m] [DecidableEq m]

/-- A matrix-valued function is measurable as soon as all of its entries are. -/
lemma measurable_matrix_of_entries {M : Ω → Matrix m m ℂ}
    (hM : ∀ a b, Measurable fun x => M x a b) : Measurable M :=
  measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun b => hM a b

/-- The polynomial functional calculus is continuous in the matrix variable. -/
lemma continuous_polyMatrix (q : ℝ[X]) :
    Continuous fun M : Matrix m m ℂ => polyMatrix q M := by
  have hfun : (fun M : Matrix m m ℂ => polyMatrix q M) =
      fun M => ∑ k ∈ q.support, q.coeff k • M ^ k := by
    funext M
    exact polyMatrix_eq_sum q M
  rw [hfun]
  fun_prop

/-- The Hilbert–Schmidt norm squared is measurable in the entries. -/
lemma measurable_hsNorm {M : Ω → Matrix m m ℂ}
    (hM : ∀ a b, Measurable fun x => M x a b) :
    Measurable fun x => hsNorm (M x) := by
  have hfun : (fun x => hsNorm (M x)) = fun x => ∑ a, ∑ b, ‖M x a b‖ ^ 2 := by
    funext x
    show hsNorm (M x) = ∑ a, ∑ b, ‖M x a b‖ ^ 2
    rw [hsNorm]
  rw [hfun]
  refine Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => ?_
  exact ((hM a b).norm).pow_const 2

/-- Every entry of a matrix is bounded by the square root of its Hilbert–Schmidt norm. -/
lemma norm_entry_le_sqrt_hsNorm (X : Matrix m m ℂ) (a b : m) :
    ‖X a b‖ ≤ Real.sqrt (hsNorm X) := by
  have hrow : ‖X a b‖ ^ 2 ≤ ∑ b', ‖X a b'‖ ^ 2 :=
    Finset.single_le_sum (f := fun b' => ‖X a b'‖ ^ 2) (fun j _ => by positivity)
      (Finset.mem_univ b)
  have htot : (∑ b', ‖X a b'‖ ^ 2) ≤ hsNorm X := by
    show (∑ b', ‖X a b'‖ ^ 2) ≤ ∑ a', ∑ b', ‖X a' b'‖ ^ 2
    exact Finset.single_le_sum (f := fun a' => ∑ b', ‖X a' b'‖ ^ 2)
      (fun i _ => Finset.sum_nonneg fun j _ => by positivity) (Finset.mem_univ a)
  calc ‖X a b‖ = Real.sqrt (‖X a b‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (hsNorm X) := Real.sqrt_le_sqrt (hrow.trans htot)

/-- **Entrywise bound for the polynomial approximation.**  If `q` approximates `f` to accuracy
`δ` on `[-(j+1), j+1]` and `hsNorm X ≤ j`, then every entry of `cfc f X - q(X)` is at most
`√n · δ`. -/
lemma norm_entry_polyMatrix_sub_cfc_le {X : Matrix m m ℂ} (hX : X.IsHermitian)
    {q : ℝ[X]} {f : ℝ → ℝ} (hf : Continuous f) {j : ℕ} (hj : hsNorm X ≤ (j : ℝ))
    {δ : ℝ} (hq : ∀ y ∈ Set.Icc (-(j : ℝ) - 1) ((j : ℝ) + 1), |q.eval y - f y| ≤ δ)
    (hδ0 : 0 ≤ δ) (a b : m) :
    ‖(polyMatrix q X - cfc f X) a b‖ ≤ Real.sqrt (Fintype.card m : ℝ) * δ := by
  -- the difference is the cfc of `q - f`
  let g : ℝ → ℝ := fun y => q.eval y - f y
  have hgcont : Continuous g := (Polynomial.continuous q).sub hf
  have hdiff : polyMatrix q X - cfc f X = cfc g X := by
    rw [← cfc_polyMatrix_eq q X hX,
      ← cfc_sub_of_hermitian (fun y : ℝ => q.eval y) f (Polynomial.continuous q) hf X hX]
  have hspec : ∀ i, |hX.eigenvalues i| ≤ (j : ℝ) + 1 := by
    intro i
    have h1 : |hX.eigenvalues i| ≤ Real.sqrt (hsNorm X) := eigenvalues_abs_le_sqrt_hsNorm X hX i
    have h2 : Real.sqrt (hsNorm X) ≤ (j : ℝ) + 1 := by
      have h3 : Real.sqrt (hsNorm X) ≤ Real.sqrt ((j : ℝ) + 1) :=
        Real.sqrt_le_sqrt (hj.trans (by linarith))
      have h4 : Real.sqrt ((j : ℝ) + 1) ≤ (j : ℝ) + 1 := by
        have h5 : (j : ℝ) + 1 ≤ ((j : ℝ) + 1) ^ 2 := by
          have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
          nlinarith
        calc Real.sqrt ((j : ℝ) + 1) ≤ Real.sqrt (((j : ℝ) + 1) ^ 2) := Real.sqrt_le_sqrt h5
          _ = (j : ℝ) + 1 := Real.sqrt_sq (by linarith)
      linarith
    exact h1.trans h2
  have hsnorm : hsNorm (cfc g X) ≤ (Fintype.card m : ℝ) * δ ^ 2 := by
    rw [hsNorm_cfc_eq_sum_eigenvalues X hX g hgcont]
    calc ∑ i, (g (hX.eigenvalues i)) ^ 2 ≤ ∑ _i : m, δ ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have habs : |g (hX.eigenvalues i)| ≤ δ :=
            hq _ (Set.mem_Icc.mpr (by
              have hsp := hspec i
              rw [abs_le] at hsp
              constructor <;> linarith [hsp.1, hsp.2]))
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) habs 2
      _ = (Fintype.card m : ℝ) * δ ^ 2 := by
          simp [Finset.sum_const, nsmul_eq_mul]
  have hle := norm_entry_le_sqrt_hsNorm (cfc g X) a b
  have h2 : Real.sqrt (hsNorm (cfc g X)) ≤ Real.sqrt ((Fintype.card m : ℝ) * δ ^ 2) :=
    Real.sqrt_le_sqrt hsnorm
  have h3 : Real.sqrt ((Fintype.card m : ℝ) * δ ^ 2) = Real.sqrt (Fintype.card m : ℝ) * δ := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hδ0]
  rw [hdiff]
  calc ‖(cfc g X) a b‖ ≤ Real.sqrt (hsNorm (cfc g X)) := hle
    _ ≤ Real.sqrt ((Fintype.card m : ℝ) * δ ^ 2) := h2
    _ = Real.sqrt (Fintype.card m : ℝ) * δ := h3

/-- Pointwise limits of measurable functions into `ℂ` are measurable. -/
lemma measurable_of_tendsto_nat {g : Ω → ℂ} {F : ℕ → Ω → ℂ} (hF : ∀ j, Measurable (F j))
    (h : ∀ x, Tendsto (fun j => F j x) atTop (𝓝 (g x))) : Measurable g :=
  measurable_of_tendsto_metrizable hF (tendsto_pi_nhds.mpr h)

/-- **Measurability of the continuous functional calculus.**  For a matrix-valued function with
measurable entries and Hermitian values, `x ↦ cfc f (M x)` is measurable for every continuous
function `f`. -/
theorem measurable_cfc_of_hermitian {M : Ω → Matrix m m ℂ}
    (hM : ∀ a b, Measurable fun x => M x a b) (hHerm : ∀ x, (M x).IsHermitian)
    {f : ℝ → ℝ} (hf : Continuous f) :
    Measurable fun x => cfc f (M x) := by
  classical
  -- polynomial approximations to accuracy `1/(j+1)` on `[-(j+1), j+1]`
  have hex : ∀ j : ℕ, ∃ q : ℝ[X], ∀ y ∈ Set.Icc (-(j : ℝ) - 1) ((j : ℝ) + 1),
      |q.eval y - f y| ≤ 1 / ((j : ℝ) + 1) := by
    intro j
    have hjpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    obtain ⟨q, hq⟩ := exists_polynomial_near_of_continuousOn (-(j : ℝ) - 1) ((j : ℝ) + 1) f
      hf.continuousOn (ε := 1 / ((j : ℝ) + 1)) (one_div_pos.mpr hjpos)
    exact ⟨q, fun y hy => le_of_lt (hq y hy)⟩
  choose q hq using hex
  have hq0 : ∀ j : ℕ, (0 : ℝ) ≤ 1 / ((j : ℝ) + 1) := by
    intro j
    have hjpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    exact le_of_lt (one_div_pos.mpr hjpos)
  -- entrywise measurability via the pointwise limit of the cut-off approximants
  refine measurable_matrix_of_entries fun a b => ?_
  have hev : ∀ x : Ω, ∀ᶠ j : ℕ in atTop, hsNorm (M x) ≤ (j : ℝ) := fun x =>
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (hsNorm (M x)))
  refine measurable_of_tendsto_nat (g := fun x : Ω => cfc f (M x) a b)
    (F := fun j (x : Ω) => if hsNorm (M x) ≤ (j : ℝ) then polyMatrix (q j) (M x) a b else 0) ?_ ?_
  · intro j
    have hcond : MeasurableSet {x : Ω | hsNorm (M x) ≤ (j : ℝ)} :=
      measurableSet_le (measurable_hsNorm hM) measurable_const
    have hpoly : Measurable fun x : Ω => polyMatrix (q j) (M x) a b := by
      have hcont : Continuous fun X : Matrix m m ℂ => polyMatrix (q j) X a b :=
        (continuous_apply b).comp ((continuous_apply a).comp (continuous_polyMatrix (q j)))
      exact hcont.measurable.comp (measurable_matrix_of_entries hM)
    exact Measurable.ite hcond hpoly measurable_const
  · intro x
    have hpoly_tend : Tendsto (fun j : ℕ => polyMatrix (q j) (M x) a b) atTop
        (𝓝 (cfc f (M x) a b)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero_norm' (f := fun j : ℕ =>
        ‖polyMatrix (q j) (M x) a b - cfc f (M x) a b‖)
        (a := fun j : ℕ => Real.sqrt (Fintype.card m : ℝ) * (1 / ((j : ℝ) + 1))) ?_ ?_
      · filter_upwards [hev x] with j hj
        simpa using norm_entry_polyMatrix_sub_cfc_le (hHerm x) hf hj (hq j) (hq0 j) a b
      · have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
          (Real.sqrt (Fintype.card m : ℝ))
        simpa using h
    refine Tendsto.congr' ?_ hpoly_tend
    filter_upwards [hev x] with j hj
    exact (ite_eq_left hj).symm

end Measurability

section FinTraceMeasure

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

/-- The normalized trace is continuous in the matrix entries. -/
lemma continuous_normTrace : Continuous fun X : Matrix (Fin n) (Fin n) ℂ => normTrace X := by
  have hfun : (fun X : Matrix (Fin n) (Fin n) ℂ => normTrace X)
      = fun X => (n : ℝ)⁻¹ * (∑ i, X i i).re := by
    funext X
    simp only [normTrace, Matrix.trace, Matrix.diag]
  rw [hfun]
  fun_prop

/-- **Measurability of the normalized-trace statistic.** -/
lemma measurable_normTrace_cfc {M : Ω → Matrix (Fin n) (Fin n) ℂ}
    (hM : ∀ a b, Measurable fun x => M x a b) (hHerm : ∀ x, (M x).IsHermitian)
    {f : ℝ → ℝ} (hf : Continuous f) :
    Measurable fun x => normTrace (hermCfc (M x) f (hHerm x)) :=
  continuous_normTrace.measurable.comp (measurable_cfc_of_hermitian hM hHerm hf)

end FinTraceMeasure

/-! ## 3. Bounds on the normalized trace of a cfc -/

section Bounds

variable {n : ℕ}

/-- The trace of the cfc of a Hermitian matrix is the sum of `g` over the eigenvalues. -/
lemma trace_hermCfc_eq (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.IsHermitian) (g : ℝ → ℝ) :
    (hermCfc M g hM).trace = ((∑ i, g (hM.eigenvalues i) : ℝ) : ℂ) := by
  rw [trace_cfc_eq_sum_eigenvalues hM g, ← Complex.ofReal_sum]

/-- **Pointwise bound for the normalized trace.**  If `|g| ≤ C` everywhere then the normalized
trace of `g(M)` is bounded by `C`. -/
lemma abs_normTrace_cfc_le {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) (g : ℝ → ℝ)
    {C : ℝ} (hC : ∀ y, |g y| ≤ C) (hC0 : 0 ≤ C) :
    |normTrace (hermCfc M g hM)| ≤ C := by
  rw [normTrace, trace_hermCfc_eq M hM g, Complex.ofReal_re]
  have hinv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
  have hsum : |∑ i, g (hM.eigenvalues i)| ≤ (n : ℝ) * C := by
    calc |∑ i, g (hM.eigenvalues i)| ≤ ∑ i, |g (hM.eigenvalues i)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, C := Finset.sum_le_sum fun i _ => hC _
      _ = (n : ℝ) * C := by simp
  rw [abs_mul, abs_of_nonneg hinv]
  refine (mul_le_mul_of_nonneg_left hsum hinv).trans ?_
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simpa using hC0
  · have h1 : (n : ℝ)⁻¹ * (n : ℝ) = 1 := inv_mul_cancel₀ (by exact_mod_cast hn.ne')
    rw [← mul_assoc, h1, one_mul]

/-- **Nonnegativity of the normalized trace.**  If `0 ≤ g` then `0 ≤ τ(g(M))`. -/
lemma normTrace_cfc_nonneg {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) {g : ℝ → ℝ}
    (hg : ∀ y, 0 ≤ g y) : 0 ≤ normTrace (hermCfc M g hM) := by
  rw [normTrace, trace_hermCfc_eq M hM g, Complex.ofReal_re]
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => hg _)

end Bounds

/-! ## 4. The `L²`/integrability side conditions from boundedness -/

section GaussianStats

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n : ℕ} {M : Ω → Matrix (Fin n) (Fin n) ℂ}
  (hM : ∀ a b, Measurable fun x => M x a b) (hHerm : ∀ x, (M x).IsHermitian)

include hM hHerm

/-- The normalized-trace statistic of a matrix family satisfies `MemLp 2` as soon as the
cutoff is bounded. -/
lemma memLp_normTrace_cfc {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ} (hC : ∀ y, |f y| ≤ C)
    (hC0 : 0 ≤ C) :
    MemLp (fun x => normTrace (hermCfc (M x) f (hHerm x))) 2 μ :=
  MemLp.of_bound (measurable_normTrace_cfc hM hHerm hf).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using abs_normTrace_cfc_le (hHerm x) f hC hC0)

/-- The normalized-trace statistic of a matrix family is integrable as soon as the cutoff is
bounded. -/
lemma integrable_normTrace_cfc {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ} (hC : ∀ y, |f y| ≤ C)
    (hC0 : 0 ≤ C) :
    Integrable (fun x => normTrace (hermCfc (M x) f (hHerm x))) μ :=
  Integrable.of_bound (measurable_normTrace_cfc hM hHerm hf).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using abs_normTrace_cfc_le (hHerm x) f hC hC0)

/-- The `W`-statistic `τ(g(M))` of a nonnegative `g` has nonnegative integral. -/
lemma integral_normTrace_cfc_nonneg {g : ℝ → ℝ} (hg : ∀ y, 0 ≤ g y) :
    0 ≤ ∫ x, normTrace (hermCfc (M x) g (hHerm x)) ∂μ :=
  integral_nonneg fun x => normTrace_cfc_nonneg (hHerm x) hg

end GaussianStats

/-! ## 5. The smooth cutoff package -/

/-- The properties of a smooth cutoff that the spectral-exclusion argument consumes: `f ∈ C¹`,
`0 ≤ f ≤ 1`, `f = 1` outside `S + (-ε, ε)`, and `(f')²` compactly supported (which makes `f'`
globally bounded). -/
structure IsSmoothCutoff (S : Set ℝ) (ε : ℝ) (f : ℝ → ℝ) : Prop where
  /-- `f` is continuously differentiable -/
  contDiff : ContDiff ℝ 1 f
  /-- `f` is nonnegative -/
  nonneg : ∀ x, 0 ≤ f x
  /-- `f` is bounded by one -/
  le_one : ∀ x, f x ≤ 1
  /-- `f` equals one outside the `ε`-neighbourhood of `S` -/
  eq_one : ∀ x, x ∉ S + Set.Ioo (-ε) ε → f x = 1
  /-- the square of the derivative has compact support -/
  compactSupport : HasCompactSupport fun x => (deriv f x) ^ 2

lemma IsSmoothCutoff.abs_le_one {S : Set ℝ} {ε : ℝ} {f : ℝ → ℝ} (h : IsSmoothCutoff S ε f)
    (x : ℝ) : |f x| ≤ 1 := by
  rw [abs_le]
  exact ⟨by linarith [h.nonneg x], h.le_one x⟩

/-- **Global bound for the derivative of a smooth cutoff.**  The support of `f'` is contained in
the (compact) support of `(f')²`, and `f'` is continuous. -/
theorem IsSmoothCutoff.exists_deriv_bound {S : Set ℝ} {ε : ℝ} {f : ℝ → ℝ}
    (h : IsSmoothCutoff S ε f) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |deriv f x| ≤ M := by
  have hsub : Function.support (deriv f) ⊆ tsupport fun x => (deriv f x) ^ 2 := by
    intro x hx
    refine subset_tsupport _ ?_
    simp only [Function.mem_support] at hx ⊢
    exact pow_ne_zero 2 hx
  obtain ⟨C, hC⟩ := h.compactSupport.isCompact.exists_bound_of_continuousOn
    h.contDiff.continuous_deriv_one.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ tsupport (fun y => (deriv f y) ^ 2)
  · have h1 : ‖deriv f x‖ ≤ C := hC x hx
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (le_max_left _ _)
  · have hzero : deriv f x = 0 := by
      by_contra hne
      exact hx (hsub (by simpa [Function.mem_support] using hne))
    rw [hzero, abs_zero]
    exact le_max_right _ _

/-- `exists_contDiff_cutoff` packaged as an `IsSmoothCutoff`. -/
theorem exists_isSmoothCutoff {S : Set ℝ} {ε : ℝ} (hS : IsCompact S) (hε : 0 < ε) :
    ∃ f : ℝ → ℝ, IsSmoothCutoff S ε f := by
  obtain ⟨f, hcd, h0, -, hone, hle, -, hsupp⟩ := exists_contDiff_cutoff hS hε
  exact ⟨f, hcd, h0, hle, hone, hsupp⟩

/-! ## 6. Spectral inclusion for the scalar GUE matrix with a smooth cutoff -/

/-- **Scalar spectral inclusion with a smooth cutoff.**  For a `C¹` cutoff `f` with
`0 ≤ f ≤ 1`, `f = 1` outside `S + (-ε, ε)` and `(f')²` compactly supported, the analytic inputs
of Lemma S that are *not* mean estimates are discharged:

* the variance input `(V)` is an explicit hypothesis here and is discharged in
  `ae_eventually_spectrum_subset_scalar_smooth` from the unconditional smooth Lemma V;
* the `L²`/integrability side conditions `hZ`, `hWint`, `hW0` are discharged from `|f| ≤ 1` and
  the global bound on `f'`.

Only the mean comparison `hM` (Lemma M) and the `(W)` bound `hWb` (Lemma W) remain explicit. -/
theorem ae_eventually_spectrum_subset_scalar_smooth_of_hV {r : ℕ} (i : Fin r) {ε : ℝ}
    (hε : 0 < ε) {f : ℝ → ℝ}
    (hf : IsSmoothCutoff (spectrum ℝ (semicircularFamily r i)) ε f)
    {C C' : ℝ} (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (hM : ∀ᶠ N : ℕ in atTop,
      |∫ x, normTrace (hermCfc (gueFamily r N x i) f (gueMatrixOn_isHermitian x N i))
        ∂(commonGaussianMeasure (Fin r))| ≤ C / (N : ℝ) ^ 2)
    (hV : ∀ N : ℕ,
      variance (fun x => normTrace (hermCfc (gueFamily r N x i) f
        (gueMatrixOn_isHermitian x N i))) (commonGaussianMeasure (Fin r))
      ≤ C / (N : ℝ) ^ 2 * ∫ x, normTrace (hermCfc (gueFamily r N x i)
          (fun y => (deriv f y) ^ 2) (gueMatrixOn_isHermitian x N i))
          ∂(commonGaussianMeasure (Fin r)))
    (hWb : ∀ N : ℕ,
      ∫ x, normTrace (hermCfc (gueFamily r N x i) (fun y => (deriv f y) ^ 2)
        (gueMatrixOn_isHermitian x N i)) ∂(commonGaussianMeasure (Fin r))
        ≤ C' / (N : ℝ) ^ 2) :
    ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ᶠ N : ℕ in atTop,
      spectrum ℝ (gueFamily r N x i) ⊆
        spectrum ℝ (semicircularFamily r i) + Set.Ioo (-ε) ε := by
  classical
  obtain ⟨M, hM0, hMbound⟩ := hf.exists_deriv_bound
  have hderiv_cont : Continuous (fun y : ℝ => (deriv f y) ^ 2) :=
    hf.contDiff.continuous_deriv_one.pow 2
  refine ae_eventually_spectrum_subset_growing (m := fun N => N)
    (hm := (eventually_ge_atTop (1 : ℕ)).mono fun N hN =>
      Nat.lt_of_lt_of_le Nat.zero_lt_one hN)
    (hε := hε) (hf0 := hf.nonneg) (hf1 := hf.eq_one)
    (H := fun N x => gueFamily r N x i) (hH := fun N x => gueMatrixOn_isHermitian x N i)
    (C := C) (C' := C') (D := 1) hC hC' zero_le_one
    (by filter_upwards with N; simp) ?_ ?_ ?_ hM (Eventually.of_forall hV) (Eventually.of_forall hWb)
  · -- `hZ`: bounded by one
    intro N
    exact memLp_normTrace_cfc (μ := commonGaussianMeasure (Fin r))
      (M := fun x => gueMatrixOn x N i)
      (hM := fun a b => measurable_gueMatrixOn_entry N i a b)
      (hHerm := fun x => gueMatrixOn_isHermitian x N i) hf.contDiff.continuous
      (fun y => hf.abs_le_one y) zero_le_one
  · -- `hWint`: bounded by `M ^ 2`
    intro N
    exact integrable_normTrace_cfc (μ := commonGaussianMeasure (Fin r))
      (M := fun x => gueMatrixOn x N i)
      (hM := fun a b => measurable_gueMatrixOn_entry N i a b)
      (hHerm := fun x => gueMatrixOn_isHermitian x N i) hderiv_cont
      (fun y => by
        rw [abs_of_nonneg (sq_nonneg (deriv f y))]
        calc (deriv f y) ^ 2 = |deriv f y| ^ 2 := by rw [sq_abs]
          _ ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hMbound y) 2)
      (sq_nonneg M)
  · -- `hW0`: the integrand is nonnegative
    intro N
    exact integral_normTrace_cfc_nonneg (μ := commonGaussianMeasure (Fin r))
      (M := fun x => gueMatrixOn x N i)
      (hM := fun a b => measurable_gueMatrixOn_entry N i a b)
      (hHerm := fun x => gueMatrixOn_isHermitian x N i) (fun y => sq_nonneg (deriv f y))

/-! ## 7. The chosen smooth cutoff and the final scalar inclusion -/

local instance instNontrivialClosedSemicircular (r : ℕ) :
    Nontrivial (closedSemicircularAlgebra (Fin r)) :=
  (closedGeneratedVacuumState (Fin r)).toProbabilitySpace.nontrivial

/-- The spectrum of `i`-th semicircular element is compact (and nonempty). -/
lemma isCompact_spectrum_semicircular {r : ℕ} (i : Fin r) :
    IsCompact (spectrum ℝ (semicircularFamily r i)) :=
  ContinuousFunctionalCalculus.isCompact_spectrum _

/-- A chosen **smooth cutoff** for the spectrum of the `i`-th semicircular element at radius
`ε > 0`, produced by `exists_contDiff_cutoff`. -/
noncomputable def smoothCutoff {r : ℕ} (i : Fin r) (ε : ℝ) (hε : 0 < ε) : ℝ → ℝ :=
  Classical.choose (exists_isSmoothCutoff (isCompact_spectrum_semicircular i) hε)

lemma smoothCutoff_spec {r : ℕ} (i : Fin r) {ε : ℝ} (hε : 0 < ε) :
    IsSmoothCutoff (spectrum ℝ (semicircularFamily r i)) ε (smoothCutoff i ε hε) :=
  Classical.choose_spec (exists_isSmoothCutoff (isCompact_spectrum_semicircular i) hε)

/-- **Scalar spectral inclusion from the smooth cutoff**, with the variance input `(V)` still
explicit. -/
theorem scalarSpectralInclusion_of_smoothCutoff_of_hV {r : ℕ}
    (C C' : ℝ) (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (hM : ∀ (i : Fin r) (ε : ℝ) (hε : 0 < ε),
      ∀ᶠ N : ℕ in atTop,
        |∫ x, normTrace (hermCfc (gueFamily r N x i) (smoothCutoff i ε hε)
          (gueMatrixOn_isHermitian x N i)) ∂(commonGaussianMeasure (Fin r))|
          ≤ C / (N : ℝ) ^ 2)
    (hV : ∀ (i : Fin r) (ε : ℝ) (hε : 0 < ε) (N : ℕ),
      variance (fun x => normTrace (hermCfc (gueFamily r N x i) (smoothCutoff i ε hε)
        (gueMatrixOn_isHermitian x N i))) (commonGaussianMeasure (Fin r))
      ≤ C / (N : ℝ) ^ 2 * ∫ x, normTrace (hermCfc (gueFamily r N x i)
          (fun y => (deriv (smoothCutoff i ε hε) y) ^ 2)
          (gueMatrixOn_isHermitian x N i)) ∂(commonGaussianMeasure (Fin r)))
    (hWb : ∀ (i : Fin r) (ε : ℝ) (hε : 0 < ε) (N : ℕ),
      ∫ x, normTrace (hermCfc (gueFamily r N x i)
        (fun y => (deriv (smoothCutoff i ε hε) y) ^ 2)
        (gueMatrixOn_isHermitian x N i)) ∂(commonGaussianMeasure (Fin r))
        ≤ C' / (N : ℝ) ^ 2) :
    ScalarSpectralInclusion r := by
  classical
  have hstep : ∀ (i : Fin r) (k : ℕ),
      ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ᶠ N : ℕ in atTop,
        spectrum ℝ (gueFamily r N x i) ⊆
          spectrum ℝ (semicircularFamily r i) +
            Set.Ioo (-(1 / (k + 1 : ℝ))) (1 / (k + 1 : ℝ)) := by
    intro i k
    have hε : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
    exact ae_eventually_spectrum_subset_scalar_smooth_of_hV i hε (smoothCutoff_spec i hε)
      hC hC' (hM i _ hε) (hV i _ hε) (hWb i _ hε)
  have hall : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      ∀ i : Fin r, ∀ k : ℕ, ∀ᶠ N : ℕ in atTop,
        spectrum ℝ (gueFamily r N x i) ⊆
          spectrum ℝ (semicircularFamily r i) +
            Set.Ioo (-(1 / (k + 1 : ℝ))) (1 / (k + 1 : ℝ)) := by
    have h := ae_all_iff.2 (fun p : Fin r × ℕ => hstep p.1 p.2)
    filter_upwards [h] with x hx
    intro i k
    exact hx (i, k)
  filter_upwards [hall] with x hx
  intro i ε hε
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (1 : ℝ) / (k + 1 : ℝ) < ε := by
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
    refine ⟨n, ?_⟩
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < n + 1)]
    have hn' : (1 : ℝ) < ε * (n + 1) := by
      have h : (1 : ℝ) / ε < n + 1 := by linarith
      rw [div_lt_iff₀ hε] at h
      rw [mul_comm]
      exact h
    linarith
  have hsub : Set.Ioo (-(1 / (k + 1 : ℝ))) (1 / (k + 1 : ℝ)) ⊆ Set.Ioo (-ε) ε := by
    intro y hy
    exact ⟨lt_trans (neg_lt_neg hk) hy.1, lt_trans hy.2 hk⟩
  filter_upwards [hx i k] with N hN
  intro a ha
  have hmem : a ∈ spectrum ℝ (semicircularFamily r i) + Set.Ioo (-ε) ε := by
    have h1 : a ∈ spectrum ℝ (semicircularFamily r i) +
        Set.Ioo (-(1 / (k + 1 : ℝ))) (1 / (k + 1 : ℝ)) := hN ha
    rw [Set.mem_add] at h1 ⊢
    obtain ⟨b, hb, c, hc, hbc⟩ := h1
    exact ⟨b, hb, c, hsub hc, hbc⟩
  exact exists_mem_of_mem_add_Ioo hmem

/-! ## 8. Block-level statistics: the side conditions of the unconditional Lemma V -/

section BlockStats

variable {r N : ℕ}

/-- Entry measurability of the GUE matrix on the Gaussian block. -/
lemma measurable_gueMatrix_entry_euclid {ι : Type*} [Fintype ι] (N : ℕ) (i : ι) (a b : Fin N) :
    Measurable fun y : EuclideanSpace ℝ (GUECoord ι N) => gueMatrix y i a b :=
  measurable_pi_iff.mp (measurable_pi_iff.mp (measurable_gueMatrix N i) a) b

/-- The pencil statistic of the scalar pencil, as a function of the block coordinate. -/
lemma gueStatisticCfc_scalarCoeff_eq_fun (f : ℝ → ℝ) (i : Fin r)
    (h0 : (0 : Matrix Unit Unit ℂ).IsHermitian)
    (hA : ∀ j, (scalarCoeff i j).IsHermitian) :
    gueStatisticCfc (N := N) (ι := Fin r) (d := Unit) f 0 (scalarCoeff i) h0 hA
      = fun y : EuclideanSpace ℝ (GUECoord (Fin r) N) =>
          normTrace (hermCfc (gueMatrix y i) f (gueMatrix_isHermitian y i)) :=
  funext fun y => gueStatisticCfc_scalarCoeff_eq f i y h0 hA

/-- `MemLp 2` of the scalar pencil statistic, from a bound on the cutoff. -/
lemma memLp_gueStatisticCfc_scalar {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ}
    (hC : ∀ y, |f y| ≤ C) (hC0 : 0 ≤ C) (i : Fin r)
    (h0 : (0 : Matrix Unit Unit ℂ).IsHermitian)
    (hA : ∀ j, (scalarCoeff i j).IsHermitian) :
    MemLp (gueStatisticCfc (N := N) (ι := Fin r) (d := Unit) f 0 (scalarCoeff i) h0 hA) 2
      (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) N))) := by
  rw [gueStatisticCfc_scalarCoeff_eq_fun f i h0 hA]
  exact memLp_normTrace_cfc (μ := stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) N)))
    (M := fun y : EuclideanSpace ℝ (GUECoord (Fin r) N) => gueMatrix y i)
    (hM := fun a b => measurable_gueMatrix_entry_euclid N i a b)
    (hHerm := fun y => gueMatrix_isHermitian y i) hf hC hC0

end BlockStats

/-! ## 9. The direction statistic `τ(f'(H) D_p)` at the block level -/

section DirStats

variable {r N : ℕ}

/-- A uniformly bounded function has polynomial growth. -/
lemma polyGrowth_of_bound' {g : ℝ → ℝ} {C : ℝ} (h : ∀ x, |g x| ≤ C) : PolyGrowth g :=
  ⟨max C 0, le_max_right _ _, 0, fun x => by
    rw [pow_zero, mul_one]
    exact (h x).trans (le_max_left _ _)⟩

/-- Measurability of a matrix product, entrywise. -/
lemma measurable_matrix_mul_entries {Ω : Type*} [MeasurableSpace Ω] {m : Type*} [Fintype m]
    {X Y : Ω → Matrix m m ℂ} (hX : ∀ a b, Measurable fun x => X x a b)
    (hY : ∀ a b, Measurable fun x => Y x a b) :
    ∀ a b, Measurable fun x => (X x * Y x) a b := by
  intro a b
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ => (hX a k).mul (hY k b)

/-- Measurability of the real part of the trace, entrywise. -/
lemma measurable_trace_re {Ω : Type*} [MeasurableSpace Ω] {m : Type*} [Fintype m]
    {X : Ω → Matrix m m ℂ} (hX : ∀ a b, Measurable fun x => X x a b) :
    Measurable fun x => (X x).trace.re := by
  have h : (fun x => (X x).trace.re) = fun x => (∑ i, X x i i).re := by
    funext x
    simp only [Matrix.trace, Matrix.diag]
  rw [h]
  exact Complex.measurable_re.comp (Finset.measurable_sum _ fun i _ => hX i i)

section PencilDir

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]

/-- The normalized pencil trace as `(card (d × Fin N))⁻¹` times the real trace. -/
lemma guePencilNormTrace_eq_inv_card (M : Matrix (d × Fin N) (d × Fin N) ℂ) :
    guePencilNormTrace M = ((Fintype.card (d × Fin N) : ℕ) : ℝ)⁻¹ * M.trace.re := by
  simp [guePencilNormTrace, gueNormConst]

/-- The direction statistic as an explicit normalized trace. -/
lemma gueStatisticCfcDir_eq (f : ℝ → ℝ) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (p : GUECoord ι N)
    (y : EuclideanSpace ℝ (GUECoord ι N)) :
    gueStatisticCfcDir f A₀ A hA₀ hA p y
      = ((Fintype.card (d × Fin N) : ℕ) : ℝ)⁻¹ *
          (cfc (deriv f) (guePencilMatrix A₀ A (WithLp.ofLp y)) * gueDirMatrix A p).trace.re := by
  simp only [gueStatisticCfcDir, guePencilNormTrace_eq_inv_card, guePencilCfc_eq_cfc]

/-- Hilbert–Schmidt bound for the cfc of a bounded function. -/
lemma hsNorm_cfc_le_card_mul_sq {m : Type*} [Fintype m] [DecidableEq m]
    (X : Matrix m m ℂ) (hX : X.IsHermitian) {g : ℝ → ℝ} (hg : Continuous g) {M : ℝ}
    (hM : ∀ y, |g y| ≤ M) :
    hsNorm (cfc g X) ≤ (Fintype.card m : ℝ) * M ^ 2 := by
  rw [hsNorm_cfc_eq_sum_eigenvalues X hX g hg]
  calc ∑ i, (g (hX.eigenvalues i)) ^ 2 ≤ ∑ _i : m, M ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hM _) 2
    _ = (Fintype.card m : ℝ) * M ^ 2 := by
        simp [Finset.sum_const, nsmul_eq_mul]

/-- Bound on the normalized trace of a product. -/
lemma abs_inv_card_trace_mul_le {m : Type*} [Fintype m] [DecidableEq m]
    (X D : Matrix m m ℂ) :
    |(Fintype.card m : ℝ)⁻¹ * (X * D).trace.re|
      ≤ (Fintype.card m : ℝ)⁻¹ * (Real.sqrt (hsNorm X) * Real.sqrt (hsNorm D)) := by
  have h1 : |(X * D).trace.re| ≤ ‖(X * D).trace‖ := Complex.abs_re_le_norm _
  have h2 : ‖(X * D).trace‖ ≤ Real.sqrt (hsNorm X) * Real.sqrt (hsNorm D) :=
    norm_trace_mul_le_sqrt_hsNorm X D
  rw [abs_mul, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)

/-- Entry measurability of the affine pencil on the Gaussian block. -/
lemma measurable_guePencilMatrix_entry_euclid (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (a b : d × Fin N) :
    Measurable fun y : EuclideanSpace ℝ (GUECoord ι N) =>
      guePencilMatrix A₀ A (WithLp.ofLp y) a b :=
  measurable_pi_iff.mp (measurable_pi_iff.mp (continuous_guePencilMatrix A₀ A).measurable a) b

/-- Measurability of the direction statistic. -/
lemma measurable_gueStatisticCfcDir (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) (p : GUECoord ι N) :
    Measurable fun y : EuclideanSpace ℝ (GUECoord ι N) =>
      gueStatisticCfcDir f A₀ A hA₀ hA p y := by
  have hD : ∀ a b, Measurable fun _ : EuclideanSpace ℝ (GUECoord ι N) =>
      gueDirMatrix A p a b := fun a b => measurable_const
  have hX : ∀ a b, Measurable fun y : EuclideanSpace ℝ (GUECoord ι N) =>
      cfc (deriv f) (guePencilMatrix A₀ A (WithLp.ofLp y)) a b := by
    have hcfc : Measurable fun y : EuclideanSpace ℝ (GUECoord ι N) =>
        cfc (deriv f) (guePencilMatrix A₀ A (WithLp.ofLp y)) :=
      measurable_cfc_of_hermitian (fun a b => measurable_guePencilMatrix_entry_euclid A₀ A a b)
        (fun y => guePencilMatrix_isHermitian A₀ A hA₀ hA _) hf.continuous_deriv_one
    exact fun a b => measurable_pi_iff.mp (measurable_pi_iff.mp hcfc a) b
  have hfun : (fun y : EuclideanSpace ℝ (GUECoord ι N) =>
        gueStatisticCfcDir f A₀ A hA₀ hA p y)
      = fun y => ((Fintype.card (d × Fin N) : ℕ) : ℝ)⁻¹ *
          (cfc (deriv f) (guePencilMatrix A₀ A (WithLp.ofLp y)) * gueDirMatrix A p).trace.re :=
    funext fun y => gueStatisticCfcDir_eq f A₀ A hA₀ hA p y
  rw [hfun]
  exact measurable_const.mul (measurable_trace_re (measurable_matrix_mul_entries hX hD))

/-- Bound on the direction statistic, uniform in the GUE coordinates. -/
lemma abs_gueStatisticCfcDir_le (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) (p : GUECoord ι N) {M : ℝ}
    (hMbound : ∀ y, |deriv f y| ≤ M) (y : EuclideanSpace ℝ (GUECoord ι N)) :
    |gueStatisticCfcDir f A₀ A hA₀ hA p y|
      ≤ ((Fintype.card (d × Fin N) : ℕ) : ℝ)⁻¹ *
          (Real.sqrt ((Fintype.card (d × Fin N) : ℝ) * M ^ 2) *
            Real.sqrt (hsNorm (gueDirMatrix A p))) := by
  rw [gueStatisticCfcDir_eq]
  refine (abs_inv_card_trace_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  exact Real.sqrt_le_sqrt
    (hsNorm_cfc_le_card_mul_sq _ (guePencilMatrix_isHermitian A₀ A hA₀ hA _)
      hf.continuous_deriv_one hMbound)

/-- Measurability of the Hilbert–Schmidt norm of the cfc of the derivative. -/
lemma measurable_hsNorm_guePencilCfc (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) :
    Measurable fun y : EuclideanSpace ℝ (GUECoord ι N) =>
      hsNorm (guePencilCfc (deriv f) A₀ A hA₀ hA y) := by
  have hcfc : Measurable fun y : EuclideanSpace ℝ (GUECoord ι N) =>
      cfc (deriv f) (guePencilMatrix A₀ A (WithLp.ofLp y)) :=
    measurable_cfc_of_hermitian (fun a b => measurable_guePencilMatrix_entry_euclid A₀ A a b)
      (fun y => guePencilMatrix_isHermitian A₀ A hA₀ hA _) hf.continuous_deriv_one
  have hfun : (fun y : EuclideanSpace ℝ (GUECoord ι N) =>
        hsNorm (guePencilCfc (deriv f) A₀ A hA₀ hA y))
      = fun y => hsNorm (cfc (deriv f) (guePencilMatrix A₀ A (WithLp.ofLp y))) := by
    funext y
    rw [guePencilCfc_eq_cfc]
  rw [hfun]
  exact measurable_hsNorm (fun a b => measurable_pi_iff.mp
    (measurable_pi_iff.mp hcfc a) b)

/-- Bound on the Hilbert–Schmidt norm of the cfc of the derivative. -/
lemma hsNorm_guePencilCfc_le (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) {M : ℝ} (hMbound : ∀ y, |deriv f y| ≤ M)
    (y : EuclideanSpace ℝ (GUECoord ι N)) :
    hsNorm (guePencilCfc (deriv f) A₀ A hA₀ hA y)
      ≤ (Fintype.card (d × Fin N) : ℝ) * M ^ 2 := by
  rw [guePencilCfc_eq_cfc]
  exact hsNorm_cfc_eq_sum_eigenvalues _ (guePencilMatrix_isHermitian A₀ A hA₀ hA _)
    (deriv f) hf.continuous_deriv_one ▸
    hsNorm_cfc_le_card_mul_sq _ (guePencilMatrix_isHermitian A₀ A hA₀ hA _)
      hf.continuous_deriv_one hMbound

end PencilDir

end DirStats

/-! ## 10. Discharging the variance input `(V)` -/

section HVDischarge

variable {r : ℕ}

/-- The scalar coefficient matrix `1` has Frobenius norm one. -/
lemma frob_one_unit : frob (1 : Matrix Unit Unit ℂ) = 1 := by
  simp [frob]

/-- The Frobenius sum of the scalar pencil coefficients is one. -/
lemma sum_frob_scalarCoeff_sq (i : Fin r) :
    ∑ j, (frob (scalarCoeff i j)) ^ 2 = 1 := by
  rw [Finset.sum_eq_single i]
  · rw [scalarCoeff, ite_eq_left rfl, frob_one_unit]
    norm_num
  · intro j _ hji
    rw [scalarCoeff, ite_eq_right hji]
    simp [frob]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- **The variance input `(V)` of Lemma S, at the block level**, from the unconditional smooth
Lemma V specialized to the `Unit`-pencil `A₀ = 0`, `A_i = 1`, `A_j = 0`: the constant is
`2 (∑_j frob(A_j)²) / card Unit = 2`. -/
theorem variance_gueStatisticCfc_scalar_block (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hf1 : ∀ y, |f y| ≤ 1) {M : ℝ} (hMbound : ∀ y, |deriv f y| ≤ M) (i : Fin r)
    (h0 : (0 : Matrix Unit Unit ℂ).IsHermitian)
    (hA : ∀ j, (scalarCoeff i j).IsHermitian) {N : ℕ} (hN : 0 < N) :
    variance (gueStatisticCfc (N := N) (ι := Fin r) (d := Unit) f 0 (scalarCoeff i) h0 hA)
        (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) N)))
      ≤ 2 / (N : ℝ) ^ 2 * ∫ x, gueStatisticCfc (N := N) (ι := Fin r) (d := Unit)
          (fun y => (deriv f y) ^ 2) 0 (scalarCoeff i) h0 hA x
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) N))) := by
  classical
  have hderiv_cont : Continuous (fun y : ℝ => (deriv f y) ^ 2) :=
    hf.continuous_deriv_one.pow 2
  have hderiv_bound : ∀ y : ℝ, |(deriv f y) ^ 2| ≤ M ^ 2 := fun y => by
    rw [abs_of_nonneg (sq_nonneg (deriv f y))]
    calc (deriv f y) ^ 2 = |deriv f y| ^ 2 := by rw [sq_abs]
      _ ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hMbound y) 2
  have hmeasDir : ∀ p : GUECoord (Fin r) N,
      AEStronglyMeasurable (fun y : EuclideanSpace ℝ (GUECoord (Fin r) N) =>
        gueStatisticCfcDir f 0 (scalarCoeff i) h0 hA p y)
        (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) N))) := fun p =>
    (measurable_gueStatisticCfcDir f hf 0 (scalarCoeff i) h0 hA p).aestronglyMeasurable
  have hmeasHS : AEStronglyMeasurable (fun y : EuclideanSpace ℝ (GUECoord (Fin r) N) =>
      hsNorm (guePencilCfc (deriv f) 0 (scalarCoeff i) h0 hA y))
      (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) N))) :=
    (measurable_hsNorm_guePencilCfc f hf 0 (scalarCoeff i) h0 hA).aestronglyMeasurable
  have hmain := lemmaS_V_input_unconditional (d := Unit) (ι := Fin r) (N := N) f hf
    (0 : Matrix Unit Unit ℂ) (scalarCoeff i) h0 hA hN ?_ ?_ ?_ ?_
  · -- the constant is `2 / N²`
    have hcard : (Fintype.card Unit : ℝ) = 1 := by simp
    have hconst : 2 * (∑ j, (frob (scalarCoeff i j)) ^ 2) / (Fintype.card Unit : ℝ)
        / (N : ℝ) ^ 2 = 2 / (N : ℝ) ^ 2 := by
      rw [sum_frob_scalarCoeff_sq i, hcard]
      ring
    rw [hconst] at hmain
    exact hmain
  · -- `hF`
    exact memLp_gueStatisticCfc_scalar hf.continuous hf1 zero_le_one i h0 hA
  · -- `hDmem`
    intro p
    refine MemLp.of_bound (hmeasDir p)
      (((Fintype.card (Unit × Fin N) : ℕ) : ℝ)⁻¹ *
        (Real.sqrt ((Fintype.card (Unit × Fin N) : ℝ) * M ^ 2) *
          Real.sqrt (hsNorm (gueDirMatrix (scalarCoeff i) p))))
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]
    exact abs_gueStatisticCfcDir_le f hf 0 (scalarCoeff i) h0 hA p hMbound y
  · -- `hpoly`
    intro p
    refine Filter.Eventually.of_forall fun y => ⟨?_, ?_⟩
    · refine polyGrowth_of_bound' (C := 1) fun u => ?_
      rw [gueStatisticCfc_scalarCoeff_eq f i (euclidUpdate y p u) h0 hA]
      exact abs_normTrace_cfc_le _ f hf1 zero_le_one
    · refine polyGrowth_of_bound' (C := ((Fintype.card (Unit × Fin N) : ℕ) : ℝ)⁻¹ *
        (Real.sqrt ((Fintype.card (Unit × Fin N) : ℝ) * M ^ 2) *
          Real.sqrt (hsNorm (gueDirMatrix (scalarCoeff i) p)))) fun u => ?_
      exact abs_gueStatisticCfcDir_le f hf 0 (scalarCoeff i) h0 hA p hMbound _
  · -- `hint`
    refine Integrable.of_bound hmeasHS ((Fintype.card (Unit × Fin N) : ℝ) * M ^ 2)
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hsNorm_nonneg _)]
    exact hsNorm_guePencilCfc_le f hf 0 (scalarCoeff i) h0 hA hMbound y

/-- **The variance input `(V)` on the common space**, from the block-level Lemma V: the constant
is exactly `2`.  For `N = 0` the statistic vanishes identically. -/
theorem variance_scalarStatistic_le_two (i : Fin r) {ε : ℝ} {f : ℝ → ℝ}
    (hf : IsSmoothCutoff (spectrum ℝ (semicircularFamily r i)) ε f) (N : ℕ) :
    variance (fun x : CommonSpace (Fin r) =>
        normTrace (hermCfc (gueFamily r N x i) f (gueMatrixOn_isHermitian x N i)))
        (commonGaussianMeasure (Fin r))
      ≤ 2 / (N : ℝ) ^ 2 * ∫ x, normTrace (hermCfc (gueFamily r N x i)
          (fun y => (deriv f y) ^ 2) (gueMatrixOn_isHermitian x N i))
          ∂(commonGaussianMeasure (Fin r)) := by
  classical
  obtain ⟨M, hM0, hMbound⟩ := hf.exists_deriv_bound
  have h0 : (0 : Matrix Unit Unit ℂ).IsHermitian := isHermitian_zero
  have hA : ∀ j, (scalarCoeff i j).IsHermitian := scalarCoeff_isHermitian i
  -- pointwise identification of the two statistics with the block statistics
  have hZfun : (fun x : CommonSpace (Fin r) =>
        normTrace (hermCfc (gueFamily r N x i) f (gueMatrixOn_isHermitian x N i)))
      = fun x => gueStatisticCfc (N := N) (ι := Fin r) (d := Unit) f 0 (scalarCoeff i) h0 hA (x N) :=
    funext fun x => (gueStatisticCfc_scalarCoeff_eq_commonSpace f i x h0 hA).symm
  have hWfun : (fun x : CommonSpace (Fin r) =>
        normTrace (hermCfc (gueFamily r N x i) (fun y => (deriv f y) ^ 2)
          (gueMatrixOn_isHermitian x N i)))
      = fun x => gueStatisticCfc (N := N) (ι := Fin r) (d := Unit)
          (fun y => (deriv f y) ^ 2) 0 (scalarCoeff i) h0 hA (x N) :=
    funext fun x => (gueStatisticCfc_scalarCoeff_eq_commonSpace
      (fun y => (deriv f y) ^ 2) i x h0 hA).symm
  have hderiv_bound : ∀ y : ℝ, |(deriv f y) ^ 2| ≤ M ^ 2 := fun y => by
    rw [abs_of_nonneg (sq_nonneg (deriv f y))]
    calc (deriv f y) ^ 2 = |deriv f y| ^ 2 := by rw [sq_abs]
      _ ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hMbound y) 2
  have hB : AEMeasurable (fun y : EuclideanSpace ℝ (GUECoord (Fin r) N) =>
      gueStatisticCfc (N := N) (ι := Fin r) (d := Unit) f 0 (scalarCoeff i) h0 hA y)
      (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) N))) :=
    (memLp_gueStatisticCfc_scalar hf.contDiff.continuous hf.abs_le_one zero_le_one
      i h0 hA).aemeasurable
  have hWB : AEStronglyMeasurable (fun y : EuclideanSpace ℝ (GUECoord (Fin r) N) =>
      gueStatisticCfc (N := N) (ι := Fin r) (d := Unit) (fun y => (deriv f y) ^ 2) 0
        (scalarCoeff i) h0 hA y)
      (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) N))) :=
    (memLp_gueStatisticCfc_scalar (hf.contDiff.continuous_deriv_one.pow 2) hderiv_bound
      (sq_nonneg M) i h0 hA).aestronglyMeasurable
  rw [hZfun, hWfun, variance_eval_commonGaussian (N := N) hB,
    integral_eval_commonGaussian (N := N) hWB]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have hzero : (fun y : EuclideanSpace ℝ (GUECoord (Fin r) 0) =>
        gueStatisticCfc (N := 0) (ι := Fin r) (d := Unit) f 0 (scalarCoeff i) h0 hA y)
        = fun _ => 0 := by
      funext y
      rw [gueStatisticCfc_scalarCoeff_eq f i y h0 hA]
      simp [normTrace]
    rw [hzero]
    have h0var : variance (fun _ : EuclideanSpace ℝ (GUECoord (Fin r) 0) => (0 : ℝ))
        (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) 0))) = 0 := by
      simp [variance, evariance]
    rw [h0var]
    simp
  · exact variance_gueStatisticCfc_scalar_block f hf.contDiff hf.abs_le_one hMbound i h0 hA hN

end HVDischarge

/-! ## 11. The strengthened scalar spectral inclusion -/

/-- **Scalar spectral inclusion with a smooth cutoff and the variance input discharged.**

The only analytic inputs left explicit are the mean comparison `hM` (Lemma M) and the `(W)`
bound `hWb` (Lemma W):
`hZ`, `hWint`, `hW0` are discharged from `|f| ≤ 1` and the bound on `f'` (§4, §6), and `hV`
is discharged from the unconditional smooth Lemma V with the constant
`2 (∑_j frob(A_j)²)/card Unit = 2` (§10). -/
theorem ae_eventually_spectrum_subset_scalar_smooth {r : ℕ} (i : Fin r) {ε : ℝ}
    (hε : 0 < ε) {f : ℝ → ℝ}
    (hf : IsSmoothCutoff (spectrum ℝ (semicircularFamily r i)) ε f)
    {C C' : ℝ} (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (hM : ∀ᶠ N : ℕ in atTop,
      |∫ x, normTrace (hermCfc (gueFamily r N x i) f (gueMatrixOn_isHermitian x N i))
        ∂(commonGaussianMeasure (Fin r))| ≤ C / (N : ℝ) ^ 2)
    (hWb : ∀ N : ℕ,
      ∫ x, normTrace (hermCfc (gueFamily r N x i) (fun y => (deriv f y) ^ 2)
        (gueMatrixOn_isHermitian x N i)) ∂(commonGaussianMeasure (Fin r))
        ≤ C' / (N : ℝ) ^ 2) :
    ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ᶠ N : ℕ in atTop,
      spectrum ℝ (gueFamily r N x i) ⊆
        spectrum ℝ (semicircularFamily r i) + Set.Ioo (-ε) ε := by
  have hCmax : (0 : ℝ) ≤ max C 2 := le_max_iff.mpr (Or.inr (by norm_num))
  -- `(V)` holds with the constant `2`; the engine uses one constant for `(M)` and `(V)`,
  -- so both are upgraded to `max C 2`
  refine ae_eventually_spectrum_subset_scalar_smooth_of_hV (r := r) i hε hf
    (C := max C 2) (C' := C') hCmax hC' ?_ ?_ hWb
  · filter_upwards [hM] with N hN
    refine hN.trans ?_
    gcongr
    exact le_max_left _ _
  · intro N
    refine (variance_scalarStatistic_le_two i hf N).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ ?_
    · gcongr
      exact le_max_right _ _
    · exact integral_normTrace_cfc_nonneg (μ := commonGaussianMeasure (Fin r))
        (M := fun x => gueMatrixOn x N i)
        (hM := fun a b => measurable_gueMatrixOn_entry N i a b)
        (hHerm := fun x => gueMatrixOn_isHermitian x N i)
        (fun y => sq_nonneg (deriv f y))

/-- **`ScalarSpectralInclusion` from the mean comparison and the `(W)` bound.**

This is the strengthened form of `scalarSpectralInclusion_of_inputs`: the indicator cutoff is
replaced by the smooth cutoff `smoothCutoff i ε hε` of `Probability/CutoffConstruction.lean`,
and of the six analytic inputs only `hM` (Lemma M) and `hWb` (Lemma W) remain. -/
theorem scalarSpectralInclusion_of_smoothCutoff {r : ℕ}
    (C C' : ℝ) (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (hM : ∀ (i : Fin r) (ε : ℝ) (hε : 0 < ε),
      ∀ᶠ N : ℕ in atTop,
        |∫ x, normTrace (hermCfc (gueFamily r N x i) (smoothCutoff i ε hε)
          (gueMatrixOn_isHermitian x N i)) ∂(commonGaussianMeasure (Fin r))|
          ≤ C / (N : ℝ) ^ 2)
    (hWb : ∀ (i : Fin r) (ε : ℝ) (hε : 0 < ε) (N : ℕ),
      ∫ x, normTrace (hermCfc (gueFamily r N x i)
        (fun y => (deriv (smoothCutoff i ε hε) y) ^ 2)
        (gueMatrixOn_isHermitian x N i)) ∂(commonGaussianMeasure (Fin r))
        ≤ C' / (N : ℝ) ^ 2) :
    ScalarSpectralInclusion r := by
  classical
  have hstep : ∀ (i : Fin r) (k : ℕ),
      ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ᶠ N : ℕ in atTop,
        spectrum ℝ (gueFamily r N x i) ⊆
          spectrum ℝ (semicircularFamily r i) +
            Set.Ioo (-(1 / (k + 1 : ℝ))) (1 / (k + 1 : ℝ)) := by
    intro i k
    have hε : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
    exact ae_eventually_spectrum_subset_scalar_smooth i hε (smoothCutoff_spec i hε)
      hC hC' (hM i _ hε) (hWb i _ hε)
  have hall : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      ∀ i : Fin r, ∀ k : ℕ, ∀ᶠ N : ℕ in atTop,
        spectrum ℝ (gueFamily r N x i) ⊆
          spectrum ℝ (semicircularFamily r i) +
            Set.Ioo (-(1 / (k + 1 : ℝ))) (1 / (k + 1 : ℝ)) := by
    have h := ae_all_iff.2 (fun p : Fin r × ℕ => hstep p.1 p.2)
    filter_upwards [h] with x hx
    intro i k
    exact hx (i, k)
  filter_upwards [hall] with x hx
  intro i ε hε
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (1 : ℝ) / (k + 1 : ℝ) < ε := by
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
    refine ⟨n, ?_⟩
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < n + 1)]
    have hn' : (1 : ℝ) < ε * (n + 1) := by
      have h : (1 : ℝ) / ε < n + 1 := by linarith
      rw [div_lt_iff₀ hε] at h
      rw [mul_comm]
      exact h
    linarith
  have hsub : Set.Ioo (-(1 / (k + 1 : ℝ))) (1 / (k + 1 : ℝ)) ⊆ Set.Ioo (-ε) ε := by
    intro y hy
    exact ⟨lt_trans (neg_lt_neg hk) hy.1, lt_trans hy.2 hk⟩
  filter_upwards [hx i k] with N hN
  intro a ha
  have hmem : a ∈ spectrum ℝ (semicircularFamily r i) + Set.Ioo (-ε) ε := by
    have h1 : a ∈ spectrum ℝ (semicircularFamily r i) +
        Set.Ioo (-(1 / (k + 1 : ℝ))) (1 / (k + 1 : ℝ)) := hN ha
    rw [Set.mem_add] at h1 ⊢
    obtain ⟨b, hb, c, hc, hbc⟩ := h1
    exact ⟨b, hb, c, hsub hc, hbc⟩
  exact exists_mem_of_mem_add_Ioo hmem

end

end GUEStrongConvergence
