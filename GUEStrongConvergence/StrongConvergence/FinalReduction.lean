/-
# Final reduction: one weighted-strip bundle for the strong convergence statement

`Probability/LimitFlatten.lean` reduces the analytic input to

`WeightedStripInputs''' r` = (order-`k` weighted-strip data for `1 ≤ k`) ∧ (first-order
mean-comparison data for `k = 0`).

This file performs the last two bookkeeping reductions:

1. **A single `∀ k` weighted-strip field.**  The order-`k` weighted-strip machinery of
   `Probability/LemmaMWeighted.lean` requires order `m ≥ 1` (the order-`k` Cauchy--Pompeiu
   identity needs `1 ≤ m`), while the *polynomial* index `k` is independent of the strip order.
   We decouple the two (`flatLemmaM_of_weightedStrip_order`) and state the data uniformly as

   `WeightedStripDataAtFinal r k F z ε` = the `LimitFlatten` data with the strip order and the
   regularity bumped to `max k 1`.

   For `k ≥ 1` this is *literally* `WeightedStripDataAt'''`; for `k = 0` it is the same data at
   order `1`, which is the honest first-order statement consumed by the mean comparison.  Hence
   the `k = 0` field is no longer a separate conjunct of a different shape: one `∀ k` field
   covers all polynomial indices.

2. **The scalar spectral inclusion from the same weighted-strip machinery.**
   `scalarSpectralInclusion_of_weightedStrip` derives `ScalarSpectralInclusion r` from the
   scalar (`d = 1`) weighted-strip data, by running the weighted mean comparison on the
   `Unit`/one-dimensional scalar pencil `A₀ = 0`, `A_i = 1`; the vanishing of the limit
   statistic comes from `IsSmoothCutoffZeroOn` on the spectrum of the closed pencil, which is
   `spectrum ℝ (semicircularFamily r i)`.

3. **The final theorem with a single hypothesis bundle**
   `GUEStrongConvergenceStatement_of_weightedStripInputsFinal : WeightedStripInputsFinal r →
   GUEStrongConvergenceStatement r`.

No `sorry`, no new axioms.
-/
import GUEStrongConvergence.Probability.LimitFlatten
import GUEStrongConvergence.Probability.LemmaMWeighted
import GUEStrongConvergence.StrongConvergence.ScalarInclusionSmooth

open Filter MeasureTheory ProbabilityTheory FreeProbability FreeProbability.Fock Matrix
open scoped BigOperators ComplexOrder ENNReal Pointwise Topology

namespace GUEStrongConvergence

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

variable {r : ℕ}

local instance finalRedNontrivial : Nontrivial (closedSemicircularAlgebra (Fin r)) :=
  (closedGeneratedVacuumState (Fin r)).toProbabilitySpace.nontrivial

local instance finalRedPartialOrder : PartialOrder (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrder _

local instance finalRedStarOrderedRing : StarOrderedRing (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrderedRing _

/-! ## 1. Decoupling the strip order from the polynomial order

`flatLemmaM_of_weightedStrip` (`Probability/LemmaMWeighted.lean`) ties the *polynomial* index
`k` (the `RatPolyIdx r (k+1)` argument and the `flatStat r k F z` family) to the *strip* order
`k` (the order of the almost-analytic extension, the `ContDiff ℝ (k+1)` regularity and the
exponent bound `β < k`).  For the `k = 0` polynomial data we need strip order `1`, so we restate
the reduction with the two orders separated.  The proof is the one of
`flatLemmaM_of_weightedStrip` with the strip order renamed `m`. -/

/-- **`FlatLemmaM` from a weighted strip bound of independent order `m ≥ 1`.**

`hstat` identifies the flattened statistic at block `N` with the GUE statistic of the
realisation `(A₀, A)` at block `N + 1`, and `hlim0` is the vanishing of the order-`m` limit
statistic.  This is `flatLemmaM_of_weightedStrip` with the polynomial index `k` and the strip
order `m` decoupled. -/
theorem flatLemmaM_of_weightedStrip_order {k : ℕ} {F : RatPolyIdx r (k + 1)} {z : ℝ}
    {g : ℝ → ℝ} {d' : ℕ} [NeZero d'] (A₀ : Matrix (Fin d') (Fin d') ℂ)
    (A : Fin r → Matrix (Fin d') (Fin d') ℂ) (hA₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) {m : ℕ} (hm : 1 ≤ m) {η₀ C_s β : ℝ} (hη₀2 : 2 < η₀)
    (hC_s : 0 ≤ C_s) (hβ0 : 0 ≤ β) (hβm : β < m) (hg : ContDiff ℝ (m + 1) g)
    (hgc : HasCompactSupport g) (hstrip : WeightedStripBound A₀ A m η₀ C_s β)
    (hstat : ∀ N : ℕ,
      ∫ x, flatStat r k F z N g x ∂(commonGaussianMeasure (Fin r))
        = ∫ y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)),
            gueStatisticCfc (N := N + 1) g A₀ A hA₀ hA y
              ∂(stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))))
    (hlim0 : guePlaneLimitOrder m A₀ A g = 0)
    (hIntN : ∀ᶠ N : ℕ in atTop, Integrable (fun p : ℝ × ℝ =>
      dbarNumOrder (m + 1) g (zOf p) *
        Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p))))
    (hIntLim : Integrable (fun p : ℝ × ℝ => dbarNumOrder (m + 1) g (zOf p) *
      Matrix.trace (operatorMatrixPencilCauchy A₀ A (zOf p)))) :
    FlatLemmaM r k F z g (weightedStripConstant g m C_s β) := by
  have hmain : ∀ᶠ N : ℕ in atTop,
      |∫ y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)),
          gueStatisticCfc (N := N + 1) g A₀ A hA₀ hA y
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1))))|
        ≤ weightedStripConstant g m C_s β / ((N + 1 : ℕ) : ℝ) ^ 2 := by
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hstrip
    obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 hIntN
    refine eventually_atTop.2 ⟨max N₀ M₀, fun n hn => ?_⟩
    have hn₀ : N₀ ≤ n + 1 := le_trans (le_max_left N₀ M₀) (by omega)
    have hm₀ : M₀ ≤ n + 1 := le_trans (le_max_right N₀ M₀) (by omega)
    have hfixed := abs_integral_gueStatisticCfc_le_of_weighted_strip (N := n + 1) A₀ A hA₀ hA
      (by omega) hm hg (K := m + 1) le_rfl hgc hη₀2 hC_s hβ0 hβm
      (fun w hw hlt => hN₀ (n + 1) hn₀ w hw hlt) (hM₀ (n + 1) hm₀) hIntLim hlim0
    simpa [weightedStripConstant] using hfixed
  filter_upwards [hmain, eventually_ge_atTop (1 : ℕ)] with N hN hN1
  rw [hstat N]
  refine hN.trans ?_
  have hC0 : 0 ≤ weightedStripConstant g m C_s β := weightedStripConstant_nonneg (f := g) hC_s
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hsq : (N : ℝ) ^ 2 ≤ ((N : ℝ) + 1) ^ 2 := by nlinarith
  push_cast
  exact div_le_div_of_nonneg_left hC0 (by positivity) hsq

/-! ## 2. The uniform weighted-strip data

For `k ≥ 1` the strip order is `k` and the data is exactly `WeightedStripDataAt'''`; for
`k = 0` the strip order is `1` (the smallest order for which the weighted mean comparison is
available).  Both are instances of the single definition below. -/

/-- **The weighted-strip data at one pencil, uniform in the polynomial index.**

The strip order and the regularity are `max k 1`: for `k ≥ 1` this is the original order `k`,
while for `k = 0` it is the first order at which `smooth_trace_comparison_of_weighted_strip`
applies. -/
def WeightedStripDataAtFinal (r k : ℕ) (F : RatPolyIdx r (k + 1)) (z ε : ℝ) : Prop :=
  letI : Nonempty (Fin (pencilCoeffDim k F)) :=
    ⟨⟨0, pencilCoeffDim_pos r k F⟩⟩
  ∃ (η₀ C_s β : ℝ) (hη₀2 : 2 < η₀) (hC_s : 0 ≤ C_s) (hβ0 : 0 ≤ β)
    (hβm : β < max k 1) (f : ℝ → ℝ) (C' : ℝ),
    IsSmoothCutoffZeroOn (specC (h1PencilLimit r k F z)) ε f ∧
    ContDiff ℝ (max k 1 + 1) f ∧
    ContDiff ℝ (max k 1 + 1) (fun y => (deriv f y) ^ 2) ∧
    HasCompactSupport f ∧
    WeightedStripBound (pencilConstCoeff k F z) (pencilDirCoeff k F) (max k 1) η₀ C_s β ∧
    0 ≤ C'

/-- For `k ≥ 1` the uniform data is literally `WeightedStripDataAt'''`. -/
theorem weightedStripDataAtFinal_iff {k : ℕ} (hk : 1 ≤ k) {F : RatPolyIdx r (k + 1)}
    {z ε : ℝ} :
    WeightedStripDataAtFinal r k F z ε ↔ WeightedStripDataAt''' r k F z ε := by
  unfold WeightedStripDataAtFinal WeightedStripDataAt'''
  rw [Nat.max_eq_left hk]

/-- **The uniform weighted-strip data gives the mean comparisons.**  This is
`WeightedMeanInputs_of_weightedStripInputs'''` with the single uniform `∀ k` field: both `k = 0`
and `k ≥ 1` go through `flatLemmaM_of_weightedStrip_order` at strip order `max k 1`. -/
theorem WeightedMeanInputs_of_weightedStripDataAtFinal
    (h : ∀ (k : ℕ) (F : RatPolyIdx r (k + 1)) (z ε : ℝ), 0 < ε →
      WeightedStripDataAtFinal r k F z ε) :
    WeightedMeanInputs r := by
  intro k F z ε hε
  obtain ⟨η₀, C_s, β, hη₀2, hC_s, hβ0, hβm, f, C', hcut, hreg, hregw, hfc, hstrip, hC'⟩ :=
    h k F z ε hε
  haveI hne : NeZero (pencilCoeffDim k F) :=
    ⟨Nat.ne_of_gt (pencilCoeffDim_pos r k F)⟩
  haveI hne' : Nonempty (Fin (pencilCoeffDim k F)) :=
    ⟨⟨0, pencilCoeffDim_pos r k F⟩⟩
  have hm : 1 ≤ max k 1 := le_max_right _ _
  have hA₀ := pencilConstCoeff_isHermitian k F z
  have hA := pencilDirCoeff_isHermitian k F
  set C₀ : Matrix (Fin (pencilCoeffDim k F)) (Fin (pencilCoeffDim k F)) ℂ :=
    pencilConstCoeff k F z with hC₀def
  set C : Fin r → Matrix (Fin (pencilCoeffDim k F)) (Fin (pencilCoeffDim k F)) ℂ :=
    pencilDirCoeff k F with hCdef
  have hsp : spectrum ℝ (closedPencil (n := Fin (pencilCoeffDim k F)) C₀ C) =
      specC (h1PencilLimit r k F z) :=
    (specC_eq_spectrum_closedPencil r k F z).symm
  have hres : ∀ z' : ℂ, z'.im ≠ 0 →
      Matrix.trace (operatorMatrixPencilCauchy C₀ C z') =
        blockLimitResolventTrace (closedPencil (n := Fin (pencilCoeffDim k F)) C₀ C) z' :=
    fun z' hz' =>
      trace_operatorMatrixPencilCauchy_eq_blockLimitResolventTrace_gen
        (pencilCoeffDim k F) C₀ C hA₀ hA hz'
  have hhh : IsSelfAdjoint (closedPencil (n := Fin (pencilCoeffDim k F)) C₀ C) :=
    closedPencil_isSelfAdjoint C₀ C hA₀ hA
  have hzerof : ∀ x ∈ spectrum ℝ (closedPencil (n := Fin (pencilCoeffDim k F)) C₀ C),
      f x = 0 := by
    intro x hx
    rw [hsp] at hx
    exact hcut.eq_zero x hx
  have hzerow : ∀ x ∈ spectrum ℝ (closedPencil (n := Fin (pencilCoeffDim k F)) C₀ C),
      (deriv f x) ^ 2 = 0 := by
    intro x hx
    rw [hsp] at hx
    rw [hcut.deriv_eq_zero x hx]
    ring
  refine ⟨f, weightedStripConstant f (max k 1) C_s β,
    weightedStripConstant (fun y => (deriv f y) ^ 2) (max k 1) C_s β,
    ?_, ?_, ?_, weightedStripConstant_nonneg hC_s,
    weightedStripConstant_nonneg hC_s⟩
  · exact hcut
  · refine flatLemmaM_of_weightedStrip_order (m := max k 1) C₀ C hA₀ hA hm
      hη₀2 hC_s hβ0 hβm hreg hfc hstrip
      (fun N => flatGUEStatisticEqCont_canonical k F z N f hreg.continuous)
      (guePlaneLimitOrder_eq_zero_of_eq_zero_on_spectrum hm hhh hres hreg le_rfl hfc hzerof)
      (eventually_integrable_dbarNumOrder_mul_trace_gueResolventMean C₀ C hA₀ hA hm
        hreg le_rfl hfc)
      (integrable_dbarNumOrder_mul_trace_operatorMatrixPencilCauchy_of_eq
        (closedPencil (n := Fin (pencilCoeffDim k F)) C₀ C) hhh hres hm hreg le_rfl hfc)
  · refine flatLemmaM_of_weightedStrip_order (m := max k 1) C₀ C hA₀ hA hm
      hη₀2 hC_s hβ0 hβm hregw hcut.smooth.compactSupport hstrip
      (fun N => flatGUEStatisticEqCont_canonical k F z N
        (fun y => (deriv f y) ^ 2) hregw.continuous)
      (guePlaneLimitOrder_eq_zero_of_eq_zero_on_spectrum hm hhh hres hregw le_rfl
        hcut.smooth.compactSupport hzerow)
      (eventually_integrable_dbarNumOrder_mul_trace_gueResolventMean C₀ C hA₀ hA hm
        hregw le_rfl hcut.smooth.compactSupport)
      (integrable_dbarNumOrder_mul_trace_operatorMatrixPencilCauchy_of_eq
        (closedPencil (n := Fin (pencilCoeffDim k F)) C₀ C) hhh hres hm hregw le_rfl
        hcut.smooth.compactSupport)


/-! ## 3. The scalar pencil at `d = 1` -/

/-- The index identification `Fin 1 × Fin N ≃ Fin N`. -/
def finOneProdFinEquiv (N : ℕ) : Fin 1 × Fin N ≃ Fin N where
  toFun p := p.2
  invFun a := (0, a)
  left_inv p := by
    obtain ⟨u, a⟩ := p
    refine Prod.ext ?_ rfl
    exact Subsingleton.elim _ _
  right_inv _ := rfl

/-- The coefficient matrices of the one-dimensional scalar pencil: `A i = 1`, `A j = 0` for
`j ≠ i`.  This is the `d = 1` version of `scalarCoeff`
(`StrongConvergence/ScalarInclusionSmooth.lean`): the pencil then lives in `BlockLimit r 1`,
which is the shape required by the limit-side vanishing lemma. -/
def scalarPencilCoeff {r : ℕ} (i : Fin r) : Fin r → Matrix (Fin 1) (Fin 1) ℂ :=
  fun j => if j = i then 1 else 0

lemma scalarPencilCoeff_isHermitian {r : ℕ} (i : Fin r) :
    ∀ j, (scalarPencilCoeff i j).IsHermitian := by
  intro j
  by_cases h : j = i
  · rw [scalarPencilCoeff]
    simp only [h, ↓reduceIte]
    exact isHermitian_one
  · rw [scalarPencilCoeff]
    simp only [h, ↓reduceIte]
    exact isHermitian_zero

/-- The one-dimensional pencil is the individual GUE matrix up to the block reindexing. -/
lemma guePencilMatrix_scalarPencilCoeff {r N : ℕ} (i : Fin r)
    (y : GUECoord (Fin r) N → ℝ) :
    guePencilMatrix (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) y =
      Matrix.reindex (finOneProdFinEquiv N).symm (finOneProdFinEquiv N).symm (gueMatrix y i) := by
  ext ⟨u, a⟩ ⟨v, b⟩
  fin_cases u
  fin_cases v
  rw [guePencilMatrix_apply, Matrix.reindex_apply]
  simp only [Matrix.zero_apply, zero_mul, zero_add, Equiv.symm_symm, finOneProdFinEquiv,
    Equiv.coe_fn_mk]
  rw [Finset.sum_eq_single i]
  · simp [scalarPencilCoeff]
  · intro j _ hji
    simp [scalarPencilCoeff, hji]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- **The pencil statistic of the one-dimensional scalar pencil is the scalar normalized
trace.** -/
lemma gueStatisticCfc_scalarPencilCoeff_eq {N : ℕ} (f : ℝ → ℝ) (i : Fin r)
    (x : EuclideanSpace ℝ (GUECoord (Fin r) N))
    (hA₀ : (0 : Matrix (Fin 1) (Fin 1) ℂ).IsHermitian)
    (hA : ∀ j, (scalarPencilCoeff i j).IsHermitian) :
    gueStatisticCfc (N := N) (ι := Fin r) (d := Fin 1) f
        (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) hA₀ hA x =
      normTrace (hermCfc (gueMatrix (WithLp.ofLp x) i) f
        (gueMatrix_isHermitian (WithLp.ofLp x) i)) := by
  simp only [gueStatisticCfc, guePencilCfc_eq_cfc, guePencilMatrix_scalarPencilCoeff,
    cfc_reindex, guePencilNormTrace, gueNormConst, normTrace, hermCfc, trace_reindex,
    Fintype.card_fin, one_mul]

/-- The same identification on the common space. -/
lemma gueStatisticCfc_scalarPencilCoeff_eq_commonSpace {N : ℕ} (f : ℝ → ℝ) (i : Fin r)
    (x : CommonSpace (Fin r)) (hA₀ : (0 : Matrix (Fin 1) (Fin 1) ℂ).IsHermitian)
    (hA : ∀ j, (scalarPencilCoeff i j).IsHermitian) :
    gueStatisticCfc (N := N) (ι := Fin r) (d := Fin 1) f
        (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) hA₀ hA (x N) =
      normTrace (hermCfc (gueMatrixOn x N i) f (gueMatrixOn_isHermitian x N i)) := by
  simpa [gueMatrixOn] using
    gueStatisticCfc_scalarPencilCoeff_eq (f := f) (i := i) (x := x N) hA₀ hA

/-- `MemLp 2` of the one-dimensional pencil statistic, from a bound on the test function. -/
lemma memLp_gueStatisticCfc_scalarPencilCoeff {N : ℕ} {f : ℝ → ℝ} (hf : Continuous f)
    {C : ℝ} (hC : ∀ y, |f y| ≤ C) (hC0 : 0 ≤ C) (i : Fin r)
    (h0 : (0 : Matrix (Fin 1) (Fin 1) ℂ).IsHermitian)
    (hA : ∀ j, (scalarPencilCoeff i j).IsHermitian) :
    MemLp (gueStatisticCfc (N := N) (ι := Fin r) (d := Fin 1) f 0 (scalarPencilCoeff i) h0 hA) 2
      (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) N))) := by
  rw [funext fun y => gueStatisticCfc_scalarPencilCoeff_eq f i y h0 hA]
  exact memLp_normTrace_cfc (μ := stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) N)))
    (M := fun y : EuclideanSpace ℝ (GUECoord (Fin r) N) => gueMatrix y i)
    (hM := fun a b => measurable_gueMatrix_entry_euclid N i a b)
    (hHerm := fun y => gueMatrix_isHermitian y i) hf hC hC0

/-- The common-space integral of the scalar statistic is the block integral of the
one-dimensional pencil statistic. -/
lemma integral_commonSpace_scalarPencilStat_eq {N : ℕ} (i : Fin r) (f : ℝ → ℝ)
    (h0 : (0 : Matrix (Fin 1) (Fin 1) ℂ).IsHermitian)
    (hA : ∀ j, (scalarPencilCoeff i j).IsHermitian)
    (hB : AEStronglyMeasurable
      (fun y : EuclideanSpace ℝ (GUECoord (Fin r) N) =>
        gueStatisticCfc (N := N) (ι := Fin r) (d := Fin 1) f 0 (scalarPencilCoeff i) h0 hA y)
      (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) N)))) :
    ∫ x : CommonSpace (Fin r),
        normTrace (hermCfc (gueFamily r N x i) f (gueMatrixOn_isHermitian x N i))
        ∂(commonGaussianMeasure (Fin r))
      = ∫ y : EuclideanSpace ℝ (GUECoord (Fin r) N),
          gueStatisticCfc (N := N) (ι := Fin r) (d := Fin 1) f 0 (scalarPencilCoeff i) h0 hA y
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) N))) := by
  rw [← integral_eval_commonGaussian (ι := Fin r) (N := N) hB]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  exact (gueStatisticCfc_scalarPencilCoeff_eq_commonSpace f i x h0 hA).symm

/-! ## 4. The `1 × 1` matrix algebra and the closed scalar pencil -/

/-- The `1 × 1` matrix algebra over an `ℝ`-algebra is the algebra itself, as a star algebra
equivalence. -/
def matrixFinOneStarAlgEquiv (A : Type*) [Ring A] [StarRing A] [Algebra ℝ A] :
    Matrix (Fin 1) (Fin 1) A ≃⋆ₐ[ℝ] A :=
  StarAlgEquiv.ofAlgEquiv
    { toFun := fun M => M 0 0
      invFun := fun a => Matrix.of fun _ _ => a
      left_inv := by
        intro M
        ext i j
        fin_cases i
        fin_cases j
        rfl
      right_inv := by
        intro a
        rfl
      map_mul' := by
        intro M N
        simp only [Matrix.mul_apply, Fin.sum_univ_one]
      map_add' := by
        intro M N
        rfl
      commutes' := by
        intro c
        simp [Matrix.algebraMap_eq_diagonal] }
    (by
      intro M
      change Mᴴ 0 0 = star (M 0 0)
      exact Matrix.conjTranspose_apply M 0 0)

/-- The real spectrum of a `1 × 1` matrix is the spectrum of its entry. -/
lemma spectrum_cstarMatrix_finOne {A : Type*} [Ring A] [StarRing A] [Algebra ℝ A]
    (M : CStarMatrix (Fin 1) (Fin 1) A) :
    spectrum ℝ M = spectrum ℝ (M 0 0) := by
  have h1 := AlgEquiv.spectrum_eq (matrixFinOneStarAlgEquiv A)
    (show Matrix (Fin 1) (Fin 1) A from M)
  have h2 : (matrixFinOneStarAlgEquiv A) (show Matrix (Fin 1) (Fin 1) A from M)
      = M 0 0 := rfl
  rw [h2] at h1
  exact h1.symm

/-- The closed pencil of the one-dimensional scalar pencil is the `i`-th semicircular
element. -/
lemma closedPencil_scalarPencilCoeff (i : Fin r) :
    closedPencil (n := Fin 1) (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) =
      CStarMatrix.ofMatrix (fun _ _ : Fin 1 => semicircularFamily r i) := by
  refine CStarMatrix.ext fun a b => ?_
  fin_cases a
  fin_cases b
  rw [closedPencil_apply]
  rw [Finset.sum_eq_single i]
  · simp [scalarPencilCoeff]
  · intro j _ hji
    simp [scalarPencilCoeff, hji]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- **The spectrum of the closed one-dimensional scalar pencil** is the spectrum of the `i`-th
semicircular element. -/
lemma spectrum_closedPencil_scalarPencilCoeff (i : Fin r) :
    spectrum ℝ (closedPencil (n := Fin 1) (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i))
      = spectrum ℝ (semicircularFamily r i) := by
  rw [closedPencil_scalarPencilCoeff, spectrum_cstarMatrix_finOne]
  simp

/-! ## 5. The scalar weighted-strip data and the scalar spectral inclusion -/

/-- **The scalar weighted-strip data.**  At the one-dimensional pencil `A₀ = 0`,
`A = scalarPencilCoeff i`, at strip order `1`: a strengthened smooth cutoff on the spectrum of
the `i`-th semicircular element, the regularity needed to run the order-`1` mean comparison on
`f` and `(f')²`, and the weighted resolvent-strip estimate itself. -/
def ScalarWeightedStripDataAt (r : ℕ) (i : Fin r) (ε : ℝ) : Prop :=
  letI : Nonempty (Fin 1) := ⟨⟨0, by norm_num⟩⟩
  ∃ (η₀ C_s β : ℝ) (hη₀2 : 2 < η₀) (hC_s : 0 ≤ C_s) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (f : ℝ → ℝ) (C' : ℝ),
    IsSmoothCutoffZeroOn (spectrum ℝ (semicircularFamily r i)) ε f ∧
    ContDiff ℝ 2 f ∧
    ContDiff ℝ 2 (fun y => (deriv f y) ^ 2) ∧
    HasCompactSupport f ∧
    WeightedStripBound (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) 1 η₀ C_s β ∧
    0 ≤ C'

/-- **Scalar spectral inclusion with a smooth cutoff and an eventual `(W)` bound.**  This is
`ae_eventually_spectrum_subset_scalar_smooth` with the `(W)` bound in the eventual form
produced by `eventually_abs_integral_gueStatisticCfc_le_of_weighted_strip`.  The variance input
is still discharged from the unconditional smooth Lemma V. -/
theorem ae_eventually_spectrum_subset_scalar_smooth_eventual {r : ℕ} (i : Fin r) {ε : ℝ}
    (hε : 0 < ε) {f : ℝ → ℝ}
    (hf : IsSmoothCutoff (spectrum ℝ (semicircularFamily r i)) ε f)
    {C C' : ℝ} (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (hM : ∀ᶠ N : ℕ in atTop,
      |∫ x, normTrace (hermCfc (gueFamily r N x i) f (gueMatrixOn_isHermitian x N i))
        ∂(commonGaussianMeasure (Fin r))| ≤ C / (N : ℝ) ^ 2)
    (hWb : ∀ᶠ N : ℕ in atTop,
      ∫ x, normTrace (hermCfc (gueFamily r N x i) (fun y => (deriv f y) ^ 2)
        (gueMatrixOn_isHermitian x N i)) ∂(commonGaussianMeasure (Fin r))
        ≤ C' / (N : ℝ) ^ 2) :
    ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ᶠ N : ℕ in atTop,
      spectrum ℝ (gueFamily r N x i) ⊆
        spectrum ℝ (semicircularFamily r i) + Set.Ioo (-ε) ε := by
  have hCmax : (0 : ℝ) ≤ max C 2 := le_max_iff.mpr (Or.inr (by norm_num))
  have hM' : ∀ᶠ N : ℕ in atTop,
      |∫ x, normTrace (hermCfc (gueFamily r N x i) f (gueMatrixOn_isHermitian x N i))
        ∂(commonGaussianMeasure (Fin r))| ≤ max C 2 / (N : ℝ) ^ 2 := by
    filter_upwards [hM] with N hN
    refine hN.trans ?_
    gcongr
    exact le_max_left _ _
  have hV : ∀ᶠ N : ℕ in atTop,
      variance (fun x => normTrace (hermCfc (gueFamily r N x i) f
        (gueMatrixOn_isHermitian x N i))) (commonGaussianMeasure (Fin r))
      ≤ max C 2 / (N : ℝ) ^ 2 * ∫ x, normTrace (hermCfc (gueFamily r N x i)
          (fun y => (deriv f y) ^ 2) (gueMatrixOn_isHermitian x N i))
          ∂(commonGaussianMeasure (Fin r)) := by
    filter_upwards with N
    refine (variance_scalarStatistic_le_two i hf N).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ ?_
    · gcongr
      exact le_max_right _ _
    · exact integral_normTrace_cfc_nonneg (μ := commonGaussianMeasure (Fin r))
        (M := fun x => gueMatrixOn x N i)
        (hM := fun a b => measurable_gueMatrixOn_entry N i a b)
        (hHerm := fun x => gueMatrixOn_isHermitian x N i)
        (fun y => sq_nonneg (deriv f y))
  obtain ⟨M, hM0, hMbound⟩ := hf.exists_deriv_bound
  have hderiv_cont : Continuous (fun y : ℝ => (deriv f y) ^ 2) :=
    hf.contDiff.continuous_deriv_one.pow 2
  refine ae_eventually_spectrum_subset_growing (m := fun N => N)
    (hm := (eventually_ge_atTop (1 : ℕ)).mono fun N hN =>
      Nat.lt_of_lt_of_le Nat.zero_lt_one hN)
    (hε := hε) (hf0 := hf.nonneg) (hf1 := hf.eq_one)
    (H := fun N x => gueFamily r N x i) (hH := fun N x => gueMatrixOn_isHermitian x N i)
    (C := max C 2) (C' := C') (D := 1) hCmax hC' zero_le_one
    (by filter_upwards with N; simp) ?_ ?_ ?_ hM' hV hWb
  · intro N
    exact memLp_normTrace_cfc (μ := commonGaussianMeasure (Fin r))
      (M := fun x => gueMatrixOn x N i)
      (hM := fun a b => measurable_gueMatrixOn_entry N i a b)
      (hHerm := fun x => gueMatrixOn_isHermitian x N i) hf.contDiff.continuous
      (fun y => hf.abs_le_one y) zero_le_one
  · intro N
    exact integrable_normTrace_cfc (μ := commonGaussianMeasure (Fin r))
      (M := fun x => gueMatrixOn x N i)
      (hM := fun a b => measurable_gueMatrixOn_entry N i a b)
      (hHerm := fun x => gueMatrixOn_isHermitian x N i) hderiv_cont
      (fun y => by
        rw [abs_of_nonneg (sq_nonneg (deriv f y))]
        calc (deriv f y) ^ 2 = |deriv f y| ^ 2 := by rw [sq_abs]
          _ ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hMbound y) 2)
      (sq_nonneg M)
  · intro N
    exact integral_normTrace_cfc_nonneg (μ := commonGaussianMeasure (Fin r))
      (M := fun x => gueMatrixOn x N i)
      (hM := fun a b => measurable_gueMatrixOn_entry N i a b)
      (hHerm := fun x => gueMatrixOn_isHermitian x N i) (fun y => sq_nonneg (deriv f y))

/-- **`ScalarSpectralInclusion r` from the scalar weighted-strip data.**

The scalar GUE matrix is the one-dimensional pencil `A₀ = 0`, `A_i = 1`; the weighted mean
comparison at strip order `1` (`abs_integral_gueStatisticCfc_le_of_weighted_strip`) gives the
mean bound for `f` and for `(f')²`.  The limit statistic vanishes because the closed pencil of
that scalar pencil is the `i`-th semicircular element and `f`, `f'` vanish on its spectrum
(`IsSmoothCutoffZeroOn`).  The variance input is discharged by the unconditional smooth
Lemma V (`variance_scalarStatistic_le_two`). -/
theorem scalarSpectralInclusion_of_weightedStrip
    (h : ∀ (i : Fin r) (ε : ℝ), 0 < ε → ScalarWeightedStripDataAt r i ε) :
    ScalarSpectralInclusion r := by
  classical
  have hstep : ∀ (i : Fin r) (k : ℕ),
      ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ᶠ N : ℕ in atTop,
        spectrum ℝ (gueFamily r N x i) ⊆
          spectrum ℝ (semicircularFamily r i) +
            Set.Ioo (-(1 / (k + 1 : ℝ))) (1 / (k + 1 : ℝ)) := by
    intro i k
    have hε : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
    haveI hne1 : Nonempty (Fin 1) := ⟨⟨0, by norm_num⟩⟩
    obtain ⟨η₀, C_s, β, hη₀2, hC_s, hβ0, hβ1, f, C', hcut, hreg, hregw, hfc, hstrip, hC'⟩ :=
      h i _ hε
    have hsa : IsSelfAdjoint
        (closedPencil (n := Fin 1) (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i)) :=
      closedPencil_isSelfAdjoint _ _ isHermitian_zero (scalarPencilCoeff_isHermitian i)
    have hres : ∀ z : ℂ, z.im ≠ 0 →
        Matrix.trace (operatorMatrixPencilCauchy (0 : Matrix (Fin 1) (Fin 1) ℂ)
          (scalarPencilCoeff i) z) =
          blockLimitResolventTrace
            (closedPencil (n := Fin 1) (0 : Matrix (Fin 1) (Fin 1) ℂ)
              (scalarPencilCoeff i)) z :=
      fun z hz =>
        trace_operatorMatrixPencilCauchy_eq_blockLimitResolventTrace_gen 1
          (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) isHermitian_zero
          (scalarPencilCoeff_isHermitian i) hz
    have hspec : spectrum ℝ
        (closedPencil (n := Fin 1) (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i)) =
        spectrum ℝ (semicircularFamily r i) := spectrum_closedPencil_scalarPencilCoeff i
    have hlim0f : guePlaneLimitOrder 1 (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) f
        = 0 := by
      refine guePlaneLimitOrder_eq_zero_of_eq_zero_on_spectrum (k := 1) (K := 2) le_rfl
        hsa hres hreg le_rfl hfc ?_
      intro x hx
      rw [hspec] at hx
      exact hcut.eq_zero x hx
    have hlim0w : guePlaneLimitOrder 1 (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i)
        (fun y => (deriv f y) ^ 2) = 0 := by
      refine guePlaneLimitOrder_eq_zero_of_eq_zero_on_spectrum (k := 1) (K := 2) le_rfl
        hsa hres hregw le_rfl hcut.smooth.compactSupport ?_
      intro x hx
      rw [hspec] at hx
      rw [hcut.deriv_eq_zero x hx]
      ring
    have hMe : ∀ᶠ N : ℕ in atTop,
        |∫ y : EuclideanSpace ℝ (GUECoord (Fin r) N),
          gueStatisticCfc (N := N) (ι := Fin r) (d := Fin 1) f
            (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) isHermitian_zero
            (scalarPencilCoeff_isHermitian i) y
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) N)))| ≤
          weightedStripConstant f 1 C_s β / (N : ℝ) ^ 2 :=
      eventually_abs_integral_gueStatisticCfc_le_of_weighted_strip
        (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) isHermitian_zero
        (scalarPencilCoeff_isHermitian i) (k := 1) (K := 2) le_rfl hreg le_rfl hfc
        hη₀2 hC_s hβ0 (by simpa using hβ1) hstrip
        (eventually_integrable_dbarNumOrder_mul_trace_gueResolventMean
          (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) isHermitian_zero
          (scalarPencilCoeff_isHermitian i) le_rfl hreg le_rfl hfc)
        (integrable_dbarNumOrder_mul_trace_operatorMatrixPencilCauchy_of_eq _ hsa hres
          le_rfl hreg le_rfl hfc)
        hlim0f
    have hWe : ∀ᶠ N : ℕ in atTop,
        |∫ y : EuclideanSpace ℝ (GUECoord (Fin r) N),
          gueStatisticCfc (N := N) (ι := Fin r) (d := Fin 1) (fun y => (deriv f y) ^ 2)
            (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) isHermitian_zero
            (scalarPencilCoeff_isHermitian i) y
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) N)))| ≤
          weightedStripConstant (fun y => (deriv f y) ^ 2) 1 C_s β / (N : ℝ) ^ 2 :=
      eventually_abs_integral_gueStatisticCfc_le_of_weighted_strip
        (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) isHermitian_zero
        (scalarPencilCoeff_isHermitian i) (k := 1) (K := 2) le_rfl hregw le_rfl
        hcut.smooth.compactSupport hη₀2 hC_s hβ0 (by simpa using hβ1) hstrip
        (eventually_integrable_dbarNumOrder_mul_trace_gueResolventMean
          (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) isHermitian_zero
          (scalarPencilCoeff_isHermitian i) le_rfl hregw le_rfl hcut.smooth.compactSupport)
        (integrable_dbarNumOrder_mul_trace_operatorMatrixPencilCauchy_of_eq _ hsa hres
          le_rfl hregw le_rfl hcut.smooth.compactSupport)
        hlim0w
    have hMe' : ∀ᶠ N : ℕ in atTop,
        |∫ x : CommonSpace (Fin r),
          normTrace (hermCfc (gueFamily r N x i) f (gueMatrixOn_isHermitian x N i))
          ∂(commonGaussianMeasure (Fin r))| ≤
          weightedStripConstant f 1 C_s β / (N : ℝ) ^ 2 := by
      filter_upwards [hMe] with N hN
      have hB : AEStronglyMeasurable
          (fun y : EuclideanSpace ℝ (GUECoord (Fin r) N) =>
            gueStatisticCfc (N := N) (ι := Fin r) (d := Fin 1) f
              (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) isHermitian_zero
              (scalarPencilCoeff_isHermitian i) y)
          (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) N))) :=
        (memLp_gueStatisticCfc_scalarPencilCoeff hreg.continuous
          (fun y => hcut.smooth.abs_le_one y) zero_le_one i isHermitian_zero
          (scalarPencilCoeff_isHermitian i)).aestronglyMeasurable
      rw [integral_commonSpace_scalarPencilStat_eq i f isHermitian_zero
        (scalarPencilCoeff_isHermitian i) hB]
      exact hN
    have hWe' : ∀ᶠ N : ℕ in atTop,
        ∫ x : CommonSpace (Fin r),
          normTrace (hermCfc (gueFamily r N x i) (fun y => (deriv f y) ^ 2)
            (gueMatrixOn_isHermitian x N i)) ∂(commonGaussianMeasure (Fin r)) ≤
          weightedStripConstant (fun y => (deriv f y) ^ 2) 1 C_s β / (N : ℝ) ^ 2 := by
      filter_upwards [hWe] with N hN
      have hB : AEStronglyMeasurable
          (fun y : EuclideanSpace ℝ (GUECoord (Fin r) N) =>
            gueStatisticCfc (N := N) (ι := Fin r) (d := Fin 1) (fun y => (deriv f y) ^ 2)
              (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) isHermitian_zero
              (scalarPencilCoeff_isHermitian i) y)
          (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) N))) := by
        obtain ⟨M, hM0, hMbound⟩ := hcut.smooth.exists_deriv_bound
        have hbound : ∀ y : ℝ, |(deriv f y) ^ 2| ≤ M ^ 2 := fun y => by
          rw [abs_of_nonneg (sq_nonneg (deriv f y))]
          calc (deriv f y) ^ 2 = |deriv f y| ^ 2 := by rw [sq_abs]
            _ ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hMbound y) 2
        exact (memLp_gueStatisticCfc_scalarPencilCoeff hregw.continuous hbound
          (sq_nonneg M) i isHermitian_zero (scalarPencilCoeff_isHermitian i)).aestronglyMeasurable
      rw [integral_commonSpace_scalarPencilStat_eq i (fun y => (deriv f y) ^ 2)
        isHermitian_zero (scalarPencilCoeff_isHermitian i) hB]
      exact le_trans (le_abs_self _) hN
    exact ae_eventually_spectrum_subset_scalar_smooth_eventual i hε hcut.smooth
      (weightedStripConstant_nonneg hC_s) (weightedStripConstant_nonneg hC_s) hMe' hWe'
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

/-! ## 6. The single final bundle -/

/-- **The final weighted-strip input bundle.**  A single `Prop` with two fields:

* `pencil`: the uniform weighted-strip data at *every* polynomial index `k` (strip order
  `max k 1`) — this is one `∀ k` statement, with no separate `k = 0` conjunct; for `k ≥ 1`
  each instance is literally `WeightedStripDataAt'''`;
* `scalar`: the scalar (`d = 1`) weighted-strip data for the individual GUE generators.  This
  field is genuinely separate: the scalar pencil has coefficient dimension `1`, while the
  linearization pencils of the `pencil` field have coefficient dimension
  `pencilCoeffDim k F ≥ 2`, so the scalar data is not an instance of the same `RatPolyIdx`
  family. -/
def WeightedStripInputsFinal (r : ℕ) : Prop :=
  (∀ (k : ℕ) (F : RatPolyIdx r (k + 1)) (z ε : ℝ), 0 < ε →
    WeightedStripDataAtFinal r k F z ε) ∧
  (∀ (i : Fin r) (ε : ℝ), 0 < ε → ScalarWeightedStripDataAt r i ε)

/-- **The pencil part of the final bundle implies the previous reduced bundle.**  The `k = 0`
instance is the order-`1` data, and its `FlatLemmaM` consequence is *derived* by
`flatLemmaM_of_weightedStrip_order`, so `WeightedStripInputs'''` follows.  Hence the uniform
bundle loses no strength relative to `WeightedStripInputs'''`. -/
theorem WeightedStripInputs'''_of_weightedStripDataAtFinal
    (h : ∀ (k : ℕ) (F : RatPolyIdx r (k + 1)) (z ε : ℝ), 0 < ε →
      WeightedStripDataAtFinal r k F z ε) :
    WeightedStripInputs''' r := by
  refine ⟨fun k F z ε hk hε => (weightedStripDataAtFinal_iff hk).mp (h k F z ε hε), ?_⟩
  intro F z ε hε
  exact WeightedMeanInputs_of_weightedStripDataAtFinal h 0 F z ε hε

/-- **The project target from the single final weighted-strip bundle.**

The scalar spectral inclusion is derived from the scalar weighted-strip field
(`scalarSpectralInclusion_of_weightedStrip`) and the pencil mean comparisons from the uniform
pencil field (`WeightedMeanInputs_of_weightedStripDataAtFinal`); the two are combined by the
already verified reduction `GUEStrongConvergenceStatement_of_weightedMeanInputs`. -/
theorem GUEStrongConvergenceStatement_of_weightedStripInputsFinal
    (h : WeightedStripInputsFinal r) : GUEStrongConvergenceStatement r :=
  GUEStrongConvergenceStatement_of_weightedMeanInputs
    (scalarSpectralInclusion_of_weightedStrip h.2)
    (WeightedMeanInputs_of_weightedStripDataAtFinal h.1)

end

end GUEStrongConvergence
