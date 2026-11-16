/-
# Deterministic limit-side identifications for the weighted-strip chain

`flatLemmaM_of_weightedStrip` (`Probability/LemmaMWeighted.lean`) and its order-decoupled form
`flatLemmaM_of_weightedStrip_order` carry four *deterministic* hypotheses besides the weighted
strip bound:

* `hstat`  — the flat ⟶ GUE identification of the two statistics;
* `hlim0`  — vanishing of the order-`k` plane limit statistic on the limit spectrum;
* `hIntN`  — plane integrability of `∂̄_k f · Tr(g_N)`;
* `hIntLim`— plane integrability of `∂̄_k f · Tr(g)`.

This file closes the three that are pure bookkeeping, from the definitions:

* `trace_operatorMatrixPencilCauchy_eq_blockLimitResolventTrace_fin` — the closed-pencil bridge
  `Tr(operatorMatrixPencilCauchy A₀ A z) = blockLimitResolventTrace (closedPencil A₀ A) z` at an
  **arbitrary** square size `Fin n` (the version in `Probability/LimitBridge.lean` is restricted
  to `Fin (d'+1)`; the restriction was only geometric bookkeeping);
* `guePlaneLimitOrder_eq_zero_of_isSmoothCutoffZeroOn` — `hlim0` from the *cutoff* property
  `IsSmoothCutoffZeroOn S ε g` together with the spectral inclusion
  `spectrum ℝ (closedPencil A₀ A) ⊆ S`.  This is the shape in which the cutoffs of
  `Probability/CutoffConstruction.lean` (with `S = specC (h1PencilLimit r k F z)`) enter;
* `integrable_dbarNumOrder_mul_trace_operatorMatrixPencilCauchy_fin` — `hIntLim`
  unconditionally for every `C^{k+1}` compactly supported `g`;
* `hstat` is `integral_flatStat_eq_gueStatisticCfc_canonical`
  (`Probability/KroneckerIdentity.lean`), which is unconditional for continuous `g`; the
  wrapper `integral_flatStat_eq_gueStatisticCfc_pencil` below records that.

**What remains**: the spectral inclusion
`spectrum ℝ (closedPencil (pencilConstCoeff k F z) (pencilDirCoeff k F)) ⊆ specC (h1PencilLimit r k F z)`.
It is *not* derivable from the present lemmas: it is the Kronecker/affine identity
`flatPencilBlk = reindex (guePencilMatrix …)`, i.e. the same bookkeeping gap that underlies the
limit-side spectrum of the linearization.  The theorems below therefore take it as the single
remaining hypothesis.
-/
import GUEStrongConvergence.Probability.LimitBridge
import GUEStrongConvergence.Probability.KroneckerIdentity

open MeasureTheory ProbabilityTheory Matrix Filter Complex FreeProbability FreeProbability.Fock
open scoped ComplexOrder Topology BigOperators ENNReal NNReal

namespace GUEStrongConvergence

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

variable {r : ℕ}

local instance limIdNontrivial : Nontrivial (closedSemicircularAlgebra (Fin r)) :=
  (closedGeneratedVacuumState (Fin r)).toProbabilitySpace.nontrivial

local instance limIdPartialOrder : PartialOrder (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrder _

local instance limIdStarOrderedRing : StarOrderedRing (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrderedRing _

/-! ## The closed-pencil bridge at an arbitrary square size -/

/-- **The closed-pencil bridge for `Fin n`.**  The matrix trace of the operator-valued Cauchy
transform of the pencil `(A₀, A)` equals the block-limit resolvent trace of the canonical limit
element `closedPencil A₀ A`, for every square size `n` (no `n = d' + 1` restriction). -/
theorem trace_operatorMatrixPencilCauchy_eq_blockLimitResolventTrace_fin
    (n : ℕ) [NeZero n] (C₀ : Matrix (Fin n) (Fin n) ℂ) (C : Fin r → Matrix (Fin n) (Fin n) ℂ)
    (hC₀ : C₀.IsHermitian) (hC : ∀ i, (C i).IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    Matrix.trace (operatorMatrixPencilCauchy C₀ C z) =
      blockLimitResolventTrace (d := n) (closedPencil (n := Fin n) C₀ C) z := by
  have hsa := closedPencil_isSelfAdjoint (n := Fin n) C₀ C hC₀ hC
  have hunit : IsUnit (algebraMap ℂ
      (CStarMatrix (Fin n) (Fin n) (closedSemicircularAlgebra (Fin r))) z -
        closedPencil (n := Fin n) C₀ C) := by
    rw [← spectrum.notMem_iff]
    intro hzmem
    exact hz (hsa.im_eq_zero_of_mem_spectrum hzmem)
  have hres := cmap_resolvent (f := StarSubalgebra.subtype (closedSemicircularAlgebra (Fin r)))
    (M := closedPencil (n := Fin n) C₀ C) (z := z) hunit
  rw [cmap_subtype_closedPencil] at hres
  rw [trace_operatorMatrixPencilCauchy]
  unfold blockLimitResolventTrace
  rw [← hres]
  have hsymm : CStarMatrix.ofMatrix.symm
      ((cmap (StarSubalgebra.subtype (closedSemicircularAlgebra (Fin r))))
        (resolvent (closedPencil (n := Fin n) C₀ C) z)) =
      (cmap (StarSubalgebra.subtype (closedSemicircularAlgebra (Fin r))))
        (resolvent (closedPencil (n := Fin n) C₀ C) z) := rfl
  rw [hsymm, trace_cmap]
  rfl

/-! ## Vanishing of the limit statistic from the cutoff -/

/-- **`hlim0` from a cutoff vanishing on a set containing the limit spectrum.**  If `g` is a
smooth cutoff vanishing (with derivative) on `S`, and `S` contains the spectrum of the canonical
limit element `closedPencil A₀ A`, then the order-`k` plane limit statistic of `g` vanishes.

This is the exact form needed downstream: the concrete cutoffs satisfy
`IsSmoothCutoffZeroOn (specC (h1PencilLimit r k F z)) ε g`, so the only extra input is
`spectrum ℝ (closedPencil A₀ A) ⊆ specC (h1PencilLimit r k F z)`. -/
theorem guePlaneLimitOrder_eq_zero_of_isSmoothCutoffZeroOn {k K : ℕ} (hk : 1 ≤ k)
    {n : ℕ} [NeZero n] {A₀ : Matrix (Fin n) (Fin n) ℂ} {A : Fin r → Matrix (Fin n) (Fin n) ℂ}
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    {S : Set ℝ} {ε : ℝ} {g : ℝ → ℝ} (hcut : IsSmoothCutoffZeroOn S ε g)
    (hsub : spectrum ℝ (closedPencil (n := Fin n) A₀ A) ⊆ S)
    (hg : ContDiff ℝ K g) (hK : k + 1 ≤ K) (hgc : HasCompactSupport g) :
    guePlaneLimitOrder k A₀ A g = 0 := by
  have hsa := closedPencil_isSelfAdjoint (n := Fin n) A₀ A hA₀ hA
  refine guePlaneLimitOrder_eq_zero_of_eq_zero_on_spectrum hk hsa ?_ hg hK hgc ?_
  · intro z hz
    exact trace_operatorMatrixPencilCauchy_eq_blockLimitResolventTrace_fin n A₀ A hA₀ hA hz
  · intro x hx
    exact (eq_zero_and_deriv_eq_zero_on_spectrum_of_isSmoothCutoffZeroOn hcut hsub x hx).1

/-- Variant of `guePlaneLimitOrder_eq_zero_of_isSmoothCutoffZeroOn` from the two scalar
conditions directly (no `IsSmoothCutoffZeroOn` needed). -/
theorem guePlaneLimitOrder_eq_zero_of_eq_zero_on_subset {k K : ℕ} (hk : 1 ≤ k)
    {n : ℕ} [NeZero n] {A₀ : Matrix (Fin n) (Fin n) ℂ} {A : Fin r → Matrix (Fin n) (Fin n) ℂ}
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    {S : Set ℝ} {g : ℝ → ℝ} (hzero : ∀ x ∈ S, g x = 0)
    (hsub : spectrum ℝ (closedPencil (n := Fin n) A₀ A) ⊆ S)
    (hg : ContDiff ℝ K g) (hK : k + 1 ≤ K) (hgc : HasCompactSupport g) :
    guePlaneLimitOrder k A₀ A g = 0 := by
  have hsa := closedPencil_isSelfAdjoint (n := Fin n) A₀ A hA₀ hA
  refine guePlaneLimitOrder_eq_zero_of_eq_zero_on_spectrum hk hsa ?_ hg hK hgc ?_
  · intro z hz
    exact trace_operatorMatrixPencilCauchy_eq_blockLimitResolventTrace_fin n A₀ A hA₀ hA hz
  · intro x hx
    exact hzero x (hsub hx)

/-! ## The limit-side plane integrability, unconditionally -/

/-- **`hIntLim` unconditionally.**  For a `C^{k+1}` compactly supported `g` and a Hermitian
pencil, the plane integrand `∂̄_k g · Tr(g(·))` is integrable; the trace identification needed by
the general lemma is the closed-pencil bridge. -/
theorem integrable_dbarNumOrder_mul_trace_operatorMatrixPencilCauchy_fin
    (n : ℕ) [NeZero n] (A₀ : Matrix (Fin n) (Fin n) ℂ) (A : Fin r → Matrix (Fin n) (Fin n) ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    {g : ℝ → ℝ} {k K : ℕ} (hk : 1 ≤ k) (hg : ContDiff ℝ K g) (hK : k + 1 ≤ K)
    (hgc : HasCompactSupport g) :
    Integrable (fun p : ℝ × ℝ => dbarNumOrder (k + 1) g (zOf p) *
      Matrix.trace (operatorMatrixPencilCauchy A₀ A (zOf p)))
      (volume : Measure (ℝ × ℝ)) :=
  integrable_dbarNumOrder_mul_trace_operatorMatrixPencilCauchy_of_eq
    (closedPencil (n := Fin n) A₀ A)
    (closedPencil_isSelfAdjoint (n := Fin n) A₀ A hA₀ hA)
    (fun z hz =>
      trace_operatorMatrixPencilCauchy_eq_blockLimitResolventTrace_fin n A₀ A hA₀ hA hz)
    hk hg hK hgc

/-! ## The flat ⟶ GUE statistic identification at the canonical pencil -/

/-- **`hstat` at the canonical pencil.**  The flattened statistic at block `N` of the canonical
dilated polynomial is the GUE statistic of the pencil coefficients at block `N+1`; this is
`integral_flatStat_eq_gueStatisticCfc_canonical` rewritten in the exact shape consumed by
`flatLemmaM_of_weightedStrip_order`. -/
theorem integral_flatStat_eq_gueStatisticCfc_pencil {k : ℕ} (F : RatPolyIdx r (k + 1))
    (z : ℝ) {g : ℝ → ℝ} (hg : Continuous g) (N : ℕ) :
    ∫ x, flatStat r k F z N g x ∂(commonGaussianMeasure (Fin r))
      = ∫ y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)),
          gueStatisticCfc (N := N + 1) g (pencilConstCoeff k F z) (pencilDirCoeff k F)
            (pencilConstCoeff_isHermitian k F z) (pencilDirCoeff_isHermitian k F) y
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))) :=
  integral_flatStat_eq_gueStatisticCfc_canonical k F N z hg

end

end GUEStrongConvergence
