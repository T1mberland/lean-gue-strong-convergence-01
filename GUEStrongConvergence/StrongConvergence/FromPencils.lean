/-
# Deterministic transfer from pencil spectral inclusion

This file begins the deterministic reduction of §3 of the linearization handoff:
the operator-norm convergence `‖P(X_n)‖ → ‖P(x)‖` is reduced to

* (H1) one-sided spectral inclusion for every *fixed* Hermitian linearization
  pencil `ℒ_z`, and
* (H2) convergence of noncommutative polynomial moments.

Nothing here assumes norm convergence of the generators or of `P`; the only
norm input is the explicit uniform bound `‖P(X_n)‖ ≤ C`, which in the GUE
application comes from the probabilistic edge estimate.

The algebraic linearization (`penL`, `penL_isUnit_iff`) is reused from
`Linearization/SelfAdjointPencil.lean` and `Linearization/Evaluation.lean`.
-/
import GUEStrongConvergence.Linearization.Evaluation
import GUEStrongConvergence.Linearization.SelfAdjointPencil
import GUEStrongConvergence.StrongConvergence.HermitianDilation
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.Order.Field
import GUEStrongConvergence.Analysis.FaithfulMomentNorm
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.Compact

namespace GUEStrongConvergence

open Matrix Filter
open scoped Topology

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {B : Type*} [CStarAlgebra B] [Nontrivial B] [PartialOrder B] [StarOrderedRing B]
  {I κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **The evaluated noncommutative polynomial** `∑ k, coeff k * wds k`. -/
def wordPolyEval (x : I → B) (wds : κ → List I) (coeff : κ → B) : B :=
  ∑ k, coeff k * wordProd x (wds k)

/-- The evaluated polynomial with a constant term `C`:
`C + q + q*`, the self-adjoint polynomial attached to the pencil. -/
def wordPolyEvalC (C : B) (x : I → B) (wds : κ → List I) (coeff : κ → B) : B :=
  C + wordPolyEval x wds coeff + star (wordPolyEval x wds coeff)

/-- The `(1,1)` block used in the linearization: `z • 1 - C`. -/
def penA0 (C : B) (z : ℝ) : Matrix (Fin 1) (Fin 1) B :=
  Matrix.of fun _ _ => (z : ℂ) • (1 : B) - C

/-- The block index type of the pencil. -/
abbrev PenIdx (wds : κ → List I) : Type _ :=
  (Fin 1) ⊕ (BlkIdx wds ⊕ BlkIdx wds)

/-- The pencil `ℒ_z`, as an actual element of the C⋆-algebra of block matrices. -/
def penLCS (x : I → B) (wds : κ → List I) (coeff : κ → B) (C : B) (z : ℝ) :
    CStarMatrix (PenIdx wds) (PenIdx wds) B :=
  CStarMatrix.ofMatrix (penL x wds coeff (penA0 C z))

/-- Invertibility of a `1 × 1` matrix over a ring is invertibility of its entry. -/
theorem isUnit_oneByOne_iff (a : B) :
    IsUnit (Matrix.of (fun _ _ : Fin 1 => a)) ↔ IsUnit a := by
  constructor
  · rintro ⟨u, hu⟩
    refine isUnit_iff_exists.mpr
      ⟨(((u⁻¹ : (Matrix (Fin 1) (Fin 1) B)ˣ) : Matrix (Fin 1) (Fin 1) B) 0 0), ?_, ?_⟩
    · have hmul := congrArg (fun M : Matrix (Fin 1) (Fin 1) B => M 0 0)
        (Units.mul_inv u)
      have h := congrArg (fun M : Matrix (Fin 1) (Fin 1) B => M 0 0) hu
      simp only [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_one,
        Matrix.of_apply] at h hmul
      rw [h] at hmul
      exact hmul
    · have hmul := congrArg (fun M : Matrix (Fin 1) (Fin 1) B => M 0 0)
        (Units.inv_mul u)
      have h := congrArg (fun M : Matrix (Fin 1) (Fin 1) B => M 0 0) hu
      simp only [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_one,
        Matrix.of_apply] at h hmul
      rw [h] at hmul
      exact hmul
  · rintro ⟨u, hu⟩
    refine isUnit_iff_exists.mpr
      ⟨Matrix.of (fun _ _ : Fin 1 => ((u⁻¹ : Bˣ) : B)), ?_, ?_⟩
    · ext i j
      fin_cases i; fin_cases j
      simp only [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_one]
      rw [← hu]
      simpa using Units.mul_inv u
    · ext i j
      fin_cases i; fin_cases j
      simp only [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_one]
      rw [← hu]
      simpa using Units.inv_mul u

/-- **Invertibility equivalence at a real spectral parameter.** For the polynomial
`P = C + q + q*` with `q = ∑ k, coeff k * wordProd x (wds k)`, the pencil `ℒ_z(x)`
is invertible in the C⋆-algebra of block matrices if and only if `z - P` is
invertible in `B`. -/
theorem penLCS_isUnit_iff (x : I → B) (wds : κ → List I) (coeff : κ → B)
    (C : B) (z : ℝ) :
    IsUnit (penLCS x wds coeff C z) ↔
      IsUnit (((z : ℂ) • (1 : B)) - wordPolyEvalC C x wds coeff) := by
  set q : Matrix (Fin 1) (Fin 1) B :=
    linU wds coeff * linQinvMat x wds * linV x wds with hq
  have hq00 : q 0 0 = wordPolyEval x wds coeff := by
    rw [hq]
    exact linU_mul_linQinvMat_mul_linV x wds coeff
  have hmat : penA0 C z - (q + qᴴ) =
      Matrix.of (fun _ _ : Fin 1 =>
        ((z : ℂ) • (1 : B) - C)
          - (wordPolyEval x wds coeff + star (wordPolyEval x wds coeff))) := by
    ext i j
    fin_cases i; fin_cases j
    rw [Matrix.sub_apply, Matrix.add_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply, penA0, Matrix.of_apply]
    change ((z : ℂ) • (1 : B) - C) - (q 0 0 + star (q 0 0))
      = ((z : ℂ) • (1 : B) - C)
        - (wordPolyEval x wds coeff + star (wordPolyEval x wds coeff))
    rw [hq00]
  have hmain : IsUnit (penL x wds coeff (penA0 C z)) ↔
      IsUnit (((z : ℂ) • (1 : B)) - wordPolyEvalC C x wds coeff) := by
    rw [penL_isUnit_iff, hmat, isUnit_oneByOne_iff]
    have he : ((z : ℂ) • (1 : B) - C
          - (wordPolyEval x wds coeff + star (wordPolyEval x wds coeff)))
        = ((z : ℂ) • (1 : B)) - wordPolyEvalC C x wds coeff := by
      rw [wordPolyEvalC, sub_sub, add_assoc]
    rw [he]
  have htransfer := isUnit_map_iff
    (f := CStarMatrix.ofMatrixRingEquiv (n := PenIdx wds) (A := B))
    (penL x wds coeff (penA0 C z))
  exact htransfer.symm.trans hmain

/-- **Inverse norm from a spectral gap.** A self-adjoint unit whose spectrum stays
away from `0` by `δ` has inverse norm at most `δ⁻¹`. -/
theorem norm_ringInverse_le_of_spectrum_gap {v : B} (hv : IsSelfAdjoint v)
    {δ : ℝ} (hδ : 0 < δ) (hunit : IsUnit v)
    (hgap : ∀ w ∈ spectrum ℂ v, δ ≤ ‖w‖) :
    ‖Ring.inverse v‖ ≤ δ⁻¹ := by
  haveI : IsStarNormal v := IsSelfAdjoint.isStarNormal hv
  have hvne : ∀ w ∈ spectrum ℂ v, w ≠ 0 := by
    intro w hw hw0
    have h := hgap w hw
    rw [hw0, norm_zero] at h
    linarith
  have hcfc : cfc (fun w : ℂ => w⁻¹) v = Ring.inverse v :=
    cfc_ringInverse_id v hunit
  rw [← hcfc]
  refine norm_cfc_le (c := δ⁻¹) (by positivity) ?_
  intro w hw
  calc ‖(w : ℂ)⁻¹‖ = (‖w‖)⁻¹ := norm_inv w
    _ ≤ δ⁻¹ := inv_anti₀ hδ (hgap w hw)

/-- If `u` is a unit and `‖u⁻¹ (w • 1)‖ < 1`, then `u - w • 1` is a unit. -/
theorem isUnit_sub_scalar_of_isUnit {u : B} (hu : IsUnit u) {w : ℂ}
    (h : ‖Ring.inverse u * ((w : ℂ) • (1 : B))‖ < 1) :
    IsUnit (u - (w : ℂ) • (1 : B)) := by
  have hfac : u - (w : ℂ) • (1 : B) =
      u * (1 - Ring.inverse u * ((w : ℂ) • (1 : B))) := by
    rw [mul_sub, mul_one, ← mul_assoc, Ring.mul_inverse_cancel u hu, one_mul]
  rw [hfac]
  exact hu.mul (isUnit_one_sub_of_norm_lt_one h)

/-- **Spectral gap from an inverse norm.** Every spectral value of a unit is bounded
below by the reciprocal of the inverse norm. -/
theorem spectrum_gap_of_inverse_norm {v : B} (hunit : IsUnit v) :
    ∀ w ∈ spectrum ℂ v, (‖Ring.inverse v‖)⁻¹ ≤ ‖w‖ := by
  intro w hw
  set K := ‖Ring.inverse v‖ with hK
  rcases eq_or_lt_of_le (norm_nonneg (Ring.inverse v)) with hK0 | hKpos
  · -- `K = 0`: the reciprocal is `0`
    have hKz : K = 0 := hK0.symm
    simp [hKz]
  · by_contra hle
    have hlt : ‖w‖ < K⁻¹ := not_le.mp hle
    have hprod : ‖w‖ * K < 1 := by
      calc ‖w‖ * K < K⁻¹ * K := mul_lt_mul_of_pos_right hlt hKpos
        _ = 1 := inv_mul_cancel₀ (ne_of_gt hKpos)
    have hnorm : ‖Ring.inverse v * ((w : ℂ) • (1 : B))‖ < 1 := by
      calc ‖Ring.inverse v * ((w : ℂ) • (1 : B))‖
          ≤ ‖Ring.inverse v‖ * ‖((w : ℂ) • (1 : B))‖ := norm_mul_le _ _
        _ = K * ‖w‖ := by rw [norm_smul, norm_one, mul_one]
        _ = ‖w‖ * K := mul_comm _ _
        _ < 1 := hprod
    have hsub : IsUnit (v - (w : ℂ) • (1 : B)) :=
      isUnit_sub_scalar_of_isUnit hunit hnorm
    have hnot : ¬ IsUnit (algebraMap ℂ B w - v) := hw
    apply hnot
    have hneg : algebraMap ℂ B w - v = -((v - (w : ℂ) • (1 : B))) := by
      rw [Algebra.algebraMap_eq_smul_one]
      abel
    rw [hneg]
    exact hsub.neg

/-- **Neumann perturbation of a unit.** If `u` is a unit and `‖u⁻¹ v‖ < 1`, then
`u + v` is a unit. -/
theorem isUnit_add_of_isUnit_of_norm_mul_lt_one {u v : B} (hu : IsUnit u)
    (h : ‖Ring.inverse u * v‖ < 1) : IsUnit (u + v) := by
  have hfac : u + v = u * (1 + Ring.inverse u * v) := by
    rw [mul_add, mul_one, ← mul_assoc, Ring.mul_inverse_cancel u hu, one_mul]
  rw [hfac]
  refine hu.mul ?_
  have h' : IsUnit (1 - -(Ring.inverse u * v)) :=
    isUnit_one_sub_of_norm_lt_one (by simpa using h)
  simpa [sub_neg_eq_add] using h'

/-- The `(1,1)` block `z • 1 - C` is self-adjoint for real `z` and self-adjoint `C`. -/
theorem penA0_conjTranspose {C : B} (hC : IsSelfAdjoint C) (z : ℝ) :
    (penA0 C z)ᴴ = penA0 C z := by
  ext i j
  fin_cases i; fin_cases j
  have hz : star (z : ℂ) = (z : ℂ) := by simp
  simp only [penA0, Matrix.conjTranspose_apply, Matrix.of_apply, star_sub, star_smul,
    hC.star_eq, star_one, hz]

/-- The pencil is self-adjoint for real `z` and self-adjoint `C`. -/
theorem penLCS_isSelfAdjoint (x : I → B) (wds : κ → List I) (coeff : κ → B)
    {C : B} (hC : IsSelfAdjoint C) (z : ℝ) :
    IsSelfAdjoint (penLCS x wds coeff C z) := by
  change CStarMatrix.ofMatrix ((penL x wds coeff (penA0 C z))ᴴ)
    = CStarMatrix.ofMatrix (penL x wds coeff (penA0 C z))
  rw [penL_conjTranspose, penA0_conjTranspose hC]

/-- The fixed projection `Π_D` in the C⋆-algebra of block matrices has norm at most one. -/
theorem penPiCS_norm_le_one (wds : κ → List I) :
    ‖CStarMatrix.ofMatrix (penPi (M := B) wds)‖ ≤ 1 := by
  set p : CStarMatrix (PenIdx wds) (PenIdx wds) B :=
    CStarMatrix.ofMatrix (penPi (M := B) wds) with hp
  have hproj : p * p = p := by
    rw [hp]
    change CStarMatrix.ofMatrix (penPi (M := B) wds * penPi (M := B) wds)
      = CStarMatrix.ofMatrix (penPi (M := B) wds)
    rw [penPi_mul_self]
  have hstar : star p = p := by
    rw [hp]
    change CStarMatrix.ofMatrix (star (penPi (M := B) wds))
      = CStarMatrix.ofMatrix (penPi (M := B) wds)
    rw [Matrix.star_eq_conjTranspose, penPi_conjTranspose]
  have h := CStarRing.norm_star_mul_self (x := p)
  rw [hstar, hproj] at h
  have hnn : 0 ≤ ‖p‖ := norm_nonneg _
  nlinarith

/-- **Lipschitz continuity of the pencil in the real spectral parameter.** -/
theorem penLCS_sub_norm_le (x : I → B) (wds : κ → List I) (coeff : κ → B)
    (C : B) (z z' : ℝ) :
    ‖penLCS x wds coeff C z - penLCS x wds coeff C z'‖ ≤ |z - z'| := by
  have hdiff : penLCS x wds coeff C z - penLCS x wds coeff C z'
      = CStarMatrix.ofMatrix ((z - z') • penPi (M := B) wds) := by
    rw [penLCS, penLCS, CStarMatrix.of_sub_of, penL_sub]
    have hA : penA0 C z - penA0 C z'
        = (z - z') • (1 : Matrix (Fin 1) (Fin 1) B) := by
      ext i j
      fin_cases i; fin_cases j
      simp only [penA0, Matrix.sub_apply, Matrix.of_apply, Matrix.smul_apply,
        Matrix.one_apply, Complex.ofReal_sub, sub_smul]
      abel
    rw [hA]
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · fin_cases i; fin_cases j
      simp [penPi, fromBlocks, Matrix.smul_apply]
    · fin_cases i
      simp [penPi, fromBlocks, Matrix.smul_apply]
    · fin_cases j
      simp [penPi, fromBlocks, Matrix.smul_apply]
    · simp [penPi, fromBlocks, Matrix.smul_apply]
  rw [hdiff]
  have hsmul : CStarMatrix.ofMatrix ((z - z') • penPi (M := B) wds)
      = ((z - z' : ℝ) : ℂ) • CStarMatrix.ofMatrix (penPi (M := B) wds) := by
    ext i j
    rfl
  rw [hsmul, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  calc |z - z'| * ‖CStarMatrix.ofMatrix (penPi (M := B) wds)‖
      ≤ |z - z'| * 1 := mul_le_mul_of_nonneg_left (penPiCS_norm_le_one wds) (abs_nonneg _)
    _ = |z - z'| := mul_one _


/-- **One-sided spectral inclusion (H1)** for every fixed real pencil parameter. -/
def SpectralInclusion (x : I → B) (X : ℕ → I → B) (wds : κ → List I)
    (coeff : κ → B) (C : B) : Prop :=
  ∀ z : ℝ, ∀ ε > 0, ∀ᶠ n in atTop,
    ∀ a ∈ spectrum ℝ (penLCS (X n) wds coeff C z),
      ∃ b ∈ spectrum ℝ (penLCS x wds coeff C z), |a - b| ≤ ε

/-- A real spectral value of a complex C⋆-algebra element makes the corresponding
complex scalar shift non-invertible. -/
theorem not_isUnit_of_mem_spectrum_real {v : B} {z : ℝ} (hz : z ∈ spectrum ℝ v) :
    ¬ IsUnit (((z : ℂ) • (1 : B)) - v) := by
  have hzC : (z : ℂ) ∈ spectrum ℂ v := (spectrum.algebraMap_mem_iff ℂ).mpr hz
  intro hu
  have hres : (z : ℂ) ∈ resolventSet ℂ v := by
    rw [spectrum.mem_resolventSet_iff]
    simpa [Algebra.algebraMap_eq_smul_one] using hu
  have hzC' : (z : ℂ) ∉ resolventSet ℂ v := by simpa [spectrum] using hzC
  exact hzC' hres

attribute [local irreducible] penLCS

/-- **Core no-outlier lemma.** A sequence of eigenvalues `z n` of the evaluated
polynomials cannot converge to a real point outside `[-‖P(x)‖, ‖P(x)‖]`, assuming
one-sided spectral inclusion for every fixed pencil parameter. This is the
sequential form of the upper bound `limsup ‖P(X n)‖ ≤ ‖P(x)‖`; the uniform norm
bound needed to extract a convergent subsequence is supplied separately by the
probabilistic side. -/

theorem no_outlier_of_spectral_inclusion
    (x : I → B) (X : ℕ → I → B) (wds : κ → List I) (coeff : κ → B)
    {C : B} (hC : IsSelfAdjoint C)
    (hH1 : SpectralInclusion x X wds coeff C)
    {zs : ℕ → ℝ}
    (hzs : ∀ n, zs n ∈ spectrum ℝ (wordPolyEvalC C (X n) wds coeff))
    {z : ℝ} (hzt : Tendsto zs atTop (𝓝 z))
    (hout : ‖wordPolyEvalC C x wds coeff‖ < |z|) : False := by
  let P : B := wordPolyEvalC C x wds coeff
  have hPunit : IsUnit (((z : ℂ) • (1 : B)) - P) := by
    by_contra hnot
    have hmem : (z : ℂ) ∈ spectrum ℂ P := by
      rw [spectrum, Set.mem_compl_iff, spectrum.mem_resolventSet_iff]
      simpa [Algebra.algebraMap_eq_smul_one] using hnot
    have hle : ‖(z : ℂ)‖ ≤ ‖P‖ := spectrum.norm_le_norm_of_mem hmem
    have hnorm : ‖(z : ℂ)‖ = |z| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm] at hle
    linarith
  have hL0 : IsUnit (penLCS x wds coeff C z) :=
    (penLCS_isUnit_iff x wds coeff C z).mpr hPunit
  set K : ℝ := ‖Ring.inverse (penLCS x wds coeff C z)‖ with hK
  have hKpos : 0 < K := by
    have hne : Ring.inverse (penLCS x wds coeff C z) ≠ 0 := by
      intro h0
      have h1 := Ring.mul_inverse_cancel (penLCS x wds coeff C z) hL0
      rw [h0, mul_zero] at h1
      exact zero_ne_one h1
    exact norm_pos_iff.mpr hne
  have hgap0 : ∀ a ∈ spectrum ℂ (penLCS x wds coeff C z), K⁻¹ ≤ ‖a‖ := by
    have h := spectrum_gap_of_inverse_norm hL0
    simpa [hK] using h
  set ε : ℝ := K⁻¹ / 4 with hε
  have hεpos : 0 < ε := by positivity
  have hH1e : ∀ᶠ n in atTop,
      ∀ a ∈ spectrum ℝ (penLCS (X n) wds coeff C z),
        ∃ b ∈ spectrum ℝ (penLCS x wds coeff C z), |a - b| ≤ ε :=
    hH1 z ε hεpos
  have hzt' : ∀ᶠ n in atTop, |zs n - z| < K⁻¹ / 4 := by
    have h0 : Tendsto (fun n => zs n - z) atTop (𝓝 0) := by
      simpa using hzt.sub_const z
    have h1 : Tendsto (fun n => |zs n - z|) atTop (𝓝 0) := by
      simpa using h0.abs
    exact h1.eventually (gt_mem_nhds hεpos)
  obtain ⟨n, hspec, hclose⟩ := (hH1e.and hzt').exists
  have hnotn : ¬ IsUnit (((zs n : ℂ) • (1 : B)) - wordPolyEvalC C (X n) wds coeff) :=
    not_isUnit_of_mem_spectrum_real (hzs n)
  have hLnot : ¬ IsUnit (penLCS (X n) wds coeff C (zs n)) := by
    intro hu
    exact hnotn ((penLCS_isUnit_iff (X n) wds coeff C (zs n)).mp hu)
  have hsa : IsSelfAdjoint (penLCS (X n) wds coeff C z) :=
    penLCS_isSelfAdjoint (X n) wds coeff hC z
  have hgapn : ∀ a ∈ spectrum ℂ (penLCS (X n) wds coeff C z),
      3 * K⁻¹ / 4 ≤ ‖a‖ := by
    intro a ha
    have him : a.im = 0 := hsa.im_eq_zero_of_mem_spectrum ha
    have hEq : ((a.re : ℂ)) = a := by
      apply Complex.ext
      · rfl
      · simpa using him.symm
    have hre : a.re ∈ spectrum ℝ (penLCS (X n) wds coeff C z) := by
      have hCmem : ((a.re : ℂ)) ∈ spectrum ℂ (penLCS (X n) wds coeff C z) := by
        rwa [hEq]
      exact (spectrum.algebraMap_mem_iff ℂ).mp hCmem
    obtain ⟨b, hb, hdist⟩ := hspec a.re hre
    have hbC : (b : ℂ) ∈ spectrum ℂ (penLCS x wds coeff C z) :=
      (spectrum.algebraMap_mem_iff ℂ).mpr hb
    have hbge : K⁻¹ ≤ |b| := by
      have h := hgap0 (b : ℂ) hbC
      simpa [Complex.norm_real, Real.norm_eq_abs] using h
    have hdist' : |a.re - b| ≤ ε := hdist
    have htri : |b| - |a.re| ≤ |b - a.re| := abs_sub_abs_le_abs_sub b a.re
    have htri' : |b| - |a.re| ≤ ε := by
      refine htri.trans ?_
      simpa [abs_sub_comm] using hdist'
    have hanorm : ‖a‖ = |a.re| := by
      rw [← hEq]
      simp [Complex.norm_real, Real.norm_eq_abs]
    rw [hanorm]
    calc 3 * K⁻¹ / 4 = K⁻¹ - ε := by rw [hε]; ring
      _ ≤ |a.re| := by linarith
  have h0not : (0 : ℂ) ∉ spectrum ℂ (penLCS (X n) wds coeff C z) := by
    intro h0
    have h := hgapn 0 h0
    have hKinv : 0 < K⁻¹ := inv_pos.mpr hKpos
    simp at h
    linarith
  have hunitn : IsUnit (penLCS (X n) wds coeff C z) := by
    have hres : (0 : ℂ) ∈ resolventSet ℂ (penLCS (X n) wds coeff C z) := by
      simpa [spectrum] using h0not
    have hu := spectrum.mem_resolventSet_iff.mp hres
    have hu' : IsUnit (-(penLCS (X n) wds coeff C z)) := by
      simpa [Algebra.algebraMap_eq_smul_one] using hu
    simpa using hu'.neg
  have hδpos : 0 < 3 * K⁻¹ / 4 := by positivity
  have hinv : ‖Ring.inverse (penLCS (X n) wds coeff C z)‖ ≤ (3 * K⁻¹ / 4)⁻¹ :=
    norm_ringInverse_le_of_spectrum_gap hsa hδpos hunitn hgapn
  let Lz : CStarMatrix (PenIdx wds) (PenIdx wds) B := penLCS (X n) wds coeff C z
  let Lzn : CStarMatrix (PenIdx wds) (PenIdx wds) B := penLCS (X n) wds coeff C (zs n)
  have hΔ0 := @penLCS_sub_norm_le B _ _ _ _ I κ _ _ (X n) wds coeff C (zs n) z
  have hΔ : ‖Lzn - Lz‖ ≤ |zs n - z| := hΔ0
  have hsmall : |zs n - z| < 3 * K⁻¹ / 4 := by linarith
  have hnormΔ : ‖Ring.inverse Lz * (Lzn - Lz)‖ < 1 := by
    have h1 : ‖Ring.inverse Lz * (Lzn - Lz)‖
        ≤ ‖Ring.inverse Lz‖ * ‖Lzn - Lz‖ := norm_mul_le _ _
    have h2 : ‖Ring.inverse Lz‖ * ‖Lzn - Lz‖
        ≤ (3 * K⁻¹ / 4)⁻¹ * |zs n - z| := by
      exact mul_le_mul hinv hΔ (norm_nonneg _) (by positivity)
    have h3 : (3 * K⁻¹ / 4)⁻¹ * |zs n - z| < 1 := by
      have h := mul_lt_mul_of_pos_left hsmall (inv_pos.mpr hδpos)
      rwa [inv_mul_cancel₀ (ne_of_gt hδpos)] at h
    exact lt_of_le_of_lt h1 (lt_of_le_of_lt h2 h3)
  have hadd : IsUnit (Lz + (Lzn - Lz)) :=
    isUnit_add_of_isUnit_of_norm_mul_lt_one hunitn hnormΔ
  have heq : Lzn = Lz + (Lzn - Lz) := (add_sub_cancel Lz Lzn).symm
  have hLnot' : ¬ IsUnit Lzn := hLnot
  rw [heq] at hLnot'
  exact hLnot' hadd


variable {B : Type*} [CStarAlgebra B] [Nontrivial B] [PartialOrder B] [StarOrderedRing B]
  {I κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Evaluation of the free algebra on the letters `I ⊕ B`: generators are evaluated
at `X`, coefficient letters are fixed elements of `B`. -/
noncomputable def evalFree (X : I → B) : FreeAlgebra ℂ (I ⊕ B) →ₐ[ℂ] B :=
  FreeAlgebra.lift ℂ fun a => match a with
    | Sum.inl i => X i
    | Sum.inr b => b

@[simp] theorem evalFree_ι_inl (X : I → B) (i : I) :
    evalFree X (FreeAlgebra.ι ℂ (Sum.inl i)) = X i :=
  FreeAlgebra.lift_ι_apply _ _

@[simp] theorem evalFree_ι_inr (X : I → B) (b : B) :
    evalFree X (FreeAlgebra.ι ℂ (Sum.inr b)) = b :=
  FreeAlgebra.lift_ι_apply _ _

/-- The monomial of the free algebra attached to a word of generators. -/
noncomputable def freeWord (w : List I) : FreeAlgebra ℂ (I ⊕ B) :=
  (w.map (fun i => FreeAlgebra.ι ℂ (Sum.inl i))).prod

theorem freeWord_append (u v : List I) :
    freeWord (B := B) (u ++ v) = freeWord u * freeWord v := by
  simp [freeWord, List.map_append, List.prod_append]

theorem evalFree_freeWord (X : I → B) (w : List I) :
    evalFree X (freeWord (B := B) w) = wordProd X w := by
  induction w with
  | nil => simp [freeWord, wordProd]
  | cons i w ih =>
      calc evalFree X (freeWord (B := B) (i :: w))
          = evalFree X (FreeAlgebra.ι ℂ (Sum.inl i) * freeWord (B := B) w) := by
            rw [freeWord, List.map_cons, List.prod_cons]
            rfl
        _ = X i * evalFree X (freeWord (B := B) w) := by
            rw [map_mul, evalFree_ι_inl]
        _ = X i * wordProd X w := by rw [ih]
        _ = wordProd X (i :: w) := by
            simp [wordProd]

/-- Reverse words evaluate to the star of the word product when the generators are
self-adjoint. -/
theorem evalFree_freeWord_reverse {X : I → B} (hX : ∀ i, star (X i) = X i) (w : List I) :
    evalFree X (freeWord (B := B) w.reverse) = star (wordProd X w) := by
  induction w with
  | nil => simp [freeWord, wordProd]
  | cons i w ih =>
      calc evalFree X (freeWord (B := B) (i :: w).reverse)
          = evalFree X (freeWord (B := B) w.reverse * freeWord (B := B) [i]) := by
            rw [List.reverse_cons, freeWord_append]
        _ = evalFree X (freeWord (B := B) w.reverse) * X i := by
            rw [map_mul, evalFree_freeWord, freeWord, List.map_cons, List.prod_cons,
              List.map_nil, List.prod_nil, mul_one, evalFree_ι_inl]
        _ = star (wordProd X w) * X i := by rw [ih]
        _ = star (wordProd X (i :: w)) := by
            simp only [wordProd, List.map_cons, List.prod_cons, star_mul, hX i]

/-- The free-algebra lift of the polynomial `C + q + q*`. -/
noncomputable def freePoly (C : B) (wds : κ → List I) (coeff : κ → B) :
    FreeAlgebra ℂ (I ⊕ B) :=
  FreeAlgebra.ι ℂ (Sum.inr C)
    + (∑ k, FreeAlgebra.ι ℂ (Sum.inr (coeff k)) * freeWord (B := B) (wds k))
    + (∑ k, freeWord (B := B) (wds k).reverse
        * FreeAlgebra.ι ℂ (Sum.inr (star (coeff k))))

theorem evalFree_freePoly {X : I → B} (hX : ∀ i, star (X i) = X i)
    (C : B) (wds : κ → List I) (coeff : κ → B) :
    evalFree X (freePoly C wds coeff) = wordPolyEvalC C X wds coeff := by
  simp only [freePoly, map_add, map_sum, map_mul, evalFree_ι_inr, evalFree_freeWord,
    evalFree_freeWord_reverse hX, wordPolyEvalC, wordPolyEval, star_sum, star_mul]

/-- **Word moment convergence (H2).** The state converges on every element of the
free algebra generated by the generators and the fixed coefficients. -/
def WordMomentConvergence (ψ : ℕ → FreeProbability.StarProbabilitySpace B)
    (φ : FreeProbability.StarProbabilitySpace B) (X : ℕ → I → B) (x : I → B) : Prop :=
  ∀ q : FreeAlgebra ℂ (I ⊕ B),
    Tendsto (fun n => (ψ n).expectation (evalFree (X n) q)) atTop
      (𝓝 (φ.expectation (evalFree x q)))

/-- `(s ^ n) ^ (1/n) = s` for `s ≥ 0` and `n ≠ 0`. -/
theorem pow_rpow_inv_natCast {s : ℝ} (hs : 0 ≤ s) {n : ℕ} (hn : n ≠ 0) :
    (s ^ n) ^ ((1 : ℝ) / (n : ℝ)) = s := by
  rw [← Real.rpow_natCast s n, ← Real.rpow_mul hs]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [one_div, mul_inv_cancel₀ hn', Real.rpow_one]

/-- A state value on a nonnegative element is at most the norm. -/
theorem state_re_le_norm (ψ : FreeProbability.StarProbabilitySpace B) {a : B}
    (ha : 0 ≤ a) : (ψ.expectation a).re ≤ ‖a‖ := by
  exact (Complex.re_le_norm _).trans (ψ.expectation_norm_le a)

/-- Even powers of a self-adjoint element are nonnegative. -/
theorem pow_even_nonneg {a : B} (ha : IsSelfAdjoint a) (k : ℕ) : 0 ≤ a ^ (2 * k) := by
  have h : a ^ (2 * k) = star (a ^ k) * a ^ k := by
    rw [star_pow, ha.star_eq, ← pow_add]
    ring_nf
  rw [h]
  exact star_mul_self_nonneg _

/-- The norm of an even power of a self-adjoint element is the power of its norm. -/
theorem norm_pow_even {a : B} (ha : IsSelfAdjoint a) {k : ℕ} (hk : k ≠ 0) :
    ‖a ^ (2 * k)‖ = ‖a‖ ^ (2 * k) := by
  haveI : IsStarNormal a := ha.isStarNormal
  exact CFC.norm_pow (𝕜 := ℂ) a (2 * k) (by omega)


/-- **Lower bound from word moments.** If the states converge on the free algebra,
then for every `ε > 0` eventually `‖P(X n)‖ ≥ ‖P(x)‖ - ε`.  This is the liminf half
of the transfer; the only analytic input is the faithful moment-norm formula. -/
theorem eventually_norm_ge_of_word_moments
    (X : ℕ → I → B) (x : I → B)
    (hX : ∀ n i, star (X n i) = X n i) (hx : ∀ i, star (x i) = x i)
    (ψ : ℕ → FreeProbability.StarProbabilitySpace B)
    (φ : FreeProbability.StarProbabilitySpace B)
    (hH2 : WordMomentConvergence ψ φ X x)
    (hfaith : FreeProbability.IsFaithful φ.toProbabilitySpace)
    (C : B) (wds : κ → List I) (coeff : κ → B)
    (hPn : ∀ n, IsSelfAdjoint (wordPolyEvalC C (X n) wds coeff))
    (hPlim : IsSelfAdjoint (wordPolyEvalC C x wds coeff))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      ‖wordPolyEvalC C x wds coeff‖ - ε ≤ ‖wordPolyEvalC C (X n) wds coeff‖ := by
  let P : B := wordPolyEvalC C x wds coeff
  let Pn : ℕ → B := fun n => wordPolyEvalC C (X n) wds coeff
  have hPnE : ∀ n, Pn n = evalFree (X n) (freePoly C wds coeff) := fun n =>
    (evalFree_freePoly (hX n) C wds coeff).symm
  have hPE : P = evalFree x (freePoly C wds coeff) :=
    (evalFree_freePoly hx C wds coeff).symm
  by_cases hpos : 0 < ‖P‖ - ε
  · have hroot := (tendsto_expectation_pow_rpow_eq_norm φ hfaith hPlim).eventually
      (eventually_ge_nhds (show ‖P‖ - ε / 2 < ‖P‖ by linarith))
    have hk1 : ∀ᶠ k : ℕ in atTop, 1 ≤ k := eventually_ge_atTop 1
    obtain ⟨k, hrootk, hkge⟩ := (hroot.and hk1).exists
    have hk0 : k ≠ 0 := by omega
    have hk2 : 2 * k ≠ 0 := by omega
    set xk : ℝ := (φ.expectation (P ^ (2 * k))).re with hxk
    have hxk_nonneg : 0 ≤ xk := by
      rw [hxk]
      simpa using (φ.expectation_nonneg (pow_even_nonneg hPlim k)).1
    have hrootk' : ‖P‖ - ε / 2 ≤ xk ^ ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) := by
      simpa [hxk] using hrootk
    have hroot_pow : (‖P‖ - ε / 2) ^ (2 * k) ≤ xk := by
      have hbase : 0 ≤ ‖P‖ - ε / 2 := by linarith
      calc (‖P‖ - ε / 2) ^ (2 * k)
          ≤ ((xk ^ ((1 : ℝ) / ((2 * k : ℕ) : ℝ))) ^ (2 * k)) := by
            exact pow_le_pow_left₀ hbase hrootk' (2 * k)
        _ = xk := by
            have h2k : ((2 * k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hk2
            rw [← Real.rpow_natCast (xk ^ ((1 : ℝ) / ((2 * k : ℕ) : ℝ))) (2 * k),
              ← Real.rpow_mul hxk_nonneg]
            rw [mul_comm, one_div, mul_inv_cancel₀ h2k, Real.rpow_one]
    have hxkgt : (‖P‖ - ε) ^ (2 * k) < xk := by
      have hlt : ‖P‖ - ε < ‖P‖ - ε / 2 := by linarith
      exact lt_of_lt_of_le (pow_lt_pow_left₀ hlt hpos.le hk2) hroot_pow
    let q : FreeAlgebra ℂ (I ⊕ B) := freePoly C wds coeff ^ (2 * k)
    have hmom := hH2 q
    have hmom_re : Tendsto (fun n => ((ψ n).expectation (Pn n ^ (2 * k))).re)
        atTop (𝓝 xk) := by
      have hcomplex : Tendsto (fun n => (ψ n).expectation (evalFree (X n) q))
          atTop (𝓝 (φ.expectation (evalFree x q))) := hmom
      have hinter : Tendsto (fun n => (ψ n).expectation (Pn n ^ (2 * k)))
          atTop (𝓝 (φ.expectation (P ^ (2 * k)))) := by
        have hEqfun : (fun n => (ψ n).expectation (evalFree (X n) q)) =ᶠ[atTop]
            (fun n => (ψ n).expectation (Pn n ^ (2 * k))) := by
          filter_upwards with n
          rw [hPnE n, map_pow]
        have hlim : φ.expectation (evalFree x q) = φ.expectation (P ^ (2 * k)) := by
          rw [hPE, map_pow]
        rw [← hlim]
        exact hcomplex.congr' hEqfun
      simpa [hxk, Function.comp_def] using
        (Complex.continuous_re.tendsto (φ.expectation (P ^ (2 * k)))).comp hinter
    have hboundn : ∀ n, ((ψ n).expectation (Pn n ^ (2 * k))).re ≤ ‖Pn n‖ ^ (2 * k) := by
      intro n
      have hnonneg : 0 ≤ Pn n ^ (2 * k) := pow_even_nonneg (hPn n) k
      calc ((ψ n).expectation (Pn n ^ (2 * k))).re
          ≤ ‖Pn n ^ (2 * k)‖ := state_re_le_norm (ψ n) hnonneg
        _ = ‖Pn n‖ ^ (2 * k) := norm_pow_even (hPn n) hk0
    filter_upwards [hmom_re.eventually (eventually_gt_nhds hxkgt)] with n hn
    have hle := hboundn n
    have hlt : (‖P‖ - ε) ^ (2 * k) < ‖Pn n‖ ^ (2 * k) := lt_of_lt_of_le hn hle
    have hfinal : ‖P‖ - ε < ‖Pn n‖ :=
      lt_of_pow_lt_pow_left₀ (2 * k) (norm_nonneg (Pn n)) hlt
    simpa [P, Pn] using hfinal.le
  · have hneg : ‖P‖ - ε ≤ 0 := by linarith
    filter_upwards with n
    exact hneg.trans (norm_nonneg (Pn n))

/-- **Conditional operator-norm transfer.**  One-sided spectral inclusion for fixed
pencils (H1), word-moment convergence (H2), the no-outlier upper bound and the
uniform bound give `‖P(X n)‖ → ‖P(x)‖`.  No norm convergence is assumed. -/
theorem tendsto_norm_of_word_moments
    (X : ℕ → I → B) (x : I → B)
    (hX : ∀ n i, star (X n i) = X n i) (hx : ∀ i, star (x i) = x i)
    (ψ : ℕ → FreeProbability.StarProbabilitySpace B)
    (φ : FreeProbability.StarProbabilitySpace B)
    (hH2 : WordMomentConvergence ψ φ X x)
    (hfaith : FreeProbability.IsFaithful φ.toProbabilitySpace)
    (C : B) (wds : κ → List I) (coeff : κ → B)
    (hPn : ∀ n, IsSelfAdjoint (wordPolyEvalC C (X n) wds coeff))
    (hPlim : IsSelfAdjoint (wordPolyEvalC C x wds coeff))
    (hNoOutlier : ∀ ε > 0, ∀ᶠ n in atTop,
      ‖wordPolyEvalC C (X n) wds coeff‖ ≤ ‖wordPolyEvalC C x wds coeff‖ + ε) :
    Tendsto (fun n => ‖wordPolyEvalC C (X n) wds coeff‖) atTop
      (𝓝 ‖wordPolyEvalC C x wds coeff‖) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    have hε : 0 < (‖wordPolyEvalC C x wds coeff‖ - a) / 2 := by linarith
    filter_upwards [eventually_norm_ge_of_word_moments X x hX hx ψ φ hH2 hfaith
      C wds coeff hPn hPlim hε] with n hn
    have hmid : a < ‖wordPolyEvalC C x wds coeff‖
        - (‖wordPolyEvalC C x wds coeff‖ - a) / 2 := by linarith
    exact lt_of_lt_of_le hmid hn
  · intro b hb
    have hε : 0 < (b - ‖wordPolyEvalC C x wds coeff‖) / 2 := by linarith
    filter_upwards [hNoOutlier ((b - ‖wordPolyEvalC C x wds coeff‖) / 2) hε] with n hn
    have hmid : ‖wordPolyEvalC C x wds coeff‖
        + (b - ‖wordPolyEvalC C x wds coeff‖) / 2 < b := by linarith
    exact lt_of_le_of_lt hn hmid


/-- **From spectral inclusion and a uniform bound to the no-outlier upper bound.**
This is the compactness extraction: a sequence of eigenvalues attaining `±‖P(X n)‖`
is bounded, hence has a convergent subsequence, and `no_outlier_of_spectral_inclusion`
contradicts a limit outside `[-‖P(x)‖, ‖P(x)‖]`. -/
theorem noOutlierOfSpectralInclusion
    (x : I → B) (X : ℕ → I → B) (wds : κ → List I) (coeff : κ → B)
    {C : B} (hC : IsSelfAdjoint C)
    (hH1 : SpectralInclusion x X wds coeff C)
    (hPn : ∀ n, IsSelfAdjoint (wordPolyEvalC C (X n) wds coeff))
    {Rb : ℝ} (hB : ∀ᶠ n in atTop,
      ‖wordPolyEvalC C (X n) wds coeff‖ ≤ Rb) :
    ∀ ε > 0, ∀ᶠ n in atTop,
      ‖wordPolyEvalC C (X n) wds coeff‖
        ≤ ‖wordPolyEvalC C x wds coeff‖ + ε := by
  classical
  intro ε hε
  by_contra h
  rw [Filter.not_eventually] at h
  have hfreq : ∃ᶠ n in atTop,
      ‖wordPolyEvalC C x wds coeff‖ + ε
        < ‖wordPolyEvalC C (X n) wds coeff‖ := by
    exact h.mono fun n hn => not_le.mp hn
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hB
  have hex : ∀ N, ∃ n, N ≤ n ∧
      ‖wordPolyEvalC C x wds coeff‖ + ε
        < ‖wordPolyEvalC C (X n) wds coeff‖ := fun N =>
    frequently_atTop.1 hfreq N
  choose m hm_ge hm_gt using hex
  let P : ℕ → B := fun n => wordPolyEvalC C (X n) wds coeff
  let z : ℕ → ℝ := fun n => if ‖P n‖ ∈ spectrum ℝ (P n) then ‖P n‖ else -‖P n‖
  have hz : ∀ n, z n ∈ spectrum ℝ (P n) := by
    intro n
    by_cases h : ‖P n‖ ∈ spectrum ℝ (P n)
    · simp [z, h]
    · rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum (P n) (hPn n) with hpos | hneg
      · exact absurd hpos h
      · simpa [z, h] using hneg
  have hz_abs : ∀ n, |z n| = ‖P n‖ := by
    intro n
    by_cases h : ‖P n‖ ∈ spectrum ℝ (P n)
    · simp [z, h, abs_of_nonneg (norm_nonneg _)]
    · simp [z, h, abs_of_nonneg (norm_nonneg _)]
  let zs : ℕ → ℝ := fun k => z (m (k + N0))
  have hmem : ∀ k, zs k ∈ Set.Icc (-Rb) Rb := by
    intro k
    have hb := hN0 (m (k + N0)) (le_trans (Nat.le_add_left N0 k) (hm_ge (k + N0)))
    have hle : |zs k| ≤ Rb := by
      rw [show zs k = z (m (k + N0)) from rfl, hz_abs]
      exact hb
    exact abs_le.mp hle
  obtain ⟨a, ha_mem, φ, hφ, hconv⟩ :=
    IsCompact.tendsto_subseq isCompact_Icc (x := zs) hmem
  have hzs : ∀ k, zs (φ k) ∈ spectrum ℝ
      (wordPolyEvalC C (X (m (φ k + N0))) wds coeff) := fun k => by
    simpa [P, zs] using hz (m (φ k + N0))
  have hout : ‖wordPolyEvalC C x wds coeff‖ < |a| := by
    have hlow : ∀ k, ‖wordPolyEvalC C x wds coeff‖ + ε ≤ |zs (φ k)| := by
      intro k
      rw [show zs (φ k) = z (m (φ k + N0)) from rfl, hz_abs]
      exact (hm_gt (φ k + N0)).le
    have habs : Tendsto (fun k => |zs (φ k)|) atTop (𝓝 |a|) := hconv.abs
    have hle : ‖wordPolyEvalC C x wds coeff‖ + ε ≤ |a| :=
      le_of_tendsto_of_tendsto tendsto_const_nhds habs (Eventually.of_forall hlow)
    linarith
  have hH1sub : SpectralInclusion x (fun k => X (m (φ k + N0))) wds coeff C := by
    intro z0 ε0 hε0
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hH1 z0 ε0 hε0)
    exact eventually_atTop.2 ⟨N, fun k hk => by
      have hkN : k ≤ m (φ k + N0) := by
        have h1 : k ≤ φ k := hφ.id_le k
        have h2 : φ k + N0 ≤ m (φ k + N0) := hm_ge (φ k + N0)
        omega
      exact hN _ (le_trans hk hkN)⟩
  exact no_outlier_of_spectral_inclusion x (fun k => X (m (φ k + N0))) wds coeff
    hC hH1sub (fun k => hzs k) hconv hout

/-- **Combined conditional operator-norm transfer.**  One-sided spectral inclusion
for fixed pencils (H1), word-moment convergence (H2), a faithful state, self-adjoint
evaluated polynomials and an explicit uniform operator-norm bound imply
`‖P(X n)‖ → ‖P(x)‖`. -/
theorem tendsto_norm_of_spectral_inclusion_and_word_moments
    (x : I → B) (X : ℕ → I → B) (wds : κ → List I) (coeff : κ → B)
    {C : B} (hC : IsSelfAdjoint C)
    (hH1 : SpectralInclusion x X wds coeff C)
    (hX : ∀ n i, star (X n i) = X n i) (hx : ∀ i, star (x i) = x i)
    (ψ : ℕ → FreeProbability.StarProbabilitySpace B)
    (φ : FreeProbability.StarProbabilitySpace B)
    (hH2 : WordMomentConvergence ψ φ X x)
    (hfaith : FreeProbability.IsFaithful φ.toProbabilitySpace)
    (hPn : ∀ n, IsSelfAdjoint (wordPolyEvalC C (X n) wds coeff))
    (hPlim : IsSelfAdjoint (wordPolyEvalC C x wds coeff))
    {Rb : ℝ} (hB : ∀ᶠ n in atTop,
      ‖wordPolyEvalC C (X n) wds coeff‖ ≤ Rb) :
    Tendsto (fun n => ‖wordPolyEvalC C (X n) wds coeff‖) atTop
      (𝓝 ‖wordPolyEvalC C x wds coeff‖) :=
  tendsto_norm_of_word_moments X x hX hx ψ φ hH2 hfaith C wds coeff hPn hPlim
    (noOutlierOfSpectralInclusion x X wds coeff hC hH1 hPn hB)


end GUEStrongConvergence
