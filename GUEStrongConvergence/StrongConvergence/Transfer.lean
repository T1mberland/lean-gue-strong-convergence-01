/-
# Abstract norm transfer across varying C⋆-algebras

This file isolates the dimension-independent analytic core of the strong-convergence
transfer.  The approximating elements `P n` live in *varying* C⋆-algebras `B n`
(e.g. `M_N(ℂ)`), while the limit `Pinf` lives in a possibly different C⋆-algebra `Binf`
(e.g. the semicircular algebra).  No common ambient algebra is assumed.

The two inputs are exactly the outputs of the two halves of the deterministic
reduction:

* `hmom`: convergence of all even moments of `P n` against the state `ψ n` to the
  corresponding moments of `Pinf` against `φ`;
* `hupper`: the one-sided no-outlier upper bound.

The lower bound is supplied by the faithful moment-norm formula applied to `φ`.
-/
import GUEStrongConvergence.StrongConvergence.FromPencils

namespace GUEStrongConvergence

open Filter
open scoped Topology ComplexOrder

/-- **Lower bound across varying algebras.**  Even-moment convergence plus a
faithful limit state gives `‖Pinf‖ - ε ≤ ‖P n‖` eventually. -/
theorem eventually_norm_ge_of_moment_convergence
    {B : ℕ → Type*} [∀ n, CStarAlgebra (B n)] [∀ n, Nontrivial (B n)]
    [∀ n, PartialOrder (B n)] [∀ n, StarOrderedRing (B n)]
    {Binf : Type*} [CStarAlgebra Binf] [Nontrivial Binf] [PartialOrder Binf]
    [StarOrderedRing Binf]
    (P : ∀ n, B n) (Pinf : Binf)
    (hPs : ∀ n, IsSelfAdjoint (P n)) (hPinfs : IsSelfAdjoint Pinf)
    (ψ : ∀ n, FreeProbability.StarProbabilitySpace (B n))
    (φ : FreeProbability.StarProbabilitySpace Binf)
    (hφ : FreeProbability.IsFaithful φ.toProbabilitySpace)
    (hmom : ∀ k, Tendsto
      (fun n => ((ψ n).expectation ((P n) ^ (2 * k))).re) atTop
      (𝓝 ((φ.expectation (Pinf ^ (2 * k))).re)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ‖Pinf‖ - ε ≤ ‖P n‖ := by
  by_cases hpos : 0 < ‖Pinf‖ - ε
  · have hroot := (tendsto_expectation_pow_rpow_eq_norm φ hφ hPinfs).eventually
      (eventually_ge_nhds (show ‖Pinf‖ - ε / 2 < ‖Pinf‖ by linarith))
    have hk1 : ∀ᶠ k : ℕ in atTop, 1 ≤ k := eventually_ge_atTop 1
    obtain ⟨k, hrootk, hkge⟩ := (hroot.and hk1).exists
    have hk0 : k ≠ 0 := by omega
    have hk2 : 2 * k ≠ 0 := by omega
    set xk : ℝ := (φ.expectation (Pinf ^ (2 * k))).re with hxk
    have hxk_nonneg : 0 ≤ xk := by
      rw [hxk]
      simpa using (φ.expectation_nonneg (pow_even_nonneg hPinfs k)).1
    have hrootk' : ‖Pinf‖ - ε / 2 ≤ xk ^ ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) := by
      simpa [hxk] using hrootk
    have hroot_pow : (‖Pinf‖ - ε / 2) ^ (2 * k) ≤ xk := by
      have hbase : 0 ≤ ‖Pinf‖ - ε / 2 := by linarith
      calc (‖Pinf‖ - ε / 2) ^ (2 * k)
          ≤ ((xk ^ ((1 : ℝ) / ((2 * k : ℕ) : ℝ))) ^ (2 * k)) := by
            exact pow_le_pow_left₀ hbase hrootk' (2 * k)
        _ = xk := by
            have h2k : ((2 * k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hk2
            rw [← Real.rpow_natCast (xk ^ ((1 : ℝ) / ((2 * k : ℕ) : ℝ))) (2 * k),
              ← Real.rpow_mul hxk_nonneg]
            rw [mul_comm, one_div, mul_inv_cancel₀ h2k, Real.rpow_one]
    have hxkgt : (‖Pinf‖ - ε) ^ (2 * k) < xk := by
      have hlt : ‖Pinf‖ - ε < ‖Pinf‖ - ε / 2 := by linarith
      exact lt_of_lt_of_le (pow_lt_pow_left₀ hlt hpos.le hk2) hroot_pow
    have hmom_re : Tendsto
        (fun n => ((ψ n).expectation ((P n) ^ (2 * k))).re) atTop (𝓝 xk) := by
      simpa [hxk] using hmom k
    have hboundn : ∀ n,
        ((ψ n).expectation ((P n) ^ (2 * k))).re ≤ ‖P n‖ ^ (2 * k) := by
      intro n
      have hnonneg : 0 ≤ (P n) ^ (2 * k) := pow_even_nonneg (hPs n) k
      calc ((ψ n).expectation ((P n) ^ (2 * k))).re
          ≤ ‖(P n) ^ (2 * k)‖ := state_re_le_norm (ψ n) hnonneg
        _ = ‖P n‖ ^ (2 * k) := norm_pow_even (hPs n) hk0
    filter_upwards [hmom_re.eventually (eventually_gt_nhds hxkgt)] with n hn
    have hle := hboundn n
    have hlt : (‖Pinf‖ - ε) ^ (2 * k) < ‖P n‖ ^ (2 * k) := lt_of_lt_of_le hn hle
    have hfinal : ‖Pinf‖ - ε < ‖P n‖ :=
      lt_of_pow_lt_pow_left₀ (2 * k) (norm_nonneg (P n)) hlt
    exact hfinal.le
  · have hneg : ‖Pinf‖ - ε ≤ 0 := by linarith
    filter_upwards with n
    exact hneg.trans (norm_nonneg (P n))

/-- **Abstract norm transfer across varying C⋆-algebras.**  Even-moment
convergence for self-adjoint elements, a faithful limit state and the one-sided
no-outlier upper bound imply `‖P n‖ → ‖Pinf‖`. -/
theorem tendsto_norm_of_moment_convergence
    {B : ℕ → Type*} [∀ n, CStarAlgebra (B n)] [∀ n, Nontrivial (B n)]
    [∀ n, PartialOrder (B n)] [∀ n, StarOrderedRing (B n)]
    {Binf : Type*} [CStarAlgebra Binf] [Nontrivial Binf] [PartialOrder Binf]
    [StarOrderedRing Binf]
    (P : ∀ n, B n) (Pinf : Binf)
    (hPs : ∀ n, IsSelfAdjoint (P n)) (hPinfs : IsSelfAdjoint Pinf)
    (ψ : ∀ n, FreeProbability.StarProbabilitySpace (B n))
    (φ : FreeProbability.StarProbabilitySpace Binf)
    (hφ : FreeProbability.IsFaithful φ.toProbabilitySpace)
    (hmom : ∀ k, Tendsto
      (fun n => ((ψ n).expectation ((P n) ^ (2 * k))).re) atTop
      (𝓝 ((φ.expectation (Pinf ^ (2 * k))).re)))
    (hupper : ∀ ε > 0, ∀ᶠ n in atTop, ‖P n‖ ≤ ‖Pinf‖ + ε) :
    Tendsto (fun n => ‖P n‖) atTop (𝓝 ‖Pinf‖) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    have hε : 0 < (‖Pinf‖ - a) / 2 := by linarith
    filter_upwards [eventually_norm_ge_of_moment_convergence P Pinf hPs hPinfs ψ φ hφ
      hmom hε] with n hn
    have hmid : a < ‖Pinf‖ - (‖Pinf‖ - a) / 2 := by linarith
    exact lt_of_lt_of_le hmid hn
  · intro b hb
    have hε : 0 < (b - ‖Pinf‖) / 2 := by linarith
    filter_upwards [hupper _ hε] with n hn
    have hmid : ‖Pinf‖ + (b - ‖Pinf‖) / 2 < b := by linarith
    exact lt_of_le_of_lt hn hmid

/-- **Family spectral inclusion (H1) for varying algebras.**  Word/coefficient data
are allowed to vary in the approximating algebra; the limit data live in `Binf`.
The same word list `wds` is used on both sides (the compatibility assumption). -/
def SpectralFamilyInclusion
    {B : ℕ → Type*} [∀ n, CStarAlgebra (B n)] [∀ n, Nontrivial (B n)]
    [∀ n, PartialOrder (B n)] [∀ n, StarOrderedRing (B n)]
    {Binf : Type*} [CStarAlgebra Binf] [Nontrivial Binf] [PartialOrder Binf]
    [StarOrderedRing Binf]
    {I κ : Type*} [Fintype κ] [DecidableEq κ]
    (x : I → Binf) (X : ∀ n, I → B n) (wds : κ → List I)
    (coeffn : ∀ n, κ → B n) (coeffinf : κ → Binf)
    (Cn : ∀ n, B n) (Cinf : Binf) : Prop :=
  ∀ z : ℝ, ∀ ε > 0, ∀ᶠ n in atTop,
    ∀ a ∈ spectrum ℝ (penLCS (X n) wds (coeffn n) (Cn n) z),
      ∃ b ∈ spectrum ℝ (penLCS x wds coeffinf Cinf z), |a - b| ≤ ε

/-- **No-outlier contradiction for varying algebras.** -/
theorem noOutlier_of_spectral_family_inclusion
    {B : ℕ → Type*} [∀ n, CStarAlgebra (B n)] [∀ n, Nontrivial (B n)]
    [∀ n, PartialOrder (B n)] [∀ n, StarOrderedRing (B n)]
    {Binf : Type*} [CStarAlgebra Binf] [Nontrivial Binf] [PartialOrder Binf]
    [StarOrderedRing Binf]
    {I κ : Type*} [Fintype κ] [DecidableEq κ]
    (x : I → Binf) (X : ∀ n, I → B n) (wds : κ → List I)
    (coeffn : ∀ n, κ → B n) (coeffinf : κ → Binf)
    (Cn : ∀ n, B n) (Cinf : Binf)
    (hCn : ∀ n, IsSelfAdjoint (Cn n)) (hCinf : IsSelfAdjoint Cinf)
    (hH1 : SpectralFamilyInclusion x X wds coeffn coeffinf Cn Cinf)
    {zs : ℕ → ℝ}
    (hzs : ∀ n, zs n ∈ spectrum ℝ
      (wordPolyEvalC (Cn n) (X n) wds (coeffn n)))
    {z : ℝ} (hzt : Tendsto zs atTop (𝓝 z))
    (hout : ‖wordPolyEvalC Cinf x wds coeffinf‖ < |z|) : False := by
  let P : Binf := wordPolyEvalC Cinf x wds coeffinf
  have hPunit : IsUnit (((z : ℂ) • (1 : Binf)) - P) := by
    by_contra hnot
    have hmem : (z : ℂ) ∈ spectrum ℂ P := by
      rw [spectrum, Set.mem_compl_iff, spectrum.mem_resolventSet_iff]
      simpa [Algebra.algebraMap_eq_smul_one] using hnot
    have hle : ‖(z : ℂ)‖ ≤ ‖P‖ := spectrum.norm_le_norm_of_mem hmem
    have hnorm : ‖(z : ℂ)‖ = |z| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm] at hle
    linarith
  have hL0 : IsUnit (penLCS x wds coeffinf Cinf z) :=
    (penLCS_isUnit_iff x wds coeffinf Cinf z).mpr hPunit
  set K : ℝ := ‖Ring.inverse (penLCS x wds coeffinf Cinf z)‖ with hK
  have hKpos : 0 < K := by
    have hne : Ring.inverse (penLCS x wds coeffinf Cinf z) ≠ 0 := by
      intro h0
      have h1 := Ring.mul_inverse_cancel
        (penLCS x wds coeffinf Cinf z) hL0
      rw [h0, mul_zero] at h1
      exact zero_ne_one h1
    exact norm_pos_iff.mpr hne
  have hgap0 : ∀ a ∈ spectrum ℂ (penLCS x wds coeffinf Cinf z),
      K⁻¹ ≤ ‖a‖ := by
    have h := spectrum_gap_of_inverse_norm hL0
    simpa [hK] using h
  set ε : ℝ := K⁻¹ / 4 with hε
  have hεpos : 0 < ε := by positivity
  have hH1e : ∀ᶠ n in atTop,
      ∀ a ∈ spectrum ℝ (penLCS (X n) wds (coeffn n) (Cn n) z),
        ∃ b ∈ spectrum ℝ (penLCS x wds coeffinf Cinf z),
          |a - b| ≤ ε :=
    hH1 z ε hεpos
  have hzt' : ∀ᶠ n in atTop, |zs n - z| < K⁻¹ / 4 := by
    have h0 : Tendsto (fun n => zs n - z) atTop (𝓝 0) := by
      simpa using hzt.sub_const z
    have h1 : Tendsto (fun n => |zs n - z|) atTop (𝓝 0) := by
      simpa using h0.abs
    exact h1.eventually (gt_mem_nhds hεpos)
  obtain ⟨n, hspec, hclose⟩ := (hH1e.and hzt').exists
  have hnotn : ¬ IsUnit (((zs n : ℂ) • (1 : B n)) -
      wordPolyEvalC (Cn n) (X n) wds (coeffn n)) :=
    not_isUnit_of_mem_spectrum_real (hzs n)
  have hLnot : ¬ IsUnit (penLCS (X n) wds (coeffn n) (Cn n) (zs n)) := by
    intro hu
    exact hnotn ((penLCS_isUnit_iff (X n) wds (coeffn n)
      (Cn n) (zs n)).mp hu)
  have hsa : IsSelfAdjoint (penLCS (X n) wds (coeffn n) (Cn n) z) :=
    penLCS_isSelfAdjoint (X n) wds (coeffn n) (hCn n) z
  have hgapn : ∀ a ∈ spectrum ℂ (penLCS (X n) wds (coeffn n) (Cn n) z),
      3 * K⁻¹ / 4 ≤ ‖a‖ := by
    intro a ha
    have him : a.im = 0 := hsa.im_eq_zero_of_mem_spectrum ha
    have hEq : ((a.re : ℂ)) = a := by
      apply Complex.ext
      · rfl
      · simpa using him.symm
    have hre : a.re ∈ spectrum ℝ
        (penLCS (X n) wds (coeffn n) (Cn n) z) := by
      have hCmem : ((a.re : ℂ)) ∈ spectrum ℂ
          (penLCS (X n) wds (coeffn n) (Cn n) z) := by
        rwa [hEq]
      exact (spectrum.algebraMap_mem_iff ℂ).mp hCmem
    obtain ⟨b, hb, hdist⟩ := hspec a.re hre
    have hbC : (b : ℂ) ∈ spectrum ℂ
        (penLCS x wds coeffinf Cinf z) :=
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
  have h0not : (0 : ℂ) ∉ spectrum ℂ
      (penLCS (X n) wds (coeffn n) (Cn n) z) := by
    intro h0
    have h := hgapn 0 h0
    have hKinv : 0 < K⁻¹ := inv_pos.mpr hKpos
    simp at h
    linarith
  have hunitn : IsUnit (penLCS (X n) wds (coeffn n) (Cn n) z) := by
    have hres : (0 : ℂ) ∈ resolventSet ℂ
        (penLCS (X n) wds (coeffn n) (Cn n) z) := by
      simpa [spectrum] using h0not
    have hu := spectrum.mem_resolventSet_iff.mp hres
    have hu' : IsUnit (-(penLCS (X n) wds (coeffn n) (Cn n) z)) := by
      simpa [Algebra.algebraMap_eq_smul_one] using hu
    simpa using hu'.neg
  have hδpos : 0 < 3 * K⁻¹ / 4 := by positivity
  have hinv : ‖Ring.inverse (penLCS (X n) wds (coeffn n) (Cn n) z)‖
      ≤ (3 * K⁻¹ / 4)⁻¹ :=
    norm_ringInverse_le_of_spectrum_gap hsa hδpos hunitn hgapn
  let Lz : CStarMatrix (PenIdx wds) (PenIdx wds) (B n) :=
    penLCS (X n) wds (coeffn n) (Cn n) z
  let Lzn : CStarMatrix (PenIdx wds) (PenIdx wds) (B n) :=
    penLCS (X n) wds (coeffn n) (Cn n) (zs n)
  have hΔ0 := @penLCS_sub_norm_le (B n) _ _ _ _ I κ _ _ (X n) wds (coeffn n) (Cn n) (zs n) z
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

/-- **Compactness extraction for varying algebras**: spectral family inclusion and a
uniform bound imply the one-sided no-outlier upper bound. -/
theorem noOutlierOfSpectralFamilyInclusion
    {B : ℕ → Type*} [∀ n, CStarAlgebra (B n)] [∀ n, Nontrivial (B n)]
    [∀ n, PartialOrder (B n)] [∀ n, StarOrderedRing (B n)]
    {Binf : Type*} [CStarAlgebra Binf] [Nontrivial Binf] [PartialOrder Binf]
    [StarOrderedRing Binf]
    {I κ : Type*} [Fintype κ] [DecidableEq κ]
    (x : I → Binf) (X : ∀ n, I → B n) (wds : κ → List I)
    (coeffn : ∀ n, κ → B n) (coeffinf : κ → Binf)
    (Cn : ∀ n, B n) (Cinf : Binf)
    (hCn : ∀ n, IsSelfAdjoint (Cn n)) (hCinf : IsSelfAdjoint Cinf)
    (hH1 : SpectralFamilyInclusion x X wds coeffn coeffinf Cn Cinf)
    (hPn : ∀ n, IsSelfAdjoint (wordPolyEvalC (Cn n) (X n) wds (coeffn n)))
    {Rb : ℝ} (hB : ∀ᶠ n in atTop,
      ‖wordPolyEvalC (Cn n) (X n) wds (coeffn n)‖ ≤ Rb) :
    ∀ ε > 0, ∀ᶠ n in atTop,
      ‖wordPolyEvalC (Cn n) (X n) wds (coeffn n)‖
        ≤ ‖wordPolyEvalC Cinf x wds coeffinf‖ + ε := by
  classical
  intro ε hε
  by_contra h
  rw [Filter.not_eventually] at h
  have hfreq : ∃ᶠ n in atTop,
      ‖wordPolyEvalC Cinf x wds coeffinf‖ + ε
        < ‖wordPolyEvalC (Cn n) (X n) wds (coeffn n)‖ := by
    exact h.mono fun n hn => not_le.mp hn
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hB
  have hex : ∀ N, ∃ n, N ≤ n ∧
      ‖wordPolyEvalC Cinf x wds coeffinf‖ + ε
        < ‖wordPolyEvalC (Cn n) (X n) wds (coeffn n)‖ := fun N =>
    frequently_atTop.1 hfreq N
  choose m hm_ge hm_gt using hex
  let P : ∀ n, B n := fun n => wordPolyEvalC (Cn n) (X n) wds (coeffn n)
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
      (wordPolyEvalC (Cn (m (φ k + N0))) (X (m (φ k + N0))) wds
        (coeffn (m (φ k + N0)))) := fun k => by
    simpa [P, zs] using hz (m (φ k + N0))
  have hout : ‖wordPolyEvalC Cinf x wds coeffinf‖ < |a| := by
    have hlow : ∀ k, ‖wordPolyEvalC Cinf x wds coeffinf‖ + ε ≤ |zs (φ k)| := by
      intro k
      rw [show zs (φ k) = z (m (φ k + N0)) from rfl, hz_abs]
      exact (hm_gt (φ k + N0)).le
    have habs : Tendsto (fun k => |zs (φ k)|) atTop (𝓝 |a|) := hconv.abs
    have hle : ‖wordPolyEvalC Cinf x wds coeffinf‖ + ε ≤ |a| :=
      le_of_tendsto_of_tendsto tendsto_const_nhds habs (Eventually.of_forall hlow)
    linarith
  have hH1sub : SpectralFamilyInclusion x (fun k => X (m (φ k + N0))) wds
      (fun k => coeffn (m (φ k + N0))) coeffinf
      (fun k => Cn (m (φ k + N0))) Cinf := by
    intro z0 ε0 hε0
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hH1 z0 ε0 hε0)
    exact eventually_atTop.2 ⟨N, fun k hk => by
      have hkN : k ≤ m (φ k + N0) := by
        have h1 : k ≤ φ k := hφ.id_le k
        have h2 : φ k + N0 ≤ m (φ k + N0) := hm_ge (φ k + N0)
        omega
      exact hN _ (le_trans hk hkN)⟩
  exact noOutlier_of_spectral_family_inclusion x (fun k => X (m (φ k + N0))) wds
    (fun k => coeffn (m (φ k + N0))) coeffinf (fun k => Cn (m (φ k + N0))) Cinf
    (fun k => hCn (m (φ k + N0))) hCinf hH1sub hzs hconv hout

/-- **Final conditional transfer for varying algebras.** -/
theorem tendsto_norm_of_spectral_family_and_moments
    {B : ℕ → Type*} [∀ n, CStarAlgebra (B n)] [∀ n, Nontrivial (B n)]
    [∀ n, PartialOrder (B n)] [∀ n, StarOrderedRing (B n)]
    {Binf : Type*} [CStarAlgebra Binf] [Nontrivial Binf] [PartialOrder Binf]
    [StarOrderedRing Binf]
    {I κ : Type*} [Fintype κ] [DecidableEq κ]
    (x : I → Binf) (X : ∀ n, I → B n) (wds : κ → List I)
    (coeffn : ∀ n, κ → B n) (coeffinf : κ → Binf)
    (Cn : ∀ n, B n) (Cinf : Binf)
    (hCn : ∀ n, IsSelfAdjoint (Cn n)) (hCinf : IsSelfAdjoint Cinf)
    (hH1 : SpectralFamilyInclusion x X wds coeffn coeffinf Cn Cinf)
    (ψ : ∀ n, FreeProbability.StarProbabilitySpace (B n))
    (φ : FreeProbability.StarProbabilitySpace Binf)
    (hφ : FreeProbability.IsFaithful φ.toProbabilitySpace)
    (hPn : ∀ n, IsSelfAdjoint (wordPolyEvalC (Cn n) (X n) wds (coeffn n)))
    (hPinf : IsSelfAdjoint (wordPolyEvalC Cinf x wds coeffinf))
    (hmom : ∀ k, Tendsto
      (fun n => ((ψ n).expectation
        ((wordPolyEvalC (Cn n) (X n) wds (coeffn n)) ^ (2 * k))).re) atTop
      (𝓝 ((φ.expectation
        ((wordPolyEvalC Cinf x wds coeffinf) ^ (2 * k))).re)))
    {Rb : ℝ} (hB : ∀ᶠ n in atTop,
      ‖wordPolyEvalC (Cn n) (X n) wds (coeffn n)‖ ≤ Rb) :
    Tendsto (fun n => ‖wordPolyEvalC (Cn n) (X n) wds (coeffn n)‖) atTop
      (𝓝 ‖wordPolyEvalC Cinf x wds coeffinf‖) :=
  tendsto_norm_of_moment_convergence
    (fun n => wordPolyEvalC (Cn n) (X n) wds (coeffn n))
    (wordPolyEvalC Cinf x wds coeffinf) hPn hPinf ψ φ hφ hmom
    (noOutlierOfSpectralFamilyInclusion x X wds coeffn coeffinf Cn Cinf
      hCn hCinf hH1 hPn hB)


end GUEStrongConvergence
