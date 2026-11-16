/-
# The operator/trace form of the Cauchy–Pompeiu representation

For a Hermitian matrix `H` and a `C²` compactly supported `f : ℝ → ℝ`, summing the scalar
identity `pompeiu_plane` over the eigenvalues of `H` gives

`Tr(f(H)) = (i/2π) ∫∫ ∂̄F(z) · Tr((z - H)⁻¹)`,

where `Tr((z - H)⁻¹)` is the eigenvalue sum `∑ i, (z - λᵢ)⁻¹` (`resolventTrace`).

## Main results

* `integrable_planeIntegrand` — the plane integrand is integrable on `ℝ × ℝ`;
* `integral_planeIntegrand_eq_iterated` — the two-dimensional integral is the iterated one;
* `resolventTrace` — the eigenvalue-sum resolvent trace;
* `trace_cfc_eq_plane_integral` — the trace form of the representation.
-/
import GUEStrongConvergence.Probability.HelfferSjostrand
import GUEStrongConvergence.Probability.LemmaVSmooth

open MeasureTheory Set Filter Topology Complex
open scoped Real NNReal ENNReal

namespace GUEStrongConvergence

variable {f : ℝ → ℝ}

/-! ## Integrability of the plane integrand on the whole plane -/

/-- The plane integrand vanishes outside any rectangle containing the support. -/
lemma planeIntegrand_eq_zero_of_not_mem_rect {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {X Y : ℝ} (hXpos : 0 < X)
    (hXsupp : ∀ z ∈ tsupport (almostAnalyticExtCut f), |z.re| < X)
    {p : ℝ × ℝ} (hp : p ∉ Set.Ioc (-X) X ×ˢ Set.Ioc (-Y) Y) (hY : 2 < Y) (lam : ℝ) :
    planeIntegrand f lam p = 0 := by
  rw [Set.mem_prod] at hp
  rcases not_and_or.mp hp with h | h
  · rw [Set.mem_Ioc, not_and_or] at h
    rcases h with h | h
    · rw [not_lt] at h
      have hre : X ≤ |(((p.1 : ℂ) + (p.2 : ℂ) * I)).re| := by
        rw [show (((p.1 : ℂ) + (p.2 : ℂ) * I)).re = p.1 from by simp,
          abs_of_nonpos (by linarith)]
        linarith
      exact planeIntegrand_eq_zero_of_notMem_tsupport hf
        (notMem_tsupport_of_le_abs_re hXsupp hre)
    · rw [not_le] at h
      have hre : X ≤ |(((p.1 : ℂ) + (p.2 : ℂ) * I)).re| := by
        rw [show (((p.1 : ℂ) + (p.2 : ℂ) * I)).re = p.1 from by simp,
          abs_of_pos (by linarith)]
        linarith
      exact planeIntegrand_eq_zero_of_notMem_tsupport hf
        (notMem_tsupport_of_le_abs_re hXsupp hre)
  · rw [Set.mem_Ioc, not_and_or] at h
    rcases h with h | h
    · rw [not_lt] at h
      have him : 2 < |(((p.1 : ℂ) + (p.2 : ℂ) * I)).im| := by
        rw [show (((p.1 : ℂ) + (p.2 : ℂ) * I)).im = p.2 from by simp,
          abs_of_nonpos (by linarith)]
        linarith
      exact planeIntegrand_eq_zero_of_notMem_tsupport hf
        (notMem_tsupport_almostAnalyticExtCut_of_lt_abs_im him)
    · rw [not_le] at h
      have him : 2 < |(((p.1 : ℂ) + (p.2 : ℂ) * I)).im| := by
        rw [show (((p.1 : ℂ) + (p.2 : ℂ) * I)).im = p.2 from by simp,
          abs_of_pos (by linarith)]
        linarith
      exact planeIntegrand_eq_zero_of_notMem_tsupport hf
        (notMem_tsupport_almostAnalyticExtCut_of_lt_abs_im him)

/-- The plane integrand is integrable on `ℝ × ℝ`. -/
lemma integrable_planeIntegrand {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (lam : ℝ) : Integrable (planeIntegrand f lam) (volume : Measure (ℝ × ℝ)) := by
  classical
  obtain ⟨X, hXpos, hXsupp⟩ : ∃ X : ℝ, 0 < X ∧
      ∀ z ∈ tsupport (almostAnalyticExtCut f), |z.re| < X := by
    have hKc : IsCompact (tsupport (almostAnalyticExtCut f)) :=
      hasCompactSupport_almostAnalyticExtCut hfc
    have hKr : IsCompact (Complex.re '' tsupport (almostAnalyticExtCut f)) :=
      hKc.image Complex.continuous_re
    obtain ⟨X₀, hX₀⟩ := hKr.exists_bound_of_continuousOn continuous_id.continuousOn
    refine ⟨max X₀ 0 + 1, by have := le_max_right X₀ 0; linarith, fun z hz => ?_⟩
    have h1 : ‖z.re‖ ≤ X₀ := hX₀ _ ⟨z, hz, rfl⟩
    have h2 : |z.re| ≤ X₀ := by simpa [Real.norm_eq_abs] using h1
    have h3 : X₀ ≤ max X₀ 0 := le_max_left _ _
    linarith
  set R : Set (ℝ × ℝ) := Set.Ioc (-X) X ×ˢ Set.Ioc (-3 : ℝ) 3 with hR
  have hmeas : MeasurableSet R := measurableSet_Ioc.prod measurableSet_Ioc
  have hrect : IntegrableOn (planeIntegrand f lam) R (volume : Measure (ℝ × ℝ)) :=
    integrableOn_planeIntegrand hf hfc lam (-X) X (-3) 3
  have hcompl : IntegrableOn (planeIntegrand f lam) Rᶜ (volume : Measure (ℝ × ℝ)) := by
    have hae : planeIntegrand f lam =ᵐ[volume.restrict Rᶜ] (0 : ℝ × ℝ → ℂ) := by
      filter_upwards [ae_restrict_mem hmeas.compl] with p hp
      exact planeIntegrand_eq_zero_of_not_mem_rect hf hXpos hXsupp hp (by norm_num) lam
    exact (integrable_zero (α := ℝ × ℝ) ℂ _).congr hae.symm
  have hunion : IntegrableOn (planeIntegrand f lam) (R ∪ Rᶜ) (volume : Measure (ℝ × ℝ)) :=
    hrect.union hcompl
  rwa [Set.union_compl_self, integrableOn_univ] at hunion

/-- The two-dimensional integral of the plane integrand is the iterated one. -/
lemma integral_planeIntegrand_eq_iterated {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (lam : ℝ) :
    (∫ p : ℝ × ℝ,
        pompeiuIntegrand (almostAnalyticExtCut f) (lam : ℂ) ((p.1 : ℂ) + (p.2 : ℂ) * I))
      = ∫ x : ℝ, ∫ y : ℝ,
          pompeiuIntegrand (almostAnalyticExtCut f) (lam : ℂ) ((x : ℂ) + (y : ℂ) * I) := by
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod (volume : Measure ℝ) from rfl]
  rw [integral_prod]
  exact integrable_planeIntegrand hf hfc lam

/-! ## The trace form -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The eigenvalue-sum resolvent trace of a Hermitian matrix. -/
noncomputable def resolventTrace (H : Matrix n n ℂ) (hH : H.IsHermitian) (z : ℂ) : ℂ :=
  ∑ i, (z - ((hH.eigenvalues i : ℝ) : ℂ))⁻¹

/-- Almost every point of the plane represents a complex number outside the spectrum. -/
lemma ae_not_eigenvalue (H : Matrix n n ℂ) (hH : H.IsHermitian) :
    ∀ᵐ p : ℝ × ℝ, ∀ i : n,
      ((p.1 : ℂ) + (p.2 : ℂ) * I) ≠ (((hH.eigenvalues i : ℝ)) : ℂ) := by
  classical
  have hfin : ({p : ℝ × ℝ | ∃ i : n,
      ((p.1 : ℂ) + (p.2 : ℂ) * I) = (((hH.eigenvalues i : ℝ)) : ℂ)}).Finite := by
    have him : ({p : ℝ × ℝ | ∃ i : n, p = (hH.eigenvalues i, 0)}).Finite := by
      simpa [Set.range, eq_comm] using
        (Set.finite_range (fun i : n => (hH.eigenvalues i, (0 : ℝ))))
    refine Set.Finite.subset him ?_
    rintro p ⟨i, hi⟩
    refine ⟨i, ?_⟩
    have h1 : p.2 = 0 := by
      have := congrArg Complex.im hi
      simpa using this
    have h2 : p.1 = hH.eigenvalues i := by
      have := congrArg Complex.re hi
      simpa using this
    exact Prod.ext h2 h1
  filter_upwards [(compl_mem_ae_iff).mpr (hfin.measure_zero (volume : Measure (ℝ × ℝ)))]
    with p hp
  intro i h
  exact hp ⟨i, h⟩

/-- **Trace form of the Cauchy–Pompeiu representation.**  Summing `pompeiu_plane` over the
eigenvalues of a Hermitian matrix gives
`Tr(f(H)) = (i/2π) ∫∫ ∂̄F(z) · Tr((z - H)⁻¹)`. -/
theorem trace_cfc_eq_plane_integral (H : Matrix n n ℂ) (hH : H.IsHermitian)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (hH.cfc f).trace =
      (I / (2 * (Real.pi : ℂ))) *
        ∫ p : ℝ × ℝ,
          dbarNum f ((p.1 : ℂ) + (p.2 : ℂ) * I) *
            resolventTrace H hH ((p.1 : ℂ) + (p.2 : ℂ) * I) := by
  classical
  rw [trace_cfc_eq_sum_eigenvalues_general H hH f]
  have hlam : ∀ i : n, ((f (hH.eigenvalues i) : ℝ) : ℂ) =
      (I / (2 * (Real.pi : ℂ))) *
        ∫ p : ℝ × ℝ,
          pompeiuIntegrand (almostAnalyticExtCut f) (((hH.eigenvalues i : ℝ)) : ℂ)
            ((p.1 : ℂ) + (p.2 : ℂ) * I) := by
    intro i
    rw [integral_planeIntegrand_eq_iterated hf hfc (hH.eigenvalues i)]
    exact pompeiu_plane hf hfc (hH.eigenvalues i)
  rw [Finset.sum_congr rfl (fun i _ => hlam i)]
  rw [← Finset.mul_sum]
  congr 1
  have hswap : (∑ i : n, ∫ p : ℝ × ℝ,
        pompeiuIntegrand (almostAnalyticExtCut f) (((hH.eigenvalues i : ℝ)) : ℂ)
          ((p.1 : ℂ) + (p.2 : ℂ) * I))
      = ∫ p : ℝ × ℝ, ∑ i : n,
          pompeiuIntegrand (almostAnalyticExtCut f) (((hH.eigenvalues i : ℝ)) : ℂ)
            ((p.1 : ℂ) + (p.2 : ℂ) * I) := by
    rw [integral_finsetSum]
    intro i _
    exact integrable_planeIntegrand hf hfc (hH.eigenvalues i)
  rw [hswap]
  refine integral_congr_ae ?_
  filter_upwards [ae_not_eigenvalue H hH] with p hne
  rw [resolventTrace, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rfl

/-! ## Identification with the matrix resolvent trace -/

section ResolventTrace

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The eigenvalue sum is the trace of the matrix resolvent.**  For a Hermitian `H` and `z`
outside the spectrum, `Tr((z - H)⁻¹) = ∑ i, (z - λᵢ)⁻¹`. -/
theorem resolventTrace_eq_trace_inv (H : Matrix n n ℂ) (hH : H.IsHermitian) (z : ℂ)
    (hz : ∀ i, z ≠ ((hH.eigenvalues i : ℝ) : ℂ)) :
    resolventTrace H hH z = Matrix.trace ((z • (1 : Matrix n n ℂ) - H)⁻¹) := by
  classical
  set U : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  set D : Matrix n n ℂ := Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) with hDdef
  have hUU : U * star U = 1 := Unitary.coe_mul_star_self _
  have hU'U : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUinv : U⁻¹ = star U := Matrix.inv_eq_right_inv hUU
  have hU'inv : (star U)⁻¹ = U := Matrix.inv_eq_right_inv hU'U
  have hspec : H = U * D * star U := by
    have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa [hUdef, hDdef, Matrix.diagonal, Function.comp_def] using h
  have hcong : U * (z • (1 : Matrix n n ℂ)) * star U = z • 1 := by
    rw [Matrix.mul_smul, Matrix.smul_mul, mul_one, hUU]
  have hzH : z • (1 : Matrix n n ℂ) - H = U * (z • (1 : Matrix n n ℂ) - D) * star U := by
    have h1 : U * (z • (1 : Matrix n n ℂ) - D) * star U
        = U * (z • (1 : Matrix n n ℂ)) * star U - U * D * star U := by
      rw [mul_sub, sub_mul]
    rw [h1, hcong, ← hspec]
  have hzD : z • (1 : Matrix n n ℂ) - D
      = Matrix.diagonal (fun i => z - ((hH.eigenvalues i : ℝ) : ℂ)) := by
    rw [Matrix.smul_one_eq_diagonal, hDdef, ← Matrix.diagonal_sub]
  have hdiag : (Matrix.diagonal (fun i => z - ((hH.eigenvalues i : ℝ) : ℂ)))⁻¹
      = Matrix.diagonal (fun i => (z - ((hH.eigenvalues i : ℝ) : ℂ))⁻¹) := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.diagonal_mul_diagonal]
    have hfun : (fun i => (z - ((hH.eigenvalues i : ℝ) : ℂ)) *
        (z - ((hH.eigenvalues i : ℝ) : ℂ))⁻¹) = fun _ => 1 := by
      funext i
      exact mul_inv_cancel₀ (sub_ne_zero.mpr (hz i))
    rw [hfun, Matrix.diagonal_one]
  have hinv : (z • (1 : Matrix n n ℂ) - H)⁻¹
      = U * (z • (1 : Matrix n n ℂ) - D)⁻¹ * star U := by
    rw [hzH, Matrix.mul_inv_rev, Matrix.mul_inv_rev, hUinv, hU'inv]
    noncomm_ring
  rw [hinv, show U = (↑hH.eigenvectorUnitary : Matrix n n ℂ) from rfl,
    show star U = star (↑hH.eigenvectorUnitary : Matrix n n ℂ) from rfl,
    trace_conj_unitary hH.eigenvectorUnitary, hzD, hdiag, Matrix.trace_diagonal]
  rfl

/-- **Trace form with the matrix resolvent.**  `Tr(f(H)) = (i/2π) ∫∫ ∂̄F(z) Tr((z - H)⁻¹)`. -/
theorem trace_cfc_eq_plane_integral_resolvent (H : Matrix n n ℂ) (hH : H.IsHermitian)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (hH.cfc f).trace =
      (I / (2 * (Real.pi : ℂ))) *
        ∫ p : ℝ × ℝ,
          dbarNum f ((p.1 : ℂ) + (p.2 : ℂ) * I) *
            Matrix.trace ((((p.1 : ℂ) + (p.2 : ℂ) * I)) • (1 : Matrix n n ℂ) - H)⁻¹ := by
  rw [trace_cfc_eq_plane_integral H hH hf hfc]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [ae_not_eigenvalue H hH] with p hne
  rw [resolventTrace_eq_trace_inv H hH _ (fun i => hne i)]

end ResolventTrace

end GUEStrongConvergence
