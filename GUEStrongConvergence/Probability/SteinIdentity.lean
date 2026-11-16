/-
# Coordinate Stein identity (Gaussian integration by parts in one coordinate)

This file proves the multivariable form of the Gaussian integration-by-parts identity used in
the HT05 master equation: on a product `ℝ × γ` of a real line carrying the standard Gaussian
density `ρ = gaussianPDFReal 0 1` with an arbitrary finite measure, integration by parts can be
performed in the Gaussian coordinate, uniformly in the other coordinates.

The statement is in the unnormalized (density) form

`∫ z, z.1 • (ρ z.1 • G z) = ∫ z, ρ z.1 • G' z`

against `volume.prod ν`, where `G'` differentiates `G` in the first coordinate. The proof
applies Fubini (`MeasureTheory.integral_prod_symm`) and then, for almost every `y`, the
one-dimensional algebra-valued identity `gaussian_integration_by_parts_density`.
-/
import GUEStrongConvergence.Probability.GaussianIBP

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace ENNReal NNReal Topology

namespace GUEStrongConvergence

noncomputable section

variable {γ : Type*} [MeasurableSpace γ] {ν : Measure γ} [SigmaFinite ν]

/-- Coordinate Stein identity on a product space: for a product of the standard Gaussian with
an arbitrary finite measure, integration by parts in the first coordinate. -/
theorem integral_fst_smul_prod
    {γ : Type*} [MeasurableSpace γ] {ν : Measure γ} [SigmaFinite ν]
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    {G G' : ℝ × γ → A}
    (hderiv : ∀ (a : ℝ) (y : γ), HasDerivAt (fun t => G (t, y)) (G' (a, y)) a)
    (hint₁ : Integrable (fun z : ℝ × γ => gaussianPDFReal 0 1 z.1 • G' z)
      ((volume : Measure ℝ).prod ν))
    (hint₂ : Integrable (fun z : ℝ × γ => z.1 • (gaussianPDFReal 0 1 z.1 • G z))
      ((volume : Measure ℝ).prod ν))
    (hbot : ∀ᵐ y ∂ν, Tendsto (fun t => gaussianPDFReal 0 1 t • G (t, y)) atBot (𝓝 0))
    (htop : ∀ᵐ y ∂ν, Tendsto (fun t => gaussianPDFReal 0 1 t • G (t, y)) atTop (𝓝 0)) :
    ∫ z, z.1 • (gaussianPDFReal 0 1 z.1 • G z) ∂((volume : Measure ℝ).prod ν)
      = ∫ z, gaussianPDFReal 0 1 z.1 • G' z ∂((volume : Measure ℝ).prod ν) := by
  rw [integral_prod_symm _ hint₂, integral_prod_symm _ hint₁]
  have h1ae := hint₁.prod_left_ae (μ := (volume : Measure ℝ)) (ν := ν)
  have h2ae := hint₂.prod_left_ae (μ := (volume : Measure ℝ)) (ν := ν)
  refine integral_congr_ae ?_
  filter_upwards [h1ae, h2ae, hbot, htop] with y hy1 hy2 hb ht
  exact gaussian_integration_by_parts_density (f := fun a => G (a, y)) (f' := fun a => G' (a, y))
    (fun a => hderiv a y) hy1 hy2 hb ht


lemma integral_prod_gaussianReal_eq_integral_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : ℝ × γ → E) :
    ∫ z, g z ∂((gaussianReal 0 1).prod ν)
      = ∫ z, gaussianPDFReal 0 1 z.1 • g z ∂((volume : Measure ℝ).prod ν) := by
  have hv : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  rw [gaussianReal_of_var_ne_zero (0 : ℝ) hv,
    MeasureTheory.prod_withDensity_left (measurable_gaussianPDF 0 1)]
  change ∫ z, g z ∂((volume : Measure ℝ).prod ν).withDensity (gaussianPDF 0 1 ∘ Prod.fst)
      = ∫ z, gaussianPDFReal 0 1 z.1 • g z ∂((volume : Measure ℝ).prod ν)
  rw [integral_withDensity_eq_integral_toReal_smul
    ((measurable_gaussianPDF (μ := 0) (v := 1)).comp measurable_fst)
    (by filter_upwards with z using gaussianPDF_lt_top (μ := 0) (v := 1) (x := z.1))]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  show ((gaussianPDF 0 1 ∘ Prod.fst) z).toReal • g z = gaussianPDFReal 0 1 z.1 • g z
  rw [Function.comp_apply, toReal_gaussianPDF]

/-- **Coordinate Stein identity in normalized form**: for `G` with derivative `G'` in the first
coordinate, `∫ z, z.1 • G z ∂((gaussianReal 0 1).prod ν) = ∫ z, G' z ∂((gaussianReal 0 1).prod ν)`. -/
theorem integral_fst_smul_prod_gaussianReal
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    {G G' : ℝ × γ → A}
    (hderiv : ∀ (a : ℝ) (y : γ), HasDerivAt (fun t => G (t, y)) (G' (a, y)) a)
    (hint₁ : Integrable (fun z : ℝ × γ => gaussianPDFReal 0 1 z.1 • G' z)
      ((volume : Measure ℝ).prod ν))
    (hint₂ : Integrable (fun z : ℝ × γ => z.1 • (gaussianPDFReal 0 1 z.1 • G z))
      ((volume : Measure ℝ).prod ν))
    (hbot : ∀ᵐ y ∂ν, Tendsto (fun t => gaussianPDFReal 0 1 t • G (t, y)) atBot (𝓝 0))
    (htop : ∀ᵐ y ∂ν, Tendsto (fun t => gaussianPDFReal 0 1 t • G (t, y)) atTop (𝓝 0)) :
    ∫ z, z.1 • G z ∂((gaussianReal 0 1).prod ν)
      = ∫ z, G' z ∂((gaussianReal 0 1).prod ν) := by
  rw [integral_prod_gaussianReal_eq_integral_smul (E := A),
    integral_prod_gaussianReal_eq_integral_smul (E := A)]
  rw [show (∫ z, gaussianPDFReal 0 1 z.1 • (z.1 • G z) ∂((volume : Measure ℝ).prod ν))
      = ∫ z, z.1 • (gaussianPDFReal 0 1 z.1 • G z) ∂((volume : Measure ℝ).prod ν) from by
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    show gaussianPDFReal 0 1 z.1 • z.1 • G z = z.1 • (gaussianPDFReal 0 1 z.1 • G z)
    rw [smul_smul, smul_smul, mul_comm]]
  exact integral_fst_smul_prod hderiv hint₁ hint₂ hbot htop

/-- Coordinate IBP with the Gaussian density in the *second* factor of a product, in
unnormalized (density) form. -/
theorem integral_snd_smul_prod
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    {G G' : γ × ℝ → A}
    (hderiv : ∀ (y : γ) (a : ℝ), HasDerivAt (fun t => G (y, t)) (G' (y, a)) a)
    (hint₁ : Integrable (fun z : γ × ℝ => gaussianPDFReal 0 1 z.2 • G' z)
      (ν.prod (volume : Measure ℝ)))
    (hint₂ : Integrable (fun z : γ × ℝ => z.2 • (gaussianPDFReal 0 1 z.2 • G z))
      (ν.prod (volume : Measure ℝ)))
    (hbot : ∀ᵐ y ∂ν, Tendsto (fun t => gaussianPDFReal 0 1 t • G (y, t)) atBot (𝓝 0))
    (htop : ∀ᵐ y ∂ν, Tendsto (fun t => gaussianPDFReal 0 1 t • G (y, t)) atTop (𝓝 0)) :
    ∫ z, z.2 • (gaussianPDFReal 0 1 z.2 • G z) ∂(ν.prod (volume : Measure ℝ))
      = ∫ z, gaussianPDFReal 0 1 z.2 • G' z ∂(ν.prod (volume : Measure ℝ)) := by
  rw [integral_prod _ hint₂, integral_prod _ hint₁]
  have h1ae := hint₁.prod_right_ae (μ := ν) (ν := (volume : Measure ℝ))
  have h2ae := hint₂.prod_right_ae (μ := ν) (ν := (volume : Measure ℝ))
  refine integral_congr_ae ?_
  filter_upwards [h1ae, h2ae, hbot, htop] with y hy1 hy2 hb ht
  exact gaussian_integration_by_parts_density (f := fun a => G (y, a))
    (f' := fun a => G' (y, a)) (fun a => hderiv y a) hy1 hy2 hb ht

/-- Density transfer with the Gaussian in the second factor:
`∫ z, g z ∂(ν.prod (gaussianReal 0 1)) = ∫ z, ρ z.2 • g z ∂(ν.prod volume)`. -/
lemma integral_prod_gaussianReal_right_eq_integral_smul
    {γ : Type*} [MeasurableSpace γ] (ν : Measure γ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : γ × ℝ → E) :
    ∫ z, g z ∂(ν.prod (gaussianReal 0 1))
      = ∫ z, gaussianPDFReal 0 1 z.2 • g z ∂(ν.prod (volume : Measure ℝ)) := by
  have hv : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  rw [gaussianReal_of_var_ne_zero (0 : ℝ) hv,
    MeasureTheory.prod_withDensity_right (measurable_gaussianPDF 0 1)]
  change ∫ z, g z ∂(ν.prod (volume : Measure ℝ)).withDensity (gaussianPDF 0 1 ∘ Prod.snd)
      = ∫ z, gaussianPDFReal 0 1 z.2 • g z ∂(ν.prod (volume : Measure ℝ))
  rw [integral_withDensity_eq_integral_toReal_smul
    ((measurable_gaussianPDF (μ := 0) (v := 1)).comp measurable_snd)
    (by filter_upwards with z using gaussianPDF_lt_top (μ := 0) (v := 1) (x := z.2))]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  show ((gaussianPDF 0 1 ∘ Prod.snd) z).toReal • g z = gaussianPDFReal 0 1 z.2 • g z
  rw [Function.comp_apply, toReal_gaussianPDF]

/-- **Coordinate Stein identity, Gaussian in the second factor** (the orientation produced by
Mathlib's `piOptionEquivProd`): `∫ z, z.2 • G z ∂(ν.prod (gaussianReal 0 1))
= ∫ z, G' z ∂(ν.prod (gaussianReal 0 1))`. -/
theorem integral_snd_smul_prod_gaussianReal
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    {G G' : γ × ℝ → A}
    (hderiv : ∀ (y : γ) (a : ℝ), HasDerivAt (fun t => G (y, t)) (G' (y, a)) a)
    (hint₁ : Integrable (fun z : γ × ℝ => gaussianPDFReal 0 1 z.2 • G' z)
      (ν.prod (volume : Measure ℝ)))
    (hint₂ : Integrable (fun z : γ × ℝ => z.2 • (gaussianPDFReal 0 1 z.2 • G z))
      (ν.prod (volume : Measure ℝ)))
    (hbot : ∀ᵐ y ∂ν, Tendsto (fun t => gaussianPDFReal 0 1 t • G (y, t)) atBot (𝓝 0))
    (htop : ∀ᵐ y ∂ν, Tendsto (fun t => gaussianPDFReal 0 1 t • G (y, t)) atTop (𝓝 0)) :
    ∫ z, z.2 • G z ∂(ν.prod (gaussianReal 0 1))
      = ∫ z, G' z ∂(ν.prod (gaussianReal 0 1)) := by
  rw [integral_prod_gaussianReal_right_eq_integral_smul (E := A),
    integral_prod_gaussianReal_right_eq_integral_smul (E := A)]
  rw [show (∫ z, gaussianPDFReal 0 1 z.2 • (z.2 • G z) ∂(ν.prod (volume : Measure ℝ)))
      = ∫ z, z.2 • (gaussianPDFReal 0 1 z.2 • G z) ∂(ν.prod (volume : Measure ℝ)) from by
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    show gaussianPDFReal 0 1 z.2 • z.2 • G z = z.2 • (gaussianPDFReal 0 1 z.2 • G z)
    rw [smul_smul, smul_smul, mul_comm]]
  exact integral_snd_smul_prod hderiv hint₁ hint₂ hbot htop

variable {κ' : Type*}

/-- Glue a value at `none` and a function on the `some`-part into a function on `Option κ'`. -/
def glue (z : (κ' → ℝ) × ℝ) : Option κ' → ℝ :=
  fun o => match o with | none => z.2 | some i => z.1 i

/-- The measurable splitting map `(Option κ' → ℝ) → (κ' → ℝ) × ℝ`. -/
def splitFun (x : Option κ' → ℝ) : (κ' → ℝ) × ℝ := (fun i => x (some i), x none)

@[simp] lemma glue_splitFun (x : Option κ' → ℝ) : glue (splitFun x) = x := by
  funext o
  cases o <;> rfl

@[simp] lemma glue_none (z : (κ' → ℝ) × ℝ) : glue z none = z.2 := rfl

lemma measurable_splitFun : Measurable (splitFun : (Option κ' → ℝ) → (κ' → ℝ) × ℝ) := by
  unfold splitFun
  fun_prop

lemma map_splitFun_eq_prod [Fintype κ'] :
    (Measure.pi (fun _ : Option κ' => gaussianReal 0 1)).map splitFun
      = (Measure.pi (fun _ : κ' => gaussianReal 0 1)).prod (gaussianReal 0 1) := by
  let e := MeasurableEquiv.piOptionEquivProd (fun _ : Option κ' => ℝ)
  have h := Measure.pi_map_piOptionEquivProd (μ := fun _ : Option κ' => gaussianReal 0 1)
  have key : (((Measure.pi (fun _ : κ' => gaussianReal 0 1)).prod (gaussianReal 0 1)).map
      e.symm).map e
      = (Measure.pi (fun _ : κ' => gaussianReal 0 1)).prod (gaussianReal 0 1) := by
    rw [Measure.map_map e.measurable e.symm.measurable]
    rw [show ((e : (Option κ' → ℝ) → (κ' → ℝ) × ℝ) ∘ e.symm) = id from
      funext fun z => e.apply_symm_apply z]
    exact Measure.map_id
  rw [h] at key
  rw [show splitFun = (e : (Option κ' → ℝ) → (κ' → ℝ) × ℝ) from rfl]
  exact key

lemma glue_splitFun' (z : (κ' → ℝ) × ℝ) : splitFun (glue z) = z := by
  ext <;> rfl

lemma measurable_glue : Measurable (glue : (κ' → ℝ) × ℝ → Option κ' → ℝ) := by
  rw [measurable_pi_iff]
  intro o
  cases o with
  | none => exact measurable_snd
  | some i => exact (measurable_pi_apply i).comp measurable_fst

/-- The measurable equivalence `(Option κ' → ℝ) ≃ᵐ (κ' → ℝ) × ℝ` splitting off the value at
`none`. -/
def splitEquiv : (Option κ' → ℝ) ≃ᵐ ((κ' → ℝ) × ℝ) where
  toEquiv :=
    { toFun := splitFun
      invFun := glue
      left_inv := glue_splitFun
      right_inv := glue_splitFun' }
  measurable_toFun := measurable_splitFun
  measurable_invFun := measurable_glue

lemma measurePreserving_splitEquiv [Fintype κ'] :
    MeasurePreserving (splitEquiv (κ' := κ'))
      (Measure.pi (fun _ : Option κ' => gaussianReal 0 1))
      ((Measure.pi (fun _ : κ' => gaussianReal 0 1)).prod (gaussianReal 0 1)) :=
  ⟨measurable_splitFun, by simpa [splitEquiv] using map_splitFun_eq_prod (κ' := κ')⟩

/-- **Coordinate Stein identity on `Measure.pi`**: Gaussian integration by parts in the
`none`-coordinate of a product of standard Gaussians indexed by `Option κ'`. -/
theorem integral_eval_none_smul [Fintype κ']
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    {F F' : (Option κ' → ℝ) → A}
    (hderiv : ∀ (y : κ' → ℝ) (a : ℝ),
      HasDerivAt (fun t => F (glue (y, t))) (F' (glue (y, a))) a)
    (hint₁ : Integrable (fun z : (κ' → ℝ) × ℝ => gaussianPDFReal 0 1 z.2 • F' (glue z))
      ((Measure.pi (fun _ : κ' => gaussianReal 0 1)).prod (volume : Measure ℝ)))
    (hint₂ : Integrable (fun z : (κ' → ℝ) × ℝ => z.2 • (gaussianPDFReal 0 1 z.2 • F (glue z)))
      ((Measure.pi (fun _ : κ' => gaussianReal 0 1)).prod (volume : Measure ℝ)))
    (hbot : ∀ᵐ y ∂(Measure.pi (fun _ : κ' => gaussianReal 0 1)),
      Tendsto (fun t => gaussianPDFReal 0 1 t • F (glue (y, t))) atBot (𝓝 0))
    (htop : ∀ᵐ y ∂(Measure.pi (fun _ : κ' => gaussianReal 0 1)),
      Tendsto (fun t => gaussianPDFReal 0 1 t • F (glue (y, t))) atTop (𝓝 0)) :
    ∫ x : Option κ' → ℝ, x none • F x ∂(Measure.pi (fun _ : Option κ' => gaussianReal 0 1))
      = ∫ x : Option κ' → ℝ, F' x ∂(Measure.pi (fun _ : Option κ' => gaussianReal 0 1)) := by
  have hmp := measurePreserving_splitEquiv (κ' := κ')
  have hF : ∫ x : Option κ' → ℝ, x none • F x ∂(Measure.pi (fun _ : Option κ' => gaussianReal 0 1))
      = ∫ z : (κ' → ℝ) × ℝ, z.2 • F (glue z)
          ∂((Measure.pi (fun _ : κ' => gaussianReal 0 1)).prod (gaussianReal 0 1)) := by
    rw [← hmp.integral_comp' (fun z : (κ' → ℝ) × ℝ => z.2 • F (glue z))]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show x none • F x = (splitFun x).2 • F (glue (splitFun x))
    rw [glue_splitFun]
    rfl
  have hF' : ∫ x : Option κ' → ℝ, F' x ∂(Measure.pi (fun _ : Option κ' => gaussianReal 0 1))
      = ∫ z : (κ' → ℝ) × ℝ, F' (glue z)
          ∂((Measure.pi (fun _ : κ' => gaussianReal 0 1)).prod (gaussianReal 0 1)) := by
    rw [← hmp.integral_comp' (fun z : (κ' → ℝ) × ℝ => F' (glue z))]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show F' x = F' (glue (splitFun x))
    rw [glue_splitFun]
  rw [hF, hF', integral_snd_smul_prod_gaussianReal hderiv hint₁ hint₂ hbot htop]

/-- **Coordinate Stein identity on `stdGaussian`**: the same integration by parts, now for the
standard Gaussian measure on the Euclidean space `EuclideanSpace ℝ (Option κ')` used by the GUE
model, transported from `Measure.pi` along `WithLp.toLp 2` (`map_pi_eq_stdGaussian`). -/
theorem integral_eval_none_smul_stdGaussian [Fintype κ']
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    {F F' : EuclideanSpace ℝ (Option κ') → A}
    (hderiv : ∀ (y : κ' → ℝ) (a : ℝ),
      HasDerivAt (fun t => F (WithLp.toLp 2 (glue (y, t))))
        (F' (WithLp.toLp 2 (glue (y, a)))) a)
    (hint₁ : Integrable
      (fun z : (κ' → ℝ) × ℝ => gaussianPDFReal 0 1 z.2 • F' (WithLp.toLp 2 (glue z)))
      ((Measure.pi (fun _ : κ' => gaussianReal 0 1)).prod (volume : Measure ℝ)))
    (hint₂ : Integrable
      (fun z : (κ' → ℝ) × ℝ => z.2 • (gaussianPDFReal 0 1 z.2 • F (WithLp.toLp 2 (glue z))))
      ((Measure.pi (fun _ : κ' => gaussianReal 0 1)).prod (volume : Measure ℝ)))
    (hbot : ∀ᵐ y ∂(Measure.pi (fun _ : κ' => gaussianReal 0 1)),
      Tendsto (fun t => gaussianPDFReal 0 1 t • F (WithLp.toLp 2 (glue (y, t)))) atBot (𝓝 0))
    (htop : ∀ᵐ y ∂(Measure.pi (fun _ : κ' => gaussianReal 0 1)),
      Tendsto (fun t => gaussianPDFReal 0 1 t • F (WithLp.toLp 2 (glue (y, t)))) atTop (𝓝 0)) :
    ∫ x : EuclideanSpace ℝ (Option κ'), x none • F x ∂(stdGaussian (EuclideanSpace ℝ (Option κ')))
      = ∫ x : EuclideanSpace ℝ (Option κ'), F' x
          ∂(stdGaussian (EuclideanSpace ℝ (Option κ'))) := by
  have hstd : MeasurePreserving (MeasurableEquiv.toLp 2 (Option κ' → ℝ))
      (Measure.pi (fun _ : Option κ' => gaussianReal 0 1))
      (stdGaussian (EuclideanSpace ℝ (Option κ'))) :=
    ⟨(MeasurableEquiv.toLp 2 (Option κ' → ℝ)).measurable, map_pi_eq_stdGaussian⟩
  rw [← hstd.integral_comp' (fun y : EuclideanSpace ℝ (Option κ') => y none • F y)]
  rw [← hstd.integral_comp' (fun y : EuclideanSpace ℝ (Option κ') => F' y)]
  exact integral_eval_none_smul hderiv hint₁ hint₂ hbot htop

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The equivalence `κ ≃ Option {i // i ≠ p}` sending the distinguished point to `none`. -/
def optionEquiv (p : κ) : κ ≃ Option {i : κ // ¬(i = p)} where
  toFun i := if h : i = p then none else some ⟨i, h⟩
  invFun o := match o with | none => p | some x => x.1
  left_inv := by
    intro i
    by_cases h : i = p
    · subst h; simp
    · simp [h]
  right_inv := by
    intro o
    cases o with
    | none => simp
    | some x =>
      have hx : ¬ (x.1 = p) := x.2
      simp [hx]

/-- The measurable reindexing `(κ → ℝ) ≃ᵐ (Option {i // i ≠ p} → ℝ)` induced by `optionEquiv`. -/
def piReindex (p : κ) : (κ → ℝ) ≃ᵐ (Option {i : κ // ¬(i = p)} → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : Option {i : κ // ¬(i = p)} => ℝ) (optionEquiv p)

lemma measurePreserving_piReindex (p : κ) :
    MeasurePreserving (piReindex p) (Measure.pi (fun _ : κ => gaussianReal 0 1))
      (Measure.pi (fun _ : Option {i : κ // ¬(i = p)} => gaussianReal 0 1)) := by
  have h := measurePreserving_piCongrLeft (α := fun _ : Option {i : κ // ¬(i = p)} => ℝ)
    (μ := fun _ => gaussianReal 0 1) (optionEquiv p)
  simpa [piReindex] using h

omit [Fintype κ] in
lemma piReindex_apply_none (p : κ) (x : κ → ℝ) : (piReindex p x) none = x p := by
  simp [piReindex, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply, optionEquiv]

/-- Reconstruction of a function on `κ` from its value at `p` and the values on the rest. -/
def piRecon (p : κ) (a : ℝ) (y : {i : κ // ¬(i = p)} → ℝ) : κ → ℝ :=
  fun i => if h : i = p then a else y ⟨i, h⟩

omit [Fintype κ] in
lemma piReindex_symm_glue (p : κ) (y : {i : κ // ¬(i = p)} → ℝ) (a : ℝ) :
    (piReindex p).symm (glue (y, a)) = piRecon p a y := by
  funext i
  have key : ∀ (j : κ), (piReindex p).symm (glue (y, a)) j
      = glue (y, a) ((optionEquiv p) j) := by
    intro j
    show (Equiv.piCongrLeft (fun _ => ℝ) (optionEquiv p)).symm (glue (y, a)) j = _
    rw [Equiv.piCongrLeft_symm_apply]
  rw [key]
  by_cases h : i = p
  · rw [h]
    simp [optionEquiv, glue, piRecon]
  · simp [optionEquiv, glue, piRecon, h]

/-- **Coordinate Stein identity for `Measure.pi` on an arbitrary finite index type.** -/
theorem integral_eval_smul_pi (p : κ)
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    {F F' : (κ → ℝ) → A}
    (hderiv : ∀ (y : {i : κ // ¬(i = p)} → ℝ) (a : ℝ),
      HasDerivAt (fun t => F (piRecon p t y)) (F' (piRecon p a y)) a)
    (hint₁ : Integrable (fun z : ({i : κ // ¬(i = p)} → ℝ) × ℝ =>
        gaussianPDFReal 0 1 z.2 • F' (piRecon p z.2 z.1))
      ((Measure.pi (fun _ : {i : κ // ¬(i = p)} => gaussianReal 0 1)).prod (volume : Measure ℝ)))
    (hint₂ : Integrable (fun z : ({i : κ // ¬(i = p)} → ℝ) × ℝ =>
        z.2 • (gaussianPDFReal 0 1 z.2 • F (piRecon p z.2 z.1)))
      ((Measure.pi (fun _ : {i : κ // ¬(i = p)} => gaussianReal 0 1)).prod (volume : Measure ℝ)))
    (hbot : ∀ᵐ y ∂(Measure.pi (fun _ : {i : κ // ¬(i = p)} => gaussianReal 0 1)),
      Tendsto (fun t => gaussianPDFReal 0 1 t • F (piRecon p t y)) atBot (𝓝 0))
    (htop : ∀ᵐ y ∂(Measure.pi (fun _ : {i : κ // ¬(i = p)} => gaussianReal 0 1)),
      Tendsto (fun t => gaussianPDFReal 0 1 t • F (piRecon p t y)) atTop (𝓝 0)) :
    ∫ x : κ → ℝ, x p • F x ∂(Measure.pi (fun _ : κ => gaussianReal 0 1))
      = ∫ x : κ → ℝ, F' x ∂(Measure.pi (fun _ : κ => gaussianReal 0 1)) := by
  have hmp := measurePreserving_piReindex (p := p)
  have hL : ∫ x : κ → ℝ, x p • F x ∂(Measure.pi (fun _ : κ => gaussianReal 0 1))
      = ∫ y : Option {i : κ // ¬(i = p)} → ℝ, y none •
          F ((piReindex p).symm y)
          ∂(Measure.pi (fun _ : Option {i : κ // ¬(i = p)} => gaussianReal 0 1)) := by
    rw [← hmp.integral_comp' (fun y : Option {i : κ // ¬(i = p)} → ℝ =>
      y none • F ((piReindex p).symm y))]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show x p • F x = (piReindex p x) none • F ((piReindex p).symm (piReindex p x))
    rw [MeasurableEquiv.symm_apply_apply, piReindex_apply_none]
  have hR : ∫ x : κ → ℝ, F' x ∂(Measure.pi (fun _ : κ => gaussianReal 0 1))
      = ∫ y : Option {i : κ // ¬(i = p)} → ℝ, F' ((piReindex p).symm y)
          ∂(Measure.pi (fun _ : Option {i : κ // ¬(i = p)} => gaussianReal 0 1)) := by
    rw [← hmp.integral_comp' (fun y : Option {i : κ // ¬(i = p)} → ℝ =>
      F' ((piReindex p).symm y))]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show F' x = F' ((piReindex p).symm (piReindex p x))
    rw [MeasurableEquiv.symm_apply_apply]
  rw [hL, hR]
  simp only [← piReindex_symm_glue] at hderiv hint₁ hint₂ hbot htop
  exact integral_eval_none_smul (F := fun y => F ((piReindex p).symm y))
    (F' := fun y => F' ((piReindex p).symm y)) hderiv hint₁ hint₂ hbot htop

/-- **Coordinate Stein identity for `stdGaussian` on any finite index type** — the form used
by the GUE model on `EuclideanSpace ℝ (GUECoord ι N)`: integration by parts in the coordinate
`p`, transported from `Measure.pi` along `WithLp.toLp 2`. -/
theorem integral_eval_smul_stdGaussian (p : κ)
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    {F F' : EuclideanSpace ℝ κ → A}
    (hderiv : ∀ (y : {i : κ // ¬(i = p)} → ℝ) (a : ℝ),
      HasDerivAt (fun t => F (WithLp.toLp 2 (piRecon p t y)))
        (F' (WithLp.toLp 2 (piRecon p a y))) a)
    (hint₁ : Integrable (fun z : ({i : κ // ¬(i = p)} → ℝ) × ℝ =>
        gaussianPDFReal 0 1 z.2 • F' (WithLp.toLp 2 (piRecon p z.2 z.1)))
      ((Measure.pi (fun _ : {i : κ // ¬(i = p)} => gaussianReal 0 1)).prod (volume : Measure ℝ)))
    (hint₂ : Integrable (fun z : ({i : κ // ¬(i = p)} → ℝ) × ℝ =>
        z.2 • (gaussianPDFReal 0 1 z.2 • F (WithLp.toLp 2 (piRecon p z.2 z.1))))
      ((Measure.pi (fun _ : {i : κ // ¬(i = p)} => gaussianReal 0 1)).prod (volume : Measure ℝ)))
    (hbot : ∀ᵐ y ∂(Measure.pi (fun _ : {i : κ // ¬(i = p)} => gaussianReal 0 1)),
      Tendsto (fun t => gaussianPDFReal 0 1 t • F (WithLp.toLp 2 (piRecon p t y))) atBot (𝓝 0))
    (htop : ∀ᵐ y ∂(Measure.pi (fun _ : {i : κ // ¬(i = p)} => gaussianReal 0 1)),
      Tendsto (fun t => gaussianPDFReal 0 1 t • F (WithLp.toLp 2 (piRecon p t y))) atTop (𝓝 0)) :
    ∫ x : EuclideanSpace ℝ κ, x p • F x ∂(stdGaussian (EuclideanSpace ℝ κ))
      = ∫ x : EuclideanSpace ℝ κ, F' x ∂(stdGaussian (EuclideanSpace ℝ κ)) := by
  have hstd : MeasurePreserving (MeasurableEquiv.toLp 2 (κ → ℝ))
      (Measure.pi (fun _ : κ => gaussianReal 0 1))
      (stdGaussian (EuclideanSpace ℝ κ)) :=
    ⟨(MeasurableEquiv.toLp 2 (κ → ℝ)).measurable, map_pi_eq_stdGaussian⟩
  rw [← hstd.integral_comp' (fun y : EuclideanSpace ℝ κ => y p • F y)]
  rw [← hstd.integral_comp' (fun y : EuclideanSpace ℝ κ => F' y)]
  exact integral_eval_smul_pi p hderiv hint₁ hint₂ hbot htop

end

end GUEStrongConvergence
