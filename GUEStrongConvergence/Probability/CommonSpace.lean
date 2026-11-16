/-
# A common probability space for GUE matrices of every dimension

Checkpoint **P0** of the GUE strong-convergence project requires a *single* probability
space carrying the normalized complex GUE matrix `G_N` for **every** matrix size `N`
simultaneously, with the blocks for different `N` independent.

Mathlib provides exactly the required countably infinite product measure,
`Measure.infinitePi` (`Mathlib/Probability/ProductMeasure.lean`), together with its
projection/cylinder lemmas.  In this file we use it to build

`CommonSpace ι = (N : ℕ) → EuclideanSpace ℝ (GUECoord ι N)`

with measure

`commonGaussianMeasure ι = Measure.infinitePi (fun N ↦ stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))`.

The main results are:

* `isProbabilityMeasure_commonGaussianMeasure` — the common measure is a probability measure;
* `measurePreserving_eval_commonGaussian` / `hasLaw_eval_commonGaussian` — evaluating at a
  dimension `N` is measure preserving, with law the standard Gaussian measure on the block;
* `gueMatrixOn` — the normalized GUE matrix of size `N`, read off from the common space;
* `gueMatrixOn_isHermitian`, `measurable_gueMatrixOn_entry`, `measurable_gueMatrixOn` —
  pointwise Hermiticity and measurability of the matrix and its entries;
* `map_gueMatrixOn`, `map_gueMatrixOn_entry`, `hasLaw_gueMatrixOn` — the law of the `N`-th
  block is exactly the law of `gueMatrix` under `stdGaussian` (the construction of
  `GUEModel.lean`), and `integral_gueMatrixOn_mul` transports the covariance identity (1.2)
  to the common space;
* `iIndepFun_commonBlocks`, `iIndepFun_gueMatrixOn` — the blocks for different dimensions
  are independent, in particular the GUE matrices of different sizes (with a fixed label)
  are independent;
* `iIndepFun_gaussianCoord` — **all** real scalar Gaussian coordinates of the whole family are
  independent, by rewriting `stdGaussian` as the push-forward of a product of one-dimensional
  standard Gaussians (`map_pi_eq_stdGaussian`) and applying the infinite-product independence
  theorem `iIndepFun_uncurry_infinitePi`;
* `map_gaussianCoord`, `hasLaw_gaussianCoord`, `measurable_gaussianCoord` — each scalar
  coordinate has the one-dimensional standard Gaussian law `gaussianReal 0 1`, so together
  with `iIndepFun_gaussianCoord` the scalar coordinates are iid standard Gaussians.

No unstated assumptions are used: aside from the index type `ι` and the matrix size `N`,
the only hypothesis is `[Fintype ι]`, which is what makes each Euclidean block
finite-dimensional (and hence `stdGaussian` available).  `[DecidableEq ι]` is required only
for the transported covariance identity, matching `integral_gueMatrix_mul`.
-/
import Mathlib.Probability.Independence.InfinitePi
import GUEStrongConvergence.Probability.GUEModel

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix ENNReal

set_option autoImplicit false

namespace GUEStrongConvergence

noncomputable section

variable {ι : Type*} [Fintype ι]

/-! ### The common space and its measure -/

/-- The common sample space: one standard Gaussian Euclidean block for each matrix dimension
`N`.  The block for `N` carries the `N × N` matrix coordinates for every label in `ι`. -/
abbrev CommonSpace (ι : Type*) : Type _ :=
  (N : ℕ) → EuclideanSpace ℝ (GUECoord ι N)

/-- The common probability measure: the countable product of the standard Gaussian measures
on the blocks. -/
def commonGaussianMeasure (ι : Type*) [Fintype ι] : Measure (CommonSpace ι) :=
  Measure.infinitePi (fun N : ℕ => stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))

instance isProbabilityMeasure_commonGaussianMeasure :
    IsProbabilityMeasure (commonGaussianMeasure ι) := by
  rw [commonGaussianMeasure]
  infer_instance

/-- Evaluating a point of the common space at dimension `N` is measure preserving onto the
standard Gaussian measure on the `N`-th block. -/
theorem measurePreserving_eval_commonGaussian (N : ℕ) :
    MeasurePreserving (fun x : CommonSpace ι => x N) (commonGaussianMeasure ι)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
  measurePreserving_eval_infinitePi
    (fun N : ℕ => stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) N

/-- The law of the `N`-th block coordinate is the standard Gaussian measure. -/
theorem commonGaussianMeasure_map_eval (N : ℕ) :
    (commonGaussianMeasure ι).map (fun x : CommonSpace ι => x N) =
      stdGaussian (EuclideanSpace ℝ (GUECoord ι N)) :=
  Measure.infinitePi_map_eval
    (fun N : ℕ => stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) N

/-- The `N`-th block coordinate of the common space has the standard Gaussian law. -/
theorem hasLaw_eval_commonGaussian (N : ℕ) :
    HasLaw (fun x : CommonSpace ι => x N)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) (commonGaussianMeasure ι) where
  aemeasurable := (measurable_pi_apply N).aemeasurable
  map_eq := commonGaussianMeasure_map_eval N

/-! ### The GUE matrix on the common space -/

/-- The normalized complex GUE matrix of size `N` and label `i`, as a random matrix on the
common space. -/
def gueMatrixOn (x : CommonSpace ι) (N : ℕ) (i : ι) : Matrix (Fin N) (Fin N) ℂ :=
  gueMatrix (x N) i

omit [Fintype ι] in
/-- Every GUE matrix on the common space is Hermitian, pointwise in the sample point. -/
theorem gueMatrixOn_isHermitian (x : CommonSpace ι) (N : ℕ) (i : ι) :
    (gueMatrixOn x N i).IsHermitian :=
  gueMatrix_isHermitian (x N) i

/-- Each entry of the `N`-th GUE matrix is a measurable function on the common space. -/
theorem measurable_gueMatrixOn_entry (N : ℕ) (i : ι) (a b : Fin N) :
    Measurable fun x : CommonSpace ι => gueMatrixOn x N i a b :=
  (measurable_gueMatrix_entry (N := N) i a b).comp (measurable_pi_apply N)

/-- The matrix-valued `N`-th GUE block is measurable on the common space. -/
theorem measurable_gueMatrix (N : ℕ) (i : ι) :
    Measurable fun y : EuclideanSpace ℝ (GUECoord ι N) => gueMatrix y i :=
  measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun b =>
    measurable_gueMatrix_entry (N := N) i a b

/-- The matrix-valued `N`-th GUE block is measurable on the common space. -/
theorem measurable_gueMatrixOn (N : ℕ) (i : ι) :
    Measurable fun x : CommonSpace ι => gueMatrixOn x N i :=
  (measurable_gueMatrix N i).comp (measurable_pi_apply N)

/-! ### Distribution transport

The law of the `N`-th block on the common space is exactly the law used in `GUEModel.lean`;
all distributional statements therefore transfer verbatim. -/

/-- The law of the `N`-th GUE matrix on the common space is the law of `gueMatrix` under the
standard Gaussian measure on the block. -/
theorem map_gueMatrixOn (N : ℕ) (i : ι) :
    (commonGaussianMeasure ι).map (fun x : CommonSpace ι => gueMatrixOn x N i) =
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))).map
        (fun y : EuclideanSpace ℝ (GUECoord ι N) => gueMatrix y i) := by
  have hcomp : (fun x : CommonSpace ι => gueMatrixOn x N i) =
      (fun y : EuclideanSpace ℝ (GUECoord ι N) => gueMatrix y i) ∘
        (fun x : CommonSpace ι => x N) := rfl
  rw [hcomp, ← Measure.map_map (measurable_gueMatrix N i) (measurable_pi_apply N),
    commonGaussianMeasure_map_eval]

/-- The law of an individual entry of the `N`-th GUE matrix on the common space. -/
theorem map_gueMatrixOn_entry (N : ℕ) (i : ι) (a b : Fin N) :
    (commonGaussianMeasure ι).map (fun x : CommonSpace ι => gueMatrixOn x N i a b) =
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))).map
        (fun y : EuclideanSpace ℝ (GUECoord ι N) => gueMatrix y i a b) := by
  have hcomp : (fun x : CommonSpace ι => gueMatrixOn x N i a b) =
      (fun y : EuclideanSpace ℝ (GUECoord ι N) => gueMatrix y i a b) ∘
        (fun x : CommonSpace ι => x N) := rfl
  rw [hcomp, ← Measure.map_map (measurable_gueMatrix_entry (N := N) i a b)
    (measurable_pi_apply N), commonGaussianMeasure_map_eval]

/-- The `N`-th GUE block on the common space has the same law as the `gueMatrix`
construction of `GUEModel.lean`. -/
theorem hasLaw_gueMatrixOn (N : ℕ) (i : ι) :
    HasLaw (fun x : CommonSpace ι => gueMatrixOn x N i)
      ((stdGaussian (EuclideanSpace ℝ (GUECoord ι N))).map
        (fun y : EuclideanSpace ℝ (GUECoord ι N) => gueMatrix y i))
      (commonGaussianMeasure ι) where
  aemeasurable := (measurable_gueMatrixOn N i).aemeasurable
  map_eq := map_gueMatrixOn N i

/-- **Covariance identity on the common space** (equation (1.2) of the handoff).  For the
`N`-th block of the common space, the covariance of two GUE entries is
`δ_{ij} δ_{ad} δ_{bc} / N`, with no complex conjugation. -/
theorem integral_gueMatrixOn_mul [DecidableEq ι] (N : ℕ) (i j : ι) (a b c d : Fin N) :
    ∫ x : CommonSpace ι, gueMatrixOn x N i a b * gueMatrixOn x N j c d
        ∂(commonGaussianMeasure ι)
      = if i = j ∧ a = d ∧ b = c then ((N : ℝ)⁻¹ : ℂ) else 0 := by
  have hcov : (∫ y : EuclideanSpace ℝ (GUECoord ι N),
        gueMatrix y i a b * gueMatrix y j c d ∂
          (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
      = if i = j ∧ a = d ∧ b = c then ((N : ℝ)⁻¹ : ℂ) else 0 :=
    integral_gueMatrix_mul i j a b c d
  rw [← hcov, ← commonGaussianMeasure_map_eval (ι := ι) N,
    integral_map (measurable_pi_apply N).aemeasurable
      ((measurable_gueMatrix_entry (N := N) i a b).mul
        (measurable_gueMatrix_entry (N := N) j c d)).aestronglyMeasurable]
  rfl

/-! ### Independence

We now prove the two independence statements needed for the almost-sure argument: the blocks
belonging to different matrix dimensions are independent, and all real scalar Gaussian
coordinates of the whole family are independent.

The scalar-coordinate statement is reduced to Mathlib's
`iIndepFun_uncurry_infinitePi` by writing each Euclidean block as the push-forward of a
product of one-dimensional standard Gaussians (`map_pi_eq_stdGaussian`) and pushing the
product measure forward along the coordinate equivalence. -/

/-- The block coordinates of different dimensions are independent on the common space. -/
theorem iIndepFun_commonBlocks :
    iIndepFun (fun N (x : CommonSpace ι) => x N) (commonGaussianMeasure ι) :=
  iIndepFun_infinitePi
    (P := fun N : ℕ => stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
    (X := fun _ y => y) (fun _ => measurable_id)

/-- The GUE matrices of different dimensions (with a fixed label `i`) are independent on the
common space. -/
theorem iIndepFun_gueMatrixOn (i : ι) :
    iIndepFun (fun N (x : CommonSpace ι) => gueMatrixOn x N i)
      (commonGaussianMeasure ι) := by
  have h := iIndepFun_infinitePi
    (P := fun N : ℕ => stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
    (X := fun N y => gueMatrix y i) (fun N => measurable_gueMatrix N i)
  simpa only [commonGaussianMeasure, gueMatrixOn] using h

/-- Pushing the standard Gaussian measure on a Euclidean block forward along the inverse of
the coordinate equivalence `toLp` gives the product of one-dimensional standard Gaussians. -/
theorem stdGaussian_map_toLp_symm (κ : Type*) [Fintype κ] :
    (stdGaussian (EuclideanSpace ℝ κ)).map
        (MeasurableEquiv.toLp 2 (κ → ℝ)).symm =
      Measure.pi (fun _ : κ => gaussianReal 0 1) := by
  have hη : (Measure.pi (fun _ : κ => gaussianReal 0 1)).map
      (MeasurableEquiv.toLp 2 (κ → ℝ)) = stdGaussian (EuclideanSpace ℝ κ) := by
    simpa only [MeasurableEquiv.coe_toLp] using map_pi_eq_stdGaussian (ι := κ)
  rw [← hη, Measure.map_map]
  · simp
  · exact (MeasurableEquiv.toLp 2 (κ → ℝ)).symm.measurable
  · exact (MeasurableEquiv.toLp 2 (κ → ℝ)).measurable

/-- The joint law of all scalar Gaussian coordinates on the common space is the countable
product of the products of one-dimensional standard Gaussians.  Equivalently, extracting the
coordinates maps the common Gaussian measure to the fully product measure. -/
theorem commonGaussianMeasure_map_coords :
    (commonGaussianMeasure ι).map
        (fun x : CommonSpace ι => fun N =>
          (MeasurableEquiv.toLp 2 (GUECoord ι N → ℝ)).symm (x N)) =
      Measure.infinitePi
        (fun N : ℕ => Measure.pi (fun _ : GUECoord ι N => gaussianReal 0 1)) := by
  rw [commonGaussianMeasure,
    Measure.infinitePi_map_pi
      (μ := fun N : ℕ => stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      (f := fun N => (MeasurableEquiv.toLp 2 (GUECoord ι N → ℝ)).symm)]
  · apply congrArg Measure.infinitePi
    funext N
    exact stdGaussian_map_toLp_symm (GUECoord ι N)
  · intro N
    exact (MeasurableEquiv.toLp 2 (GUECoord ι N → ℝ)).symm.measurable

/-- A real scalar Gaussian coordinate of the common space, indexed by a dimension `N` and a
coordinate `p` of the `N`-th block. -/
def gaussianCoord (p : (N : ℕ) × GUECoord ι N) (x : CommonSpace ι) : ℝ :=
  (MeasurableEquiv.toLp 2 (GUECoord ι p.1 → ℝ)).symm (x p.1) p.2

omit [Fintype ι] in
/-- Each scalar Gaussian coordinate is measurable. -/
theorem measurable_gaussianCoord (p : (N : ℕ) × GUECoord ι N) :
    Measurable (gaussianCoord p) := by
  have hη : Measurable (fun x : CommonSpace ι =>
      (MeasurableEquiv.toLp 2 (GUECoord ι p.1 → ℝ)).symm (x p.1)) :=
    ((MeasurableEquiv.toLp 2 (GUECoord ι p.1 → ℝ)).symm.measurable).comp
      (measurable_pi_apply p.1)
  exact (measurable_pi_apply p.2).comp hη

/-- **Each scalar Gaussian coordinate has the one-dimensional standard Gaussian law** on the
common space. -/
theorem map_gaussianCoord (p : (N : ℕ) × GUECoord ι N) :
    (commonGaussianMeasure ι).map (gaussianCoord p) = gaussianReal 0 1 := by
  have hη : Measurable (fun x : CommonSpace ι =>
      (MeasurableEquiv.toLp 2 (GUECoord ι p.1 → ℝ)).symm (x p.1)) :=
    ((MeasurableEquiv.toLp 2 (GUECoord ι p.1 → ℝ)).symm.measurable).comp
      (measurable_pi_apply p.1)
  have hcomp : gaussianCoord p =
      (fun y : GUECoord ι p.1 → ℝ => y p.2) ∘
        (fun x : CommonSpace ι =>
          (MeasurableEquiv.toLp 2 (GUECoord ι p.1 → ℝ)).symm (x p.1)) := rfl
  rw [hcomp, ← Measure.map_map (measurable_pi_apply p.2) hη]
  have hblock : (commonGaussianMeasure ι).map
      (fun x : CommonSpace ι =>
        (MeasurableEquiv.toLp 2 (GUECoord ι p.1 → ℝ)).symm (x p.1)) =
      Measure.pi (fun _ : GUECoord ι p.1 => gaussianReal 0 1) := by
    have hcomp2 : (fun x : CommonSpace ι =>
        (MeasurableEquiv.toLp 2 (GUECoord ι p.1 → ℝ)).symm (x p.1)) =
        (MeasurableEquiv.toLp 2 (GUECoord ι p.1 → ℝ)).symm ∘
          (fun x : CommonSpace ι => x p.1) := rfl
    rw [hcomp2, ← Measure.map_map
      (MeasurableEquiv.toLp 2 (GUECoord ι p.1 → ℝ)).symm.measurable
      (measurable_pi_apply p.1), commonGaussianMeasure_map_eval,
      stdGaussian_map_toLp_symm]
  rw [hblock,
    (measurePreserving_eval (fun _ : GUECoord ι p.1 => gaussianReal 0 1) p.2).map_eq]

/-- **The scalar Gaussian coordinates are iid standard Gaussians**: each coordinate has law
`gaussianReal 0 1`, and the whole family is independent. -/
theorem hasLaw_gaussianCoord (p : (N : ℕ) × GUECoord ι N) :
    HasLaw (gaussianCoord p) (gaussianReal 0 1) (commonGaussianMeasure ι) where
  aemeasurable := (measurable_gaussianCoord p).aemeasurable
  map_eq := map_gaussianCoord p

/-- Transporting independence along a measurable map with a fixed push-forward identity. -/
theorem iIndepFun_of_map_eq {σ : Type*} {β : σ → Type*} [∀ p, MeasurableSpace (β p)]
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P]
    {F : Ω → Ω'} (hF : P.map F = Q) (hFm : Measurable F)
    {g : (p : σ) → Ω' → β p} (hgm : ∀ p, Measurable (g p)) (hg : iIndepFun g Q) :
    iIndepFun (fun p x => g p (F x)) P := by
  classical
  change iIndepFun (fun p => g p ∘ F) P
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map fun p => (hgm p).comp hFm]
  have hjoint : Measurable (fun y : Ω' => fun p => g p y) := measurable_pi_iff.2 hgm
  have hL : Measure.map (fun ω i => (g i ∘ F) ω) P =
      Measure.map (fun y : Ω' => fun p => g p y) (Measure.map F P) := by
    rw [Measure.map_map hjoint hFm]
    rfl
  rw [hL, hF]
  have hmap := hg.map_fun_eq_infinitePi_map hgm
  rw [hmap]
  apply congrArg Measure.infinitePi
  funext p
  rw [← Measure.map_map (hgm p) hFm, hF]

/-- **All real scalar Gaussian coordinates are independent** on the common space. -/
theorem iIndepFun_gaussianCoord :
    iIndepFun (gaussianCoord (ι := ι)) (commonGaussianMeasure ι) := by
  have hinner : Measure.infinitePi
        (fun N : ℕ => Measure.pi (fun _ : GUECoord ι N => gaussianReal 0 1)) =
      Measure.infinitePi
        (fun N : ℕ => Measure.infinitePi (fun _ : GUECoord ι N => gaussianReal 0 1)) :=
    congrArg Measure.infinitePi (funext fun N =>
      (Measure.infinitePi_eq_pi (fun _ : GUECoord ι N => gaussianReal 0 1)).symm)
  have hQ : iIndepFun
      (fun (p : (N : ℕ) × GUECoord ι N)
        (y : (N : ℕ) → GUECoord ι N → ℝ) => y p.1 p.2)
      (Measure.infinitePi
        (fun N : ℕ => Measure.pi (fun _ : GUECoord ι N => gaussianReal 0 1))) := by
    rw [hinner]
    exact iIndepFun_uncurry_infinitePi
      (μ := fun (N : ℕ) (j : GUECoord ι N) => gaussianReal 0 1)
      (X := fun (_ : ℕ) (_ : GUECoord ι _) => id) (fun _ _ => measurable_id)
  have hcoords : Measurable
      (fun x : CommonSpace ι =>
        fun N => (MeasurableEquiv.toLp 2 (GUECoord ι N → ℝ)).symm (x N)) := by
    rw [measurable_pi_iff]
    intro N
    exact ((MeasurableEquiv.toLp 2 (GUECoord ι N → ℝ)).symm.measurable).comp
      (measurable_pi_apply N)
  have h := iIndepFun_of_map_eq
    (P := commonGaussianMeasure ι)
    (F := fun x : CommonSpace ι =>
      fun N => (MeasurableEquiv.toLp 2 (GUECoord ι N → ℝ)).symm (x N))
    (Q := Measure.infinitePi
      (fun N : ℕ => Measure.pi (fun _ : GUECoord ι N => gaussianReal 0 1)))
    (commonGaussianMeasure_map_coords (ι := ι)) hcoords
    (g := fun (p : (N : ℕ) × GUECoord ι N)
      (y : (N : ℕ) → GUECoord ι N → ℝ) => y p.1 p.2)
    (fun p => (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)) hQ
  exact h
end

end GUEStrongConvergence
