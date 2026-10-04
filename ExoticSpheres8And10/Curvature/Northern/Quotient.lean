/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Curvature.Northern.Model
import ExoticSpheres8And10.PolarBundles.StarQuotient
import ExoticSpheres8And10.PolarBundles.OrientationSphere
import ExoticSpheres8And10.StarBundles.StarBundle

/-! # §4: the northern star action on `V × S³`, and its orbit map

The star action on the northern piece `P_N ≅ D^n × S³` is `q ⋆ (Y, u) = (ρ(q)Y, qu)`, with the
product connection ([GG]: "`(qu)⁻¹d(qu) = u⁻¹du`"). This file proves:

* `mvfderiv_comp'`, `mvfderiv_clm_comp`: chain rules for `mvfderiv` (infrastructure);
* `starN`: the star action; `northMetric_starN`: **it acts by isometries** of [GG]'s northern
  metric, when `r̃` is `ρ`-invariant;
* `πN (Y, u) = ρ(u)⁻¹ Y`: the orbit map, with `πN_starN : πN ∘ (q ⋆ ·) = πN`.
-/

open RiemannianGeometry Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Real

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

/-! ### Chain rules for `mvfderiv` -/

section Chain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']

theorem mvfderiv_comp' {g : N → F} {f : M → N} {x : M} (hg : MDiffAt g (f x)) (hf : MDiffAt f x)
    (v : TangentSpace I x) :
    mvfderiv I (g ∘ f) x v = mvfderiv J g (f x) (mfderiv I J f x v) := by
  simp only [mvfderiv, ContinuousLinearMap.comp_apply, mfderiv_comp x hg hf]
  rfl

theorem mvfderiv_clm_comp (L : F →L[ℝ] F') {f : M → F} {x : M} (hf : MDiffAt f x)
    (v : TangentSpace I x) : mvfderiv I (L ∘ f) x v = L (mvfderiv I f x v) := by
  have hL : MDiffAt (L : F → F') (f x) := L.mdifferentiableAt
  rw [mvfderiv_comp' hL hf]
  simp only [mvfderiv, ContinuousLinearMap.comp_apply, L.hasMFDerivAt.mfderiv]
  rfl

end Chain

/-! ### The star action on `V × S³` -/

section Star

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (ρV : S3 →* (V ≃ₗᵢ[ℝ] V))

/-- The star action `q ⋆ (Y, u) = (ρ(q)Y, qu)`. -/
def starN (q : S3) (p : V × S3) : V × S3 := (ρV q p.1, q * p.2)

/-- The orbit map `(Y, u) ↦ ρ(u)⁻¹ Y`. -/
def πN (p : V × S3) : V := ρV p.2⁻¹ p.1

theorem πN_starN (q : S3) (p : V × S3) : πN ρV (starN ρV q p) = πN ρV p := by
  show ρV (q * p.2)⁻¹ (ρV q p.1) = ρV p.2⁻¹ p.1
  calc ρV (q * p.2)⁻¹ (ρV q p.1) = (ρV (q * p.2)⁻¹ * ρV q) p.1 := rfl
    _ = ρV ((q * p.2)⁻¹ * q) p.1 := by rw [map_mul]
    _ = ρV p.2⁻¹ p.1 := by rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]

variable {ρV} (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, V →L[ℝ] V) ∞
  fun q : S3 => ((ρV q : V ≃L[ℝ] V) : V →L[ℝ] V))

include hρ in
theorem contMDiff_starN (q : S3) : ContMDiff (IN V) (IN V) ∞ (starN ρV q) := by
  have h1 : ContMDiff (IN V) 𝓘(ℝ, V) ∞ fun p : V × S3 => ρV q p.1 :=
    ((ρV q : V ≃L[ℝ] V) : V →L[ℝ] V).contDiff.contMDiff.comp contMDiff_fst
  have h2 : ContMDiff (IN V) (𝓡 3) ∞ fun p : V × S3 => q * p.2 :=
    ContMDiff.comp (g := fun x : S3 × S3 => x.1 * x.2) (f := fun p : V × S3 => (q, p.2))
      contMDiff_mulS3 (contMDiff_const.prodMk contMDiff_snd)
  exact h1.prodMk h2

include hρ in
theorem contMDiff_πN : ContMDiff (IN V) 𝓘(ℝ, V) ∞ (πN ρV) := by
  have hi : ContMDiff (IN V) (𝓡 3) ∞ fun p : V × S3 => p.2⁻¹ :=
    contMDiff_invS3.comp contMDiff_snd
  exact (hρ.comp hi).clm_apply contMDiff_fst

/-- Left multiplication by a unit quaternion preserves the inner product. -/
theorem inner_mul_left_unit (q : S3) (a b : Quaternion ℝ) :
    ⟪(q : Quaternion ℝ) * a, (q : Quaternion ℝ) * b⟫ = ⟪a, b⟫ := by
  have hq : ‖(q : Quaternion ℝ)‖ = 1 := mem_sphere_zero_iff_norm.1 q.2
  exact inner_of_norm_pres (f := fun x => (q : Quaternion ℝ) * x) (fun x y => mul_add _ x y)
    (fun x => by rw [norm_mul, hq, one_mul]) a b

include hρ in
/-- **The star action is isometric** for [GG]'s northern metric, when `r̃` is `ρ`-invariant. -/
theorem northMetric_starN {δ : ℝ} {rt : V → ℝ} (hrt : ∀ q Y, rt (ρV q Y) = rt Y) (q : S3)
    (p : V × S3) (v w : TangentSpace (IN V) p) :
    northMetric δ rt (starN ρV q p) (mfderiv (IN V) (IN V) (starN ρV q) p v)
      (mfderiv (IN V) (IN V) (starN ρV q) p w) = northMetric δ rt p v w := by
  have hS : MDifferentiableAt (IN V) (IN V) (starN ρV q) p :=
    (contMDiff_starN hρ q p).mdifferentiableAt (by simp)
  have hY : ∀ y, MDifferentiableAt (IN V) 𝓘(ℝ, V) (fY (V := V)) y := fun y =>
    (contMDiff_fY y).mdifferentiableAt (by simp)
  have hQ : ∀ y, MDifferentiableAt (IN V) 𝓘(ℝ, ℝ) (fQ (V := V)) y := fun y =>
    (contMDiff_fQ y).mdifferentiableAt (by simp)
  have hU : ∀ y, MDifferentiableAt (IN V) 𝓘(ℝ, Quaternion ℝ) (fU (V := V)) y := fun y =>
    (contMDiff_fU y).mdifferentiableAt (by simp)
  -- the three coordinates transform linearly under the action
  have eY : fY ∘ starN ρV q = ((ρV q : V ≃L[ℝ] V) : V →L[ℝ] V) ∘ fY := rfl
  have eQ : fQ ∘ starN ρV q = fQ := by
    funext y; simp [fQ, starN, LinearIsometryEquiv.norm_map]
  have eU : fU ∘ starN ρV q =
      (ContinuousLinearMap.mul ℝ (Quaternion ℝ) (q : Quaternion ℝ)) ∘ fU := by
    funext y; simp [fU, starN]
  have tY : ∀ u : TangentSpace (IN V) p,
      mvfderiv (IN V) fY (starN ρV q p) (mfderiv (IN V) (IN V) (starN ρV q) p u) =
        ρV q (mvfderiv (IN V) fY p u) := fun u => by
    rw [← mvfderiv_comp' (hY _) hS, eY, mvfderiv_clm_comp _ (hY p)]; rfl
  have tQ : ∀ u : TangentSpace (IN V) p,
      mvfderiv (IN V) fQ (starN ρV q p) (mfderiv (IN V) (IN V) (starN ρV q) p u) =
        mvfderiv (IN V) fQ p u := fun u => by
    rw [← mvfderiv_comp' (hQ _) hS, eQ]
  have tU : ∀ u : TangentSpace (IN V) p,
      mvfderiv (IN V) fU (starN ρV q p) (mfderiv (IN V) (IN V) (starN ρV q) p u) =
        (q : Quaternion ℝ) * mvfderiv (IN V) fU p u := fun u => by
    rw [← mvfderiv_comp' (hU _) hS, eU, mvfderiv_clm_comp _ (hU p)]; rfl
  rw [northMetric_apply, northMetric_apply, tY, tY, tQ, tQ, tU, tU,
    LinearIsometryEquiv.inner_map_map, inner_mul_left_unit]
  simp only [starN, LinearIsometryEquiv.norm_map, hrt]

end Star

end

end ExoticSpheres8And10
