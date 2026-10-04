/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import RiemannianGeometry.SectionalCurvature

/-! # Infrastructure: Riemannian geometry in coordinates, for `RiemannianGeometry`'s Levi-Civita connection

The library `RiemannianGeometry` defines the Levi-Civita connection `leviCivita g`, the
curvature tensor `riemannTensorAt` and the sectional curvature `sectionalCurvatureAt` of a
metric on an arbitrary manifold, abstractly (Koszul formula, inverse metric). To compute them
for a given metric, one needs their coordinate expressions. This file supplies them on a model
vector space `E` (charted over itself), i.e. in a coordinate chart.

For a smooth family `G : E → E →L E →L ℝ` of symmetric positive-definite forms:

* `isContMDiffMetricSection_cmet`: `G` is a `C^n` metric section in `RiemannianGeometry`'s sense;
* `kz G x v w z = ½(∂_vG(w,z) + ∂_wG(v,z) − ∂_zG(v,w))`, the Christoffel form of the first kind;
* `leviCivita_cmet`: **`∇_X Y = DY·X + Γ(X, Y)`** for any `Γ` with `G(Γ(v,w), z) = kz(v,w,z)`
  (the Christoffel symbols of the second kind);
* `riemannTensorAt_cmet`: **`Rm(u,v,w,z) = G(R(u,v)w, z)`** with
  `R(u,v)w = ∂_uΓ(v,w) − ∂_vΓ(u,w) + Γ(u,Γ(v,w)) − Γ(v,Γ(u,w))`.

`Γ` is taken as an input characterised by the Koszul identity, rather than built from the
inverse metric, so that a concrete metric can supply its Christoffel symbols in closed form.
-/

open RiemannianGeometry VectorField

namespace ExoticSpheres8And10

open Set Function Filter Topology Bundle

open scoped Manifold ContDiff

noncomputable section

section Coord

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### Casts between `E` and its tangent spaces (all identities)

`TangentSpace 𝓘(ℝ, E) x` is `E` by definition, but not reducibly so, and rewriting fails on
terms that mix the two. The explicit casts `toTSv`, `fromTS`, `toTS` keep every statement
type-correct at reducible transparency. -/

/-- A vector of `E` as a tangent vector at `x`. -/
def toTSv (x v : E) : TangentSpace 𝓘(ℝ, E) x := v

/-- A tangent vector at `x` as a vector of `E`. -/
def fromTS {x : E} (v : TangentSpace 𝓘(ℝ, E) x) : E := v

/-- A map `E → E` as a vector field on the manifold `E`. -/
def toTS (X : E → E) : Π x : E, TangentSpace 𝓘(ℝ, E) x := fun x => toTSv x (X x)

@[simp] theorem fromTS_toTSv (x v : E) : fromTS (toTSv x v) = v := rfl
@[simp] theorem toTSv_fromTS {x : E} (v : TangentSpace 𝓘(ℝ, E) x) : toTSv x (fromTS v) = v := rfl
@[simp] theorem toTS_apply (X : E → E) (x : E) : toTS X x = toTSv x (X x) := rfl
@[simp] theorem fromTS_sub {x : E} (a b : TangentSpace 𝓘(ℝ, E) x) :
    fromTS (a - b) = fromTS a - fromTS b := rfl
@[simp] theorem fromTS_zero {x : E} : fromTS (0 : TangentSpace 𝓘(ℝ, E) x) = 0 := rfl

/-- A family of bilinear forms on `E`, as a metric on the manifold `E` in `RiemannianGeometry`'s sense. -/
def cmet (G : E → E →L[ℝ] E →L[ℝ] ℝ) :
    Π x : E, TangentSpace 𝓘(ℝ, E) x →L[ℝ] TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ := G

@[simp] theorem cmet_ts (G : E → E →L[ℝ] E →L[ℝ] ℝ) {x : E} (a b : TangentSpace 𝓘(ℝ, E) x) :
    cmet G x a b = G x (fromTS a) (fromTS b) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- **A `C^n` family of forms is a `C^n` metric section.** On a model space the trivialisation
of `Hom(TE, Hom(TE, ℝ))` is the identity in coordinates. -/
theorem isContMDiffMetricSection_cmet {G : E → E →L[ℝ] E →L[ℝ] ℝ} {n : ℕ∞ω}
    (hG : ContDiff ℝ n G) : IsContMDiffMetricSection E n (cmet G) := by
  intro x
  rw [contMDiffAt_section]
  convert! (hG.contMDiff x)
  ext v w
  simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, TangentSpace, cmet]

theorem isMDiffMetric_cmet {G : E → E →L[ℝ] E →L[ℝ] ℝ} (hG : ContDiff ℝ 1 G) :
    IsMDiffMetric E (cmet G) := fun y =>
  ((isContMDiffMetricSection_cmet hG) y).mdifferentiableAt one_ne_zero

theorem mdiffAt_toTS {X : E → E} {x : E} (hX : ContDiffAt ℝ 1 X x) : MDiffAt (T% (toTS X)) x :=
  ((contMDiffAt_vectorSpace_iff_contDiffAt (V := toTS X)).2 hX).mdifferentiableAt one_ne_zero

theorem cmdiffAt_toTS {X : E → E} {x : E} {n : ℕ∞ω} (hX : ContDiffAt ℝ n X x) :
    CMDiffAt n (T% (toTS X)) x :=
  (contMDiffAt_vectorSpace_iff_contDiffAt (V := toTS X)).2 hX

/-- `d%` (Mathlib's `mvfderiv`) is `fderiv` on a model space. -/
@[simp] theorem mvfderiv_model (f : E → ℝ) (x v : E) :
    mvfderiv 𝓘(ℝ, E) f x (toTSv x v) = fderiv ℝ f x v := by
  unfold mvfderiv
  rw [ContinuousLinearMap.comp_apply, mfderiv_eq_fderiv]
  rfl

@[simp] theorem mlieBracket_toTS (X Y : E → E) (x : E) :
    fromTS (mlieBracket 𝓘(ℝ, E) (toTS X) (toTS Y) x) = fderiv ℝ Y x (X x) - fderiv ℝ X x (Y x) := by
  unfold fromTS
  rw [← mlieBracketWithin_univ, mlieBracketWithin_eq_lieBracketWithin]
  change lieBracketWithin ℝ X Y univ x = _
  rw [lieBracketWithin_univ, lieBracket_eq]

variable {G : E → E →L[ℝ] E →L[ℝ] ℝ}

/-- Nondegeneracy, in coordinates. -/
theorem eq_of_G_eq (hnd : IsNondegenerate (cmet G)) {x a b : E} (h : ∀ z, G x a z = G x b z) :
    a = b := by
  refine sub_eq_zero.1 (hnd x (toTSv x (a - b)) fun w => ?_)
  rw [cmet_ts, fromTS_toTSv, map_sub, ContinuousLinearMap.sub_apply, h, sub_self]

/-- **The Christoffel form of the first kind**, `½(∂_vG(w,z) + ∂_wG(v,z) − ∂_zG(v,w))`. -/
def kz (G : E → E →L[ℝ] E →L[ℝ] ℝ) (x v w z : E) : ℝ :=
  (1 / 2 : ℝ) * (fderiv ℝ G x v w z + fderiv ℝ G x w v z - fderiv ℝ G x z v w)

/-- The derivative of `y ↦ G_y(A(y), B(y))`. -/
theorem fderiv_pair {A B : E → E} {x : E} (hG : DifferentiableAt ℝ G x)
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x) (v : E) :
    fderiv ℝ (fun y => G y (A y) (B y)) x v =
      fderiv ℝ G x v (A x) (B x) + G x (fderiv ℝ A x v) (B x) + G x (A x) (fderiv ℝ B x v) := by
  have h := (hG.hasFDerivAt.clm_apply hA.hasFDerivAt).clm_apply hB.hasFDerivAt
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  ring

theorem G_symm (hsymm : IsSymm (cmet G)) (x a b : E) : G x a b = G x b a :=
  hsymm x (toTSv x a) (toTSv x b)

/-- The derivative of a symmetric family is symmetric. -/
theorem fderiv_symm {x : E} (hsymm : IsSymm (cmet G)) (hG : DifferentiableAt ℝ G x)
    (v a b : E) : fderiv ℝ G x v a b = fderiv ℝ G x v b a := by
  have h1 := fderiv_pair (A := fun _ => a) (B := fun _ => b) hG (differentiableAt_const a)
    (differentiableAt_const b) v
  have h2 := fderiv_pair (A := fun _ => b) (B := fun _ => a) hG (differentiableAt_const b)
    (differentiableAt_const a) v
  have e : (fun y => G y a b) = fun y => G y b a := funext fun y => G_symm hsymm y a b
  simp only [fderiv_const_apply, ContinuousLinearMap.zero_apply, map_zero, add_zero] at h1 h2
  rw [← h1, ← h2, e]

/-- **The Levi-Civita connection in coordinates**: `∇_X Y = DY·X + Γ(X,Y)`, for any `Γ`
satisfying the Koszul identity `G(Γ(v,w), z) = kz(v,w,z)` at `x`. -/
theorem leviCivita_cmet (hsymm : IsSymm (cmet G)) (hnd : IsNondegenerate (cmet G))
    (hG : ContDiff ℝ 1 G) {Γ : E → E → E → E} {x : E}
    (hΓ : ∀ v w z, G x (Γ x v w) z = kz G x v w z)
    {X Y : E → E} (hX : ContDiffAt ℝ 1 X x) (hY : ContDiffAt ℝ 1 Y x) :
    fromTS (leviCivita (cmet G) (toTS Y) x (toTSv x (X x))) =
      fderiv ℝ Y x (X x) + Γ x (X x) (Y x) := by
  have hGd : ∀ y, DifferentiableAt ℝ G y := fun y => (hG.differentiable one_ne_zero) y
  have hXd : DifferentiableAt ℝ X x := hX.differentiableAt one_ne_zero
  have hYd : DifferentiableAt ℝ Y x := hY.differentiableAt one_ne_zero
  refine eq_of_G_eq (x := x) hnd fun z => ?_
  have hspec := leviCivita_spec (g := cmet G) (X := toTS X) (Y := toTS Y)
    (Z := toTS fun _ => z) hsymm hnd (isMDiffMetric_cmet hG)
    (mdiffAt_toTS hX) (mdiffAt_toTS hY) (mdiffAt_toTS contDiffAt_const)
  simp only [koszulRHS, toTS_apply, cmet_ts, fromTS_toTSv, mvfderiv_model, mlieBracket_toTS,
    fderiv_const_apply, ContinuousLinearMap.zero_apply] at hspec
  rw [hspec]
  have hZd : DifferentiableAt ℝ (fun _ : E => z) x := differentiableAt_const z
  have p1 := fderiv_pair (A := Y) (B := fun _ => z) (hGd x) hYd hZd (X x)
  have p2 := fderiv_pair (A := fun _ => z) (B := X) (hGd x) hZd hXd (Y x)
  have p3 := fderiv_pair (A := X) (B := Y) (hGd x) hXd hYd z
  simp only [fderiv_const_apply, ContinuousLinearMap.zero_apply, map_zero, add_zero] at p1 p2 p3
  rw [p1, p2, p3, map_add, ContinuousLinearMap.add_apply, hΓ, kz]
  have s1 := fderiv_symm hsymm (hGd x) (Y x) z (X x)
  have s2 := G_symm hsymm x z (fderiv ℝ X x (Y x))
  have s3 := G_symm hsymm x (X x) (fderiv ℝ Y x z)
  simp only [map_sub, ContinuousLinearMap.sub_apply, zero_sub, map_neg,
    ContinuousLinearMap.neg_apply]
  rw [s1, s2, s3]
  ring

/-- **The Riemann tensor in coordinates.** For `u, v, w, z ∈ E`,
`Rm(u,v,w,z) = G(R(u,v)w, z)` with
`R(u,v)w = ∂_uΓ(v,w) − ∂_vΓ(u,w) + Γ(u,Γ(v,w)) − Γ(v,Γ(u,w))`. -/
theorem riemannTensorAt_cmet (hsymm : IsSymm (cmet G)) (hnd : IsNondegenerate (cmet G))
    (hG : ContDiff ℝ 2 G) {Γ : E → E → E → E}
    (hΓ : ∀ y v w z, G y (Γ y v w) z = kz G y v w z) (x : E) (u v w z : E)
    (hΓu : ContDiffAt ℝ 1 (fun y => Γ y u w) x) (hΓv : ContDiffAt ℝ 1 (fun y => Γ y v w) x) :
    riemannTensorAt hsymm hnd (isContMDiffMetricSection_cmet hG) x (toTSv x u) (toTSv x v)
        (toTSv x w) (toTSv x z) =
      G x (fderiv ℝ (fun y => Γ y v w) x u - fderiv ℝ (fun y => Γ y u w) x v +
        Γ x u (Γ x v w) - Γ x v (Γ x u w)) z := by
  have hG1 : ContDiff ℝ 1 G := hG.of_le (by norm_num)
  rw [riemannTensorAt_apply, cmet_ts, fromTS_toTSv]
  have hR := riemannCurvatureAt_apply hsymm hnd (isContMDiffMetricSection_cmet hG) (x := x)
    (X := toTS fun _ => u) (Y := toTS fun _ => v) (Z := toTS fun _ => w)
    (Eventually.of_forall fun y => cmdiffAt_toTS contDiffAt_const)
    (Eventually.of_forall fun y => cmdiffAt_toTS contDiffAt_const)
    (cmdiffAt_toTS contDiffAt_const)
  simp only [toTS_apply] at hR
  rw [hR]
  have hcovW : ∀ (c y : E),
      leviCivita (cmet G) (toTS fun _ => w) y (toTSv y c) = toTSv y (Γ y c w) := fun c y => by
    have := leviCivita_cmet (G := G) hsymm hnd hG1 (x := y) (hΓ y) (X := fun _ => c)
      (Y := fun _ => w) contDiffAt_const contDiffAt_const
    rw [fderiv_const_apply, ContinuousLinearMap.zero_apply, zero_add] at this
    rw [← this, toTSv_fromTS]
  have e1 : (fun y => leviCivita (cmet G) (toTS fun _ => w) y (toTS (fun _ => v) y)) =
      toTS fun y => Γ y v w := funext fun y => by rw [toTS_apply, hcovW, toTS_apply]
  have e2 : (fun y => leviCivita (cmet G) (toTS fun _ => w) y (toTS (fun _ => u) y)) =
      toTS fun y => Γ y u w := funext fun y => by rw [toTS_apply, hcovW, toTS_apply]
  have h1 := leviCivita_cmet (G := G) hsymm hnd hG1 (hΓ x) (X := fun _ => u)
    (Y := fun y => Γ y v w) contDiffAt_const hΓv
  have h2 := leviCivita_cmet (G := G) hsymm hnd hG1 (hΓ x) (X := fun _ => v)
    (Y := fun y => Γ y u w) contDiffAt_const hΓu
  have hb : mlieBracket 𝓘(ℝ, E) (toTS fun _ => u) (toTS fun _ => v) x = 0 := by
    have := mlieBracket_toTS (fun _ : E => u) (fun _ : E => v) x
    simp only [fderiv_const_apply, ContinuousLinearMap.zero_apply, sub_zero] at this
    exact this
  unfold curvature
  rw [e1, e2, hb, map_zero, sub_zero, fromTS_sub, toTS_apply, toTS_apply]
  rw [h1, h2]
  congr 1
  abel

end Coord

end

end ExoticSpheres8And10
