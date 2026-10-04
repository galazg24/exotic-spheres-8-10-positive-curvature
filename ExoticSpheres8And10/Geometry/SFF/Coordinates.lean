/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Geometry.SFF.LevelSets

/-! # Second fundamental forms in coordinates

On a model space `E` with a metric field `G : E → E →L E →L ℝ` (`cmet G`):

* `G_leviCivita_cmet`: `G(∇_X Y, z) = G(DY·X, z) + kz(X, Y, z)`, the Koszul form, with no
  Christoffel symbols of the second kind needed;
* **`G_leviCivita_cmet_self`**: for a constant direction `Z`,
  `G(∇_Z ν, Z) = G(Dν·Z, Z) + ½ DG(ν)(Z, Z)`;
* `gradAt_cmet`, `unitNormal_cmet`: the gradient and the unit normal, identified from any
  explicit candidate;
* **`sff_cmet`**: `sff = G(Dν·Z, Z) + ½ DG(ν)(Z, Z)` for any smooth field `ν` equal to the unit
  normal near `x`.
-/

open RiemannianGeometry Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Real

open scoped Manifold ContDiff

noncomputable section

section Coord

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {G : E → E →L[ℝ] E →L[ℝ] ℝ}

/-- **The Koszul form of `∇`, in coordinates.** -/
theorem G_leviCivita_cmet (hsymm : IsSymm (cmet G)) (hnd : IsNondegenerate (cmet G))
    (hG : ContDiff ℝ 1 G) {x : E} {X Y : E → E} (hX : ContDiffAt ℝ 1 X x)
    (hY : ContDiffAt ℝ 1 Y x) (z : E) :
    G x (fromTS (leviCivita (cmet G) (toTS Y) x (toTSv x (X x)))) z =
      G x (fderiv ℝ Y x (X x)) z + kz G x (X x) (Y x) z := by
  have hGd : ∀ y, DifferentiableAt ℝ G y := fun y => (hG.differentiable one_ne_zero) y
  have hXd : DifferentiableAt ℝ X x := hX.differentiableAt one_ne_zero
  have hYd : DifferentiableAt ℝ Y x := hY.differentiableAt one_ne_zero
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
  rw [p1, p2, p3, kz]
  have s1 := fderiv_symm hsymm (hGd x) (Y x) z (X x)
  have s2 := G_symm hsymm x z (fderiv ℝ X x (Y x))
  have s3 := G_symm hsymm x (X x) (fderiv ℝ Y x z)
  simp only [map_sub, ContinuousLinearMap.sub_apply, zero_sub, map_neg,
    ContinuousLinearMap.neg_apply]
  rw [s1, s2, s3]
  ring

/-- **The coordinate formula for `g(∇_Z ν, Z)`.** -/
theorem G_leviCivita_cmet_self (hsymm : IsSymm (cmet G)) (hnd : IsNondegenerate (cmet G))
    (hG : ContDiff ℝ 1 G) {x : E} {ν : E → E} (hν : ContDiffAt ℝ 1 ν x) (Z : E) :
    G x (fromTS (leviCivita (cmet G) (toTS ν) x (toTSv x Z))) Z =
      G x (fderiv ℝ ν x Z) Z + (1 / 2) * fderiv ℝ G x (ν x) Z Z := by
  have h := G_leviCivita_cmet (X := fun _ => Z) hsymm hnd hG contDiffAt_const hν Z
  rw [h, kz, fderiv_symm hsymm ((hG.differentiable one_ne_zero) x) Z (ν x) Z]
  ring

omit [CompleteSpace E] in
/-- The gradient, identified from an explicit candidate. -/
theorem gradAt_cmet (hnd : IsNondegenerate (cmet G)) {f : E → ℝ} {x v : E}
    (hv : ∀ w, G x v w = fderiv ℝ f x w) : gradAt hnd f x = toTSv x v :=
  (eq_gradAt hnd f x fun w => by
    rw [cmet_ts, fromTS_toTSv]; exact (hv _).trans (mvfderiv_model f x w).symm).symm

omit [CompleteSpace E] in
/-- The unit normal, identified from an explicit gradient. -/
theorem unitNormal_cmet (hnd : IsNondegenerate (cmet G)) {f : E → ℝ} {x v : E}
    (hv : ∀ w, G x v w = fderiv ℝ f x w) :
    unitNormal hnd f x = toTSv x ((√(G x v v))⁻¹ • v) := by
  simp only [unitNormal, gradAt_cmet hnd hv, cmet_ts, fromTS_toTSv]
  rfl

/-- **The second fundamental form in coordinates**: if a `C¹` field `ν` equals the unit normal
of `f` near `x`, then `sff(Z, Z) = G(Dν·Z, Z) + ½ DG(ν)(Z, Z)`. -/
theorem sff_cmet (hsymm : IsSymm (cmet G)) (hnd : IsNondegenerate (cmet G))
    (hG : ContDiff ℝ 1 G) {f : E → ℝ} {x : E} {ν : E → E} (hν : ContDiffAt ℝ 1 ν x)
    (hνeq : ∀ᶠ y in 𝓝 x, unitNormal hnd f y = toTS ν y) (Z : E) :
    sff hnd f x (toTSv x Z) (toTSv x Z) =
      G x (fderiv ℝ ν x Z) Z + (1 / 2) * fderiv ℝ G x (ν x) Z Z := by
  unfold sff
  rw [leviCivita_congr_of_eventuallyEq hνeq, cmet_ts]
  exact G_leviCivita_cmet_self hsymm hnd hG hν Z

end Coord

end

end ExoticSpheres8And10
