/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Curvature.Boundary.QuotientSFF

/-! # Local naturality: maps that are local isometries only near a point

`S4_Natural` and `sff_pullback` need a map `f : M → N` that is smooth, with invertible
differential and `g_M = f^*g_N`, **everywhere**. The gluing boundary needs these facts for maps
that are local isometries only on a neighbourhood of the boundary. Examples are the gauge
`(y, u) ↦ (y, θ̂(y)u)`, which is singular at the south pole, and the chart transition near
`t = a`.

With the hypotheses only near `x` (smoothness and invertibility at `x`, and `g_M = f^*g_N` on a
neighbourhood):
* `koszulRHS_mpullback_loc`, `mfderiv_leviCivita_mpullback_loc`;
* `gradAt_pullback_loc`, `unitNormal_pullback_loc` (eventually near `x`);
* **`sff_pullback_loc`**.
-/

open RiemannianGeometry VectorField Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology

open scoped Manifold ContDiff

noncomputable section

section Local

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [FiniteDimensional ℝ E'] {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
  {f : M → N}
  {gM : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
  {gN : Π y : N, TangentSpace I' y →L[ℝ] TangentSpace I' y →L[ℝ] ℝ}

theorem mvfderiv_congr_of_eventuallyEq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ ψ : M → F} {x : M} (h : φ =ᶠ[𝓝 x] ψ) : mvfderiv I φ x = mvfderiv I ψ x := by
  unfold mvfderiv; rw [h.mfderiv_eq, h.eq_of_nhds]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ M] [CompleteSpace E']
  [FiniteDimensional ℝ E'] [IsManifold I' ∞ N] in
theorem mfderiv_mpullback_at {x : M} (hfix : (mfderiv I I' f x).IsInvertible)
    (V : Π y : N, TangentSpace I' y) : mfderiv I I' f x (mpullback I I' f V x) = V (f x) := by
  rw [mpullback_apply]; exact hfix.self_apply_inverse _

/-- **The Koszul right-hand side is natural**, for a local isometry near `x`. -/
theorem koszulRHS_mpullback_loc {x : M} (hfx : ContMDiffAt I I' ∞ f x)
    (hfi : ∀ᶠ y in 𝓝 x, (mfderiv I I' f y).IsInvertible)
    (hpull : ∀ᶠ y in 𝓝 x, ∀ u v, gM y u v = gN (f y) (mfderiv I I' f y u) (mfderiv I I' f y v))
    (hgN : IsMDiffMetric E' gN) {X Y Z : Π y : N, TangentSpace I' y}
    (hX : MDiffAt (T% X) (f x)) (hY : MDiffAt (T% Y) (f x)) (hZ : MDiffAt (T% Z) (f x)) :
    koszulRHS gM (mpullback I I' f X) (mpullback I I' f Y) x (mpullback I I' f Z) =
      koszulRHS gN X Y (f x) Z := by
  have hfxd : MDiffAt f x := hfx.mdifferentiableAt (by simp)
  haveI : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le minSmoothness_two_le_infty
  haveI : IsManifold I' (minSmoothness ℝ 2) N := IsManifold.of_le minSmoothness_two_le_infty
  have hfix := hfi.self_of_nhds
  have pair : ∀ A B : Π y : N, TangentSpace I' y,
      (fun y => gM y (mpullback I I' f A y) (mpullback I I' f B y)) =ᶠ[𝓝 x]
        (fun y' => gN y' (A y') (B y')) ∘ f := fun A B => by
    filter_upwards [hfi, hpull] with y hy hy'
    show gM y _ _ = gN (f y) (A (f y)) (B (f y))
    rw [hy', mfderiv_mpullback_at hy, mfderiv_mpullback_at hy]
  have b1 := mpullback_mlieBracket (n := ∞) hX hY hfx minSmoothness_two_le_infty
  have b2 := mpullback_mlieBracket (n := ∞) hX hZ hfx minSmoothness_two_le_infty
  have b3 := mpullback_mlieBracket (n := ∞) hY hZ hfx minSmoothness_two_le_infty
  simp only [koszulRHS]
  rw [mvfderiv_congr_of_eventuallyEq (pair Y Z), mvfderiv_congr_of_eventuallyEq (pair Z X),
    mvfderiv_congr_of_eventuallyEq (pair X Y),
    mvfderiv_comp x (mdiffAt_pairing (hgN (f x)) hY hZ) hfxd,
    mvfderiv_comp x (mdiffAt_pairing (hgN (f x)) hZ hX) hfxd,
    mvfderiv_comp x (mdiffAt_pairing (hgN (f x)) hX hY) hfxd, ← b1, ← b2, ← b3,
    hpull.self_of_nhds, hpull.self_of_nhds, hpull.self_of_nhds]
  simp only [ContinuousLinearMap.comp_apply, mfderiv_mpullback_at hfix]

/-- **The Levi-Civita connection is natural**, for a local isometry near `x`. -/
theorem mfderiv_leviCivita_mpullback_loc {x : M} (hfx : ContMDiffAt I I' ∞ f x)
    (hfi : ∀ᶠ y in 𝓝 x, (mfderiv I I' f y).IsInvertible)
    (hpull : ∀ᶠ y in 𝓝 x, ∀ u v, gM y u v = gN (f y) (mfderiv I I' f y u) (mfderiv I I' f y v))
    (hsM : IsSymm gM) (hndM : IsNondegenerate gM) (hgM : IsMDiffMetric E gM)
    (hsN : IsSymm gN) (hndN : IsNondegenerate gN) (hgN : IsMDiffMetric E' gN)
    {Y : Π y : N, TangentSpace I' y} (hY : MDiffAt (T% Y) (f x)) (v : TangentSpace I x) :
    mfderiv I I' f x (leviCivita gM (mpullback I I' f Y) x v) =
      leviCivita gN Y (f x) (mfderiv I I' f x v) := by
  have hfix := hfi.self_of_nhds
  set X : Π y : N, TangentSpace I' y := FiberBundle.extend E' (mfderiv I I' f x v)
  have hX : MDiffAt (T% X) (f x) := FiberBundle.mdifferentiableAt_extend I' E' _
  have hXx : X (f x) = mfderiv I I' f x v := FiberBundle.extend_apply_self E' _
  have hXv : mpullback I I' f X x = v := by
    rw [mpullback_apply, hXx]; exact hfix.inverse_apply_self v
  refine eq_of_g_eq (hndN (f x)) fun w => ?_
  set Z : Π y : N, TangentSpace I' y := FiberBundle.extend E' w
  have hZ : MDiffAt (T% Z) (f x) := FiberBundle.mdifferentiableAt_extend I' E' _
  have hZw : Z (f x) = w := FiberBundle.extend_apply_self E' w
  have hpX := MDifferentiableAt.mpullback_vectorField (n := ∞) hX hfx hfix two_le_infty'
  have hpY := MDifferentiableAt.mpullback_vectorField (n := ∞) hY hfx hfix two_le_infty'
  have hpZ := MDifferentiableAt.mpullback_vectorField (n := ∞) hZ hfx hfix two_le_infty'
  have hsM' := leviCivita_spec (g := gM) hsM hndM hgM hpX hpY hpZ
  have hsN' := leviCivita_spec (g := gN) hsN hndN hgN hX hY hZ
  rw [← hZw, ← mfderiv_mpullback_at hfix Z, ← hpull.self_of_nhds, ← hXv, hsM',
    koszulRHS_mpullback_loc hfx hfi hpull hgN hX hY hZ, ← hsN', mfderiv_mpullback_at hfix,
    mfderiv_mpullback_at hfix]

theorem gradAt_pullback_loc (hndM : IsNondegenerate gM) (hndN : IsNondegenerate gN)
    {h : N → ℝ} {y : M} (hfy : MDiffAt f y) (hhy : MDiffAt h (f y))
    (hfiy : (mfderiv I I' f y).IsInvertible)
    (hpy : ∀ u v, gM y u v = gN (f y) (mfderiv I I' f y u) (mfderiv I I' f y v)) :
    mfderiv I I' f y (gradAt hndM (h ∘ f) y) = gradAt hndN h (f y) := by
  refine eq_gradAt hndN h (f y) fun w => ?_
  obtain ⟨u, rfl⟩ : ∃ u, mfderiv I I' f y u = w :=
    ⟨(mfderiv I I' f y).inverse w, hfiy.self_apply_inverse w⟩
  rw [← hpy, g_gradAt, mvfderiv_comp' hhy hfy]

theorem unitNormal_pullback_loc (hndM : IsNondegenerate gM) (hndN : IsNondegenerate gN)
    {h : N → ℝ} {y : M} (hfy : MDiffAt f y) (hhy : MDiffAt h (f y))
    (hfiy : (mfderiv I I' f y).IsInvertible)
    (hpy : ∀ u v, gM y u v = gN (f y) (mfderiv I I' f y u) (mfderiv I I' f y v)) :
    unitNormal hndM (h ∘ f) y = mpullback I I' f (unitNormal hndN h) y := by
  have hg := gradAt_pullback_loc hndM hndN hfy hhy hfiy hpy
  rw [mpullback_apply]
  refine (hfiy.inverse_apply_self _).symm.trans ?_
  congr 1
  simp only [unitNormal, map_smul, hg, hpy, hg]

/-- **The second fundamental form is natural under local isometries near `x`.** -/
theorem sff_pullback_loc {x : M} (hf : ∀ᶠ y in 𝓝 x, ContMDiffAt I I' ∞ f y)
    (hfi : ∀ᶠ y in 𝓝 x, (mfderiv I I' f y).IsInvertible)
    (hpull : ∀ᶠ y in 𝓝 x, ∀ u v, gM y u v = gN (f y) (mfderiv I I' f y u) (mfderiv I I' f y v))
    (hsM : IsSymm gM) (hndM : IsNondegenerate gM) (hgM : IsMDiffMetric E gM)
    (hsN : IsSymm gN) (hndN : IsNondegenerate gN) (hgN : IsMDiffMetric E' gN) {h : N → ℝ}
    (hh : ContMDiff I' 𝓘(ℝ, ℝ) ∞ h)
    (hν : MDiffAt (T% (unitNormal hndN h)) (f x)) (v w : TangentSpace I x) :
    sff hndM (h ∘ f) x v w = sff hndN h (f x) (mfderiv I I' f x v) (mfderiv I I' f x w) := by
  have hev : ∀ᶠ y in 𝓝 x, unitNormal hndM (h ∘ f) y = mpullback I I' f (unitNormal hndN h) y := by
    filter_upwards [hf, hfi, hpull] with y hy1 hy2 hy3
    exact unitNormal_pullback_loc hndM hndN (hy1.mdifferentiableAt (by simp))
      ((hh _).mdifferentiableAt (by simp)) hy2 hy3
  unfold sff
  rw [leviCivita_congr_of_eventuallyEq hev, hpull.self_of_nhds,
    mfderiv_leviCivita_mpullback_loc hf.self_of_nhds hfi hpull hsM hndM hgM hsN hndN hgN hν]

end Local

end

end ExoticSpheres8And10
