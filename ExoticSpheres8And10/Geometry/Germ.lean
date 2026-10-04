/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Geometry.Naturality

/-! # Infrastructure: `RiemannianGeometry`'s curvature depends only on the germ of the metric

If two metrics `g`, `g'` agree on a neighbourhood of `x`, then:

* `koszulRHS_congr_metric`: their Koszul right-hand sides agree at `x`;
* `leviCivita_congr_metric`: their Levi-Civita connections agree at `x`;
* `riemannTensorAt_congr_metric`, **`sectionalCurvatureAt_congr_metric`**: their Riemann tensors
  and sectional curvatures agree at `x`.

This is the locality step: curvature computed from any metric that coincides with the given one
near a point is the curvature at that point.
-/

open RiemannianGeometry VectorField Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology

open scoped Manifold ContDiff

noncomputable section

section Germ

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {g g' : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem koszulRHS_congr_metric {x : M} (h : ∀ᶠ y in 𝓝 x, g y = g' y)
    (X Y Z : Π y : M, TangentSpace I y) : koszulRHS g X Y x Z = koszulRHS g' X Y x Z := by
  have hp : ∀ A B : Π y : M, TangentSpace I y,
      (fun y => g y (A y) (B y)) =ᶠ[𝓝 x] fun y => g' y (A y) (B y) := fun A B =>
    h.mono fun y hy => by show g y (A y) (B y) = g' y (A y) (B y); rw [hy]
  have hm : ∀ A B : Π y : M, TangentSpace I y, mvfderiv I (fun y => g y (A y) (B y)) x =
      mvfderiv I (fun y => g' y (A y) (B y)) x := fun A B => by
    simp only [mvfderiv]
    rw [(hp A B).mfderiv_eq]
    rfl
  have hx : g x = g' x := h.self_of_nhds
  simp only [koszulRHS]
  rw [hm, hm, hm, hx]

omit [CompleteSpace E] in
/-- **The Levi-Civita connection depends only on the germ of the metric.** -/
theorem leviCivita_congr_metric (hs : IsSymm g) (hnd : IsNondegenerate g) (hg : IsMDiffMetric E g)
    (hs' : IsSymm g') (hnd' : IsNondegenerate g') (hg' : IsMDiffMetric E g') {x : M}
    (h : ∀ᶠ y in 𝓝 x, g y = g' y) {Y : Π y : M, TangentSpace I y} (hY : MDiffAt (T% Y) x)
    (v : TangentSpace I x) : leviCivita g Y x v = leviCivita g' Y x v := by
  set X : Π y : M, TangentSpace I y := FiberBundle.extend E v
  have hX : MDiffAt (T% X) x := FiberBundle.mdifferentiableAt_extend I E _
  have hXx : X x = v := FiberBundle.extend_apply_self E _
  have hx : g x = g' x := h.self_of_nhds
  refine eq_of_g_eq (hnd x) fun w => ?_
  set Z : Π y : M, TangentSpace I y := FiberBundle.extend E w
  have hZ : MDiffAt (T% Z) x := FiberBundle.mdifferentiableAt_extend I E _
  have hZw : Z x = w := FiberBundle.extend_apply_self E w
  have h1 := leviCivita_spec (g := g) hs hnd hg hX hY hZ
  have h2 := leviCivita_spec (g := g') hs' hnd' hg' hX hY hZ
  rw [← hZw, ← hXx, h1, koszulRHS_congr_metric h, ← h2, hx]

omit [CompleteSpace E] in
/-- **The curvature operator depends only on the germ of the metric.** -/
theorem curvature_congr_metric (hs : IsSymm g) (hnd : IsNondegenerate g)
    (hg : IsContMDiffMetricSection E 2 g) (hs' : IsSymm g') (hnd' : IsNondegenerate g')
    (hg' : IsContMDiffMetricSection E 2 g') {x : M} (h : ∀ᶠ y in 𝓝 x, g y = g' y)
    {X Y Z : Π y : M, TangentSpace I y}
    (hX : ∀ᶠ z in 𝓝 x, CMDiffAt (2 : ℕ∞ω) (T% X) z)
    (hY : ∀ᶠ z in 𝓝 x, CMDiffAt (2 : ℕ∞ω) (T% Y) z)
    (hZ : ∀ᶠ z in 𝓝 x, CMDiffAt (2 : ℕ∞ω) (T% Z) z) :
    curvature (leviCivita g) X Y Z x = curvature (leviCivita g') X Y Z x := by
  have hg1 : IsMDiffMetric E g := hg.isMDiffMetric (by simp)
  have hg1' : IsMDiffMetric E g' := hg'.isMDiffMetric (by simp)
  have hmd : ∀ {V : Π y : M, TangentSpace I y}, (∀ᶠ z in 𝓝 x, CMDiffAt (2 : ℕ∞ω) (T% V) z) →
      ∀ᶠ y in 𝓝 x, MDiffAt (T% V) y := fun hV =>
    eventually_mdiffAt_of_eventually_contMDiffAt_two hV
  have hh := h.eventually_nhds
  have eY : ∀ᶠ y in 𝓝 x, leviCivita g Z y (Y y) = leviCivita g' Z y (Y y) :=
    ((hmd hZ).and hh).mono fun y hy =>
      leviCivita_congr_metric hs hnd hg1 hs' hnd' hg1' hy.2 hy.1 _
  have eX : ∀ᶠ y in 𝓝 x, leviCivita g Z y (X y) = leviCivita g' Z y (X y) :=
    ((hmd hZ).and hh).mono fun y hy =>
      leviCivita_congr_metric hs hnd hg1 hs' hnd' hg1' hy.2 hy.1 _
  have hcov := covC2LocalMDiffAt_leviCivita hs' hnd' hg' x Z hZ
  have hWY : MDiffAt (T% (fun z => leviCivita g' Z z (Y z))) x :=
    mdiffAt_cov_apply hcov (hY.self_of_nhds.mdifferentiableAt (by simp))
  have hWX : MDiffAt (T% (fun z => leviCivita g' Z z (X z))) x :=
    mdiffAt_cov_apply hcov (hX.self_of_nhds.mdifferentiableAt (by simp))
  have hZd : MDiffAt (T% Z) x := hZ.self_of_nhds.mdifferentiableAt (by simp)
  simp only [curvature]
  rw [leviCivita_congr_of_eventuallyEq eY, leviCivita_congr_of_eventuallyEq eX,
    leviCivita_congr_metric hs hnd hg1 hs' hnd' hg1' h hWY,
    leviCivita_congr_metric hs hnd hg1 hs' hnd' hg1' h hWX,
    leviCivita_congr_metric hs hnd hg1 hs' hnd' hg1' h hZd]

/-- **The Riemann tensor depends only on the germ of the metric.** -/
theorem riemannTensorAt_congr_metric (hs : IsSymm g) (hnd : IsNondegenerate g)
    (hg : IsContMDiffMetricSection E 2 g) (hs' : IsSymm g') (hnd' : IsNondegenerate g')
    (hg' : IsContMDiffMetricSection E 2 g') {x : M} (h : ∀ᶠ y in 𝓝 x, g y = g' y)
    (u v w z : TangentSpace I x) :
    riemannTensorAt hs hnd hg x u v w z = riemannTensorAt hs' hnd' hg' x u v w z := by
  set X : Π y : M, TangentSpace I y := FiberBundle.extend E u
  set Y : Π y : M, TangentSpace I y := FiberBundle.extend E v
  set Z : Π y : M, TangentSpace I y := FiberBundle.extend E w
  have hX := eventually_contMDiffAt_extendTangent (k := (2 : ℕ∞ω)) (I := I) (M := M) u
  have hY := eventually_contMDiffAt_extendTangent (k := (2 : ℕ∞ω)) (I := I) (M := M) v
  have hZ := eventually_contMDiffAt_extendTangent (k := (2 : ℕ∞ω)) (I := I) (M := M) w
  have hR := riemannCurvatureAt_apply hs hnd hg (x := x) hX hY hZ.self_of_nhds
  have hR' := riemannCurvatureAt_apply hs' hnd' hg' (x := x) hX hY hZ.self_of_nhds
  simp only [X, Y, Z, FiberBundle.extend_apply_self] at hR hR'
  rw [riemannTensorAt_apply, riemannTensorAt_apply, hR, hR', h.self_of_nhds,
    curvature_congr_metric hs hnd hg hs' hnd' hg' h hX hY hZ]

/-- **The sectional curvature depends only on the germ of the metric.** -/
theorem sectionalCurvatureAt_congr_metric (hs : IsSymm g) (hp : IsPosDef g)
    (hg : IsContMDiffMetricSection E 2 g) (hs' : IsSymm g') (hp' : IsPosDef g')
    (hg' : IsContMDiffMetricSection E 2 g') {x : M} (h : ∀ᶠ y in 𝓝 x, g y = g' y)
    (u v : TangentSpace I x) :
    sectionalCurvatureAt hs hp hg x u v = sectionalCurvatureAt hs' hp' hg' x u v := by
  rw [sectionalCurvatureAt_def, sectionalCurvatureAt_def,
    riemannTensorAt_congr_metric hs hp.isNondegenerate hg hs' hp'.isNondegenerate hg' h]
  simp only [gramDet, h.self_of_nhds]

end Germ

end

end ExoticSpheres8And10
