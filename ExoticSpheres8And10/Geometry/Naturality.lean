/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import RiemannianGeometry.SectionalCurvature
import RiemannianGeometry.CurvatureBundled
import RiemannianGeometry.LeviCivitaGerm
import Mathlib

/-! # Infrastructure: naturality of `RiemannianGeometry`'s Levi-Civita connection and curvature

For a smooth map `f : M → N` with invertible differential at every point (a local
diffeomorphism) and metrics with `g_M = f^* g_N`:

* `mfderiv_leviCivita_mpullback`: `df(∇^M_v (f^*Y)) = ∇^N_{df v} Y`;
* `mfderiv_curvature_mpullback`: `df(R^M(f^*X, f^*Y) f^*Z) = R^N(X, Y) Z` at `f x`;
* **`riemannTensorAt_pullback`**: `Rm^M_x(u,v,w,z) = Rm^N_{f x}(df u, df v, df w, df z)`;
* **`sectionalCurvatureAt_pullback`**: the sectional curvatures agree.

The proof characterises both connections by the Koszul formula (`RiemannianGeometry`'s `leviCivita_spec`). Every
Koszul term is natural: the derivative terms by the chain rule, and the brackets by Mathlib's
`mpullback_mlieBracket`. Nondegeneracy and surjectivity of `df` then conclude. The curvature
follows by `RiemannianGeometry`'s germ locality (`leviCivita_congr_of_eventuallyEq`).

This is the chart-change step: curvature computed in any coordinate system that is a local
isometry is the curvature of the manifold.
-/

open RiemannianGeometry VectorField Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology

open scoped Manifold ContDiff

noncomputable section

theorem two_le_infty' : (2 : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top

theorem minSmoothness_two_le_infty : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
  rw [minSmoothness_of_isRCLikeNormedField]; exact two_le_infty'

section Natural

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [FiniteDimensional ℝ E'] {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
  {f : M → N}
  {gM : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
  {gN : Π y : N, TangentSpace I' y →L[ℝ] TangentSpace I' y →L[ℝ] ℝ}

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ M] [CompleteSpace E']
  [FiniteDimensional ℝ E'] [IsManifold I' ∞ N] in
theorem mfderiv_mpullback (hfi : ∀ x, (mfderiv I I' f x).IsInvertible) (x : M)
    (V : Π y : N, TangentSpace I' y) : mfderiv I I' f x (mpullback I I' f V x) = V (f x) := by
  rw [mpullback_apply]; exact (hfi x).self_apply_inverse _

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ M] [CompleteSpace E']
  [FiniteDimensional ℝ E'] [IsManifold I' ∞ N] in
theorem mpullback_mfderiv (hfi : ∀ x, (mfderiv I I' f x).IsInvertible) {x : M}
    (v : TangentSpace I x) : (mfderiv I I' f x).inverse (mfderiv I I' f x v) = v :=
  (hfi x).inverse_apply_self v

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ M] [CompleteSpace E']
  [FiniteDimensional ℝ E'] [IsManifold I' ∞ N] in
theorem pairing_mpullback (hfi : ∀ x, (mfderiv I I' f x).IsInvertible)
    (hpull : ∀ x u v, gM x u v = gN (f x) (mfderiv I I' f x u) (mfderiv I I' f x v))
    (Y Z : Π y : N, TangentSpace I' y) (y : M) :
    gM y (mpullback I I' f Y y) (mpullback I I' f Z y) = gN (f y) (Y (f y)) (Z (f y)) := by
  rw [hpull, mfderiv_mpullback hfi, mfderiv_mpullback hfi]

/-- **The Koszul right-hand side is natural.** -/
theorem koszulRHS_mpullback (hf : ContMDiff I I' ∞ f)
    (hfi : ∀ x, (mfderiv I I' f x).IsInvertible)
    (hpull : ∀ x u v, gM x u v = gN (f x) (mfderiv I I' f x u) (mfderiv I I' f x v))
    (hgN : IsMDiffMetric E' gN) {X Y Z : Π y : N, TangentSpace I' y} {x : M}
    (hX : MDiffAt (T% X) (f x)) (hY : MDiffAt (T% Y) (f x)) (hZ : MDiffAt (T% Z) (f x)) :
    koszulRHS gM (mpullback I I' f X) (mpullback I I' f Y) x (mpullback I I' f Z) =
      koszulRHS gN X Y (f x) Z := by
  have hfx : MDiffAt f x := (hf x).mdifferentiableAt (by simp)
  haveI : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le minSmoothness_two_le_infty
  haveI : IsManifold I' (minSmoothness ℝ 2) N := IsManifold.of_le minSmoothness_two_le_infty
  have e1 : (fun y => gM y (mpullback I I' f Y y) (mpullback I I' f Z y)) =
      (fun y' => gN y' (Y y') (Z y')) ∘ f := funext (pairing_mpullback hfi hpull Y Z)
  have e2 : (fun y => gM y (mpullback I I' f Z y) (mpullback I I' f X y)) =
      (fun y' => gN y' (Z y') (X y')) ∘ f := funext (pairing_mpullback hfi hpull Z X)
  have e3 : (fun y => gM y (mpullback I I' f X y) (mpullback I I' f Y y)) =
      (fun y' => gN y' (X y') (Y y')) ∘ f := funext (pairing_mpullback hfi hpull X Y)
  have b1 := mpullback_mlieBracket (n := ∞) hX hY (hf x) minSmoothness_two_le_infty
  have b2 := mpullback_mlieBracket (n := ∞) hX hZ (hf x) minSmoothness_two_le_infty
  have b3 := mpullback_mlieBracket (n := ∞) hY hZ (hf x) minSmoothness_two_le_infty
  simp only [koszulRHS]
  rw [e1, e2, e3, mvfderiv_comp x (mdiffAt_pairing (hgN (f x)) hY hZ) hfx,
    mvfderiv_comp x (mdiffAt_pairing (hgN (f x)) hZ hX) hfx,
    mvfderiv_comp x (mdiffAt_pairing (hgN (f x)) hX hY) hfx, ← b1, ← b2, ← b3,
    hpull, hpull, hpull]
  simp only [ContinuousLinearMap.comp_apply, mfderiv_mpullback hfi]

/-- **The Levi-Civita connection is natural**: `df(∇^M_v f^*Y) = ∇^N_{df v} Y`. -/
theorem mfderiv_leviCivita_mpullback (hf : ContMDiff I I' ∞ f)
    (hfi : ∀ x, (mfderiv I I' f x).IsInvertible)
    (hpull : ∀ x u v, gM x u v = gN (f x) (mfderiv I I' f x u) (mfderiv I I' f x v))
    (hsM : IsSymm gM) (hndM : IsNondegenerate gM) (hgM : IsMDiffMetric E gM)
    (hsN : IsSymm gN) (hndN : IsNondegenerate gN) (hgN : IsMDiffMetric E' gN)
    {Y : Π y : N, TangentSpace I' y} {x : M} (hY : MDiffAt (T% Y) (f x))
    (v : TangentSpace I x) :
    mfderiv I I' f x (leviCivita gM (mpullback I I' f Y) x v) =
      leviCivita gN Y (f x) (mfderiv I I' f x v) := by
  set X : Π y : N, TangentSpace I' y := FiberBundle.extend E' (mfderiv I I' f x v)
  have hX : MDiffAt (T% X) (f x) := FiberBundle.mdifferentiableAt_extend I' E' _
  have hXx : X (f x) = mfderiv I I' f x v := FiberBundle.extend_apply_self E' _
  have hXv : mpullback I I' f X x = v := by
    rw [mpullback_apply, hXx]; exact mpullback_mfderiv hfi v
  refine eq_of_g_eq (hndN (f x)) fun w => ?_
  set Z : Π y : N, TangentSpace I' y := FiberBundle.extend E' w
  have hZ : MDiffAt (T% Z) (f x) := FiberBundle.mdifferentiableAt_extend I' E' _
  have hZw : Z (f x) = w := FiberBundle.extend_apply_self E' w
  have hpX := MDifferentiableAt.mpullback_vectorField (n := ∞) hX (hf x) (hfi x) two_le_infty'
  have hpY := MDifferentiableAt.mpullback_vectorField (n := ∞) hY (hf x) (hfi x) two_le_infty'
  have hpZ := MDifferentiableAt.mpullback_vectorField (n := ∞) hZ (hf x) (hfi x) two_le_infty'
  have hsM' := leviCivita_spec (g := gM) hsM hndM hgM hpX hpY hpZ
  have hsN' := leviCivita_spec (g := gN) hsN hndN hgN hX hY hZ
  rw [← hZw, ← mfderiv_mpullback hfi x Z, ← hpull, ← hXv, hsM',
    koszulRHS_mpullback hf hfi hpull hgN hX hY hZ, ← hsN', mfderiv_mpullback hfi,
    mfderiv_mpullback hfi]

/-- The field form: `∇^M_{f^*X} f^*Y = f^*(∇^N_X Y)` at every point where `X`, `Y` are
differentiable. -/
theorem leviCivita_mpullback_eq (hf : ContMDiff I I' ∞ f)
    (hfi : ∀ x, (mfderiv I I' f x).IsInvertible)
    (hpull : ∀ x u v, gM x u v = gN (f x) (mfderiv I I' f x u) (mfderiv I I' f x v))
    (hsM : IsSymm gM) (hndM : IsNondegenerate gM) (hgM : IsMDiffMetric E gM)
    (hsN : IsSymm gN) (hndN : IsNondegenerate gN) (hgN : IsMDiffMetric E' gN)
    {X Y : Π y : N, TangentSpace I' y} {x : M} (hY : MDiffAt (T% Y) (f x)) :
    leviCivita gM (mpullback I I' f Y) x (mpullback I I' f X x) =
      mpullback I I' f (fun z => leviCivita gN Y z (X z)) x := by
  have h := mfderiv_leviCivita_mpullback hf hfi hpull hsM hndM hgM hsN hndN hgN hY
    (mpullback I I' f X x)
  rw [mfderiv_mpullback hfi] at h
  rw [mpullback_apply (V := fun z => leviCivita gN Y z (X z)), ← h, mpullback_mfderiv hfi]

/-- **Curvature is natural**: `df(R^M(f^*X, f^*Y) f^*Z) = R^N(X, Y) Z` at `f x`, for fields `C²`
near `f x`. -/
theorem mfderiv_curvature_mpullback (hf : ContMDiff I I' ∞ f)
    (hfi : ∀ x, (mfderiv I I' f x).IsInvertible)
    (hpull : ∀ x u v, gM x u v = gN (f x) (mfderiv I I' f x u) (mfderiv I I' f x v))
    (hsM : IsSymm gM) (hndM : IsNondegenerate gM) (hgM : IsMDiffMetric E gM)
    (hsN : IsSymm gN) (hndN : IsNondegenerate gN) (hgN : IsContMDiffMetricSection E' 2 gN)
    {X Y Z : Π y : N, TangentSpace I' y} {x : M}
    (hX : ∀ᶠ z in 𝓝 (f x), CMDiffAt (2 : ℕ∞ω) (T% X) z)
    (hY : ∀ᶠ z in 𝓝 (f x), CMDiffAt (2 : ℕ∞ω) (T% Y) z)
    (hZ : ∀ᶠ z in 𝓝 (f x), CMDiffAt (2 : ℕ∞ω) (T% Z) z) :
    mfderiv I I' f x (curvature (leviCivita gM) (mpullback I I' f X) (mpullback I I' f Y)
      (mpullback I I' f Z) x) = curvature (leviCivita gN) X Y Z (f x) := by
  have hgN1 : IsMDiffMetric E' gN := hgN.isMDiffMetric (by simp)
  have hmd : ∀ {V : Π y : N, TangentSpace I' y}, (∀ᶠ z in 𝓝 (f x), CMDiffAt (2 : ℕ∞ω) (T% V) z) →
      ∀ᶠ y in 𝓝 x, MDiffAt (T% V) (f y) := fun hV =>
    (hf.continuous.continuousAt.eventually (eventually_mdiffAt_of_eventually_contMDiffAt_two hV))
  -- the inner covariant derivatives are pullbacks near `x`
  have eY : ∀ᶠ y in 𝓝 x, leviCivita gM (mpullback I I' f Z) y (mpullback I I' f Y y) =
      mpullback I I' f (fun z => leviCivita gN Z z (Y z)) y :=
    (hmd hZ).mono fun y hy => leviCivita_mpullback_eq hf hfi hpull hsM hndM hgM hsN hndN hgN1 hy
  have eX : ∀ᶠ y in 𝓝 x, leviCivita gM (mpullback I I' f Z) y (mpullback I I' f X y) =
      mpullback I I' f (fun z => leviCivita gN Z z (X z)) y :=
    (hmd hZ).mono fun y hy => leviCivita_mpullback_eq hf hfi hpull hsM hndM hgM hsN hndN hgN1 hy
  have hcov := covC2LocalMDiffAt_leviCivita hsN hndN hgN (f x) Z hZ
  have hWY : MDiffAt (T% (fun z => leviCivita gN Z z (Y z))) (f x) :=
    mdiffAt_cov_apply hcov (hY.self_of_nhds.mdifferentiableAt (by simp))
  have hWX : MDiffAt (T% (fun z => leviCivita gN Z z (X z))) (f x) :=
    mdiffAt_cov_apply hcov (hX.self_of_nhds.mdifferentiableAt (by simp))
  haveI : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le minSmoothness_two_le_infty
  haveI : IsManifold I' (minSmoothness ℝ 2) N := IsManifold.of_le minSmoothness_two_le_infty
  have hb := mpullback_mlieBracket (n := ∞) (hX.self_of_nhds.mdifferentiableAt (by simp))
    (hY.self_of_nhds.mdifferentiableAt (by simp)) (hf x) minSmoothness_two_le_infty
  have hZd : MDiffAt (T% Z) (f x) := hZ.self_of_nhds.mdifferentiableAt (by simp)
  simp only [curvature]
  rw [leviCivita_congr_of_eventuallyEq eY, leviCivita_congr_of_eventuallyEq eX, ← hb, map_sub,
    map_sub, mfderiv_leviCivita_mpullback hf hfi hpull hsM hndM hgM hsN hndN hgN1 hWY,
    mfderiv_leviCivita_mpullback hf hfi hpull hsM hndM hgM hsN hndN hgN1 hWX,
    mfderiv_leviCivita_mpullback hf hfi hpull hsM hndM hgM hsN hndN hgN1 hZd,
    mfderiv_mpullback hfi, mfderiv_mpullback hfi, mfderiv_mpullback hfi]

/-- **The Riemann tensor is natural** under local isometries. -/
theorem riemannTensorAt_pullback (hf : ContMDiff I I' ∞ f)
    (hfi : ∀ x, (mfderiv I I' f x).IsInvertible)
    (hpull : ∀ x u v, gM x u v = gN (f x) (mfderiv I I' f x u) (mfderiv I I' f x v))
    (hsM : IsSymm gM) (hndM : IsNondegenerate gM) (hgM : IsContMDiffMetricSection E 2 gM)
    (hsN : IsSymm gN) (hndN : IsNondegenerate gN) (hgN : IsContMDiffMetricSection E' 2 gN)
    (x : M) (u v w z : TangentSpace I x) :
    riemannTensorAt hsM hndM hgM x u v w z =
      riemannTensorAt hsN hndN hgN (f x) (mfderiv I I' f x u) (mfderiv I I' f x v)
        (mfderiv I I' f x w) (mfderiv I I' f x z) := by
  have hgM1 : IsMDiffMetric E gM := hgM.isMDiffMetric (by simp)
  set X : Π y : N, TangentSpace I' y := FiberBundle.extend E' (mfderiv I I' f x u)
  set Y : Π y : N, TangentSpace I' y := FiberBundle.extend E' (mfderiv I I' f x v)
  set Z : Π y : N, TangentSpace I' y := FiberBundle.extend E' (mfderiv I I' f x w)
  have hX := eventually_contMDiffAt_extendTangent (k := (2 : ℕ∞ω)) (I := I') (M := N)
    (mfderiv I I' f x u)
  have hY := eventually_contMDiffAt_extendTangent (k := (2 : ℕ∞ω)) (I := I') (M := N)
    (mfderiv I I' f x v)
  have hZ := eventually_contMDiffAt_extendTangent (k := (2 : ℕ∞ω)) (I := I') (M := N)
    (mfderiv I I' f x w)
  have hpb : ∀ {V : Π y : N, TangentSpace I' y},
      (∀ᶠ z in 𝓝 (f x), CMDiffAt (2 : ℕ∞ω) (T% V) z) →
      ∀ᶠ y in 𝓝 x, CMDiffAt (2 : ℕ∞ω) (T% (mpullback I I' f V)) y := fun hV =>
    (hf.continuous.continuousAt.eventually hV).mono fun y hy =>
      ContMDiffAt.mpullback_vectorField_preimage (n := ∞) hy (hf y) (hfi y)
        (WithTop.coe_le_coe.mpr le_top)
  have ev : ∀ (a : TangentSpace I x), mpullback I I' f
      (FiberBundle.extend E' (mfderiv I I' f x a) : Π y : N, TangentSpace I' y) x = a := fun a => by
    rw [mpullback_apply, FiberBundle.extend_apply_self]; exact mpullback_mfderiv hfi a
  have hRM := riemannCurvatureAt_apply hsM hndM hgM (x := x) (hpb hX) (hpb hY)
    (hpb hZ).self_of_nhds
  have hRN := riemannCurvatureAt_apply hsN hndN hgN (x := f x) hX hY hZ.self_of_nhds
  rw [ev, ev, ev] at hRM
  simp only [X, Y, Z, FiberBundle.extend_apply_self] at hRN
  rw [riemannTensorAt_apply, riemannTensorAt_apply, hpull, hRM, hRN]
  congr 1
  exact congrArg _ (mfderiv_curvature_mpullback hf hfi hpull hsM hndM hgM1 hsN hndN hgN hX hY hZ)

/-- **Sectional curvature is natural** under local isometries. -/
theorem sectionalCurvatureAt_pullback (hf : ContMDiff I I' ∞ f)
    (hfi : ∀ x, (mfderiv I I' f x).IsInvertible)
    (hpull : ∀ x u v, gM x u v = gN (f x) (mfderiv I I' f x u) (mfderiv I I' f x v))
    (hsM : IsSymm gM) (hpM : IsPosDef gM) (hgM : IsContMDiffMetricSection E 2 gM)
    (hsN : IsSymm gN) (hpN : IsPosDef gN) (hgN : IsContMDiffMetricSection E' 2 gN)
    (x : M) (u v : TangentSpace I x) :
    sectionalCurvatureAt hsM hpM hgM x u v =
      sectionalCurvatureAt hsN hpN hgN (f x) (mfderiv I I' f x u) (mfderiv I I' f x v) := by
  rw [sectionalCurvatureAt_def, sectionalCurvatureAt_def,
    riemannTensorAt_pullback hf hfi hpull hsM hpM.isNondegenerate hgM hsN hpN.isNondegenerate hgN]
  simp only [gramDet, hpull]

end Natural

end

end ExoticSpheres8And10
