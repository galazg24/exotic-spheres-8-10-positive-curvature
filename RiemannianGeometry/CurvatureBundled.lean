/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import RiemannianGeometry.CurvaturePointwise

/-!
# The curvature endomorphism of a fibre

## Main results

* `curvatureEnd` — the endomorphism `V x →L[𝕜] V x`.
* `curvatureEnd_apply` — evaluation: `curvatureEnd … (σ x) = R(X, Y)σ x` for any `C^n` section.
* `curvatureEnd_unique` — it is the **only** continuous linear map with that property, so it does
  not depend on the canonical extension, the trivialization or the frame used to build it.

## Construction, and why the auxiliary choice is harmless

`v ↦ R(X, Y)(extend F v) x`, where `extend` is Mathlib's canonical extension of a fibre vector to a
section. Linearity is *not* proved from properties of `extend`:

* additivity — `extend F (v + w)` and `extend F v + extend F w` agree at `x` (each has value
  `v + w` there), so `curvature_eq_of_eq_at` identifies their curvatures, and
  `curvature_add_section_of_eventually` splits the sum;
* homogeneity — likewise with `(fun _ ↦ c) • extend F v`, using
  `curvature_smul_section_of_eventually` at the **constant** function `c`.

So the only property of `extend` used is `extend F v x = v`, plus its regularity near `x`. Any other
extension operator would give the same map, and `curvature_end_unique` proves that outright rather
than by inspection: it appeals to `VectorBundle.injective_eval_contMDiffAt_sec`, which says a
continuous linear map on `V x` is determined by its values on `{σ x | σ a C^n section}`.

Continuity comes from `LinearMap.toContinuousLinearMap`, which needs `V x` finite-dimensional —
supplied by `VectorBundle.finiteDimensional` from `[FiniteDimensional 𝕜 F]`, exactly as Mathlib's
own `TensorialAt.mkHom` does.

Also bundled: `curvatureAt : T_xM →L[𝕜] T_xM →L[𝕜] End(V x)`, the intrinsic pointwise curvature
operator, with

* `curvatureAt_apply` — the canonical evaluation `R_x (X x) (Y x) (σ x) = R(X, Y)σ x`;
* `curvatureAt_swap`, `curvatureAt_self` — antisymmetry and vanishing on the diagonal, so the object
  is alternating in the tangent variables;
* additivity and homogeneity in every slot, free from the `ContinuousLinearMap` structure
  (`map_add`, `map_smul`) — not restated here.

The ordering is the standard one: `curvatureAt … u w : End(V x)` corresponds to `R(X, Y)` acting on
the fibre, so `curvatureAt … (X x) (Y x) (σ x)` is `R(X, Y)σ` at `x`.

-/

noncomputable section

open Bundle FiberBundle Set VectorField Filter Module
open scoped Manifold ContDiff Topology

namespace RiemannianGeometry

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V] [ContMDiffVectorBundle (1 : ℕ∞ω) F V I]
  {n : ℕ∞} [IsManifold I 1 M] [IsManifold I (n + 1) M]
  {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
  {X X' Y Y' : Π x : M, TangentSpace I x} {σ : Π x : M, V x} {x : M}

section Extend

variable [ContMDiffVectorBundle (n : ℕ∞ω) F V I]

omit [IsManifold I 1 M] [ContMDiffVectorBundle (n : ℕ∞ω) F V I]
  [ContMDiffVectorBundle 1 F V I] in
/-- `extend F v` is `C^k` **near** `x`, not merely at `x`.
-/
theorem eventually_contMDiffAt_extend {k : ℕ∞ω} [ContMDiffVectorBundle k F V I] (v : V x) :
    ∀ᶠ y in 𝓝 x, CMDiffAt k (T% (extend F v)) y := by
  obtain ⟨s, hs, hsm⟩ := FiberBundle.exists_contMDiffOn_extend (k := k) (I := I) F v
  obtain ⟨u, hu_sub, hu_open, hxu⟩ := mem_nhds_iff.1 hs
  filter_upwards [hu_open.mem_nhds hxu] with y hy
  exact (hsm.mono hu_sub) y hy |>.contMDiffAt (hu_open.mem_nhds hy)

/-- The canonical extension of a **tangent** vector is `C^k` on a whole neighbourhood of `x`.

The type ascription on the instance binder is load-bearing: `ContMDiffVectorBundle`'s bundle
argument has `M` implicit, and `I` pins down `𝕜`, `E`, `H` but never `M`, so a bare
`TangentSpace I` leaves the base manifold — and hence `ChartedSpace H ?M` — undetermined. -/
theorem eventually_contMDiffAt_extendTangent {k : ℕ∞ω}
    [ContMDiffVectorBundle k E (TangentSpace I : M → Type _) I] (u : TangentSpace I x) :
    ∀ᶠ y in 𝓝 x, CMDiffAt k (T% (extend E u : Π y : M, TangentSpace I y)) y := by
  obtain ⟨s, hs, hsm⟩ := FiberBundle.exists_contMDiffOn_extend (k := k) (I := I)
    (V := fun y : M ↦ TangentSpace I y) E u
  obtain ⟨t, ht_sub, ht_open, hxt⟩ := mem_nhds_iff.1 hs
  filter_upwards [ht_open.mem_nhds hxt] with y hy
  exact (hsm.mono ht_sub) y hy |>.contMDiffAt (ht_open.mem_nhds hy)

end Extend

section Bundle

variable [CompleteSpace 𝕜] [CompleteSpace E] [FiniteDimensional 𝕜 F]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [ContMDiffVectorBundle (n : ℕ∞ω) F V I]

/-- **The curvature endomorphism at a point.** For fixed `x`, `X`, `Y`, the map
`v ↦ R(X, Y)σ x` for any section `σ` with `σ x = v`, realised through the canonical extension. -/
def curvatureEnd (hcov : IsCovariantDerivativeOn F cov Set.univ)
    (hcovloc : CovC2LocalMDiffAt F cov x) (hn : minSmoothness 𝕜 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hX : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% X) y)
    (hY : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% Y) y) :
    V x →L[𝕜] V x :=
  have hne : (n : ℕ∞ω) ≠ 0 := by
    have h2n : (2 : ℕ∞ω) ≤ (n : ℕ∞ω) := le_minSmoothness.trans hn
    intro h; rw [h] at h2n; simp at h2n
  have hXd : MDiffAt (T% X) x := hX.self_of_nhds.mdifferentiableAt hne
  have hYd : MDiffAt (T% Y) x := hY.self_of_nhds.mdifferentiableAt hne
  have h2n : (2 : ℕ∞ω) ≤ (n : ℕ∞ω) := le_minSmoothness.trans hn
  have : ContMDiffVectorBundle (2 : ℕ∞ω) F V I := ContMDiffVectorBundle.of_le h2n
  have : FiniteDimensional 𝕜 (V x) := VectorBundle.finiteDimensional 𝕜 F V x
  have : T2Space (V x) := FiberBundle.t2Space F V x
  LinearMap.toContinuousLinearMap
    { toFun := fun v ↦ curvature cov X Y (extend F v) x
      map_add' := fun v w ↦ by
        have hv := eventually_contMDiffAt_extend (k := (2 : ℕ∞ω)) (I := I) (F := F) v
        have hw := eventually_contMDiffAt_extend (k := (2 : ℕ∞ω)) (I := I) (F := F) w
        have hsum : ∀ᶠ y in 𝓝 x, CMDiffAt (2 : ℕ∞ω) (T% (extend F v + extend F w)) y := by
          filter_upwards [hv, hw] with y h1 h2
          exact ContMDiffAt.add_section h1 h2
        have heq : curvature cov X Y (extend F (v + w)) x
            = curvature cov X Y (extend F v + extend F w) x := by
          refine curvature_eq_of_eq_at hcov hcovloc hn hn' (FiberBundle.contMDiffAt_extend I F _)
            (ContMDiffAt.add_section (FiberBundle.contMDiffAt_extend I F v)
              (FiberBundle.contMDiffAt_extend I F w)) hX hY ?_
          simp
        rw [heq, curvature_add_section_of_eventually hcov (hcovloc _ hv) (hcovloc _ hw)
          (eventually_mdiffAt_of_eventually_contMDiffAt_two hv)
          (eventually_mdiffAt_of_eventually_contMDiffAt_two hw) hXd hYd]
      map_smul' := fun c v ↦ by
        have hv := eventually_contMDiffAt_extend (k := (2 : ℕ∞ω)) (I := I) (F := F) v
        have heq : curvature cov X Y (extend F (c • v)) x
            = curvature cov X Y (((fun _ ↦ c : M → 𝕜)) • extend F v) x := by
          refine curvature_eq_of_eq_at hcov hcovloc hn hn' (FiberBundle.contMDiffAt_extend I F _)
            (ContMDiffAt.smul_section contMDiffAt_const
              (FiberBundle.contMDiffAt_extend I F v)) hX hY ?_
          simp
        rw [heq, curvature_smul_section_of_eventually hcov (hcovloc _ hv) hn hn'
          contMDiffAt_const (eventually_mdiffAt_of_eventually_contMDiffAt_two hv) hX hY]
        rfl }

/-- **Evaluation.** The endomorphism, applied to `σ x`, returns the field-level curvature. -/
theorem curvatureEnd_apply (hcov : IsCovariantDerivativeOn F cov Set.univ)
    (hcovloc : CovC2LocalMDiffAt F cov x) (hn : minSmoothness 𝕜 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hX : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% X) y)
    (hY : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% Y) y)
    (hσ : CMDiffAt (n : ℕ∞ω) (T% σ) x) :
    curvatureEnd hcov hcovloc hn hn' hX hY (σ x) = curvature cov X Y σ x :=
  curvature_eq_of_eq_at hcov hcovloc hn hn' (FiberBundle.contMDiffAt_extend I F _) hσ hX hY
    (by simp)

/-- **Independence of the construction.** The endomorphism is the *unique* continuous linear map
whose evaluation reproduces the field-level curvature, so it does not depend on the canonical
extension, the trivialization, or the frame used to build it. -/
theorem curvatureEnd_unique (hcov : IsCovariantDerivativeOn F cov Set.univ)
    (hcovloc : CovC2LocalMDiffAt F cov x) (hn : minSmoothness 𝕜 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hX : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% X) y)
    (hY : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% Y) y)
    (A : V x →L[𝕜] V x)
    (hA : ∀ s : Π y : M, V y, CMDiffAt (n : ℕ∞ω) (T% s) x → A (s x) = curvature cov X Y s x) :
    A = curvatureEnd hcov hcovloc hn hn' hX hY := by
  refine VectorBundle.injective_eval_contMDiffAt_sec (n := (n : ℕ∞ω)) I F V (V x) x ?_
  funext s hs
  change A (s x) = curvatureEnd hcov hcovloc hn hn' hX hY (s x)
  rw [hA s hs, curvatureEnd_apply hcov hcovloc hn hn' hX hY hs]

end Bundle
section Congr

variable [CompleteSpace 𝕜] [CompleteSpace E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 E]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [ContMDiffVectorBundle (n : ℕ∞ω) F V I]

/-- **The endomorphism depends on the first vector field only through its value at `x`.**
-/
theorem curvatureEnd_congr_left
    (hcov : IsCovariantDerivativeOn F cov Set.univ) (hcovloc : CovC2LocalMDiffAt F cov x)
    (hn : minSmoothness 𝕜 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hX : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% X) y)
    (hX' : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% X') y)
    (hY : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% Y) y)
    (h : X x = X' x) :
    curvatureEnd hcov hcovloc hn hn' hX hY = curvatureEnd hcov hcovloc hn hn' hX' hY := by
  have h2n : (2 : ℕ∞ω) ≤ (n : ℕ∞ω) := le_minSmoothness.trans hn
  have hne : (n : ℕ∞ω) ≠ 0 := by intro h0; rw [h0] at h2n; simp at h2n
  have hMn : IsManifold I (n : ℕ∞ω) M := IsManifold.of_le (n := (n : ℕ∞ω) + 1) le_self_add
  have hM2 : IsManifold I 2 M := IsManifold.of_le (n := (n : ℕ∞ω)) h2n
  have hXd : MDiffAt (T% X) x := hX.self_of_nhds.mdifferentiableAt hne
  have hX'd : MDiffAt (T% X') x := hX'.self_of_nhds.mdifferentiableAt hne
  refine VectorBundle.injective_eval_contMDiffAt_sec (n := (n : ℕ∞ω)) I F V (V x) x ?_
  funext s hs
  change curvatureEnd hcov hcovloc hn hn' hX hY (s x)
      = curvatureEnd hcov hcovloc hn hn' hX' hY (s x)
  rw [curvatureEnd_apply hcov hcovloc hn hn' hX hY hs,
    curvatureEnd_apply hcov hcovloc hn hn' hX' hY hs]
  have hsd2 : ∀ᶠ y in 𝓝 x, CMDiffAt (2 : ℕ∞ω) (T% s) y :=
    ((contMDiffAt_iff_contMDiffAt_nhds hn').1 hs).mono fun _ hh ↦ hh.of_le h2n
  have hsd : ∀ᶠ y in 𝓝 x, MDiffAt (T% s) y :=
    eventually_mdiffAt_of_eventually_contMDiffAt_two hsd2
  have hcovσ : MDiffAtCovSection F cov s x := hcovloc s hsd2
  have ht : TensorialAt I E (fun Z : Π y : M, TangentSpace I y ↦ curvature cov Z Y s x) x :=
    { smul := fun hf hZ ↦ curvature_smul_left hcov hcovσ hf hZ
      add := fun hZ hZ' ↦ curvature_add_left hcov hcovσ hZ hZ' }
  exact ht.pointwise hXd hX'd h

/-! ### Slotwise linearity of the endomorphism
-/

omit [FiniteDimensional 𝕜 E] in
theorem curvatureEnd_add_left
    (hcov : IsCovariantDerivativeOn F cov Set.univ) (hcovloc : CovC2LocalMDiffAt F cov x)
    (hn : minSmoothness 𝕜 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hX : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% X) y)
    (hX' : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% X') y)
    (hY : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% Y) y)
    (hXX' : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% (X + X')) y) :
    curvatureEnd hcov hcovloc hn hn' hXX' hY
      = curvatureEnd hcov hcovloc hn hn' hX hY + curvatureEnd hcov hcovloc hn hn' hX' hY := by
  have h2n : (2 : ℕ∞ω) ≤ (n : ℕ∞ω) := le_minSmoothness.trans hn
  have hne : (n : ℕ∞ω) ≠ 0 := by intro h0; rw [h0] at h2n; simp at h2n
  have hMn : IsManifold I (n : ℕ∞ω) M := IsManifold.of_le (n := (n : ℕ∞ω) + 1) le_self_add
  have hM2 : IsManifold I 2 M := IsManifold.of_le (n := (n : ℕ∞ω)) h2n
  have hXd : MDiffAt (T% X) x := hX.self_of_nhds.mdifferentiableAt hne
  have hX'd : MDiffAt (T% X') x := hX'.self_of_nhds.mdifferentiableAt hne
  refine VectorBundle.injective_eval_contMDiffAt_sec (n := (n : ℕ∞ω)) I F V (V x) x ?_
  funext s hs
  change curvatureEnd hcov hcovloc hn hn' hXX' hY (s x)
      = (curvatureEnd hcov hcovloc hn hn' hX hY + curvatureEnd hcov hcovloc hn hn' hX' hY) (s x)
  rw [add_apply,
    curvatureEnd_apply hcov hcovloc hn hn' hXX' hY hs,
    curvatureEnd_apply hcov hcovloc hn hn' hX hY hs,
    curvatureEnd_apply hcov hcovloc hn hn' hX' hY hs]
  have hsd2 : ∀ᶠ y in 𝓝 x, CMDiffAt (2 : ℕ∞ω) (T% s) y :=
    ((contMDiffAt_iff_contMDiffAt_nhds hn').1 hs).mono fun _ hh ↦ hh.of_le h2n
  have hsd : ∀ᶠ y in 𝓝 x, MDiffAt (T% s) y :=
    eventually_mdiffAt_of_eventually_contMDiffAt_two hsd2
  have hcovσ : MDiffAtCovSection F cov s x := hcovloc s hsd2
  exact curvature_add_left hcov hcovσ hXd hX'd

omit [FiniteDimensional 𝕜 E] in
theorem curvatureEnd_smul_left
    (hcov : IsCovariantDerivativeOn F cov Set.univ) (hcovloc : CovC2LocalMDiffAt F cov x)
    (hn : minSmoothness 𝕜 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hX : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% X) y)
    (hY : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% Y) y)
    {c : 𝕜}
    (hcX : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% (((fun _ ↦ c) : M → 𝕜) • X)) y) :
    curvatureEnd hcov hcovloc hn hn' hcX hY = c • curvatureEnd hcov hcovloc hn hn' hX hY := by
  have h2n : (2 : ℕ∞ω) ≤ (n : ℕ∞ω) := le_minSmoothness.trans hn
  have hne : (n : ℕ∞ω) ≠ 0 := by intro h0; rw [h0] at h2n; simp at h2n
  have hMn : IsManifold I (n : ℕ∞ω) M := IsManifold.of_le (n := (n : ℕ∞ω) + 1) le_self_add
  have hM2 : IsManifold I 2 M := IsManifold.of_le (n := (n : ℕ∞ω)) h2n
  have hXd : MDiffAt (T% X) x := hX.self_of_nhds.mdifferentiableAt hne
  refine VectorBundle.injective_eval_contMDiffAt_sec (n := (n : ℕ∞ω)) I F V (V x) x ?_
  funext s hs
  change curvatureEnd hcov hcovloc hn hn' hcX hY (s x)
      = (c • curvatureEnd hcov hcovloc hn hn' hX hY) (s x)
  rw [smul_apply,
    curvatureEnd_apply hcov hcovloc hn hn' hcX hY hs,
    curvatureEnd_apply hcov hcovloc hn hn' hX hY hs]
  have hsd2 : ∀ᶠ y in 𝓝 x, CMDiffAt (2 : ℕ∞ω) (T% s) y :=
    ((contMDiffAt_iff_contMDiffAt_nhds hn').1 hs).mono fun _ hh ↦ hh.of_le h2n
  have hsd : ∀ᶠ y in 𝓝 x, MDiffAt (T% s) y :=
    eventually_mdiffAt_of_eventually_contMDiffAt_two hsd2
  have hcovσ : MDiffAtCovSection F cov s x := hcovloc s hsd2
  exact curvature_smul_left hcov hcovσ (f := fun _ ↦ c) mdifferentiableAt_const hXd

omit [FiniteDimensional 𝕜 E] in
theorem curvatureEnd_add_right
    (hcov : IsCovariantDerivativeOn F cov Set.univ) (hcovloc : CovC2LocalMDiffAt F cov x)
    (hn : minSmoothness 𝕜 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hX : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% X) y)
    (hY : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% Y) y)
    (hY' : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% Y') y)
    (hYY' : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% (Y + Y')) y) :
    curvatureEnd hcov hcovloc hn hn' hX hYY'
      = curvatureEnd hcov hcovloc hn hn' hX hY + curvatureEnd hcov hcovloc hn hn' hX hY' := by
  have h2n : (2 : ℕ∞ω) ≤ (n : ℕ∞ω) := le_minSmoothness.trans hn
  have hne : (n : ℕ∞ω) ≠ 0 := by intro h0; rw [h0] at h2n; simp at h2n
  have hMn : IsManifold I (n : ℕ∞ω) M := IsManifold.of_le (n := (n : ℕ∞ω) + 1) le_self_add
  have hM2 : IsManifold I 2 M := IsManifold.of_le (n := (n : ℕ∞ω)) h2n
  have hYd : MDiffAt (T% Y) x := hY.self_of_nhds.mdifferentiableAt hne
  have hY'd : MDiffAt (T% Y') x := hY'.self_of_nhds.mdifferentiableAt hne
  refine VectorBundle.injective_eval_contMDiffAt_sec (n := (n : ℕ∞ω)) I F V (V x) x ?_
  funext s hs
  change curvatureEnd hcov hcovloc hn hn' hX hYY' (s x)
      = (curvatureEnd hcov hcovloc hn hn' hX hY + curvatureEnd hcov hcovloc hn hn' hX hY') (s x)
  rw [add_apply,
    curvatureEnd_apply hcov hcovloc hn hn' hX hYY' hs,
    curvatureEnd_apply hcov hcovloc hn hn' hX hY hs,
    curvatureEnd_apply hcov hcovloc hn hn' hX hY' hs]
  have hsd2 : ∀ᶠ y in 𝓝 x, CMDiffAt (2 : ℕ∞ω) (T% s) y :=
    ((contMDiffAt_iff_contMDiffAt_nhds hn').1 hs).mono fun _ hh ↦ hh.of_le h2n
  have hsd : ∀ᶠ y in 𝓝 x, MDiffAt (T% s) y :=
    eventually_mdiffAt_of_eventually_contMDiffAt_two hsd2
  have hcovσ : MDiffAtCovSection F cov s x := hcovloc s hsd2
  exact curvature_add_right hcov hcovσ hYd hY'd

omit [FiniteDimensional 𝕜 E] in
theorem curvatureEnd_smul_right
    (hcov : IsCovariantDerivativeOn F cov Set.univ) (hcovloc : CovC2LocalMDiffAt F cov x)
    (hn : minSmoothness 𝕜 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hX : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% X) y)
    (hY : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% Y) y)
    {c : 𝕜}
    (hcY : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% (((fun _ ↦ c) : M → 𝕜) • Y)) y) :
    curvatureEnd hcov hcovloc hn hn' hX hcY = c • curvatureEnd hcov hcovloc hn hn' hX hY := by
  have h2n : (2 : ℕ∞ω) ≤ (n : ℕ∞ω) := le_minSmoothness.trans hn
  have hne : (n : ℕ∞ω) ≠ 0 := by intro h0; rw [h0] at h2n; simp at h2n
  have hMn : IsManifold I (n : ℕ∞ω) M := IsManifold.of_le (n := (n : ℕ∞ω) + 1) le_self_add
  have hM2 : IsManifold I 2 M := IsManifold.of_le (n := (n : ℕ∞ω)) h2n
  have hYd : MDiffAt (T% Y) x := hY.self_of_nhds.mdifferentiableAt hne
  refine VectorBundle.injective_eval_contMDiffAt_sec (n := (n : ℕ∞ω)) I F V (V x) x ?_
  funext s hs
  change curvatureEnd hcov hcovloc hn hn' hX hcY (s x)
      = (c • curvatureEnd hcov hcovloc hn hn' hX hY) (s x)
  rw [smul_apply,
    curvatureEnd_apply hcov hcovloc hn hn' hX hcY hs,
    curvatureEnd_apply hcov hcovloc hn hn' hX hY hs]
  have hsd2 : ∀ᶠ y in 𝓝 x, CMDiffAt (2 : ℕ∞ω) (T% s) y :=
    ((contMDiffAt_iff_contMDiffAt_nhds hn').1 hs).mono fun _ hh ↦ hh.of_le h2n
  have hsd : ∀ᶠ y in 𝓝 x, MDiffAt (T% s) y :=
    eventually_mdiffAt_of_eventually_contMDiffAt_two hsd2
  have hcovσ : MDiffAtCovSection F cov s x := hcovloc s hsd2
  exact curvature_smul_right hcov hcovσ (f := fun _ ↦ c) mdifferentiableAt_const hYd

/-! ### Antisymmetry, and dependence on the second slot

`curvatureEnd_swap` and `curvatureEnd_self` come straight from the **unconditional** field-level
`curvature_swap_apply` and `curvature_self_apply`, so they need no regularity beyond what
`curvatureEnd` already assumes. `curvatureEnd_congr_right` mirrors `curvatureEnd_congr_left` through
the `Y`-slot `TensorialAt` structure. -/

omit [FiniteDimensional 𝕜 E] in
/-- **Antisymmetry of the curvature endomorphism in the two vector fields.** -/
theorem curvatureEnd_swap
    (hcov : IsCovariantDerivativeOn F cov Set.univ) (hcovloc : CovC2LocalMDiffAt F cov x)
    (hn : minSmoothness 𝕜 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hX : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% X) y)
    (hY : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% Y) y) :
    curvatureEnd hcov hcovloc hn hn' hX hY = - curvatureEnd hcov hcovloc hn hn' hY hX := by
  refine VectorBundle.injective_eval_contMDiffAt_sec (n := (n : ℕ∞ω)) I F V (V x) x ?_
  funext s hs
  change curvatureEnd hcov hcovloc hn hn' hX hY (s x)
      = (- curvatureEnd hcov hcovloc hn hn' hY hX) (s x)
  rw [neg_apply, curvatureEnd_apply hcov hcovloc hn hn' hX hY hs,
    curvatureEnd_apply hcov hcovloc hn hn' hY hX hs]
  exact curvature_swap_apply

omit [FiniteDimensional 𝕜 E] in
/-- **The curvature endomorphism vanishes on the diagonal.** -/
theorem curvatureEnd_self
    (hcov : IsCovariantDerivativeOn F cov Set.univ) (hcovloc : CovC2LocalMDiffAt F cov x)
    (hn : minSmoothness 𝕜 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hX : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% X) y) :
    curvatureEnd hcov hcovloc hn hn' hX hX = 0 := by
  refine VectorBundle.injective_eval_contMDiffAt_sec (n := (n : ℕ∞ω)) I F V (V x) x ?_
  funext s hs
  change curvatureEnd hcov hcovloc hn hn' hX hX (s x) = (0 : V x →L[𝕜] V x) (s x)
  rw [zero_apply, curvatureEnd_apply hcov hcovloc hn hn' hX hX hs]
  exact curvature_self_apply

/-- **The endomorphism depends on the second vector field only through its value at `x`.** -/
theorem curvatureEnd_congr_right
    (hcov : IsCovariantDerivativeOn F cov Set.univ) (hcovloc : CovC2LocalMDiffAt F cov x)
    (hn : minSmoothness 𝕜 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hY : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% Y) y)
    (hY' : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% Y') y)
    (hX : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% X) y)
    (h : Y x = Y' x) :
    curvatureEnd hcov hcovloc hn hn' hX hY = curvatureEnd hcov hcovloc hn hn' hX hY' := by
  have h2n : (2 : ℕ∞ω) ≤ (n : ℕ∞ω) := le_minSmoothness.trans hn
  have hne : (n : ℕ∞ω) ≠ 0 := by intro h0; rw [h0] at h2n; simp at h2n
  have hMn : IsManifold I (n : ℕ∞ω) M := IsManifold.of_le (n := (n : ℕ∞ω) + 1) le_self_add
  have hM2 : IsManifold I 2 M := IsManifold.of_le (n := (n : ℕ∞ω)) h2n
  have hYd : MDiffAt (T% Y) x := hY.self_of_nhds.mdifferentiableAt hne
  have hY'd : MDiffAt (T% Y') x := hY'.self_of_nhds.mdifferentiableAt hne
  refine VectorBundle.injective_eval_contMDiffAt_sec (n := (n : ℕ∞ω)) I F V (V x) x ?_
  funext s hs
  change curvatureEnd hcov hcovloc hn hn' hX hY (s x)
      = curvatureEnd hcov hcovloc hn hn' hX hY' (s x)
  rw [curvatureEnd_apply hcov hcovloc hn hn' hX hY hs,
    curvatureEnd_apply hcov hcovloc hn hn' hX hY' hs]
  have hsd2 : ∀ᶠ y in 𝓝 x, CMDiffAt (2 : ℕ∞ω) (T% s) y :=
    ((contMDiffAt_iff_contMDiffAt_nhds hn').1 hs).mono fun _ hh ↦ hh.of_le h2n
  have hsd : ∀ᶠ y in 𝓝 x, MDiffAt (T% s) y :=
    eventually_mdiffAt_of_eventually_contMDiffAt_two hsd2
  have hcovσ : MDiffAtCovSection F cov s x := hcovloc s hsd2
  have ht : TensorialAt I E (fun Z : Π y : M, TangentSpace I y ↦ curvature cov X Z s x) x :=
    { smul := fun hf hZ ↦ curvature_smul_right hcov hcovσ hf hZ
      add := fun hZ hZ' ↦ curvature_add_right hcov hcovσ hZ hZ' }
  exact ht.pointwise hYd hY'd h


end Congr

section Bundle₂

variable [CompleteSpace 𝕜] [CompleteSpace E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 E]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [ContMDiffVectorBundle (n : ℕ∞ω) F V I]
  [ContMDiffVectorBundle (n : ℕ∞ω) E (TangentSpace I : M → Type _) I]

/-! ### The bundled pointwise curvature operator

`curvatureAt` is `R_x : T_xM →L[𝕜] T_xM →L[𝕜] End(V x)`, built as two nested
`LinearMap.toContinuousLinearMap` over `u ↦ w ↦ curvatureEnd … (extend u) (extend w)`.

Linearity in each tangent slot uses no property of `extend` beyond `extend E u x = u`: the fields
`extend E (u + u')` and `extend E u + extend E u'` agree **at `x`**, so `curvatureEnd_congr_left`
identifies the two endomorphisms and `curvatureEnd_add_left` splits them; likewise for `smul` with
a constant scalar, and in the second slot. So the extension used to build the object is provably
irrelevant to it — and `curvatureAt_apply` below pins the object down without mentioning any
extension at all.

Two instances have to be transported by hand: `LinearMap.toContinuousLinearMap` needs `T2Space` and
`FiniteDimensional` on its **domain**, and neither crosses the `TangentSpace I x` type synonym
automatically even with `[FiniteDimensional 𝕜 E]` in scope. `inferInstanceAs` supplies both. -/

/-- Inner layer: for a fixed `u`, the map `w ↦ curvatureEnd … (extend u) (extend w)`. -/
def curvatureAtAux (hcov : IsCovariantDerivativeOn F cov Set.univ)
    (hcovloc : CovC2LocalMDiffAt F cov x) (hn : minSmoothness 𝕜 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (u : TangentSpace I x) :
    TangentSpace I x →L[𝕜] (V x →L[𝕜] V x) :=
  have : FiniteDimensional 𝕜 (V x) := VectorBundle.finiteDimensional 𝕜 F V x
  have : T2Space (V x) := FiberBundle.t2Space F V x
  have : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  have : FiniteDimensional 𝕜 (TangentSpace I x) := inferInstanceAs (FiniteDimensional 𝕜 E)
  LinearMap.toContinuousLinearMap
    { toFun := fun w ↦ curvatureEnd hcov hcovloc hn hn'
        (eventually_contMDiffAt_extendTangent (I := I) (k := (n : ℕ∞ω)) u)
        (eventually_contMDiffAt_extendTangent (I := I) (k := (n : ℕ∞ω)) w)
      map_add' := fun w w' ↦ by
        have hu := eventually_contMDiffAt_extendTangent (I := I) (k := (n : ℕ∞ω)) u
        have hw := eventually_contMDiffAt_extendTangent (I := I) (k := (n : ℕ∞ω)) w
        have hw' := eventually_contMDiffAt_extendTangent (I := I) (k := (n : ℕ∞ω)) w'
        have hsum : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω)
            (T% ((extend E w : Π y : M, TangentSpace I y) + extend E w')) y := by
          filter_upwards [hw, hw'] with y h1 h2 using h1.add_section h2
        rw [curvatureEnd_congr_right hcov hcovloc hn hn'
          (eventually_contMDiffAt_extendTangent (I := I) (k := (n : ℕ∞ω)) (w + w')) hsum hu
          (by simp), curvatureEnd_add_right hcov hcovloc hn hn' hu hw hw' hsum]
      map_smul' := fun c w ↦ by
        have hu := eventually_contMDiffAt_extendTangent (I := I) (k := (n : ℕ∞ω)) u
        have hw := eventually_contMDiffAt_extendTangent (I := I) (k := (n : ℕ∞ω)) w
        have hsmul : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω)
            (T% (((fun _ ↦ c) : M → 𝕜) • (extend E w : Π y : M, TangentSpace I y))) y := by
          filter_upwards [hw] with y h1 using contMDiffAt_const.smul_section h1
        rw [curvatureEnd_congr_right hcov hcovloc hn hn'
          (eventually_contMDiffAt_extendTangent (I := I) (k := (n : ℕ∞ω)) (c • w)) hsmul hu
          (by simp), curvatureEnd_smul_right hcov hcovloc hn hn' hu hw hsmul]
        rfl }

/-- Evaluation of the inner layer. -/
theorem curvatureAtAux_apply (hcov : IsCovariantDerivativeOn F cov Set.univ)
    (hcovloc : CovC2LocalMDiffAt F cov x) (hn : minSmoothness 𝕜 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (u w : TangentSpace I x) :
    curvatureAtAux hcov hcovloc hn hn' u w
      = curvatureEnd hcov hcovloc hn hn'
          (eventually_contMDiffAt_extendTangent (I := I) (k := (n : ℕ∞ω)) u)
          (eventually_contMDiffAt_extendTangent (I := I) (k := (n : ℕ∞ω)) w) :=
  rfl

/-- **The bundled pointwise curvature operator.** `R_x : T_xM →L T_xM →L End(V x)`. -/
def curvatureAt (hcov : IsCovariantDerivativeOn F cov Set.univ)
    (hcovloc : CovC2LocalMDiffAt F cov x) (hn : minSmoothness 𝕜 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞) :
    TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] (V x →L[𝕜] V x) :=
  have : FiniteDimensional 𝕜 (V x) := VectorBundle.finiteDimensional 𝕜 F V x
  have : T2Space (V x) := FiberBundle.t2Space F V x
  have : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  have : FiniteDimensional 𝕜 (TangentSpace I x) := inferInstanceAs (FiniteDimensional 𝕜 E)
  LinearMap.toContinuousLinearMap
    { toFun := fun u ↦ curvatureAtAux hcov hcovloc hn hn' u
      map_add' := fun u u' ↦ by
        have hu := eventually_contMDiffAt_extendTangent (I := I) (k := (n : ℕ∞ω)) u
        have hu' := eventually_contMDiffAt_extendTangent (I := I) (k := (n : ℕ∞ω)) u'
        have hsum : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω)
            (T% ((extend E u : Π y : M, TangentSpace I y) + extend E u')) y := by
          filter_upwards [hu, hu'] with y h1 h2 using h1.add_section h2
        refine ContinuousLinearMap.ext fun w ↦ ?_
        rw [add_apply, curvatureAtAux_apply, curvatureAtAux_apply, curvatureAtAux_apply,
          curvatureEnd_congr_left hcov hcovloc hn hn'
            (eventually_contMDiffAt_extendTangent (I := I) (k := (n : ℕ∞ω)) (u + u')) hsum
            (eventually_contMDiffAt_extendTangent (I := I) (k := (n : ℕ∞ω)) w) (by simp),
          curvatureEnd_add_left hcov hcovloc hn hn' hu hu'
            (eventually_contMDiffAt_extendTangent (I := I) (k := (n : ℕ∞ω)) w) hsum]
      map_smul' := fun c u ↦ by
        have hu := eventually_contMDiffAt_extendTangent (I := I) (k := (n : ℕ∞ω)) u
        have hsmul : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω)
            (T% (((fun _ ↦ c) : M → 𝕜) • (extend E u : Π y : M, TangentSpace I y))) y := by
          filter_upwards [hu] with y h1 using contMDiffAt_const.smul_section h1
        refine ContinuousLinearMap.ext fun w ↦ ?_
        rw [smul_apply, curvatureAtAux_apply, curvatureAtAux_apply,
          curvatureEnd_congr_left hcov hcovloc hn hn'
            (eventually_contMDiffAt_extendTangent (I := I) (k := (n : ℕ∞ω)) (c • u)) hsmul
            (eventually_contMDiffAt_extendTangent (I := I) (k := (n : ℕ∞ω)) w) (by simp),
          curvatureEnd_smul_left hcov hcovloc hn hn' hu
            (eventually_contMDiffAt_extendTangent (I := I) (k := (n : ℕ∞ω)) w) hsmul]
        rfl }

/-- **Evaluation of the bundled operator on canonical extensions.** -/
theorem curvatureAt_apply_extend (hcov : IsCovariantDerivativeOn F cov Set.univ)
    (hcovloc : CovC2LocalMDiffAt F cov x) (hn : minSmoothness 𝕜 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (u w : TangentSpace I x) :
    curvatureAt hcov hcovloc hn hn' u w
      = curvatureEnd hcov hcovloc hn hn'
          (eventually_contMDiffAt_extendTangent (I := I) (k := (n : ℕ∞ω)) u)
          (eventually_contMDiffAt_extendTangent (I := I) (k := (n : ℕ∞ω)) w) :=
  rfl

/-- **Antisymmetry of the bundled pointwise curvature operator.** -/
theorem curvatureAt_swap (hcov : IsCovariantDerivativeOn F cov Set.univ)
    (hcovloc : CovC2LocalMDiffAt F cov x) (hn : minSmoothness 𝕜 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (u w : TangentSpace I x) :
    curvatureAt hcov hcovloc hn hn' u w = - curvatureAt hcov hcovloc hn hn' w u := by
  rw [curvatureAt_apply_extend, curvatureAt_apply_extend,
    curvatureEnd_swap hcov hcovloc hn hn'
      (eventually_contMDiffAt_extendTangent (I := I) (k := (n : ℕ∞ω)) u)
      (eventually_contMDiffAt_extendTangent (I := I) (k := (n : ℕ∞ω)) w)]

/-- **The bundled pointwise curvature operator vanishes on the diagonal.** -/
theorem curvatureAt_self (hcov : IsCovariantDerivativeOn F cov Set.univ)
    (hcovloc : CovC2LocalMDiffAt F cov x) (hn : minSmoothness 𝕜 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (u : TangentSpace I x) :
    curvatureAt hcov hcovloc hn hn' u u = 0 := by
  rw [curvatureAt_apply_extend,
    curvatureEnd_self hcov hcovloc hn hn'
      (eventually_contMDiffAt_extendTangent (I := I) (k := (n : ℕ∞ω)) u)]

/-- **The canonical evaluation theorem: the bundled object *is* the field-level curvature.**

`R_x (X x) (Y x) (σ x) = R(X, Y)σ x` for any vector fields regular near `x` and any section `C^n`
at `x`. No extension, trivialization or frame appears in the statement, so this is the certification
that `curvatureAt` represents the operator `curvature` and not some artefact of the construction.

Proof: unfold to the extension form, then replace each extension by the field it agrees with at `x`
(`curvatureEnd_congr_left`, `curvatureEnd_congr_right`, whose side conditions are
`FiberBundle.extend_apply_self`), then `curvatureEnd_apply`. Every later corollary should be derived
from this rather than from the construction. -/
theorem curvatureAt_apply (hcov : IsCovariantDerivativeOn F cov Set.univ)
    (hcovloc : CovC2LocalMDiffAt F cov x) (hn : minSmoothness 𝕜 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hX : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% X) y)
    (hY : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% Y) y)
    (hσ : CMDiffAt (n : ℕ∞ω) (T% σ) x) :
    curvatureAt hcov hcovloc hn hn' (X x) (Y x) (σ x) = curvature cov X Y σ x := by
  rw [curvatureAt_apply_extend,
    curvatureEnd_congr_left hcov hcovloc hn hn'
      (eventually_contMDiffAt_extendTangent (X x)) hX
      (eventually_contMDiffAt_extendTangent (Y x)) (by simp),
    curvatureEnd_congr_right hcov hcovloc hn hn'
      (eventually_contMDiffAt_extendTangent (Y x)) hY hX (by simp),
    curvatureEnd_apply hcov hcovloc hn hn' hX hY hσ]

end Bundle₂

end RiemannianGeometry
