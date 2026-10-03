/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import RiemannianGeometry.CurvatureTensorial
import RiemannianGeometry.MLieBracketDerivation

/-!
# Tensoriality of the curvature operator in its section argument

  `R(X, Y)(f • σ) x = f x • R(X, Y)σ x`,   `R(X, Y)(σ + τ) x = R(X, Y)σ x + R(X, Y)τ x`.

## Main results

* `curvature_smul_section` — homogeneity, the hard one.
* `curvature_add_section` — additivity, which needs no second derivative at all.
* `curvature_smul_section_of_contMDiffAt` — the localised homogeneity law: `f` only `C^n` at `x`,
  `σ` only differentiable near `x`.
* `curvature_add_section_of_eventually` — the localised additivity law.

## The cancellation, exactly

Substituting `f • σ` makes the Leibniz rule fire *inside* the iterated term, which is why this slot
is not a variation on the vector-field slots. Writing `Xf` for `fun y ↦ d% f y (X y)`:

  `∇_X∇_Y(fσ)   = f ∇_X∇_Yσ + (Xf) ∇_Yσ + (Yf) ∇_Xσ + (X(Yf)) σ`
  `∇_Y∇_X(fσ)   = f ∇_Y∇_Xσ + (Yf) ∇_Xσ + (Xf) ∇_Yσ + (Y(Xf)) σ`
  `∇_{[X,Y]}(fσ) = f ∇_{[X,Y]}σ + ([X,Y]f) σ`

The four first-order terms cancel pairwise between the first two lines. What is left over is

  `R(X,Y)(fσ) - f · R(X,Y)σ = ( X(Yf) - Y(Xf) - [X,Y]f ) · σ`

In the Lean proof the cancellation is not hidden: `match_scalars` reduces the module identity to one
scalar goal per atom, `ring` closes every goal belonging to a first-order term, and the single
surviving goal is *literally* the derivation identity, discharged by `exact key`.

## Hypotheses, and the one that is stronger than in the vector-field slots

`hcov` and `hcovσ` are as in `CurvatureTensorial`. The new ones:

* `hf : ContMDiff I 𝓘(𝕜, 𝕜) n f` with `minSmoothness 𝕜 2 ≤ n` — `f` must be twice differentiable,
  which is intrinsic: the leftover coefficient is a second derivative of `f`. No weakening can
  remove it.
* `hσ : ContMDiff I (I.prod 𝓘(𝕜, F)) 1 (T% σ)` — differentiability of `σ` **everywhere**, not just
  at `x`. This is needed because the Leibniz rewrite of the intermediate section
  `fun y ↦ cov (f • σ) y (Y y)` must hold at every `y` before that section can be differentiated
  again. It can be localised to a neighbourhood of `x` using
  `IsCovariantDerivativeOn.congr_of_eventuallyEq`; that refinement is not done here.

## Consequence for the bundled curvature tensor

-/

noncomputable section
open Bundle Set VectorField Filter
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
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {n : ℕ∞} [IsManifold I 1 M] [IsManifold I (n + 1) M]
  {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
  {X Y : Π x : M, TangentSpace I x} {σ τ : Π x : M, V x} {f : M → 𝕜} {x : M}

section Smul

variable [CompleteSpace E]

/-- **The curvature operator is homogeneous in its section argument.** -/
theorem curvature_smul_section
    (hcov : IsCovariantDerivativeOn F cov Set.univ)
    (hcovσ : MDiffAtCovSection F cov σ x)
    (hn : minSmoothness 𝕜 2 ≤ n)
    (hf : ContMDiff I 𝓘(𝕜, 𝕜) n f)
    (hσ : ContMDiff I (I.prod 𝓘(𝕜, F)) 1 (T% σ))
    (hX : ContMDiff I I.tangent n (T% X)) (hY : ContMDiff I I.tangent n (T% Y)) :
    curvature cov X Y (f • σ) x = f x • curvature cov X Y σ x := by
  have h2n : (2 : ℕ∞ω) ≤ (n : ℕ∞ω) := le_minSmoothness.trans hn
  have hne : (n : ℕ∞ω) ≠ 0 := by intro h; rw [h] at h2n; simp at h2n
  have h1n : (1 : ℕ∞ω) ≤ (n : ℕ∞ω) := le_trans (by norm_num) h2n
  have hfd : ∀ y, MDiffAt f y := fun y ↦ hf.mdifferentiableAt hne
  have hσd : ∀ y, MDiffAt (T% σ) y := fun y ↦ hσ.mdifferentiableAt one_ne_zero
  -- rewrite the two intermediate sections
  have S1 : (fun y ↦ cov (f • σ) y (Y y))
      = f • (fun y ↦ cov σ y (Y y)) + (fun y ↦ d% f y (Y y)) • σ := by
    funext y
    rw [hcov.leibniz (hσd y) (hfd y)]
    simp
  have S2 : (fun y ↦ cov (f • σ) y (X y))
      = f • (fun y ↦ cov σ y (X y)) + (fun y ↦ d% f y (X y)) • σ := by
    funext y
    rw [hcov.leibniz (hσd y) (hfd y)]
    simp
  -- differentiability at x
  have hA : MDiffAt (T% (fun y ↦ cov σ y (Y y))) x :=
    mdiffAt_cov_apply hcovσ (hY.mdifferentiableAt hne)
  have hA' : MDiffAt (T% (fun y ↦ cov σ y (X y))) x :=
    mdiffAt_cov_apply hcovσ (hX.mdifferentiableAt hne)
  have hb : MDiffAt (fun y ↦ d% f y (Y y)) x :=
    mdifferentiableAt_mvfderiv_apply hf h2n (hY.of_le h1n)
  have ha : MDiffAt (fun y ↦ d% f y (X y)) x :=
    mdifferentiableAt_mvfderiv_apply hf h2n (hX.of_le h1n)
  have hfA : MDiffAt (T% (f • (fun y ↦ cov σ y (Y y)))) x := (hfd x).smul_section hA
  have hfA' : MDiffAt (T% (f • (fun y ↦ cov σ y (X y)))) x := (hfd x).smul_section hA'
  have hbσ : MDiffAt (T% ((fun y ↦ d% f y (Y y)) • σ)) x := hb.smul_section (hσd x)
  have haσ : MDiffAt (T% ((fun y ↦ d% f y (X y)) • σ)) x := ha.smul_section (hσd x)
  -- expand
  rw [curvature_apply, curvature_apply, S1, S2,
    hcov.add hfA hbσ, hcov.add hfA' haσ,
    hcov.leibniz hA (hfd x), hcov.leibniz (hσd x) hb,
    hcov.leibniz hA' (hfd x), hcov.leibniz (hσd x) ha,
    hcov.leibniz (hσd x) (hfd x)]
  have key := sub_eq_zero_of_eq (mvfderiv_apply_mlieBracket (I := I) (g := f) (x := x) hn hf hX hY)
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, FunLike.coe_smul, Pi.smul_apply]
  match_scalars
  all_goals first | ring1 | linear_combination key

/-- **The localised homogeneity law.** `f` need only be `C^n` at `x` (finite `n`), and `σ`
differentiable only *near* `x`.

This is the form the bundled tensor needs, because the local-frame coefficient functions and frame
sections that appear there live only on a trivialization's base set. The global version
`curvature_smul_section` is retained for callers who have global smoothness.

Two things change relative to the global proof. The Leibniz rewrite of the intermediate section
holds only near `x`, so it is swapped inside the outer connection by
`IsCovariantDerivativeOn.congr_of_eventuallyEq` — which demands differentiability of *both*
sections at `x`, and the original one is not a hypothesis, so it is transported from the
replacement by `MDifferentiableAt.congr_of_eventuallyEq`. And the cancellation identity is the
localised `mvfderiv_apply_mlieBracket_of_contMDiffAt`.

The cancellation is unchanged and still exposed: `match_scalars` splits the module identity, `ring1`
closes every first-order term, and the one surviving goal is

  `X(Yf) - Y(Xf) - [X,Y]f = 0`. -/
theorem curvature_smul_section_of_eventually
    (hcov : IsCovariantDerivativeOn F cov Set.univ)
    (hcovσ : MDiffAtCovSection F cov σ x)
    (hn : minSmoothness 𝕜 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : CMDiffAt (n : ℕ∞ω) f x)
    (hσ : ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y)
    (hX : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% X) y)
    (hY : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% Y) y) :
    curvature cov X Y (f • σ) x = f x • curvature cov X Y σ x := by
  have h2n : (2 : ℕ∞ω) ≤ (n : ℕ∞ω) := le_minSmoothness.trans hn
  have hne : (n : ℕ∞ω) ≠ 0 := by intro h; rw [h] at h2n; simp at h2n
  have h1n : (1 : ℕ∞ω) ≤ (n : ℕ∞ω) := le_trans (by norm_num) h2n
  have : IsManifold I (n : ℕ∞ω) M := IsManifold.of_le (n := (n : ℕ∞ω) + 1) le_self_add
  have hfev : ∀ᶠ y in 𝓝 x, MDiffAt f y :=
    ((contMDiffAt_iff_contMDiffAt_nhds hn').1 hf).mono fun _ h ↦ h.mdifferentiableAt hne
  have hfd : MDiffAt f x := hfev.self_of_nhds
  have hσd : MDiffAt (T% σ) x := hσ.self_of_nhds
  have hA : MDiffAt (T% fun y ↦ cov σ y (Y y)) x :=
    mdiffAt_cov_apply hcovσ (hY.self_of_nhds.mdifferentiableAt hne)
  have hA' : MDiffAt (T% fun y ↦ cov σ y (X y)) x :=
    mdiffAt_cov_apply hcovσ (hX.self_of_nhds.mdifferentiableAt hne)
  have hb : MDiffAt (fun y ↦ d% f y (Y y)) x :=
    mdifferentiableAt_mvfderiv_apply_of_contMDiffAt hf h2n hn' (hY.self_of_nhds.of_le h1n)
  have ha : MDiffAt (fun y ↦ d% f y (X y)) x :=
    mdifferentiableAt_mvfderiv_apply_of_contMDiffAt hf h2n hn' (hX.self_of_nhds.of_le h1n)
  have hfA : MDiffAt (T% (f • fun y ↦ cov σ y (Y y))) x := hfd.smul_section hA
  have hfA' : MDiffAt (T% (f • fun y ↦ cov σ y (X y))) x := hfd.smul_section hA'
  have hbσ : MDiffAt (T% ((fun y ↦ d% f y (Y y)) • σ)) x := hb.smul_section hσd
  have haσ : MDiffAt (T% ((fun y ↦ d% f y (X y)) • σ)) x := ha.smul_section hσd
  have hsumY : MDiffAt (T% (f • (fun y ↦ cov σ y (Y y)) + (fun y ↦ d% f y (Y y)) • σ)) x :=
    mdifferentiableAt_add_section hfA hbσ
  have hsumX : MDiffAt (T% (f • (fun y ↦ cov σ y (X y)) + (fun y ↦ d% f y (X y)) • σ)) x :=
    mdifferentiableAt_add_section hfA' haσ
  have S : ∀ Z : Π y : M, TangentSpace I y, ∀ᶠ y in 𝓝 x, cov (f • σ) y (Z y)
      = (f • (fun y ↦ cov σ y (Z y)) + (fun y ↦ d% f y (Z y)) • σ) y := by
    intro Z
    filter_upwards [hσ, hfev] with y hσy hfy
    rw [hcov.leibniz hσy hfy]
    simp
  have hIY : MDiffAt (T% fun y ↦ cov (f • σ) y (Y y)) x := by
    refine hsumY.congr_of_eventuallyEq ?_
    filter_upwards [S Y] with y hy
    simp [hy]
  have hIX : MDiffAt (T% fun y ↦ cov (f • σ) y (X y)) x := by
    refine hsumX.congr_of_eventuallyEq ?_
    filter_upwards [S X] with y hy
    simp [hy]
  have hXd : MDiffAt (T% X) x := hX.self_of_nhds.mdifferentiableAt hne
  have hYd : MDiffAt (T% Y) x := hY.self_of_nhds.mdifferentiableAt hne
  rw [curvature_apply, curvature_apply,
    hcov.congr_of_eventuallyEq hIY hsumY univ_mem (S Y),
    hcov.congr_of_eventuallyEq hIX hsumX univ_mem (S X),
    hcov.add hfA hbσ, hcov.add hfA' haσ,
    hcov.leibniz hA hfd, hcov.leibniz hσd hb,
    hcov.leibniz hA' hfd, hcov.leibniz hσd ha,
    hcov.leibniz hσd hfd]
  have key := sub_eq_zero_of_eq
    (mvfderiv_apply_mlieBracket_of_contMDiffAt (I := I) (g := f) (x := x) hn hn' hf hX hY)
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, FunLike.coe_smul, Pi.smul_apply]
  match_scalars
  all_goals first | ring1 | linear_combination key


/-- The `ContMDiff`-hypothesis form of `curvature_smul_section_of_eventually`.

Kept with its original statement because it is a frozen benchmark target
(`benchmarks/pw-foundations-v1`, goal 17); global smoothness of `X` and `Y` trivially implies the
eventual `C^n` hypotheses the localised version asks for. -/
theorem curvature_smul_section_of_contMDiffAt
    (hcov : IsCovariantDerivativeOn F cov Set.univ)
    (hcovσ : MDiffAtCovSection F cov σ x)
    (hn : minSmoothness 𝕜 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : CMDiffAt (n : ℕ∞ω) f x)
    (hσ : ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y)
    (hX : ContMDiff I I.tangent n (T% X)) (hY : ContMDiff I I.tangent n (T% Y)) :
    curvature cov X Y (f • σ) x = f x • curvature cov X Y σ x :=
  curvature_smul_section_of_eventually hcov hcovσ hn hn' hf hσ
    (Filter.Eventually.of_forall fun y ↦ hX y) (Filter.Eventually.of_forall fun y ↦ hY y)

end Smul

/-- **The curvature operator is additive in its section argument.**

Much easier than `curvature_smul_section`: no second derivative appears, because `∇` is additive on
the nose and the Leibniz rule never fires. Only additivity of the connection is used, once on each
of the three terms, plus once more inside the intermediate sections. -/
theorem curvature_add_section
    (hcov : IsCovariantDerivativeOn F cov Set.univ)
    (hcovσ : MDiffAtCovSection F cov σ x) (hcovτ : MDiffAtCovSection F cov τ x)
    (hσ : ContMDiff I (I.prod 𝓘(𝕜, F)) 1 (T% σ)) (hτ : ContMDiff I (I.prod 𝓘(𝕜, F)) 1 (T% τ))
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    curvature cov X Y (σ + τ) x = curvature cov X Y σ x + curvature cov X Y τ x := by
  have hσd : ∀ y, MDiffAt (T% σ) y := fun y ↦ hσ.mdifferentiableAt one_ne_zero
  have hτd : ∀ y, MDiffAt (T% τ) y := fun y ↦ hτ.mdifferentiableAt one_ne_zero
  have S1 : (fun y ↦ cov (σ + τ) y (Y y))
      = (fun y ↦ cov σ y (Y y)) + (fun y ↦ cov τ y (Y y)) := by
    funext y; rw [hcov.add (hσd y) (hτd y)]; simp
  have S2 : (fun y ↦ cov (σ + τ) y (X y))
      = (fun y ↦ cov σ y (X y)) + (fun y ↦ cov τ y (X y)) := by
    funext y; rw [hcov.add (hσd y) (hτd y)]; simp
  rw [curvature_apply, curvature_apply, curvature_apply, S1, S2,
    hcov.add (mdiffAt_cov_apply hcovσ hY) (mdiffAt_cov_apply hcovτ hY),
    hcov.add (mdiffAt_cov_apply hcovσ hX) (mdiffAt_cov_apply hcovτ hX),
    hcov.add (hσd x) (hτd x)]
  simp only [add_apply]
  abel

/-- **Curvature depends only on the germ of the section at the point.**

If `σ` and `τ` agree near `x` then `R(X, Y)σ x = R(X, Y)τ x`. Each of the three terms of the
curvature is handled by `IsCovariantDerivativeOn.congr_of_eventuallyEq`: for the two iterated terms
the *intermediate* sections agree near `x`, which is where `Filter.Eventually.eventually_nhds` is
needed — germ equality at `x` gives germ equality at every nearby point, and that is what lets the
connection be applied pointwise before the outer derivative is taken.
-/
theorem curvature_congr_of_eventuallyEq
    (hcov : IsCovariantDerivativeOn F cov Set.univ)
    (hσ : ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y) (hτ : ∀ᶠ y in 𝓝 x, MDiffAt (T% τ) y)
    (hcovσ : MDiffAtCovSection F cov σ x) (hcovτ : MDiffAtCovSection F cov τ x)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (h : ∀ᶠ y in 𝓝 x, σ y = τ y) :
    curvature cov X Y σ x = curvature cov X Y τ x := by
  have hgerm : ∀ᶠ y in 𝓝 x, ∀ᶠ z in 𝓝 y, σ z = τ z := h.eventually_nhds
  have inner : ∀ Z : Π x : M, TangentSpace I x,
      ∀ᶠ z in 𝓝 x, cov σ z (Z z) = cov τ z (Z z) := by
    intro Z
    filter_upwards [hgerm, hσ, hτ] with y hy hσy hτy
    rw [hcov.congr_of_eventuallyEq hσy hτy univ_mem hy]
  rw [curvature_apply, curvature_apply,
    hcov.congr_of_eventuallyEq (mdiffAt_cov_apply hcovσ hY) (mdiffAt_cov_apply hcovτ hY)
      univ_mem (inner Y),
    hcov.congr_of_eventuallyEq (mdiffAt_cov_apply hcovσ hX) (mdiffAt_cov_apply hcovτ hX)
      univ_mem (inner X),
    hcov.congr_of_eventuallyEq hσ.self_of_nhds hτ.self_of_nhds univ_mem h]

/-- **The localised additivity law.** `σ` and `τ` differentiable only near `x`.

Same localisation pattern as `curvature_smul_section_of_contMDiffAt`, and much shorter: additivity
of a connection needs no Leibniz rule and hence no second derivative. -/
theorem curvature_add_section_of_eventually
    (hcov : IsCovariantDerivativeOn F cov Set.univ)
    (hcovσ : MDiffAtCovSection F cov σ x) (hcovτ : MDiffAtCovSection F cov τ x)
    (hσ : ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y) (hτ : ∀ᶠ y in 𝓝 x, MDiffAt (T% τ) y)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    curvature cov X Y (σ + τ) x = curvature cov X Y σ x + curvature cov X Y τ x := by
  have hσd : MDiffAt (T% σ) x := hσ.self_of_nhds
  have hτd : MDiffAt (T% τ) x := hτ.self_of_nhds
  have hAY : MDiffAt (T% fun y ↦ cov σ y (Y y)) x := mdiffAt_cov_apply hcovσ hY
  have hAX : MDiffAt (T% fun y ↦ cov σ y (X y)) x := mdiffAt_cov_apply hcovσ hX
  have hBY : MDiffAt (T% fun y ↦ cov τ y (Y y)) x := mdiffAt_cov_apply hcovτ hY
  have hBX : MDiffAt (T% fun y ↦ cov τ y (X y)) x := mdiffAt_cov_apply hcovτ hX
  have hsumY : MDiffAt (T% ((fun y ↦ cov σ y (Y y)) + fun y ↦ cov τ y (Y y))) x :=
    mdifferentiableAt_add_section hAY hBY
  have hsumX : MDiffAt (T% ((fun y ↦ cov σ y (X y)) + fun y ↦ cov τ y (X y))) x :=
    mdifferentiableAt_add_section hAX hBX
  have S : ∀ Z : Π y : M, TangentSpace I y, ∀ᶠ y in 𝓝 x, cov (σ + τ) y (Z y)
      = ((fun y ↦ cov σ y (Z y)) + fun y ↦ cov τ y (Z y)) y := by
    intro Z
    filter_upwards [hσ, hτ] with y hσy hτy
    rw [hcov.add hσy hτy]
    simp
  have hIY : MDiffAt (T% fun y ↦ cov (σ + τ) y (Y y)) x := by
    refine hsumY.congr_of_eventuallyEq ?_
    filter_upwards [S Y] with y hy
    simp [hy]
  have hIX : MDiffAt (T% fun y ↦ cov (σ + τ) y (X y)) x := by
    refine hsumX.congr_of_eventuallyEq ?_
    filter_upwards [S X] with y hy
    simp [hy]
  rw [curvature_apply, curvature_apply, curvature_apply,
    hcov.congr_of_eventuallyEq hIY hsumY univ_mem (S Y),
    hcov.congr_of_eventuallyEq hIX hsumX univ_mem (S X),
    hcov.add hAY hBY, hcov.add hAX hBX, hcov.add hσd hτd]
  simp only [add_apply]
  abel

end RiemannianGeometry
