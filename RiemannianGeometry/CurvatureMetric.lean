/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import RiemannianGeometry.Curvature
import RiemannianGeometry.CurvaturePointwise
import RiemannianGeometry.CovariantDerivativeSmooth
import RiemannianGeometry.MLieBracketDerivation

/-!
# Curvature of a metric-compatible connection is skew-adjoint

For a connection compatible with a fibre metric,

  `g (R(X,Y)Z) W = − g Z (R(X,Y)W)`,

i.e. each curvature endomorphism is skew-adjoint for the metric. Lowered to the `(0,4)` tensor this
is antisymmetry in the **last** pair.

Stated at the strongest natural level: an **arbitrary** vector bundle `V` over `M`, a fibre metric
supplied as *data*, and an arbitrary `cov` **compatible with it**. Not the tangent bundle and not
`ℝ`.

Compatibility is the essential hypothesis and is present as `hmc : IsMetricCompatibleWith F cov g` —
the statement is false without it, and it is what ties `cov` to `g`. What is *not* needed is the
structure of a covariant derivative: `IsCovariantDerivativeOn` never appears, so neither the Leibniz
rule nor additivity in the section is used, and `cov` may be any function of the right type that
happens to satisfy compatibility and the local regularity. Symmetry of `g`, nondegeneracy and
positive definiteness are also unused.

(An earlier report of this campaign compressed that to "no connection axioms are needed", which read
as though nothing linked `cov` to `g`. The theorem was always stated correctly; only the summary was
loose. Corrected here and in `PROJECT_STATE.md`.)

## Main results

* `Filter.EventuallyEq.mvfderiv_eq` — germ-locality of `mvfderiv`, absent from Mathlib.
* `mdiffAt_pairing_bundle` — the general-`V` pairing lemma.
* `IsMetricCompatibleWith` — compatibility with a fibre metric given as data.
* `curvature_skewAdjoint`, and `curvature_skewAdjoint_two` at `C²` over `ℝ`/`ℂ`.

## Proof, and why it needs no third derivative of the metric

Write `f := g(Z,W)`. Metric compatibility is a *proposition*, so it may be applied as often as one
likes at no cost in regularity, and it is applied three times: along `X` and along `Y` (after an
eventual identity of functions near `x`), and along `[X,Y]`. The only differentiation performed is
of the **scalar** `f`, twice, and the two second derivatives are related by the manifold derivation
identity `X(Yf) − Y(Xf) = [X,Y]f` of `RiemannianGeometry.MLieBracketDerivation`. Substituting the three
expansions, the two cross terms `g(∇_Y Z, ∇_X W)` and `g(∇_X Z, ∇_Y W)` appear once in each of
`X(Yf)` and `Y(Xf)` and cancel in the difference, leaving exactly
`g(R(X,Y)Z, W) + g(Z, R(X,Y)W) = 0`.

## Regularity, exactly

The base manifold must be `C³` (`IsManifold I 3 M`) in the `C²` corollary. That is forced by
Mathlib's Lie-bracket lemmas, not by the geometry, and is a condition on the charts rather than on
the metric. Where `[IsManifold I ∞ M]` is assumed, as downstream, it costs nothing.

`minSmoothness 𝕜 2 ≤ n` with `n : ℕ∞` is satisfiable only over an `IsRCLikeNormedField`; off `ℝ`
and `ℂ` the general statement is honest but empty. `curvature_skewAdjoint_two` is therefore the
form to quote, since it discharges that hypothesis rather than carrying it.
-/

noncomputable section

open Bundle NormedSpace Set VectorField Filter
open scoped Manifold ContDiff Topology

/-! ## A congruence lemma for `mvfderiv` under eventual equality

Mathlib has `Filter.EventuallyEq.mfderiv_eq` but not the `mvfderiv` version. -/

section MVFDerivCongr

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- `mvfderiv` depends only on the germ: if `f₁ = f` near `x` then `d% f₁ x = d% f x`.

`mvfderiv` is `(fromTangentSpace (f x)).toContinuousLinearMap ∘L mfderiv% f x`; `h.mfderiv_eq`
handles the differential, and the residual mismatch of the base point of `fromTangentSpace` is
closed by `rfl`, since `fromTangentSpace` is the identity for every base point. -/
theorem Filter.EventuallyEq.mvfderiv_eq {f₁ f : M → F} {x : M} (h : f₁ =ᶠ[𝓝 x] f) :
    d% f₁ x = d% f x := by
  exact Filter.EventuallyEq.mfderiv_eq h

end MVFDerivCongr

namespace RiemannianGeometry

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-! ## Differentiability of the pairing, for a general bundle `V`

`RiemannianGeometry.KoszulBundled.mdiffAt_pairing` is the same statement for the tangent bundle; the
proof is verbatim the same three lines through `MDifferentiableAt.clm_bundle_apply₂`. -/

omit [CompleteSpace E] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)] in
/-- `y ↦ g y (U y) (W y)` is differentiable at `y` as soon as the metric *section* `g`, and the
sections `U`, `W`, are. -/
theorem mdiffAt_pairing_bundle {g : Π y : M, V y →L[𝕜] V y →L[𝕜] 𝕜} {y : M}
    (hgm : MDiffAt (fun z ↦ TotalSpace.mk' (F →L[𝕜] F →L[𝕜] 𝕜)
      (E := fun (z : M) ↦ V z →L[𝕜] V z →L[𝕜] 𝕜) z (g z)) y)
    {U W : Π z : M, V z} (hU : MDiffAt (T% U) y) (hW : MDiffAt (T% W) y) :
    MDiffAt (fun z ↦ g z (U z) (W z)) y := by
  have h : MDifferentiableAt I (I.prod 𝓘(𝕜, 𝕜))
      (fun z ↦ TotalSpace.mk' 𝕜 (E := Bundle.Trivial M 𝕜) z (g z (U z) (W z))) y :=
    MDifferentiableAt.clm_bundle_apply₂ (F₁ := F) (F₂ := F) (F₃ := 𝕜) hgm hU hW
  rw [mdifferentiableAt_totalSpace] at h
  exact h.2

/-! ## Metric compatibility for a general bundle -/

variable (F) in
/-- **Compatibility of a connection on `V` with a fibre metric given as data.**

`X g(σ, τ) = g(∇_X σ, τ) + g(σ, ∇_X τ)` whenever `σ` and `τ` are differentiable at the point.
This mirrors `RiemannianGeometry.IsCompatibleWith` (which is the tangent-bundle, real case), and it is
Mathlib's `IsMetricCompatible.mvfderiv_inner_eq` with the metric supplied explicitly.  No
hypothesis on the direction `X` is needed, exactly as in Mathlib's version; in particular the
direction may be instantiated to `mlieBracket I X Y`. -/
def IsMetricCompatibleWith
    (cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x))
    (g : Π x : M, V x →L[𝕜] V x →L[𝕜] 𝕜) : Prop :=
  ∀ {X : Π x : M, TangentSpace I x} {σ τ : Π x : M, V x} {x : M},
    MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      d% (fun y ↦ g y (σ y) (τ y)) x (X x)
        = g x (cov σ x (X x)) (τ x) + g x (σ x) (cov τ x (X x))

/-! ## Skew-adjointness of the curvature operator -/

variable {n : ℕ∞} [IsManifold I 1 M] [IsManifold I (n + 1) M]
  {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
  {g : Π x : M, V x →L[𝕜] V x →L[𝕜] 𝕜}
  {X Y : Π x : M, TangentSpace I x} {Z W : Π x : M, V x} {x : M}

/-- **The curvature of a metric-compatible connection is fibrewise skew-adjoint.**

`g(R(X,Y)Z, W) = - g(Z, R(X,Y)W)`.

No symmetry, nondegeneracy or positive-definiteness of `g` is used, and `cov` need not even be a
genuine covariant derivative: only the compatibility identity `hmc`, the local regularity `hcovloc`
of `cov`, and the regularity hypotheses below.

The proof is the classical one.  Write `f := g(Z, W)`.  Compatibility at every point near `x`
identifies `Y f` with `g(∇_Y Z, W) + g(Z, ∇_Y W)` as *functions* near `x`; differentiating that
along `X` and using compatibility twice more expands `X(Y f)`, and symmetrically for `Y(X f)`.
The four cross terms `g(∇_Y Z, ∇_X W)`, `g(∇_X Z, ∇_Y W)` occur in both expansions and cancel in
the difference.  `mvfderiv_apply_mlieBracket_of_contMDiffAt` equates that difference with
`[X,Y] f`, which compatibility expands as `g(∇_{[X,Y]}Z, W) + g(Z, ∇_{[X,Y]}W)`.  What is left is
`g(R(X,Y)Z, W) + g(Z, R(X,Y)W) = 0`. -/
theorem curvature_skewAdjoint
    (hn : minSmoothness 𝕜 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hmc : IsMetricCompatibleWith F cov g)
    (hcovloc : CovC2LocalMDiffAt F cov x)
    (hgx : MDiffAt (fun z ↦ TotalSpace.mk' (F →L[𝕜] F →L[𝕜] 𝕜)
      (E := fun (z : M) ↦ V z →L[𝕜] V z →L[𝕜] 𝕜) z (g z)) x)
    (hZ : ∀ᶠ y in 𝓝 x, CMDiffAt (2 : ℕ∞ω) (T% Z) y)
    (hW : ∀ᶠ y in 𝓝 x, CMDiffAt (2 : ℕ∞ω) (T% W) y)
    (hX : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% X) y)
    (hY : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% Y) y)
    (hf : CMDiffAt (n : ℕ∞ω) (fun y ↦ g y (Z y) (W y)) x) :
    g x (curvature cov X Y Z x) (W x) = - g x (Z x) (curvature cov X Y W x) := by
  -- numeric bookkeeping
  have h2n : (2 : ℕ∞ω) ≤ (n : ℕ∞ω) := le_minSmoothness.trans hn
  have hne : (n : ℕ∞ω) ≠ 0 := by intro h; rw [h] at h2n; simp at h2n
  have hne2 : (2 : ℕ∞ω) ≠ 0 := by simp
  -- pointwise differentiability of the four data sections
  have hZx : MDiffAt (T% Z) x := hZ.self_of_nhds.mdifferentiableAt hne2
  have hWx : MDiffAt (T% W) x := hW.self_of_nhds.mdifferentiableAt hne2
  have hXx : MDiffAt (T% X) x := hX.self_of_nhds.mdifferentiableAt hne
  have hYx : MDiffAt (T% Y) x := hY.self_of_nhds.mdifferentiableAt hne
  -- the covariant derivatives of `Z` and `W`, as `Hom`-sections, are differentiable at `x`
  have hcovZ : MDiffAtCovSection F cov Z x := hcovloc Z hZ
  have hcovW : MDiffAtCovSection F cov W x := hcovloc W hW
  -- hence the four first covariant derivatives are differentiable at `x`
  have hPx : MDiffAt (T% fun y ↦ cov Z y (Y y)) x := mdiffAt_cov_apply hcovZ hYx
  have hQx : MDiffAt (T% fun y ↦ cov W y (Y y)) x := mdiffAt_cov_apply hcovW hYx
  have hP'x : MDiffAt (T% fun y ↦ cov Z y (X y)) x := mdiffAt_cov_apply hcovZ hXx
  have hQ'x : MDiffAt (T% fun y ↦ cov W y (X y)) x := mdiffAt_cov_apply hcovW hXx
  -- hence the four pairings appearing after the first differentiation are differentiable at `x`
  have hA1 : MDiffAt (fun y ↦ g y (cov Z y (Y y)) (W y)) x := mdiffAt_pairing_bundle hgx hPx hWx
  have hA2 : MDiffAt (fun y ↦ g y (Z y) (cov W y (Y y))) x := mdiffAt_pairing_bundle hgx hZx hQx
  have hB1 : MDiffAt (fun y ↦ g y (cov Z y (X y)) (W y)) x := mdiffAt_pairing_bundle hgx hP'x hWx
  have hB2 : MDiffAt (fun y ↦ g y (Z y) (cov W y (X y))) x := mdiffAt_pairing_bundle hgx hZx hQ'x
  -- STEP 1: compatibility near `x`, as an eventual identity of functions
  have eqY : (fun y ↦ d% (fun z ↦ g z (Z z) (W z)) y (Y y))
      =ᶠ[𝓝 x] ((fun y ↦ g y (cov Z y (Y y)) (W y)) + fun y ↦ g y (Z y) (cov W y (Y y))) := by
    filter_upwards [hZ, hW] with y hy hy'
    simp only [Pi.add_apply]
    exact hmc (X := Y) (hy.mdifferentiableAt hne2) (hy'.mdifferentiableAt hne2)
  have eqX : (fun y ↦ d% (fun z ↦ g z (Z z) (W z)) y (X y))
      =ᶠ[𝓝 x] ((fun y ↦ g y (cov Z y (X y)) (W y)) + fun y ↦ g y (Z y) (cov W y (X y))) := by
    filter_upwards [hZ, hW] with y hy hy'
    simp only [Pi.add_apply]
    exact hmc (X := X) (hy.mdifferentiableAt hne2) (hy'.mdifferentiableAt hne2)
  -- STEP 2: differentiate along `X`, resp. `Y`, and apply compatibility twice more
  have hA : d% (fun y ↦ d% (fun z ↦ g z (Z z) (W z)) y (Y y)) x (X x)
      = (g x (cov (fun y ↦ cov Z y (Y y)) x (X x)) (W x)
          + g x (cov Z x (Y x)) (cov W x (X x)))
        + (g x (cov Z x (X x)) (cov W x (Y x))
          + g x (Z x) (cov (fun y ↦ cov W y (Y y)) x (X x))) := by
    simp only [eqY.mvfderiv_eq, mvfderiv_add hA1 hA2, add_apply,
      hmc (X := X) (σ := fun y ↦ cov Z y (Y y)) (τ := W) hPx hWx,
      hmc (X := X) (σ := Z) (τ := fun y ↦ cov W y (Y y)) hZx hQx]
  have hB : d% (fun y ↦ d% (fun z ↦ g z (Z z) (W z)) y (X y)) x (Y x)
      = (g x (cov (fun y ↦ cov Z y (X y)) x (Y x)) (W x)
          + g x (cov Z x (X x)) (cov W x (Y x)))
        + (g x (cov Z x (Y x)) (cov W x (X x))
          + g x (Z x) (cov (fun y ↦ cov W y (X y)) x (Y x))) := by
    simp only [eqX.mvfderiv_eq, mvfderiv_add hB1 hB2, add_apply,
      hmc (X := Y) (σ := fun y ↦ cov Z y (X y)) (τ := W) hP'x hWx,
      hmc (X := Y) (σ := Z) (τ := fun y ↦ cov W y (X y)) hZx hQ'x]
  -- STEP 3: compatibility in the direction `[X, Y]`
  have hC : d% (fun z ↦ g z (Z z) (W z)) x (mlieBracket I X Y x)
      = g x (cov Z x (mlieBracket I X Y x)) (W x)
        + g x (Z x) (cov W x (mlieBracket I X Y x)) :=
    hmc (X := mlieBracket I X Y) (σ := Z) (τ := W) hZx hWx
  -- STEP 4: the derivation identity `X(Yf) - Y(Xf) = [X,Y]f`
  have hD : d% (fun y ↦ d% (fun z ↦ g z (Z z) (W z)) y (Y y)) x (X x)
        - d% (fun y ↦ d% (fun z ↦ g z (Z z) (W z)) y (X y)) x (Y x)
      = d% (fun z ↦ g z (Z z) (W z)) x (mlieBracket I X Y x) :=
    mvfderiv_apply_mlieBracket_of_contMDiffAt hn hn' hf hX hY
  -- substitute; the four cross terms cancel
  simp only [curvature_apply, map_sub, sub_apply]
  linear_combination hD - hA + hB + hC

omit [IsManifold I (n + 1) M] in
/-- **`C²` suffices.**  The `n = 2` specialisation, over `ℝ` or `ℂ` (`IsRCLikeNormedField`, which
is exactly when `minSmoothness 𝕜 2 = 2` and hence when the hypothesis `minSmoothness 𝕜 2 ≤ n` of
the general statement is satisfiable at a finite `n` at all).

Everything is at order `2`: the sections `Z`, `W` and the vector fields `X`, `Y` are `C²` near `x`,
the metric is a differentiable section at `x`, and the single pairing `g(Z, W)` is `C²` at `x`.
No third derivative of `g` appears anywhere. -/
theorem curvature_skewAdjoint_two [IsRCLikeNormedField 𝕜] [IsManifold I 3 M]
    (hmc : IsMetricCompatibleWith F cov g)
    (hcovloc : CovC2LocalMDiffAt F cov x)
    (hgx : MDiffAt (fun z ↦ TotalSpace.mk' (F →L[𝕜] F →L[𝕜] 𝕜)
      (E := fun (z : M) ↦ V z →L[𝕜] V z →L[𝕜] 𝕜) z (g z)) x)
    (hZ : ∀ᶠ y in 𝓝 x, CMDiffAt (2 : ℕ∞ω) (T% Z) y)
    (hW : ∀ᶠ y in 𝓝 x, CMDiffAt (2 : ℕ∞ω) (T% W) y)
    (hX : ∀ᶠ y in 𝓝 x, CMDiffAt (2 : ℕ∞ω) (T% X) y)
    (hY : ∀ᶠ y in 𝓝 x, CMDiffAt (2 : ℕ∞ω) (T% Y) y)
    (hf : CMDiffAt (2 : ℕ∞ω) (fun y ↦ g y (Z y) (W y)) x) :
    g x (curvature cov X Y Z x) (W x) = - g x (Z x) (curvature cov X Y W x) := by
  have h3 : IsManifold I (((2 : ℕ∞) : ℕ∞ω) + 1) M := by
    have he : (((2 : ℕ∞) : ℕ∞ω) + 1) = 3 := by norm_num
    rw [he]; infer_instance
  exact curvature_skewAdjoint (n := 2) (by simp) (by simp) hmc hcovloc hgx hZ hW hX hY hf

end RiemannianGeometry

