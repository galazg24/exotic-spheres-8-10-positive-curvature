/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import RiemannianGeometry.MLieBracketDerivation
import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-!
# Naturality of the Lie bracket for `f`-related vector fields

If `f : M → B` is a `C^n` map of manifolds and the vector fields `X'`, `Y'` on `M` are
`f`-related to the vector fields `X`, `Y` on `B`, i.e.

  `mfderiv I J f z (X' z) = X (f z)`  and  `mfderiv I J f z (Y' z) = Y (f z)`,

then `[X', Y']` is `f`-related to `[X, Y]`:

  `mfderiv I J f p (mlieBracket I X' Y' p) = mlieBracket J X Y (f p)`.

## Main results

* `mvfderiv_comp`, `mvfderiv_comp_apply` — the chain rule for `mvfderiv`.
* `mvfderiv_apply_comp_eventuallyEq` — relatedness transports directional derivatives:
  `X'(h ∘ f) = (X h) ∘ f` near `p`.
* `injective_mfderiv_extChartAt` — `mfderiv` of `extChartAt J q` at its own centre is injective.
* `eq_of_forall_mvfderiv_eq` — scalar test functions separate tangent vectors.
* `mvfderiv_apply_mfderiv_mlieBracket_of_related` — the identity tested against one scalar function.
* `mfderiv_mlieBracket_of_related` — the theorem, with relatedness assumed only near `p`.
* `mfderiv_mlieBracket_of_related_forall` — the theorem with relatedness assumed everywhere.

## Absent from Mathlib

Mathlib has no notion of `f`-relatedness of vector fields. Its only bracket-naturality statement,
`VectorField.mpullback_mlieBracket` in `Mathlib/Geometry/Manifold/VectorField/LieBracket.lean`, is
about `VectorField.mpullback`, which is defined through `ContinuousLinearMap.inverse` and therefore
takes its junk value `0` whenever `mfderiv% f x` is not invertible. That statement is thus about
local diffeomorphisms, and is vacuously true for, e.g., a submersion with positive-dimensional
fibre. The theorem below assumes no injectivity, immersivity or submersivity of `f`.

## Proof

1. A chain rule for `mvfderiv`: `d% (h ∘ f) p = d% h (f p) ∘L mfderiv I J f p`, from
   `mfderiv_comp` and the definition of `mvfderiv` (the `NormedSpace.fromTangentSpace` factor is
   the identity at every base point, so it simply passes through).
2. Relatedness turns that into an identity of *functions* on `M`: `X'(h ∘ f) = (X h) ∘ f` near `p`.
3. Applying the derivation identity upstairs with `g := h ∘ f` and downstairs with `g := h`, the
   two first-order terms match by (2), so the two bracket terms match:
   `d% h (f p) (df_p [X', Y']_p) = d% h (f p) ([X, Y]_{f p})` for every `C^n` test function `h`.
4. Separating the tangent vectors. This is the only place a chart is used, and only as a supply of
   test functions: for `φ` a continuous linear functional on `E'`, `h := φ ∘ extChartAt J (f p)` is
   `C^n` at `f p` (`contMDiffAt_extChartAt`, which needs no `IsManifold` hypothesis at the centre),
   and step 3 for these `h` gives `φ (A v) = φ (A w)` where `A := mfderiv% (extChartAt J (f p))
   (f p)`. `SeparatingDual 𝕜 E'` gives `A v = A w`, and `A` is injective because
   `mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt` exhibits a left inverse for it. Note
   that this argument never needs `A` to be the identity map.

`SeparatingDual 𝕜 E'` is Mathlib's class saying continuous linear forms separate points of `E'`;
it is an instance for every normed space over an `RCLike` field, hence automatic in the only cases
where the hypothesis `minSmoothness 𝕜 2 ≤ n` with `n : ℕ∞` is satisfiable at all.
-/

noncomputable section

open Bundle Set VectorField Filter RiemannianGeometry
open scoped Manifold ContDiff Topology

namespace RiemannianGeometry

section Chain

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {B : Type*} [TopologicalSpace B] [ChartedSpace H' B]

/-- `mvfderiv` depends only on the germ. Restated here so that this file needs only
`MLieBracketDerivation` from the project; it is `Filter.EventuallyEq.mfderiv_eq` up to the
`NormedSpace.fromTangentSpace` factor, which is the identity at every base point. -/
theorem mvfderiv_congr_of_eventuallyEq {f₁ f : M → F} {x : M} (h : f₁ =ᶠ[𝓝 x] f) :
    d% f₁ x = d% f x :=
  Filter.EventuallyEq.mfderiv_eq h

/-- **Step 1: the chain rule for `mvfderiv`.** For `h : B → F` and `f : M → B`,
`d% (h ∘ f) p = d% h (f p) ∘L mfderiv I J f p`. -/
theorem mvfderiv_comp {h : B → F} {f : M → B} {p : M}
    (hh : MDifferentiableAt J 𝓘(𝕜, F) h (f p)) (hf : MDifferentiableAt I J f p) :
    d% (h ∘ f) p = (d% h (f p)) ∘L (mfderiv I J f p) := by
  simp only [mvfderiv, Function.comp_apply]
  rw [mfderiv_comp p hh hf]
  rfl

/-- The applied form of `mvfderiv_comp`. -/
theorem mvfderiv_comp_apply {h : B → F} {f : M → B} {p : M}
    (hh : MDifferentiableAt J 𝓘(𝕜, F) h (f p)) (hf : MDifferentiableAt I J f p)
    (v : TangentSpace I p) :
    d% (h ∘ f) p v = d% h (f p) (mfderiv I J f p v) := by
  rw [mvfderiv_comp hh hf]; rfl

/-- **Step 2: relatedness transports directional derivatives.** If `V` is `f`-related to `W` near
`p`, then, as functions on `M` near `p`, `V (h ∘ f) = (W h) ∘ f`. -/
theorem mvfderiv_apply_comp_eventuallyEq {h : B → 𝕜} {f : M → B}
    {V : Π x : M, TangentSpace I x} {W : Π y : B, TangentSpace J y} {p : M}
    (hrel : ∀ᶠ z in 𝓝 p, mfderiv I J f z (V z) = W (f z))
    (hh : ∀ᶠ z in 𝓝 p, MDifferentiableAt J 𝓘(𝕜, 𝕜) h (f z))
    (hf : ∀ᶠ z in 𝓝 p, MDifferentiableAt I J f z) :
    (fun y ↦ d% (h ∘ f) y (V y)) =ᶠ[𝓝 p] ((fun q ↦ d% h q (W q)) ∘ f) := by
  filter_upwards [hrel, hh, hf] with z h1 h2 h3
  rw [mvfderiv_comp_apply h2 h3, h1]
  rfl

end Chain

section Separate

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {B : Type*} [TopologicalSpace B] [ChartedSpace H' B]

/-- The differential of `extChartAt J q` at its own centre is injective: it has the differential of
the inverse chart as a left inverse. No claim that it is the identity is needed. -/
theorem injective_mfderiv_extChartAt [IsManifold J 1 B] (q : B) :
    Function.Injective (mfderiv J 𝓘(𝕜, E') (extChartAt J q) q) := by
  have h2 := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt
    (I := J) (x := q) (y := extChartAt J q q) (by simp)
  rw [show (extChartAt J q).symm (extChartAt J q q) = q by simp] at h2
  have h5 : ∀ v : TangentSpace J q,
      mfderivWithin 𝓘(𝕜, E') J (extChartAt J q).symm (range J) (extChartAt J q q)
        (mfderiv J 𝓘(𝕜, E') (extChartAt J q) q v) = v :=
    fun v ↦ DFunLike.congr_fun h2 v
  intro a b hab
  rw [← h5 a, ← h5 b, hab]

/-- The `mvfderiv` of a continuous linear functional is the functional itself. -/
theorem mvfderiv_clm (φ : E' →L[𝕜] 𝕜) (z : E') (t : TangentSpace 𝓘(𝕜, E') z) :
    d% (⇑φ) z t = φ t := by
  simp only [mvfderiv, mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
  rfl

/-- **Step 4: scalar test functions separate tangent vectors.** If every `C^n` function `h : B → 𝕜`
has `d% h q v = d% h q w`, then `v = w`. The test functions used are `φ ∘ extChartAt J q` for `φ`
in the continuous dual of `E'`. -/
theorem eq_of_forall_mvfderiv_eq [IsManifold J 1 B] [SeparatingDual 𝕜 E'] {n : ℕ∞ω} {q : B}
    {v w : TangentSpace J q}
    (H : ∀ h : B → 𝕜, ContMDiffAt J 𝓘(𝕜, 𝕜) n h q → d% h q v = d% h q w) :
    v = w := by
  set e := extChartAt J q with he
  have hde : MDifferentiableAt J 𝓘(𝕜, E') e q :=
    mdifferentiableAt_extChartAt (mem_chart_source H' q)
  apply injective_mfderiv_extChartAt q
  apply (NormedSpace.fromTangentSpace (𝕜 := 𝕜) (E := E') (e q)).injective
  refine SeparatingDual.eq_iff_forall_dual_eq (R := 𝕜) |>.2 fun φ ↦ ?_
  have key := H (⇑φ ∘ e) (φ.contMDiffAt.comp q contMDiffAt_extChartAt)
  rw [mvfderiv_comp_apply ((φ.contMDiffAt (n := 1)).mdifferentiableAt one_ne_zero) hde,
    mvfderiv_comp_apply ((φ.contMDiffAt (n := 1)).mdifferentiableAt one_ne_zero) hde,
    mvfderiv_clm, mvfderiv_clm] at key
  exact key

end Separate

section Related

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [CompleteSpace E']
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {B : Type*} [TopologicalSpace B] [ChartedSpace H' B]
  {n : ℕ∞} [IsManifold I 1 M] [IsManifold I (n + 1) M]
  [IsManifold J 1 B] [IsManifold J (n + 1) B]
  {f : M → B} {X' Y' : Π x : M, TangentSpace I x} {X Y : Π y : B, TangentSpace J y} {p : M}

/-- **Step 3: the identity, tested against a single scalar function.**

For every `h : B → 𝕜` of class `C^n` at `f p`,
`d% h (f p) (df_p [X', Y']_p) = d% h (f p) ([X, Y]_{f p})`.

Obtained by applying the derivation identity `X(Yg) - Y(Xg) = [X,Y]g` upstairs with `g := h ∘ f`
and downstairs with `g := h`, and matching the first-order terms with
`mvfderiv_apply_comp_eventuallyEq`. -/
theorem mvfderiv_apply_mfderiv_mlieBracket_of_related {h : B → 𝕜}
    (hn : minSmoothness 𝕜 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiffAt I J (n : ℕ∞ω) f p) (hh : ContMDiffAt J 𝓘(𝕜, 𝕜) (n : ℕ∞ω) h (f p))
    (hXrel : ∀ᶠ z in 𝓝 p, mfderiv I J f z (X' z) = X (f z))
    (hYrel : ∀ᶠ z in 𝓝 p, mfderiv I J f z (Y' z) = Y (f z))
    (hX' : ∀ᶠ z in 𝓝 p, ContMDiffAt I I.tangent (n : ℕ∞ω) (T% X') z)
    (hY' : ∀ᶠ z in 𝓝 p, ContMDiffAt I I.tangent (n : ℕ∞ω) (T% Y') z)
    (hX : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent (n : ℕ∞ω) (T% X) q)
    (hY : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent (n : ℕ∞ω) (T% Y) q) :
    d% h (f p) (mfderiv I J f p (mlieBracket I X' Y' p))
      = d% h (f p) (mlieBracket J X Y (f p)) := by
  have h2n : (2 : ℕ∞ω) ≤ (n : ℕ∞ω) := le_minSmoothness.trans hn
  have hne : (n : ℕ∞ω) ≠ 0 := by intro hc; rw [hc] at h2n; simp at h2n
  have h1n : (1 : ℕ∞ω) ≤ (n : ℕ∞ω) := le_trans (by norm_num) h2n
  have iM : IsManifold I (n : ℕ∞ω) M := IsManifold.of_le (n := (n : ℕ∞ω) + 1) le_self_add
  have iB : IsManifold J (n : ℕ∞ω) B := IsManifold.of_le (n := (n : ℕ∞ω) + 1) le_self_add
  have hfev : ∀ᶠ z in 𝓝 p, ContMDiffAt I J (n : ℕ∞ω) f z :=
    (contMDiffAt_iff_contMDiffAt_nhds hn').1 hf
  have hfd : ∀ᶠ z in 𝓝 p, MDifferentiableAt I J f z := hfev.mono fun _ hz ↦ hz.mdifferentiableAt hne
  have hhev : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J 𝓘(𝕜, 𝕜) (n : ℕ∞ω) h q :=
    (contMDiffAt_iff_contMDiffAt_nhds hn').1 hh
  have hhf : ∀ᶠ z in 𝓝 p, MDifferentiableAt J 𝓘(𝕜, 𝕜) h (f z) :=
    hf.continuousAt.eventually (hhev.mono fun _ hz ↦ hz.mdifferentiableAt hne)
  have hgf : ContMDiffAt I 𝓘(𝕜, 𝕜) (n : ℕ∞ω) (h ∘ f) p := hh.comp p hf
  have eq1 := mvfderiv_apply_mlieBracket_of_contMDiffAt (I := I) (g := h ∘ f) (X := X') (Y := Y')
    (x := p) hn hn' hgf hX' hY'
  have eq2 := mvfderiv_apply_mlieBracket_of_contMDiffAt (I := J) (g := h) (X := X) (Y := Y)
    (x := f p) hn hn' hh hX hY
  have eqA : d% (fun y ↦ d% (h ∘ f) y (Y' y)) p (X' p)
      = d% (fun q ↦ d% h q (Y q)) (f p) (X (f p)) := by
    rw [mvfderiv_congr_of_eventuallyEq (mvfderiv_apply_comp_eventuallyEq hYrel hhf hfd),
      mvfderiv_comp_apply
        (mdifferentiableAt_mvfderiv_apply_of_contMDiffAt hh h2n hn' (hY.self_of_nhds.of_le h1n))
        hfd.self_of_nhds, hXrel.self_of_nhds]
  have eqB : d% (fun y ↦ d% (h ∘ f) y (X' y)) p (Y' p)
      = d% (fun q ↦ d% h q (X q)) (f p) (Y (f p)) := by
    rw [mvfderiv_congr_of_eventuallyEq (mvfderiv_apply_comp_eventuallyEq hXrel hhf hfd),
      mvfderiv_comp_apply
        (mdifferentiableAt_mvfderiv_apply_of_contMDiffAt hh h2n hn' (hX.self_of_nhds.of_le h1n))
        hfd.self_of_nhds, hYrel.self_of_nhds]
  have eqC : d% (h ∘ f) p (mlieBracket I X' Y' p)
      = d% h (f p) (mfderiv I J f p (mlieBracket I X' Y' p)) :=
    mvfderiv_comp_apply hhf.self_of_nhds hfd.self_of_nhds _
  rw [← eqC, ← eq1, eqA, eqB, eq2]

/-- **Naturality of the Lie bracket for `f`-related vector fields.**

If `X'` is `f`-related to `X` and `Y'` is `f`-related to `Y` near `p`, then `[X', Y']` is
`f`-related to `[X, Y]` at `p`:

  `mfderiv I J f p [X', Y']_p = [X, Y]_{f p}`.

No injectivity, immersivity or submersivity of `f` is assumed. -/
theorem mfderiv_mlieBracket_of_related [SeparatingDual 𝕜 E']
    (hn : minSmoothness 𝕜 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiffAt I J (n : ℕ∞ω) f p)
    (hXrel : ∀ᶠ z in 𝓝 p, mfderiv I J f z (X' z) = X (f z))
    (hYrel : ∀ᶠ z in 𝓝 p, mfderiv I J f z (Y' z) = Y (f z))
    (hX' : ∀ᶠ z in 𝓝 p, ContMDiffAt I I.tangent (n : ℕ∞ω) (T% X') z)
    (hY' : ∀ᶠ z in 𝓝 p, ContMDiffAt I I.tangent (n : ℕ∞ω) (T% Y') z)
    (hX : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent (n : ℕ∞ω) (T% X) q)
    (hY : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent (n : ℕ∞ω) (T% Y) q) :
    mfderiv I J f p (mlieBracket I X' Y' p) = mlieBracket J X Y (f p) :=
  eq_of_forall_mvfderiv_eq (n := (n : ℕ∞ω)) fun _ hh ↦
    mvfderiv_apply_mfderiv_mlieBracket_of_related hn hn' hf hh hXrel hYrel hX' hY' hX hY

/-- **Naturality of the Lie bracket for `f`-related vector fields**, with the relatedness and
regularity hypotheses in global form. -/
theorem mfderiv_mlieBracket_of_related_forall [SeparatingDual 𝕜 E']
    (hn : minSmoothness 𝕜 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J (n : ℕ∞ω) f)
    (hXrel : ∀ z, mfderiv I J f z (X' z) = X (f z))
    (hYrel : ∀ z, mfderiv I J f z (Y' z) = Y (f z))
    (hX' : ContMDiff I I.tangent (n : ℕ∞ω) (T% X'))
    (hY' : ContMDiff I I.tangent (n : ℕ∞ω) (T% Y'))
    (hX : ContMDiff J J.tangent (n : ℕ∞ω) (T% X))
    (hY : ContMDiff J J.tangent (n : ℕ∞ω) (T% Y)) :
    mfderiv I J f p (mlieBracket I X' Y' p) = mlieBracket J X Y (f p) :=
  mfderiv_mlieBracket_of_related hn hn' (hf p)
    (Filter.Eventually.of_forall hXrel) (Filter.Eventually.of_forall hYrel)
    (Filter.Eventually.of_forall fun z ↦ hX' z) (Filter.Eventually.of_forall fun z ↦ hY' z)
    (Filter.Eventually.of_forall fun q ↦ hX q) (Filter.Eventually.of_forall fun q ↦ hY q)

end Related

end RiemannianGeometry
