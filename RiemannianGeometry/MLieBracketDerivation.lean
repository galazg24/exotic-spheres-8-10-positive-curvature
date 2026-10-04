/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# The Lie bracket of vector fields on a manifold acts on functions as a commutator

For vector fields `X`, `Y` on a manifold and a scalar function `g`,

  `X (Y g) - Y (X g) = [X, Y] g`,

where `X g` is the directional derivative `fun y ↦ d% g y (X y)`. This is the statement that
`[X, Y]` is the commutator of `X` and `Y` as derivations of the algebra of functions, and it is the
identity that makes the curvature operator of a connection tensorial in its section argument.

## Main results

* `mdifferentiableAt_mvfderiv_apply` — a directional derivative of a `C²` map along a `C¹` vector
  field is differentiable. Stated for an arbitrary normed target space.
* `contMDiffAt_mvfderiv_apply_of_contMDiffOn` — the same with the smoothness kept: a directional
  derivative of a `C^n` map along a `C^m` vector field is `C^m` when `m + 1 ≤ n`. Needed by the
  Koszul construction, which must produce `C^m` sections rather than merely differentiable ones.
* `mvfderiv_apply_mlieBracket_smul` — the identity, multiplied by an arbitrary vector field. This
  is the form the proof produces.
* `mvfderiv_apply_mlieBracket` — the identity itself.

## Absent from Mathlib

## Proof architecture: no charts

The obvious route is to expand both directional derivatives in a chart and appeal to symmetry of
the second derivative. That route is blocked, and the block is precise: Mathlib has no
`mfderiv_clm_apply` (no product rule for applying a differentiable family of maps on a manifold)
and no intrinsic manifold second-derivative symmetry — every manifold use of
`IsSymmSndFDerivWithinAt` in Mathlib is a hypothesis about a *chart representation*. Worse,
`mfderiv` is defined through `writtenInExtChartAt` at the *base point*, so `fun y ↦ d% g y (Y y)`
in a single chart involves a chart that varies with `y`.

**This proof enters no chart at all.** It uses only the bracket's algebraic laws:

1. Mathlib's product rule `VectorField.mlieBracket_smul_right`,
   `[V, f • W] = (V f) • W + f • [V, W]`, applied at *every* point to give a section identity;
2. Mathlib's Jacobi identity `VectorField.leibniz_identity_mlieBracket_apply`.

Expanding `[X, [Y, g • Z]]` and `[[X, Y], g • Z] + [Y, [X, g • Z]]` by (1) and equating them by (2),
every term cancels — the `(X g) • [Y, Z]` and `(Y g) • [X, Z]` terms pairwise, and the
`g • [X, [Y, Z]]` term against `g • [[X, Y], Z] + g • [Y, [X, Z]]` by a *second* application of the
Jacobi identity, this time to `X`, `Y`, `Z`. What survives is

  `( X(Yg) - Y(Xg) - [X,Y]g ) • Z = 0`

for every `C^n` vector field `Z`, which is `mvfderiv_apply_mlieBracket_smul`.

**Where second-derivative symmetry enters.** Not in this file. It enters inside Mathlib's Jacobi
identity, which is proved by transport to a chart and reduction to
`leibniz_identity_lieBracketWithin` on the model space, where symmetry of the second derivative is
what makes it true. The `minSmoothness 𝕜 2` hypothesis is exactly the device that guarantees it:
`minSmoothness 𝕜 n` is `n` when `𝕜` is `ℝ` or `ℂ` and `ω` otherwise, since only analytic functions
are well behaved over, say, `ℚₚ`. So the chart-level analytic input is inherited, in the form
Mathlib already vouches for, rather than redone here.

## Removing the last factor: choosing `Z`

Passing from `c • Z x = 0` for all `Z` to `c = 0` needs one field with `Z x ≠ 0`, and constructing a
nonvanishing field would mean chart work. It is avoided by a case analysis that needs no new field
at all:

* if `X x ≠ 0`, take `Z := X`;
* else if `Y x ≠ 0`, take `Z := Y`;
* else `X x = 0` and `Y x = 0`, and all three terms of `c` vanish separately —
  the two directional derivatives because they are evaluated at `0`, and `[X, Y] x` by
  `VectorField.mlieBracketWithin_eq_zero_of_eq_zero`.

## Regularity hypotheses

`n : ℕ∞` with `minSmoothness 𝕜 2 ≤ n`, and `g`, `X`, `Y` of class `C^n`. This is deliberately the
same hypothesis shape as Mathlib's own `ContMDiffAt.mlieBracket_vectorField`, on which the proof
depends: because that lemma quantifies over `ℕ∞` rather than `ℕ∞ω`, the hypothesis
`minSmoothness 𝕜 2 ≤ n` is satisfiable exactly when `𝕜` is `ℝ` or `ℂ`, and the statement is vacuous
otherwise. Lifting that restriction means generalising Mathlib's lemma first; recorded rather than
worked around.

`ContMDiff` (global) rather than `ContMDiffAt` is used because the product rule must hold at every
point of a neighbourhood before it can be differentiated again. Localising it — to `ContMDiffOn` on
an open set, or via `ContMDiffAt.eventually` — is a refinement, not a change of mathematics.
-/

noncomputable section

open Bundle Set VectorField
open scoped Manifold ContDiff Topology

namespace RiemannianGeometry

section MVFDerivApply

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {Y : Π x : M, TangentSpace I x} {x : M}

/-- A directional derivative of a `C²` map along a `C¹` vector field is differentiable.

The proof is a composition: `fun y ↦ d% f y (Y y)` is the fibre component of the tangent map of `f`
evaluated on the section `Y`, i.e. `Prod.snd ∘ tangentMap f ∘ T% Y`, and each factor is `C¹` — the
tangent map by `ContMDiff.contMDiff_tangentMap`, the fibre projection of a tangent bundle over a
model space by `contMDiff_snd_tangentBundle_modelSpace`.

This is the ingredient that a naive approach would try to obtain from a nonexistent
`mfderiv_clm_apply`. Note it gives *differentiability only*: no formula for the derivative is
available, and none is needed below. -/
theorem mdifferentiableAt_mvfderiv_apply {n : ℕ∞ω} {f : M → F}
    (hf : ContMDiff I 𝓘(𝕜, F) n f) (hn : 2 ≤ n) (hY : ContMDiff I I.tangent 1 (T% Y)) :
    MDifferentiableAt I 𝓘(𝕜, F) (fun y ↦ d% f y (Y y)) x := by
  have h1 : ContMDiff (ModelWithCorners.tangent 𝓘(𝕜, F)) 𝓘(𝕜, F) 1
      (fun p : TangentBundle 𝓘(𝕜, F) F ↦ p.2) := contMDiff_snd_tangentBundle_modelSpace F 𝓘(𝕜, F)
  have h2 : ContMDiff I.tangent (ModelWithCorners.tangent 𝓘(𝕜, F)) 1
      (tangentMap I 𝓘(𝕜, F) f) := (hf.of_le hn).contMDiff_tangentMap (by norm_num)
  exact ((h1.comp h2).comp hY).mdifferentiableAt one_ne_zero

/-- The localised form of `mdifferentiableAt_mvfderiv_apply`: `f` need only be `C^n` on an open
neighbourhood of `x`.

The global proof composes `ContMDiff.contMDiff_tangentMap` with the fibre projection. Localising it
means using `ContMDiffOn.contMDiffOn_tangentMapWithin` instead — which produces
`tangentMapWithin`, so `mfderivWithin_eq_mfderiv` and `IsOpen.uniqueMDiffWithinAt` are needed to
identify it with `mfderiv` at points of `u`. Still no charts and no new second-derivative theory.
-/
theorem mdifferentiableAt_mvfderiv_apply_of_contMDiffOn {n : ℕ∞ω} {f : M → F} {u : Set M}
    (hu : IsOpen u) (hxu : x ∈ u) (hf : ContMDiffOn I 𝓘(𝕜, F) n f u) (hn : 2 ≤ n)
    (hY : CMDiffAt (1 : ℕ∞ω) (T% Y) x) :
    MDifferentiableAt I 𝓘(𝕜, F) (fun y ↦ d% f y (Y y)) x := by
  have hn0 : n ≠ 0 := by intro h; rw [h] at hn; simp at hn
  have htm := (hf.of_le hn).contMDiffOn_tangentMapWithin (m := 1) (by norm_num) hu.uniqueMDiffOn
  have hmem : (T% Y) x ∈ π E (TangentSpace I) ⁻¹' u := hxu
  have hmaps : MapsTo (T% Y) u (π E (TangentSpace I) ⁻¹' u) := fun y hy ↦ hy
  have h1 : ContMDiffWithinAt I (ModelWithCorners.tangent 𝓘(𝕜, F)) 1
      (fun y ↦ tangentMapWithin I 𝓘(𝕜, F) f u ((T% Y) y)) u x :=
    (htm _ hmem).comp x hY.contMDiffWithinAt hmaps
  have h2 : ContMDiff (ModelWithCorners.tangent 𝓘(𝕜, F)) 𝓘(𝕜, F) 1
      (fun p : TangentBundle 𝓘(𝕜, F) F ↦ p.2) := contMDiff_snd_tangentBundle_modelSpace F 𝓘(𝕜, F)
  have h3 : MDifferentiableAt I 𝓘(𝕜, F)
      (fun y ↦ (tangentMapWithin I 𝓘(𝕜, F) f u ((T% Y) y)).2) x :=
    ((h2.contMDiffAt.comp_contMDiffWithinAt x h1).mdifferentiableWithinAt
      one_ne_zero).mdifferentiableAt (hu.mem_nhds hxu)
  refine h3.congr_of_eventuallyEq ?_
  filter_upwards [hu.mem_nhds hxu] with y hy
  have hfy : MDifferentiableAt I 𝓘(𝕜, F) f y :=
    ((hf y hy).contMDiffAt (hu.mem_nhds hy)).mdifferentiableAt hn0
  simp only [mvfderiv, tangentMapWithin, ContinuousLinearMap.coe_comp, Function.comp_apply,
    mfderivWithin_eq_mfderiv (hu.uniqueMDiffWithinAt hy) hfy]
  rfl

/-- The pointwise form of `mdifferentiableAt_mvfderiv_apply_of_contMDiffOn`: `f` need only be
`C^n` **at** `x`, at a finite order. Convenience wrapper that performs the neighbourhood
extraction. -/
theorem mdifferentiableAt_mvfderiv_apply_of_contMDiffAt {n : ℕ∞ω} {f : M → F} [IsManifold I n M]
    (hf : CMDiffAt n f x) (hn : 2 ≤ n) (hn' : n ≠ ∞)
    (hY : CMDiffAt (1 : ℕ∞ω) (T% Y) x) :
    MDifferentiableAt I 𝓘(𝕜, F) (fun y ↦ d% f y (Y y)) x := by
  obtain ⟨u, hu_nhds, hfu⟩ := (contMDiffAt_iff_contMDiffOn_nhds hn').1 hf
  obtain ⟨v, hv_sub, hv_open, hxv⟩ := mem_nhds_iff.1 hu_nhds
  exact mdifferentiableAt_mvfderiv_apply_of_contMDiffOn hv_open hxv (hfu.mono hv_sub) hn hY

/-- **The `C^m` strengthening**: a directional derivative of a `C^n` map along a `C^m` vector field
is `C^m`, whenever `m + 1 ≤ n`.

Same proof as `mdifferentiableAt_mvfderiv_apply_of_contMDiffOn` with `1` replaced throughout by `m`:
the differentiability version discards smoothness at the last step (`.mdifferentiableWithinAt`), and
simply not discarding it gives this. It is stated separately rather than replacing the
differentiability version because the tensoriality development below needs only the latter, whereas
the Koszul construction needs this one — the Levi-Civita connection has to produce a `C^m` section,
so every term of the Koszul form must be `C^m` and not merely differentiable.

`m + 1 ≤ n` is where the order is genuinely lost: differentiating once costs one degree, and
`ContMDiffOn.contMDiffOn_tangentMapWithin` is stated with exactly that hypothesis. -/
theorem contMDiffAt_mvfderiv_apply_of_contMDiffOn {m n : ℕ∞ω} {f : M → F} {u : Set M}
    (hu : IsOpen u) (hxu : x ∈ u) (hf : ContMDiffOn I 𝓘(𝕜, F) n f u) (hmn : m + 1 ≤ n)
    (hY : CMDiffAt m (T% Y) x) :
    ContMDiffAt I 𝓘(𝕜, F) m (fun y ↦ d% f y (Y y)) x := by
  have hn0 : n ≠ 0 := by
    intro h; rw [h] at hmn; simp at hmn
  have htm := hf.contMDiffOn_tangentMapWithin hmn hu.uniqueMDiffOn
  have hmem : (T% Y) x ∈ π E (TangentSpace I) ⁻¹' u := hxu
  have hmaps : MapsTo (T% Y) u (π E (TangentSpace I) ⁻¹' u) := fun y hy ↦ hy
  have h1 : ContMDiffWithinAt I (ModelWithCorners.tangent 𝓘(𝕜, F)) m
      (fun y ↦ tangentMapWithin I 𝓘(𝕜, F) f u ((T% Y) y)) u x :=
    (htm _ hmem).comp x hY.contMDiffWithinAt hmaps
  have h2 : ContMDiff (ModelWithCorners.tangent 𝓘(𝕜, F)) 𝓘(𝕜, F) m
      (fun p : TangentBundle 𝓘(𝕜, F) F ↦ p.2) := contMDiff_snd_tangentBundle_modelSpace F 𝓘(𝕜, F)
  have h3 : ContMDiffAt I 𝓘(𝕜, F) m
      (fun y ↦ (tangentMapWithin I 𝓘(𝕜, F) f u ((T% Y) y)).2) x :=
    (h2.contMDiffAt.comp_contMDiffWithinAt x h1).contMDiffAt (hu.mem_nhds hxu)
  refine h3.congr_of_eventuallyEq ?_
  filter_upwards [hu.mem_nhds hxu] with y hy
  have hfy : MDifferentiableAt I 𝓘(𝕜, F) f y :=
    ((hf y hy).contMDiffAt (hu.mem_nhds hy)).mdifferentiableAt hn0
  simp only [mvfderiv, tangentMapWithin, ContinuousLinearMap.coe_comp, Function.comp_apply,
    mfderivWithin_eq_mfderiv (hu.uniqueMDiffWithinAt hy) hfy]
  rfl

/-- The pointwise form of `contMDiffAt_mvfderiv_apply_of_contMDiffOn`: `f` need only be `C^n` **at**
`x`, at a finite order. Convenience wrapper that performs the neighbourhood extraction. -/
theorem contMDiffAt_mvfderiv_apply_of_contMDiffAt {m n : ℕ∞ω} {f : M → F} [IsManifold I n M]
    (hf : CMDiffAt n f x) (hmn : m + 1 ≤ n) (hn' : n ≠ ∞) (hY : CMDiffAt m (T% Y) x) :
    ContMDiffAt I 𝓘(𝕜, F) m (fun y ↦ d% f y (Y y)) x := by
  obtain ⟨u, hu_nhds, hfu⟩ := (contMDiffAt_iff_contMDiffOn_nhds hn').1 hf
  obtain ⟨v, hv_sub, hv_open, hxv⟩ := mem_nhds_iff.1 hu_nhds
  exact contMDiffAt_mvfderiv_apply_of_contMDiffOn hv_open hxv (hfu.mono hv_sub) hmn hY

end MVFDerivApply

section Derivation

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞} [IsManifold I 1 M] [IsManifold I (n + 1) M]
  {g : M → 𝕜} {X Y Z : Π x : M, TangentSpace I x} {x : M}

/-- **The derivation identity, multiplied by a vector field.**

`( X(Yg) - Y(Xg) - [X,Y]g ) • Z = 0` for every `C^n` vector field `Z`. This is what the Jacobi
cancellation produces directly; `mvfderiv_apply_mlieBracket` removes the `Z`. See the module
docstring for the architecture. -/
theorem mvfderiv_apply_mlieBracket_smul_aux (hn : minSmoothness 𝕜 2 ≤ n)
    (hgev : ∀ᶠ y in 𝓝 x, MDiffAt g y) (hg2 : CMDiffAt (minSmoothness 𝕜 2) g x)
    (hb : MDiffAt (fun y ↦ d% g y (Y y)) x) (ha : MDiffAt (fun y ↦ d% g y (X y)) x)
    (hX : CMDiffAt (n : ℕ∞ω) (T% X) x) (hY : CMDiffAt (n : ℕ∞ω) (T% Y) x)
    (hZ : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% Z) y) :
    (d% (fun y ↦ d% g y (Y y)) x (X x) - d% (fun y ↦ d% g y (X y)) x (Y x)
      - d% g x (mlieBracket I X Y x)) • Z x = 0 := by
  have h2n : (2 : ℕ∞ω) ≤ (n : ℕ∞ω) := le_minSmoothness.trans hn
  have hne : (n : ℕ∞ω) ≠ 0 := by
    intro h; rw [h] at h2n; simp at h2n
  have h1n : (1 : ℕ∞ω) ≤ (n : ℕ∞ω) := le_trans (by norm_num) h2n
  -- The Jacobi identity is stated for manifolds of class `minSmoothness 𝕜 3`.
  have : IsManifold I (minSmoothness 𝕜 3) M := by
    apply IsManifold.of_le (n := (n : ℕ∞ω) + 1)
    calc minSmoothness 𝕜 3 = minSmoothness 𝕜 2 + 1 := by
          rw [show (3 : ℕ∞ω) = 2 + 1 by norm_num, minSmoothness_add]
      _ ≤ (n : ℕ∞ω) + 1 := by gcongr
  -- Differentiability of everything the product rules are applied to.
  have hgd : MDiffAt g x := hgev.self_of_nhds
  have hZev : ∀ᶠ y in 𝓝 x, MDiffAt (T% Z) y := hZ.mono fun _ h ↦ h.mdifferentiableAt hne
  have hZd : MDiffAt (T% Z) x := hZev.self_of_nhds
  have hYZ : MDiffAt (T% (mlieBracket I Y Z)) x :=
    (hY.mlieBracket_vectorField (m := 1) hZ.self_of_nhds hn).mdifferentiableAt one_ne_zero
  have hXZ : MDiffAt (T% (mlieBracket I X Z)) x :=
    (hX.mlieBracket_vectorField (m := 1) hZ.self_of_nhds hn).mdifferentiableAt one_ne_zero
  have hbZ : MDiffAt (T% ((fun y ↦ d% g y (Y y)) • Z)) x := hb.smul_section hZd
  have haZ : MDiffAt (T% ((fun y ↦ d% g y (X y)) • Z)) x := ha.smul_section hZd
  have hgYZ : MDiffAt (T% (g • mlieBracket I Y Z)) x := hgd.smul_section hYZ
  have hgXZ : MDiffAt (T% (g • mlieBracket I X Z)) x := hgd.smul_section hXZ
  -- The product rule holds only *near* `x`, and that is enough: the outer bracket sees only the
  -- germ of its second argument, by `EventuallyEq.mlieBracket_vectorField_eq`.
  have E1 : mlieBracket I X (mlieBracket I Y (g • Z)) x
      = mlieBracket I X ((fun y ↦ d% g y (Y y)) • Z + g • mlieBracket I Y Z) x := by
    refine Filter.EventuallyEq.mlieBracket_vectorField_eq .rfl ?_
    filter_upwards [hgev, hZev] with y hgy hZy
    exact mlieBracket_smul_right (V := Y) hgy hZy
  have E2 : mlieBracket I Y (mlieBracket I X (g • Z)) x
      = mlieBracket I Y ((fun y ↦ d% g y (X y)) • Z + g • mlieBracket I X Z) x := by
    refine Filter.EventuallyEq.mlieBracket_vectorField_eq .rfl ?_
    filter_upwards [hgev, hZev] with y hgy hZy
    exact mlieBracket_smul_right (V := X) hgy hZy
  -- The two nested expansions, and the outer bracket with `[X, Y]`.
  have L : mlieBracket I X (mlieBracket I Y (g • Z)) x
      = d% (fun y ↦ d% g y (Y y)) x (X x) • Z x
        + d% g x (Y x) • mlieBracket I X Z x
        + (d% g x (X x) • mlieBracket I Y Z x
        + g x • mlieBracket I X (mlieBracket I Y Z) x) := by
    rw [E1, mlieBracket_add_right hbZ hgYZ,
      mlieBracket_smul_right hb hZd, mlieBracket_smul_right hgd hYZ]
  have R : mlieBracket I Y (mlieBracket I X (g • Z)) x
      = d% (fun y ↦ d% g y (X y)) x (Y x) • Z x
        + d% g x (X x) • mlieBracket I Y Z x
        + (d% g x (Y x) • mlieBracket I X Z x
        + g x • mlieBracket I Y (mlieBracket I X Z) x) := by
    rw [E2, mlieBracket_add_right haZ hgXZ,
      mlieBracket_smul_right ha hZd, mlieBracket_smul_right hgd hXZ]
  have B : mlieBracket I (mlieBracket I X Y) (g • Z) x
      = d% g x (mlieBracket I X Y x) • Z x
        + g x • mlieBracket I (mlieBracket I X Y) Z x :=
    mlieBracket_smul_right hgd hZd
  -- Jacobi, twice: once for `X, Y, g • Z`, once for `X, Y, Z`.
  have hX2 : CMDiffAt (minSmoothness 𝕜 2) (T% X) x := hX.of_le hn
  have hY2 : CMDiffAt (minSmoothness 𝕜 2) (T% Y) x := hY.of_le hn
  have hZ2 : CMDiffAt (minSmoothness 𝕜 2) (T% Z) x := hZ.self_of_nhds.of_le hn
  have hgZ2 : CMDiffAt (minSmoothness 𝕜 2) (T% (g • Z)) x := ContMDiffAt.smul_section hg2 hZ2
  have J2 := leibniz_identity_mlieBracket_apply (I := I) hX2 hY2 hZ2
  have J1 := leibniz_identity_mlieBracket_apply (I := I) hX2 hY2 hgZ2
  rw [L, B, R, J2, smul_add] at J1
  have h := sub_eq_zero_of_eq J1
  rw [sub_smul, sub_smul]
  abel_nf at h ⊢
  exact h


/-- **The derivation identity, multiplied by a vector field**, from global smoothness of `g`. -/
theorem mvfderiv_apply_mlieBracket_smul (hn : minSmoothness 𝕜 2 ≤ n)
    (hg : ContMDiff I 𝓘(𝕜, 𝕜) n g)
    (hX : ContMDiff I I.tangent n (T% X)) (hY : ContMDiff I I.tangent n (T% Y))
    (hZ : ContMDiff I I.tangent n (T% Z)) :
    (d% (fun y ↦ d% g y (Y y)) x (X x) - d% (fun y ↦ d% g y (X y)) x (Y x)
      - d% g x (mlieBracket I X Y x)) • Z x = 0 := by
  have h2n : (2 : ℕ∞ω) ≤ (n : ℕ∞ω) := le_minSmoothness.trans hn
  have hne : (n : ℕ∞ω) ≠ 0 := by intro h; rw [h] at h2n; simp at h2n
  have h1n : (1 : ℕ∞ω) ≤ (n : ℕ∞ω) := le_trans (by norm_num) h2n
  exact mvfderiv_apply_mlieBracket_smul_aux hn
    (Filter.Eventually.of_forall fun y ↦ hg.mdifferentiableAt hne) ((hg x).of_le hn)
    (mdifferentiableAt_mvfderiv_apply hg h2n (hY.of_le h1n))
    (mdifferentiableAt_mvfderiv_apply hg h2n (hX.of_le h1n)) (hX x) (hY x)
    (Filter.Eventually.of_forall fun y ↦ hZ y)

/-- **The localised form**: `g` need only be `C^n` at `x`, at a finite order `n`.

The finiteness is what `contMDiffAt_iff_contMDiffOn_nhds` costs; a caller with a `C^∞` function
applies this at any finite order. This is the version the bundled curvature tensor needs, because
the local-frame coefficient functions that appear there are defined only near `x`. -/
theorem mvfderiv_apply_mlieBracket_smul_of_contMDiffAt (hn : minSmoothness 𝕜 2 ≤ n)
    (hn' : (n : ℕ∞ω) ≠ ∞) (hg : CMDiffAt (n : ℕ∞ω) g x)
    (hX : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% X) y)
    (hY : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% Y) y)
    (hZ : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% Z) y) :
    (d% (fun y ↦ d% g y (Y y)) x (X x) - d% (fun y ↦ d% g y (X y)) x (Y x)
      - d% g x (mlieBracket I X Y x)) • Z x = 0 := by
  have h2n : (2 : ℕ∞ω) ≤ (n : ℕ∞ω) := le_minSmoothness.trans hn
  have hne : (n : ℕ∞ω) ≠ 0 := by intro h; rw [h] at h2n; simp at h2n
  have h1n : (1 : ℕ∞ω) ≤ (n : ℕ∞ω) := le_trans (by norm_num) h2n
  have : IsManifold I (n : ℕ∞ω) M := IsManifold.of_le (n := (n : ℕ∞ω) + 1) le_self_add
  exact mvfderiv_apply_mlieBracket_smul_aux hn
    (((contMDiffAt_iff_contMDiffAt_nhds hn').1 hg).mono fun _ h ↦ h.mdifferentiableAt hne)
    (hg.of_le hn)
    (mdifferentiableAt_mvfderiv_apply_of_contMDiffAt hg h2n hn' (hY.self_of_nhds.of_le h1n))
    (mdifferentiableAt_mvfderiv_apply_of_contMDiffAt hg h2n hn' (hX.self_of_nhds.of_le h1n))
    hX.self_of_nhds hY.self_of_nhds hZ

/-- **The Lie bracket acts on functions as the commutator of directional derivatives.**

`X (Y g) - Y (X g) = [X, Y] g`, where `X g` is `fun y ↦ d% g y (X y)`.

Obtained from `mvfderiv_apply_mlieBracket_smul` by taking `Z := X` or `Z := Y`, whichever is nonzero
at `x`; if both vanish at `x` then all three terms vanish separately. No nonvanishing vector field
has to be constructed, and no chart is used. -/
theorem mvfderiv_apply_mlieBracket (hn : minSmoothness 𝕜 2 ≤ n)
    (hg : ContMDiff I 𝓘(𝕜, 𝕜) n g)
    (hX : ContMDiff I I.tangent n (T% X)) (hY : ContMDiff I I.tangent n (T% Y)) :
    d% (fun y ↦ d% g y (Y y)) x (X x) - d% (fun y ↦ d% g y (X y)) x (Y x)
      = d% g x (mlieBracket I X Y x) := by
  refine sub_eq_zero.mp ?_
  by_cases hX0 : X x = 0
  · by_cases hY0 : Y x = 0
    · have hbr : mlieBracket I X Y x = 0 := by
        rw [← mlieBracketWithin_univ]
        exact mlieBracketWithin_eq_zero_of_eq_zero hX0 hY0
      rw [hX0, hY0, hbr, map_zero, map_zero, map_zero, sub_zero, sub_zero]
    · exact (smul_eq_zero.mp (mvfderiv_apply_mlieBracket_smul hn hg hX hY hY)).resolve_right hY0
  · exact (smul_eq_zero.mp (mvfderiv_apply_mlieBracket_smul hn hg hX hY hX)).resolve_right hX0

/-- **The localised form of the derivation identity**: `g` need only be `C^n` at `x`, at a finite
order. Same case analysis as the global version. -/
theorem mvfderiv_apply_mlieBracket_of_contMDiffAt (hn : minSmoothness 𝕜 2 ≤ n)
    (hn' : (n : ℕ∞ω) ≠ ∞) (hg : CMDiffAt (n : ℕ∞ω) g x)
    (hX : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% X) y)
    (hY : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% Y) y) :
    d% (fun y ↦ d% g y (Y y)) x (X x) - d% (fun y ↦ d% g y (X y)) x (Y x)
      = d% g x (mlieBracket I X Y x) := by
  refine sub_eq_zero.mp ?_
  by_cases hX0 : X x = 0
  · by_cases hY0 : Y x = 0
    · have hbr : mlieBracket I X Y x = 0 := by
        rw [← mlieBracketWithin_univ]
        exact mlieBracketWithin_eq_zero_of_eq_zero hX0 hY0
      rw [hX0, hY0, hbr, map_zero, map_zero, map_zero, sub_zero, sub_zero]
    · exact (smul_eq_zero.mp
        (mvfderiv_apply_mlieBracket_smul_of_contMDiffAt hn hn' hg hX hY hY)).resolve_right hY0
  · exact (smul_eq_zero.mp
      (mvfderiv_apply_mlieBracket_smul_of_contMDiffAt hn hn' hg hX hY hX)).resolve_right hX0

end Derivation

end RiemannianGeometry
