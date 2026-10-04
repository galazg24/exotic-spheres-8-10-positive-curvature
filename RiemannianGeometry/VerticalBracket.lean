/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import RiemannianGeometry.HorizontalLift

/-!
# Vertical vector fields and the Lie bracket

A vector field `V` on the total space of a submersion `f : M → B` is **vertical** when
`V z ∈ ker (df_z)` for every `z` (`IsVerticalField` of `RiemannianGeometry.HorizontalLift`). Unwinding
`verticalSpace` shows that this says exactly that `V` is `f`-**related to the zero vector field**
on `B`. O'Neill uses precisely this observation once, in the proof of his Lemma 2 — "But `[V, X]`
`= ∇_V X - ∇_X V` is vertical (since `V` is `π`-related to the zero vector field)", with `X`
*basic* — and it is the whole content of this file.

Because `[0, 0] = 0` and `[0, Y] = 0` on the base, bracket naturality for `f`-related fields
(`mfderiv_mlieBracket_of_related` of `RiemannianGeometry.RelatedVectorFields`) gives at once:

* the bracket of two vertical fields is vertical;
* the bracket of a vertical field with a **basic** field — a horizontal lift `Yᴴ` — is vertical.

## Main results

* `contMDiff_zeroVectorField`, `contMDiffAt_zeroVectorField` — the zero section of `TB` is `C^m`,
  in the `T%` spelling that `mfderiv_mlieBracket_of_related` consumes.
* `isVerticalField_iff_mfderiv_eq_zero`, `mfderiv_eq_zero_of_isVerticalField` — the bridge:
  vertical means `f`-related to zero.
* `mem_verticalSpace_mlieBracket_of_mfderiv_eq_zero`, `mem_verticalSpace_mlieBracket`,
  `isVerticalField_mlieBracket` — **the bracket of two vertical fields is vertical**, pointwise
  and as fields.
* `mem_verticalSpace_mlieBracket_of_related` — **the bracket of a vertical field with any
  `f`-related field is vertical**. This is the honest core of the next two statements; see
  "Relatedness, not horizontality" below.
* `mem_verticalSpace_mlieBracket_horizontalLiftField`,
  `mem_verticalSpace_horizontalLiftField_mlieBracket` — **the bracket of a vertical field with a
  horizontal lift is vertical**, in both orders. This is the step O'Neill's Lemma 2 uses.

## What Mathlib already has

`VectorField.mlieBracket_zero_left : mlieBracket I 0 W = 0` and
`VectorField.mlieBracket_zero_right : mlieBracket I W 0 = 0` are already in
`Mathlib/Geometry/Manifold/VectorField/LieBracket.lean`, as `@[simp]` lemmas, together with their
`mlieBracketWithin` forms. They hold **unconditionally**, with no differentiability hypothesis,
because `mlieBracket` takes the junk value `0` off the differentiable locus. Nothing about the
zero cases of the bracket is reproved here. Likewise `Bundle.contMDiff_zeroSection` supplies the
regularity of the zero section, and `VectorField.mlieBracket_swap_apply` — also unconditional —
supplies the antisymmetry used for the second order of the mixed bracket.

The one thing that does need saying is the *spelling*: the hypotheses of
`mfderiv_mlieBracket_of_related` are about `T% X` for a dependent section `X`, and Mathlib's
`Bundle.zeroSection E' (TangentSpace J)` is a non-dependent function into the total space. The two
agree definitionally, and `contMDiff_zeroVectorField` records this once. Both candidate spellings
of the zero field, `fun q ↦ (0 : TangentSpace J q)` and `(0 : Π q : B, TangentSpace J q)`,
elaborate equally well and are accepted by `contMDiff_zeroSection` without any bridging lemma; the
second is used throughout, because it is the form in which `mlieBracket_zero_left` and
`mlieBracket_zero_right` are stated and so needs no `Pi.zero_apply` rewriting at the point of use.

## Hypotheses, and what is *not* assumed

The two vertical statements are not symmetric in their needs, and the difference is worth
recording.

* For two vertical fields, **no submersion hypothesis of any kind is used** — not
  `IsSubmersionAtPoint`, not `IsRiemannianSubmersionAtPoint`, not even at `p`, and no metric on
  the base. The vertical space is `ker (df)` whatever `df` does, `[0, 0] = 0` needs nothing, and
  bracket naturality is proved in `RiemannianGeometry.RelatedVectorFields` with no hypothesis on `f`
  beyond regularity. The statement is therefore about an arbitrary `C^n` map.
* For a vertical field against a horizontal lift, `IsSubmersionAtPoint` and
  `IsRiemannianSubmersionAtPoint` are needed in the **eventual** form `∀ᶠ z in 𝓝 p, …`, and not
  merely at `p`: they are used only through `mfderiv_horizontalLiftField`, but
  `mfderiv_mlieBracket_of_related` consumes relatedness on a whole neighbourhood, a bracket being
  a first-order object in the fields. This matches the form the hypotheses already take in
  `RiemannianGeometry.HorizontalLift`.

In both cases `f` itself must be `C^n` at `p`, and the fields `C^n` near `p`; verticality alone
never suffices, because `mlieBracket` differentiates its arguments.

## Relatedness, not horizontality

`mem_verticalSpace_mlieBracket_horizontalLiftField` is stated for the lift `Yᴴ` specifically, and
it is **false** for a general horizontal field. The smallest example: take `M = ℝ²`, `B = ℝ`,
`f (x, y) = x`, so that `∂/∂y` is vertical and `∂/∂x` horizontal. Then `V := ∂/∂y` is vertical and
`Z := a(x, y) ∂/∂x` is horizontal for every `a`, and `[V, Z] = (∂a/∂y) ∂/∂x`, which is horizontal
and non-zero as soon as `a` genuinely depends on `y`.

What rules this out for `Yᴴ` is, however, **not** its horizontality. The proof below goes through
`mem_verticalSpace_mlieBracket_of_related`, whose hypothesis on the second field is only that it
be `f`-related to *some* field `Y` on the base; horizontality is never used, and `Yᴴ` enters solely
through `mfderiv_horizontalLiftField`. The counterexample is consistent with this: `a(x, y) ∂/∂x`
is `f`-related to nothing unless `∂a/∂y = 0`, since `dπ_z (Z z) = a(x, y)` must factor through
`f`. Indeed a horizontal field that *is* `f`-related to `Y` is forced to be `Yᴴ`, by
`eq_horizontalLiftField`, so "horizontal and basic" and "a lift" name the same fields and there is
nothing to reconcile.

## Regularity accounting

Nothing here differentiates anything: every statement is `mfderiv_mlieBracket_of_related` fed with
`mem_verticalSpace_iff` and, for the mixed bracket, `mfderiv_horizontalLiftField`. The order `n`
is kept variable under the hypotheses `minSmoothness ℝ 2 ≤ n` and `(n : ℕ∞ω) ≠ ∞` inherited from
that theorem, exactly as in `RiemannianGeometry.HorizontalLift`; the `IsManifold` premises at orders `1`
and `n + 1`, and `CompleteSpace E`, `CompleteSpace E'`, `SeparatingDual ℝ E'`, are found by
instance search from the ambient block. The regularity of `Yᴴ` is taken as a hypothesis rather
than rederived from `contMDiffAt_horizontalLiftField`, so that a caller who already has it is not
forced through the metric hypotheses of that theorem.
-/

noncomputable section

open Bundle VectorField
open scoped Manifold ContDiff Topology

namespace RiemannianGeometry

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {B : Type*} [TopologicalSpace B] [ChartedSpace H' B] [IsManifold J ∞ B]
  [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]
  {f : M → B}

/-! ## The zero vector field on the base

Mathlib already has everything about the *bracket* of the zero field (`mlieBracket_zero_left`,
`mlieBracket_zero_right`); what is recorded here is only its regularity, in the `T%` spelling. -/

omit [FiniteDimensional ℝ E'] in
variable (J B) in
/-- **The zero vector field on `B` is `C^m`**, at every order and with no hypothesis, as a section
of the tangent bundle. This is `Bundle.contMDiff_zeroSection`:
`T% (0 : Π q : B, TangentSpace J q)` is `Bundle.zeroSection E' (TangentSpace J)`, definitionally.
-/
theorem contMDiff_zeroVectorField {m : ℕ∞ω} :
    ContMDiff J J.tangent m (T% (0 : Π q : B, TangentSpace J q)) :=
  contMDiff_zeroSection ℝ (TangentSpace J)

omit [FiniteDimensional ℝ E'] in
variable (J B) in
/-- **The zero vector field on `B` is `C^m` at every point.** The pointwise form of
`contMDiff_zeroVectorField`, which is what `mfderiv_mlieBracket_of_related` asks for. -/
theorem contMDiffAt_zeroVectorField {m : ℕ∞ω} (q : B) :
    ContMDiffAt J J.tangent m (T% (0 : Π q : B, TangentSpace J q)) q :=
  contMDiff_zeroVectorField J B q

/-! ## Vertical fields are exactly the fields `f`-related to zero -/

variable {V W : Π z : M, TangentSpace I z}

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B]
  [Bundle.RiemannianBundle (TangentSpace I : M → Type _)] in
/-- **A field is vertical iff it is `f`-related to the zero field**: `IsVerticalField I J f V` iff
`dπ_z (V z) = 0` for every `z`. This is `mem_verticalSpace_iff` repackaged, and it is the bridge
every statement below crosses. -/
theorem isVerticalField_iff_mfderiv_eq_zero :
    IsVerticalField I J f V ↔ ∀ z, mfderiv I J f z (V z) = 0 :=
  forall_congr' fun _ ↦ mem_verticalSpace_iff

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B]
  [Bundle.RiemannianBundle (TangentSpace I : M → Type _)] in
/-- The pointwise half of `isVerticalField_iff_mfderiv_eq_zero`. -/
theorem mfderiv_eq_zero_of_isVerticalField (hV : IsVerticalField I J f V) (z : M) :
    mfderiv I J f z (V z) = 0 :=
  mem_verticalSpace_iff.mp (hV z)

/-! ## The bracket of two vertical fields

No submersion hypothesis appears in this section: `f` is an arbitrary `C^n` map. -/

omit [Bundle.RiemannianBundle (TangentSpace I : M → Type _)] in
/-- **The bracket of two vertical fields is vertical**, in the weakest form: relatedness to zero
and regularity are both assumed only near `p`.

`V` and `W` are `f`-related to the zero field on `B`, so `mfderiv_mlieBracket_of_related` makes
`[V, W]` `f`-related to `[0, 0] = 0` at `p`, which is membership in `ker (dπ_p)`. Nothing about
`f` beyond `ContMDiffAt I J n f p` is used — in particular `f` is not assumed to be a submersion
anywhere, not even at `p`. -/
theorem mem_verticalSpace_mlieBracket_of_mfderiv_eq_zero {n : ℕ∞} {p : M}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiffAt I J ((n : ℕ∞ω)) f p)
    (hV : ∀ᶠ z in 𝓝 p, mfderiv I J f z (V z) = 0)
    (hW : ∀ᶠ z in 𝓝 p, mfderiv I J f z (W z) = 0)
    (hV' : ∀ᶠ z in 𝓝 p, ContMDiffAt I I.tangent ((n : ℕ∞ω)) (T% V) z)
    (hW' : ∀ᶠ z in 𝓝 p, ContMDiffAt I I.tangent ((n : ℕ∞ω)) (T% W) z) :
    mlieBracket I V W p ∈ verticalSpace I J f p := by
  rw [mem_verticalSpace_iff,
    mfderiv_mlieBracket_of_related (X := (0 : Π q : B, TangentSpace J q))
      (Y := (0 : Π q : B, TangentSpace J q)) hn hn' hf hV hW hV' hW'
      (Filter.Eventually.of_forall fun q ↦ contMDiffAt_zeroVectorField J B q)
      (Filter.Eventually.of_forall fun q ↦ contMDiffAt_zeroVectorField J B q)]
  simp

omit [Bundle.RiemannianBundle (TangentSpace I : M → Type _)] in
/-- **The bracket of two vertical fields is vertical**, with verticality in the global form
`IsVerticalField` and regularity near `p`. -/
theorem mem_verticalSpace_mlieBracket {n : ℕ∞} {p : M}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiffAt I J ((n : ℕ∞ω)) f p)
    (hV : IsVerticalField I J f V) (hW : IsVerticalField I J f W)
    (hV' : ∀ᶠ z in 𝓝 p, ContMDiffAt I I.tangent ((n : ℕ∞ω)) (T% V) z)
    (hW' : ∀ᶠ z in 𝓝 p, ContMDiffAt I I.tangent ((n : ℕ∞ω)) (T% W) z) :
    mlieBracket I V W p ∈ verticalSpace I J f p :=
  mem_verticalSpace_mlieBracket_of_mfderiv_eq_zero hn hn' hf
    (Filter.Eventually.of_forall (mfderiv_eq_zero_of_isVerticalField hV))
    (Filter.Eventually.of_forall (mfderiv_eq_zero_of_isVerticalField hW)) hV' hW'

omit [Bundle.RiemannianBundle (TangentSpace I : M → Type _)] in
/-- **The vertical fields are closed under the Lie bracket**, as a statement about fields: if `V`
and `W` are vertical and `C^n`, then `[V, W]` is vertical. This is the Lie-subalgebra-flavoured
form of `mem_verticalSpace_mlieBracket`; no Lie algebra structure is built here, and none is needed
for O'Neill's Lemma 2. -/
theorem isVerticalField_mlieBracket {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n : ℕ∞ω)) f)
    (hV : IsVerticalField I J f V) (hW : IsVerticalField I J f W)
    (hV' : ContMDiff I I.tangent ((n : ℕ∞ω)) (T% V))
    (hW' : ContMDiff I I.tangent ((n : ℕ∞ω)) (T% W)) :
    IsVerticalField I J f (mlieBracket I V W) := fun p ↦
  mem_verticalSpace_mlieBracket hn hn' (hf p) hV hW
    (Filter.Eventually.of_forall fun z ↦ hV' z) (Filter.Eventually.of_forall fun z ↦ hW' z)

/-! ## The bracket of a vertical field with an `f`-related field

The core of O'Neill's step, before any metric is chosen: what makes `[V, Z]` vertical is that `Z`
is `f`-related to something, not that `Z` is horizontal. -/

omit [Bundle.RiemannianBundle (TangentSpace I : M → Type _)] in
/-- **The bracket of a vertical field with an `f`-related field is vertical.**

`V` is `f`-related to `0` and `Z` is `f`-related to `Y`, so `[V, Z]` is `f`-related to
`[0, Y] = 0`. No metric on either manifold, no horizontality of `Z`, and no submersion condition
on `f` are used; see "Relatedness, not horizontality" in the module docstring. -/
theorem mem_verticalSpace_mlieBracket_of_related {n : ℕ∞} {p : M}
    {Y : Π q : B, TangentSpace J q} {Z : Π z : M, TangentSpace I z}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiffAt I J ((n : ℕ∞ω)) f p)
    (hV : ∀ᶠ z in 𝓝 p, mfderiv I J f z (V z) = 0)
    (hZrel : ∀ᶠ z in 𝓝 p, mfderiv I J f z (Z z) = Y (f z))
    (hV' : ∀ᶠ z in 𝓝 p, ContMDiffAt I I.tangent ((n : ℕ∞ω)) (T% V) z)
    (hZ' : ∀ᶠ z in 𝓝 p, ContMDiffAt I I.tangent ((n : ℕ∞ω)) (T% Z) z)
    (hY : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q) :
    mlieBracket I V Z p ∈ verticalSpace I J f p := by
  rw [mem_verticalSpace_iff,
    mfderiv_mlieBracket_of_related (X := (0 : Π q : B, TangentSpace J q)) (Y := Y) hn hn' hf
      hV hZrel hV' hZ'
      (Filter.Eventually.of_forall fun q ↦ contMDiffAt_zeroVectorField J B q) hY]
  simp

/-! ## The bracket of a vertical field with a horizontal lift

This is the step O'Neill's Lemma 2 uses. The metric on the base enters, because
`horizontalLiftField` is defined through the fibrewise metric adjoint. -/

section Base

variable [Bundle.RiemannianBundle (TangentSpace J : B → Type _)]

/-- **O'Neill's step: `[V, Yᴴ]` is vertical for `V` vertical and `Yᴴ` a horizontal lift.**

`mem_verticalSpace_mlieBracket_of_related` applied to `Z := Yᴴ`, whose relatedness to `Y` is
`mfderiv_horizontalLiftField`.

The submersion and Riemannian hypotheses are needed in the **eventual** form, not merely at `p`:
they are consumed only through `mfderiv_horizontalLiftField`, but
`mfderiv_mlieBracket_of_related` needs the relatedness of `Yᴴ` on a whole neighbourhood of `p`.
Only eventual verticality of `V` is used, although the global `IsVerticalField` is what is asked
for here.

Stated for `horizontalLiftField` — O'Neill's *basic* field — and not for an arbitrary horizontal
field, for which it is false; see the module docstring. -/
theorem mem_verticalSpace_mlieBracket_horizontalLiftField {n : ℕ∞} {p : M}
    {Y : Π q : B, TangentSpace J q}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiffAt I J ((n : ℕ∞ω)) f p)
    (hsub : ∀ᶠ z in 𝓝 p, IsSubmersionAtPoint I J f z)
    (hriem : ∀ᶠ z in 𝓝 p, IsRiemannianSubmersionAtPoint I J f z)
    (hV : IsVerticalField I J f V)
    (hV' : ∀ᶠ z in 𝓝 p, ContMDiffAt I I.tangent ((n : ℕ∞ω)) (T% V) z)
    (hYH : ∀ᶠ z in 𝓝 p,
      ContMDiffAt I I.tangent ((n : ℕ∞ω)) (T% (horizontalLiftField I J f Y)) z)
    (hY : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q) :
    mlieBracket I V (horizontalLiftField I J f Y) p ∈ verticalSpace I J f p := by
  have hYrel : ∀ᶠ z in 𝓝 p,
      mfderiv I J f z (horizontalLiftField I J f Y z) = Y (f z) := by
    filter_upwards [hsub, hriem] with z hz hz' using mfderiv_horizontalLiftField hz hz'
  exact mem_verticalSpace_mlieBracket_of_related hn hn' hf
    (Filter.Eventually.of_forall (mfderiv_eq_zero_of_isVerticalField hV)) hYrel hV' hYH hY

/-- **The same bracket in the other order**, `[Yᴴ, V]`. Immediate from
`mem_verticalSpace_mlieBracket_horizontalLiftField` and the unconditional antisymmetry
`mlieBracket_swap_apply`, since a submodule is closed under negation. -/
theorem mem_verticalSpace_horizontalLiftField_mlieBracket {n : ℕ∞} {p : M}
    {Y : Π q : B, TangentSpace J q}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiffAt I J ((n : ℕ∞ω)) f p)
    (hsub : ∀ᶠ z in 𝓝 p, IsSubmersionAtPoint I J f z)
    (hriem : ∀ᶠ z in 𝓝 p, IsRiemannianSubmersionAtPoint I J f z)
    (hV : IsVerticalField I J f V)
    (hV' : ∀ᶠ z in 𝓝 p, ContMDiffAt I I.tangent ((n : ℕ∞ω)) (T% V) z)
    (hYH : ∀ᶠ z in 𝓝 p,
      ContMDiffAt I I.tangent ((n : ℕ∞ω)) (T% (horizontalLiftField I J f Y)) z)
    (hY : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q) :
    mlieBracket I (horizontalLiftField I J f Y) V p ∈ verticalSpace I J f p := by
  rw [mlieBracket_swap_apply]
  exact Submodule.neg_mem _
    (mem_verticalSpace_mlieBracket_horizontalLiftField hn hn' hf hsub hriem hV hV' hYH hY)

end Base

end RiemannianGeometry
