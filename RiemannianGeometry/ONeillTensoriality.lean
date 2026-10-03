/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import RiemannianGeometry.ONeillLemmaTwo

/-!
# Field-slot tensoriality of O'Neill's tensors `T` and `A`

O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. **13** (1966) 459–469,
asserts on p. 460 — without proof — that

    T_D F = 𝓗∇_{𝓥D}(𝓥F) + 𝓥∇_{𝓥D}(𝓗F),    A_D F = 𝓥∇_{𝓗D}(𝓗F) + 𝓗∇_{𝓗D}(𝓥F)

are `(1,2)`-tensors. `Foundations.ONeillTensors` proves the *direction*-slot half
(`oneillA_congr_direction`, `oneillA_add_direction`, `oneillA_smul_direction` and their `T`
analogues), where the direction enters only as the argument of a continuous linear map precomposed
with a projection. This file proves the *field*-slot half, and draws the consequence O'Neill
actually uses.

## Why it is true: the Leibniz correction lands in the complementary summand

By the Leibniz rule (`leviCivita_smul_section`),

    ∇_X (c • F) x = c x • ∇_X F x + (d% c x).smulRight (F x)

For the first summand of `A`: `𝓗(c • F) = c • 𝓗F`, so the correction contributed at the direction
`w = 𝓗_p(D p)` is `(d% c p w) • 𝓗F p`, which is **horizontal**, and the outer projection of that
summand is `𝓥`. Since `𝓥 ∘ 𝓗 = 0` the correction dies. In the second summand the correction is
vertical and the outer projection is `𝓗`, and `𝓗 ∘ 𝓥 = 0` kills it there.

**That is the whole reason `A` and `T` are tensors**, and it is why the three projections in each
summand cannot be collapsed: collapsing the inner field projection into the outer one would leave
the Leibniz correction alive.

## Main results

* `verticalProjection_horizontalProjection`, `horizontalProjection_verticalProjection` — the two
  composition identities `𝓥 ∘ 𝓗 = 0` and `𝓗 ∘ 𝓥 = 0`, which `Foundations.HorizontalSpace` has
  only in the membership form. These are the load-bearing algebraic facts of the file.
* `oneillA_add_field`, `oneillA_smul_field`, `oneillT_add_field`, `oneillT_smul_field` —
  **field-slot additivity and homogeneity**: the two clauses of O'Neill's tensoriality assertion in
  the field slot.
* `oneillA_eq_of_eq_at`, `oneillT_eq_of_eq_at` — **`A_D F p` and `T_D F p` depend only on `F p`**,
  the consequence O'Neill actually uses.
* `oneillA_self_eq_zero` — `A_X X = 0` for an **arbitrary** horizontal field.
* `oneillA_swap_neg` — **O'Neill's property 3′** for arbitrary horizontal fields.
* `oneillA_eq_two_inv_smul_verticalProjection_mlieBracket` — **O'Neill's Lemma 2** for arbitrary
  horizontal fields.

## The route to order zero: skew-symmetry, not a local frame

`Foundations.CurvaturePointwise.curvature_eq_of_eq_at` reaches the analogous order-zero statement
for the curvature operator through a **local-frame expansion**: additivity plus homogeneity plus
germ locality plus `Trivialization.localFrameCoeff_congr`. That machinery is *not* used here, and
is not needed.

The reason is that `A` and `T` carry something curvature does not: O'Neill's properties 1 and 1′,
skew-symmetry, already proved as `tangentMetric_oneillA_skew` and `tangentMetric_oneillT_skew`. For
any `w ∈ T_pM`, pick any field `G` with `G p = w` whose two projections are differentiable at `p`;
then

    ⟪A_D F p, w⟫ = ⟪A_D F p, G p⟫ = −⟪A_D G p, F p⟫,

and the right-hand side depends on `F` only through `F p`. Nondegeneracy of the metric
(`isNondegenerate_tangentMetric`, through `eq_of_g_eq`) turns that into the order-zero statement.
So `oneillA_eq_of_eq_at` is **three lines**, needs no frame, no germ argument, no bump function and
no `ContMDiffVectorBundle` instance — and, notably, does not even use the additivity and
homogeneity above. The two are recorded independently: `oneillA_add_field` and `oneillA_smul_field`
are the tensoriality statement, `oneillA_eq_of_eq_at` is the consequence, and here the consequence
happens to have the shorter proof.

The supply of test fields is `exists_mdiffAt_parts_eq`: `FiberBundle.extend E w` has the prescribed
value at `p` and is `C^m` at `p` at every order, and `contMDiffAt_horizontalPart`,
`contMDiffAt_verticalPart` project that at the price of their submersion and metric-regularity
hypotheses. It is taken as a hypothesis of `oneillA_eq_of_eq_at` rather than built into it, so that
the order-zero statement is charged only for what it uses.

## O'Neill's reduction to basic fields, completed

1. `oneillA_self_eq_zero`: for arbitrary horizontal `X`, pick a basic field through `X p`, move the
   direction slot by `oneillA_congr_direction` and the field slot by `oneillA_eq_of_eq_at`, and
   apply the basic-field vanishing.
2. `oneillA_swap_neg`: polarise `A_{X+Y}(X+Y) p = 0` using `oneillA_add_direction` and
   `oneillA_add_field`. This is where field-slot **additivity** is consumed; `ONeillLemmaTwo` had
   to avoid it by polarising inside `∇` instead.
3. `oneillA_eq_two_inv_smul_verticalProjection_mlieBracket`: `𝓥[X,Y] p` is **not** tensorial as a
   bracket, so it is not transferred. Instead `verticalProjection_mlieBracket_eq_oneillA_sub` —
   which already holds for arbitrary horizontal fields, being pure torsion-freeness — rewrites it
   as `A_X Y p − A_Y X p`, and property 3′ folds that to `2 A_X Y p`.

## Why the basic-field lemmas are re-proved here at eventual regularity

`ONeillLemmaTwo.oneillA_horizontalLiftField_self_eq_zero` asks for the base field to be `C^n` at
**every** point of `B`. The basic field supplied by `exists_basic_eq_of_mem_horizontalSpace` is
`FiberBundle.extend E' (dπ_p u)`, which is `C^∞` only on a *neighbourhood* of `f p`. So the global
hypothesis cannot be fed, and the reduction would stall on a regularity technicality rather than on
anything mathematical.

`tangentMetric_leviCivita_horizontalLiftField_self_eq_zero_of_eventually` and
`oneillA_horizontalLiftField_self_eq_zero_of_eventually` are therefore the same statements with
`∀ q, …` weakened to `∀ᶠ q in 𝓝 (f p), …`. Nothing else changes: `hXe` is rebuilt from continuity
of `f` (`Filter.Tendsto.eventually`, through `ContinuousAt`),
`mem_verticalSpace_mlieBracket_horizontalLiftField`
already takes its base-field hypothesis eventually, and
`HorizontalLift.tangentMetric_horizontalLiftField` uses no base-field regularity at all. They
**strictly generalise** the two theorems in `ONeillLemmaTwo`, which are their
`Filter.Eventually.of_forall` specialisations.

## Regularity actually consumed, and the `C²` ceiling

* The projection identities and the part-algebra lemmas need nothing.
* Field-slot additivity and homogeneity need `IsMDiffMetric E (tangentMetric I M)` and
  differentiability at `p` of the **projected** parts of the fields involved — exactly the shape
  `tangentMetric_oneillA_skew` already carries, and exactly what `leviCivita_add_section` and
  `leviCivita_smul_section` consume. Homogeneity adds `MDiffAt c p` for the scalar.
* `exists_mdiffAt_parts_eq` needs `f` of class `C^(m+1)` and both metrics of class `C^m`, at
  `m := 1` for the differentiability the order-zero statement wants: so `f ∈ C²` and both metrics
  in `C¹`.
* The reduction of §"O'Neill's reduction" inherits `minSmoothness ℝ 2 ≤ n` and `(n : ℕ∞ω) ≠ ∞` from
  the vertical-bracket layer, with `f ∈ C^(n+1)` and both metrics in `C^n`; at `n = 2` that is
  `f ∈ C³` and both metrics in `C²`.

**No metric hypothesis anywhere in this file exceeds `C²`.** The `C³` is on the submersion `f`,
never on `gM` or `gB`, and it is inherited unchanged from `Foundations.ONeillLemmaTwo` rather than
introduced here.
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
  {f : M → B} {p : M}

/-! ## The two composition identities

`Foundations.HorizontalSpace` supplies `𝓗𝓗 = 𝓗`, `𝓥𝓥 = 𝓥` and the membership characterisations,
but not the mixed compositions. Both are one line from `horizontalProjection_eq_sub`, and both are
what kills the Leibniz correction below. -/

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **`𝓥 ∘ 𝓗 = 0`**: the vertical projection kills every horizontal vector. -/
theorem verticalProjection_horizontalProjection (u : TangentSpace I p) :
    verticalProjection I J f p (horizontalProjection I J f p u) = 0 := by
  rw [horizontalProjection_eq_sub, map_sub, verticalProjection_verticalProjection, sub_self]

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **`𝓗 ∘ 𝓥 = 0`**: the horizontal projection kills every vertical vector. -/
theorem horizontalProjection_verticalProjection (u : TangentSpace I p) :
    horizontalProjection I J f p (verticalProjection I J f p u) = 0 := by
  rw [horizontalProjection_eq_sub, verticalProjection_verticalProjection, sub_self]

/-! ## The part algebra

`𝓗` and `𝓥` are linear on each fibre, so they commute with sums and with multiplication by a
scalar *function*. This is what lets the Leibniz rule be applied to the projected field rather
than to the field. -/

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- `𝓗(F + F') = 𝓗F + 𝓗F'`, as sections. -/
theorem horizontalPart_add (F F' : Π z : M, TangentSpace I z) :
    horizontalPart I J f (F + F') = horizontalPart I J f F + horizontalPart I J f F' := by
  funext z
  change horizontalProjection I J f z ((F + F') z) = _
  rw [Pi.add_apply, map_add]
  rfl

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- `𝓥(F + F') = 𝓥F + 𝓥F'`, as sections. -/
theorem verticalPart_add (F F' : Π z : M, TangentSpace I z) :
    verticalPart I J f (F + F') = verticalPart I J f F + verticalPart I J f F' := by
  funext z
  change verticalProjection I J f z ((F + F') z) = _
  rw [Pi.add_apply, map_add]
  rfl

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- `𝓗(c • F) = c • 𝓗F` for a scalar **function** `c`. -/
theorem horizontalPart_smul (c : M → ℝ) (F : Π z : M, TangentSpace I z) :
    horizontalPart I J f (c • F) = c • horizontalPart I J f F := by
  funext z
  change horizontalProjection I J f z ((c • F) z) = _
  rw [Pi.smul_apply', map_smul]
  rfl

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- `𝓥(c • F) = c • 𝓥F` for a scalar **function** `c`. -/
theorem verticalPart_smul (c : M → ℝ) (F : Π z : M, TangentSpace I z) :
    verticalPart I J f (c • F) = c • verticalPart I J f F := by
  funext z
  change verticalProjection I J f z ((c • F) z) = _
  rw [Pi.smul_apply', map_smul]
  rfl

/-! ## Field-slot additivity and homogeneity

The mathematical content of this file. Additivity is `leviCivita_add_section` applied in each
summand; homogeneity is `leviCivita_smul_section`, and there the Leibniz correction appears and is
annihilated by the outer projection of its own summand. -/

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **`A` is additive in the field slot**: `A_D (F + F') p = A_D F p + A_D F' p`.

The differentiability consumed is exactly `leviCivita_add_section`'s, and it is about the
**projections** of `F` and `F'`, not about `F` and `F'` — the same hypothesis shape as
`tangentMetric_oneillA_skew`. A caller with `F`, `F'` differentiable and the projections smooth
obtains the four from `contMDiffAt_horizontalPart` and `contMDiffAt_verticalPart`.

-/
theorem oneillA_add_field (hgm : IsMDiffMetric E (tangentMetric I M))
    {D F F' : Π z : M, TangentSpace I z}
    (hHF : MDiffAt (T% (horizontalPart I J f F)) p)
    (hVF : MDiffAt (T% (verticalPart I J f F)) p)
    (hHF' : MDiffAt (T% (horizontalPart I J f F')) p)
    (hVF' : MDiffAt (T% (verticalPart I J f F')) p) :
    oneillA I J f D (F + F') p = oneillA I J f D F p + oneillA I J f D F' p := by
  rw [oneillA_apply, oneillA_apply, oneillA_apply, horizontalPart_add, verticalPart_add,
    leviCivita_add_section isSymm_tangentMetric isNondegenerate_tangentMetric hgm hHF hHF',
    leviCivita_add_section isSymm_tangentMetric isNondegenerate_tangentMetric hgm hVF hVF']
  simp only [add_apply, map_add]
  abel

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **`A` is homogeneous in the field slot**: `A_D (c • F) p = c p • A_D F p`.

This is the theorem in which the mechanism is visible. `𝓗(c • F) = c • 𝓗F`, so the Leibniz rule
contributes `(d% c p w) • 𝓗F p` at the direction `w = 𝓗_p(D p)`; that vector is horizontal and the
outer projection of the summand is `𝓥`, so `𝓥 ∘ 𝓗 = 0` removes it. The second summand is the same
with `𝓗` and `𝓥` exchanged.

-/
theorem oneillA_smul_field (hgm : IsMDiffMetric E (tangentMetric I M))
    {c : M → ℝ} {D F : Π z : M, TangentSpace I z} (hc : MDiffAt c p)
    (hHF : MDiffAt (T% (horizontalPart I J f F)) p)
    (hVF : MDiffAt (T% (verticalPart I J f F)) p) :
    oneillA I J f D (c • F) p = c p • oneillA I J f D F p := by
  rw [oneillA_apply, oneillA_apply, horizontalPart_smul, verticalPart_smul,
    leviCivita_smul_section isSymm_tangentMetric isNondegenerate_tangentMetric hgm hc hHF,
    leviCivita_smul_section isSymm_tangentMetric isNondegenerate_tangentMetric hgm hc hVF]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, smul_apply, map_add, map_smul]
  rw [show verticalProjection I J f p (horizontalPart I J f F p) = 0 from
      verticalProjection_horizontalProjection (F p),
    show horizontalProjection I J f p (verticalPart I J f F p) = 0 from
      horizontalProjection_verticalProjection (F p)]
  simp only [smul_zero, add_zero]
  rw [smul_add]

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **`T` is additive in the field slot**: `T_D (F + F') p = T_D F p + T_D F' p`.

Same proof as `oneillA_add_field` with the roles of `𝓗` and `𝓥` exchanged.

-/
theorem oneillT_add_field (hgm : IsMDiffMetric E (tangentMetric I M))
    {D F F' : Π z : M, TangentSpace I z}
    (hHF : MDiffAt (T% (horizontalPart I J f F)) p)
    (hVF : MDiffAt (T% (verticalPart I J f F)) p)
    (hHF' : MDiffAt (T% (horizontalPart I J f F')) p)
    (hVF' : MDiffAt (T% (verticalPart I J f F')) p) :
    oneillT I J f D (F + F') p = oneillT I J f D F p + oneillT I J f D F' p := by
  rw [oneillT_apply, oneillT_apply, oneillT_apply, horizontalPart_add, verticalPart_add,
    leviCivita_add_section isSymm_tangentMetric isNondegenerate_tangentMetric hgm hHF hHF',
    leviCivita_add_section isSymm_tangentMetric isNondegenerate_tangentMetric hgm hVF hVF']
  simp only [add_apply, map_add]
  abel

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **`T` is homogeneous in the field slot**: `T_D (c • F) p = c p • T_D F p`.

The Leibniz correction of the first summand is `(d% c p w) • 𝓥F p`, killed by that summand's outer
`𝓗` through `𝓗 ∘ 𝓥 = 0`; the second summand is the mirror image.

-/
theorem oneillT_smul_field (hgm : IsMDiffMetric E (tangentMetric I M))
    {c : M → ℝ} {D F : Π z : M, TangentSpace I z} (hc : MDiffAt c p)
    (hHF : MDiffAt (T% (horizontalPart I J f F)) p)
    (hVF : MDiffAt (T% (verticalPart I J f F)) p) :
    oneillT I J f D (c • F) p = c p • oneillT I J f D F p := by
  rw [oneillT_apply, oneillT_apply, horizontalPart_smul, verticalPart_smul,
    leviCivita_smul_section isSymm_tangentMetric isNondegenerate_tangentMetric hgm hc hHF,
    leviCivita_smul_section isSymm_tangentMetric isNondegenerate_tangentMetric hgm hc hVF]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, smul_apply, map_add, map_smul]
  rw [show verticalProjection I J f p (horizontalPart I J f F p) = 0 from
      verticalProjection_horizontalProjection (F p),
    show horizontalProjection I J f p (verticalPart I J f F p) = 0 from
      horizontalProjection_verticalProjection (F p)]
  simp only [smul_zero, add_zero]
  rw [smul_add]

/-! ## Order zero: dependence on the value of the field alone

The consequence O'Neill actually uses. The hypothesis `htest` — enough fields with prescribed value
whose two projections are differentiable at `p` — is discharged by `exists_mdiffAt_parts_eq`
below. -/

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **`A_D F p` depends only on `F p`.**

Proved from skew-symmetry (`tangentMetric_oneillA_skew`, O'Neill's property 1′) and nondegeneracy,
not from a local-frame expansion: for `w ∈ T_pM` and any test field `G` with `G p = w`,
`⟪A_D F p, w⟫ = −⟪A_D G p, F p⟫`, whose right-hand side sees `F` only at `p`. See the module
docstring for the comparison with `Foundations.CurvaturePointwise.curvature_eq_of_eq_at`, which has
no skew-symmetry available and must go through a frame.

-/
theorem oneillA_eq_of_eq_at (hgm : IsMDiffMetric E (tangentMetric I M))
    (htest : ∀ w : TangentSpace I p, ∃ G : Π z : M, TangentSpace I z, G p = w ∧
      MDiffAt (T% (horizontalPart I J f G)) p ∧ MDiffAt (T% (verticalPart I J f G)) p)
    {D F F' : Π z : M, TangentSpace I z}
    (hHF : MDiffAt (T% (horizontalPart I J f F)) p)
    (hVF : MDiffAt (T% (verticalPart I J f F)) p)
    (hHF' : MDiffAt (T% (horizontalPart I J f F')) p)
    (hVF' : MDiffAt (T% (verticalPart I J f F')) p)
    (hFF' : F p = F' p) :
    oneillA I J f D F p = oneillA I J f D F' p := by
  refine eq_of_g_eq (isNondegenerate_tangentMetric p) fun w ↦ ?_
  obtain ⟨G, hGp, hHG, hVG⟩ := htest w
  rw [← hGp, tangentMetric_oneillA_skew hgm hHF hVF hHG hVG,
    tangentMetric_oneillA_skew hgm hHF' hVF' hHG hVG, hFF']

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **`T_D F p` depends only on `F p`.** Same proof as `oneillA_eq_of_eq_at`, from
`tangentMetric_oneillT_skew` (O'Neill's property 1).

-/
theorem oneillT_eq_of_eq_at (hgm : IsMDiffMetric E (tangentMetric I M))
    (htest : ∀ w : TangentSpace I p, ∃ G : Π z : M, TangentSpace I z, G p = w ∧
      MDiffAt (T% (horizontalPart I J f G)) p ∧ MDiffAt (T% (verticalPart I J f G)) p)
    {D F F' : Π z : M, TangentSpace I z}
    (hHF : MDiffAt (T% (horizontalPart I J f F)) p)
    (hVF : MDiffAt (T% (verticalPart I J f F)) p)
    (hHF' : MDiffAt (T% (horizontalPart I J f F')) p)
    (hVF' : MDiffAt (T% (verticalPart I J f F')) p)
    (hFF' : F p = F' p) :
    oneillT I J f D F p = oneillT I J f D F' p := by
  refine eq_of_g_eq (isNondegenerate_tangentMetric p) fun w ↦ ?_
  obtain ⟨G, hGp, hHG, hVG⟩ := htest w
  rw [← hGp, tangentMetric_oneillT_skew hgm hHF hVF hHG hVG,
    tangentMetric_oneillT_skew hgm hHF' hVF' hHG hVG, hFF']

/-! ## The projections of a horizontal field

For a horizontal field the two hypotheses above collapse to one: `𝓗X = X`, and `𝓥X = X − 𝓗X` is
then a difference of differentiable sections. Stated rather than inlined because every use of
`oneillA_eq_of_eq_at` on horizontal fields needs both. -/

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- The horizontal part of a differentiable horizontal field is differentiable, with no submersion
or metric hypothesis: it *is* the field. -/
theorem mdiffAt_horizontalPart_of_isHorizontalField {X : Π z : M, TangentSpace I z}
    (hX : IsHorizontalField I J f X) (hXd : MDiffAt (T% X) p) :
    MDiffAt (T% (horizontalPart I J f X)) p := by
  rw [isHorizontalField_iff.mp hX]
  exact hXd

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- The vertical part of a differentiable horizontal field is differentiable, with no submersion or
metric hypothesis: it is `X − X`. -/
theorem mdiffAt_verticalPart_of_isHorizontalField {X : Π z : M, TangentSpace I z}
    (hX : IsHorizontalField I J f X) (hXd : MDiffAt (T% X) p) :
    MDiffAt (T% (verticalPart I J f X)) p := by
  rw [verticalPart_eq_sub, isHorizontalField_iff.mp hX]
  exact mdifferentiableAt_sub_section hXd hXd

section Base

variable [Bundle.RiemannianBundle (TangentSpace J : B → Type _)]
variable {Y : Π q : B, TangentSpace J q}

/-! ## The supply of test fields -/

omit [FiniteDimensional ℝ E'] in
/-- **A field with prescribed value at `p` whose two projections are differentiable at `p`.**

`FiberBundle.extend E v` takes the value `v` at `p` (`FiberBundle.extend_apply_self`) and is `C^m`
at `p` at every order with no hypothesis at all (`FiberBundle.contMDiffAt_extend`); the projections
then cost exactly `contMDiffAt_horizontalPart`'s and `contMDiffAt_verticalPart`'s hypotheses — one
derivative of `f` and both metrics at order `m`.

This is the horizontal-and-vertical companion of `ONeillLemmaTwo.verticalExtend` and its regularity
lemma: there only the vertical part was wanted, and it was wanted on a whole neighbourhood; here
both parts are wanted, and only at `p`. -/
theorem exists_mdiffAt_parts_eq {m : ℕ∞} {u : Set M} (hu : IsOpen u) (hpu : p ∈ u)
    (hf : ContMDiffOn I J ((m + 1 : ℕ∞)) f u)
    (hgM : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ((m : ℕ∞ω))
      (fun z ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ) z
        (tangentMetric I M z)) p)
    (hgB : ContMDiffAt J (J.prod 𝓘(ℝ, E' →L[ℝ] E' →L[ℝ] ℝ)) ((m : ℕ∞ω))
      (fun q ↦ TotalSpace.mk' (E' →L[ℝ] E' →L[ℝ] ℝ)
        (E := fun q : B ↦ TangentSpace J q →L[ℝ] TangentSpace J q →L[ℝ] ℝ) q
        (tangentMetric J B q)) (f p))
    (hsub : ∀ᶠ z in 𝓝 p, IsSubmersionAtPoint I J f z)
    (hriem : ∀ᶠ z in 𝓝 p, IsRiemannianSubmersionAtPoint I J f z)
    (hm : ((m : ℕ∞ω)) ≠ 0) (v : TangentSpace I p) :
    ∃ G : Π z : M, TangentSpace I z, G p = v ∧
      MDiffAt (T% (horizontalPart I J f G)) p ∧ MDiffAt (T% (verticalPart I J f G)) p :=
  ⟨FiberBundle.extend E v, FiberBundle.extend_apply_self E v,
    (contMDiffAt_horizontalPart hu hpu hf hgM hgB hsub hriem
      (FiberBundle.contMDiffAt_extend I E v)).mdifferentiableAt hm,
    (contMDiffAt_verticalPart hu hpu hf hgM hgB hsub hriem
      (FiberBundle.contMDiffAt_extend I E v)).mdifferentiableAt hm⟩

omit [FiniteDimensional ℝ E'] in
/-- `exists_mdiffAt_parts_eq` in the hypothesis shape of `Foundations.ONeillLemmaTwo`: `f` of class
`C^(n+1)` globally, both metrics `C^n` as sections, submersion and isometry conditions at every
point. This is the form the reduction below consumes. -/
theorem exists_mdiffAt_parts_eq_of_isContMDiffMetricSection {n : ℕ∞} (hn0 : (n : ℕ∞ω) ≠ 0)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z) (v : TangentSpace I p) :
    ∃ G : Π z : M, TangentSpace I z, G p = v ∧
      MDiffAt (T% (horizontalPart I J f G)) p ∧ MDiffAt (T% (verticalPart I J f G)) p :=
  exists_mdiffAt_parts_eq isOpen_univ (Set.mem_univ p) hf.contMDiffOn (hgM p) (hgB (f p))
    (Filter.Eventually.of_forall hsub) (Filter.Eventually.of_forall hriem) hn0 v

/-! ## The basic-field input, at eventual regularity

`ONeillLemmaTwo`'s two basic-field theorems ask for the base field to be `C^n` at every point of
`B`. `exists_basic_eq_of_mem_horizontalSpace` produces a base field that is `C^∞` only near `f p`,
so the reduction needs the same statements with that hypothesis taken eventually. Both are
otherwise verbatim; see the module docstring. -/

/-- **`⟨∇_X X, v⟩ = 0` for `X` basic and `v` vertical**, with the base field `C^n` only near `f p`.

This is `ONeillLemmaTwo.tangentMetric_leviCivita_horizontalLiftField_self_eq_zero` with `∀ q, …`
weakened to `∀ᶠ q in 𝓝 (f p), …`, and it strictly generalises it. The only step that changes is the
construction of `hXe`: the eventual regularity of `Y` near `f p` is pulled back along `f` by
continuity (`Filter.Tendsto.eventually`, through `ContinuousAt`), before
`contMDiffAt_horizontalLiftField` is applied.
`mem_verticalSpace_mlieBracket_horizontalLiftField` already takes its base-field hypothesis
eventually, and `HorizontalLift.tangentMetric_horizontalLiftField` uses no base-field regularity at
all. -/
theorem tangentMetric_leviCivita_horizontalLiftField_self_eq_zero_of_eventually {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    (hY : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q)
    {v : TangentSpace I p} (hv : v ∈ verticalSpace I J f p) :
    tangentMetric I M p (leviCivita (tangentMetric I M) (horizontalLiftField I J f Y) p
      (horizontalLiftField I J f Y p)) v = 0 := by
  have hn0 := coe_ne_zero_of_minSmoothness_two_le hn
  have hgm : IsMDiffMetric E (tangentMetric I M) :=
    IsContMDiffMetricSection.isMDiffMetric hn0 hgM
  have hXhor : IsHorizontalField I J f (horizontalLiftField I J f Y) :=
    isHorizontalField_horizontalLiftField
  have hle : ((n : ℕ∞ω)) ≤ (((n + 1 : ℕ∞)) : ℕ∞ω) := by push_cast; exact le_self_add
  have hYf : ∀ᶠ z in 𝓝 p, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) (f z) :=
    hf.continuous.continuousAt.eventually hY
  have hXe : ∀ᶠ z in 𝓝 p,
      ContMDiffAt I I.tangent ((n : ℕ∞ω)) (T% (horizontalLiftField I J f Y)) z := by
    filter_upwards [hYf] with z hz
    exact contMDiffAt_horizontalLiftField isOpen_univ (Set.mem_univ z) hf.contMDiffOn (hgM z)
      (hgB (f z)) hz
  have hXd : MDiffAt (T% (horizontalLiftField I J f Y)) p :=
    hXe.self_of_nhds.mdifferentiableAt hn0
  have hfp : ContMDiffAt I J ((n : ℕ∞ω)) f p := (hf p).of_le hle
  have hfd : MDiffAt f p := hfp.mdifferentiableAt hn0
  have hYY : MDiffAt (fun q ↦ tangentMetric J B q (Y q) (Y q)) (f p) :=
    mdiffAt_pairing ((hgB (f p)).mdifferentiableAt hn0)
      (hY.self_of_nhds.mdifferentiableAt hn0) (hY.self_of_nhds.mdifferentiableAt hn0)
  -- metric compatibility. The `have` is required: `IsCompatibleWith` is a plain `def`, so its
  -- binder names are lost on unfolding and named-argument application to it fails.
  have hc : ∀ {U W Z : Π z : M, TangentSpace I z} {x : M},
      MDiffAt (T% W) x → MDiffAt (T% Z) x →
        d% (fun y ↦ tangentMetric I M y (W y) (Z y)) x (U x)
          = tangentMetric I M x (leviCivita (tangentMetric I M) W x (U x)) (Z x)
            + tangentMetric I M x (W x) (leviCivita (tangentMetric I M) Z x (U x)) :=
    isCompatibleWith_leviCivita isSymm_tangentMetric isNondegenerate_tangentMetric hgm
  have hVvert : IsVerticalField I J f (verticalExtend I J f v) := isVerticalField_verticalExtend
  have hVp : verticalExtend I J f v p = v := verticalExtend_apply_self hv
  have hVe : ∀ᶠ z in 𝓝 p,
      ContMDiffAt I I.tangent ((n : ℕ∞ω)) (T% (verticalExtend I J f v)) z :=
    eventually_contMDiffAt_verticalExtend hf hgM hgB hsub hriem
  have hVd : MDiffAt (T% (verticalExtend I J f v)) p := hVe.self_of_nhds.mdifferentiableAt hn0
  -- step 3: `V⟨X,X⟩ = 0`, hence `⟨∇_v X, X p⟩ = 0`.
  have hb : tangentMetric I M p
      (leviCivita (tangentMetric I M) (horizontalLiftField I J f Y) p v)
      (horizontalLiftField I J f Y p) = 0 := by
    have e := hc (U := FiberBundle.extend E v) (W := horizontalLiftField I J f Y)
      (Z := horizontalLiftField I J f Y) (x := p) hXd hXd
    rw [tangentMetric_horizontalLiftField hsub hriem, mvfderiv_comp_apply hYY hfd,
      FiberBundle.extend_apply_self, mem_verticalSpace_iff.mp hv, map_zero] at e
    have hs := isSymm_tangentMetric p (horizontalLiftField I J f Y p)
      (leviCivita (tangentMetric I M) (horizontalLiftField I J f Y) p v)
    linarith
  -- steps 1 and 2: `⟨X, V⟩ ≡ 0`, hence `⟨∇_X X, v⟩ = −⟨X p, ∇_X V⟩`.
  have hzero : (fun y ↦ tangentMetric I M y (horizontalLiftField I J f Y y)
      (verticalExtend I J f v y)) = fun _ : M ↦ (0 : ℝ) := by
    funext y
    rw [← mem_horizontalSpace_iff_horizontalProjection_eq_self.mp (hXhor y),
      ← mem_verticalSpace_iff_verticalProjection_eq_self.mp (hVvert y)]
    exact tangentMetric_horizontalProjection_verticalProjection
      (horizontalLiftField I J f Y y) (verticalExtend I J f v y)
  have hcc := hc (U := horizontalLiftField I J f Y) (W := horizontalLiftField I J f Y)
    (Z := verticalExtend I J f v) (x := p) hXd hVd
  rw [hzero, mvfderiv_const, zero_apply, hVp] at hcc
  -- step 4: `[V, X]` is vertical, so `⟨∇_V X − ∇_X V, X p⟩ = 0`.
  have hbr : mlieBracket I (verticalExtend I J f v) (horizontalLiftField I J f Y) p
      ∈ verticalSpace I J f p :=
    mem_verticalSpace_mlieBracket_horizontalLiftField hn hn' hfp
      (Filter.Eventually.of_forall hsub) (Filter.Eventually.of_forall hriem) hVvert hVe hXe hY
  have hswap := leviCivita_sub_swap (g := tangentMetric I M) (X := verticalExtend I J f v)
    (Y := horizontalLiftField I J f Y) (x := p)
    isSymm_tangentMetric isNondegenerate_tangentMetric hgm hVd hXd
  have hbr0 : tangentMetric I M p
      (mlieBracket I (verticalExtend I J f v) (horizontalLiftField I J f Y) p)
      (horizontalLiftField I J f Y p) = 0 :=
    tangentMetric_eq_zero_of_mem_verticalSpace_of_mem_horizontalSpace hbr (hXhor p)
  rw [← hswap, map_sub, sub_apply, hVp] at hbr0
  have hs2 := isSymm_tangentMetric p (horizontalLiftField I J f Y p)
    (leviCivita (tangentMetric I M) (verticalExtend I J f v) p (horizontalLiftField I J f Y p))
  linarith

/-- **`A_X X = 0` for a basic field `X = Yᴴ`**, with the base field `C^n` only near `f p`.

`ONeillLemmaTwo.oneillA_horizontalLiftField_self_eq_zero` with `∀ q, …` weakened to
`∀ᶠ q in 𝓝 (f p), …`; it strictly generalises that theorem. The final move is unchanged:
nondegeneracy is applied on all of `T_pM`, the horizontal half of `u = 𝓗u + 𝓥u` pairing to zero
with the `𝓥`-image `A_X X p`. -/
theorem oneillA_horizontalLiftField_self_eq_zero_of_eventually {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    (hY : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q) :
    oneillA I J f (horizontalLiftField I J f Y) (horizontalLiftField I J f Y) p = 0 := by
  have hXhor : IsHorizontalField I J f (horizontalLiftField I J f Y) :=
    isHorizontalField_horizontalLiftField
  rw [oneillA_horizontal_horizontal hXhor hXhor]
  refine isNondegenerate_tangentMetric p _ fun u ↦ ?_
  have hd : horizontalProjection I J f p u + verticalProjection I J f p u = u :=
    horizontalProjection_add_verticalProjection u
  rw [← hd, map_add, tangentMetric_verticalProjection_horizontalProjection,
    tangentMetric_verticalProjection_left, verticalProjection_verticalProjection, zero_add]
  exact tangentMetric_leviCivita_horizontalLiftField_self_eq_zero_of_eventually hn hn' hf hgM hgB
    hsub hriem hY (verticalProjection_mem u)

/-! ## O'Neill's reduction, completed: property 3′ and Lemma 2 for all horizontal fields -/

/-- **`A_X X = 0` for an arbitrary horizontal field `X`.**

O'Neill's "we may assume that `X` is basic", carried out. `exists_basic_eq_of_mem_horizontalSpace`
produces a basic field `Wᴴ` with `Wᴴ p = X p`; the direction slot moves by
`oneillA_congr_direction` and the field slot by `oneillA_eq_of_eq_at`, and the basic-field
vanishing finishes. Both slots have to move, and they move for different reasons: the direction
slot because `A_D` sees `D` only through `𝓗_p(D p)`, the field slot because of this campaign's
order-zero statement. -/
theorem oneillA_self_eq_zero {n : ℕ∞} (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    {X : Π z : M, TangentSpace I z} (hXhor : IsHorizontalField I J f X)
    (hXd : MDiffAt (T% X) p) :
    oneillA I J f X X p = 0 := by
  have hn0 := coe_ne_zero_of_minSmoothness_two_le hn
  have hgm : IsMDiffMetric E (tangentMetric I M) :=
    IsContMDiffMetricSection.isMDiffMetric hn0 hgM
  obtain ⟨W, hWe, hWX⟩ :=
    exists_basic_eq_of_mem_horizontalSpace (m := n) (hsub p) (hriem p) (hXhor p)
  have hWhor : IsHorizontalField I J f (horizontalLiftField I J f W) :=
    isHorizontalField_horizontalLiftField
  have hWd : MDiffAt (T% (horizontalLiftField I J f W)) p :=
    (contMDiffAt_horizontalLiftField isOpen_univ (Set.mem_univ p) hf.contMDiffOn (hgM p)
      (hgB (f p)) hWe.self_of_nhds).mdifferentiableAt hn0
  have htest := exists_mdiffAt_parts_eq_of_isContMDiffMetricSection (p := p) hn0 hf hgM hgB hsub
    hriem
  have e1 : oneillA I J f X X p = oneillA I J f (horizontalLiftField I J f W) X p :=
    oneillA_congr_direction (by rw [hWX])
  have e2 : oneillA I J f (horizontalLiftField I J f W) X p
      = oneillA I J f (horizontalLiftField I J f W) (horizontalLiftField I J f W) p :=
    oneillA_eq_of_eq_at hgm htest (mdiffAt_horizontalPart_of_isHorizontalField hXhor hXd)
      (mdiffAt_verticalPart_of_isHorizontalField hXhor hXd)
      (mdiffAt_horizontalPart_of_isHorizontalField hWhor hWd)
      (mdiffAt_verticalPart_of_isHorizontalField hWhor hWd) hWX.symm
  rw [e1, e2]
  exact oneillA_horizontalLiftField_self_eq_zero_of_eventually hn hn' hf hgM hgB hsub hriem hWe

/-- **O'Neill's property 3′: `A_X Y = −A_Y X` for arbitrary horizontal fields.**

This **generalises** `ONeillLemmaTwo.oneillA_horizontalLiftField_swap_neg`, which is the case of
basic fields, to O'Neill's own hypotheses; the reduction from horizontal to basic is O'Neill's own
("we may assume that `X` is basic"), and it is carried out in `oneillA_self_eq_zero`.

The polarisation is now the direct one: `A_{X+Y}(X+Y) p = 0` expands by `oneillA_add_direction` and
`oneillA_add_field`. `ONeillLemmaTwo` had to expand inside `∇` instead, because field-slot
additivity of `A` was unavailable there; that detour is no longer needed.

-/
theorem oneillA_swap_neg {n : ℕ∞} (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    {X W : Π z : M, TangentSpace I z} (hXhor : IsHorizontalField I J f X)
    (hWhor : IsHorizontalField I J f W) (hXd : MDiffAt (T% X) p) (hWd : MDiffAt (T% W) p) :
    oneillA I J f X W p = -oneillA I J f W X p := by
  have hn0 := coe_ne_zero_of_minSmoothness_two_le hn
  have hgm : IsMDiffMetric E (tangentMetric I M) :=
    IsContMDiffMetricSection.isMDiffMetric hn0 hgM
  have hShor : IsHorizontalField I J f (X + W) := fun z ↦
    (horizontalSpace I J f z).add_mem (hXhor z) (hWhor z)
  have hSd : MDiffAt (T% (X + W)) p := mdifferentiableAt_add_section hXd hWd
  have hXX : oneillA I J f X X p = 0 :=
    oneillA_self_eq_zero hn hn' hf hgM hgB hsub hriem hXhor hXd
  have hWW : oneillA I J f W W p = 0 :=
    oneillA_self_eq_zero hn hn' hf hgM hgB hsub hriem hWhor hWd
  have hS : oneillA I J f (X + W) (X + W) p = 0 :=
    oneillA_self_eq_zero hn hn' hf hgM hgB hsub hriem hShor hSd
  rw [oneillA_add_direction,
    oneillA_add_field hgm (mdiffAt_horizontalPart_of_isHorizontalField hXhor hXd)
      (mdiffAt_verticalPart_of_isHorizontalField hXhor hXd)
      (mdiffAt_horizontalPart_of_isHorizontalField hWhor hWd)
      (mdiffAt_verticalPart_of_isHorizontalField hWhor hWd),
    oneillA_add_field hgm (mdiffAt_horizontalPart_of_isHorizontalField hXhor hXd)
      (mdiffAt_verticalPart_of_isHorizontalField hXhor hXd)
      (mdiffAt_horizontalPart_of_isHorizontalField hWhor hWd)
      (mdiffAt_verticalPart_of_isHorizontalField hWhor hWd), hXX, hWW] at hS
  simp only [zero_add, add_zero] at hS
  exact add_eq_zero_iff_eq_neg.mp hS

/-- **O'Neill's LEMMA 2 for arbitrary horizontal fields**: `A_X Y = ½ 𝓥[X, Y]`.

This **generalises** `ONeillLemmaTwo`'s basic-field Lemma 2,
`oneillA_horizontalLiftField_eq_two_inv_smul_verticalProjection_mlieBracket`, to O'Neill's own
hypotheses; the reduction from horizontal to basic fields is O'Neill's own.

`𝓥[X, Y] p` is **not** tensorial as a bracket and is therefore *not* transferred from a basic pair:
`verticalProjection_mlieBracket_eq_oneillA_sub` — pure torsion-freeness, already stated for
arbitrary horizontal fields — rewrites it as `A_X Y p − A_Y X p`, which is tensorial once `A` is,
and property 3′ folds that to `A_X Y p + A_X Y p`. The `2` that gets inverted is `two_smul`, so the
`½` is still not a normalisation put in by hand; see `ONeillLemmaTwo`'s module docstring.

-/
theorem oneillA_eq_two_inv_smul_verticalProjection_mlieBracket {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    {X W : Π z : M, TangentSpace I z} (hXhor : IsHorizontalField I J f X)
    (hWhor : IsHorizontalField I J f W) (hXd : MDiffAt (T% X) p) (hWd : MDiffAt (T% W) p) :
    oneillA I J f X W p
      = (2 : ℝ)⁻¹ • verticalProjection I J f p (mlieBracket I X W p) := by
  have hn0 := coe_ne_zero_of_minSmoothness_two_le hn
  have hgm : IsMDiffMetric E (tangentMetric I M) :=
    IsContMDiffMetricSection.isMDiffMetric hn0 hgM
  have hbr := verticalProjection_mlieBracket_eq_oneillA_sub hgm hXhor hWhor hXd hWd
  have hsw : oneillA I J f W X p = -oneillA I J f X W p :=
    oneillA_swap_neg hn hn' hf hgM hgB hsub hriem hWhor hXhor hWd hXd
  rw [hbr, hsw, sub_neg_eq_add, ← two_smul ℝ, smul_smul]
  norm_num

end Base

end RiemannianGeometry
