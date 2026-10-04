/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import RiemannianGeometry.HorizontalLift
import RiemannianGeometry.LeviCivita

/-!
# O'Neill's tensors `T` and `A` of a Riemannian submersion

O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. **13** (1966) 459–469,
§2 (p. 460), defines for arbitrary vector fields `E`, `F` on the total space

    T_E F = 𝓗∇_{𝓥E}(𝓥F) + 𝓥∇_{𝓥E}(𝓗F)
    A_E F = 𝓥∇_{𝓗E}(𝓗F) + 𝓗∇_{𝓗E}(𝓥F)

where `∇` is the Levi-Civita connection of the total space and `𝓗`, `𝓥` are the horizontal and
vertical projections. `T` is the second fundamental form of all the fibres; `A` is its dual,
obtained by exchanging `𝓗` and `𝓥`.

## ⚠ The direction is the LAST argument

This development writes `cov σ x v` for `(∇_v σ)(x)`, following the warning in Mathlib's
`CovariantDerivative/Basic.lean`. So `∇_{𝓗E}(𝓗F)` at `p` is

    leviCivita g (horizontalPart I J f F) p (horizontalProjection I J f p (E p))

— the projected *field* being differentiated is the second argument, the projected *direction* is
the last one. Reading it the other way inverts everything below.

## ⚠ The three projections in each summand are different objects

In `𝓥∇_{𝓗E}(𝓗F)` the outer `𝓥` is applied to the result, the inner `𝓗` to the direction, and the
third `𝓗` to the field being differentiated. Collapsing any two of them produces something that
typechecks and is wrong.

## Main definitions

* `oneillT I J f D F` — the tensor `T`, as a field; `D` plays O'Neill's direction slot `E`
  (the letter `E` is taken by the model vector space in the ambient variable block).
* `oneillA I J f D F` — the tensor `A`.

## Main results

* `oneillT_apply`, `oneillA_apply` — the unfolded definitions, by `rfl`. **These are the canonical
  specifications**: every result below is derived from them and never from the definition body.
* `isSymm_tangentMetric`, `isNondegenerate_tangentMetric` — the two side conditions of
  `leviCivita` that the `RiemannianBundle` supplies for free. The third, `IsMDiffMetric`, is not
  available from the class and is taken as a hypothesis wherever it is needed (only in the
  skew-symmetry group).
* `oneillT_eq_oneillT_verticalPart`, `oneillA_eq_oneillA_horizontalPart` — O'Neill's properties 2
  and 2′, `T_E = T_{𝓥E}` and `A_E = A_{𝓗E}`.
* `oneillT_congr_direction`, `oneillA_congr_direction` — the sharper form: `T` and `A` see the
  direction only through `𝓥E p`, resp. `𝓗E p`.
* `oneillT_vertical_vertical`, `oneillT_vertical_horizontal`, `oneillA_horizontal_vertical`,
  `oneillA_horizontal_horizontal` — **O'Neill's Lemma 3 (§9a), parts (1), (2), (3), (4)**: the
  one-summand simplifications. These, not the definitions, are what later computations cite.
* `oneillT_add_direction`, `oneillT_smul_direction`, `oneillA_add_direction`,
  `oneillA_smul_direction` — linearity in the direction slot.
* `oneillT_mem_verticalSpace_of_isHorizontalField` and its three companions — the easy half of
  properties 1 and 1′: `T_E` and `A_E` **reverse** horizontal and vertical.
* `tangentMetric_oneillT_skew`, `tangentMetric_oneillA_skew` — the substantive half of properties
  1 and 1′: skew-symmetry, `⟪T_E F, G⟫ = −⟪F, T_E G⟫` and `⟪A_E F, G⟫ = −⟪A_E G, F⟫`.

## The metric, and why it is `tangentMetric I M`

`leviCivita` takes its metric as data. Taking that data to be `tangentMetric I M`, the metric
underlying the ambient `Bundle.RiemannianBundle`, is what makes the horizontal layer of
`RiemannianGeometry.HorizontalSpace` and the connection speak about the *same* metric — without it
`𝓗` and `∇` would be unrelated. `inner_eq_tangentMetric` is `rfl`, so the inner-product spelling of
the horizontal layer and the metric-as-data spelling of the connection are interchangeable, and
both appear below.

The skew-symmetry statements are phrased with `tangentMetric I M p` rather than `inner ℝ` because
`IsCompatibleWith` — the only substantive input — is phrased that way, so the proof needs no
translation step at all. Read them as `⟪·,·⟫` through `inner_eq_tangentMetric`.

## Regularity actually consumed

* The definitions, the evaluation lemmas, properties 2 and 2′, Lemma 3 and the reversal statements
  need **no** differentiability hypothesis whatever. `leviCivita` is total (junk values where its
  side conditions fail), and every step above is either a projection identity or `∇0 = 0`.
* Linearity in the direction is free from the type: `leviCivita g Y p` is a continuous linear map.
* Skew-symmetry needs metric compatibility, hence `IsMDiffMetric E (tangentMetric I M)` **and**
  differentiability at `p` of the four *projected* fields `𝓗F`, `𝓥F`, `𝓗G`, `𝓥G` — not of `F` and
  `G`. That is exactly what `IsCompatibleWith` consumes and it is stated honestly; a caller with
  `F` and `G` differentiable and the projections smooth obtains the four from
  `contMDiffAt_horizontalPart` and `contMDiffAt_verticalPart`, at the price of those theorems'
  submersion and metric-smoothness hypotheses.

Deliberately **not** here: `T_V W = T_W V` (property 3), `A_X Y = −A_Y X` (property 3′) and
`A_X Y = ½𝓥[X,Y]` (Lemma 2), all of which need the vertical-bracket results; and the curvature
equations `{0}`–`{4}`.
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

/-! ## The two side conditions of `leviCivita` that the bundle supplies -/

omit [FiniteDimensional ℝ E] in
/-- **The tangent metric is symmetric**, from the `symm` field of `Bundle.RiemannianMetric`. One of
the three side conditions of `leviCivita`. -/
theorem isSymm_tangentMetric : IsSymm (tangentMetric I M) :=
  fun y u v ↦ (Bundle.RiemannianBundle.g (E := (TangentSpace I : M → Type _))).symm y u v

omit [FiniteDimensional ℝ E] in
/-- **The tangent metric is nondegenerate**, in the weak form `leviCivita` asks for. This is
literally `tangentMetric_nondegenerate` — `IsNondegenerate` quantifies over the point exactly as
that theorem's explicit argument does, so no wrapper is needed. -/
theorem isNondegenerate_tangentMetric : IsNondegenerate (tangentMetric I M) :=
  tangentMetric_nondegenerate I M

/-! ## Projection calculus used below -/

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- The horizontal part of a vertical field is the zero field. -/
theorem horizontalPart_eq_zero {V : Π z : M, TangentSpace I z} (hV : IsVerticalField I J f V) :
    horizontalPart I J f V = 0 := by
  funext z
  change horizontalProjection I J f z (V z) = 0
  rw [horizontalProjection_eq_sub,
    mem_verticalSpace_iff_verticalProjection_eq_self.mp (hV z), sub_self]

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- The vertical part of a horizontal field is the zero field. -/
theorem verticalPart_eq_zero {X : Π z : M, TangentSpace I z} (hX : IsHorizontalField I J f X) :
    verticalPart I J f X = 0 := by
  rw [verticalPart_eq_sub, isHorizontalField_iff.mp hX, sub_self]

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **`𝓗` is self-adjoint for the tangent metric**: it is an orthogonal projection. -/
theorem tangentMetric_horizontalProjection_left (u w : TangentSpace I p) :
    tangentMetric I M p (horizontalProjection I J f p u) w
      = tangentMetric I M p u (horizontalProjection I J f p w) := by
  have : FiniteDimensional ℝ (TangentSpace I p) := inferInstanceAs (FiniteDimensional ℝ E)
  rw [← inner_eq_tangentMetric, ← inner_eq_tangentMetric]
  change inner ℝ ((horizontalSpace I J f p).starProjection u) w
    = inner ℝ u ((horizontalSpace I J f p).starProjection w)
  exact (horizontalSpace I J f p).starProjection_isSymmetric u w

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **`𝓥` is self-adjoint for the tangent metric.** -/
theorem tangentMetric_verticalProjection_left (u w : TangentSpace I p) :
    tangentMetric I M p (verticalProjection I J f p u) w
      = tangentMetric I M p u (verticalProjection I J f p w) := by
  have : FiniteDimensional ℝ (TangentSpace I p) := inferInstanceAs (FiniteDimensional ℝ E)
  rw [← inner_eq_tangentMetric, ← inner_eq_tangentMetric]
  change inner ℝ ((verticalSpace I J f p).starProjection u) w
    = inner ℝ u ((verticalSpace I J f p).starProjection w)
  exact (verticalSpace I J f p).starProjection_isSymmetric u w

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- Horizontal is orthogonal to vertical, in metric-as-data form. -/
theorem tangentMetric_horizontalProjection_verticalProjection (u w : TangentSpace I p) :
    tangentMetric I M p (horizontalProjection I J f p u) (verticalProjection I J f p w) = 0 :=
  inner_horizontalProjection_verticalProjection u w

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- Vertical is orthogonal to horizontal, in metric-as-data form. -/
theorem tangentMetric_verticalProjection_horizontalProjection (u w : TangentSpace I p) :
    tangentMetric I M p (verticalProjection I J f p u) (horizontalProjection I J f p w) = 0 := by
  rw [← inner_eq_tangentMetric, real_inner_comm]
  exact inner_horizontalProjection_verticalProjection w u

/-! ## The definitions -/

variable (I J f) in
/-- **O'Neill's tensor `T`** (ON1966 §2, p. 460), the second fundamental form of all the fibres:

    T_D F = 𝓗∇_{𝓥D}(𝓥F) + 𝓥∇_{𝓥D}(𝓗F).

`D` is O'Neill's direction argument `E`, renamed because `E` is the model vector space here. The
three projections in each summand are distinct: the outer one acts on the result, the inner one on
the direction, the one inside `verticalPart`/`horizontalPart` on the field being differentiated.
The direction is the **last** argument of `leviCivita`. 

-/
def oneillT (D F : Π z : M, TangentSpace I z) (p : M) : TangentSpace I p :=
  horizontalProjection I J f p
      (leviCivita (tangentMetric I M) (verticalPart I J f F) p
        (verticalProjection I J f p (D p)))
    + verticalProjection I J f p
      (leviCivita (tangentMetric I M) (horizontalPart I J f F) p
        (verticalProjection I J f p (D p)))

variable (I J f) in
/-- **O'Neill's tensor `A`** (ON1966 §2, p. 460), the dual of `T` obtained by exchanging `𝓗`
and `𝓥`:

    A_D F = 𝓥∇_{𝓗D}(𝓗F) + 𝓗∇_{𝓗D}(𝓥F).

Same three warnings as for `oneillT`. 

-/
def oneillA (D F : Π z : M, TangentSpace I z) (p : M) : TangentSpace I p :=
  verticalProjection I J f p
      (leviCivita (tangentMetric I M) (horizontalPart I J f F) p
        (horizontalProjection I J f p (D p)))
    + horizontalProjection I J f p
      (leviCivita (tangentMetric I M) (verticalPart I J f F) p
        (horizontalProjection I J f p (D p)))

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **The evaluation lemma for `T`, and its canonical specification.** Everything below is derived
from this rather than from the definition body. -/
theorem oneillT_apply (D F : Π z : M, TangentSpace I z) (p : M) :
    oneillT I J f D F p =
      horizontalProjection I J f p
          (leviCivita (tangentMetric I M) (verticalPart I J f F) p
            (verticalProjection I J f p (D p)))
        + verticalProjection I J f p
          (leviCivita (tangentMetric I M) (horizontalPart I J f F) p
            (verticalProjection I J f p (D p))) := rfl

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **The evaluation lemma for `A`, and its canonical specification.** -/
theorem oneillA_apply (D F : Π z : M, TangentSpace I z) (p : M) :
    oneillA I J f D F p =
      verticalProjection I J f p
          (leviCivita (tangentMetric I M) (horizontalPart I J f F) p
            (horizontalProjection I J f p (D p)))
        + horizontalProjection I J f p
          (leviCivita (tangentMetric I M) (verticalPart I J f F) p
            (horizontalProjection I J f p (D p))) := rfl

/-! ## Properties 2 and 2′, and tensoriality in the direction slot -/

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **`T` sees the direction only through `𝓥D` at the point.** This is the cleanest form of the
direction-slot tensoriality of `T`: pointwise dependence on `𝓥D p` alone. Property 2 is the special
case `D' = 𝓥D`. -/
theorem oneillT_congr_direction {D D' F : Π z : M, TangentSpace I z}
    (hD : verticalProjection I J f p (D p) = verticalProjection I J f p (D' p)) :
    oneillT I J f D F p = oneillT I J f D' F p := by
  rw [oneillT_apply, oneillT_apply, hD]

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **`A` sees the direction only through `𝓗D` at the point.** Property 2′ is the special case
`D' = 𝓗D`. -/
theorem oneillA_congr_direction {D D' F : Π z : M, TangentSpace I z}
    (hD : horizontalProjection I J f p (D p) = horizontalProjection I J f p (D' p)) :
    oneillA I J f D F p = oneillA I J f D' F p := by
  rw [oneillA_apply, oneillA_apply, hD]

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **O'Neill's property 2: `T` is vertical, `T_E = T_{𝓥E}`.** Immediate from `𝓥𝓥 = 𝓥`. 

-/
theorem oneillT_eq_oneillT_verticalPart (D F : Π z : M, TangentSpace I z) (p : M) :
    oneillT I J f D F p = oneillT I J f (verticalPart I J f D) F p :=
  oneillT_congr_direction (verticalProjection_verticalProjection (D p)).symm

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **O'Neill's property 2′: `A` is horizontal, `A_E = A_{𝓗E}`.** Immediate from `𝓗𝓗 = 𝓗`. 

-/
theorem oneillA_eq_oneillA_horizontalPart (D F : Π z : M, TangentSpace I z) (p : M) :
    oneillA I J f D F p = oneillA I J f (horizontalPart I J f D) F p :=
  oneillA_congr_direction (horizontalProjection_horizontalProjection (D p)).symm

/-! ## O'Neill's Lemma 3 (§9a): the one-summand simplifications

Each says that the *other* summand of the definition vanishes, because its inner projection is
applied to a field already lying in the complementary subbundle. These four statements — not the
two-summand definitions — are what every later computation cites. None of them needs a
differentiability hypothesis. -/

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **Lemma 3(1): `T_V W = 𝓗∇_V W` for `V`, `W` vertical.** 

-/
theorem oneillT_vertical_vertical {V W : Π z : M, TangentSpace I z}
    (hV : IsVerticalField I J f V) (hW : IsVerticalField I J f W) (p : M) :
    oneillT I J f V W p
      = horizontalProjection I J f p (leviCivita (tangentMetric I M) W p (V p)) := by
  rw [oneillT_apply, horizontalPart_eq_zero hW, leviCivita_zero_section, zero_apply, map_zero,
    add_zero, isVerticalField_iff.mp hW,
    mem_verticalSpace_iff_verticalProjection_eq_self.mp (hV p)]

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **Lemma 3(2): `T_V X = 𝓥∇_V X` for `V` vertical and `X` horizontal.** 

-/
theorem oneillT_vertical_horizontal {V X : Π z : M, TangentSpace I z}
    (hV : IsVerticalField I J f V) (hX : IsHorizontalField I J f X) (p : M) :
    oneillT I J f V X p
      = verticalProjection I J f p (leviCivita (tangentMetric I M) X p (V p)) := by
  rw [oneillT_apply, verticalPart_eq_zero hX, leviCivita_zero_section, zero_apply, map_zero,
    zero_add, isHorizontalField_iff.mp hX,
    mem_verticalSpace_iff_verticalProjection_eq_self.mp (hV p)]

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **Lemma 3(3): `A_X V = 𝓗∇_X V` for `X` horizontal and `V` vertical.** 

-/
theorem oneillA_horizontal_vertical {X V : Π z : M, TangentSpace I z}
    (hX : IsHorizontalField I J f X) (hV : IsVerticalField I J f V) (p : M) :
    oneillA I J f X V p
      = horizontalProjection I J f p (leviCivita (tangentMetric I M) V p (X p)) := by
  rw [oneillA_apply, horizontalPart_eq_zero hV, leviCivita_zero_section, zero_apply, map_zero,
    zero_add, isVerticalField_iff.mp hV,
    mem_horizontalSpace_iff_horizontalProjection_eq_self.mp (hX p)]

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **Lemma 3(4): `A_X Y = 𝓥∇_X Y` for `X`, `Y` horizontal.** 

-/
theorem oneillA_horizontal_horizontal {X Y : Π z : M, TangentSpace I z}
    (hX : IsHorizontalField I J f X) (hY : IsHorizontalField I J f Y) (p : M) :
    oneillA I J f X Y p
      = verticalProjection I J f p (leviCivita (tangentMetric I M) Y p (X p)) := by
  rw [oneillA_apply, verticalPart_eq_zero hY, leviCivita_zero_section, zero_apply, map_zero,
    add_zero, isHorizontalField_iff.mp hY,
    mem_horizontalSpace_iff_horizontalProjection_eq_self.mp (hX p)]

/-! ## Linearity in the direction slot

Free from the type: the direction enters only as the argument of the continuous linear map
`leviCivita … p`, precomposed with a projection. The field `F` does not move. -/

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- `T` is additive in the direction slot, pointwise. -/
theorem oneillT_add_direction (D D' F : Π z : M, TangentSpace I z) (p : M) :
    oneillT I J f (D + D') F p = oneillT I J f D F p + oneillT I J f D' F p := by
  simp only [oneillT_apply, Pi.add_apply, map_add]
  abel

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- `T` is homogeneous in the direction slot, pointwise. -/
theorem oneillT_smul_direction (c : ℝ) (D F : Π z : M, TangentSpace I z) (p : M) :
    oneillT I J f (c • D) F p = c • oneillT I J f D F p := by
  simp only [oneillT_apply, Pi.smul_apply, map_smul, smul_add]

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- `A` is additive in the direction slot, pointwise. -/
theorem oneillA_add_direction (D D' F : Π z : M, TangentSpace I z) (p : M) :
    oneillA I J f (D + D') F p = oneillA I J f D F p + oneillA I J f D' F p := by
  simp only [oneillA_apply, Pi.add_apply, map_add]
  abel

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- `A` is homogeneous in the direction slot, pointwise. -/
theorem oneillA_smul_direction (c : ℝ) (D F : Π z : M, TangentSpace I z) (p : M) :
    oneillA I J f (c • D) F p = c • oneillA I J f D F p := by
  simp only [oneillA_apply, Pi.smul_apply, map_smul, smul_add]

/-! ## Properties 1 and 1′, easy half: `T_E` and `A_E` reverse horizontal and vertical

Immediate from the definitions: for a field lying in one subbundle the complementary summand's
inner projection kills it, and the surviving summand's *outer* projection puts the answer in the
other subbundle. -/

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **`T_E` maps horizontal fields to vertical vectors.** -/
theorem oneillT_mem_verticalSpace_of_isHorizontalField {X : Π z : M, TangentSpace I z}
    (hX : IsHorizontalField I J f X) (D : Π z : M, TangentSpace I z) (p : M) :
    oneillT I J f D X p ∈ verticalSpace I J f p := by
  rw [oneillT_apply, verticalPart_eq_zero hX, leviCivita_zero_section, zero_apply, map_zero,
    zero_add]
  exact verticalProjection_mem _

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **`T_E` maps vertical fields to horizontal vectors.** -/
theorem oneillT_mem_horizontalSpace_of_isVerticalField {V : Π z : M, TangentSpace I z}
    (hV : IsVerticalField I J f V) (D : Π z : M, TangentSpace I z) (p : M) :
    oneillT I J f D V p ∈ horizontalSpace I J f p := by
  rw [oneillT_apply, horizontalPart_eq_zero hV, leviCivita_zero_section, zero_apply, map_zero,
    add_zero]
  exact horizontalProjection_mem _

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **`A_E` maps horizontal fields to vertical vectors.** -/
theorem oneillA_mem_verticalSpace_of_isHorizontalField {X : Π z : M, TangentSpace I z}
    (hX : IsHorizontalField I J f X) (D : Π z : M, TangentSpace I z) (p : M) :
    oneillA I J f D X p ∈ verticalSpace I J f p := by
  rw [oneillA_apply, verticalPart_eq_zero hX, leviCivita_zero_section, zero_apply, map_zero,
    add_zero]
  exact verticalProjection_mem _

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **`A_E` maps vertical fields to horizontal vectors.** -/
theorem oneillA_mem_horizontalSpace_of_isVerticalField {V : Π z : M, TangentSpace I z}
    (hV : IsVerticalField I J f V) (D : Π z : M, TangentSpace I z) (p : M) :
    oneillA I J f D V p ∈ horizontalSpace I J f p := by
  rw [oneillA_apply, horizontalPart_eq_zero hV, leviCivita_zero_section, zero_apply, map_zero,
    zero_add]
  exact horizontalProjection_mem _

/-! ## Properties 1 and 1′, substantive half: skew-symmetry

The first place metric compatibility enters. The mechanism: `⟪𝓥F, 𝓗G⟫` and `⟪𝓗F, 𝓥G⟫` are the
**identically zero** functions on `M`, so their directional derivatives vanish, and compatibility
turns each vanishing derivative into a sign flip between the two `∇` terms. -/

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **O'Neill's property 1, skew-symmetry of `T_E`:** `⟪T_E F, G⟫ = −⟪F, T_E G⟫`, pointwise.

The differentiability consumed is exactly what `IsCompatibleWith` asks for, and it is about the
**projections** of `F` and `G`, not about `F` and `G`: each summand of `T` differentiates `𝓥F` or
`𝓗F`. Read `tangentMetric I M p` as `⟪·,·⟫` through `inner_eq_tangentMetric`, which is `rfl`. 

-/
theorem tangentMetric_oneillT_skew (hgm : IsMDiffMetric E (tangentMetric I M))
    {D F G : Π z : M, TangentSpace I z}
    (hHF : MDiffAt (T% (horizontalPart I J f F)) p)
    (hVF : MDiffAt (T% (verticalPart I J f F)) p)
    (hHG : MDiffAt (T% (horizontalPart I J f G)) p)
    (hVG : MDiffAt (T% (verticalPart I J f G)) p) :
    tangentMetric I M p (oneillT I J f D F p) (G p)
      = -tangentMetric I M p (F p) (oneillT I J f D G p) := by
  have hc : ∀ {X Y Z : Π z : M, TangentSpace I z} {x : M},
      MDiffAt (T% Y) x → MDiffAt (T% Z) x →
        d% (fun y ↦ tangentMetric I M y (Y y) (Z y)) x (X x)
          = tangentMetric I M x (leviCivita (tangentMetric I M) Y x (X x)) (Z x)
            + tangentMetric I M x (Y x) (leviCivita (tangentMetric I M) Z x (X x)) :=
    isCompatibleWith_leviCivita isSymm_tangentMetric isNondegenerate_tangentMetric hgm
  have z1 : (fun y ↦ tangentMetric I M y (verticalPart I J f F y) (horizontalPart I J f G y))
      = fun _ : M ↦ (0 : ℝ) :=
    funext fun y ↦ tangentMetric_verticalProjection_horizontalProjection (F y) (G y)
  have z2 : (fun y ↦ tangentMetric I M y (horizontalPart I J f F y) (verticalPart I J f G y))
      = fun _ : M ↦ (0 : ℝ) :=
    funext fun y ↦ tangentMetric_horizontalProjection_verticalProjection (F y) (G y)
  have e1 := hc (X := verticalPart I J f D) (Y := verticalPart I J f F)
    (Z := horizontalPart I J f G) (x := p) hVF hHG
  have e2 := hc (X := verticalPart I J f D) (Y := horizontalPart I J f F)
    (Z := verticalPart I J f G) (x := p) hHF hVG
  have hdir : verticalPart I J f D p = verticalProjection I J f p (D p) := rfl
  rw [z1, mvfderiv_const, zero_apply, hdir] at e1
  rw [z2, mvfderiv_const, zero_apply, hdir] at e2
  have s1 : tangentMetric I M p
        (horizontalProjection I J f p (leviCivita (tangentMetric I M) (verticalPart I J f F) p
          (verticalProjection I J f p (D p)))) (G p)
      = tangentMetric I M p (leviCivita (tangentMetric I M) (verticalPart I J f F) p
          (verticalProjection I J f p (D p))) (horizontalPart I J f G p) :=
    tangentMetric_horizontalProjection_left _ _
  have s2 : tangentMetric I M p
        (verticalProjection I J f p (leviCivita (tangentMetric I M) (horizontalPart I J f F) p
          (verticalProjection I J f p (D p)))) (G p)
      = tangentMetric I M p (leviCivita (tangentMetric I M) (horizontalPart I J f F) p
          (verticalProjection I J f p (D p))) (verticalPart I J f G p) :=
    tangentMetric_verticalProjection_left _ _
  have s3 : tangentMetric I M p (horizontalPart I J f F p)
        (leviCivita (tangentMetric I M) (verticalPart I J f G) p
          (verticalProjection I J f p (D p)))
      = tangentMetric I M p (F p)
        (horizontalProjection I J f p (leviCivita (tangentMetric I M) (verticalPart I J f G) p
          (verticalProjection I J f p (D p)))) :=
    tangentMetric_horizontalProjection_left _ _
  have s4 : tangentMetric I M p (verticalPart I J f F p)
        (leviCivita (tangentMetric I M) (horizontalPart I J f G) p
          (verticalProjection I J f p (D p)))
      = tangentMetric I M p (F p)
        (verticalProjection I J f p (leviCivita (tangentMetric I M) (horizontalPart I J f G) p
          (verticalProjection I J f p (D p)))) :=
    tangentMetric_verticalProjection_left _ _
  simp only [oneillT_apply, map_add, add_apply]
  linarith [e1, e2, s1, s2, s3, s4]

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **O'Neill's property 1′, skew-symmetry of `A_E`:** `⟪A_E F, G⟫ = −⟪A_E G, F⟫`, pointwise.

Same mechanism and same differentiability as `tangentMetric_oneillT_skew`; the direction is now
`𝓗D` instead of `𝓥D`. One instance of symmetry of the metric is used, to line up the two sides. 

-/
theorem tangentMetric_oneillA_skew (hgm : IsMDiffMetric E (tangentMetric I M))
    {D F G : Π z : M, TangentSpace I z}
    (hHF : MDiffAt (T% (horizontalPart I J f F)) p)
    (hVF : MDiffAt (T% (verticalPart I J f F)) p)
    (hHG : MDiffAt (T% (horizontalPart I J f G)) p)
    (hVG : MDiffAt (T% (verticalPart I J f G)) p) :
    tangentMetric I M p (oneillA I J f D F p) (G p)
      = -tangentMetric I M p (oneillA I J f D G p) (F p) := by
  have hc : ∀ {X Y Z : Π z : M, TangentSpace I z} {x : M},
      MDiffAt (T% Y) x → MDiffAt (T% Z) x →
        d% (fun y ↦ tangentMetric I M y (Y y) (Z y)) x (X x)
          = tangentMetric I M x (leviCivita (tangentMetric I M) Y x (X x)) (Z x)
            + tangentMetric I M x (Y x) (leviCivita (tangentMetric I M) Z x (X x)) :=
    isCompatibleWith_leviCivita isSymm_tangentMetric isNondegenerate_tangentMetric hgm
  have z1 : (fun y ↦ tangentMetric I M y (verticalPart I J f F y) (horizontalPart I J f G y))
      = fun _ : M ↦ (0 : ℝ) :=
    funext fun y ↦ tangentMetric_verticalProjection_horizontalProjection (F y) (G y)
  have z2 : (fun y ↦ tangentMetric I M y (horizontalPart I J f F y) (verticalPart I J f G y))
      = fun _ : M ↦ (0 : ℝ) :=
    funext fun y ↦ tangentMetric_horizontalProjection_verticalProjection (F y) (G y)
  have e1 := hc (X := horizontalPart I J f D) (Y := verticalPart I J f F)
    (Z := horizontalPart I J f G) (x := p) hVF hHG
  have e2 := hc (X := horizontalPart I J f D) (Y := horizontalPart I J f F)
    (Z := verticalPart I J f G) (x := p) hHF hVG
  have hdir : horizontalPart I J f D p = horizontalProjection I J f p (D p) := rfl
  rw [z1, mvfderiv_const, zero_apply, hdir] at e1
  rw [z2, mvfderiv_const, zero_apply, hdir] at e2
  have s1 : tangentMetric I M p
        (verticalProjection I J f p (leviCivita (tangentMetric I M) (horizontalPart I J f F) p
          (horizontalProjection I J f p (D p)))) (G p)
      = tangentMetric I M p (leviCivita (tangentMetric I M) (horizontalPart I J f F) p
          (horizontalProjection I J f p (D p))) (verticalPart I J f G p) :=
    tangentMetric_verticalProjection_left _ _
  have s2 : tangentMetric I M p
        (horizontalProjection I J f p (leviCivita (tangentMetric I M) (verticalPart I J f F) p
          (horizontalProjection I J f p (D p)))) (G p)
      = tangentMetric I M p (leviCivita (tangentMetric I M) (verticalPart I J f F) p
          (horizontalProjection I J f p (D p))) (horizontalPart I J f G p) :=
    tangentMetric_horizontalProjection_left _ _
  have s3 : tangentMetric I M p
        (verticalProjection I J f p (leviCivita (tangentMetric I M) (horizontalPart I J f G) p
          (horizontalProjection I J f p (D p)))) (F p)
      = tangentMetric I M p (leviCivita (tangentMetric I M) (horizontalPart I J f G) p
          (horizontalProjection I J f p (D p))) (verticalPart I J f F p) :=
    tangentMetric_verticalProjection_left _ _
  have s4 : tangentMetric I M p
        (horizontalProjection I J f p (leviCivita (tangentMetric I M) (verticalPart I J f G) p
          (horizontalProjection I J f p (D p)))) (F p)
      = tangentMetric I M p (leviCivita (tangentMetric I M) (verticalPart I J f G) p
          (horizontalProjection I J f p (D p))) (horizontalPart I J f F p) :=
    tangentMetric_horizontalProjection_left _ _
  simp only [oneillA_apply, map_add, add_apply]
  linarith [e1, e2, s1, s2, s3, s4,
    isSymm_tangentMetric p (horizontalPart I J f F p)
      (leviCivita (tangentMetric I M) (verticalPart I J f G) p
        (horizontalProjection I J f p (D p))),
    isSymm_tangentMetric p (verticalPart I J f F p)
      (leviCivita (tangentMetric I M) (horizontalPart I J f G) p
        (horizontalProjection I J f p (D p)))]

end RiemannianGeometry
