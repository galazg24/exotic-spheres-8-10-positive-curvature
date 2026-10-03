/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import RiemannianGeometry.ONeillHorizontalCurvature
import RiemannianGeometry.ONeillTensoriality

/-!
# O'Neill's horizontal curvature equation: `hAe` discharged, and the scalar form

Two things are done here, both at **metrics `C²`**.

## 1. The undischarged hypothesis of `ONeillHorizontalCurvature` is removed

`Foundations.ONeillHorizontalCurvature` proves the vector relation of O'Neill's p. 464 — his
*parenthesised* equation `(4)`, an intermediate step, not the braced `{4}` of his Theorem 2 — but
carries one hypothesis its module docstring records as not dischargeable at `C²`:

    hAe : ∀ᶠ z in 𝓝 p, ContMDiffAt I I.tangent n (T% (oneillA I J f Xᴴ Yᴴ)) z

with `n ≥ 2`. Since `A_{Xᴴ}Yᴴ = 𝓥∇_{Xᴴ}Yᴴ`, obtaining that from `contMDiffAt_leviCivita` costs
`gM ∈ C³`, which is outside the project's `C²` invariant on metrics.

It is discharged here. The hypothesis is consumed inside Step 3 by the final clause of O'Neill's
Lemma 3 (`𝓗∇_V Xᴴ = A_{Xᴴ}V`) applied at `V = A_{Xᴴ}Yᴴ`, whose verticality-of-`[V, Xᴴ]` input wants
`V` at `C^n`. Rather than supply that, Step 0′ below applies Lemma 3's final clause to the
**substitute** field `V' = verticalExtend I J f (V p)`, which is `C^n` near `p` for free
(`eventually_contMDiffAt_verticalExtend`, at metrics `C²`), and then transfers both sides to `V`:

* the left-hand side by **direction-slot** tensoriality, which is a `congrArg` on
  `horizontalLeviCivita_apply` and not a lemma at all;
* the right-hand side by **field-slot** tensoriality, `ONeillTensoriality.oneillA_eq_of_eq_at`,
  whose `htest` argument is discharged by
  `exists_mdiffAt_parts_eq_of_isContMDiffMetricSection`.

Swapping the field *inside the bracket* would not be legitimate — a Lie bracket is not tensorial —
and that is not what happens: the bracket is never touched, only the vertical field entering
Lemma 3's conclusion is.

What survives is `MDiffAt (T% (A_{Xᴴ}Yᴴ)) p`, pointwise differentiability at `p`. That is the same
currency as the four `MDiffAt` hypotheses the vector relation already carried, and it holds at
metrics `C²`. It is **not** removable: `A_{Zᴴ}(A_{Xᴴ}Yᴴ) p` is `𝓗(∇_{Zᴴ}(A_{Xᴴ}Yᴴ))(p)` by
Lemma 3(3), which differentiates `A_{Xᴴ}Yᴴ` as a field, and the field-slot tensoriality that moves
it is stated for fields differentiable at `p`.

## 2. The scalar form

Pairing the vector relation against a fourth basic field `Uᴴ` gives O'Neill's `{4}`, the dual Gauss
equation, in the form his Theorem 2 states it:

    ⟪R(Xᴴ,Yᴴ)Zᴴ, Uᴴ⟫ = ⟪R^H(X,Y)Z, Uᴴ⟫
                        − ⟪A_{Xᴴ}Uᴴ, A_{Yᴴ}Zᴴ⟫ + ⟪A_{Yᴴ}Uᴴ, A_{Xᴴ}Zᴴ⟫
                        + 2 ⟪A_{Zᴴ}Uᴴ, A_{Xᴴ}Yᴴ⟫.

The `𝓗` of the vector relation disappears, because `⟪𝓗u, Uᴴ⟫ = ⟪u, 𝓗Uᴴ⟫ = ⟪u, Uᴴ⟫` for `Uᴴ`
horizontal; that is what makes the scalar version the useful one — it speaks about the curvature of
`M`, with no projection in it. The three `A`-compositions collapse to pairings of `A`-**values** by
**skew-symmetry alone** (`tangentMetric_oneillA_skew`, O'Neill's property 1′); alternation
(`ONeillTensoriality.oneillA_swap_neg`) is **not** used.

Note what the scalar form does *not* buy. Its `A_{Xᴴ}Yᴴ` term is a pairing of two values, but
skew-symmetry's own hypotheses are about the **projections of both paired fields**, so the step

    ⟪A_{Zᴴ}(A_{Xᴴ}Yᴴ), Uᴴ⟫ = −⟪A_{Zᴴ}Uᴴ, A_{Xᴴ}Yᴴ⟫

needs `A_{Xᴴ}Yᴴ` differentiable at `p` just as the vector relation does. The scalar form is
reachable at metrics `C²`, but for the reason given in §1, not because the field regularity of
`A_{Xᴴ}Yᴴ` drops out.

## Main results

* `mdiffAt_horizontalPart_of_isVerticalField`, `mdiffAt_verticalPart_of_isVerticalField` — the
  vertical-field companions of `ONeillTensoriality`'s two horizontal-field projection lemmas.
* `horizontalLeviCivita_vertical_horizontalLiftField_of_mdiffAt` — **Step 0′**, Lemma 3's final
  clause with the vertical field asked only to be differentiable at `p`.
* `horizontalProjection_leviCivita_mlieBracket_horizontalLiftField_of_mdiffAt` — **Step 3** without
  `hAe`.
* `horizontalProjection_curvature_horizontalLiftField_of_mdiffAt` — **the vector relation** without
  `hAe`.
* `tangentMetric_horizontalProjection_left_of_mem_horizontalSpace`,
  `tangentMetric_horizontalProjection_left_horizontalLiftField` — the `𝓗`-drop.
* `tangentMetric_curvature_horizontalLiftField` — **the scalar form**, O'Neill's `{4}`.

## Spelling notes

`H` is the model topological space of `I`, so O'Neill's fourth horizontal field is called `U` here,
not `H`. Everything metric-valued is written with `tangentMetric I M p`, never `inner ℝ`.
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
  [Bundle.RiemannianBundle (TangentSpace J : B → Type _)]
  {f : M → B} {p : M} {X Y Z U : Π q : B, TangentSpace J q}
  {V : Π z : M, TangentSpace I z}

/-! ## The projections of a vertical field -/

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B]
  [Bundle.RiemannianBundle (TangentSpace J : B → Type _)] in
/-- The horizontal part of a vertical field is differentiable, with no hypothesis: it is `0`. -/
theorem mdiffAt_horizontalPart_of_isVerticalField (hV : IsVerticalField I J f V) :
    MDiffAt (T% (horizontalPart I J f V)) p := by
  rw [horizontalPart_eq_zero hV]
  exact mdifferentiableAt_zeroSection ..

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B]
  [Bundle.RiemannianBundle (TangentSpace J : B → Type _)] in
/-- The vertical part of a differentiable vertical field is differentiable: it *is* the field. -/
theorem mdiffAt_verticalPart_of_isVerticalField (hV : IsVerticalField I J f V)
    (hVd : MDiffAt (T% V) p) :
    MDiffAt (T% (verticalPart I J f V)) p := by
  rw [isVerticalField_iff.mp hV]
  exact hVd

/-! ## Step 0′: the final clause of Lemma 3 at pointwise regularity -/

/-- **The final clause of O'Neill's LEMMA 3 with the vertical field asked only to be
differentiable at `p`**: `𝓗∇_V Xᴴ p = A_{Xᴴ}V p`.

`horizontalLeviCivita_vertical_horizontalLiftField` asks for `V` to be `C^n` on a whole
neighbourhood of `p`, because the verticality of `[V, Xᴴ]` that its proof consumes is obtained from
`mem_verticalSpace_mlieBracket_horizontalLiftField`, which needs `n ≥ 2` on both bracket arguments.
Here that hypothesis is *discharged* rather than assumed, by moving to a substitute field.

The route. Put `v := V p` and `V' := verticalExtend I J f v`. Then `V'` is vertical
(`isVerticalField_verticalExtend`), has `V' p = v` (`verticalExtend_apply_self`), and is `C^n` near
`p` for free — `eventually_contMDiffAt_verticalExtend` costs only `f ∈ C^(n+1)` and the two metrics
at `C^n`, i.e. nothing beyond this file's standing hypotheses. Applying the neighbourhood version to
`V'` and transferring both sides to `V` finishes, and the two transfers are of different kinds:

* the left-hand side moves by **direction-slot** tensoriality, which is not a lemma at all —
  `horizontalLeviCivita I J f V Xᴴ p` is `𝓗(∇ Xᴴ p (V p))` by `horizontalLeviCivita_apply` and so
  sees `V` only through `V p`;
* the right-hand side moves by **field-slot** tensoriality, `oneillA_eq_of_eq_at`, whose `htest`
  argument is supplied by `exists_mdiffAt_parts_eq_of_isContMDiffMetricSection`.

Swapping the field *inside the bracket* would not be valid: a Lie bracket is not tensorial. -/
theorem horizontalLeviCivita_vertical_horizontalLiftField_of_mdiffAt {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    (hV : IsVerticalField I J f V) (hVd : MDiffAt (T% V) p)
    (hXHe : ∀ᶠ z in 𝓝 p,
      ContMDiffAt I I.tangent ((n : ℕ∞ω)) (T% (horizontalLiftField I J f X)) z)
    (hX : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% X) q) :
    horizontalLeviCivita I J f V (horizontalLiftField I J f X) p
      = oneillA I J f (horizontalLiftField I J f X) V p := by
  have hn0 := coe_ne_zero_of_minSmoothness_two_le hn
  have hgm : IsMDiffMetric E (tangentMetric I M) :=
    IsContMDiffMetricSection.isMDiffMetric hn0 hgM
  have hle : ((n : ℕ∞ω)) ≤ (((n + 1 : ℕ∞)) : ℕ∞ω) := by push_cast; exact le_self_add
  have hfp : ContMDiffAt I J ((n : ℕ∞ω)) f p := (hf p).of_le hle
  set V' := verticalExtend I J f (V p)
  have hV'vert : IsVerticalField I J f V' := isVerticalField_verticalExtend
  have hV'p : V' p = V p := verticalExtend_apply_self (hV p)
  have hV'e : ∀ᶠ z in 𝓝 p, ContMDiffAt I I.tangent ((n : ℕ∞ω)) (T% V') z :=
    eventually_contMDiffAt_verticalExtend hf hgM hgB hsub hriem
  have hV'd : MDiffAt (T% V') p := hV'e.self_of_nhds.mdifferentiableAt hn0
  have key : horizontalLeviCivita I J f V' (horizontalLiftField I J f X) p
      = oneillA I J f (horizontalLiftField I J f X) V' p :=
    horizontalLeviCivita_vertical_horizontalLiftField hn hn' hgm hfp
      (Filter.Eventually.of_forall hsub) (Filter.Eventually.of_forall hriem) hV'vert hV'e hXHe hX
  have hleft : horizontalLeviCivita I J f V (horizontalLiftField I J f X) p
      = horizontalLeviCivita I J f V' (horizontalLiftField I J f X) p := by
    rw [horizontalLeviCivita_apply, horizontalLeviCivita_apply, hV'p]
  have htest := exists_mdiffAt_parts_eq_of_isContMDiffMetricSection (p := p) hn0 hf hgM hgB hsub
    hriem
  have hright : oneillA I J f (horizontalLiftField I J f X) V' p
      = oneillA I J f (horizontalLiftField I J f X) V p :=
    oneillA_eq_of_eq_at hgm htest (mdiffAt_horizontalPart_of_isVerticalField hV'vert)
      (mdiffAt_verticalPart_of_isVerticalField hV'vert hV'd)
      (mdiffAt_horizontalPart_of_isVerticalField hV)
      (mdiffAt_verticalPart_of_isVerticalField hV hVd) hV'p
  rw [hleft, key, hright]

/-! ## Step 3′ and the vector relation, without the undischarged hypothesis -/

/-- **Step 3 of the horizontal curvature equation, with `hAe` discharged.**

    𝓗∇_{[Xᴴ,Yᴴ]}Zᴴ = 𝓗∇_{([X,Y])ᴴ}Zᴴ + 2 A_{Zᴴ}(A_{Xᴴ}Yᴴ)

This supersedes `horizontalProjection_leviCivita_mlieBracket_horizontalLiftField`: its hypothesis

    hAe : ∀ᶠ z in 𝓝 p, ContMDiffAt I I.tangent n (T% (A_{Xᴴ}Yᴴ)) z

— eventual `C^n` regularity of `A_{Xᴴ}Yᴴ` with `n ≥ 2`, which the present API supplies only at
`gM ∈ C³` — is replaced by

    hAXY : MDiffAt (T% (A_{Xᴴ}Yᴴ)) p

which is the same currency as the four `MDiffAt` hypotheses the vector relation already carries and
is available at metrics `C²`. The replacement is
`horizontalLeviCivita_vertical_horizontalLiftField_of_mdiffAt`; everything else is unchanged.

`MDiffAt (T% (A_{Xᴴ}Yᴴ)) p` cannot itself be removed: `A_{Zᴴ}(A_{Xᴴ}Yᴴ) p` is
`𝓗(∇_{Zᴴ}(A_{Xᴴ}Yᴴ))(p)` by Lemma 3(3), which differentiates `A_{Xᴴ}Yᴴ` as a field, and the
field-slot tensoriality that moves it needs that field differentiable at `p`.
-/
theorem horizontalProjection_leviCivita_mlieBracket_horizontalLiftField_of_mdiffAt {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    (hX : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% X) q)
    (hY : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q)
    (hZ : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Z) q)
    (hAXY : MDiffAt (T% (oneillA I J f (horizontalLiftField I J f X)
      (horizontalLiftField I J f Y))) p) :
    horizontalProjection I J f p
        (leviCivita (tangentMetric I M) (horizontalLiftField I J f Z) p
          (mlieBracket I (horizontalLiftField I J f X) (horizontalLiftField I J f Y) p))
      = horizontalLeviCivita I J f (horizontalLiftField I J f (mlieBracket J X Y))
            (horizontalLiftField I J f Z) p
        + (2 : ℝ) • oneillA I J f (horizontalLiftField I J f Z)
            (oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Y)) p := by
  have hn0 := coe_ne_zero_of_minSmoothness_two_le hn
  have hle : ((n : ℕ∞ω)) ≤ (((n + 1 : ℕ∞)) : ℕ∞ω) := by push_cast; exact le_self_add
  have hfp : ContMDiffAt I J ((n : ℕ∞ω)) f p := (hf p).of_le hle
  have hlift : ∀ T : Π q : B, TangentSpace J q,
      (∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% T) q) → ∀ᶠ z in 𝓝 p,
        ContMDiffAt I I.tangent ((n : ℕ∞ω)) (T% (horizontalLiftField I J f T)) z :=
    fun T hT ↦ Filter.Eventually.of_forall fun z ↦
      contMDiffAt_horizontalLiftField isOpen_univ (Set.mem_univ z) hf.contMDiffOn (hgM z)
        (hgB (f z)) (hT (f z))
  have hdec : mlieBracket I (horizontalLiftField I J f X) (horizontalLiftField I J f Y) p
      = horizontalLiftField I J f (mlieBracket J X Y) p
        + (2 : ℝ) • oneillA I J f (horizontalLiftField I J f X)
            (horizontalLiftField I J f Y) p := by
    have h : horizontalProjection I J f p
          (mlieBracket I (horizontalLiftField I J f X) (horizontalLiftField I J f Y) p)
        + verticalProjection I J f p
          (mlieBracket I (horizontalLiftField I J f X) (horizontalLiftField I J f Y) p)
        = mlieBracket I (horizontalLiftField I J f X) (horizontalLiftField I J f Y) p :=
      horizontalProjection_add_verticalProjection _
    rw [horizontalProjection_mlieBracket_horizontalLiftField hn hn' hfp
        (Filter.Eventually.of_forall hsub) (Filter.Eventually.of_forall hriem) (hlift X hX)
        (hlift Y hY) (Filter.Eventually.of_forall hX) (Filter.Eventually.of_forall hY),
      verticalProjection_mlieBracket_horizontalLiftField_eq_two_smul_oneillA hn hn' hf hgM hgB
        hsub hriem hX hY] at h
    exact h.symm
  rw [hdec, leviCivita_apply_add_direction, leviCivita_apply_smul_direction, map_add, map_smul,
    ← horizontalLeviCivita_apply, ← horizontalLeviCivita_apply,
    horizontalLeviCivita_vertical_horizontalLiftField_of_mdiffAt hn hn' hf hgM hgB hsub hriem
      isVerticalField_oneillA_horizontalLiftField hAXY (hlift Z hZ)
      (Filter.Eventually.of_forall hZ)]

/-- **O'Neill's horizontal curvature equation in vector form, with `hAe` discharged.**

    𝓗R(Xᴴ, Yᴴ)Zᴴ = R^H(X, Y)Z + A_{Xᴴ}(A_{Yᴴ}Zᴴ) − A_{Yᴴ}(A_{Xᴴ}Zᴴ) − 2 A_{Zᴴ}(A_{Xᴴ}Yᴴ)

Identical in statement to `horizontalProjection_curvature_horizontalLiftField` except that the
eventual-`C^n` hypothesis `hAe` on `A_{Xᴴ}Yᴴ` is replaced by `MDiffAt (T% (A_{Xᴴ}Yᴴ)) p`. **Every
metric hypothesis is at `C^n` with `n ≥ 2`, and all five `MDiffAt` hypotheses are of the kind the
earlier statement already carried; no `C³` metric occurs.** The proof is the earlier one with Step 3
replaced by `horizontalProjection_leviCivita_mlieBracket_horizontalLiftField_of_mdiffAt`.
-/
theorem horizontalProjection_curvature_horizontalLiftField_of_mdiffAt {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    (hX : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% X) q)
    (hY : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q)
    (hZ : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Z) q)
    (hAXY : MDiffAt (T% (oneillA I J f (horizontalLiftField I J f X)
      (horizontalLiftField I J f Y))) p)
    (hHYZ : MDiffAt (T% (horizontalLeviCivita I J f (horizontalLiftField I J f Y)
      (horizontalLiftField I J f Z))) p)
    (hAYZ : MDiffAt (T% (oneillA I J f (horizontalLiftField I J f Y)
      (horizontalLiftField I J f Z))) p)
    (hHXZ : MDiffAt (T% (horizontalLeviCivita I J f (horizontalLiftField I J f X)
      (horizontalLiftField I J f Z))) p)
    (hAXZ : MDiffAt (T% (oneillA I J f (horizontalLiftField I J f X)
      (horizontalLiftField I J f Z))) p) :
    horizontalProjection I J f p
        (curvature (leviCivita (tangentMetric I M)) (horizontalLiftField I J f X)
          (horizontalLiftField I J f Y) (horizontalLiftField I J f Z) p)
      = oneillHorizontalCurvature I J f X Y Z p
        + oneillA I J f (horizontalLiftField I J f X)
            (oneillA I J f (horizontalLiftField I J f Y) (horizontalLiftField I J f Z)) p
        - oneillA I J f (horizontalLiftField I J f Y)
            (oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Z)) p
        - (2 : ℝ) • oneillA I J f (horizontalLiftField I J f Z)
            (oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Y)) p := by
  have hn0 := coe_ne_zero_of_minSmoothness_two_le hn
  have hgm : IsMDiffMetric E (tangentMetric I M) :=
    IsContMDiffMetricSection.isMDiffMetric hn0 hgM
  rw [curvature_apply, map_sub, map_sub,
    horizontalProjection_leviCivita_leviCivita_horizontalLiftField hgm hHYZ hAYZ,
    horizontalProjection_leviCivita_leviCivita_horizontalLiftField (X := Y) (Y := X) (Z := Z)
      hgm hHXZ hAXZ,
    horizontalProjection_leviCivita_mlieBracket_horizontalLiftField_of_mdiffAt hn hn' hf hgM hgB
      hsub hriem hX hY hZ hAXY,
    oneillHorizontalCurvature_apply]
  abel

/-! ## Dropping `𝓗` against a horizontal vector -/

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B]
  [Bundle.RiemannianBundle (TangentSpace J : B → Type _)] in
/-- **`⟪𝓗u, w⟫ = ⟪u, w⟫` for `w` horizontal**: self-adjointness of `𝓗`
(`tangentMetric_horizontalProjection_left`) followed by `𝓗w = w`. This is what makes the scalar
form of the curvature equation an equation about `R` rather than about `𝓗R`. -/
theorem tangentMetric_horizontalProjection_left_of_mem_horizontalSpace (u : TangentSpace I p)
    {w : TangentSpace I p} (hw : w ∈ horizontalSpace I J f p) :
    tangentMetric I M p (horizontalProjection I J f p u) w = tangentMetric I M p u w := by
  rw [tangentMetric_horizontalProjection_left,
    mem_horizontalSpace_iff_horizontalProjection_eq_self.mp hw]

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **The `𝓗` in front of a curvature term can be dropped when the test field is basic**:
`⟪𝓗u, Uᴴ⟫ = ⟪u, Uᴴ⟫`. Stated separately because this is the step that turns the vector relation's
`𝓗R(Xᴴ,Yᴴ)Zᴴ` into `R(Xᴴ,Yᴴ)Zᴴ` in the scalar form; the curvature case is the instance
`u := curvature (leviCivita (tangentMetric I M)) Xᴴ Yᴴ Zᴴ p`. -/
theorem tangentMetric_horizontalProjection_left_horizontalLiftField (u : TangentSpace I p)
    (U : Π q : B, TangentSpace J q) :
    tangentMetric I M p (horizontalProjection I J f p u) (horizontalLiftField I J f U p)
      = tangentMetric I M p u (horizontalLiftField I J f U p) :=
  tangentMetric_horizontalProjection_left_of_mem_horizontalSpace u
    (isHorizontalField_horizontalLiftField p)

/-! ## The scalar form -/

/-- **O'Neill's equation `{4}`, the dual Gauss equation, in scalar form.** For basic fields
`Xᴴ`, `Yᴴ`, `Zᴴ`, `Uᴴ`,

    ⟪R(Xᴴ,Yᴴ)Zᴴ, Uᴴ⟫ = ⟪R^H(X,Y)Z, Uᴴ⟫
                        − ⟪A_{Xᴴ}Uᴴ, A_{Yᴴ}Zᴴ⟫ + ⟪A_{Yᴴ}Uᴴ, A_{Xᴴ}Zᴴ⟫
                        + 2 ⟪A_{Zᴴ}Uᴴ, A_{Xᴴ}Yᴴ⟫.

Two things happen relative to the vector relation
`horizontalProjection_curvature_horizontalLiftField_of_mdiffAt`.

* **`𝓗` disappears.** `⟪𝓗R(Xᴴ,Yᴴ)Zᴴ, Uᴴ⟫ = ⟪R(Xᴴ,Yᴴ)Zᴴ, Uᴴ⟫` because `Uᴴ` is horizontal
  (`tangentMetric_horizontalProjection_left_of_mem_horizontalSpace`). This is what makes the scalar
  form the useful one: it is a statement about the curvature of `M`, with no projection in it.
* **The `A`-compositions become pairings of `A`-values.** Each of the three composed terms is
  unfolded by **skew-symmetry alone** (`tangentMetric_oneillA_skew`, O'Neill's property 1′):

      ⟪A_{Xᴴ}(A_{Yᴴ}Zᴴ), Uᴴ⟫ = −⟪A_{Xᴴ}Uᴴ, A_{Yᴴ}Zᴴ⟫

  and likewise for the other two. **Alternation (`oneillA_swap_neg`) is not used**; the three
  identities are instances of one skew-symmetry statement with the composed field in the field slot
  and `Uᴴ` in the test slot.

The three sign flips against the vector relation's `+ A_X(A_Y Z) − A_Y(A_X Z) − 2 A_Z(A_X Y)` give
exactly `− ⟪A_X U, A_Y Z⟫ + ⟪A_Y U, A_X Z⟫ + 2 ⟪A_Z U, A_X Y⟫`; nothing was normalised.

**Regularity.** Every metric hypothesis is at `C^n`, `n ≥ 2`. `MDiffAt (T% (A_{Xᴴ}Yᴴ)) p` is still
required — not by the `𝓗`-drop, but by skew-symmetry itself, whose hypotheses are about the
*projections of both paired fields*, so applying it with `A_{Xᴴ}Yᴴ` in the field slot needs that
field differentiable at `p`. The scalar form therefore does **not** avoid the regularity of
`A_{Xᴴ}Yᴴ` as a field; it needs it at exactly the strength the discharged vector relation does.
-/
theorem tangentMetric_curvature_horizontalLiftField {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    (hX : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% X) q)
    (hY : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q)
    (hZ : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Z) q)
    (hU : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% U) q)
    (hAXY : MDiffAt (T% (oneillA I J f (horizontalLiftField I J f X)
      (horizontalLiftField I J f Y))) p)
    (hHYZ : MDiffAt (T% (horizontalLeviCivita I J f (horizontalLiftField I J f Y)
      (horizontalLiftField I J f Z))) p)
    (hAYZ : MDiffAt (T% (oneillA I J f (horizontalLiftField I J f Y)
      (horizontalLiftField I J f Z))) p)
    (hHXZ : MDiffAt (T% (horizontalLeviCivita I J f (horizontalLiftField I J f X)
      (horizontalLiftField I J f Z))) p)
    (hAXZ : MDiffAt (T% (oneillA I J f (horizontalLiftField I J f X)
      (horizontalLiftField I J f Z))) p) :
    tangentMetric I M p
        (curvature (leviCivita (tangentMetric I M)) (horizontalLiftField I J f X)
          (horizontalLiftField I J f Y) (horizontalLiftField I J f Z) p)
        (horizontalLiftField I J f U p)
      = tangentMetric I M p (oneillHorizontalCurvature I J f X Y Z p)
            (horizontalLiftField I J f U p)
        - tangentMetric I M p
            (oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f U) p)
            (oneillA I J f (horizontalLiftField I J f Y) (horizontalLiftField I J f Z) p)
        + tangentMetric I M p
            (oneillA I J f (horizontalLiftField I J f Y) (horizontalLiftField I J f U) p)
            (oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Z) p)
        + 2 * tangentMetric I M p
            (oneillA I J f (horizontalLiftField I J f Z) (horizontalLiftField I J f U) p)
            (oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Y) p) := by
  have hn0 := coe_ne_zero_of_minSmoothness_two_le hn
  have hgm : IsMDiffMetric E (tangentMetric I M) :=
    IsContMDiffMetricSection.isMDiffMetric hn0 hgM
  have hUd : MDiffAt (T% (horizontalLiftField I J f U)) p :=
    (contMDiffAt_horizontalLiftField isOpen_univ (Set.mem_univ p) hf.contMDiffOn (hgM p)
      (hgB (f p)) (hU (f p))).mdifferentiableAt hn0
  have hUhor : IsHorizontalField I J f (horizontalLiftField I J f U) :=
    isHorizontalField_horizontalLiftField
  have hHU := mdiffAt_horizontalPart_of_isHorizontalField (p := p) hUhor hUd
  have hVU := mdiffAt_verticalPart_of_isHorizontalField (p := p) hUhor hUd
  have hAYZv : IsVerticalField I J f
      (oneillA I J f (horizontalLiftField I J f Y) (horizontalLiftField I J f Z)) :=
    isVerticalField_oneillA_horizontalLiftField
  have hAXZv : IsVerticalField I J f
      (oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Z)) :=
    isVerticalField_oneillA_horizontalLiftField
  have hAXYv : IsVerticalField I J f
      (oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Y)) :=
    isVerticalField_oneillA_horizontalLiftField
  have s1 := tangentMetric_oneillA_skew (p := p) (I := I) (J := J) (f := f)
    (D := horizontalLiftField I J f X)
    (F := oneillA I J f (horizontalLiftField I J f Y) (horizontalLiftField I J f Z))
    (G := horizontalLiftField I J f U) hgm
    (mdiffAt_horizontalPart_of_isVerticalField hAYZv)
    (mdiffAt_verticalPart_of_isVerticalField hAYZv hAYZ) hHU hVU
  have s2 := tangentMetric_oneillA_skew (p := p) (I := I) (J := J) (f := f)
    (D := horizontalLiftField I J f Y)
    (F := oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Z))
    (G := horizontalLiftField I J f U) hgm
    (mdiffAt_horizontalPart_of_isVerticalField hAXZv)
    (mdiffAt_verticalPart_of_isVerticalField hAXZv hAXZ) hHU hVU
  have s3 := tangentMetric_oneillA_skew (p := p) (I := I) (J := J) (f := f)
    (D := horizontalLiftField I J f Z)
    (F := oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Y))
    (G := horizontalLiftField I J f U) hgm
    (mdiffAt_horizontalPart_of_isVerticalField hAXYv)
    (mdiffAt_verticalPart_of_isVerticalField hAXYv hAXY) hHU hVU
  have hdrop : tangentMetric I M p
        (curvature (leviCivita (tangentMetric I M)) (horizontalLiftField I J f X)
          (horizontalLiftField I J f Y) (horizontalLiftField I J f Z) p)
        (horizontalLiftField I J f U p)
      = tangentMetric I M p (horizontalProjection I J f p
          (curvature (leviCivita (tangentMetric I M)) (horizontalLiftField I J f X)
            (horizontalLiftField I J f Y) (horizontalLiftField I J f Z) p))
        (horizontalLiftField I J f U p) :=
    (tangentMetric_horizontalProjection_left_of_mem_horizontalSpace _ (hUhor p)).symm
  rw [hdrop, horizontalProjection_curvature_horizontalLiftField_of_mdiffAt hn hn' hf hgM hgB
    hsub hriem hX hY hZ hAXY hHYZ hAYZ hHXZ hAXZ]
  simp only [map_sub, map_add, map_smul, sub_apply, add_apply, smul_apply, smul_eq_mul]
  linarith [s1, s2, s3]

end RiemannianGeometry
