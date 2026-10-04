/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import RiemannianGeometry.Curvature
import RiemannianGeometry.ONeillLemmaTwo

/-!
# O'Neill's horizontal curvature equation, in vector form

O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. **13** (1966) 459–469,
proves on p. 464 the **dual Gauss equation**. His proof factors through a vector identity,
displayed there as his equation `(4)`:

    𝓗R_XY Z = −[∇*_X, ∇*_Y]Z + 2 A_Z A_X Y − A_X A_Y Z + A_Y A_X Z

for horizontal `X`, `Y`, `Z`; the braced `{4}` of his Theorem 2 is the *scalar* consequence
obtained by pairing this against a fourth horizontal field `H`. This file proves the vector
identity, for basic fields, in this project's conventions.

## The two numbering streams, and which one this is

## Convention translation, and why the signs are these

Two conventions differ from the source and both are recorded in `ONEILL_EQUATIONS.md` §7a.

* **Curvature sign.** O'Neill's `R_XY Z = ∇_{[X,Y]}Z − ∇_X∇_YZ + ∇_Y∇_XZ` (p. 464, eq. (1)) is
  **minus** `RiemannianGeometry.curvature`. Multiplying his `(4)` through by `−1` gives the statement
  proved here.
* **Direction last.** `leviCivita g F z v` is `(∇_v F)(z)`, so the differentiated field is the
  *second* argument and the direction the *last*. In `oneillA I J f D F` the direction is the
  *first* argument and the differentiated field the second. `A_Z A_X Y` is therefore
  `oneillA I J f Zᴴ (oneillA I J f Xᴴ Yᴴ)`.
* **`∇*` is `𝓗∇`.** O'Neill writes on p. 464 "we write the basic vector field `𝓗∇_Y Z` as
  `∇*_Y Z`", so his `∇*∇*` *is* `𝓗∇𝓗∇` and no push-forward to the base occurs in his eq. `(4)`.
  `horizontalLeviCivita` is that operator, read on the total space.

After translation the identity proved is

    𝓗R(Xᴴ, Yᴴ)Zᴴ = R^H(X, Y)Z + A_{Xᴴ}(A_{Yᴴ}Zᴴ) − A_{Yᴴ}(A_{Xᴴ}Zᴴ) − 2 A_{Zᴴ}(A_{Xᴴ}Yᴴ)

with `R^H` the horizontal-connection curvature `oneillHorizontalCurvature`.

## Main definitions

* `horizontalLeviCivita I J f D F` — the field `𝓗∇_D F`, O'Neill's `∇*` on basic fields.
* `oneillHorizontalCurvature I J f X Y Z` — the curvature of `𝓗∇` on basic fields,
  `R^H(X, Y)Z = 𝓗∇_{Xᴴ}(𝓗∇_{Yᴴ}Zᴴ) − 𝓗∇_{Yᴴ}(𝓗∇_{Xᴴ}Zᴴ) − 𝓗∇_{([X,Y])ᴴ}Zᴴ`.

## Main results

* `horizontalLeviCivita_vertical_horizontalLiftField` — **the final clause of O'Neill's Lemma 3**
  (p. 461): `𝓗∇_V X = A_X V` for `V` vertical and `X` basic. The project had Lemma 3(1)–(4) but
  not this clause, and Step 3 below cannot be done without it.
* `leviCivita_horizontalLiftField_eq_add_oneillA` — **Step 1**, `∇_{Yᴴ}Zᴴ = 𝓗∇_{Yᴴ}Zᴴ + A_{Yᴴ}Zᴴ`
  as an identity of *sections*, which is what the outer derivative consumes.
* `horizontalProjection_leviCivita_leviCivita_horizontalLiftField` — **Step 2**,
  `𝓗∇_{Xᴴ}(∇_{Yᴴ}Zᴴ) = 𝓗∇_{Xᴴ}(𝓗∇_{Yᴴ}Zᴴ) + A_{Xᴴ}(A_{Yᴴ}Zᴴ)`.
* `horizontalProjection_leviCivita_mlieBracket_horizontalLiftField` — **Step 3**, the bracket term
  `𝓗∇_{[Xᴴ,Yᴴ]}Zᴴ = 𝓗∇_{([X,Y])ᴴ}Zᴴ + 2 A_{Zᴴ}(A_{Xᴴ}Yᴴ)`.
* `horizontalProjection_curvature_horizontalLiftField` — **the identity**, assembled.

Steps 1, 2, 3 are kept separate on purpose: each corresponds to one move in O'Neill's proof, and
inlining them would make the source correspondence unauditable.

## Where the coefficient `2` comes from

Entirely from Step 3, and entirely from **Lemma 2**. `[Xᴴ,Yᴴ]` splits as
`𝓗[Xᴴ,Yᴴ] + 𝓥[Xᴴ,Yᴴ] = ([X,Y])ᴴ + 2 A_{Xᴴ}Yᴴ`, the second summand by
`oneillA_horizontalLiftField_eq_two_inv_smul_verticalProjection_mlieBracket` inverted. Linearity of
`leviCivita` in the direction then carries the `2` out, and the final clause of Lemma 3 turns
`𝓗∇_{A_{Xᴴ}Yᴴ}Zᴴ` into `A_{Zᴴ}(A_{Xᴴ}Yᴴ)`. **If Lemma 2's constant were wrong this coefficient
would be wrong**, and nothing else in the file would notice.

## What is deliberately *not* here

## Regularity, and one hypothesis that is *not* discharged at `C²`

There is however one hypothesis that the present API cannot discharge at metrics `C²`, and it is
recorded here rather than hidden. `horizontalProjection_leviCivita_mlieBracket_horizontalLiftField`
takes

    hAe : ∀ᶠ z in 𝓝 p, ContMDiffAt I I.tangent n (T% (oneillA I J f Xᴴ Yᴴ)) z

## Instance and spelling notes

Everything metric-valued is written with `tangentMetric I M p`, never `inner ℝ`, following
`RiemannianGeometry.ONeillTensors`; the two are `rfl`-equal but distinct atoms to every tactic.
`horizontalProjection_add_verticalProjection` is bound with its full expected type before use — a
bare application leaves `ChartedSpace ?m ?m` stuck.
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
  {f : M → B} {p : M} {X Y Z : Π q : B, TangentSpace J q}
  {V W : Π z : M, TangentSpace I z}

/-! ## The horizontal covariant derivative, O'Neill's `∇*` -/

variable (I J f) in
/-- **The horizontal part of the covariant derivative**, `𝓗∇_D F`, as a section of `TM`.

On basic fields this is O'Neill's `∇*`: he writes on p. 464 "we write the basic vector field
`𝓗∇_Y Z` as `∇*_Y Z`", so `∇*` never leaves the total space and no push-forward is involved. It is
defined for arbitrary `D`, `F` because the outer derivative of Step 2 must differentiate it as a
section, and because nothing below needs `D` or `F` restricted.

The direction is the **last** argument of `leviCivita`, so `D` — the direction — appears there and
`F` — the differentiated field — in the section slot. -/
def horizontalLeviCivita (D F : Π z : M, TangentSpace I z) : Π z : M, TangentSpace I z :=
  horizontalPart I J f (fun z ↦ leviCivita (tangentMetric I M) F z (D z))

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B]
  [Bundle.RiemannianBundle (TangentSpace J : B → Type _)] in
/-- `𝓗∇_D F` evaluated at a point, by `rfl`. This is the canonical specification: every result
below is derived from it and never from the definition body. -/
theorem horizontalLeviCivita_apply (D F : Π z : M, TangentSpace I z) (z : M) :
    horizontalLeviCivita I J f D F z
      = horizontalProjection I J f z (leviCivita (tangentMetric I M) F z (D z)) := rfl

variable (I J f) in
/-- **The curvature of the horizontal covariant derivative on basic fields**,

    R^H(X, Y)Z = 𝓗∇_{Xᴴ}(𝓗∇_{Yᴴ}Zᴴ) − 𝓗∇_{Yᴴ}(𝓗∇_{Xᴴ}Zᴴ) − 𝓗∇_{([X,Y])ᴴ}Zᴴ.

This is O'Neill's `∇*∇*` read **intrinsically on the total space**. His eq. `(4)` (p. 464) writes
the corresponding term as `−[∇*_X, ∇*_Y]Z` after arranging `𝓗[X,Y] = 0`; keeping the bracket term
explicit — with `𝓗[Xᴴ,Yᴴ] = ([X,Y])ᴴ` supplied by Lemma 1(2) rather than arranged away — makes the
definition unconditional and the arrangement unnecessary.

-/
def oneillHorizontalCurvature (X Y Z : Π q : B, TangentSpace J q) (p : M) : TangentSpace I p :=
  horizontalLeviCivita I J f (horizontalLiftField I J f X)
      (horizontalLeviCivita I J f (horizontalLiftField I J f Y)
        (horizontalLiftField I J f Z)) p
    - horizontalLeviCivita I J f (horizontalLiftField I J f Y)
      (horizontalLeviCivita I J f (horizontalLiftField I J f X)
        (horizontalLiftField I J f Z)) p
    - horizontalLeviCivita I J f (horizontalLiftField I J f (mlieBracket J X Y))
      (horizontalLiftField I J f Z) p

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- `R^H` unfolded, by `rfl`. -/
theorem oneillHorizontalCurvature_apply (X Y Z : Π q : B, TangentSpace J q) (p : M) :
    oneillHorizontalCurvature I J f X Y Z p =
      horizontalLeviCivita I J f (horizontalLiftField I J f X)
          (horizontalLeviCivita I J f (horizontalLiftField I J f Y)
            (horizontalLiftField I J f Z)) p
        - horizontalLeviCivita I J f (horizontalLiftField I J f Y)
          (horizontalLeviCivita I J f (horizontalLiftField I J f X)
            (horizontalLiftField I J f Z)) p
        - horizontalLeviCivita I J f (horizontalLiftField I J f (mlieBracket J X Y))
          (horizontalLiftField I J f Z) p := rfl

/-! ## Step 0: the final clause of O'Neill's Lemma 3 -/

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B]
  [Bundle.RiemannianBundle (TangentSpace J : B → Type _)] in
/-- **`𝓗∇_V W = A_W V` whenever `[V, W]` is vertical**, for `V` a vertical field and `W` a
horizontal one. This is the mathematical content of the final clause of O'Neill's Lemma 3 with its
one nontrivial input isolated as a hypothesis.

The proof is torsion-freeness and nothing else: `∇_V W = ∇_W V + [V, W]`
(`leviCivita_sub_swap`), the bracket dies under `𝓗` by hypothesis, and `𝓗∇_W V = A_W V` is
Lemma 3(3) (`oneillA_horizontal_vertical`), which carries no hypothesis at all. -/
theorem horizontalLeviCivita_eq_oneillA_of_mem_verticalSpace_mlieBracket
    (hgm : IsMDiffMetric E (tangentMetric I M)) (hVvert : IsVerticalField I J f V)
    (hWhor : IsHorizontalField I J f W)
    (hVd : MDiffAt (T% V) p) (hWd : MDiffAt (T% W) p)
    (hbr : mlieBracket I V W p ∈ verticalSpace I J f p) :
    horizontalLeviCivita I J f V W p = oneillA I J f W V p := by
  have hswap := leviCivita_sub_swap (g := tangentMetric I M) (X := V) (Y := W) (x := p)
    isSymm_tangentMetric isNondegenerate_tangentMetric hgm hVd hWd
  have hsum : leviCivita (tangentMetric I M) W p (V p)
      = leviCivita (tangentMetric I M) V p (W p) + mlieBracket I V W p := by
    rw [← hswap]; abel
  rw [horizontalLeviCivita_apply, hsum, map_add,
    horizontalProjection_eq_zero_of_mem_verticalSpace hbr, add_zero,
    oneillA_horizontal_vertical hWhor hVvert]

/-- **The final clause of O'Neill's LEMMA 3** (ON1966, p. 461): *"Furthermore, if `X` is basic,
`𝓗∇_V X = A_X V`."*

    horizontalLeviCivita I J f V Xᴴ p = oneillA I J f Xᴴ V p

for `V` vertical and `Xᴴ` basic. The project already had Lemma 3(1)–(4); this clause was missing,
and Step 3 of the horizontal curvature equation cannot be done without it.

O'Neill's argument, in his words, is that `[V, X] = ∇_V X − ∇_X V` is vertical because `V` is
`π`-related to the zero field, so `𝓗∇_V X = 𝓗∇_X V`, which is `A_X V` by Lemma 3(3). Formally the
verticality of `[V, Xᴴ]` is `mem_verticalSpace_mlieBracket_horizontalLiftField`, whose proof rests
on bracket naturality for `f`-related fields — the one step O'Neill treats as standard and which is
a theorem with a nontrivial proof here.
-/
theorem horizontalLeviCivita_vertical_horizontalLiftField {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hgm : IsMDiffMetric E (tangentMetric I M))
    (hf : ContMDiffAt I J ((n : ℕ∞ω)) f p)
    (hsub : ∀ᶠ z in 𝓝 p, IsSubmersionAtPoint I J f z)
    (hriem : ∀ᶠ z in 𝓝 p, IsRiemannianSubmersionAtPoint I J f z)
    (hV : IsVerticalField I J f V)
    (hVe : ∀ᶠ z in 𝓝 p, ContMDiffAt I I.tangent ((n : ℕ∞ω)) (T% V) z)
    (hXHe : ∀ᶠ z in 𝓝 p,
      ContMDiffAt I I.tangent ((n : ℕ∞ω)) (T% (horizontalLiftField I J f X)) z)
    (hX : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% X) q) :
    horizontalLeviCivita I J f V (horizontalLiftField I J f X) p
      = oneillA I J f (horizontalLiftField I J f X) V p := by
  have hn0 := coe_ne_zero_of_minSmoothness_two_le hn
  exact horizontalLeviCivita_eq_oneillA_of_mem_verticalSpace_mlieBracket hgm hV
    isHorizontalField_horizontalLiftField (hVe.self_of_nhds.mdifferentiableAt hn0)
    (hXHe.self_of_nhds.mdifferentiableAt hn0)
    (mem_verticalSpace_mlieBracket_horizontalLiftField hn hn' hf hsub hriem hV hVe hXHe hX)

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **`A_{Yᴴ}Zᴴ` is a vertical field**, from `oneillA_mem_verticalSpace_of_isHorizontalField`. This
is what lets the outer `𝓗∇` of Step 2 collapse to `A` by Lemma 3(3). -/
theorem isVerticalField_oneillA_horizontalLiftField :
    IsVerticalField I J f
      (oneillA I J f (horizontalLiftField I J f Y) (horizontalLiftField I J f Z)) := fun z ↦
  oneillA_mem_verticalSpace_of_isHorizontalField isHorizontalField_horizontalLiftField _ z

/-! ## Step 1: decomposing the inner derivative -/

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **Step 1**: `∇_{Yᴴ}Zᴴ = 𝓗∇_{Yᴴ}Zᴴ + A_{Yᴴ}Zᴴ`, as an identity of **sections** of `TM`.

This is O'Neill's Lemma 3(4) — `∇_X Y = 𝓗∇_X Y + A_X Y` for horizontal `X`, `Y` — read as a field
identity rather than pointwise, because Step 2 differentiates it. It needs no hypothesis
whatsoever: `horizontalPart_add_verticalPart` is unconditional and
`oneillA_horizontal_horizontal` (Lemma 3(4)) identifies the vertical part.
-/
theorem leviCivita_horizontalLiftField_eq_add_oneillA (Y Z : Π q : B, TangentSpace J q) :
    (fun z ↦ leviCivita (tangentMetric I M) (horizontalLiftField I J f Z) z
        (horizontalLiftField I J f Y z))
      = horizontalLeviCivita I J f (horizontalLiftField I J f Y) (horizontalLiftField I J f Z)
        + oneillA I J f (horizontalLiftField I J f Y) (horizontalLiftField I J f Z) := by
  have h := horizontalPart_add_verticalPart (I := I) (J := J) (f := f)
    (X := fun z ↦ leviCivita (tangentMetric I M) (horizontalLiftField I J f Z) z
      (horizontalLiftField I J f Y z))
  rw [← h]
  congr 1
  funext z
  exact (oneillA_horizontal_horizontal isHorizontalField_horizontalLiftField
    isHorizontalField_horizontalLiftField z).symm

/-! ## Step 2: differentiating again and projecting -/

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **Step 2**: `𝓗∇_{Xᴴ}(∇_{Yᴴ}Zᴴ) = 𝓗∇_{Xᴴ}(𝓗∇_{Yᴴ}Zᴴ) + A_{Xᴴ}(A_{Yᴴ}Zᴴ)`.

Step 1 splits the field being differentiated; `leviCivita_add_section` splits `∇` along that sum;
and the second summand collapses by Lemma 3(3) (`oneillA_horizontal_vertical`) because `A_{Yᴴ}Zᴴ`
is a **vertical** field. This is O'Neill's "another application of Lemma 3" on p. 464.

-/
theorem horizontalProjection_leviCivita_leviCivita_horizontalLiftField
    (hgm : IsMDiffMetric E (tangentMetric I M))
    (hHd : MDiffAt (T% (horizontalLeviCivita I J f (horizontalLiftField I J f Y)
      (horizontalLiftField I J f Z))) p)
    (hAd : MDiffAt (T% (oneillA I J f (horizontalLiftField I J f Y)
      (horizontalLiftField I J f Z))) p) :
    horizontalProjection I J f p
        (leviCivita (tangentMetric I M)
          (fun z ↦ leviCivita (tangentMetric I M) (horizontalLiftField I J f Z) z
            (horizontalLiftField I J f Y z)) p (horizontalLiftField I J f X p))
      = horizontalLeviCivita I J f (horizontalLiftField I J f X)
          (horizontalLeviCivita I J f (horizontalLiftField I J f Y)
            (horizontalLiftField I J f Z)) p
        + oneillA I J f (horizontalLiftField I J f X)
          (oneillA I J f (horizontalLiftField I J f Y) (horizontalLiftField I J f Z)) p := by
  rw [leviCivita_horizontalLiftField_eq_add_oneillA (I := I) (J := J) (f := f) Y Z,
    leviCivita_add_section isSymm_tangentMetric isNondegenerate_tangentMetric hgm hHd hAd,
    add_apply, map_add]
  congr 1
  exact (oneillA_horizontal_vertical isHorizontalField_horizontalLiftField
    isVerticalField_oneillA_horizontalLiftField p).symm

/-! ## Step 3: the bracket term -/

/-- **`𝓥[Xᴴ, Yᴴ] = 2 A_{Xᴴ}Yᴴ`**, Lemma 2 inverted.

Stated separately because this is the *only* place the constant `2` of the horizontal curvature
equation comes from, and reading it off a single named lemma keeps that visible.
-/
theorem verticalProjection_mlieBracket_horizontalLiftField_eq_two_smul_oneillA {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    (hX : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% X) q)
    (hY : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q) :
    verticalProjection I J f p
        (mlieBracket I (horizontalLiftField I J f X) (horizontalLiftField I J f Y) p)
      = (2 : ℝ) • oneillA I J f (horizontalLiftField I J f X)
          (horizontalLiftField I J f Y) p := by
  rw [oneillA_horizontalLiftField_eq_two_inv_smul_verticalProjection_mlieBracket hn hn' hf hgM
    hgB hsub hriem hX hY, smul_smul]
  norm_num

/-- **Step 3**: the bracket term of the curvature operator,

    𝓗∇_{[Xᴴ,Yᴴ]}Zᴴ = 𝓗∇_{([X,Y])ᴴ}Zᴴ + 2 A_{Zᴴ}(A_{Xᴴ}Yᴴ).

Three inputs, in order: `𝓗[Xᴴ,Yᴴ] = ([X,Y])ᴴ` (**Lemma 1(2)**), `𝓥[Xᴴ,Yᴴ] = 2 A_{Xᴴ}Yᴴ`
(**Lemma 2**), and `𝓗∇_V Zᴴ = A_{Zᴴ}V` for the vertical field `V = A_{Xᴴ}Yᴴ` (**Lemma 3**, final
clause). Between them, linearity of `leviCivita` in the direction carries the `2` out.

O'Neill instead *arranges* `𝓗[X,Y] = 0` ("we can assume that `X, Y, Z` are basic vector fields
whose brackets are vertical", p. 464), which removes the first term. Keeping it makes the identity
hold for all basic fields with no arrangement.

-/
theorem horizontalProjection_leviCivita_mlieBracket_horizontalLiftField {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    (hX : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% X) q)
    (hY : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q)
    (hZ : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Z) q)
    (hAe : ∀ᶠ z in 𝓝 p, ContMDiffAt I I.tangent ((n : ℕ∞ω))
      (T% (oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Y))) z) :
    horizontalProjection I J f p
        (leviCivita (tangentMetric I M) (horizontalLiftField I J f Z) p
          (mlieBracket I (horizontalLiftField I J f X) (horizontalLiftField I J f Y) p))
      = horizontalLeviCivita I J f (horizontalLiftField I J f (mlieBracket J X Y))
            (horizontalLiftField I J f Z) p
        + (2 : ℝ) • oneillA I J f (horizontalLiftField I J f Z)
            (oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Y)) p := by
  have hn0 := coe_ne_zero_of_minSmoothness_two_le hn
  have hgm : IsMDiffMetric E (tangentMetric I M) :=
    IsContMDiffMetricSection.isMDiffMetric hn0 hgM
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
    horizontalLeviCivita_vertical_horizontalLiftField hn hn' hgm hfp
      (Filter.Eventually.of_forall hsub) (Filter.Eventually.of_forall hriem)
      isVerticalField_oneillA_horizontalLiftField hAe (hlift Z hZ)
      (Filter.Eventually.of_forall hZ)]

/-! ## Step 4: the horizontal curvature equation -/

/-- **O'Neill's horizontal curvature equation, in vector form.** For basic fields `Xᴴ`, `Yᴴ`, `Zᴴ`,

    𝓗R(Xᴴ, Yᴴ)Zᴴ = R^H(X, Y)Z + A_{Xᴴ}(A_{Yᴴ}Zᴴ) − A_{Yᴴ}(A_{Xᴴ}Zᴴ) − 2 A_{Zᴴ}(A_{Xᴴ}Yᴴ).

-/
theorem horizontalProjection_curvature_horizontalLiftField {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    (hX : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% X) q)
    (hY : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q)
    (hZ : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Z) q)
    (hAe : ∀ᶠ z in 𝓝 p, ContMDiffAt I I.tangent ((n : ℕ∞ω))
      (T% (oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Y))) z)
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
    horizontalProjection_leviCivita_mlieBracket_horizontalLiftField hn hn' hf hgM hgB hsub hriem
      hX hY hZ hAe,
    oneillHorizontalCurvature_apply]
  abel

end RiemannianGeometry
