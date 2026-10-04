/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import RiemannianGeometry.ONeillHorizontalCurvature
import RiemannianGeometry.ONeillLemmaOne

/-!
# The lift of the second structural equation: `R^H` is the base curvature

O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. **13** (1966) 459–469,
p. 464, just before his equation `(4)`:

> By Lemma 1 and the definition of `R*` … the second structural equation of `B` lifts to `M` in
> the form `R*_XY Z = ∇*_{𝓗[X,Y]}Z − [∇*_X, ∇*_Y]Z`.

This file proves that identification for `RiemannianGeometry.oneillHorizontalCurvature`, the intrinsic
total-space operator

    R^H(X, Y)Z = 𝓗∇_{Xᴴ}(𝓗∇_{Yᴴ}Zᴴ) − 𝓗∇_{Yᴴ}(𝓗∇_{Xᴴ}Zᴴ) − 𝓗∇_{([X,Y])ᴴ}Zᴴ,

whose relation to the base curvature `RiemannianGeometry.curvature (leviCivita (tangentMetric J B))` was
deliberately deferred when `R^H` was defined.

## Why this needed a separate campaign, and what changed

**metric compatibility trades a covariant derivative for a directional derivative of a scalar, and
Lemma 1(1) transports scalars with no differentiability hypothesis at all.**

So the outer derivative is never pushed down as a connection identity. Instead
`isCompatibleWith_leviCivita` is applied **on `M`**, the resulting scalar derivative is transported
by `mvfderiv_tangentMetric_horizontalLiftField`, and `isCompatibleWith_leviCivita` is applied a
second time **on `B`** to reassemble `∇*_X(∇*_Y Z)`. The only differentiability of `∇*_Y Z` that
enters is `C¹`, which `contMDiffAt_leviCivita` supplies from `gB ∈ C²` and `Y, Z ∈ C²`.

**No metric hypothesis in this file exceeds `C²`**, and no third derivative of either metric is
taken anywhere in it.

## Main results, one per line of the derivation

* `tangentMetric_leviCivita_horizontalLiftField` — **the workhorse**, the single-derivative case
  `⟪∇_{Uᴴ}Vᴴ, Kᴴ⟫ = ⟪∇*_U V, K⟫ ∘ f`. It is Lemma 1(3) followed by Lemma 1(1), and it needs
  differentiability of **`V` alone**: neither the direction `U` nor the test field `K` carries any
  hypothesis (see "Two hypotheses that are not needed" below).
* `tangentMetric_horizontalLeviCivita_horizontalLiftField` — the same with the redundant outer `𝓗`
  in place, which is the shape `oneillHorizontalCurvature` is built from.
* `tangentMetric_horizontalLeviCivita_horizontalLeviCivita_horizontalLiftField` — **the
  two-derivative case**, `⟪𝓗∇_{Xᴴ}(𝓗∇_{Yᴴ}Zᴴ), Wᴴ⟫ = ⟪∇*_X(∇*_Y Z), W⟫ ∘ f`, by the compatibility
  route. This is the step the campaign exists for.
* `tangentMetric_oneillHorizontalCurvature_horizontalLiftField` — **the scalar identification**,
  `⟪R^H(X,Y)Z, Wᴴ p⟫ = ⟪R*(X,Y)Z, W⟫ (f p)`.
* `oneillHorizontalCurvature_eq_horizontalLiftField_curvature` — **the vector identification**,
  `R^H(X,Y)Z = (R*(X,Y)Z)ᴴ`, which the scalar form gives for free through nondegeneracy and
  `HorizontalLift.exists_basic_eq_horizontalProjection`.

Two regularity helpers are stated first: `two_le_of_minSmoothness_two_le`,
`contMDiffAt_leviCivita_apply_base` and `mdiffAt_horizontalLiftField_of_one`.

## Two hypotheses that are not needed, and why that matters

**The direction field.** `leviCivita g V x` is a continuous linear map applied to the direction's
value at `x`, and `horizontalLiftField I J f U p` depends only on `U (f p)`. So the direction may
be replaced by any base field with the same value at `f p`, and
`HorizontalLift.exists_basic_eq_of_mem_horizontalSpace` supplies a `C^m` one. Consequently
`tangentMetric_leviCivita_horizontalLiftField` assumes **nothing** about the direction, even though
Lemma 1(3) does.

**The test field.** The right-hand slot of the metric is never differentiated: Lemma 1(1) carries no
differentiability hypothesis and the outer `𝓗` is removed by self-adjointness of the projection
(`tangentMetric_horizontalProjection_left`), not discarded. So the workhorse's test field is free
too, which is what lets the two-derivative case pair `(∇*_Y Z)ᴴ` — a field known only to be `C¹` —
against `∇_{Xᴴ}Wᴴ`.

## Where the global hypotheses come from, and where they do not

`hsub`, `hriem`, `hX`, `hY`, `hZ` are global in the two-derivative case and below, for one reason:
the inner field `𝓗∇_{Yᴴ}Zᴴ` must be replaced by `(∇*_Y Z)ᴴ` **inside** `leviCivita`'s section slot,
and the only available form of that identity is
`ONeillLemmaOne.horizontalPart_leviCivita_horizontalLiftField`, an equality of fields on all of `M`.
An eventual form would suffice mathematically — `leviCivita g V x` depends only on the germ of `V`
at `x` — but no germ-congruence lemma for `leviCivita` exists in the tree, and adding one is not
this campaign. The global hypotheses match
`ONeillHorizontalCurvature.horizontalProjection_curvature_horizontalLiftField` exactly, so nothing
downstream is tightened by them.

**The fourth field `W` is different, and deliberately so.** Its hypothesis is taken
`∀ᶠ q in 𝓝 (f p)`, because in the vector identification it is produced by
`HorizontalLift.exists_basic_eq_horizontalProjection`, which supplies a basic field only on a
neighbourhood of `f p`. A globally-quantified hypothesis there would make the vector form
unprovable.

## Regularity accounting

* both metrics `C²` — `hgM`, `hgB` at `(n : ℕ∞ω)`. Used at `C²` by Lemma 1(3) and by
  `contMDiffAt_leviCivita` (which spends the one derivative of the Koszul formula), and at `C¹` by
  `IsMDiffMetric` for compatibility and by the lift of `∇*_Y Z`;
* submersion `C³` — `hf` at `(n + 1 : ℕ∞)`. The `+1` is the derivative of `dπ`;
* base fields `X`, `Y`, `Z`, `W` at `C²`;
* **`∇*_Y Z` at `C¹` only**, derived, never assumed.

`contMDiffAt_leviCivita` takes its metric hypothesis as a `ContMDiffOn` on an open set rather than
as an `IsContMDiffMetricSection`; `contMDiffAt_leviCivita_apply_base` performs that conversion on
`univ` once, so no statement below has to be shaped around it.
-/

noncomputable section

open Bundle VectorField Set
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
  {f : M → B} {p : M} {X Y Z W : Π q : B, TangentSpace J q}

/-! ## Three regularity facts, isolated -/

omit [FiniteDimensional ℝ E] [ChartedSpace H M] [IsManifold I ∞ M] [FiniteDimensional ℝ E']
  [ChartedSpace H' B] [IsManifold J ∞ B]
  [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]
  [Bundle.RiemannianBundle (TangentSpace J : B → Type _)] in
/-- **`minSmoothness ℝ 2 ≤ n` gives `2 ≤ n` in `ℕ∞`.**

`ONeillLemmaTwo.coe_ne_zero_of_minSmoothness_two_le` extracts `n ≠ 0` from the same hypothesis;
this extracts the inequality itself, which is what the `of_le` steps below need. `norm_cast`
cannot cross `ℕ∞ → ℕ∞ω` here on its own, so `WithTop.coe_le_coe` is applied explicitly. -/
theorem two_le_of_minSmoothness_two_le {n : ℕ∞} (hn : minSmoothness ℝ 2 ≤ n) : (2 : ℕ∞) ≤ n := by
  simp only [minSmoothness_of_isRCLikeNormedField] at hn
  exact WithTop.coe_le_coe.mp (by simpa using hn)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [Bundle.RiemannianBundle (TangentSpace I : M → Type _)] in
/-- **`∇*_Y Z` is `C¹` when `gB` is `C²` and `Y`, `Z` are `C²`.**

This is the one place the whole campaign turns on: the second covariant derivative of the
derivation is applied to a field known only to be **`C¹`**, and this lemma is what supplies that
`C¹` from a `C²` base metric. `contMDiffAt_leviCivita` at `m := 1` gives the `Hom(TB, TB)`-section
`∇*Z` at `C¹`, and `ContMDiffAt.clm_bundle_apply` evaluates it on `Y`.

`contMDiffAt_leviCivita` wants its metric and its differentiated field as `ContMDiffOn`s on an open
set, not as the section predicates used elsewhere; the conversion is done here on `univ`, once, so
that no statement downstream has to be shaped around it. -/
theorem contMDiffAt_leviCivita_apply_base {n : ℕ∞} (hn : minSmoothness ℝ 2 ≤ n)
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hY : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q)
    (hZ : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Z) q) (q : B) :
    ContMDiffAt J J.tangent (((1 : ℕ∞) : ℕ∞ω))
      (T% (fun q' ↦ leviCivita (tangentMetric J B) Z q' (Y q'))) q := by
  have hn2 := two_le_of_minSmoothness_two_le hn
  have h2 : ((2 : ℕ∞) : ℕ∞ω) ≤ ((n : ℕ∞ω)) := WithTop.coe_le_coe.mpr hn2
  have h1 : ((1 : ℕ∞) : ℕ∞ω) ≤ ((n : ℕ∞ω)) :=
    WithTop.coe_le_coe.mpr (le_trans (by norm_num) hn2)
  have hgB2 : ContMDiffOn J (J.prod 𝓘(ℝ, E' →L[ℝ] E' →L[ℝ] ℝ)) ((2 : ℕ∞))
      (fun q' ↦ TotalSpace.mk' (E' →L[ℝ] E' →L[ℝ] ℝ)
        (E := fun (q' : B) ↦ TangentSpace J q' →L[ℝ] TangentSpace J q' →L[ℝ] ℝ) q'
        (tangentMetric J B q')) univ :=
    fun q' _ ↦ ((hgB q').of_le h2).contMDiffWithinAt
  have hZ2 : CMDiff[univ] ((2 : ℕ∞)) (T% Z) := fun q' _ ↦ ((hZ q').of_le h2).contMDiffWithinAt
  exact ContMDiffAt.clm_bundle_apply
    (contMDiffAt_leviCivita (m := 1) isOpen_univ (mem_univ q) isSymm_tangentMetric
      isNondegenerate_tangentMetric hgB2 hZ2) ((hY q).of_le h1)

omit [FiniteDimensional ℝ E'] in
/-- **A basic field is differentiable at `p` as soon as its base field is `C¹` at `f p`.**

`contMDiffAt_horizontalLiftField` at `m := 1`: `f ∈ C²` and both metrics `C¹` suffice, and both are
implied by the campaign's `hf`, `hgM`, `hgB` at `n ≥ 2`. Stated separately because the
two-derivative case needs it for `(∇*_Y Z)ᴴ`, whose base field is only `C¹` — the order-`n` route
used everywhere else in `ONeillLemmaOne` is unavailable there. -/
theorem mdiffAt_horizontalLiftField_of_one {n : ℕ∞} (hn : minSmoothness ℝ 2 ≤ n)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hZ : ContMDiffAt J J.tangent (((1 : ℕ∞) : ℕ∞ω)) (T% Z) (f p)) :
    MDiffAt (T% (horizontalLiftField I J f Z)) p := by
  have hn2 := two_le_of_minSmoothness_two_le hn
  have h1n : (1 : ℕ∞) ≤ n := le_trans (by norm_num) hn2
  have h1 : ((1 : ℕ∞) : ℕ∞ω) ≤ ((n : ℕ∞ω)) := WithTop.coe_le_coe.mpr h1n
  have hf2 : ContMDiffOn I J (((1 : ℕ∞) + 1 : ℕ∞)) f univ :=
    (hf.of_le (WithTop.coe_le_coe.mpr (by gcongr))).contMDiffOn
  exact (contMDiffAt_horizontalLiftField (m := 1) isOpen_univ (mem_univ p) hf2
    ((hgM p).of_le h1) ((hgB (f p)).of_le h1) hZ).mdifferentiableAt (by simp)

/-! ## The workhorse: one covariant derivative -/

/-- **`⟪∇_{Uᴴ} Vᴴ, Kᴴ⟫ p = ⟪∇*_U V, K⟫ (f p)`** — the single-derivative case.

This is O'Neill's Lemma 1(3) followed by his Lemma 1(1), and it is the identity every other
statement in this file is assembled from. Three things happen and each is a named lemma:

1. the direction `U` is replaced by a `C^n` basic field with the same value at `f p`
   (`exists_basic_eq_of_mem_horizontalSpace`, legitimate because `leviCivita` is linear in the
   direction and `horizontalLiftField I J f U p` depends only on `U (f p)`);
2. an outer `𝓗` is **inserted** — not discarded — using self-adjointness of the projection
   (`tangentMetric_horizontalProjection_left`) and horizontality of `Kᴴ p`, after which
   `horizontalProjection_leviCivita_horizontalLiftField` is Lemma 1(3);
3. `tangentMetric_horizontalLiftField_apply` is Lemma 1(1), which carries no differentiability
   hypothesis.

**Only `V` carries a regularity hypothesis.** The direction `U` and the test field `K` carry none:
see the module docstring for why that is what makes the rest of the file possible at `C²`. -/
theorem tangentMetric_leviCivita_horizontalLiftField {n : ℕ∞}
    {U V K : Π q : B, TangentSpace J q}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ᶠ z in 𝓝 p, IsSubmersionAtPoint I J f z)
    (hriem : ∀ᶠ z in 𝓝 p, IsRiemannianSubmersionAtPoint I J f z)
    (hV : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% V) q) :
    tangentMetric I M p (leviCivita (tangentMetric I M) (horizontalLiftField I J f V) p
        (horizontalLiftField I J f U p)) (horizontalLiftField I J f K p)
      = tangentMetric J B (f p) (leviCivita (tangentMetric J B) V (f p) (U (f p))) (K (f p)) := by
  obtain ⟨U', hU', hU'p⟩ := exists_basic_eq_of_mem_horizontalSpace (m := n)
    hsub.self_of_nhds hriem.self_of_nhds (horizontalLiftField_mem (Y := U) p)
  have hU'val : U' (f p) = U (f p) := by
    have h := congrArg (fun v ↦ mfderiv I J f p v) hU'p
    simpa only [mfderiv_horizontalLiftField hsub.self_of_nhds hriem.self_of_nhds] using h
  rw [← hU'p, ← hU'val]
  calc tangentMetric I M p (leviCivita (tangentMetric I M) (horizontalLiftField I J f V) p
          (horizontalLiftField I J f U' p)) (horizontalLiftField I J f K p)
      = tangentMetric I M p (horizontalProjection I J f p (leviCivita (tangentMetric I M)
          (horizontalLiftField I J f V) p (horizontalLiftField I J f U' p)))
          (horizontalLiftField I J f K p) := by
        rw [tangentMetric_horizontalProjection_left,
          mem_horizontalSpace_iff_horizontalProjection_eq_self.mp
            (horizontalLiftField_mem (Y := K) p)]
    _ = tangentMetric I M p (horizontalLiftField I J f
          (fun q ↦ leviCivita (tangentMetric J B) V q (U' q)) p)
          (horizontalLiftField I J f K p) := by
        rw [horizontalProjection_leviCivita_horizontalLiftField hn hn' hf hgM hgB hsub hriem
          hU' hV]
    _ = tangentMetric J B (f p) (leviCivita (tangentMetric J B) V (f p) (U' (f p))) (K (f p)) :=
        tangentMetric_horizontalLiftField_apply hsub.self_of_nhds hriem.self_of_nhds

/-- **`⟪𝓗∇_{Uᴴ} Vᴴ, Kᴴ⟫ p = ⟪∇*_U V, K⟫ (f p)`** — the workhorse in the shape
`oneillHorizontalCurvature` is built from.

The outer `𝓗` of `horizontalLeviCivita` is invisible to the pairing against a horizontal `Kᴴ p`,
by self-adjointness of the projection. This is the third term of `R^H` verbatim, with the direction
`U := [X, Y]`, and it consumes **no** hypothesis on that bracket. -/
theorem tangentMetric_horizontalLeviCivita_horizontalLiftField {n : ℕ∞}
    {U V K : Π q : B, TangentSpace J q}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ᶠ z in 𝓝 p, IsSubmersionAtPoint I J f z)
    (hriem : ∀ᶠ z in 𝓝 p, IsRiemannianSubmersionAtPoint I J f z)
    (hV : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% V) q) :
    tangentMetric I M p (horizontalLeviCivita I J f (horizontalLiftField I J f U)
        (horizontalLiftField I J f V) p) (horizontalLiftField I J f K p)
      = tangentMetric J B (f p) (leviCivita (tangentMetric J B) V (f p) (U (f p))) (K (f p)) := by
  rw [horizontalLeviCivita_apply, tangentMetric_horizontalProjection_left,
    mem_horizontalSpace_iff_horizontalProjection_eq_self.mp (horizontalLiftField_mem (Y := K) p)]
  exact tangentMetric_leviCivita_horizontalLiftField hn hn' hf hgM hgB hsub hriem hV

/-! ## Two covariant derivatives, by metric compatibility -/

/-- **`⟪𝓗∇_{Xᴴ}(𝓗∇_{Yᴴ}Zᴴ), Wᴴ⟫ p = ⟪∇*_X(∇*_Y Z), W⟫ (f p)`** — the two-derivative case, and the
step this campaign exists for.

    ⟪∇_{Xᴴ}((∇*_Y Z)ᴴ), Wᴴ⟫
      = Xᴴ⟪(∇*_Y Z)ᴴ, Wᴴ⟫ − ⟪(∇*_Y Z)ᴴ, ∇_{Xᴴ}Wᴴ⟫        -- `e1`, compatibility on `M`
      = (X⟪∇*_Y Z, W⟫) ∘ f  − ⟪(∇*_Y Z)ᴴ, ∇_{Xᴴ}Wᴴ⟫        -- `e2`, Lemma 1(1) + chain rule
      = (X⟪∇*_Y Z, W⟫) ∘ f  − ⟪∇*_Y Z, ∇*_X W⟫ ∘ f         -- `e3`, the workhorse
      = ⟪∇*_X(∇*_Y Z), W⟫ ∘ f                              -- `e4`, compatibility on `B`

`e1` and `e4` are `isCompatibleWith_leviCivita` on `M` and on `B`; since `IsCompatibleWith` is a
plain `def`, each is bound to a `have` with named binders before use. `e2` is
`ONeillLemmaOne.mvfderiv_tangentMetric_horizontalLiftField`, which is Lemma 1(1) in its eventual
form followed by the chain rule and relatedness. `e3` is the workhorse above, applied with the
**test slot** holding `∇*_Y Z` — which is exactly why the workhorse had to be free of hypotheses
there.

**`∇*_Y Z` is used only at `C¹`**: for `e1` (through the lift,
`mdiffAt_horizontalLiftField_of_one`), for `e2`'s pairing, and for `e4`. It is never fed to Lemma
1(3), which is what would have forced `gB ∈ C³`. -/
theorem tangentMetric_horizontalLeviCivita_horizontalLeviCivita_horizontalLiftField {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    (hY : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q)
    (hZ : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Z) q)
    (hW : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% W) q) :
    tangentMetric I M p (horizontalLeviCivita I J f (horizontalLiftField I J f X)
        (horizontalLeviCivita I J f (horizontalLiftField I J f Y)
          (horizontalLiftField I J f Z)) p) (horizontalLiftField I J f W p)
      = tangentMetric J B (f p) (leviCivita (tangentMetric J B)
          (fun q ↦ leviCivita (tangentMetric J B) Z q (Y q)) (f p) (X (f p))) (W (f p)) := by
  have hn0 := coe_ne_zero_of_minSmoothness_two_le hn
  have hgmM : IsMDiffMetric E (tangentMetric I M) :=
    IsContMDiffMetricSection.isMDiffMetric hn0 hgM
  have hgmB : IsMDiffMetric E' (tangentMetric J B) :=
    IsContMDiffMetricSection.isMDiffMetric hn0 hgB
  have hsube : ∀ᶠ z in 𝓝 p, IsSubmersionAtPoint I J f z := Filter.Eventually.of_forall hsub
  have hrieme : ∀ᶠ z in 𝓝 p, IsRiemannianSubmersionAtPoint I J f z :=
    Filter.Eventually.of_forall hriem
  have hle : ((n : ℕ∞ω)) ≤ (((n + 1 : ℕ∞)) : ℕ∞ω) := by push_cast; exact le_self_add
  have hfd : MDiffAt f p := ((hf p).of_le hle).mdifferentiableAt hn0
  -- Lemma 1(3) as an equality of fields: the inner `𝓗∇_{Yᴴ}Zᴴ` **is** `(∇*_Y Z)ᴴ`.
  have hfield : horizontalLeviCivita I J f (horizontalLiftField I J f Y)
      (horizontalLiftField I J f Z)
      = horizontalLiftField I J f (fun q ↦ leviCivita (tangentMetric J B) Z q (Y q)) :=
    horizontalPart_leviCivita_horizontalLiftField hn hn' hf hgM hgB hsub hriem hY hZ
  -- the `C¹` regularity of `∇*_Y Z`, and the four `MDiffAt` facts it yields
  have hS1 : ContMDiffAt J J.tangent (((1 : ℕ∞) : ℕ∞ω))
      (T% (fun q ↦ leviCivita (tangentMetric J B) Z q (Y q))) (f p) :=
    contMDiffAt_leviCivita_apply_base hn hgB hY hZ (f p)
  have hSd : MDiffAt (T% (fun q ↦ leviCivita (tangentMetric J B) Z q (Y q))) (f p) :=
    hS1.mdifferentiableAt (by simp)
  have hWd : MDiffAt (T% W) (f p) := hW.self_of_nhds.mdifferentiableAt hn0
  have hSHd : MDiffAt (T% (horizontalLiftField I J f
      (fun q ↦ leviCivita (tangentMetric J B) Z q (Y q)))) p :=
    mdiffAt_horizontalLiftField_of_one hn hf hgM hgB hS1
  have hWHd : MDiffAt (T% (horizontalLiftField I J f W)) p := by
    have hn2 := two_le_of_minSmoothness_two_le hn
    have h1 : ((1 : ℕ∞) : ℕ∞ω) ≤ ((n : ℕ∞ω)) :=
      WithTop.coe_le_coe.mpr (le_trans (by norm_num) hn2)
    exact mdiffAt_horizontalLiftField_of_one hn hf hgM hgB (hW.self_of_nhds.of_le h1)
  -- metric compatibility on both manifolds, bound with named binders
  have hcM : ∀ {U₁ U₂ U₃ : Π z : M, TangentSpace I z} {z : M},
      MDiffAt (T% U₂) z → MDiffAt (T% U₃) z →
      d% (fun y ↦ tangentMetric I M y (U₂ y) (U₃ y)) z (U₁ z)
        = tangentMetric I M z (leviCivita (tangentMetric I M) U₂ z (U₁ z)) (U₃ z)
          + tangentMetric I M z (U₂ z) (leviCivita (tangentMetric I M) U₃ z (U₁ z)) :=
    isCompatibleWith_leviCivita isSymm_tangentMetric isNondegenerate_tangentMetric hgmM
  have hcB : ∀ {U₁ U₂ U₃ : Π q : B, TangentSpace J q} {q : B},
      MDiffAt (T% U₂) q → MDiffAt (T% U₃) q →
      d% (fun q' ↦ tangentMetric J B q' (U₂ q') (U₃ q')) q (U₁ q)
        = tangentMetric J B q (leviCivita (tangentMetric J B) U₂ q (U₁ q)) (U₃ q)
          + tangentMetric J B q (U₂ q) (leviCivita (tangentMetric J B) U₃ q (U₁ q)) :=
    isCompatibleWith_leviCivita isSymm_tangentMetric isNondegenerate_tangentMetric hgmB
  -- the four lines of the derivation
  have e1 := hcM (U₁ := horizontalLiftField I J f X) hSHd hWHd
  have e2 : d% (fun z ↦ tangentMetric I M z (horizontalLiftField I J f
        (fun q ↦ leviCivita (tangentMetric J B) Z q (Y q)) z)
        (horizontalLiftField I J f W z)) p (horizontalLiftField I J f X p)
      = d% (fun q ↦ tangentMetric J B q
          (leviCivita (tangentMetric J B) Z q (Y q)) (W q)) (f p) (X (f p)) :=
    mvfderiv_tangentMetric_horizontalLiftField (Y₁ := X)
      (Y₂ := fun q ↦ leviCivita (tangentMetric J B) Z q (Y q)) (Y₃ := W) hsube hrieme hfd
      (mdiffAt_pairing (hgmB (f p)) hSd hWd)
  have e3 : tangentMetric I M p (horizontalLiftField I J f
        (fun q ↦ leviCivita (tangentMetric J B) Z q (Y q)) p)
        (leviCivita (tangentMetric I M) (horizontalLiftField I J f W) p
          (horizontalLiftField I J f X p))
      = tangentMetric J B (f p) (leviCivita (tangentMetric J B) Z (f p) (Y (f p)))
          (leviCivita (tangentMetric J B) W (f p) (X (f p))) := by
    rw [isSymm_tangentMetric p (horizontalLiftField I J f
        (fun q ↦ leviCivita (tangentMetric J B) Z q (Y q)) p) _,
      tangentMetric_leviCivita_horizontalLiftField (U := X) (V := W)
        (K := fun q ↦ leviCivita (tangentMetric J B) Z q (Y q)) hn hn' hf hgM hgB hsube hrieme hW,
      isSymm_tangentMetric (f p) _ (leviCivita (tangentMetric J B) Z (f p) (Y (f p)))]
  have e4 := hcB (U₁ := X) (U₂ := fun q ↦ leviCivita (tangentMetric J B) Z q (Y q)) (U₃ := W)
    hSd hWd
  rw [hfield, horizontalLeviCivita_apply, tangentMetric_horizontalProjection_left,
    mem_horizontalSpace_iff_horizontalProjection_eq_self.mp (horizontalLiftField_mem (Y := W) p)]
  rw [e2, e4, e3] at e1
  linarith [e1]

/-! ## The scalar identification -/

/-- **The lift of the second structural equation of `B`, in scalar form.**

    ⟪R^H(X, Y)Z, Wᴴ p⟫ = ⟪R*(X, Y)Z, W⟫ (f p)

for basic fields, where `R* = RiemannianGeometry.curvature (leviCivita (tangentMetric J B))` is this
project's curvature of the **base** connection, in the same modern convention as on `M`.

The three terms of `oneillHorizontalCurvature` are matched one-to-one with the three terms of
`RiemannianGeometry.curvature`: the first two by the two-derivative case (the second with `X` and `Y`
exchanged), the third by the single-derivative case with direction `[X, Y]`. **No sign is
adjusted**: after the three rewrites the two sides are equal by `abel`-free syntactic matching,
because `RiemannianGeometry.curvature`'s subtractions and `oneillHorizontalCurvature`'s are the same
subtractions.

-/
theorem tangentMetric_oneillHorizontalCurvature_horizontalLiftField {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    (hX : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% X) q)
    (hY : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q)
    (hZ : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Z) q)
    (hW : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% W) q) :
    tangentMetric I M p (oneillHorizontalCurvature I J f X Y Z p)
        (horizontalLiftField I J f W p)
      = tangentMetric J B (f p)
          (curvature (leviCivita (tangentMetric J B)) X Y Z (f p)) (W (f p)) := by
  have hsube : ∀ᶠ z in 𝓝 p, IsSubmersionAtPoint I J f z := Filter.Eventually.of_forall hsub
  have hrieme : ∀ᶠ z in 𝓝 p, IsRiemannianSubmersionAtPoint I J f z :=
    Filter.Eventually.of_forall hriem
  rw [oneillHorizontalCurvature_apply, curvature_apply]
  simp only [map_sub, sub_apply]
  rw [tangentMetric_horizontalLeviCivita_horizontalLeviCivita_horizontalLiftField
      hn hn' hf hgM hgB hsub hriem hY hZ hW,
    tangentMetric_horizontalLeviCivita_horizontalLeviCivita_horizontalLiftField
      (X := Y) (Y := X) hn hn' hf hgM hgB hsub hriem hX hZ hW,
    tangentMetric_horizontalLeviCivita_horizontalLiftField (U := mlieBracket J X Y) (V := Z)
      hn hn' hf hgM hgB hsube hrieme (Filter.Eventually.of_forall hZ)]

/-! ## The vector identification -/

/-- **The lift of the second structural equation of `B`, in vector form.**

    R^H(X, Y)Z = (R*(X, Y)Z)ᴴ at `p`.

Free from the scalar form: both sides are horizontal — the left is a difference of three
`𝓗`-images, the right a `horizontalLiftField` — so pairing against an arbitrary `u` and splitting
`u = 𝓗u + 𝓥u` kills the vertical half on both sides, and `𝓗u` **is** the value at `p` of a basic
field by `HorizontalLift.exists_basic_eq_horizontalProjection`. Nondegeneracy is then applied on
the whole tangent space, through `eq_of_g_eq`.

**Lemma 1(3) is applied no more times here than in the scalar form.** The construction of the
fourth field is `exists_basic_eq_horizontalProjection`, not a second push-forward, and this is why
the vector identity costs no extra metric regularity: the hypotheses are those of
`tangentMetric_oneillHorizontalCurvature_horizontalLiftField` minus `hW`, whose place the
constructed field takes. That constructed field is `C^n` only on a **neighbourhood** of `f p`,
which is exactly the form the scalar theorem's `hW` takes.
-/
theorem oneillHorizontalCurvature_eq_horizontalLiftField_curvature {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    (hX : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% X) q)
    (hY : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q)
    (hZ : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Z) q) :
    oneillHorizontalCurvature I J f X Y Z p
      = horizontalLiftField I J f (curvature (leviCivita (tangentMetric J B)) X Y Z) p := by
  refine eq_of_g_eq (tangentMetric_nondegenerate I M p) fun u ↦ ?_
  obtain ⟨W', hW', hW'u⟩ :=
    exists_basic_eq_horizontalProjection (m := n) (hsub p) (hriem p) u
  have hhor : oneillHorizontalCurvature I J f X Y Z p ∈ horizontalSpace I J f p := by
    rw [oneillHorizontalCurvature_apply]
    simp only [horizontalLeviCivita_apply]
    exact Submodule.sub_mem _
      (Submodule.sub_mem _ (horizontalProjection_mem _) (horizontalProjection_mem _))
      (horizontalProjection_mem _)
  have hd : horizontalProjection I J f p u + verticalProjection I J f p u = u :=
    horizontalProjection_add_verticalProjection u
  rw [← hd, map_add, map_add, ← hW'u,
    tangentMetric_eq_zero_of_mem_horizontalSpace_of_mem_verticalSpace hhor
      (verticalProjection_mem u),
    tangentMetric_eq_zero_of_mem_horizontalSpace_of_mem_verticalSpace
      (horizontalLiftField_mem p) (verticalProjection_mem u),
    add_zero, add_zero,
    tangentMetric_oneillHorizontalCurvature_horizontalLiftField hn hn' hf hgM hgB hsub hriem
      hX hY hZ hW',
    tangentMetric_horizontalLiftField_apply (hsub p) (hriem p)]

end RiemannianGeometry
