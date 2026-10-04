/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import RiemannianGeometry.ONeillLemmaTwo

/-!
# O'Neill's Lemma 1(1) and Lemma 1(3): the connection comparison

O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. **13** (1966) 459–469,
p. 460:

> **LEMMA 1.** If `X` and `Y` are basic vector fields on `M`, then
> 1. `⟨X, Y⟩ = ⟨X_*, Y_*⟩ ∘ π`,
> 2. `𝓗[X, Y]` is the basic vector field corresponding to `[X_*, Y_*]`,
> 3. `𝓗∇_X Y` is the basic vector field corresponding to `∇*_{X_*}(Y_*)`.

## Main results

* `tangentMetric_horizontalLiftField_apply`, `tangentMetric_horizontalLiftField`,
  `tangentMetric_horizontalLiftField_eventuallyEq` — **Lemma 1(1)** for two independent basic
  fields, pointwise, globally as an equality of functions, and near a point.
* `mvfderiv_tangentMetric_horizontalLiftField` — the derivative terms of the Koszul formula
  transfer: `Xᴴ⟨Yᴴ, Zᴴ⟩ = (X_*⟨Y_*, Z_*⟩) ∘ π` at a point.
* `tangentMetric_mlieBracket_horizontalLiftField` — the bracket terms transfer:
  `⟨[Xᴴ, Yᴴ], Zᴴ⟩ = ⟨[X_*, Y_*], Z_*⟩ ∘ π` at a point.
* `koszulRHS_horizontalLiftField` — the two Koszul right-hand sides agree, from the previous two
  applied three times each.
* `tangentMetric_horizontalProjection_leviCivita_horizontalLiftField` — the two sides of
  Lemma 1(3) pair equally against an arbitrary *basic* field.
* `horizontalProjection_leviCivita_horizontalLiftField` — **Lemma 1(3)**, at a point.
* `horizontalPart_leviCivita_horizontalLiftField` — Lemma 1(3) as an equality of vector fields:
  `𝓗∇_{Xᴴ} Yᴴ` **is** the horizontal lift of `∇*_{X_*} Y_*`.
* `exists_horizontalPart_leviCivita_horizontalLiftField_eq` — the half O'Neill states as "is the
  basic vector field corresponding to": `𝓗∇_{Xᴴ} Yᴴ` is basic.

## Scope: basic fields, not arbitrary horizontal fields

As in `RiemannianGeometry.ONeillLemmaTwo`, everything is proved for `horizontalLiftField I J f Y`, which
is **exactly** O'Neill's class of basic fields and not a weakening of it
(`eq_horizontalLiftField`). No tensoriality reduction from horizontal to basic is available in
this development, and none is used.

## `∇*` costs nothing to have

`leviCivita (tangentMetric J B)` is the same construction as `leviCivita (tangentMetric I M)`,
applied to the base's tangent metric, with the same certification theorems. This is nevertheless
the **first result in the project to use `leviCivita` on two manifolds simultaneously**, so the
statement of Lemma 1(3) was probed before being committed. It elaborates in the spelling written
below with no annotation, no `letI`, and no reshaping; in particular
`IsMDiffMetric E' (tangentMetric J B)`, `isSymm_tangentMetric` and
`isNondegenerate_tangentMetric` all resolve on `B` from the section variables alone, and both
`Bundle.RiemannianBundle` instances coexist without the fibrewise `InnerProductSpace` ambiguity
that Rule 1 of `RiemannianGeometry.HorizontalSpace` guards against.

## The proof of Lemma 1(3), and where nondegeneracy is applied

Both sides are horizontal: the left is literally a `𝓗`-image, the right is a
`horizontalLiftField` (`horizontalLiftField_mem`). Paired against a basic `Zᴴ`, each side is
`½ κ` for its own manifold by `leviCivita_spec`, and the two `κ`'s agree term by term. Passing
from "equal against every basic field" to "equal" is the argument
`ONeillLemmaTwo.oneillA_horizontalLiftField_self_eq_zero` already runs: decompose an arbitrary
`u` as `𝓗u + 𝓥u`, kill the vertical half against the horizontal difference, and observe that
`𝓗u` **is** a basic field's value at `p`, by
`HorizontalLift.exists_basic_eq_horizontalProjection` — a named reusable lemma, not an inline
construction. So nondegeneracy is applied on the whole tangent space
(`eq_of_g_eq`), never on a restricted metric, and no non-degeneracy of `g|H` is needed.

The one snag worth recording: `rw [← horizontalProjection_add_verticalProjection u]` fails, with a
stuck `ChartedSpace ?H ?B`, because `J`, `B` and `f` are not determined by `u`. The identity is
bound in a `have` first, exactly as in `ONeillLemmaTwo`.

## Regularity accounting — and where less was needed than predicted

* **Lemma 1(1) needs no differentiability and no metric smoothness at all**, exactly as §2
  predicted, and the pointwise form needs `hsub`/`hriem` only at the one point.
* the three base fields are likewise assumed `C^n` only **near** `f p`, which is what
  `horizontalProjection_mlieBracket_horizontalLiftField` and `contMDiffAt_horizontalLiftField`
  consume.

What is genuinely needed, and what forces it:

* `minSmoothness ℝ 2 ≤ n` and `(n : ℕ∞ω) ≠ ∞` — `mfderiv_mlieBracket_of_related`, through the
  bracket terms. The `2` is the intrinsic cost of a Lie bracket; the finiteness is the genuine
  restriction inherited from that theorem.
* `f` of class `C^(n+1)` — `contMDiffAt_horizontalLiftField`, to know the lifts are `C^n` near
  `p`. The `+1` is spent once, in `contMDiffAt_mfderiv_inCoordinates`.
* both metrics `C^n` — the lifts again, the adjoint being built from both metrics, and
  `IsMDiffMetric` for `leviCivita_spec` on each side, derived by
  `IsContMDiffMetricSection.isMDiffMetric` and never assumed.
* the base fields `C^n` near `f p` — the lifts, and the derivative terms.
* `hsub`, `hriem` near `p` — Lemma 1(1), `mfderiv_horizontalLiftField`,
  `horizontalProjection_eq`.

**At `n = 2`: `f ∈ C³` and both metrics `C²`.** No third derivative of either metric is taken
anywhere in this file, and no statement below asks for one. `IsSymm` and `IsNondegenerate` are
free from the bundle (`isSymm_tangentMetric`, `isNondegenerate_tangentMetric`,
`tangentMetric_nondegenerate`) on **both** manifolds.

## `ONeillLemmaTwo.tangentMetric_horizontalLiftField_self` is now redundant

That theorem is the diagonal case `Y₁ = Y₂ = Y` of `tangentMetric_horizontalLiftField` below,
with the same hypotheses and the same `omit` list. It **should be deleted** and re-derived. Since
`ONeillLemmaTwo` consumes it internally, the general form has to be available upstream: the two
D1 lemmas use only `horizontalLiftField_mem`, `mfderiv_horizontalLiftField` and
`inner_eq_tangentMetric`, so they belong in the `Base` section of
`RiemannianGeometry/HorizontalLift.lean`, ahead of `ONeillTensors`. With them there, the replacement
proof term for the diagonal statement is

    tangentMetric_horizontalLiftField hsub hriem

and its two uses inside `ONeillLemmaTwo` (in
`tangentMetric_leviCivita_horizontalLiftField_self_eq_zero`) go through unchanged, since the
statement is identical.

## Instance notes

Rule 1 of `RiemannianGeometry.HorizontalSpace` is respected: no fibrewise `InnerProductSpace` or
`NormedAddCommGroup` on a tangent space is bound to a local name, no instance is declared, and
every fibre-valued variable is typed with the `TangentSpace` synonym. `CompleteSpace E`,
`CompleteSpace E'` and `SeparatingDual ℝ E'`, which `leviCivita` and the bracket lemmas need, are
found by search from `FiniteDimensional ℝ E`, `FiniteDimensional ℝ E'` and the real base field.

Everything metric-valued is written with `tangentMetric`, never `inner ℝ`, following
`RiemannianGeometry.ONeillTensors`. The single crossing point is inside
`tangentMetric_horizontalLiftField_apply`, where `IsRiemannianSubmersionAtPoint` — phrased with
`inner ℝ` — is consumed, and it is crossed by `inner_eq_tangentMetric`.
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
  {f : M → B} {p : M} {Y₁ Y₂ Y₃ : Π q : B, TangentSpace J q}


omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **Lemma 1(1) near a point**, in the form `mvfderiv_congr_of_eventuallyEq` consumes.

Stated separately because `mvfderiv` is a germ notion: differentiating `⟨Y₁ᴴ, Y₂ᴴ⟩` at `p` never
needs the equality of functions on all of `M`, only on a neighbourhood, and hence needs the
submersion and isometry conditions only near `p`. -/
theorem tangentMetric_horizontalLiftField_eventuallyEq
    (hsub : ∀ᶠ z in 𝓝 p, IsSubmersionAtPoint I J f z)
    (hriem : ∀ᶠ z in 𝓝 p, IsRiemannianSubmersionAtPoint I J f z) :
    (fun z ↦ tangentMetric I M z (horizontalLiftField I J f Y₁ z)
        (horizontalLiftField I J f Y₂ z))
      =ᶠ[𝓝 p] ((fun q ↦ tangentMetric J B q (Y₁ q) (Y₂ q)) ∘ f) := by
  filter_upwards [hsub, hriem] with z h1 h2
  exact tangentMetric_horizontalLiftField_apply h1 h2

/-! ## One missing orientation of the mixed pairing -/

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B]
  [Bundle.RiemannianBundle (TangentSpace J : B → Type _)] in
/-- **A horizontal vector pairs to zero with a vertical one**, in that order.

`ONeillLemmaTwo.tangentMetric_eq_zero_of_mem_verticalSpace_of_mem_horizontalSpace` is the other
orientation; both are needed here, because in Lemma 1(3) the horizontal vector is the one on the
left. Symmetry of the metric is the only content. -/
theorem tangentMetric_eq_zero_of_mem_horizontalSpace_of_mem_verticalSpace
    {a b : TangentSpace I p} (ha : a ∈ horizontalSpace I J f p)
    (hb : b ∈ verticalSpace I J f p) : tangentMetric I M p a b = 0 := by
  rw [isSymm_tangentMetric p a b]
  exact tangentMetric_eq_zero_of_mem_verticalSpace_of_mem_horizontalSpace hb ha

/-! ## The three derivative terms of the Koszul formula transfer -/

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **`Y₁ᴴ⟨Y₂ᴴ, Y₃ᴴ⟩ p = Y₁⟨Y₂, Y₃⟩ (f p)`** — the derivative terms transfer.

`hpair` is differentiability of the *base* pairing at `f p`; the callers below get it from
`mdiffAt_pairing`. Nothing upstairs has to be differentiated. -/
theorem mvfderiv_tangentMetric_horizontalLiftField
    (hsub : ∀ᶠ z in 𝓝 p, IsSubmersionAtPoint I J f z)
    (hriem : ∀ᶠ z in 𝓝 p, IsRiemannianSubmersionAtPoint I J f z)
    (hfd : MDiffAt f p)
    (hpair : MDiffAt (fun q ↦ tangentMetric J B q (Y₂ q) (Y₃ q)) (f p)) :
    d% (fun z ↦ tangentMetric I M z (horizontalLiftField I J f Y₂ z)
        (horizontalLiftField I J f Y₃ z)) p (horizontalLiftField I J f Y₁ p)
      = d% (fun q ↦ tangentMetric J B q (Y₂ q) (Y₃ q)) (f p) (Y₁ (f p)) := by
  rw [mvfderiv_congr_of_eventuallyEq
      (tangentMetric_horizontalLiftField_eventuallyEq hsub hriem),
    mvfderiv_comp_apply hpair hfd,
    mfderiv_horizontalLiftField hsub.self_of_nhds hriem.self_of_nhds]

/-! ## The three bracket terms of the Koszul formula transfer -/

/-- **`⟨[Y₁ᴴ, Y₂ᴴ], Y₃ᴴ⟩ p = ⟨[Y₁, Y₂], Y₃⟩ (f p)`** — the bracket terms transfer.

`Y₃ᴴ p` is horizontal, so only the horizontal part of the bracket contributes: split
`[Y₁ᴴ, Y₂ᴴ] p = 𝓗[Y₁ᴴ, Y₂ᴴ] p + 𝓥[Y₁ᴴ, Y₂ᴴ] p`, drop the vertical half by the mixed pairing, and
`horizontalProjection_mlieBracket_horizontalLiftField` — O'Neill's Lemma 1(2) — turns
`𝓗[Y₁ᴴ, Y₂ᴴ]` into `([Y₁, Y₂])ᴴ`. Lemma 1(1) finishes. This is the term that fixes the whole
regularity budget: it is the only one that routes through `mfderiv_mlieBracket_of_related`, and
hence the only source of `minSmoothness ℝ 2 ≤ n` and `(n : ℕ∞ω) ≠ ∞`. -/
theorem tangentMetric_mlieBracket_horizontalLiftField {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiffAt I J ((n : ℕ∞ω)) f p)
    (hsub : ∀ᶠ z in 𝓝 p, IsSubmersionAtPoint I J f z)
    (hriem : ∀ᶠ z in 𝓝 p, IsRiemannianSubmersionAtPoint I J f z)
    (hY₁H : ∀ᶠ z in 𝓝 p,
      ContMDiffAt I I.tangent ((n : ℕ∞ω)) (T% (horizontalLiftField I J f Y₁)) z)
    (hY₂H : ∀ᶠ z in 𝓝 p,
      ContMDiffAt I I.tangent ((n : ℕ∞ω)) (T% (horizontalLiftField I J f Y₂)) z)
    (hY₁ : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y₁) q)
    (hY₂ : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y₂) q) :
    tangentMetric I M p (mlieBracket I (horizontalLiftField I J f Y₁)
        (horizontalLiftField I J f Y₂) p) (horizontalLiftField I J f Y₃ p)
      = tangentMetric J B (f p) (mlieBracket J Y₁ Y₂ (f p)) (Y₃ (f p)) := by
  have hd : horizontalProjection I J f p
        (mlieBracket I (horizontalLiftField I J f Y₁) (horizontalLiftField I J f Y₂) p)
      + verticalProjection I J f p
        (mlieBracket I (horizontalLiftField I J f Y₁) (horizontalLiftField I J f Y₂) p)
      = mlieBracket I (horizontalLiftField I J f Y₁) (horizontalLiftField I J f Y₂) p :=
    horizontalProjection_add_verticalProjection _
  rw [← hd, map_add, add_apply,
    horizontalProjection_mlieBracket_horizontalLiftField hn hn' hf hsub hriem hY₁H hY₂H hY₁ hY₂,
    tangentMetric_eq_zero_of_mem_verticalSpace_of_mem_horizontalSpace
      (verticalProjection_mem _) (horizontalLiftField_mem (Y := Y₃) p),
    add_zero, tangentMetric_horizontalLiftField_apply hsub.self_of_nhds hriem.self_of_nhds]

/-! ## The two Koszul right-hand sides agree -/

/-- **`κ_M(Y₁ᴴ, Y₂ᴴ, p, Y₃ᴴ) = κ_B(Y₁, Y₂, f p, Y₃)`.**

The six terms of `koszulRHS`, in the order and with the signs of its definition — three
derivative terms by `mvfderiv_tangentMetric_horizontalLiftField` and three bracket terms by
`tangentMetric_mlieBracket_horizontalLiftField`, each in the permutation the definition asks for.
No sign is manipulated: after the six rewrites the two sides are syntactically equal.

The `have`s at the top are the derived data. `IsMDiffMetric E' (tangentMetric J B)` is *derived*
from `hgB` rather than assumed, and the three lifts' `C^n`-ness near `p` is derived from `hf`,
the two metrics and the base fields' `C^n`-ness near `f p`, pulled back along `f` by continuity
(`Filter.Tendsto.eventually`). -/
theorem koszulRHS_horizontalLiftField {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ᶠ z in 𝓝 p, IsSubmersionAtPoint I J f z)
    (hriem : ∀ᶠ z in 𝓝 p, IsRiemannianSubmersionAtPoint I J f z)
    (hY₁ : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y₁) q)
    (hY₂ : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y₂) q)
    (hY₃ : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y₃) q) :
    koszulRHS (tangentMetric I M) (horizontalLiftField I J f Y₁)
        (horizontalLiftField I J f Y₂) p (horizontalLiftField I J f Y₃)
      = koszulRHS (tangentMetric J B) Y₁ Y₂ (f p) Y₃ := by
  have hn0 := coe_ne_zero_of_minSmoothness_two_le hn
  have hgmB : IsMDiffMetric E' (tangentMetric J B) :=
    IsContMDiffMetricSection.isMDiffMetric hn0 hgB
  have hle : ((n : ℕ∞ω)) ≤ (((n + 1 : ℕ∞)) : ℕ∞ω) := by push_cast; exact le_self_add
  have hfp : ContMDiffAt I J ((n : ℕ∞ω)) f p := (hf p).of_le hle
  have hfd : MDiffAt f p := hfp.mdifferentiableAt hn0
  have hcont : Filter.Tendsto f (𝓝 p) (𝓝 (f p)) := hf.continuous.continuousAt
  have hlift : ∀ {Y : Π q : B, TangentSpace J q},
      (∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q) →
        ∀ᶠ z in 𝓝 p,
          ContMDiffAt I I.tangent ((n : ℕ∞ω)) (T% (horizontalLiftField I J f Y)) z := by
    intro Y hY
    filter_upwards [hcont.eventually hY] with z hz
    exact contMDiffAt_horizontalLiftField isOpen_univ (Set.mem_univ z) hf.contMDiffOn
      (hgM z) (hgB (f z)) hz
  have hYd : ∀ {Y : Π q : B, TangentSpace J q},
      (∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q) →
        MDiffAt (T% Y) (f p) :=
    fun hY ↦ hY.self_of_nhds.mdifferentiableAt hn0
  have hpair : ∀ {U W : Π q : B, TangentSpace J q}, MDiffAt (T% U) (f p) →
      MDiffAt (T% W) (f p) → MDiffAt (fun q ↦ tangentMetric J B q (U q) (W q)) (f p) :=
    fun hU hW ↦ mdiffAt_pairing (hgmB (f p)) hU hW
  simp only [koszulRHS]
  rw [mvfderiv_tangentMetric_horizontalLiftField hsub hriem hfd (hpair (hYd hY₂) (hYd hY₃)),
    mvfderiv_tangentMetric_horizontalLiftField hsub hriem hfd (hpair (hYd hY₃) (hYd hY₁)),
    mvfderiv_tangentMetric_horizontalLiftField hsub hriem hfd (hpair (hYd hY₁) (hYd hY₂)),
    tangentMetric_mlieBracket_horizontalLiftField hn hn' hfp hsub hriem (hlift hY₁) (hlift hY₂)
      hY₁ hY₂,
    tangentMetric_mlieBracket_horizontalLiftField hn hn' hfp hsub hriem (hlift hY₁) (hlift hY₃)
      hY₁ hY₃,
    tangentMetric_mlieBracket_horizontalLiftField hn hn' hfp hsub hriem (hlift hY₂) (hlift hY₃)
      hY₂ hY₃]

/-! ## Lemma 1(3): the connection comparison -/

/-- **Lemma 1(3), paired against an arbitrary basic field.**

`⟨𝓗∇_{Y₁ᴴ} Y₂ᴴ, Y₃ᴴ⟩ = ⟨(∇*_{Y₁} Y₂)ᴴ, Y₃ᴴ⟩` at `p`. Both sides are computed by
`leviCivita_spec` — on `M` for the left, on `B` for the right after Lemma 1(1) — and matched by
`koszulRHS_horizontalLiftField`. On the left the outer `𝓗` is removed by self-adjointness of the
projection (`tangentMetric_horizontalProjection_left`) together with horizontality of `Y₃ᴴ p`,
not by discarding it. -/
theorem tangentMetric_horizontalProjection_leviCivita_horizontalLiftField {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ᶠ z in 𝓝 p, IsSubmersionAtPoint I J f z)
    (hriem : ∀ᶠ z in 𝓝 p, IsRiemannianSubmersionAtPoint I J f z)
    (hY₁ : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y₁) q)
    (hY₂ : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y₂) q)
    (hY₃ : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y₃) q) :
    tangentMetric I M p
        (horizontalProjection I J f p (leviCivita (tangentMetric I M)
          (horizontalLiftField I J f Y₂) p (horizontalLiftField I J f Y₁ p)))
        (horizontalLiftField I J f Y₃ p)
      = tangentMetric I M p (horizontalLiftField I J f
          (fun q ↦ leviCivita (tangentMetric J B) Y₂ q (Y₁ q)) p)
        (horizontalLiftField I J f Y₃ p) := by
  have hn0 := coe_ne_zero_of_minSmoothness_two_le hn
  have hgmM : IsMDiffMetric E (tangentMetric I M) :=
    IsContMDiffMetricSection.isMDiffMetric hn0 hgM
  have hgmB : IsMDiffMetric E' (tangentMetric J B) :=
    IsContMDiffMetricSection.isMDiffMetric hn0 hgB
  have hcont : Filter.Tendsto f (𝓝 p) (𝓝 (f p)) := hf.continuous.continuousAt
  have hliftd : ∀ {Y : Π q : B, TangentSpace J q},
      (∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q) →
        MDiffAt (T% (horizontalLiftField I J f Y)) p := by
    intro Y hY
    exact (contMDiffAt_horizontalLiftField isOpen_univ (Set.mem_univ p) hf.contMDiffOn
      (hgM p) (hgB (f p)) hY.self_of_nhds).mdifferentiableAt hn0
  have hYd : ∀ {Y : Π q : B, TangentSpace J q},
      (∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q) →
        MDiffAt (T% Y) (f p) :=
    fun hY ↦ hY.self_of_nhds.mdifferentiableAt hn0
  have hL : tangentMetric I M p
        (horizontalProjection I J f p (leviCivita (tangentMetric I M)
          (horizontalLiftField I J f Y₂) p (horizontalLiftField I J f Y₁ p)))
        (horizontalLiftField I J f Y₃ p)
      = (1 / 2 : ℝ) * koszulRHS (tangentMetric I M) (horizontalLiftField I J f Y₁)
          (horizontalLiftField I J f Y₂) p (horizontalLiftField I J f Y₃) := by
    rw [tangentMetric_horizontalProjection_left,
      mem_horizontalSpace_iff_horizontalProjection_eq_self.mp
        (horizontalLiftField_mem (Y := Y₃) p)]
    exact leviCivita_spec isSymm_tangentMetric isNondegenerate_tangentMetric hgmM
      (hliftd hY₁) (hliftd hY₂) (hliftd hY₃)
  have hR : tangentMetric I M p (horizontalLiftField I J f
        (fun q ↦ leviCivita (tangentMetric J B) Y₂ q (Y₁ q)) p)
        (horizontalLiftField I J f Y₃ p)
      = (1 / 2 : ℝ) * koszulRHS (tangentMetric J B) Y₁ Y₂ (f p) Y₃ := by
    rw [tangentMetric_horizontalLiftField_apply hsub.self_of_nhds hriem.self_of_nhds]
    exact leviCivita_spec isSymm_tangentMetric isNondegenerate_tangentMetric hgmB
      (hYd hY₁) (hYd hY₂) (hYd hY₃)
  rw [hL, hR, koszulRHS_horizontalLiftField hn hn' hf hgM hgB hsub hriem hY₁ hY₂ hY₃]

/-- **O'Neill's Lemma 1(3)**: `𝓗∇_{Y₁ᴴ} Y₂ᴴ = (∇*_{Y₁} Y₂)ᴴ` at `p`.

Note the direction convention: `leviCivita g Y x (X x)` is `(∇_X Y)(x)`, the direction **last**,
so `leviCivita (tangentMetric I M) Y₂ᴴ p (Y₁ᴴ p)` is `∇_{Y₁ᴴ} Y₂ᴴ` at `p`, and the base field on
the right is `fun q ↦ leviCivita (tangentMetric J B) Y₂ q (Y₁ q)`, i.e. `∇*_{Y₁} Y₂`.

Both sides are horizontal, so it suffices to pair them against an arbitrary `u` and split
`u = 𝓗u + 𝓥u`. The vertical half dies against either side. For the horizontal half, `𝓗u` is
exhibited as the value at `p` of an honest basic field by
`HorizontalLift.exists_basic_eq_horizontalProjection`, and the previous lemma applies.
Nondegeneracy is then used on the whole tangent space, through `eq_of_g_eq`.

The extension step is **not** hidden inside this argument: it is
`HorizontalLift.exists_basic_eq_horizontalProjection`, stated and proved upstream as a reusable
lemma, because "every horizontal vector is the value of a basic field" is the standing bridge from
O'Neill's field-level statements to vector-level conclusions and will be needed again.

`Y₃` has disappeared from the hypotheses: the third field is constructed, not assumed. -/
theorem horizontalProjection_leviCivita_horizontalLiftField {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ᶠ z in 𝓝 p, IsSubmersionAtPoint I J f z)
    (hriem : ∀ᶠ z in 𝓝 p, IsRiemannianSubmersionAtPoint I J f z)
    (hY₁ : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y₁) q)
    (hY₂ : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y₂) q) :
    horizontalProjection I J f p (leviCivita (tangentMetric I M)
        (horizontalLiftField I J f Y₂) p (horizontalLiftField I J f Y₁ p))
      = horizontalLiftField I J f (fun q ↦ leviCivita (tangentMetric J B) Y₂ q (Y₁ q)) p := by
  refine eq_of_g_eq (tangentMetric_nondegenerate I M p) fun u ↦ ?_
  obtain ⟨Y₃, hY₃, hHu⟩ :=
    exists_basic_eq_horizontalProjection (m := n) hsub.self_of_nhds hriem.self_of_nhds u
  have hd : horizontalProjection I J f p u + verticalProjection I J f p u = u :=
    horizontalProjection_add_verticalProjection u
  rw [← hd, map_add, map_add, ← hHu,
    tangentMetric_horizontalProjection_verticalProjection,
    tangentMetric_eq_zero_of_mem_horizontalSpace_of_mem_verticalSpace
      (horizontalLiftField_mem p) (verticalProjection_mem u),
    add_zero, add_zero]
  exact tangentMetric_horizontalProjection_leviCivita_horizontalLiftField hn hn' hf hgM hgB
    hsub hriem hY₁ hY₂ hY₃

/-- **Lemma 1(3) as an equality of vector fields**: `𝓗∇_{Y₁ᴴ} Y₂ᴴ = (∇*_{Y₁} Y₂)ᴴ`.

The previous theorem at every point, which is why the submersion, isometry and base-field
hypotheses are global here rather than germs at one point. This is the full content of O'Neill's
Lemma 1(3): not only is `𝓗∇_{Y₁ᴴ} Y₂ᴴ` basic, the base field it corresponds to is exactly
`∇*_{Y₁} Y₂`. 

-/
theorem horizontalPart_leviCivita_horizontalLiftField {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    (hY₁ : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y₁) q)
    (hY₂ : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y₂) q) :
    horizontalPart I J f (fun z ↦ leviCivita (tangentMetric I M)
        (horizontalLiftField I J f Y₂) z (horizontalLiftField I J f Y₁ z))
      = horizontalLiftField I J f (fun q ↦ leviCivita (tangentMetric J B) Y₂ q (Y₁ q)) :=
  funext fun _ ↦ horizontalProjection_leviCivita_horizontalLiftField hn hn' hf hgM hgB
    (Filter.Eventually.of_forall hsub) (Filter.Eventually.of_forall hriem)
    (Filter.Eventually.of_forall hY₁) (Filter.Eventually.of_forall hY₂)

/-- **`𝓗∇_{Y₁ᴴ} Y₂ᴴ` is basic** — the half of Lemma 1(3) O'Neill states as "is the basic vector
field corresponding to".

Weaker than `horizontalPart_leviCivita_horizontalLiftField`, which names the witness, and
recorded only because it is the assertion the source makes. By
`eq_horizontalLiftField` a `horizontalLiftField` is exactly O'Neill's notion of a basic field, so
this is his statement and not a paraphrase of it. -/
theorem exists_horizontalPart_leviCivita_horizontalLiftField_eq {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    (hY₁ : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y₁) q)
    (hY₂ : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y₂) q) :
    ∃ Z : Π q : B, TangentSpace J q,
      horizontalPart I J f (fun z ↦ leviCivita (tangentMetric I M)
          (horizontalLiftField I J f Y₂) z (horizontalLiftField I J f Y₁ z))
        = horizontalLiftField I J f Z :=
  ⟨_, horizontalPart_leviCivita_horizontalLiftField hn hn' hf hgM hgB hsub hriem hY₁ hY₂⟩

end RiemannianGeometry
