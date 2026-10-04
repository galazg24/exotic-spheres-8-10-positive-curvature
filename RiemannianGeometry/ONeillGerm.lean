/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import RiemannianGeometry.LeviCivitaGerm
import RiemannianGeometry.ONeillCurvatureNondecreasing

/-!
# Germ hypotheses for the O'Neill submersion identities, and Corollary 1(3) for arbitrary
horizontal vectors

The submersion identities of `RiemannianGeometry.ONeillLemmaOne`, `ONeillHorizontalCurvature`,
`ONeillHorizontalCurvatureScalar`, `ONeillBaseCurvature`, `ONeillBasicRegularity`,
`ONeillCorollaryOne` and `ONeillCurvatureNondecreasing` are stated for base fields that are `C^n`
at **every** point of `B`. This file restates them with `∀ᶠ q in 𝓝 (f p), …` in place of `∀ q, …`,
and then removes basic fields from the conclusion altogether: O'Neill's Corollary 1(3), the
inequality `K_M ≤ K_B`, its equality case and the nonnegativity inheritance hold for **arbitrary
horizontal vectors** `u, v ∈ horizontalSpace I J f p`, with the base plane `P_{x_* y_*}` spanned by
`mfderiv I J f p u` and `mfderiv I J f p v`.

## Why the global hypotheses were there, and what removes them

The obstruction was not tensoriality, which `RiemannianGeometry.ONeillTensoriality` supplies. It was a
single missing lemma: the *field* form of Lemma 1(3),

    𝓗∇_{Y₁ᴴ} Y₂ᴴ = (∇*_{Y₁} Y₂)ᴴ,

is an equality of fields on all of `M`, and the two-derivative case of the base-curvature
identification substitutes it **inside** a second covariant derivative. Substituting an equality
that holds only *near* `p` requires knowing that `leviCivita g Y p` depends only on the germ of `Y`
at `p`, and no such lemma existed. It does now:
`RiemannianGeometry.LeviCivitaGerm.leviCivita_congr_of_eventuallyEq`, hypothesis-free. Everything in this
file is downstream of it.

## Main results

Germ locality in the field slot, all hypothesis-free:

* `horizontalLeviCivita_congr_of_eventuallyEq`, `oneillA_congr_of_eventuallyEq`,
  `oneillT_congr_of_eventuallyEq`.

Lemma 1(3) as a germ identity of fields, the enabler:

* `horizontalLeviCivita_horizontalLiftField_eventuallyEq`.

The chain, each entry strictly generalising the named global theorem:

* `contMDiffAt_leviCivita_apply_base_of_eventually`;
* `tangentMetric_horizontalLeviCivita_horizontalLeviCivita_horizontalLiftField_of_eventually`;
* `tangentMetric_oneillHorizontalCurvature_horizontalLiftField_of_eventually`;
* `verticalProjection_mlieBracket_horizontalLiftField_eq_two_smul_oneillA_of_eventually`;
* `horizontalProjection_leviCivita_mlieBracket_horizontalLiftField_of_eventually`;
* `horizontalProjection_curvature_horizontalLiftField_of_eventually` — the vector relation `(4)`;
* `tangentMetric_curvature_horizontalLiftField_of_eventually` — the scalar `{4}`;
* the regularity discharge, `exists_isOpen_contMDiffOn_horizontalLiftField_two` through
  `mdiffAt_oneillA_horizontalLiftField_of_eventually`;
* `tangentMetric_curvature_horizontalLiftField_base_of_eventually`,
  `tangentMetric_curvature_horizontalLiftField_self_of_eventually`;
* `riemannTensorAt_horizontalLiftField_of_eventually`,
  `sectionalCurvatureAt_horizontalLiftField_of_eventually`.

The payoff, for arbitrary horizontal vectors:

* `sectionalCurvatureAt_of_mem_horizontalSpace` — **Corollary 1(3)**;
* `sectionalCurvatureAt_le_of_mem_horizontalSpace` and its orthonormal case — **`K_M ≤ K_B`**, with
  no vector field in the statement;
* `sectionalCurvatureAt_eq_iff_of_mem_horizontalSpace` — the equality case;
* `nonneg_sectionalCurvatureAt_of_nonneg_of_mem_horizontalSpace` and its orthonormal case — the
  nonnegativity inheritance, with no vector field in the statement.

## Which hypotheses relaxed and which did not

**Base fields.** All of them, to `∀ᶠ q in 𝓝 (f p), …`.

**The submersion structure.** `hsub` and `hriem` relax to `∀ᶠ z in 𝓝 p, …` in the
`ONeillBaseCurvature` layer — `tangentMetric_horizontalLeviCivita_horizontalLeviCivita_-`
`horizontalLiftField_of_eventually` and
`tangentMetric_oneillHorizontalCurvature_horizontalLiftField_of_eventually` take them eventually —
but **not** further up. The binding constraint is
`ONeillTensoriality.oneillA_self_eq_zero` and `oneillA_swap_neg`, whose reduction from horizontal
to basic fields uses `exists_mdiffAt_parts_eq_of_isContMDiffMetricSection`, which takes them at
every point of `M`. Relaxing that is independent of this campaign and is not attempted here; the
global form is also the natural hypothesis, a Riemannian submersion being global data.

## The open sets

Three lemmas of the chain — `contMDiffAt_leviCivita` and `contMDiffAt_horizontalPart`,
`contMDiffAt_verticalPart` — take their data on an **open** set rather than as a germ. The germ
forms extract one by `Filter.eventually_nhds_iff`, and where two are needed they are intersected.
That is the only structural change in the regularity discharge.
-/

noncomputable section

open Bundle VectorField Filter Set
open scoped Manifold ContDiff Topology

namespace RiemannianGeometry

section Base

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

/-! ## Germ locality in the field slot -/

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B]
  [Bundle.RiemannianBundle (TangentSpace J : B → Type _)] in
/-- `𝓗∇_D F p` depends only on the germ of `F` at `p`. Immediate from
`leviCivita_congr_of_eventuallyEq`, and **hypothesis-free**. -/
theorem horizontalLeviCivita_congr_of_eventuallyEq {D F F' : Π z : M, TangentSpace I z}
    (h : ∀ᶠ z in 𝓝 p, F z = F' z) :
    horizontalLeviCivita I J f D F p = horizontalLeviCivita I J f D F' p := by
  rw [horizontalLeviCivita_apply, horizontalLeviCivita_apply, leviCivita_congr_of_eventuallyEq h]

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B]
  [Bundle.RiemannianBundle (TangentSpace J : B → Type _)] in
/-- `A_D F p` depends only on the germ of `F` at `p`, with **no hypothesis at all**. -/
theorem oneillA_congr_of_eventuallyEq {D F F' : Π z : M, TangentSpace I z}
    (h : ∀ᶠ z in 𝓝 p, F z = F' z) :
    oneillA I J f D F p = oneillA I J f D F' p := by
  rw [oneillA_apply, oneillA_apply,
    leviCivita_congr_of_eventuallyEq (Y := horizontalPart I J f F)
      (Y' := horizontalPart I J f F') (h.mono fun z hz ↦ by simp only [horizontalPart, hz]),
    leviCivita_congr_of_eventuallyEq (Y := verticalPart I J f F)
      (Y' := verticalPart I J f F') (h.mono fun z hz ↦ by simp only [verticalPart, hz])]

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B]
  [Bundle.RiemannianBundle (TangentSpace J : B → Type _)] in
/-- `T_D F p` depends only on the germ of `F` at `p`, with **no hypothesis at all**. -/
theorem oneillT_congr_of_eventuallyEq {D F F' : Π z : M, TangentSpace I z}
    (h : ∀ᶠ z in 𝓝 p, F z = F' z) :
    oneillT I J f D F p = oneillT I J f D F' p := by
  rw [oneillT_apply, oneillT_apply,
    leviCivita_congr_of_eventuallyEq (Y := verticalPart I J f F)
      (Y' := verticalPart I J f F') (h.mono fun z hz ↦ by simp only [verticalPart, hz]),
    leviCivita_congr_of_eventuallyEq (Y := horizontalPart I J f F)
      (Y' := horizontalPart I J f F') (h.mono fun z hz ↦ by simp only [horizontalPart, hz])]

/-! ## Pulling a germ on the base back along the submersion -/

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold J ∞ B]
  [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]
  [Bundle.RiemannianBundle (TangentSpace J : B → Type _)] in
/-- A property holding near `f p` on `B` holds near `p` on `M` **as a germ at `f z`**, for `z`
near `p`. The bridge between an eventual base-field hypothesis at `f p` and the pointwise
statements at neighbouring points that a field identity needs. -/
theorem eventually_eventually_nhds_map {P : B → Prop} (hfc : ContinuousAt f p)
    (h : ∀ᶠ q in 𝓝 (f p), P q) : ∀ᶠ z in 𝓝 p, ∀ᶠ q in 𝓝 (f z), P q :=
  hfc.eventually h.eventually_nhds

/-! ## Lemma 1(3) as a germ identity of fields -/

/-- **Lemma 1(3) as an identity of fields near `p`**: `𝓗∇_{Y₁ᴴ} Y₂ᴴ = (∇*_{Y₁} Y₂)ᴴ` on a
neighbourhood of `p`.

This strictly generalises `horizontalPart_leviCivita_horizontalLiftField`, which asks for the
submersion structure and both base fields at **every** point and concludes an equality of fields
on all of `M`. Here every hypothesis is a germ, and it is exactly this form that
`leviCivita_congr_of_eventuallyEq` can consume: an equality of fields *near* `p` is enough to
substitute inside a further covariant derivative at `p`.

-/
theorem horizontalLeviCivita_horizontalLiftField_eventuallyEq {n : ℕ∞}
    {Y₁ Y₂ : Π q : B, TangentSpace J q}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ᶠ z in 𝓝 p, IsSubmersionAtPoint I J f z)
    (hriem : ∀ᶠ z in 𝓝 p, IsRiemannianSubmersionAtPoint I J f z)
    (hY₁ : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y₁) q)
    (hY₂ : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y₂) q) :
    ∀ᶠ z in 𝓝 p, horizontalLeviCivita I J f (horizontalLiftField I J f Y₁)
        (horizontalLiftField I J f Y₂) z
      = horizontalLiftField I J f (fun q ↦ leviCivita (tangentMetric J B) Y₂ q (Y₁ q)) z := by
  have hfc : ContinuousAt f p := hf.continuous.continuousAt
  filter_upwards [hsub.eventually_nhds, hriem.eventually_nhds,
    eventually_eventually_nhds_map hfc hY₁, eventually_eventually_nhds_map hfc hY₂]
    with z h1 h2 h3 h4
  exact horizontalProjection_leviCivita_horizontalLiftField hn hn' hf hgM hgB h1 h2 h3 h4


/-! ## The base connection at germ regularity -/

omit [FiniteDimensional ℝ E] [Bundle.RiemannianBundle (TangentSpace I : M → Type _)] in
/-- **`∇*_Y Z` is `C¹` near a point of `B` when `Y` and `Z` are `C^n` near it.**

The germ form of `ONeillBaseCurvature.contMDiffAt_leviCivita_apply_base`. `contMDiffAt_leviCivita`
needs an **open** set on which its data is `C^(m+1)`; `eventually_nhds_iff` supplies one from the
germ hypothesis, which is the only change. -/
theorem contMDiffAt_leviCivita_apply_base_of_eventually {n : ℕ∞} {q₀ : B}
    (hn : minSmoothness ℝ 2 ≤ n)
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hY : ∀ᶠ q in 𝓝 q₀, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q)
    (hZ : ∀ᶠ q in 𝓝 q₀, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Z) q) :
    ContMDiffAt J J.tangent (((1 : ℕ∞) : ℕ∞ω))
      (T% (fun q' ↦ leviCivita (tangentMetric J B) Z q' (Y q'))) q₀ := by
  have hn2 := two_le_of_minSmoothness_two_le hn
  have h2 : ((2 : ℕ∞) : ℕ∞ω) ≤ ((n : ℕ∞ω)) := WithTop.coe_le_coe.mpr hn2
  have h1 : ((1 : ℕ∞) : ℕ∞ω) ≤ ((n : ℕ∞ω)) :=
    WithTop.coe_le_coe.mpr (le_trans (by norm_num) hn2)
  obtain ⟨u, hZu, hu, hqu⟩ := eventually_nhds_iff.mp hZ
  have hgB2 : ContMDiffOn J (J.prod 𝓘(ℝ, E' →L[ℝ] E' →L[ℝ] ℝ)) ((2 : ℕ∞))
      (fun q' ↦ TotalSpace.mk' (E' →L[ℝ] E' →L[ℝ] ℝ)
        (E := fun (q' : B) ↦ TangentSpace J q' →L[ℝ] TangentSpace J q' →L[ℝ] ℝ) q'
        (tangentMetric J B q')) u :=
    fun q' _ ↦ ((hgB q').of_le h2).contMDiffWithinAt
  have hZ2 : CMDiff[u] ((2 : ℕ∞)) (T% Z) := fun q' hq' ↦ ((hZu q' hq').of_le h2).contMDiffWithinAt
  exact ContMDiffAt.clm_bundle_apply
    (contMDiffAt_leviCivita (m := 1) hu hqu isSymm_tangentMetric
      isNondegenerate_tangentMetric hgB2 hZ2) (hY.self_of_nhds.of_le h1)

/-! ## Two covariant derivatives at germ regularity -/

/-- **`⟪𝓗∇_{Xᴴ}(𝓗∇_{Yᴴ}Zᴴ), Wᴴ⟫ p = ⟪∇*_X(∇*_Y Z), W⟫ (f p)`, from germ hypotheses only.**

The germ form of
`ONeillBaseCurvature.tangentMetric_horizontalLeviCivita_horizontalLeviCivita_horizontalLiftField`,
which it strictly generalises: that theorem's `hsub`, `hriem`, `hY` and `hZ` are recovered by
`Filter.Eventually.of_forall`.

**What the relaxation costs, and what makes it possible.** The global hypotheses were used in
exactly two places, and each is now a germ statement:

* the inner Lemma 1(3) substitution, which was an equality of fields on all of `M` and is now
  `horizontalLeviCivita_horizontalLiftField_eventuallyEq`, fed to
  `horizontalLeviCivita_congr_of_eventuallyEq` — that is, to
  `RiemannianGeometry.leviCivita_congr_of_eventuallyEq`. **This is the step for which germ locality of
  the connection was the missing ingredient**;
* the `C¹` regularity of `∇*_Y Z` at `f p`, now
  `contMDiffAt_leviCivita_apply_base_of_eventually`.

Everything else in the proof already consumed its base-field hypotheses eventually. -/
theorem tangentMetric_horizontalLeviCivita_horizontalLeviCivita_horizontalLiftField_of_eventually
    {n : ℕ∞} {W : Π q : B, TangentSpace J q}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ᶠ z in 𝓝 p, IsSubmersionAtPoint I J f z)
    (hriem : ∀ᶠ z in 𝓝 p, IsRiemannianSubmersionAtPoint I J f z)
    (hY : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q)
    (hZ : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Z) q)
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
  have hle : ((n : ℕ∞ω)) ≤ (((n + 1 : ℕ∞)) : ℕ∞ω) := by push_cast; exact le_self_add
  have hfd : MDiffAt f p := ((hf p).of_le hle).mdifferentiableAt hn0
  -- Lemma 1(3) as an equality of fields **near** `p`
  have hfield := horizontalLeviCivita_horizontalLiftField_eventuallyEq (p := p)
    hn hn' hf hgM hgB hsub hriem hY hZ
  have hS1 : ContMDiffAt J J.tangent (((1 : ℕ∞) : ℕ∞ω))
      (T% (fun q ↦ leviCivita (tangentMetric J B) Z q (Y q))) (f p) :=
    contMDiffAt_leviCivita_apply_base_of_eventually hn hgB hY hZ
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
  have e1 := hcM (U₁ := horizontalLiftField I J f X) hSHd hWHd
  have e2 : d% (fun z ↦ tangentMetric I M z (horizontalLiftField I J f
        (fun q ↦ leviCivita (tangentMetric J B) Z q (Y q)) z)
        (horizontalLiftField I J f W z)) p (horizontalLiftField I J f X p)
      = d% (fun q ↦ tangentMetric J B q
          (leviCivita (tangentMetric J B) Z q (Y q)) (W q)) (f p) (X (f p)) :=
    mvfderiv_tangentMetric_horizontalLiftField (Y₁ := X)
      (Y₂ := fun q ↦ leviCivita (tangentMetric J B) Z q (Y q)) (Y₃ := W) hsub hriem hfd
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
        (K := fun q ↦ leviCivita (tangentMetric J B) Z q (Y q)) hn hn' hf hgM hgB hsub hriem hW,
      isSymm_tangentMetric (f p) _ (leviCivita (tangentMetric J B) Z (f p) (Y (f p)))]
  have e4 := hcB (U₁ := X) (U₂ := fun q ↦ leviCivita (tangentMetric J B) Z q (Y q)) (U₃ := W)
    hSd hWd
  rw [horizontalLeviCivita_congr_of_eventuallyEq (D := horizontalLiftField I J f X) hfield,
    horizontalLeviCivita_apply, tangentMetric_horizontalProjection_left,
    mem_horizontalSpace_iff_horizontalProjection_eq_self.mp (horizontalLiftField_mem (Y := W) p)]
  rw [e2, e4, e3] at e1
  linarith [e1]


/-! ## The scalar identification of the base curvature, at germ regularity -/

/-- **`⟪R^H(X, Y)Z, Wᴴ p⟫ = ⟪R*(X, Y)Z, W⟫ (f p)`, from germ hypotheses only.**

The germ form of
`ONeillBaseCurvature.tangentMetric_oneillHorizontalCurvature_horizontalLiftField`, which it
strictly generalises. The proof is the earlier one with the two-derivative case replaced by
`tangentMetric_horizontalLeviCivita_horizontalLeviCivita_horizontalLiftField_of_eventually`; the
single-derivative workhorse already consumed everything eventually. `hsub` and `hriem` relax to
germs at `p` here too.
-/
theorem tangentMetric_oneillHorizontalCurvature_horizontalLiftField_of_eventually {n : ℕ∞}
    {W : Π q : B, TangentSpace J q}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ᶠ z in 𝓝 p, IsSubmersionAtPoint I J f z)
    (hriem : ∀ᶠ z in 𝓝 p, IsRiemannianSubmersionAtPoint I J f z)
    (hX : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% X) q)
    (hY : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q)
    (hZ : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Z) q)
    (hW : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% W) q) :
    tangentMetric I M p (oneillHorizontalCurvature I J f X Y Z p)
        (horizontalLiftField I J f W p)
      = tangentMetric J B (f p)
          (curvature (leviCivita (tangentMetric J B)) X Y Z (f p)) (W (f p)) := by
  rw [oneillHorizontalCurvature_apply, curvature_apply]
  simp only [map_sub, sub_apply]
  rw [tangentMetric_horizontalLeviCivita_horizontalLeviCivita_horizontalLiftField_of_eventually
      hn hn' hf hgM hgB hsub hriem hY hZ hW,
    tangentMetric_horizontalLeviCivita_horizontalLeviCivita_horizontalLiftField_of_eventually
      (X := Y) (Y := X) hn hn' hf hgM hgB hsub hriem hX hZ hW,
    tangentMetric_horizontalLeviCivita_horizontalLiftField (U := mlieBracket J X Y) (V := Z)
      hn hn' hf hgM hgB hsub hriem hZ]

/-! ## Lemma 2 and the bracket term, at germ regularity -/

/-- **`𝓥[Xᴴ, Yᴴ] = 2 A_{Xᴴ}Yᴴ` from germ hypotheses on the base fields.**

The germ form of
`ONeillHorizontalCurvature.verticalProjection_mlieBracket_horizontalLiftField_eq_two_smul_oneillA`.
It does **not** go through `ONeillLemmaTwo`'s basic-field Lemma 2, whose base-field hypotheses are
global; it goes through `ONeillTensoriality.oneillA_eq_two_inv_smul_verticalProjection_mlieBracket`,
which holds for arbitrary horizontal fields and therefore carries **no** base-field hypothesis at
all — only differentiability at `p` of the two lifts, which the germ hypotheses supply. -/
theorem verticalProjection_mlieBracket_horizontalLiftField_eq_two_smul_oneillA_of_eventually
    {n : ℕ∞} (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    (hX : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% X) q)
    (hY : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q) :
    verticalProjection I J f p
        (mlieBracket I (horizontalLiftField I J f X) (horizontalLiftField I J f Y) p)
      = (2 : ℝ) • oneillA I J f (horizontalLiftField I J f X)
          (horizontalLiftField I J f Y) p := by
  have hn0 := coe_ne_zero_of_minSmoothness_two_le hn
  have hXd : MDiffAt (T% (horizontalLiftField I J f X)) p :=
    (contMDiffAt_horizontalLiftField isOpen_univ (Set.mem_univ p) hf.contMDiffOn (hgM p)
      (hgB (f p)) hX.self_of_nhds).mdifferentiableAt hn0
  have hYd : MDiffAt (T% (horizontalLiftField I J f Y)) p :=
    (contMDiffAt_horizontalLiftField isOpen_univ (Set.mem_univ p) hf.contMDiffOn (hgM p)
      (hgB (f p)) hY.self_of_nhds).mdifferentiableAt hn0
  rw [oneillA_eq_two_inv_smul_verticalProjection_mlieBracket hn hn' hf hgM hgB hsub hriem
    isHorizontalField_horizontalLiftField isHorizontalField_horizontalLiftField hXd hYd,
    smul_smul]
  norm_num

/-- **Step 3 of the horizontal curvature equation, at germ regularity.**

    𝓗∇_{[Xᴴ,Yᴴ]}Zᴴ = 𝓗∇_{([X,Y])ᴴ}Zᴴ + 2 A_{Zᴴ}(A_{Xᴴ}Yᴴ)

The germ form of `ONeillHorizontalCurvatureScalar`'s
`horizontalProjection_leviCivita_mlieBracket_horizontalLiftField_of_mdiffAt`. The only change is
that the lifts' regularity near `p` is now assembled from a germ on the base pulled back along
`f` rather than from a global hypothesis; the three ingredients — Lemma 1(2), Lemma 2 and Lemma
3's final clause — already took their base-field hypotheses eventually. -/
theorem horizontalProjection_leviCivita_mlieBracket_horizontalLiftField_of_eventually {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    (hX : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% X) q)
    (hY : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q)
    (hZ : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Z) q)
    (hAXY : MDiffAt (T% (oneillA I J f (horizontalLiftField I J f X)
      (horizontalLiftField I J f Y))) p) :
    horizontalProjection I J f p
        (leviCivita (tangentMetric I M) (horizontalLiftField I J f Z) p
          (mlieBracket I (horizontalLiftField I J f X) (horizontalLiftField I J f Y) p))
      = horizontalLeviCivita I J f (horizontalLiftField I J f (mlieBracket J X Y))
            (horizontalLiftField I J f Z) p
        + (2 : ℝ) • oneillA I J f (horizontalLiftField I J f Z)
            (oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Y)) p := by
  have hle : ((n : ℕ∞ω)) ≤ (((n + 1 : ℕ∞)) : ℕ∞ω) := by push_cast; exact le_self_add
  have hfp : ContMDiffAt I J ((n : ℕ∞ω)) f p := (hf p).of_le hle
  have hfc : ContinuousAt f p := hf.continuous.continuousAt
  have hlift : ∀ T : Π q : B, TangentSpace J q,
      (∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% T) q) → ∀ᶠ z in 𝓝 p,
        ContMDiffAt I I.tangent ((n : ℕ∞ω)) (T% (horizontalLiftField I J f T)) z := by
    intro T hT
    filter_upwards [hfc.eventually hT] with z hz
    exact contMDiffAt_horizontalLiftField isOpen_univ (Set.mem_univ z) hf.contMDiffOn (hgM z)
      (hgB (f z)) hz
  have hsube : ∀ᶠ z in 𝓝 p, IsSubmersionAtPoint I J f z := Filter.Eventually.of_forall hsub
  have hrieme : ∀ᶠ z in 𝓝 p, IsRiemannianSubmersionAtPoint I J f z :=
    Filter.Eventually.of_forall hriem
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
    rw [horizontalProjection_mlieBracket_horizontalLiftField hn hn' hfp hsube hrieme
        (hlift X hX) (hlift Y hY) hX hY,
      verticalProjection_mlieBracket_horizontalLiftField_eq_two_smul_oneillA_of_eventually
        hn hn' hf hgM hgB hsub hriem hX hY] at h
    exact h.symm
  rw [hdec, leviCivita_apply_add_direction, leviCivita_apply_smul_direction, map_add, map_smul,
    ← horizontalLeviCivita_apply, ← horizontalLeviCivita_apply,
    horizontalLeviCivita_vertical_horizontalLiftField_of_mdiffAt hn hn' hf hgM hgB hsub hriem
      isVerticalField_oneillA_horizontalLiftField hAXY (hlift Z hZ) hZ]

/-- **The vector relation `(4)` at germ regularity.**

    𝓗R(Xᴴ, Yᴴ)Zᴴ = R^H(X, Y)Z + A_{Xᴴ}(A_{Yᴴ}Zᴴ) − A_{Yᴴ}(A_{Xᴴ}Zᴴ) − 2 A_{Zᴴ}(A_{Xᴴ}Yᴴ)

The germ form of `ONeillHorizontalCurvatureScalar`'s
`horizontalProjection_curvature_horizontalLiftField_of_mdiffAt`. Steps 1 and 2 carry no
base-field hypothesis; only Step 3 had to be relaxed. -/
theorem horizontalProjection_curvature_horizontalLiftField_of_eventually {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    (hX : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% X) q)
    (hY : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q)
    (hZ : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Z) q)
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
    horizontalProjection_leviCivita_mlieBracket_horizontalLiftField_of_eventually hn hn' hf hgM
      hgB hsub hriem hX hY hZ hAXY,
    oneillHorizontalCurvature_apply]
  abel


/-! ## The scalar dual Gauss equation `{4}` at germ regularity -/

/-- **O'Neill's `{4}`, the scalar form, from germ hypotheses on the base fields.**

    ⟪R(Xᴴ,Yᴴ)Zᴴ, Uᴴ⟫ = ⟪R^H(X,Y)Z, Uᴴ⟫ − ⟪A_XU, A_YZ⟫ + ⟪A_YU, A_XZ⟫ + 2⟪A_ZU, A_XY⟫

The germ form of `ONeillHorizontalCurvatureScalar.tangentMetric_curvature_horizontalLiftField`,
which it strictly generalises: `Filter.Eventually.of_forall` on `hX`, `hY`, `hZ`, `hU` recovers
the earlier statement. Only the vector relation had to be relaxed; the three skew-symmetry
applications and the `𝓗`-drop carry no base-field hypothesis at all.
-/
theorem tangentMetric_curvature_horizontalLiftField_of_eventually {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    (hX : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% X) q)
    (hY : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q)
    (hZ : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Z) q)
    (hU : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% U) q)
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
      (hgB (f p)) hU.self_of_nhds).mdifferentiableAt hn0
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
  rw [hdrop, horizontalProjection_curvature_horizontalLiftField_of_eventually hn hn' hf hgM hgB
    hsub hriem hX hY hZ hAXY hHYZ hAYZ hHXZ hAXZ]
  simp only [map_sub, map_add, map_smul, sub_apply, add_apply, smul_apply, smul_eq_mul]
  linarith [s1, s2, s3]


/-! ## Basic-field regularity and the two `A`-identities, at germ regularity -/

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold J ∞ B]
  [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]
  [Bundle.RiemannianBundle (TangentSpace J : B → Type _)] in
/-- Differentiability of a section at a point depends only on its germ. Used to inherit
`MDiffAt` across the germ forms of the two `A`-identities. -/
theorem mdiffAt_section_congr_of_eventuallyEq {σ τ : Π z : M, TangentSpace I z}
    (h : MDiffAt (T% τ) p) (he : ∀ᶠ z in 𝓝 p, σ z = τ z) : MDiffAt (T% σ) p :=
  h.congr_of_eventuallyEq (he.mono fun z hz ↦ by simp only [hz])

omit [FiniteDimensional ℝ E'] in
/-- **A basic field is differentiable near `p`** as soon as its base field is `C^n` near `f p`.
The germ form of `ONeillCorollaryOne.mdiffAt_horizontalLiftField_of_forall`. -/
theorem mdiffAt_horizontalLiftField_of_eventually {n : ℕ∞} (hn : minSmoothness ℝ 2 ≤ n)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hX : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% X) q) :
    ∀ᶠ z in 𝓝 p, MDiffAt (T% (horizontalLiftField I J f X)) z := by
  have hfc : ContinuousAt f p := hf.continuous.continuousAt
  filter_upwards [hfc.eventually hX] with z hz
  exact (contMDiffAt_horizontalLiftField isOpen_univ (Set.mem_univ z) hf.contMDiffOn (hgM z)
    (hgB (f z)) hz).mdifferentiableAt (coe_ne_zero_of_minSmoothness_two_le hn)

/-- **`A_{Xᴴ}Xᴴ` vanishes near `p`**, the germ form of
`ONeillCorollaryOne.oneillA_horizontalLiftField_self_section_eq_zero`. The pointwise input is
`ONeillTensoriality.oneillA_self_eq_zero`, which is stated for arbitrary horizontal fields and
therefore carries no base-field hypothesis of its own. -/
theorem oneillA_horizontalLiftField_self_eventuallyEq_zero {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    (hX : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% X) q) :
    ∀ᶠ z in 𝓝 p, oneillA I J f (horizontalLiftField I J f X)
      (horizontalLiftField I J f X) z = (0 : Π z : M, TangentSpace I z) z := by
  filter_upwards [mdiffAt_horizontalLiftField_of_eventually hn hf hgM hgB hX] with z hz
  simpa only [Pi.zero_apply] using
    oneillA_self_eq_zero (p := z) hn hn' hf hgM hgB hsub hriem
      isHorizontalField_horizontalLiftField hz

/-- **`A_{Yᴴ}Xᴴ = −A_{Xᴴ}Yᴴ` near `p`**, the germ form of
`ONeillCorollaryOne.oneillA_horizontalLiftField_swap_neg_section`, from
`ONeillTensoriality.oneillA_swap_neg` for arbitrary horizontal fields. -/
theorem oneillA_horizontalLiftField_swap_neg_eventuallyEq {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    (hX : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% X) q)
    (hY : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q) :
    ∀ᶠ z in 𝓝 p, oneillA I J f (horizontalLiftField I J f Y)
        (horizontalLiftField I J f X) z
      = (-oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Y)) z := by
  filter_upwards [mdiffAt_horizontalLiftField_of_eventually hn hf hgM hgB hX,
    mdiffAt_horizontalLiftField_of_eventually hn hf hgM hgB hY] with z hzX hzY
  simpa only [Pi.neg_apply] using
    oneillA_swap_neg (p := z) hn hn' hf hgM hgB hsub hriem
      (X := horizontalLiftField I J f Y) (W := horizontalLiftField I J f X)
      isHorizontalField_horizontalLiftField isHorizontalField_horizontalLiftField hzY hzX

/-! ## `{4}` with the base curvature, and its diagonal case, at germ regularity -/

/-- **`{4}` with the curvature of the base, from germ hypotheses.** The germ form of
`ONeillCorollaryOne.tangentMetric_curvature_horizontalLiftField_base`. -/
theorem tangentMetric_curvature_horizontalLiftField_base_of_eventually {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    (hX : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% X) q)
    (hY : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q)
    (hZ : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Z) q)
    (hU : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% U) q)
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
      = tangentMetric J B (f p)
            (curvature (leviCivita (tangentMetric J B)) X Y Z (f p)) (U (f p))
        - tangentMetric I M p
            (oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f U) p)
            (oneillA I J f (horizontalLiftField I J f Y) (horizontalLiftField I J f Z) p)
        + tangentMetric I M p
            (oneillA I J f (horizontalLiftField I J f Y) (horizontalLiftField I J f U) p)
            (oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Z) p)
        + 2 * tangentMetric I M p
            (oneillA I J f (horizontalLiftField I J f Z) (horizontalLiftField I J f U) p)
            (oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Y) p) := by
  rw [tangentMetric_curvature_horizontalLiftField_of_eventually hn hn' hf hgM hgB hsub hriem
      hX hY hZ hU hAXY hHYZ hAYZ hHXZ hAXZ,
    tangentMetric_oneillHorizontalCurvature_horizontalLiftField_of_eventually hn hn' hf hgM hgB
      (Filter.Eventually.of_forall hsub) (Filter.Eventually.of_forall hriem) hX hY hZ hU]

/-- **`{4}` with `Z := X`, `U := Y`, from germ hypotheses** — where the factor `3` appears as
`1 + 0 + 2`. The germ form of
`ONeillCorollaryOne.tangentMetric_curvature_horizontalLiftField_self`.

The two differentiability hypotheses that the diagonal substitution discharges are discharged
here from the *germ* forms of the two `A`-identities, through
`mdiffAt_section_congr_of_eventuallyEq`: a section equal to `0` (resp. to `−A_{Xᴴ}Yᴴ`) only near
`p` is still differentiable at `p`. -/
theorem tangentMetric_curvature_horizontalLiftField_self_of_eventually {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    (hX : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% X) q)
    (hY : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q)
    (hAXY : MDiffAt (T% (oneillA I J f (horizontalLiftField I J f X)
      (horizontalLiftField I J f Y))) p)
    (hHYX : MDiffAt (T% (horizontalLeviCivita I J f (horizontalLiftField I J f Y)
      (horizontalLiftField I J f X))) p)
    (hHXX : MDiffAt (T% (horizontalLeviCivita I J f (horizontalLiftField I J f X)
      (horizontalLiftField I J f X))) p) :
    tangentMetric I M p
        (curvature (leviCivita (tangentMetric I M)) (horizontalLiftField I J f X)
          (horizontalLiftField I J f Y) (horizontalLiftField I J f X) p)
        (horizontalLiftField I J f Y p)
      = tangentMetric J B (f p)
            (curvature (leviCivita (tangentMetric J B)) X Y X (f p)) (Y (f p))
        + 3 * tangentMetric I M p
            (oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Y) p)
            (oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Y) p) := by
  have hzero := oneillA_horizontalLiftField_self_eventuallyEq_zero hn hn' hf hgM hgB hsub hriem hX
  have hswap :=
    oneillA_horizontalLiftField_swap_neg_eventuallyEq hn hn' hf hgM hgB hsub hriem hX hY
  have hAXX : MDiffAt (T% (oneillA I J f (horizontalLiftField I J f X)
      (horizontalLiftField I J f X))) p :=
    mdiffAt_section_congr_of_eventuallyEq (mdifferentiableAt_zeroSection ..) hzero
  have hAYX : MDiffAt (T% (oneillA I J f (horizontalLiftField I J f Y)
      (horizontalLiftField I J f X))) p :=
    mdiffAt_section_congr_of_eventuallyEq (mdifferentiableAt_neg_section hAXY) hswap
  have hXd : MDiffAt (T% (horizontalLiftField I J f X)) p :=
    (mdiffAt_horizontalLiftField_of_eventually hn hf hgM hgB hX).self_of_nhds
  have hYd : MDiffAt (T% (horizontalLiftField I J f Y)) p :=
    (mdiffAt_horizontalLiftField_of_eventually hn hf hgM hgB hY).self_of_nhds
  rw [tangentMetric_curvature_horizontalLiftField_base_of_eventually (Z := X) (U := Y)
      hn hn' hf hgM hgB hsub hriem hX hY hX hY hAXY hHYX hAYX hHXX hAXX,
    oneillA_swap_neg (p := p) hn hn' hf hgM hgB hsub hriem
      (X := horizontalLiftField I J f Y) (W := horizontalLiftField I J f X)
      isHorizontalField_horizontalLiftField isHorizontalField_horizontalLiftField hYd hXd,
    oneillA_self_eq_zero (p := p) hn hn' hf hgM hgB hsub hriem
      (X := horizontalLiftField I J f X) isHorizontalField_horizontalLiftField hXd]
  simp only [map_neg, map_zero]
  ring


/-! ## The regularity discharge at germ regularity -/

omit [FiniteDimensional ℝ E'] in
/-- **A basic field is `C²` on an open neighbourhood of `p`** when its base field is `C^n` near
`f p`. The germ replacement for `ONeillBasicRegularity.contMDiffOn_horizontalLiftField_two`,
which produces the same conclusion on `Set.univ` from a global base-field hypothesis. The open
set is what `contMDiffAt_leviCivita` and `contMDiffAt_horizontalPart` consume, and it is
extracted from the germ by `eventually_nhds_iff`. -/
theorem exists_isOpen_contMDiffOn_horizontalLiftField_two {n : ℕ∞} (hn : minSmoothness ℝ 2 ≤ n)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hX : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% X) q) :
    ∃ u : Set M, IsOpen u ∧ p ∈ u ∧
      CMDiff[u] ((2 : ℕ∞)) (T% (horizontalLiftField I J f X)) := by
  have hn2 : (2 : ℕ∞) ≤ n := two_le_of_minSmoothness_two_le hn
  have h2 : ((2 : ℕ∞) : ℕ∞ω) ≤ ((n : ℕ∞ω)) := WithTop.coe_le_coe.mpr hn2
  have hf3 : ContMDiffOn I J (((2 : ℕ∞) + 1 : ℕ∞)) f univ :=
    (hf.of_le (WithTop.coe_le_coe.mpr (by gcongr))).contMDiffOn
  have hfc : ContinuousAt f p := hf.continuous.continuousAt
  obtain ⟨u, hXu, hu, hpu⟩ := eventually_nhds_iff.mp (hfc.eventually hX)
  refine ⟨u, hu, hpu, fun z hz ↦ ?_⟩
  exact (contMDiffAt_horizontalLiftField (m := 2) isOpen_univ (mem_univ z) hf3
    ((hgM z).of_le h2) ((hgB (f z)).of_le h2) ((hXu z hz).of_le h2)).contMDiffWithinAt

omit [FiniteDimensional ℝ E'] in
/-- **`∇_{Xᴴ}Yᴴ` is `C¹` at `p`, at metrics `C²`, from germ hypotheses.** The germ form of
`ONeillBasicRegularity.contMDiffAt_leviCivita_horizontalLiftField`; the two open neighbourhoods
supplied by `exists_isOpen_contMDiffOn_horizontalLiftField_two` are intersected, which is the
only structural change. -/
theorem contMDiffAt_leviCivita_horizontalLiftField_of_eventually {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hX : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% X) q)
    (hY : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q) :
    ContMDiffAt I I.tangent (((1 : ℕ∞) : ℕ∞ω))
      (T% (fun z ↦ leviCivita (tangentMetric I M) (horizontalLiftField I J f Y) z
        (horizontalLiftField I J f X z))) p := by
  have hn2 : (2 : ℕ∞) ≤ n := two_le_of_minSmoothness_two_le hn
  have h2 : ((2 : ℕ∞) : ℕ∞ω) ≤ ((n : ℕ∞ω)) := WithTop.coe_le_coe.mpr hn2
  obtain ⟨uX, huX, hpX, hXu⟩ := exists_isOpen_contMDiffOn_horizontalLiftField_two hn hf hgM hgB hX
  obtain ⟨uY, huY, hpY, hYu⟩ := exists_isOpen_contMDiffOn_horizontalLiftField_two hn hf hgM hgB hY
  have hu : IsOpen (uX ∩ uY) := huX.inter huY
  have hpu : p ∈ uX ∩ uY := ⟨hpX, hpY⟩
  have hgM2 : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ((2 : ℕ∞))
      (fun z ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun (z : M) ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ) z
        (tangentMetric I M z)) (uX ∩ uY) :=
    fun z _ ↦ ((hgM z).of_le h2).contMDiffWithinAt
  have hXH1 : ContMDiffAt I I.tangent (((1 : ℕ∞) : ℕ∞ω))
      (T% (horizontalLiftField I J f X)) p :=
    ((hXu p hpX).contMDiffAt (huX.mem_nhds hpX)).of_le (WithTop.coe_le_coe.mpr (by norm_num))
  exact ContMDiffAt.clm_bundle_apply
    (contMDiffAt_leviCivita (m := 1) hu hpu isSymm_tangentMetric
      isNondegenerate_tangentMetric hgM2 (fun z hz ↦ (hYu z hz.2).mono inter_subset_right)) hXH1

omit [FiniteDimensional ℝ E'] in
/-- **`𝓗∇_{Xᴴ}Yᴴ` is `C¹` at `p`, at metrics `C²`, from germ hypotheses.** -/
theorem contMDiffAt_horizontalLeviCivita_horizontalLiftField_of_eventually {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ᶠ z in 𝓝 p, IsSubmersionAtPoint I J f z)
    (hriem : ∀ᶠ z in 𝓝 p, IsRiemannianSubmersionAtPoint I J f z)
    (hX : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% X) q)
    (hY : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q) :
    ContMDiffAt I I.tangent (((1 : ℕ∞) : ℕ∞ω))
      (T% (horizontalLeviCivita I J f (horizontalLiftField I J f X)
        (horizontalLiftField I J f Y))) p := by
  have hn2 : (2 : ℕ∞) ≤ n := two_le_of_minSmoothness_two_le hn
  have h1n : (1 : ℕ∞) ≤ n := le_trans (by norm_num) hn2
  have h1 : ((1 : ℕ∞) : ℕ∞ω) ≤ ((n : ℕ∞ω)) := WithTop.coe_le_coe.mpr h1n
  have hf2 : ContMDiffOn I J (((1 : ℕ∞) + 1 : ℕ∞)) f univ :=
    (hf.of_le (WithTop.coe_le_coe.mpr (by gcongr))).contMDiffOn
  exact contMDiffAt_horizontalPart (m := 1) isOpen_univ (mem_univ p) hf2
    ((hgM p).of_le h1) ((hgB (f p)).of_le h1) hsub hriem
    (contMDiffAt_leviCivita_horizontalLiftField_of_eventually hn hf hgM hgB hX hY)

omit [FiniteDimensional ℝ E'] in
/-- **`𝓥∇_{Xᴴ}Yᴴ` is `C¹` at `p`, at metrics `C²`, from germ hypotheses.** -/
theorem contMDiffAt_verticalPart_leviCivita_horizontalLiftField_of_eventually {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ᶠ z in 𝓝 p, IsSubmersionAtPoint I J f z)
    (hriem : ∀ᶠ z in 𝓝 p, IsRiemannianSubmersionAtPoint I J f z)
    (hX : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% X) q)
    (hY : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q) :
    ContMDiffAt I I.tangent (((1 : ℕ∞) : ℕ∞ω))
      (T% (verticalPart I J f (fun z ↦ leviCivita (tangentMetric I M)
        (horizontalLiftField I J f Y) z (horizontalLiftField I J f X z)))) p := by
  have hn2 : (2 : ℕ∞) ≤ n := two_le_of_minSmoothness_two_le hn
  have h1n : (1 : ℕ∞) ≤ n := le_trans (by norm_num) hn2
  have h1 : ((1 : ℕ∞) : ℕ∞ω) ≤ ((n : ℕ∞ω)) := WithTop.coe_le_coe.mpr h1n
  have hf2 : ContMDiffOn I J (((1 : ℕ∞) + 1 : ℕ∞)) f univ :=
    (hf.of_le (WithTop.coe_le_coe.mpr (by gcongr))).contMDiffOn
  exact contMDiffAt_verticalPart (m := 1) isOpen_univ (mem_univ p) hf2
    ((hgM p).of_le h1) ((hgB (f p)).of_le h1) hsub hriem
    (contMDiffAt_leviCivita_horizontalLiftField_of_eventually hn hf hgM hgB hX hY)

omit [FiniteDimensional ℝ E'] in
/-- **`A_{Xᴴ}Yᴴ` is `C¹` at `p`, at metrics `C²`, from germ hypotheses.** -/
theorem contMDiffAt_oneillA_horizontalLiftField_of_eventually {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ᶠ z in 𝓝 p, IsSubmersionAtPoint I J f z)
    (hriem : ∀ᶠ z in 𝓝 p, IsRiemannianSubmersionAtPoint I J f z)
    (hX : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% X) q)
    (hY : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q) :
    ContMDiffAt I I.tangent (((1 : ℕ∞) : ℕ∞ω))
      (T% (oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Y))) p := by
  have heq : oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Y)
      = verticalPart I J f (fun z ↦ leviCivita (tangentMetric I M)
        (horizontalLiftField I J f Y) z (horizontalLiftField I J f X z)) :=
    funext fun z ↦ oneillA_horizontal_horizontal isHorizontalField_horizontalLiftField
      isHorizontalField_horizontalLiftField z
  rw [heq]
  exact contMDiffAt_verticalPart_leviCivita_horizontalLiftField_of_eventually hn hf hgM hgB
    hsub hriem hX hY

omit [FiniteDimensional ℝ E'] in
/-- `𝓗∇_{Xᴴ}Yᴴ` is differentiable at `p`, from germ hypotheses. -/
theorem mdiffAt_horizontalLeviCivita_horizontalLiftField_of_eventually {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ᶠ z in 𝓝 p, IsSubmersionAtPoint I J f z)
    (hriem : ∀ᶠ z in 𝓝 p, IsRiemannianSubmersionAtPoint I J f z)
    (hX : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% X) q)
    (hY : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q) :
    MDiffAt (T% (horizontalLeviCivita I J f (horizontalLiftField I J f X)
      (horizontalLiftField I J f Y))) p :=
  (contMDiffAt_horizontalLeviCivita_horizontalLiftField_of_eventually hn hf hgM hgB hsub hriem
    hX hY).mdifferentiableAt (by simp)

omit [FiniteDimensional ℝ E'] in
/-- `A_{Xᴴ}Yᴴ` is differentiable at `p`, from germ hypotheses. -/
theorem mdiffAt_oneillA_horizontalLiftField_of_eventually {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ᶠ z in 𝓝 p, IsSubmersionAtPoint I J f z)
    (hriem : ∀ᶠ z in 𝓝 p, IsRiemannianSubmersionAtPoint I J f z)
    (hX : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% X) q)
    (hY : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q) :
    MDiffAt (T% (oneillA I J f (horizontalLiftField I J f X)
      (horizontalLiftField I J f Y))) p :=
  (contMDiffAt_oneillA_horizontalLiftField_of_eventually hn hf hgM hgB hsub hriem hX
    hY).mdifferentiableAt (by simp)


/-! ## Corollary 1(3) at germ regularity -/

omit [FiniteDimensional ℝ E'] in
/-- A basic field is `C²` at every point of a neighbourhood of `p`, in the eventual form the
Riemann-tensor layer consumes. -/
theorem eventually_contMDiffAt_horizontalLiftField_two {n : ℕ∞} (hn : minSmoothness ℝ 2 ≤ n)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hX : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% X) q) :
    ∀ᶠ z in 𝓝 p,
      ContMDiffAt I I.tangent (((2 : ℕ∞) : ℕ∞ω)) (T% (horizontalLiftField I J f X)) z := by
  obtain ⟨u, hu, hpu, hXu⟩ := exists_isOpen_contMDiffOn_horizontalLiftField_two hn hf hgM hgB hX
  filter_upwards [hu.mem_nhds hpu] with z hz
  exact (hXu z hz).contMDiffAt (hu.mem_nhds hz)

/-- **Corollary 1(3), unnormalised, from germ hypotheses.** The germ form of
`ONeillCorollaryOne.riemannTensorAt_horizontalLiftField`. -/
theorem riemannTensorAt_horizontalLiftField_of_eventually
    (hsymmM : IsSymm (tangentMetric I M)) (hndM : IsNondegenerate (tangentMetric I M))
    (hsymmB : IsSymm (tangentMetric J B)) (hndB : IsNondegenerate (tangentMetric J B))
    (hf : ContMDiff I J ((3 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((2 : ℕ∞)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((2 : ℕ∞)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    (hX : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent (((2 : ℕ∞) : ℕ∞ω)) (T% X) q)
    (hY : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent (((2 : ℕ∞) : ℕ∞ω)) (T% Y) q) :
    riemannTensorAt hsymmM hndM hgM p (horizontalLiftField I J f X p)
        (horizontalLiftField I J f Y p) (horizontalLiftField I J f Y p)
        (horizontalLiftField I J f X p)
      = riemannTensorAt hsymmB hndB hgB (f p) (X (f p)) (Y (f p)) (Y (f p)) (X (f p))
        - 3 * tangentMetric I M p
            (oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Y) p)
            (oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Y) p) := by
  have hf3 : ContMDiff I J (((2 : ℕ∞) + 1 : ℕ∞)) f := by
    rwa [show ((2 : ℕ∞) + 1 : ℕ∞) = (3 : ℕ∞) by norm_num]
  have hn : minSmoothness ℝ 2 ≤ (2 : ℕ∞) := by simp
  have hsube : ∀ᶠ z in 𝓝 p, IsSubmersionAtPoint I J f z := Filter.Eventually.of_forall hsub
  have hrieme : ∀ᶠ z in 𝓝 p, IsRiemannianSubmersionAtPoint I J f z :=
    Filter.Eventually.of_forall hriem
  have hXHe := eventually_contMDiffAt_horizontalLiftField_two hn hf3 hgM hgB hX
  have hYHe := eventually_contMDiffAt_horizontalLiftField_two hn hf3 hgM hgB hY
  have hM := riemannTensorAt_apply_fields hsymmM hndM hgM
    (X := horizontalLiftField I J f X) (Y := horizontalLiftField I J f Y)
    (Z := horizontalLiftField I J f X) (W := horizontalLiftField I J f Y) (x := p)
    hXHe hYHe hXHe.self_of_nhds
  have hB := riemannTensorAt_apply_fields hsymmB hndB hgB
    (X := X) (Y := Y) (Z := X) (W := Y) (x := f p) hX hY hX.self_of_nhds
  have hAXY := mdiffAt_oneillA_horizontalLiftField_of_eventually hn hf3 hgM hgB hsube hrieme hX hY
  have hHYX := mdiffAt_horizontalLeviCivita_horizontalLiftField_of_eventually hn hf3 hgM hgB
    hsube hrieme hY hX
  have hHXX := mdiffAt_horizontalLeviCivita_horizontalLiftField_of_eventually hn hf3 hgM hgB
    hsube hrieme hX hX
  have hD2 := tangentMetric_curvature_horizontalLiftField_self_of_eventually (n := 2) (by simp)
    (by simp) hf3 hgM hgB hsub hriem hX hY hAXY hHYX hHXX
  have hswM := riemannTensorAt_swap_right hsymmM hndM hgM (horizontalLiftField I J f X p)
    (horizontalLiftField I J f Y p) (horizontalLiftField I J f Y p)
    (horizontalLiftField I J f X p)
  have hswB := riemannTensorAt_swap_right hsymmB hndB hgB (X (f p)) (Y (f p)) (Y (f p)) (X (f p))
  linarith [hM, hB, hD2, hswM, hswB]

/-- **O'Neill's Corollary 1(3), from germ hypotheses on the base fields.** The germ form of
`ONeillCorollaryOne.sectionalCurvatureAt_horizontalLiftField`, and the last step before the
statement for arbitrary horizontal vectors.
-/
theorem sectionalCurvatureAt_horizontalLiftField_of_eventually
    (hsymmM : IsSymm (tangentMetric I M)) (hposM : IsPosDef (tangentMetric I M))
    (hsymmB : IsSymm (tangentMetric J B)) (hposB : IsPosDef (tangentMetric J B))
    (hf : ContMDiff I J ((3 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((2 : ℕ∞)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((2 : ℕ∞)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    (hX : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent (((2 : ℕ∞) : ℕ∞ω)) (T% X) q)
    (hY : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent (((2 : ℕ∞) : ℕ∞ω)) (T% Y) q) :
    sectionalCurvatureAt hsymmM hposM hgM p (horizontalLiftField I J f X p)
        (horizontalLiftField I J f Y p)
      = sectionalCurvatureAt hsymmB hposB hgB (f p) (X (f p)) (Y (f p))
        - 3 * tangentMetric I M p
              (oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Y) p)
              (oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Y) p)
            / gramDet (tangentMetric I M) p (horizontalLiftField I J f X p)
              (horizontalLiftField I J f Y p) := by
  rw [sectionalCurvatureAt_def, sectionalCurvatureAt_def,
    riemannTensorAt_horizontalLiftField_of_eventually hsymmM (IsPosDef.isNondegenerate hposM)
      hsymmB (IsPosDef.isNondegenerate hposB) hf hgM hgB hsub hriem hX hY,
    gramDet_horizontalLiftField (hsub p) (hriem p), sub_div]

/-! ## Corollary 1(3) for arbitrary horizontal vectors -/

omit [FiniteDimensional ℝ E'] in
/-- **Every horizontal vector at `p` is the value at `p` of a differentiable horizontal field.**
`exists_basic_eq_of_mem_horizontalSpace` supplies the basic field, whose germ regularity is enough
for `MDiffAt`. Packaged so the statements below need name no field. -/
theorem exists_isHorizontalField_mdiffAt_eq
    (hf : ContMDiff I J ((3 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((2 : ℕ∞)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((2 : ℕ∞)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    {u : TangentSpace I p} (hu : u ∈ horizontalSpace I J f p) :
    ∃ D : Π z : M, TangentSpace I z,
      IsHorizontalField I J f D ∧ MDiffAt (T% D) p ∧ D p = u := by
  have hf3 : ContMDiff I J (((2 : ℕ∞) + 1 : ℕ∞)) f := by
    rwa [show ((2 : ℕ∞) + 1 : ℕ∞) = (3 : ℕ∞) by norm_num]
  obtain ⟨W, hWe, hWu⟩ := exists_basic_eq_of_mem_horizontalSpace (m := 2) (hsub p) (hriem p) hu
  refine ⟨horizontalLiftField I J f W, isHorizontalField_horizontalLiftField, ?_, hWu⟩
  exact (contMDiffAt_horizontalLiftField isOpen_univ (Set.mem_univ p) hf3.contMDiffOn (hgM p)
    (hgB (f p)) hWe.self_of_nhds).mdifferentiableAt (by simp)

/-- **O'Neill's Corollary 1(3) for arbitrary horizontal vectors.**

    K_M(u, v) = K_B(dπ_p u, dπ_p v) − 3 ⟪A_u v, A_u v⟫ / ‖u ∧ v‖²,   u, v ∈ H_p

The plane upstairs is spanned by **arbitrary** horizontal vectors `u`, `v ∈ horizontalSpace I J f p`
and the plane downstairs is O'Neill's `P_{x_* y_*}`, spanned by `dπ_p u` and `dπ_p v`. Neither side
mentions a base field.

The `A`-value is `A_D F p` for **any** pair of horizontal fields `D`, `F`, differentiable at `p`,
with `D p = u` and `F p = v`; by `ONeillTensoriality.oneillA_congr_direction` and
`ONeillTensoriality.oneillA_eq_of_eq_at` this value does not depend on the choice, so `A_u v` is
well defined and the statement is the honest one. Nothing forces `D` and `F` to be basic.

**The hypotheses on the two fields are deliberately asymmetric, and minimally so.** `A_D F p`
sees the direction field `D` only through `𝓗_p(D p)`, so `D` carries **no** horizontality and
**no** differentiability hypothesis at all — only `D p = u`, with `u` horizontal by `hu`. The
field slot is the one that has to be moved by order-zero tensoriality, so `F` carries both.

**Why this is the payoff of germ locality.** The proof picks basic fields `X`, `Y` through `u` and
`v` by `HorizontalLift.exists_basic_eq_of_mem_horizontalSpace`, which certifies them `C²` only on a
**neighbourhood** of `f p`. Every earlier form of Corollary 1(3) demanded base fields `C²` at every
point of `B` and so could not consume them; the germ chain of this file can, and germ locality of
`leviCivita` (`RiemannianGeometry.leviCivita_congr_of_eventuallyEq`) is what makes that chain exist.
-/
theorem sectionalCurvatureAt_of_mem_horizontalSpace
    (hsymmM : IsSymm (tangentMetric I M)) (hposM : IsPosDef (tangentMetric I M))
    (hsymmB : IsSymm (tangentMetric J B)) (hposB : IsPosDef (tangentMetric J B))
    (hf : ContMDiff I J ((3 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((2 : ℕ∞)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((2 : ℕ∞)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    {u v : TangentSpace I p} {D F : Π z : M, TangentSpace I z}
    (hu : u ∈ horizontalSpace I J f p) (hDu : D p = u)
    (hFhor : IsHorizontalField I J f F) (hFd : MDiffAt (T% F) p) (hFv : F p = v) :
    sectionalCurvatureAt hsymmM hposM hgM p u v
      = sectionalCurvatureAt hsymmB hposB hgB (f p) (mfderiv I J f p u) (mfderiv I J f p v)
        - 3 * tangentMetric I M p (oneillA I J f D F p) (oneillA I J f D F p)
            / gramDet (tangentMetric I M) p u v := by
  have hf3 : ContMDiff I J (((2 : ℕ∞) + 1 : ℕ∞)) f := by
    rwa [show ((2 : ℕ∞) + 1 : ℕ∞) = (3 : ℕ∞) by norm_num]
  have hgm : IsMDiffMetric E (tangentMetric I M) :=
    IsContMDiffMetricSection.isMDiffMetric (by simp) hgM
  have hv : v ∈ horizontalSpace I J f p := hFv ▸ hFhor p
  obtain ⟨X, hXe, hXu⟩ := exists_basic_eq_of_mem_horizontalSpace (m := 2) (hsub p) (hriem p) hu
  obtain ⟨Y, hYe, hYv⟩ := exists_basic_eq_of_mem_horizontalSpace (m := 2) (hsub p) (hriem p) hv
  have hXHhor : IsHorizontalField I J f (horizontalLiftField I J f X) :=
    isHorizontalField_horizontalLiftField
  have hYHhor : IsHorizontalField I J f (horizontalLiftField I J f Y) :=
    isHorizontalField_horizontalLiftField
  have hXHd : MDiffAt (T% (horizontalLiftField I J f X)) p :=
    (contMDiffAt_horizontalLiftField isOpen_univ (Set.mem_univ p) hf3.contMDiffOn (hgM p)
      (hgB (f p)) hXe.self_of_nhds).mdifferentiableAt (by simp)
  have hYHd : MDiffAt (T% (horizontalLiftField I J f Y)) p :=
    (contMDiffAt_horizontalLiftField isOpen_univ (Set.mem_univ p) hf3.contMDiffOn (hgM p)
      (hgB (f p)) hYe.self_of_nhds).mdifferentiableAt (by simp)
  -- the base values are the differentials of `u` and `v`
  have hXval : X (f p) = mfderiv I J f p u := by
    rw [← hXu, mfderiv_horizontalLiftField (hsub p) (hriem p)]
  have hYval : Y (f p) = mfderiv I J f p v := by
    rw [← hYv, mfderiv_horizontalLiftField (hsub p) (hriem p)]
  -- the `A`-value does not depend on the pair of fields chosen through `u` and `v`
  have htest := exists_mdiffAt_parts_eq_of_isContMDiffMetricSection (p := p) (n := 2) (by simp)
    hf3 hgM hgB hsub hriem
  have hA : oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Y) p
      = oneillA I J f D F p := by
    rw [oneillA_congr_direction (D' := D) (F := horizontalLiftField I J f Y)
        (by rw [hXu, hDu]),
      oneillA_eq_of_eq_at hgm htest
        (mdiffAt_horizontalPart_of_isHorizontalField hYHhor hYHd)
        (mdiffAt_verticalPart_of_isHorizontalField hYHhor hYHd)
        (mdiffAt_horizontalPart_of_isHorizontalField hFhor hFd)
        (mdiffAt_verticalPart_of_isHorizontalField hFhor hFd) (by rw [hYv, hFv])]
  rw [← hXu, ← hYv, sectionalCurvatureAt_horizontalLiftField_of_eventually hsymmM hposM hsymmB
    hposB hf hgM hgB hsub hriem hXe hYe, hXval, hYval, hA, hXu, hYv]

/-- **`K_M ≤ K_B` on an arbitrary horizontal 2-plane.**

    K_M(u, v) ≤ K_B(dπ_p u, dπ_p v),    u, v ∈ H_p linearly independent

**No vector field occurs in the statement.** This is the inequality the dependency chain cites,
now for every horizontal plane rather than only for planes spanned by values of globally `C²`
basic fields.
-/
theorem sectionalCurvatureAt_le_of_mem_horizontalSpace
    (hsymmM : IsSymm (tangentMetric I M)) (hposM : IsPosDef (tangentMetric I M))
    (hsymmB : IsSymm (tangentMetric J B)) (hposB : IsPosDef (tangentMetric J B))
    (hf : ContMDiff I J ((3 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((2 : ℕ∞)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((2 : ℕ∞)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    {u v : TangentSpace I p} (hu : u ∈ horizontalSpace I J f p)
    (hv : v ∈ horizontalSpace I J f p) (hli : LinearIndependent ℝ ![u, v]) :
    sectionalCurvatureAt hsymmM hposM hgM p u v
      ≤ sectionalCurvatureAt hsymmB hposB hgB (f p) (mfderiv I J f p u) (mfderiv I J f p v) := by
  obtain ⟨D, -, -, hDu⟩ :=
    exists_isHorizontalField_mdiffAt_eq hf hgM hgB hsub hriem hu
  obtain ⟨F, hFhor, hFd, hFv⟩ :=
    exists_isHorizontalField_mdiffAt_eq hf hgM hgB hsub hriem hv
  rw [sectionalCurvatureAt_of_mem_horizontalSpace hsymmM hposM hsymmB hposB hf hgM hgB hsub
    hriem hu hDu hFhor hFd hFv]
  have hnum : (0 : ℝ) ≤ 3 * tangentMetric I M p (oneillA I J f D F p) (oneillA I J f D F p) := by
    have := hposM.nonneg p (oneillA I J f D F p)
    linarith
  have hden : 0 < gramDet (tangentMetric I M) p u v := gramDet_pos hsymmM hposM hli
  have := div_nonneg hnum hden.le
  linarith

/-- **`K_M ≤ K_B` on an orthonormal horizontal pair**, with no independence hypothesis: it is
supplied by `linearIndependent_pair_of_orthonormal`.
-/
theorem sectionalCurvatureAt_le_of_mem_horizontalSpace_of_orthonormal
    (hsymmM : IsSymm (tangentMetric I M)) (hposM : IsPosDef (tangentMetric I M))
    (hsymmB : IsSymm (tangentMetric J B)) (hposB : IsPosDef (tangentMetric J B))
    (hf : ContMDiff I J ((3 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((2 : ℕ∞)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((2 : ℕ∞)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    {u v : TangentSpace I p} (hu : u ∈ horizontalSpace I J f p)
    (hv : v ∈ horizontalSpace I J f p)
    (huu : tangentMetric I M p u u = 1) (hvv : tangentMetric I M p v v = 1)
    (huv : tangentMetric I M p u v = 0) :
    sectionalCurvatureAt hsymmM hposM hgM p u v
      ≤ sectionalCurvatureAt hsymmB hposB hgB (f p) (mfderiv I J f p u) (mfderiv I J f p v) :=
  sectionalCurvatureAt_le_of_mem_horizontalSpace hsymmM hposM hsymmB hposB hf hgM hgB hsub hriem
    hu hv (linearIndependent_pair_of_orthonormal hsymmM huu hvv huv)

/-- **Nonnegative sectional curvature is inherited by the base, on an arbitrary horizontal
plane.**

    0 ≤ K_M(u, v)  →  0 ≤ K_B(dπ_p u, dπ_p v),    u, v ∈ H_p linearly independent

The statement `GM1974` invokes, with the antecedent at the **single** plane spanned by `u` and `v`
and with no vector field anywhere. This is the form in which the inequality is consumed by the
dependency chain: `GM1974` needs nonnegative curvature on the 2-planes of the quotient spanned by
arbitrary tangent vectors, and an arbitrary 2-plane of `T_{f p}B` is `dπ_p` of an arbitrary
horizontal 2-plane of `T_pM`.

**What is still missing for "`B` has nonnegative sectional curvature", stated so it is not read
into this.** Surjectivity of `f`, so that every point of `B` is an `f p`; and, at such a point,
that every 2-plane of `T_{f p}B` is the `dπ_p`-image of a horizontal 2-plane — which is
`AdjointProjection`'s isomorphism `dπ_p : H_p ≃ T_{f p}B`, available in this library but not
assembled into that statement here. What has changed relative to
`nonneg_sectionalCurvatureAt_of_nonneg_horizontalLiftField` is the *third* missing ingredient,
which was the extension of a pair of tangent vectors to globally `C²` base fields: that is no
longer needed.

**Consumers, not sources.** `GM1974` abstract p. 401 and `W2001_LOTS` introduction p. 161 cite
this inheritance. **Nothing about `GM1974` is formalised here.** -/
theorem nonneg_sectionalCurvatureAt_of_nonneg_of_mem_horizontalSpace
    (hsymmM : IsSymm (tangentMetric I M)) (hposM : IsPosDef (tangentMetric I M))
    (hsymmB : IsSymm (tangentMetric J B)) (hposB : IsPosDef (tangentMetric J B))
    (hf : ContMDiff I J ((3 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((2 : ℕ∞)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((2 : ℕ∞)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    {u v : TangentSpace I p} (hu : u ∈ horizontalSpace I J f p)
    (hv : v ∈ horizontalSpace I J f p) (hli : LinearIndependent ℝ ![u, v])
    (hM : 0 ≤ sectionalCurvatureAt hsymmM hposM hgM p u v) :
    0 ≤ sectionalCurvatureAt hsymmB hposB hgB (f p) (mfderiv I J f p u) (mfderiv I J f p v) :=
  hM.trans (sectionalCurvatureAt_le_of_mem_horizontalSpace hsymmM hposM hsymmB hposB hf hgM hgB
    hsub hriem hu hv hli)

/-- **Nonnegativity inheritance on an orthonormal horizontal pair**, with no independence
hypothesis.
-/
theorem nonneg_sectionalCurvatureAt_of_nonneg_of_mem_horizontalSpace_of_orthonormal
    (hsymmM : IsSymm (tangentMetric I M)) (hposM : IsPosDef (tangentMetric I M))
    (hsymmB : IsSymm (tangentMetric J B)) (hposB : IsPosDef (tangentMetric J B))
    (hf : ContMDiff I J ((3 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((2 : ℕ∞)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((2 : ℕ∞)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    {u v : TangentSpace I p} (hu : u ∈ horizontalSpace I J f p)
    (hv : v ∈ horizontalSpace I J f p)
    (huu : tangentMetric I M p u u = 1) (hvv : tangentMetric I M p v v = 1)
    (huv : tangentMetric I M p u v = 0)
    (hM : 0 ≤ sectionalCurvatureAt hsymmM hposM hgM p u v) :
    0 ≤ sectionalCurvatureAt hsymmB hposB hgB (f p) (mfderiv I J f p u) (mfderiv I J f p v) :=
  hM.trans (sectionalCurvatureAt_le_of_mem_horizontalSpace_of_orthonormal hsymmM hposM hsymmB
    hposB hf hgM hgB hsub hriem hu hv huu hvv huv)

/-- **The equality case for an arbitrary horizontal plane**: `K_M = K_B` exactly when the
`A`-value vanishes. O'Neill's parenthetical "(more precisely, nondecreasing)", now for every
horizontal plane.
-/
theorem sectionalCurvatureAt_eq_iff_of_mem_horizontalSpace
    (hsymmM : IsSymm (tangentMetric I M)) (hposM : IsPosDef (tangentMetric I M))
    (hsymmB : IsSymm (tangentMetric J B)) (hposB : IsPosDef (tangentMetric J B))
    (hf : ContMDiff I J ((3 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((2 : ℕ∞)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((2 : ℕ∞)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    {u v : TangentSpace I p} {D F : Π z : M, TangentSpace I z}
    (hu : u ∈ horizontalSpace I J f p) (hDu : D p = u)
    (hFhor : IsHorizontalField I J f F) (hFd : MDiffAt (T% F) p) (hFv : F p = v)
    (hli : LinearIndependent ℝ ![u, v]) :
    sectionalCurvatureAt hsymmM hposM hgM p u v
        = sectionalCurvatureAt hsymmB hposB hgB (f p) (mfderiv I J f p u) (mfderiv I J f p v)
      ↔ oneillA I J f D F p = 0 := by
  rw [sectionalCurvatureAt_of_mem_horizontalSpace hsymmM hposM hsymmB hposB hf hgM hgB hsub
    hriem hu hDu hFhor hFd hFv, sub_eq_self, div_eq_zero_iff]
  have hden : 0 < gramDet (tangentMetric I M) p u v := gramDet_pos hsymmM hposM hli
  refine ⟨fun h ↦ ?_, fun h ↦ Or.inl ?_⟩
  · rcases h with h | h
    · exact (hposM.self_eq_zero_iff p _).mp (by linarith)
    · exact absurd h hden.ne'
  · rw [h]; simp

end Base

end RiemannianGeometry
