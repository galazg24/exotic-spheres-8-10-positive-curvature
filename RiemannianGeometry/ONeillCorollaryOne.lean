/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import RiemannianGeometry.ONeillBaseCurvature
import RiemannianGeometry.ONeillHorizontalCurvatureScalar
import RiemannianGeometry.RiemannSymmetries

/-!
# O'Neill's `{4}` over the base, and Corollary 1(3)

The last step of the horizontal-curvature chain. Three things happen, in this order, and each is
a separate theorem so that the arithmetic is auditable at every stage.

## 1. `{4}` itself

`RiemannianGeometry.ONeillHorizontalCurvatureScalar` proves the scalar dual Gauss equation with
`oneillHorizontalCurvature` — the *total-space* object `R^H` — on the right, and
`RiemannianGeometry.ONeillBaseCurvature` identifies `⟪R^H(X,Y)Z, Uᴴ⟫` with the curvature of `B`. Composing
them gives O'Neill's braced `{4}` with the base curvature where the source puts it:

    ⟪R(Xᴴ,Yᴴ)Zᴴ, Uᴴ⟫ = ⟪R*(X,Y)Z, U⟫(f p)
                        − ⟪A_{Xᴴ}Uᴴ, A_{Yᴴ}Zᴴ⟫ + ⟪A_{Yᴴ}Uᴴ, A_{Xᴴ}Zᴴ⟫
                        + 2 ⟪A_{Zᴴ}Uᴴ, A_{Xᴴ}Yᴴ⟫.

## 2. The factor `3`

`tangentMetric_curvature_horizontalLiftField_self` puts `Z := X`, `U := Y` in `{4}`. The three
`A`-terms become

    − ⟪A_{Xᴴ}Yᴴ, A_{Yᴴ}Xᴴ⟫ + ⟪A_{Yᴴ}Yᴴ, A_{Xᴴ}Xᴴ⟫ + 2 ⟪A_{Xᴴ}Yᴴ, A_{Xᴴ}Yᴴ⟫

and then `A_{Yᴴ}Xᴴ = −A_{Xᴴ}Yᴴ` (alternation) turns the first into `+‖A_{Xᴴ}Yᴴ‖²` while
`A_{Xᴴ}Xᴴ = 0` kills the second, leaving `1 + 0 + 2 = 3`. **The constant is produced by `ring` from
those three summands and is not inserted**: no coefficient anywhere in this file was chosen to make
a proof close.

## 3. Corollary 1(3)

    Rm_M(uᴴ,vᴴ,vᴴ,uᴴ) = Rm_B(u,v,v,u) − 3 ‖A_{Xᴴ}Yᴴ‖²                     (unnormalised)

with **no division**, and then, dividing by the Gram determinant that the submersion preserves,

    K_M(Xᴴ p, Yᴴ p) = K_B(X (f p), Y (f p)) − 3 ‖A_{Xᴴ}Yᴴ‖² / ‖Xᴴ p ∧ Yᴴ p‖².

**No nonvanishing or linear-independence hypothesis is needed for the quotient form**, because
`sub_div` holds unconditionally in `ℝ`: on a degenerate pair every term is Lean's junk `0` and the
identity reads `0 = 0 − 0`. Positive definiteness is needed only to *form* `sectionalCurvatureAt`,
and it is a theorem here (`isPosDef_tangentMetric`), not a hypothesis.

## Main results

* `mdiffAt_horizontalLiftField_of_forall` — a basic field is differentiable everywhere.
* `oneillA_horizontalLiftField_self_section_eq_zero`,
  `oneillA_horizontalLiftField_swap_neg_section` — `A_{Xᴴ}Xᴴ = 0` and
  `A_{Yᴴ}Xᴴ = −A_{Xᴴ}Yᴴ` as identities of **sections**, which is what discharges two of the
  differentiability hypotheses of `{4}` when `Z := X` and `U := Y`.
* `tangentMetric_oneill_dualGauss_rhs_neg` — the convention translation of O'Neill's printed
  right-hand side, as algebra.
* `tangentMetric_curvature_horizontalLiftField_base` — **`{4}`**.
* `tangentMetric_curvature_horizontalLiftField_self` — **the sectional specialisation, with the
  factor `3`**.
* `isPosDef_tangentMetric` — positive definiteness of the tangent metric.
* `tangentMetric_mfderiv_of_mem_horizontalSpace`, `gramDet_mfderiv_of_mem_horizontalSpace`,
  `gramDet_horizontalLiftField` — the submersion preserves the metric, and hence the Gram
  determinant, of a horizontal pair.
* `gramDet_eq_one` — the Gram determinant of an orthonormal pair, computed rather than assumed.
* `riemannTensorAt_horizontalLiftField` — **Corollary 1(3), unnormalised**.
* `sectionalCurvatureAt_horizontalLiftField` — **Corollary 1(3)**.
* `sectionalCurvatureAt_horizontalLiftField_of_orthonormal` — the orthonormal form.

## Regularity

**The metrics stay at `C²`.** §1 and §2 are stated at `C^n`, `n ≥ 2`, with `f ∈ C^(n+1)`, inherited
verbatim from the two theorems they compose. §3 pins `n := 2`, because `riemannCurvatureAt` and
therefore `riemannTensorAt` and `sectionalCurvatureAt` hard-code the order `2` — the connection
costs one derivative and its curvature another — so the metrics are `C²` and `f` is `C³`. `C³` on
the submersion is expected and is not a defect; `C³` on either metric would be. `IsManifold I 3 M`
is used through `riemannTensorAt_swap_right`, but that is a condition on the **charts**, free from
the ambient `[IsManifold I ∞ M]`, and not a condition on the metric.

## Spelling notes

`H` is the model topological space of `I`, so O'Neill's fourth horizontal field is `U`, not `H`.
Everything metric-valued is written with `tangentMetric`, never `inner ℝ`; the one place the
`inner ℝ` layer is unavoidable is `IsRiemannianSubmersionAtPoint`, which is stated with it, and
`inner_eq_tangentMetric` is the bridge.
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

/-! ## Basic fields, and the two `A`-identities as identities of sections -/

omit [FiniteDimensional ℝ E'] in
/-- **A basic field is differentiable at every point** as soon as its base field is `C^n`
everywhere. `contMDiffAt_horizontalLiftField` on `Set.univ`, with the point quantified; it is
stated separately only because the two section-level identities below and `{4}`'s
specialisation all need it at a *varying* point, where the `p` of the surrounding variable block
is the wrong one. -/
theorem mdiffAt_horizontalLiftField_of_forall {n : ℕ∞} (hn : minSmoothness ℝ 2 ≤ n)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hX : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% X) q) (z : M) :
    MDiffAt (T% (horizontalLiftField I J f X)) z :=
  (contMDiffAt_horizontalLiftField isOpen_univ (Set.mem_univ z) hf.contMDiffOn (hgM z)
    (hgB (f z)) (hX (f z))).mdifferentiableAt (coe_ne_zero_of_minSmoothness_two_le hn)

/-- **`A_{Xᴴ}Xᴴ` is the zero section**, not merely zero at `p`.

`oneillA_self_eq_zero` holds at every point at which `Xᴴ` is differentiable, and a basic field over
a `C^n` base field is differentiable at every point, so `funext` upgrades the pointwise statement to
an identity of sections. That upgrade is what makes
`MDiffAt (T% (oneillA I J f Xᴴ Xᴴ)) p` free, and it is one of the two differentiability hypotheses
of `{4}` that disappear in the sectional specialisation.
-/
theorem oneillA_horizontalLiftField_self_section_eq_zero {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    (hX : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% X) q) :
    oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f X) = 0 := by
  funext z
  simpa only [Pi.zero_apply] using
    oneillA_self_eq_zero (p := z) hn hn' hf hgM hgB hsub hriem
      isHorizontalField_horizontalLiftField
      (mdiffAt_horizontalLiftField_of_forall hn hf hgM hgB hX z)

/-- **Alternation of `A` on basic fields, as an identity of sections**:
`A_{Yᴴ}Xᴴ = −A_{Xᴴ}Yᴴ`.

`oneillA_swap_neg` at a varying point, as above. This is the second differentiability hypothesis of
`{4}` that the sectional specialisation discharges: `MDiffAt (T% (oneillA I J f Yᴴ Xᴴ)) p` follows
from `MDiffAt (T% (oneillA I J f Xᴴ Yᴴ)) p` by `mdifferentiableAt_neg_section`.
-/
theorem oneillA_horizontalLiftField_swap_neg_section {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    (hX : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% X) q)
    (hY : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q) :
    oneillA I J f (horizontalLiftField I J f Y) (horizontalLiftField I J f X)
      = -oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Y) := by
  funext z
  simpa only [Pi.neg_apply] using
    oneillA_swap_neg (p := z) hn hn' hf hgM hgB hsub hriem
      (X := horizontalLiftField I J f Y) (W := horizontalLiftField I J f X)
      isHorizontalField_horizontalLiftField isHorizontalField_horizontalLiftField
      (mdiffAt_horizontalLiftField_of_forall hn hf hgM hgB hY z)
      (mdiffAt_horizontalLiftField_of_forall hn hf hgM hgB hX z)

/-! ## The convention translation, as algebra -/

omit [FiniteDimensional ℝ E] in
/-- **O'Neill's printed right-hand side, multiplied by `−1`, is this project's.**

    ⟨R_{XY}Z, H⟩ = ⟨R*_{XY}Z, H⟩ − 2⟨A_XY, A_ZH⟩ + ⟨A_YZ, A_XH⟩ + ⟨A_ZX, A_YH⟩

and his `R` is **minus** `RiemannianGeometry.riemannCurvatureAt` (§7a). Multiplying through by `−1` and
substituting the vector identity `A_ZX = −A_XZ` — supplied here as the argument `-aXZ` in the
`A_ZX` slot rather than assumed — this lemma says that the resulting right-hand side is exactly the
one `tangentMetric_curvature_horizontalLiftField_base` carries. Only two facts are used:
linearity of the metric in its first slot and symmetry (`isSymm_tangentMetric`).
-/
theorem tangentMetric_oneill_dualGauss_rhs_neg
    (aXY aXZ aYZ aXU aYU aZU : TangentSpace I p) (rstar : ℝ) :
    -(rstar - 2 * tangentMetric I M p aXY aZU + tangentMetric I M p aYZ aXU
        + tangentMetric I M p (-aXZ) aYU)
      = -rstar - tangentMetric I M p aXU aYZ + tangentMetric I M p aYU aXZ
        + 2 * tangentMetric I M p aZU aXY := by
  have e1 := isSymm_tangentMetric (I := I) (M := M) p aXU aYZ
  have e2 := isSymm_tangentMetric (I := I) (M := M) p aYU aXZ
  have e3 := isSymm_tangentMetric (I := I) (M := M) p aZU aXY
  simp only [map_neg, neg_apply]
  linarith [e1, e2, e3]

/-! ## `{4}`: the scalar dual Gauss equation over the base -/

/-- **O'Neill's equation `{4}`, the dual Gauss equation, with the curvature of the base.**
For basic fields `Xᴴ`, `Yᴴ`, `Zᴴ`, `Uᴴ`,

    ⟪R(Xᴴ,Yᴴ)Zᴴ, Uᴴ⟫ = ⟪R*(X,Y)Z, U⟫(f p)
                        − ⟪A_{Xᴴ}Uᴴ, A_{Yᴴ}Zᴴ⟫ + ⟪A_{Yᴴ}Uᴴ, A_{Xᴴ}Zᴴ⟫
                        + 2 ⟪A_{Zᴴ}Uᴴ, A_{Xᴴ}Yᴴ⟫,

with `R*` the curvature of `leviCivita (tangentMetric J B)` on `B` and `⟪·,·⟫` on the right the
metric of `B` at `f p`.

`tangentMetric_curvature_horizontalLiftField` has the *total-space* object
`oneillHorizontalCurvature I J f X Y Z p` in the first term;
`tangentMetric_oneillHorizontalCurvature_horizontalLiftField` replaces it by the base curvature.
That is the whole content of this theorem, and it is a single `rw`: no hypothesis is added, nothing
is normalised, and the `A`-terms are untouched. The two composed theorems carry disjoint
obligations, which is why they were kept apart — the first is the algebra of the vector relation
paired against `Uᴴ`, the second is O'Neill's Lemma 1(3) on the base.

-/
theorem tangentMetric_curvature_horizontalLiftField_base {n : ℕ∞}
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
  rw [tangentMetric_curvature_horizontalLiftField hn hn' hf hgM hgB hsub hriem hX hY hZ hU
      hAXY hHYZ hAYZ hHXZ hAXZ,
    tangentMetric_oneillHorizontalCurvature_horizontalLiftField hn hn' hf hgM hgB hsub hriem
      hX hY hZ (Filter.Eventually.of_forall hU)]

/-! ## The sectional specialisation, and the factor `3` -/

/-- **`{4}` with `Z := X` and `U := Y`, which is where the `3` comes from.**

    ⟪R(Xᴴ,Yᴴ)Xᴴ, Yᴴ⟫ = ⟪R*(X,Y)X, Y⟫(f p) + 3 ⟪A_{Xᴴ}Yᴴ, A_{Xᴴ}Yᴴ⟫

Substituting into `tangentMetric_curvature_horizontalLiftField_base` leaves the three summands

    − ⟪A_{Xᴴ}Yᴴ, A_{Yᴴ}Xᴴ⟫ + ⟪A_{Yᴴ}Yᴴ, A_{Xᴴ}Xᴴ⟫ + 2 ⟪A_{Xᴴ}Yᴴ, A_{Xᴴ}Yᴴ⟫

and then, in order:

* `oneillA_horizontalLiftField_swap_neg` rewrites `A_{Yᴴ}Xᴴ p` as `−A_{Xᴴ}Yᴴ p`, so the first
  summand becomes `+⟪A_{Xᴴ}Yᴴ, A_{Xᴴ}Yᴴ⟫` — **one**;
* `oneillA_horizontalLiftField_self_eq_zero` rewrites `A_{Xᴴ}Xᴴ p` as `0`, so the middle summand
  vanishes by `map_zero` — **nothing**;
* the last summand is already `2 ⟪A_{Xᴴ}Yᴴ, A_{Xᴴ}Yᴴ⟫` — **two**.

Two of `{4}`'s five differentiability hypotheses disappear under the substitution:
`MDiffAt (T% (oneillA I J f Xᴴ Xᴴ)) p` because that section is `0`, and
`MDiffAt (T% (oneillA I J f Yᴴ Xᴴ)) p` because that section is `−(oneillA I J f Xᴴ Yᴴ)`. The three
that remain — `hAXY`, `hHYX`, `hHXX` — are not removable at metrics `C²`; see
`RiemannianGeometry.ONeillHorizontalCurvatureScalar` §1.
-/
theorem tangentMetric_curvature_horizontalLiftField_self {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    (hX : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% X) q)
    (hY : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q)
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
  have hAXX : MDiffAt (T% (oneillA I J f (horizontalLiftField I J f X)
      (horizontalLiftField I J f X))) p := by
    rw [oneillA_horizontalLiftField_self_section_eq_zero hn hn' hf hgM hgB hsub hriem hX]
    exact mdifferentiableAt_zeroSection ..
  have hAYX : MDiffAt (T% (oneillA I J f (horizontalLiftField I J f Y)
      (horizontalLiftField I J f X))) p := by
    rw [oneillA_horizontalLiftField_swap_neg_section hn hn' hf hgM hgB hsub hriem hX hY]
    exact mdifferentiableAt_neg_section hAXY
  rw [tangentMetric_curvature_horizontalLiftField_base (Z := X) (U := Y) hn hn' hf hgM hgB
      hsub hriem hX hY hX hY hAXY hHYX hAYX hHXX hAXX,
    oneillA_horizontalLiftField_swap_neg (Y₁ := Y) (Y₂ := X) hn hn' hf hgM hgB hsub hriem hY hX,
    oneillA_horizontalLiftField_self_eq_zero (Y := X) hn hn' hf hgM hgB hsub hriem hX]
  simp only [map_neg, map_zero]
  ring

/-! ## What the sectional-curvature layer needs from the submersion -/

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- **The tangent metric is positive definite.**

The `pos` field of `Bundle.RiemannianMetric`, repackaged as the project's `IsPosDef`. This is the
one hypothesis of `sectionalCurvatureAt` that `RiemannianGeometry.ONeillTensors` did not already supply
alongside `isSymm_tangentMetric` and `isNondegenerate_tangentMetric`, because nothing before the
sectional layer needed it: `riemannCurvatureAt` and `riemannTensorAt` are pseudo-Riemannian. -/
theorem isPosDef_tangentMetric : IsPosDef (tangentMetric I M) :=
  fun y v hv ↦ (Bundle.RiemannianBundle.g (E := (TangentSpace I : M → Type _))).pos y v hv

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **`dπ` is a metric isometry on horizontal vectors**, in `tangentMetric` language:
`⟪dπ u, dπ v⟫_B = ⟪u, v⟫_M`.

`IsRiemannianSubmersionAtPoint` is stated with `inner ℝ`, which is a different atom to every tactic
from `tangentMetric I M p`; `inner_eq_tangentMetric` is the bridge and it is `rfl`. Only the
isometry condition is used — **not** `IsSubmersionAtPoint`. -/
theorem tangentMetric_mfderiv_of_mem_horizontalSpace
    (hriem : IsRiemannianSubmersionAtPoint I J f p) {u v : TangentSpace I p}
    (hu : u ∈ horizontalSpace I J f p) (hv : v ∈ horizontalSpace I J f p) :
    tangentMetric J B (f p) (mfderiv I J f p u) (mfderiv I J f p v)
      = tangentMetric I M p u v := by
  rw [← inner_eq_tangentMetric, ← inner_eq_tangentMetric]
  exact hriem u hu v hv

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **The submersion preserves the Gram determinant of a horizontal pair.**

    ‖dπ u ∧ dπ v‖² = ‖u ∧ v‖²    for `u`, `v` horizontal at `p`

Immediate from `tangentMetric_mfderiv_of_mem_horizontalSpace` applied to the three pairings
`(u,u)`, `(v,v)`, `(u,v)` that `gramDet` is built from. This is the denominator half of
Corollary 1(3): the numerators are compared by `riemannTensorAt_horizontalLiftField` and the
denominators are **equal**, so no reparametrisation and no positivity is involved. -/
theorem gramDet_mfderiv_of_mem_horizontalSpace
    (hriem : IsRiemannianSubmersionAtPoint I J f p) {u v : TangentSpace I p}
    (hu : u ∈ horizontalSpace I J f p) (hv : v ∈ horizontalSpace I J f p) :
    gramDet (tangentMetric J B) (f p) (mfderiv I J f p u) (mfderiv I J f p v)
      = gramDet (tangentMetric I M) p u v := by
  simp only [gramDet, tangentMetric_mfderiv_of_mem_horizontalSpace hriem hu hu,
    tangentMetric_mfderiv_of_mem_horizontalSpace hriem hv hv,
    tangentMetric_mfderiv_of_mem_horizontalSpace hriem hu hv]

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **The Gram determinant of a pair of basic values equals that of the base pair.**

`gramDet_mfderiv_of_mem_horizontalSpace` with `u := Xᴴ p`, `v := Yᴴ p`, whose images under `dπ_p`
are `X (f p)` and `Y (f p)` by `mfderiv_horizontalLiftField`. This is the form Corollary 1(3)
consumes, and the only place `IsSubmersionAtPoint` enters the denominator comparison. -/
theorem gramDet_horizontalLiftField (hsub : IsSubmersionAtPoint I J f p)
    (hriem : IsRiemannianSubmersionAtPoint I J f p) :
    gramDet (tangentMetric J B) (f p) (X (f p)) (Y (f p))
      = gramDet (tangentMetric I M) p (horizontalLiftField I J f X p)
          (horizontalLiftField I J f Y p) := by
  rw [← mfderiv_horizontalLiftField (Y := X) hsub hriem,
    ← mfderiv_horizontalLiftField (Y := Y) hsub hriem]
  exact gramDet_mfderiv_of_mem_horizontalSpace hriem (horizontalLiftField_mem p)
    (horizontalLiftField_mem p)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- **The Gram determinant of an orthonormal pair is `1`** — computed, not assumed.
`gramDet g x u v = g x u u * g x v v − (g x u v)²` becomes `1 * 1 − 0² = 1`. -/
theorem gramDet_eq_one {u v : TangentSpace I p} (huu : tangentMetric I M p u u = 1)
    (hvv : tangentMetric I M p v v = 1) (huv : tangentMetric I M p u v = 0) :
    gramDet (tangentMetric I M) p u v = 1 := by
  rw [gramDet, huu, hvv, huv]
  norm_num

/-! ## Corollary 1(3) -/

/-- **Corollary 1(3), unnormalised.** No division, so nothing depends on a nonvanishing
denominator:

    Rm_M(Xᴴ p, Yᴴ p, Yᴴ p, Xᴴ p)
      = Rm_B(X (f p), Y (f p), Y (f p), X (f p)) − 3 ⟪A_{Xᴴ}Yᴴ, A_{Xᴴ}Yᴴ⟫.

**The sign step, which is where an error would be invisible.**
`RiemannianGeometry.sectionalCurvatureAt` has numerator `Rm(u,v,v,u) = g (R(u,v) v) u`, whereas
`tangentMetric_curvature_horizontalLiftField_self` computes `g (R(u,v) u) v`, i.e. `Rm(u,v,u,v)`.
Last-pair antisymmetry `riemannTensorAt_swap_right` relates them, and it is applied **on both
manifolds**:

    Rm_M(u,v,v,u) = −Rm_M(u,v,u,v) = −[ Rm_B(u',v',u',v') + 3‖A‖² ]
                  = −[ −Rm_B(u',v',v',u') + 3‖A‖² ] = Rm_B(u',v',v',u') − 3‖A‖².

`riemannTensorAt_apply_fields` is the bridge from `curvature (leviCivita …)` to
`riemannTensorAt`, on both manifolds; the eventual `C²` hypotheses it wants on the four fields are
supplied by `contMDiffAt_horizontalLiftField` on `M` and by `hX`, `hY` themselves on `B`. Because
`riemannTensorAt` hard-codes the order `2`, this is where the campaign's `n` is pinned to `2` and
`f` to `C³`.
-/
theorem riemannTensorAt_horizontalLiftField
    (hsymmM : IsSymm (tangentMetric I M)) (hndM : IsNondegenerate (tangentMetric I M))
    (hsymmB : IsSymm (tangentMetric J B)) (hndB : IsNondegenerate (tangentMetric J B))
    (hf : ContMDiff I J ((3 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((2 : ℕ∞)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((2 : ℕ∞)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    (hX : ∀ q, ContMDiffAt J J.tangent (((2 : ℕ∞) : ℕ∞ω)) (T% X) q)
    (hY : ∀ q, ContMDiffAt J J.tangent (((2 : ℕ∞) : ℕ∞ω)) (T% Y) q)
    (hAXY : MDiffAt (T% (oneillA I J f (horizontalLiftField I J f X)
      (horizontalLiftField I J f Y))) p)
    (hHYX : MDiffAt (T% (horizontalLeviCivita I J f (horizontalLiftField I J f Y)
      (horizontalLiftField I J f X))) p)
    (hHXX : MDiffAt (T% (horizontalLeviCivita I J f (horizontalLiftField I J f X)
      (horizontalLiftField I J f X))) p) :
    riemannTensorAt hsymmM hndM hgM p (horizontalLiftField I J f X p)
        (horizontalLiftField I J f Y p) (horizontalLiftField I J f Y p)
        (horizontalLiftField I J f X p)
      = riemannTensorAt hsymmB hndB hgB (f p) (X (f p)) (Y (f p)) (Y (f p)) (X (f p))
        - 3 * tangentMetric I M p
            (oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Y) p)
            (oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Y) p) := by
  have hf3 : ContMDiff I J (((2 : ℕ∞) + 1 : ℕ∞)) f := by
    rwa [show ((2 : ℕ∞) + 1 : ℕ∞) = (3 : ℕ∞) by norm_num]
  have hXHe : ∀ z, ContMDiffAt I I.tangent (((2 : ℕ∞) : ℕ∞ω))
      (T% (horizontalLiftField I J f X)) z := fun z ↦
    contMDiffAt_horizontalLiftField isOpen_univ (Set.mem_univ z) hf3.contMDiffOn (hgM z)
      (hgB (f z)) (hX (f z))
  have hYHe : ∀ z, ContMDiffAt I I.tangent (((2 : ℕ∞) : ℕ∞ω))
      (T% (horizontalLiftField I J f Y)) z := fun z ↦
    contMDiffAt_horizontalLiftField isOpen_univ (Set.mem_univ z) hf3.contMDiffOn (hgM z)
      (hgB (f z)) (hY (f z))
  have hM := riemannTensorAt_apply_fields hsymmM hndM hgM
    (X := horizontalLiftField I J f X) (Y := horizontalLiftField I J f Y)
    (Z := horizontalLiftField I J f X) (W := horizontalLiftField I J f Y) (x := p)
    (Filter.Eventually.of_forall hXHe) (Filter.Eventually.of_forall hYHe) (hXHe p)
  have hB := riemannTensorAt_apply_fields hsymmB hndB hgB
    (X := X) (Y := Y) (Z := X) (W := Y) (x := f p)
    (Filter.Eventually.of_forall hX) (Filter.Eventually.of_forall hY) (hX (f p))
  have hD2 := tangentMetric_curvature_horizontalLiftField_self (n := 2) (by simp) (by simp)
    hf3 hgM hgB hsub hriem hX hY hAXY hHYX hHXX
  have hswM := riemannTensorAt_swap_right hsymmM hndM hgM (horizontalLiftField I J f X p)
    (horizontalLiftField I J f Y p) (horizontalLiftField I J f Y p)
    (horizontalLiftField I J f X p)
  have hswB := riemannTensorAt_swap_right hsymmB hndB hgB (X (f p)) (Y (f p)) (Y (f p)) (X (f p))
  linarith [hM, hB, hD2, hswM, hswB]

/-- **O'Neill's Corollary 1(3).**

    K_M(Xᴴ p, Yᴴ p) = K_B(X (f p), Y (f p)) − 3 ⟪A_{Xᴴ}Yᴴ, A_{Xᴴ}Yᴴ⟫ / ‖Xᴴ p ∧ Yᴴ p‖²

`X (f p)` **is** `dπ_p (Xᴴ p)`, by `mfderiv_horizontalLiftField`, so the plane on the right is
O'Neill's `P_{x_* y_*}`.

Three inputs, and none of them is a hypothesis about denominators:

* the numerators, by `riemannTensorAt_horizontalLiftField`;
* the denominators, which are **equal**, by `gramDet_horizontalLiftField`;
* `sub_div`, which holds unconditionally in `ℝ`.

So **no linear independence and no nonvanishing hypothesis appears.** On a degenerate pair every
term is Lean's junk `0` and the identity reads `0 = 0 − 0`, which is true; on an independent pair
the denominator is positive by `gramDet_pos` and the statement is the honest quotient. The
positive-definiteness arguments `hposM`, `hposB` are there only because `sectionalCurvatureAt`
takes them, and both are discharged by `isPosDef_tangentMetric` at the call site. Note that they
must be *the same proof terms* used to form the two `sectionalCurvatureAt`s, since
`riemannTensorAt` carries its nondegeneracy proof as an argument.
-/
theorem sectionalCurvatureAt_horizontalLiftField
    (hsymmM : IsSymm (tangentMetric I M)) (hposM : IsPosDef (tangentMetric I M))
    (hsymmB : IsSymm (tangentMetric J B)) (hposB : IsPosDef (tangentMetric J B))
    (hf : ContMDiff I J ((3 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((2 : ℕ∞)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((2 : ℕ∞)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    (hX : ∀ q, ContMDiffAt J J.tangent (((2 : ℕ∞) : ℕ∞ω)) (T% X) q)
    (hY : ∀ q, ContMDiffAt J J.tangent (((2 : ℕ∞) : ℕ∞ω)) (T% Y) q)
    (hAXY : MDiffAt (T% (oneillA I J f (horizontalLiftField I J f X)
      (horizontalLiftField I J f Y))) p)
    (hHYX : MDiffAt (T% (horizontalLeviCivita I J f (horizontalLiftField I J f Y)
      (horizontalLiftField I J f X))) p)
    (hHXX : MDiffAt (T% (horizontalLeviCivita I J f (horizontalLiftField I J f X)
      (horizontalLiftField I J f X))) p) :
    sectionalCurvatureAt hsymmM hposM hgM p (horizontalLiftField I J f X p)
        (horizontalLiftField I J f Y p)
      = sectionalCurvatureAt hsymmB hposB hgB (f p) (X (f p)) (Y (f p))
        - 3 * tangentMetric I M p
              (oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Y) p)
              (oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Y) p)
            / gramDet (tangentMetric I M) p (horizontalLiftField I J f X p)
              (horizontalLiftField I J f Y p) := by
  rw [sectionalCurvatureAt_def, sectionalCurvatureAt_def,
    riemannTensorAt_horizontalLiftField hsymmM (IsPosDef.isNondegenerate hposM) hsymmB
      (IsPosDef.isNondegenerate hposB) hf hgM hgB hsub hriem hX hY hAXY hHYX hHXX,
    gramDet_horizontalLiftField (hsub p) (hriem p), sub_div]

/-- **Corollary 1(3) on an orthonormal horizontal pair** — the form the downstream literature
uses:

    K_M(u, v) = K_B(dπ u, dπ v) − 3 ⟪A_{Xᴴ}Yᴴ, A_{Xᴴ}Yᴴ⟫,    u = Xᴴ p, v = Yᴴ p.

The denominator is `1` by `gramDet_eq_one`, which **computes** `1 * 1 − 0²` rather than assuming
it, and `X (f p) = dπ_p u`, `Y (f p) = dπ_p v` by `mfderiv_horizontalLiftField`. The base pair is
then orthonormal as well — that is `tangentMetric_mfderiv_of_mem_horizontalSpace`, so it is
available, though this proof does not need it: the base denominator is handled inside
`sectionalCurvatureAt_horizontalLiftField`, which equates the two Gram determinants rather than
evaluating either.
-/
theorem sectionalCurvatureAt_horizontalLiftField_of_orthonormal
    (hsymmM : IsSymm (tangentMetric I M)) (hposM : IsPosDef (tangentMetric I M))
    (hsymmB : IsSymm (tangentMetric J B)) (hposB : IsPosDef (tangentMetric J B))
    (hf : ContMDiff I J ((3 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((2 : ℕ∞)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((2 : ℕ∞)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    (hX : ∀ q, ContMDiffAt J J.tangent (((2 : ℕ∞) : ℕ∞ω)) (T% X) q)
    (hY : ∀ q, ContMDiffAt J J.tangent (((2 : ℕ∞) : ℕ∞ω)) (T% Y) q)
    (hAXY : MDiffAt (T% (oneillA I J f (horizontalLiftField I J f X)
      (horizontalLiftField I J f Y))) p)
    (hHYX : MDiffAt (T% (horizontalLeviCivita I J f (horizontalLiftField I J f Y)
      (horizontalLiftField I J f X))) p)
    (hHXX : MDiffAt (T% (horizontalLeviCivita I J f (horizontalLiftField I J f X)
      (horizontalLiftField I J f X))) p)
    (huu : tangentMetric I M p (horizontalLiftField I J f X p)
      (horizontalLiftField I J f X p) = 1)
    (hvv : tangentMetric I M p (horizontalLiftField I J f Y p)
      (horizontalLiftField I J f Y p) = 1)
    (huv : tangentMetric I M p (horizontalLiftField I J f X p)
      (horizontalLiftField I J f Y p) = 0) :
    sectionalCurvatureAt hsymmM hposM hgM p (horizontalLiftField I J f X p)
        (horizontalLiftField I J f Y p)
      = sectionalCurvatureAt hsymmB hposB hgB (f p) (X (f p)) (Y (f p))
        - 3 * tangentMetric I M p
            (oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Y) p)
            (oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Y) p) := by
  rw [sectionalCurvatureAt_horizontalLiftField hsymmM hposM hsymmB hposB hf hgM hgB hsub hriem
      hX hY hAXY hHYX hHXX, gramDet_eq_one huu hvv huv, div_one]

end RiemannianGeometry
