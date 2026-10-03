/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import RiemannianGeometry.ONeillGerm

/-!
# Strict positivity of base curvature under a Riemannian submersion

## Why the strict half is a separate statement and not a cosmetic variant

That is `pos_sectionalCurvatureAt_of_nonneg_horizontalLiftField` and its arbitrary-vector form
`pos_sectionalCurvatureAt_of_nonneg_of_mem_horizontalSpace`: the hypothesis is
`0 ≤ K_M` **and** `0 < K_M ∨ A_u v ≠ 0`, the disjunction visible in the statement.

## Non-degeneracy: what the strict conclusion actually requires

Two remarks on the sharpness of that, recorded because both are easy to get wrong.

* **`hli` is mathematically redundant in the presence of `A_u v ≠ 0`**, and is nevertheless kept.
  For horizontal `u`, `v` with `v = c • u` one has `A_u v = c • A_u u = 0`, so `A_u v ≠ 0`
  *implies* independence; the strict statements are true with `hli` deleted. Deleting it needs
  order-zero tensoriality of `A` in both slots — `ONeillTensors.oneillA_congr_direction` for the
  direction slot, `ONeillTensoriality.oneillA_eq_of_eq_at` and
  `ONeillTensoriality.oneillA_smul_field` for the field slot — together with the diagonal
  vanishing `A_X X = 0`, which comes from `ONeillTensoriality.oneillA_swap_neg`, and a case split
  on which vector of a dependent pair is a multiple of which. That is a real proof and not a
  rearrangement of these ones. `hli`
  is kept so that the strict statements have exactly the antecedent of the nonstrict ones and
  compose with them without a side condition; that it is removable is recorded here rather than
  left for a reader to wonder about.
* **`0 < K_M` also implies `gramDet ≠ 0`** — a vanishing `gramDet` forces `K_M = 0` — so `hli` is
  redundant in that branch too, for the same kind of reason and by an easier argument. It is not
  redundant in the conclusion: `K_B` is *also* a quotient, and `0 < K_B` needs its denominator
  nonzero, which is `hli` again on the base side via `gramDet_horizontalLiftField`.

## The inheritance statement, and its honest antecedent

The strict analogue of `nonneg_sectionalCurvatureAt_of_nonneg_horizontalLiftField` is
`pos_sectionalCurvatureAt_of_pos_horizontalLiftField`, and its antecedent is positivity of `K_M`
at the **single plane** spanned by `u` and `v` — not at all horizontal planes at `p`, not at all
points, and not "`M` has positive sectional curvature". `lt_of_lt_of_le` consumes exactly one
instance. The disjunctive statement has the same shape: `0 ≤ K_M` at that one plane, and the
disjunct at that one plane.

## Main results

* `sectionalCurvatureAt_horizontalLiftField_lt_of_oneillA_ne_zero` — **`K_M < K_B` when
  `A_{Xᴴ}Yᴴ p ≠ 0`**, and its orthonormal form, which needs no independence hypothesis.
* `pos_sectionalCurvatureAt_of_pos_horizontalLiftField` — positivity inherited on one plane.
* `pos_sectionalCurvatureAt_of_nonneg_horizontalLiftField` — **`0 < K_B` from `0 ≤ K_M` together
  with `0 < K_M ∨ A_{Xᴴ}Yᴴ p ≠ 0`**, and their orthonormal forms.

## Regularity

Every hypothesis stack here is **verbatim** the stack of the statement it is derived from —
metrics at `C²`, `f` at `C³`, the three `Mathlib` order hypotheses unchanged. Nothing in this
module differentiates anything, and no declaration raises the regularity of either metric or of
`f`.
-/

noncomputable section

open Bundle VectorField
open scoped Manifold ContDiff Topology

namespace RiemannianGeometry

/-! ## The strict inequality and positivity, for planes spanned by values of basic fields -/

section Submersion

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {B : Type*} [TopologicalSpace B] [ChartedSpace H' B] [IsManifold J ∞ B]
  [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]
  [Bundle.RiemannianBundle (TangentSpace J : B → Type _)]
  {f : M → B} {p : M} {X Y : Π q : B, TangentSpace J q}
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

include hf hsub hriem hX hY hAXY hHYX hHXX

/-- **Strict increase off the integrable locus:** if `A_{Xᴴ}Yᴴ p ≠ 0` then

    K_M(Xᴴ p, Yᴴ p) < K_B(X (f p), Y (f p))

`lt_of_le_of_ne` against `sectionalCurvatureAt_horizontalLiftField_le` and
`sectionalCurvatureAt_horizontalLiftField_eq_iff`; the inequality is not reproved and the formula
is not reopened. `hli` is used twice, once inside each of those two theorems.

**What the hypothesis `hA` is doing, in O'Neill's vocabulary.** He wrote "curvature-increasing
(more precisely, nondecreasing)", withdrawing the strict word in the same breath. `hA` is exactly
the condition under which the withdrawn word is correct, and by
`oneillA_horizontalLiftField_eq_two_inv_smul_verticalProjection_mlieBracket` (Lemma 2) it says
that the horizontal distribution is non-integrable along the pair.
-/
theorem sectionalCurvatureAt_horizontalLiftField_lt_of_oneillA_ne_zero
    (hli : LinearIndependent ℝ ![horizontalLiftField I J f X p,
      horizontalLiftField I J f Y p])
    (hA : oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Y) p ≠ 0) :
    sectionalCurvatureAt hsymmM hposM hgM p (horizontalLiftField I J f X p)
        (horizontalLiftField I J f Y p)
      < sectionalCurvatureAt hsymmB hposB hgB (f p) (X (f p)) (Y (f p)) :=
  lt_of_le_of_ne
    (sectionalCurvatureAt_horizontalLiftField_le hsymmM hposM hsymmB hposB hf hgM hgB hsub hriem
      hX hY hAXY hHYX hHXX hli)
    fun h ↦ hA ((sectionalCurvatureAt_horizontalLiftField_eq_iff hsymmM hposM hsymmB hposB hf hgM
      hgB hsub hriem hX hY hAXY hHYX hHXX hli).mp h)

/-- **The strict inequality on an orthonormal horizontal pair**, with no independence hypothesis.

    K_M(u, v) < K_B(dπ u, dπ v),    u = Xᴴ p, v = Yᴴ p orthonormal, A_{Xᴴ}Yᴴ p ≠ 0

For the reason recorded in the `ONeillCurvatureNondecreasing` module docstring: the orthonormal
form of Corollary 1(3) has **no denominator** — `gramDet_eq_one` has already discharged it — so
this needs only that the numerator is *strictly* positive, which is `IsPosDef` applied to the
nonzero vector `A_{Xᴴ}Yᴴ p`. `gramDet_pos` is not used, and this proof does **not** go through
`sectionalCurvatureAt_horizontalLiftField_lt_of_oneillA_ne_zero`. Orthonormality does supply
independence (`linearIndependent_pair_of_orthonormal`), but that is again not what closes the
proof.
-/
theorem sectionalCurvatureAt_horizontalLiftField_lt_of_orthonormal_of_oneillA_ne_zero
    (huu : tangentMetric I M p (horizontalLiftField I J f X p)
      (horizontalLiftField I J f X p) = 1)
    (hvv : tangentMetric I M p (horizontalLiftField I J f Y p)
      (horizontalLiftField I J f Y p) = 1)
    (huv : tangentMetric I M p (horizontalLiftField I J f X p)
      (horizontalLiftField I J f Y p) = 0)
    (hA : oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Y) p ≠ 0) :
    sectionalCurvatureAt hsymmM hposM hgM p (horizontalLiftField I J f X p)
        (horizontalLiftField I J f Y p)
      < sectionalCurvatureAt hsymmB hposB hgB (f p) (X (f p)) (Y (f p)) := by
  rw [sectionalCurvatureAt_horizontalLiftField_of_orthonormal hsymmM hposM hsymmB hposB hf hgM
    hgB hsub hriem hX hY hAXY hHYX hHXX huu hvv huv]
  have := hposM p
    (oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Y) p) hA
  linarith

/-- **Positive sectional curvature is inherited by the base**, on one horizontal plane at a time.

    0 < K_M(Xᴴ p, Yᴴ p)  →  0 < K_B(X (f p), Y (f p))

The strict analogue of `nonneg_sectionalCurvatureAt_of_nonneg_horizontalLiftField`, by
`lt_of_lt_of_le` in place of `le_trans`, and with the **same** antecedent shape: positivity of
`K_M` at the *single* plane spanned by `Xᴴ p` and `Yᴴ p`. No global quantifier is needed and none
is taken.

**What this is and is not the theorem for.** This is the half of the strict story that the
nonstrict inequality already delivers, and it is worth stating exactly so that the other half is
not confused with it: `K_M ≤ K_B` does transfer positivity, *wherever `K_M` is positive*. What it
cannot do is produce `0 < K_B` on a plane where `K_M = 0`, which is the Gromoll–Meyer situation
and is `pos_sectionalCurvatureAt_of_nonneg_horizontalLiftField`.

The scope limits of `nonneg_sectionalCurvatureAt_of_nonneg_horizontalLiftField` apply verbatim:
the conclusion is positivity at the planes of `T_{f p}B` spanned by `X (f p)`, `Y (f p)` for
globally-`C²` fields `X`, `Y`, at points in the image of `f`. "`B` has positive sectional
curvature" additionally needs surjectivity of `f` and arbitrary base planes; for the latter, use
`pos_sectionalCurvatureAt_of_pos_of_mem_horizontalSpace` instead.
-/
theorem pos_sectionalCurvatureAt_of_pos_horizontalLiftField
    (hli : LinearIndependent ℝ ![horizontalLiftField I J f X p,
      horizontalLiftField I J f Y p])
    (hM : 0 < sectionalCurvatureAt hsymmM hposM hgM p (horizontalLiftField I J f X p)
      (horizontalLiftField I J f Y p)) :
    0 < sectionalCurvatureAt hsymmB hposB hgB (f p) (X (f p)) (Y (f p)) :=
  hM.trans_le (sectionalCurvatureAt_horizontalLiftField_le hsymmM hposM hsymmB hposB hf hgM hgB
    hsub hriem hX hY hAXY hHYX hHXX hli)

/-- **Strict positivity of base curvature from nonnegativity upstairs and a nonvanishing
`A`-tensor.**

    0 ≤ K_M(Xᴴ p, Yᴴ p)  →  (0 < K_M(Xᴴ p, Yᴴ p) ∨ A_{Xᴴ}Yᴴ p ≠ 0)
      →  0 < K_B(X (f p), Y (f p))

Both branches are one step. On `0 < K_M` it is
`pos_sectionalCurvatureAt_of_pos_horizontalLiftField` and `hM` is not used; on `A_{Xᴴ}Yᴴ p ≠ 0` it
is `hM` against `sectionalCurvatureAt_horizontalLiftField_lt_of_oneillA_ne_zero`. Nothing here
reproves the inequality, the formula, or the equality case.

**`hM` is not implied by the second disjunct**, which is why it is a separate hypothesis rather
than folded into the disjunction: `A_{Xᴴ}Yᴴ p ≠ 0` gives `K_M < K_B` and says nothing at all about
the sign of `K_M`. A submersion with negatively curved total space and nonvanishing `A` need not
have `0 < K_B`.

**Consumers, not sources.** `GM1974` and `PW2008` need positive curvature on the quotient and are
where a statement of this shape is used. **Nothing about either is formalised here**: this is the
implication only, and both of its hypotheses are owed by constructions that do not exist in this
library. -/
theorem pos_sectionalCurvatureAt_of_nonneg_horizontalLiftField
    (hli : LinearIndependent ℝ ![horizontalLiftField I J f X p,
      horizontalLiftField I J f Y p])
    (hM : 0 ≤ sectionalCurvatureAt hsymmM hposM hgM p (horizontalLiftField I J f X p)
      (horizontalLiftField I J f Y p))
    (hdeg : 0 < sectionalCurvatureAt hsymmM hposM hgM p (horizontalLiftField I J f X p)
        (horizontalLiftField I J f Y p) ∨
      oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Y) p ≠ 0) :
    0 < sectionalCurvatureAt hsymmB hposB hgB (f p) (X (f p)) (Y (f p)) := by
  rcases hdeg with h | h
  · exact pos_sectionalCurvatureAt_of_pos_horizontalLiftField hsymmM hposM hsymmB hposB hf hgM
      hgB hsub hriem hX hY hAXY hHYX hHXX hli h
  · exact hM.trans_lt (sectionalCurvatureAt_horizontalLiftField_lt_of_oneillA_ne_zero hsymmM
      hposM hsymmB hposB hf hgM hgB hsub hriem hX hY hAXY hHYX hHXX hli h)

/-- **Positivity inheritance on an orthonormal horizontal pair**, with no independence hypothesis.

    0 < K_M(u, v)  →  0 < K_B(dπ u, dπ v),    u = Xᴴ p, v = Yᴴ p orthonormal.

The orthonormal form of `pos_sectionalCurvatureAt_of_pos_horizontalLiftField`, routed through
`sectionalCurvatureAt_horizontalLiftField_le_of_orthonormal` and so never touching a Gram
determinant. This is the form in which a downstream computation applies the inheritance, since it
chooses an orthonormal horizontal frame.
-/
theorem pos_sectionalCurvatureAt_of_pos_horizontalLiftField_of_orthonormal
    (huu : tangentMetric I M p (horizontalLiftField I J f X p)
      (horizontalLiftField I J f X p) = 1)
    (hvv : tangentMetric I M p (horizontalLiftField I J f Y p)
      (horizontalLiftField I J f Y p) = 1)
    (huv : tangentMetric I M p (horizontalLiftField I J f X p)
      (horizontalLiftField I J f Y p) = 0)
    (hM : 0 < sectionalCurvatureAt hsymmM hposM hgM p (horizontalLiftField I J f X p)
      (horizontalLiftField I J f Y p)) :
    0 < sectionalCurvatureAt hsymmB hposB hgB (f p) (X (f p)) (Y (f p)) :=
  hM.trans_le (sectionalCurvatureAt_horizontalLiftField_le_of_orthonormal hsymmM hposM hsymmB
    hposB hf hgM hgB hsub hriem hX hY hAXY hHYX hHXX huu hvv huv)

/-- **Strict positivity from nonnegativity upstairs, on an orthonormal horizontal pair**, with no
independence hypothesis.

    0 ≤ K_M(u, v)  →  (0 < K_M(u, v) ∨ A_{Xᴴ}Yᴴ p ≠ 0)  →  0 < K_B(dπ u, dπ v)

`pos_sectionalCurvatureAt_of_nonneg_horizontalLiftField` with the three normalisation equations in
place of `hli`, both branches routed through the orthonormal statements, so no Gram determinant
occurs in either. The remark there about `hM` not being implied by the second disjunct applies
unchanged.
-/
theorem pos_sectionalCurvatureAt_of_nonneg_horizontalLiftField_of_orthonormal
    (huu : tangentMetric I M p (horizontalLiftField I J f X p)
      (horizontalLiftField I J f X p) = 1)
    (hvv : tangentMetric I M p (horizontalLiftField I J f Y p)
      (horizontalLiftField I J f Y p) = 1)
    (huv : tangentMetric I M p (horizontalLiftField I J f X p)
      (horizontalLiftField I J f Y p) = 0)
    (hM : 0 ≤ sectionalCurvatureAt hsymmM hposM hgM p (horizontalLiftField I J f X p)
      (horizontalLiftField I J f Y p))
    (hdeg : 0 < sectionalCurvatureAt hsymmM hposM hgM p (horizontalLiftField I J f X p)
        (horizontalLiftField I J f Y p) ∨
      oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Y) p ≠ 0) :
    0 < sectionalCurvatureAt hsymmB hposB hgB (f p) (X (f p)) (Y (f p)) := by
  rcases hdeg with h | h
  · exact pos_sectionalCurvatureAt_of_pos_horizontalLiftField_of_orthonormal hsymmM hposM hsymmB
      hposB hf hgM hgB hsub hriem hX hY hAXY hHYX hHXX huu hvv huv h
  · exact hM.trans_lt (sectionalCurvatureAt_horizontalLiftField_lt_of_orthonormal_of_oneillA_ne_zero
      hsymmM hposM hsymmB hposB hf hgM hgB hsub hriem hX hY hAXY hHYX hHXX huu hvv huv h)

end Submersion

/-! ## The same four statements for arbitrary horizontal vectors
-/

section MemHorizontalSpace

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {B : Type*} [TopologicalSpace B] [ChartedSpace H' B] [IsManifold J ∞ B]
  [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]
  [Bundle.RiemannianBundle (TangentSpace J : B → Type _)]
  {f : M → B} {p : M}

/-- **`K_M < K_B` on an arbitrary horizontal 2-plane with nonvanishing `A`-tensor.**

    K_M(u, v) < K_B(dπ_p u, dπ_p v),    u, v ∈ H_p independent, A_u v ≠ 0

`lt_of_le_of_ne` against `sectionalCurvatureAt_le_of_mem_horizontalSpace` and
`sectionalCurvatureAt_eq_iff_of_mem_horizontalSpace`. **No base field occurs in the statement**;
the `A`-value is `A_D F p` for a pair of fields through `u` and `v`, exactly as in the equality
case, and by the tensoriality recorded there it does not depend on the choice. The hypotheses on
`D` and `F` are the asymmetric ones of `sectionalCurvatureAt_of_mem_horizontalSpace`: `D` needs
only `D p = u`, while `F` needs horizontality and differentiability at `p`. Horizontality of `v`
is not a hypothesis — it follows from `hFhor` and `hFv`.
-/
theorem sectionalCurvatureAt_lt_of_mem_horizontalSpace_of_oneillA_ne_zero
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
    (hli : LinearIndependent ℝ ![u, v]) (hA : oneillA I J f D F p ≠ 0) :
    sectionalCurvatureAt hsymmM hposM hgM p u v
      < sectionalCurvatureAt hsymmB hposB hgB (f p) (mfderiv I J f p u) (mfderiv I J f p v) := by
  have hv : v ∈ horizontalSpace I J f p := hFv ▸ hFhor p
  refine lt_of_le_of_ne (sectionalCurvatureAt_le_of_mem_horizontalSpace hsymmM hposM hsymmB hposB
    hf hgM hgB hsub hriem hu hv hli) fun h ↦ hA ?_
  exact (sectionalCurvatureAt_eq_iff_of_mem_horizontalSpace hsymmM hposM hsymmB hposB hf hgM hgB
    hsub hriem hu hDu hFhor hFd hFv hli).mp h

/-- **Positive sectional curvature is inherited by the base, on an arbitrary horizontal plane.**

    0 < K_M(u, v)  →  0 < K_B(dπ_p u, dπ_p v),    u, v ∈ H_p linearly independent

The strict analogue of `nonneg_sectionalCurvatureAt_of_nonneg_of_mem_horizontalSpace`, with the
antecedent at the **single** plane spanned by `u` and `v` and with no vector field anywhere. One
`lt_of_lt_of_le`.

**What is still missing for "`B` has positive sectional curvature"** is exactly what is missing
for the nonnegative statement, and is recorded there: surjectivity of `f`, and the assembly of the
isomorphism `dπ_p : H_p ≃ T_{f p}B` — which `AdjointProjection` has — into the statement that
every 2-plane of `T_{f p}B` is a `dπ_p`-image. Neither is here.
-/
theorem pos_sectionalCurvatureAt_of_pos_of_mem_horizontalSpace
    (hsymmM : IsSymm (tangentMetric I M)) (hposM : IsPosDef (tangentMetric I M))
    (hsymmB : IsSymm (tangentMetric J B)) (hposB : IsPosDef (tangentMetric J B))
    (hf : ContMDiff I J ((3 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((2 : ℕ∞)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((2 : ℕ∞)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    {u v : TangentSpace I p} (hu : u ∈ horizontalSpace I J f p)
    (hv : v ∈ horizontalSpace I J f p) (hli : LinearIndependent ℝ ![u, v])
    (hM : 0 < sectionalCurvatureAt hsymmM hposM hgM p u v) :
    0 < sectionalCurvatureAt hsymmB hposB hgB (f p) (mfderiv I J f p u) (mfderiv I J f p v) :=
  hM.trans_le (sectionalCurvatureAt_le_of_mem_horizontalSpace hsymmM hposM hsymmB hposB hf hgM
    hgB hsub hriem hu hv hli)

/-- **Strict positivity of base curvature on an arbitrary horizontal plane**, from nonnegativity
upstairs together with a nonvanishing `A`-tensor.

    0 ≤ K_M(u, v)  →  (0 < K_M(u, v) ∨ A_u v ≠ 0)  →  0 < K_B(dπ_p u, dπ_p v)

`hM` is **not** implied by the second disjunct: `A_u v ≠ 0` gives `K_M < K_B` and says nothing
about the sign of `K_M`.

**Consumers, not sources.** `GM1974` and `PW2008` need positive curvature downstairs and are where
a statement of this shape is used. **Nothing about either is formalised here.** This is the
implication; both of its hypotheses are owed by constructions that do not exist in this library,
and there is at present no witness in this library at which the second disjunct holds — see
`trust/consequences/ONeillGermWitnessConsequences.lean`, whose witness is flat with `A ≡ 0`. -/
theorem pos_sectionalCurvatureAt_of_nonneg_of_mem_horizontalSpace
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
    (hli : LinearIndependent ℝ ![u, v])
    (hM : 0 ≤ sectionalCurvatureAt hsymmM hposM hgM p u v)
    (hdeg : 0 < sectionalCurvatureAt hsymmM hposM hgM p u v ∨ oneillA I J f D F p ≠ 0) :
    0 < sectionalCurvatureAt hsymmB hposB hgB (f p) (mfderiv I J f p u) (mfderiv I J f p v) := by
  rcases hdeg with h | h
  · exact pos_sectionalCurvatureAt_of_pos_of_mem_horizontalSpace hsymmM hposM hsymmB hposB hf hgM
      hgB hsub hriem hu (hFv ▸ hFhor p) hli h
  · exact hM.trans_lt (sectionalCurvatureAt_lt_of_mem_horizontalSpace_of_oneillA_ne_zero hsymmM
      hposM hsymmB hposB hf hgM hgB hsub hriem hu hDu hFhor hFd hFv hli h)

/-- **Positivity inheritance on an orthonormal horizontal pair**, with no independence hypothesis:
it is supplied by `linearIndependent_pair_of_orthonormal`.

    0 < K_M(u, v)  →  0 < K_B(dπ_p u, dπ_p v),    u, v ∈ H_p orthonormal
-/
theorem pos_sectionalCurvatureAt_of_pos_of_mem_horizontalSpace_of_orthonormal
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
    (hM : 0 < sectionalCurvatureAt hsymmM hposM hgM p u v) :
    0 < sectionalCurvatureAt hsymmB hposB hgB (f p) (mfderiv I J f p u) (mfderiv I J f p v) :=
  hM.trans_le (sectionalCurvatureAt_le_of_mem_horizontalSpace_of_orthonormal hsymmM hposM hsymmB
    hposB hf hgM hgB hsub hriem hu hv huu hvv huv)

/-- **Strict positivity from nonnegativity upstairs, on an orthonormal horizontal pair**, with no
independence hypothesis.

    0 ≤ K_M(u, v)  →  (0 < K_M(u, v) ∨ A_u v ≠ 0)  →  0 < K_B(dπ_p u, dπ_p v)

`pos_sectionalCurvatureAt_of_nonneg_of_mem_horizontalSpace` with the three normalisation equations
in place of `hli`. Unlike the basic-field orthonormal statements, this one does **not** avoid the
Gram determinant: `sectionalCurvatureAt_of_mem_horizontalSpace` carries no orthonormal
specialisation in which the denominator has been discharged to `1`, so orthonormality here buys
independence only, through `linearIndependent_pair_of_orthonormal`. The distinction is recorded
because in the basic-field layer it goes the other way.
-/
theorem pos_sectionalCurvatureAt_of_nonneg_of_mem_horizontalSpace_of_orthonormal
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
    (huu : tangentMetric I M p u u = 1) (hvv : tangentMetric I M p v v = 1)
    (huv : tangentMetric I M p u v = 0)
    (hM : 0 ≤ sectionalCurvatureAt hsymmM hposM hgM p u v)
    (hdeg : 0 < sectionalCurvatureAt hsymmM hposM hgM p u v ∨ oneillA I J f D F p ≠ 0) :
    0 < sectionalCurvatureAt hsymmB hposB hgB (f p) (mfderiv I J f p u) (mfderiv I J f p v) :=
  pos_sectionalCurvatureAt_of_nonneg_of_mem_horizontalSpace hsymmM hposM hsymmB hposB hf hgM hgB
    hsub hriem hu hDu hFhor hFd hFv (linearIndependent_pair_of_orthonormal hsymmM huu hvv huv)
    hM hdeg

end MemHorizontalSpace

end RiemannianGeometry
