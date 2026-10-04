/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import RiemannianGeometry.SectionalCurvature
import RiemannianGeometry.ONeillCorollaryOne

/-!
# Riemannian submersions are curvature nondecreasing on horizontal planes

`RiemannianGeometry.ONeillCorollaryOne` proves O'Neill's *formula*

    K_M(Xᴴ p, Yᴴ p) = K_B(X (f p), Y (f p)) − 3 ⟪A_{Xᴴ}Yᴴ, A_{Xᴴ}Yᴴ⟫ / ‖Xᴴ p ∧ Yᴴ p‖².

* `ON1966` p. 465, closing remark of §4: "in the Riemannian case, equation (3) shows that
  submersions are curvature-increasing (more precisely, nondecreasing) on horizontal tangent
  planes";
* `GM1974` abstract, p. 401: "By a formula of O'Neill, `Σ` automatically inherits **nonnegative
  sectional curvature**";
* `W2001_LOTS` introduction, p. 161: "Riemannian submersions are **curvature nondecreasing on
  horizontal planes** [15]".

## Where the two hypotheses come from, and why there are exactly two

The subtracted term is a quotient, and the two facts about it are independent:

* its **numerator** `3⟪A_{Xᴴ}Yᴴ, A_{Xᴴ}Yᴴ⟫` is `≥ 0`. `isPosDef_tangentMetric` gives `> 0` only
  off the zero vector, so the degenerate case `A_{Xᴴ}Yᴴ p = 0` — which is exactly the integrable
  case, and the one O'Neill's "more precisely, nondecreasing" is about — has to be handled
  separately. That is `IsPosDef.nonneg`.
* its **denominator** `‖Xᴴ p ∧ Yᴴ p‖²` is `> 0`, by `gramDet_pos`, which needs the pair to be
  **linearly independent**. This is not a technicality that could be dropped: on a dependent pair
  `sectionalCurvatureAt` is `0/0 = 0` on both sides, the "inequality" degenerates to `0 ≤ 0`, and
  it would be true but about nothing. O'Neill writes `K(P_xy)` and `‖x ∧ y‖²`, so independence is
  part of what `P_xy` means.

`sectionalCurvatureAt_horizontalLiftField` itself needs neither hypothesis, because it is an
identity and `sub_div` is unconditional. The inequality needs both. That is the whole content of
this module.

## The orthonormal case needs no independence hypothesis — and the reason is not the obvious one

`sectionalCurvatureAt_horizontalLiftField_le_of_orthonormal` carries no
`LinearIndependent` argument. Two different facts could explain that, and only one of them is
operative:

1. an orthonormal pair in a positive-definite metric **is** linearly independent — true, and proved
   here as `linearIndependent_pair_of_orthonormal`, because the brief for this module asked for it
   to be proved rather than assumed;
2. the orthonormal form of Corollary 1(3) has **no denominator at all** —
   `sectionalCurvatureAt_horizontalLiftField_of_orthonormal` has already discharged it to `1` via
   `gramDet_eq_one` — so the inequality follows from the numerator alone.

It is (2) that the proof uses: `gramDet_pos` is never invoked, and independence is never needed.
(1) is proved anyway and is the honest answer to "does orthonormality give independence?", but it
is *not* load-bearing here. Recording which of the two closed the proof matters, because a reader
who assumed (1) would believe the orthonormal statement is a corollary of the general one
specialised along an independence proof, and it is not.

## Main results

* `IsPosDef.nonneg`, `IsPosDef.self_eq_zero_iff` — the two facts about a positive-definite
  metric-as-data that the inequality needs, and which `IsPosDef` does not state directly.
* `linearIndependent_pair_of_orthonormal` — orthonormal implies linearly independent.
* `sectionalCurvatureAt_horizontalLiftField_le` — **`K_M ≤ K_B` on horizontal planes.**
* `sectionalCurvatureAt_horizontalLiftField_le_of_orthonormal` — the same, orthonormal.
* `sectionalCurvatureAt_horizontalLiftField_eq_iff` — **the equality case**: `K_M = K_B` exactly
  when `A_{Xᴴ}Yᴴ p = 0`. This is O'Neill's parenthetical "more precisely, nondecreasing".
* `nonneg_sectionalCurvatureAt_of_nonneg_horizontalLiftField` and its orthonormal form — **the
  nonnegativity inheritance `GM1974` cites**, with the weakest antecedent that works.

## Regularity

**The metrics stay at `C²`**, and `f` at `C³`, verbatim from
`sectionalCurvatureAt_horizontalLiftField`; nothing here differentiates anything. The three
`Mathlib` order hypotheses are unchanged and no declaration in this module raises the regularity of
either metric.
-/

noncomputable section

open Bundle VectorField
open scoped Manifold ContDiff Topology

namespace RiemannianGeometry

/-! ## Positive definiteness: the nonnegative and the degenerate case -/

section PosDef

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {g : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
  {x : M}

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- **A positive-definite metric is nonnegative on the diagonal**, including at `0`.

`IsPosDef` is stated with the hypothesis `v ≠ 0`, which is what makes it usable as a
nondegeneracy condition, and which is also why it does not immediately give the `0 ≤ g y v v`
that a nonnegativity argument wants. The zero vector is the whole difference, and it is the case
that matters: `A_{Xᴴ}Yᴴ p = 0` is exactly the configuration in which O'Neill's inequality is an
equality, so a proof that quietly excluded it would be proving a strictly weaker statement. -/
theorem IsPosDef.nonneg (hpos : IsPosDef g) (y : M) (v : TangentSpace I y) : 0 ≤ g y v v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · exact (hpos y v hv).le

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- **A positive-definite metric vanishes on the diagonal only at `0`.** The forward direction is
`IsPosDef` contrapositive; the reverse is linearity. Used for the equality case of O'Neill's
inequality, where `⟪A_{Xᴴ}Yᴴ, A_{Xᴴ}Yᴴ⟫ = 0` has to be converted into `A_{Xᴴ}Yᴴ p = 0`. -/
theorem IsPosDef.self_eq_zero_iff (hpos : IsPosDef g) (y : M) (v : TangentSpace I y) :
    g y v v = 0 ↔ v = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]; simp⟩
  by_contra hv
  exact absurd h (ne_of_gt (hpos y v hv))

omit [FiniteDimensional ℝ E] in
/-- **An orthonormal pair is linearly independent**, for a positive-definite metric supplied as
data.

Pair the relation `s • u + t • v = 0` with `u` and with `v`: the first gives `s = 0` and the second
`t = 0`, using `g u u = g v v = 1` and `g u v = 0`. Positive definiteness is *not* used — the proof
needs only the three normalisation equations and symmetry, so the lemma holds for any symmetric
metric-as-data with an orthonormal pair, whether or not it is definite. The hypothesis is
nevertheless the one the submersion theorems below supply.
-/
theorem linearIndependent_pair_of_orthonormal (hsymm : IsSymm g) {u v : TangentSpace I x}
    (huu : g x u u = 1) (hvv : g x v v = 1) (huv : g x u v = 0) :
    LinearIndependent ℝ ![u, v] := by
  refine LinearIndependent.pair_iff.mpr fun s t hst ↦ ?_
  have h1 : g x (s • u + t • v) u = 0 := by rw [hst]; simp
  have h2 : g x (s • u + t • v) v = 0 := by rw [hst]; simp
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul] at h1 h2
  rw [hsymm x v u, huu, huv] at h1
  rw [hvv, huv] at h2
  constructor <;> linarith

end PosDef

/-! ## O'Neill's inequality -/

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

/-- **Riemannian submersions are curvature nondecreasing on horizontal planes.**

    K_M(Xᴴ p, Yᴴ p) ≤ K_B(X (f p), Y (f p))

`sectionalCurvatureAt_horizontalLiftField` and two sign facts, and nothing else. The subtracted
term is `3⟪A_{Xᴴ}Yᴴ, A_{Xᴴ}Yᴴ⟫ / ‖Xᴴ p ∧ Yᴴ p‖²`, whose numerator is `≥ 0` by `IsPosDef.nonneg`
(the case `A_{Xᴴ}Yᴴ p = 0` included) and whose denominator is `> 0` by `gramDet_pos`.

**Why `hli` and not something weaker.** `gramDet_pos` needs linear independence and there is
nothing weaker available: the Gram determinant of a dependent pair is `0`, not merely possibly `0`.
Independence is also what O'Neill's notation asserts — `K(P_xy)` and `‖x ∧ y‖²` presuppose that
`x`, `y` span a plane — so the hypothesis is not an addition to his statement but a rendering of
it. It is stated on the values `Xᴴ p`, `Yᴴ p` in `T_pM`, which is the pair the Gram determinant is
taken of; by `gramDet_horizontalLiftField` this is equivalent to independence of `X (f p)`,
`Y (f p)` in `T_{f p}B`, but the `M`-side form is the one `gramDet_pos` consumes and it is left as
stated rather than translated.

**Consumers, not sources.** `GM1974` abstract p. 401 and §3 p. 403, and `W2001_LOTS` introduction
p. 161, both cite this inequality. Neither is formalised by this theorem, and in particular this
is not a step towards `GM1974`'s theorem, which needs the Gromoll–Meyer construction. -/
theorem sectionalCurvatureAt_horizontalLiftField_le
    (hli : LinearIndependent ℝ ![horizontalLiftField I J f X p,
      horizontalLiftField I J f Y p]) :
    sectionalCurvatureAt hsymmM hposM hgM p (horizontalLiftField I J f X p)
        (horizontalLiftField I J f Y p)
      ≤ sectionalCurvatureAt hsymmB hposB hgB (f p) (X (f p)) (Y (f p)) := by
  rw [sectionalCurvatureAt_horizontalLiftField hsymmM hposM hsymmB hposB hf hgM hgB hsub hriem
    hX hY hAXY hHYX hHXX]
  have hnum : (0 : ℝ) ≤ 3 * tangentMetric I M p
      (oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Y) p)
      (oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Y) p) := by
    have := hposM.nonneg p
      (oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Y) p)
    linarith
  have hden : 0 < gramDet (tangentMetric I M) p (horizontalLiftField I J f X p)
      (horizontalLiftField I J f Y p) := gramDet_pos hsymmM hposM hli
  have := div_nonneg hnum hden.le
  linarith

/-- **The inequality on an orthonormal horizontal pair**, with no independence hypothesis.

    K_M(u, v) ≤ K_B(dπ u, dπ v),    u = Xᴴ p, v = Yᴴ p orthonormal.

`sectionalCurvatureAt_horizontalLiftField_of_orthonormal` has already reduced the correction term
to `3⟪A_{Xᴴ}Yᴴ, A_{Xᴴ}Yᴴ⟫` with **no division**, so the only fact needed is that the numerator is
nonnegative. `gramDet_pos` is not used and linear independence is not needed — see the module
docstring for why this is *not* the same as saying that orthonormality supplies the missing
independence, which it does (`linearIndependent_pair_of_orthonormal`) but is not what closes this
proof.
-/
theorem sectionalCurvatureAt_horizontalLiftField_le_of_orthonormal
    (huu : tangentMetric I M p (horizontalLiftField I J f X p)
      (horizontalLiftField I J f X p) = 1)
    (hvv : tangentMetric I M p (horizontalLiftField I J f Y p)
      (horizontalLiftField I J f Y p) = 1)
    (huv : tangentMetric I M p (horizontalLiftField I J f X p)
      (horizontalLiftField I J f Y p) = 0) :
    sectionalCurvatureAt hsymmM hposM hgM p (horizontalLiftField I J f X p)
        (horizontalLiftField I J f Y p)
      ≤ sectionalCurvatureAt hsymmB hposB hgB (f p) (X (f p)) (Y (f p)) := by
  rw [sectionalCurvatureAt_horizontalLiftField_of_orthonormal hsymmM hposM hsymmB hposB hf hgM
    hgB hsub hriem hX hY hAXY hHYX hHXX huu hvv huv]
  have := hposM.nonneg p
    (oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Y) p)
  linarith

/-- **The equality case: `K_M = K_B` exactly when `A_{Xᴴ}Yᴴ p = 0`.**

This is O'Neill's parenthesis. "Curvature-increasing" would be false — a Riemannian submersion with
integrable horizontal distribution is a local product and the curvatures agree — and "more
precisely, nondecreasing" is the correction. The iff says exactly where the two cases divide, and
`A_{Xᴴ}Yᴴ = ½𝓥[Xᴴ, Yᴴ]` — Lemma 2, formalised as
`RiemannianGeometry.oneillA_horizontalLiftField_eq_two_inv_smul_verticalProjection_mlieBracket` —
identifies the dividing condition as integrability of the horizontal distribution along the pair.

Both directions come out of `sectionalCurvatureAt_horizontalLiftField`: the quotient
`3⟪A_{Xᴴ}Yᴴ, A_{Xᴴ}Yᴴ⟫ / ‖Xᴴ p ∧ Yᴴ p‖²` vanishes iff its numerator does — the denominator being
nonzero by `gramDet_pos`, which is where `hli` is used a second time — and the numerator vanishes
iff `A_{Xᴴ}Yᴴ p = 0` by `IsPosDef.self_eq_zero_iff`. Positive definiteness is used in both
directions and the statement is false without it: for an indefinite metric `⟪A, A⟫` can vanish on a
nonzero `A`.
-/
theorem sectionalCurvatureAt_horizontalLiftField_eq_iff
    (hli : LinearIndependent ℝ ![horizontalLiftField I J f X p,
      horizontalLiftField I J f Y p]) :
    sectionalCurvatureAt hsymmM hposM hgM p (horizontalLiftField I J f X p)
        (horizontalLiftField I J f Y p)
      = sectionalCurvatureAt hsymmB hposB hgB (f p) (X (f p)) (Y (f p))
      ↔ oneillA I J f (horizontalLiftField I J f X) (horizontalLiftField I J f Y) p = 0 := by
  rw [sectionalCurvatureAt_horizontalLiftField hsymmM hposM hsymmB hposB hf hgM hgB hsub hriem
    hX hY hAXY hHYX hHXX, sub_eq_self, div_eq_zero_iff]
  have hden : 0 < gramDet (tangentMetric I M) p (horizontalLiftField I J f X p)
      (horizontalLiftField I J f Y p) := gramDet_pos hsymmM hposM hli
  refine ⟨fun h ↦ ?_, fun h ↦ Or.inl ?_⟩
  · rcases h with h | h
    · exact (hposM.self_eq_zero_iff p _).mp (by linarith)
    · exact absurd h hden.ne'
  · rw [h]; simp

/-- **Nonnegative sectional curvature is inherited by the base**, on one horizontal plane at a
time.

    0 ≤ K_M(Xᴴ p, Yᴴ p)  →  0 ≤ K_B(X (f p), Y (f p))

This is the statement `GM1974` invokes with "By a formula of O'Neill, `Σ` automatically inherits
nonnegative sectional curvature".

**The weakest antecedent, which is the point of the statement's shape.** The hypothesis is
nonnegativity of `K_M` at the **single plane** spanned by `Xᴴ p` and `Yᴴ p` — not on all horizontal
planes at `p`, not at all points of `M`, and certainly not "`M` has nonnegative sectional
curvature". The proof is `le_trans` against
`sectionalCurvatureAt_horizontalLiftField_le`, and transitivity consumes exactly one instance of
the antecedent. Any global quantifier here would be a hypothesis that is not needed.

**What this does not give, stated so it is not read into it.** The conclusion is nonnegativity at
the planes of `T_{f p}B` spanned by `X (f p)`, `Y (f p)` for `C²` fields `X`, `Y` on `B`, at points
`f p` in the image of `f`. Getting from there to "`B` has nonnegative sectional curvature" needs
two further things that this library does not have: surjectivity of `f`, and an extension of an
arbitrary pair of tangent vectors at a point of `B` to a pair of globally `C²` vector fields —
`hX`, `hY` are `ContMDiffAt` at *every* point, so a pair of bare tangent vectors is not enough.
Neither is hard, and neither is here; until they are, the honest scope of the inheritance is
plane-by-plane.

**Consumers, not sources.** `GM1974` abstract p. 401 and `W2001_LOTS` introduction p. 161 cite
this inheritance. **Nothing about `GM1974` is formalised here.** `GM1974`'s theorem is about the
Gromoll–Meyer sphere `Σ`, obtained from a biquotient construction that does not exist in this
library; what is formalised is the O'Neill inequality that `GM1974` invokes, and only for planes
spanned by values of basic fields. -/
theorem nonneg_sectionalCurvatureAt_of_nonneg_horizontalLiftField
    (hli : LinearIndependent ℝ ![horizontalLiftField I J f X p,
      horizontalLiftField I J f Y p])
    (hM : 0 ≤ sectionalCurvatureAt hsymmM hposM hgM p (horizontalLiftField I J f X p)
      (horizontalLiftField I J f Y p)) :
    0 ≤ sectionalCurvatureAt hsymmB hposB hgB (f p) (X (f p)) (Y (f p)) :=
  hM.trans (sectionalCurvatureAt_horizontalLiftField_le hsymmM hposM hsymmB hposB hf hgM hgB
    hsub hriem hX hY hAXY hHYX hHXX hli)

/-- **Nonnegativity inheritance on an orthonormal horizontal pair**, with no independence
hypothesis.

    0 ≤ K_M(u, v)  →  0 ≤ K_B(dπ u, dπ v),    u = Xᴴ p, v = Yᴴ p orthonormal.

The same weakest antecedent as `nonneg_sectionalCurvatureAt_of_nonneg_horizontalLiftField` — one
plane — with the independence hypothesis replaced by the three normalisation equations, which the
proof routes through `sectionalCurvatureAt_horizontalLiftField_le_of_orthonormal` and hence never
needs a Gram determinant for. This is the form in which the downstream literature applies the
inheritance, since it chooses an orthonormal horizontal frame.
-/
theorem nonneg_sectionalCurvatureAt_of_nonneg_horizontalLiftField_of_orthonormal
    (huu : tangentMetric I M p (horizontalLiftField I J f X p)
      (horizontalLiftField I J f X p) = 1)
    (hvv : tangentMetric I M p (horizontalLiftField I J f Y p)
      (horizontalLiftField I J f Y p) = 1)
    (huv : tangentMetric I M p (horizontalLiftField I J f X p)
      (horizontalLiftField I J f Y p) = 0)
    (hM : 0 ≤ sectionalCurvatureAt hsymmM hposM hgM p (horizontalLiftField I J f X p)
      (horizontalLiftField I J f Y p)) :
    0 ≤ sectionalCurvatureAt hsymmB hposB hgB (f p) (X (f p)) (Y (f p)) :=
  hM.trans (sectionalCurvatureAt_horizontalLiftField_le_of_orthonormal hsymmM hposM hsymmB hposB
    hf hgM hgB hsub hriem hX hY hAXY hHYX hHXX huu hvv huv)

end Submersion

end RiemannianGeometry
