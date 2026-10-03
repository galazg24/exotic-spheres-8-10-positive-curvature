/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import RiemannianGeometry.ONeillTensors
import RiemannianGeometry.VerticalBracket

/-!
# O'Neill's Lemma 2: `A_X Y = ½ 𝓥[X, Y]`

O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. **13** (1966) 459–469,
p. 461:

> **LEMMA 2.** If `X` and `Y` are horizontal vector fields, then `A_X Y = ½ 𝓥[X, Y]`.
>
> *Proof.* Since `[X,Y] = ∇_X Y − ∇_Y X`, we have the relation `𝓥[X,Y] = A_X Y − A_Y X`. Thus it
> suffices to prove the alternation property 3′, or equivalently, to show that `A_X X = 0`. We may
> assume that `X` is basic, hence that `0 = V⟨X,X⟩ = 2⟨∇_V X, X⟩` for any vertical vector field
> `V`. But `[V,X] = ∇_V X − ∇_X V` is vertical (since `V` is `π`-related to the zero vector
> field), hence `⟨∇_V X, X⟩ = ⟨∇_X V, X⟩ = −⟨V, ∇_X X⟩ = −⟨V, A_X X⟩`. Since `A_X X` is vertical,
> the result follows.

## Scope: basic fields, not arbitrary horizontal fields

Everything below is therefore proved for `horizontalLiftField I J f Y`, which is **exactly**
O'Neill's class of basic fields and not a weakening of it: by
`HorizontalLift.eq_horizontalLiftField`, a horizontal field `f`-related to a field `Y` on the base
*is* `horizontalLiftField I J f Y`, and O'Neill defines *basic* as "horizontal and `π`-related to a
field on `B`". **The extension of Lemma 2 to an arbitrary horizontal field is deferred**, and it is
deferred precisely because it needs field-slot tensoriality.

What *is* used in the field slot is field-slot **additivity**, and only for the Levi-Civita
connection, through `leviCivita_add_section`. Additivity is not tensoriality: it is an identity
between two differentiable sections, it carries `IsSymm`, `IsNondegenerate`, `IsMDiffMetric` and
differentiability hypotheses, and it says nothing about pointwise dependence. It enters at exactly
one place, `oneillA_horizontalLiftField_swap_neg`, and the reason it suffices there is recorded in
that theorem's docstring.

## Main definitions

* `verticalExtend I J f v` — for `v` a tangent vector at `p`, the vertical field
  `𝓥(FiberBundle.extend E v)`. This is the object O'Neill's proof needs and does not mention: his
  argument quantifies over vertical vector *fields* `V` but concludes about the *vector* `A_X X p`.

## Main results

* `verticalExtend_apply_self`, `isVerticalField_verticalExtend`,
  `eventually_contMDiffAt_verticalExtend` — the extension is vertical, has the prescribed value at
  `p`, and is `C^n` on a neighbourhood of `p`.
* `HorizontalLift.tangentMetric_horizontalLiftField` — **O'Neill's Lemma 1(1)**, used here in the
  one instance the proof
  consumes: `⟨Xᴴ, Xᴴ⟩ = ⟨Y, Y⟩ ∘ f` as functions on `M`. This is the step that uses relatedness, and
  it is why `V⟨X,X⟩ = 0`; see below.
* `horizontalLiftField_add` — `(Y₁ + Y₂)ᴴ = Y₁ᴴ + Y₂ᴴ`. The horizontal lift is *linear* in the base
  field because `mfderivAdjoint … p` is a continuous linear map. This is what makes the
  polarisation of `A_X X = 0` available without field-slot additivity of `A`.
* `tangentMetric_leviCivita_horizontalLiftField_self_eq_zero` — `⟨∇_X X, v⟩ = 0` for `X` basic and
  `v` vertical: O'Neill's four-step chain, run at a point.
* `oneillA_horizontalLiftField_self_eq_zero` — **`A_X X = 0` for `X` basic.**
* `oneillA_horizontalLiftField_swap_neg` — **O'Neill's property 3′**, `A_X Y = −A_Y X`, for basic
  `X`, `Y`.
* `verticalProjection_mlieBracket_eq_oneillA_sub` — **`𝓥[X,Y] = A_X Y − A_Y X`**, for *any* two
  horizontal fields differentiable at `p`; only torsion-freeness is used.
* `oneillA_horizontalLiftField_eq_two_inv_smul_verticalProjection_mlieBracket` — **LEMMA 2.**
* `oneillT_symm_of_isVerticalField` — **O'Neill's property 3**, `T_V W = T_W V`.

## Why `V⟨X, X⟩ = 0`, which O'Neill compresses

The source says only "We may assume that `X` is basic, hence that `0 = V⟨X,X⟩`". The reason, spelt
out, is Lemma 1(1). For `X = Yᴴ`, the isometry condition on horizontal vectors and
`mfderiv_horizontalLiftField` give, **at every** `z`,

    ⟨Xᴴ z, Xᴴ z⟩ = ⟨dπ_z (Xᴴ z), dπ_z (Xᴴ z)⟩ = ⟨Y (f z), Y (f z)⟩,

so `⟨X, X⟩ = (⟨Y, Y⟩) ∘ f` as a function on `M` — it is constant along the fibres. A vertical
vector `v` satisfies `dπ_p v = 0`, so the chain rule kills the derivative:
`d(⟨Y,Y⟩ ∘ f)_p (v) = d⟨Y,Y⟩_{f p} (dπ_p v) = 0`. Note this is where *relatedness* is consumed;
horizontality alone would not do, and it is a genuinely different use of "basic" from the one in
step (d), where `[V, X]` is vertical (`mem_verticalSpace_mlieBracket_horizontalLiftField`, which
also rests on relatedness and not on horizontality).

Only the **vector** `v` is needed for this step: metric compatibility puts no hypothesis on its
direction field, so `FiberBundle.extend E v` serves as the direction. The vertical *field*
`verticalExtend I J f v` is needed only for steps (c) and (d), which differentiate `V` itself.

## Where the `½` comes from, and the sign

Nothing was reconciled: both the constant and the sign came out of the proof exactly as the source
states them. Concretely, `verticalProjection_mlieBracket_eq_oneillA_sub` is
`leviCivita_sub_swap` — `∇_X Y − ∇_Y X = [X, Y]`, the project's torsion-freeness — pushed through
`𝓥` and read with `oneillA_horizontal_horizontal` on each summand; the subtraction is inherited
from that lemma and never chosen. Property 3′ then turns `A_X Y − A_Y X` into `A_X Y + A_X Y`, and
the `2` that appears is `two_smul`. So the `½` of Lemma 2 is the inverse of a `2` produced by
polarisation, not a normalisation put in by hand.

The `½` is written `(2 : ℝ)⁻¹ • ·`, a scalar action on `TangentSpace I p`, rather than
`(1 / 2 : ℝ) • ·`. The two are equal (`one_div`); `2⁻¹` is chosen because it is the spelling the
Levi-Civita connection is *defined* with in `Foundations.LeviCivita`
(`leviCivita g Y x = (2⁻¹ : ℝ) • …`) and the one `g_leviCivita_apply` states, so no numeral
normalisation step is needed anywhere between the connection and Lemma 2.

## Property 3, and why this route differs from O'Neill's

`oneillT_symm_of_isVerticalField` proves `T_V W = T_W V` from
`T_V W − T_W V = 𝓗(∇_V W − ∇_W V) = 𝓗[V, W] = 0`, the last step because the bracket of two
vertical fields is vertical (`mem_verticalSpace_mlieBracket`). O'Neill instead derives property 3
from integrability of the vertical distribution, for which this project has no theory. The two
arguments are the same fact seen from opposite ends — involutivity of `ker dπ` *is* the verticality
of `[V, W]` — but the formal route is different and is recorded as such rather than presented as a
transcription of his proof.

## Hypotheses, and what forces each

The `C^n`-order bookkeeping is inherited, not invented. `mfderiv_mlieBracket_of_related` (through
`mem_verticalSpace_mlieBracket_horizontalLiftField`) needs `minSmoothness ℝ 2 ≤ n` **and**
`(n : ℕ∞ω) ≠ ∞`; the second is a genuine restriction — a `C^∞`-at-a-point function need not be
`C^∞` on a neighbourhood — and it is the reason `n` is a finite-order variable rather than `∞`.
The submersion and isometry conditions are taken globally (`∀ z`) rather than eventually, because
`eventually_contMDiffAt_verticalExtend` applies `contMDiffAt_verticalPart` at every point of a
neighbourhood of `p` and that theorem itself wants them near each such point; a caller holding
`IsRiemannianSubmersion I J f` supplies both fields directly, along with `f` of every order.
`IsMDiffMetric E (tangentMetric I M)` is **not** a separate hypothesis where the metric is already
assumed `C^n`: `IsContMDiffMetricSection.isMDiffMetric` derives it.

## Instance notes

Rule 1 of `Foundations.HorizontalSpace` is respected: no fibrewise `InnerProductSpace` or
`NormedAddCommGroup` on a tangent space is bound to a local name anywhere in this file, and no
instance is declared. `CompleteSpace E`, `CompleteSpace E'` and `SeparatingDual ℝ E'`, which
`leviCivita` and the bracket lemmas need, are found by search from `FiniteDimensional ℝ E`,
`FiniteDimensional ℝ E'` and the real base field.

## The one spelling commitment

Everything metric-valued below is written with `tangentMetric I M p`, following
`Foundations.ONeillTensors`, and never with `inner ℝ`. `inner_eq_tangentMetric` is `rfl`, but `rw`,
`simp only` and `linarith` treat the two as different atoms, so mixing them silently costs a
rewrite at every step. The single crossing point is inside
`HorizontalLift.tangentMetric_horizontalLiftField`, where `IsRiemannianSubmersionAtPoint` —
phrased with
`inner ℝ` — is consumed.
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
  {f : M → B} {p : M} {Y Y₁ Y₂ : Π q : B, TangentSpace J q}

/-! ## Small facts used throughout

Three one-liners that would otherwise be repeated at every use site. -/

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B]
  [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]
  [Bundle.RiemannianBundle (TangentSpace J : B → Type _)] in
/-- **The order hypothesis of the bracket lemmas already excludes order `0`.** Over `ℝ`,
`minSmoothness ℝ 2 = 2`, so `minSmoothness ℝ 2 ≤ n` gives `n ≠ 0`, which is what
`ContMDiffAt.mdifferentiableAt` asks for. Recorded so that `n ≠ 0` never has to be carried as a
separate hypothesis beside `hn`. -/
theorem coe_ne_zero_of_minSmoothness_two_le {n : ℕ∞} (hn : minSmoothness ℝ 2 ≤ n) :
    (n : ℕ∞ω) ≠ 0 := by
  simp only [minSmoothness_of_isRCLikeNormedField] at hn
  intro h
  rw [h] at hn
  exact absurd hn (by decide)

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B]
  [Bundle.RiemannianBundle (TangentSpace J : B → Type _)] in
/-- **A vertical vector pairs to zero with a horizontal one**, in the `tangentMetric` spelling.
`tangentMetric_verticalProjection_horizontalProjection` says this for vectors presented as
projections; this is the form for vectors presented by membership. -/
theorem tangentMetric_eq_zero_of_mem_verticalSpace_of_mem_horizontalSpace
    {a b : TangentSpace I p} (ha : a ∈ verticalSpace I J f p)
    (hb : b ∈ horizontalSpace I J f p) : tangentMetric I M p a b = 0 := by
  rw [← mem_verticalSpace_iff_verticalProjection_eq_self.mp ha,
    ← mem_horizontalSpace_iff_horizontalProjection_eq_self.mp hb]
  exact tangentMetric_verticalProjection_horizontalProjection a b

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B]
  [Bundle.RiemannianBundle (TangentSpace J : B → Type _)] in
/-- **The horizontal projection of a vertical vector is `0`.** -/
theorem horizontalProjection_eq_zero_of_mem_verticalSpace {a : TangentSpace I p}
    (ha : a ∈ verticalSpace I J f p) : horizontalProjection I J f p a = 0 := by
  rw [horizontalProjection_eq_sub, mem_verticalSpace_iff_verticalProjection_eq_self.mp ha,
    sub_self]

/-! ## Extending a vertical vector to a vertical field

O'Neill's proof quantifies over vertical vector *fields* `V` and concludes about the *vector*
`A_X X p`. Closing that gap needs, for each vertical `v ∈ V_p`, a vertical field taking the value
`v` at `p` and differentiable near `p`. The projection of Mathlib's `FiberBundle.extend` does it:
verticality is automatic from `𝓥`, the value at `p` survives because `v` was already vertical, and
the regularity is `contMDiffAt_verticalPart` applied to `FiberBundle.exists_contMDiffOn_extend`.

Note which regularity is available. `FiberBundle.contMDiffAt_extend` gives smoothness of
`extend F v` **only at the point** `p` where the fibre lives, which is not enough: `mlieBracket`
needs its arguments differentiable near `p`. `FiberBundle.exists_contMDiffOn_extend` gives
smoothness on a neighbourhood — `extend` is constant in the trivialisation over its base set — and
that is the version used. -/

variable (I J f) in
/-- **A vertical vector extended to a vertical field**: `𝓥(FiberBundle.extend E v)`.

Defined for an arbitrary `v : TangentSpace I p`, with no verticality hypothesis;
`verticalExtend_apply_self` is where verticality of `v` is needed, and it is needed only to know
the value at `p`. -/
def verticalExtend {p : M} (v : TangentSpace I p) : Π z : M, TangentSpace I z :=
  verticalPart I J f (FiberBundle.extend E v)

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B]
  [Bundle.RiemannianBundle (TangentSpace J : B → Type _)] in
/-- **`verticalExtend` is a vertical field**, with no hypothesis: it is a `𝓥`-image. -/
theorem isVerticalField_verticalExtend {v : TangentSpace I p} :
    IsVerticalField I J f (verticalExtend I J f v) := isVerticalField_verticalPart

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B]
  [Bundle.RiemannianBundle (TangentSpace J : B → Type _)] in
/-- **`verticalExtend` has the prescribed value at `p`**, for `v` vertical: `𝓥_p v = v`. -/
theorem verticalExtend_apply_self {v : TangentSpace I p} (hv : v ∈ verticalSpace I J f p) :
    verticalExtend I J f v p = v := by
  change verticalProjection I J f p (FiberBundle.extend E v p) = v
  rw [FiberBundle.extend_apply_self]
  exact mem_verticalSpace_iff_verticalProjection_eq_self.mp hv

omit [FiniteDimensional ℝ E'] in
/-- **`verticalExtend` is `C^n` near `p`.**

`FiberBundle.exists_contMDiffOn_extend` supplies a neighbourhood on which `FiberBundle.extend E v`
is `C^∞`; `contMDiffAt_verticalPart` projects that, at each point of its interior, at the price of
its own hypotheses — one derivative of `f` and the two metrics at order `n`. The submersion and
isometry conditions are consumed at every point of that neighbourhood, which is why they are taken
globally here rather than at `p`. -/
theorem eventually_contMDiffAt_verticalExtend {n : ℕ∞} {v : TangentSpace I p}
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z) :
    ∀ᶠ z in 𝓝 p, ContMDiffAt I I.tangent ((n : ℕ∞ω)) (T% (verticalExtend I J f v)) z := by
  obtain ⟨s, hs, hsσ⟩ := FiberBundle.exists_contMDiffOn_extend (k := (∞ : ℕ∞ω)) I E v
  have hle : ((n : ℕ∞ω)) ≤ (∞ : ℕ∞ω) := by exact_mod_cast le_top
  filter_upwards [isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hs)] with z hz
  exact contMDiffAt_verticalPart isOpen_univ (Set.mem_univ z) hf.contMDiffOn (hgM z) (hgB (f z))
    (Filter.Eventually.of_forall hsub) (Filter.Eventually.of_forall hriem)
    ((hsσ.of_le hle).contMDiffAt (mem_interior_iff_mem_nhds.mp hz))

/-! ## Lemma 1(1), in the instance Lemma 2 consumes, and linearity of the lift -/

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **The horizontal lift is additive in the base field**: `(Y₁ + Y₂)ᴴ = Y₁ᴴ + Y₂ᴴ`.

Immediate, and it needs no hypothesis: `horizontalLiftField I J f Y z` is
`mfderivAdjoint … f z (Y (f z))`, and `mfderivAdjoint … f z` is a *continuous linear map*, so
`map_add` does all the work. This is the lemma that makes the polarisation of `A_X X = 0`
available: the sum of two basic fields is again a basic field, namely the lift of the sum, so
`oneillA_horizontalLiftField_self_eq_zero` applies to it directly and no additivity of `A` in its
field slot is required. -/
theorem horizontalLiftField_add (Y₁ Y₂ : Π q : B, TangentSpace J q) :
    horizontalLiftField I J f (Y₁ + Y₂)
      = horizontalLiftField I J f Y₁ + horizontalLiftField I J f Y₂ := by
  funext z
  change mfderivAdjoint (tangentMetric I M) (tangentMetric J B) f z ((Y₁ + Y₂) (f z))
    = horizontalLiftField I J f Y₁ z + horizontalLiftField I J f Y₂ z
  rw [Pi.add_apply, map_add]
  rfl

/-! ## `A_X X = 0` for a basic field

O'Neill's four steps, run at a point `p` and against a single vertical vector `v`:

1. `⟨X, V⟩ ≡ 0` on `M`, because `X` is horizontal and `V` vertical;
2. compatibility turns the vanishing of its `X`-derivative into `⟨∇_X X, V⟩ = −⟨X, ∇_X V⟩`;
3. `V⟨X, X⟩ = 0` because `⟨X,X⟩ = ⟨Y,Y⟩ ∘ f` and `dπ_p v = 0`; compatibility and symmetry then give
   `⟨∇_v X, X⟩ = 0`;
4. `[V, X]` is vertical and `X p` is horizontal, so `⟨∇_V X, X⟩ = ⟨∇_X V, X⟩`, and step 3 makes
   both `0`.

Combining 2 and 4 gives `⟨∇_X X, v⟩ = 0`. -/

/-- **`⟨∇_X X, v⟩ = 0` for `X` basic and `v` vertical** — the analytic core of `A_X X = 0`.

Steps 3 and 4 are the two independent uses of "basic": step 3 uses that `⟨X,X⟩` factors through
`f` (`HorizontalLift.tangentMetric_horizontalLiftField`), step 4 that `[V, X]` is vertical
(`mem_verticalSpace_mlieBracket_horizontalLiftField`). Both rest on `f`-relatedness of `Xᴴ`, not on
its horizontality; horizontality is used only to make the mixed pairings of step 1 vanish and to
place `X p` in `H_p` in step 4. -/
theorem tangentMetric_leviCivita_horizontalLiftField_self_eq_zero {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    (hY : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q)
    {v : TangentSpace I p} (hv : v ∈ verticalSpace I J f p) :
    tangentMetric I M p (leviCivita (tangentMetric I M) (horizontalLiftField I J f Y) p
      (horizontalLiftField I J f Y p)) v = 0 := by
  have hn0 := coe_ne_zero_of_minSmoothness_two_le hn
  have hgm : IsMDiffMetric E (tangentMetric I M) :=
    IsContMDiffMetricSection.isMDiffMetric hn0 hgM
  have hXhor : IsHorizontalField I J f (horizontalLiftField I J f Y) :=
    isHorizontalField_horizontalLiftField
  have hle : ((n : ℕ∞ω)) ≤ (((n + 1 : ℕ∞)) : ℕ∞ω) := by push_cast; exact le_self_add
  have hXe : ∀ᶠ z in 𝓝 p,
      ContMDiffAt I I.tangent ((n : ℕ∞ω)) (T% (horizontalLiftField I J f Y)) z :=
    Filter.Eventually.of_forall fun z ↦
      contMDiffAt_horizontalLiftField isOpen_univ (Set.mem_univ z) hf.contMDiffOn (hgM z)
        (hgB (f z)) (hY (f z))
  have hXd : MDiffAt (T% (horizontalLiftField I J f Y)) p :=
    hXe.self_of_nhds.mdifferentiableAt hn0
  have hfp : ContMDiffAt I J ((n : ℕ∞ω)) f p := (hf p).of_le hle
  have hfd : MDiffAt f p := hfp.mdifferentiableAt hn0
  have hYY : MDiffAt (fun q ↦ tangentMetric J B q (Y q) (Y q)) (f p) :=
    mdiffAt_pairing ((hgB (f p)).mdifferentiableAt hn0) ((hY (f p)).mdifferentiableAt hn0)
      ((hY (f p)).mdifferentiableAt hn0)
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
  -- step 3: `V⟨X,X⟩ = 0`, hence `⟨∇_v X, X p⟩ = 0`. The direction field is
  -- `FiberBundle.extend E v`, which compatibility accepts with no hypothesis.
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
      (Filter.Eventually.of_forall hsub) (Filter.Eventually.of_forall hriem) hVvert hVe hXe
      (Filter.Eventually.of_forall hY)
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

/-- **`A_X X = 0` for a basic field `X = Yᴴ`** — O'Neill's step towards property 3′.

The last move is the one that needs care. `isNondegenerate_tangentMetric` concludes `w = 0` from
`∀ u, ⟨w, u⟩ = 0` with `u` ranging over *all* of `T_pM`, whereas
`tangentMetric_leviCivita_horizontalLiftField_self_eq_zero` supplies the pairing only against
**vertical** `u`. The gap is closed by decomposing `u = 𝓗u + 𝓥u`: the horizontal half pairs to zero
with `A_X X p` because that vector is a `𝓥`-image
(`tangentMetric_verticalProjection_horizontalProjection`), and the vertical half is exactly the
case already proved. So nondegeneracy is applied on the whole tangent space, not restricted to
`V_p`, and no nondegeneracy of the restricted metric is needed. -/
theorem oneillA_horizontalLiftField_self_eq_zero {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    (hY : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q) :
    oneillA I J f (horizontalLiftField I J f Y) (horizontalLiftField I J f Y) p = 0 := by
  have hXhor : IsHorizontalField I J f (horizontalLiftField I J f Y) :=
    isHorizontalField_horizontalLiftField
  rw [oneillA_horizontal_horizontal hXhor hXhor]
  refine isNondegenerate_tangentMetric p _ fun u ↦ ?_
  have hd : horizontalProjection I J f p u + verticalProjection I J f p u = u :=
    horizontalProjection_add_verticalProjection u
  rw [← hd, map_add, tangentMetric_verticalProjection_horizontalProjection,
    tangentMetric_verticalProjection_left, verticalProjection_verticalProjection, zero_add]
  exact tangentMetric_leviCivita_horizontalLiftField_self_eq_zero hn hn' hf hgM hgB hsub hriem hY
    (verticalProjection_mem u)

/-! ## Property 3′: alternation of `A` -/

/-- **O'Neill's property 3′: `A_X Y = −A_Y X` for basic `X`, `Y`.**

The polarisation `A_{X+Y}(X+Y) = A_X X + A_Y X + A_X Y + A_Y Y` would ordinarily need additivity of
`A` in its **field** slot, which is unavailable. It is avoided as follows. By
`horizontalLiftField_add` the sum `Y₁ᴴ + Y₂ᴴ` *is* the basic field `(Y₁ + Y₂)ᴴ`, so
`oneillA_horizontalLiftField_self_eq_zero` applies to it as a basic field in its own right, giving
`A_{Y₁ᴴ+Y₂ᴴ}(Y₁ᴴ+Y₂ᴴ) p = 0` directly. The four-term expansion is then performed **inside**
`oneillA_horizontal_horizontal`, on the Levi-Civita connection, where additivity in the
differentiated section is `leviCivita_add_section` and additivity in the direction is linearity of
a continuous linear map. So the only field-slot input is additivity of `∇`, not any tensoriality of
`A`, and it is charged for honestly: `leviCivita_add_section` is what brings
`IsMDiffMetric E (tangentMetric I M)` and the differentiability of `Y₁ᴴ`, `Y₂ᴴ` at `p` into this
proof.

Note that the alternative route through the bracket is genuinely vacuous:
`verticalProjection_mlieBracket_eq_oneillA_sub` plus antisymmetry of `[·,·]` gives
`A_X Y − A_Y X = −(A_Y X − A_X Y)`, which is an identity and carries no information. 

-/
theorem oneillA_horizontalLiftField_swap_neg {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    (hY₁ : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y₁) q)
    (hY₂ : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y₂) q) :
    oneillA I J f (horizontalLiftField I J f Y₁) (horizontalLiftField I J f Y₂) p
      = -oneillA I J f (horizontalLiftField I J f Y₂) (horizontalLiftField I J f Y₁) p := by
  have hn0 := coe_ne_zero_of_minSmoothness_two_le hn
  have hgm : IsMDiffMetric E (tangentMetric I M) :=
    IsContMDiffMetricSection.isMDiffMetric hn0 hgM
  have hX₁hor : IsHorizontalField I J f (horizontalLiftField I J f Y₁) :=
    isHorizontalField_horizontalLiftField
  have hX₂hor : IsHorizontalField I J f (horizontalLiftField I J f Y₂) :=
    isHorizontalField_horizontalLiftField
  have hShor : IsHorizontalField I J f
      (horizontalLiftField I J f Y₁ + horizontalLiftField I J f Y₂) := fun z ↦
    (horizontalSpace I J f z).add_mem (horizontalLiftField_mem z) (horizontalLiftField_mem z)
  have hX₁d : MDiffAt (T% (horizontalLiftField I J f Y₁)) p :=
    (contMDiffAt_horizontalLiftField isOpen_univ (Set.mem_univ p) hf.contMDiffOn (hgM p)
      (hgB (f p)) (hY₁ (f p))).mdifferentiableAt hn0
  have hX₂d : MDiffAt (T% (horizontalLiftField I J f Y₂)) p :=
    (contMDiffAt_horizontalLiftField isOpen_univ (Set.mem_univ p) hf.contMDiffOn (hgM p)
      (hgB (f p)) (hY₂ (f p))).mdifferentiableAt hn0
  -- `A_X X = 0` for the three basic fields `Y₁ᴴ`, `Y₂ᴴ` and `(Y₁ + Y₂)ᴴ = Y₁ᴴ + Y₂ᴴ`
  have h₁ := oneillA_horizontalLiftField_self_eq_zero (Y := Y₁) (p := p) hn hn' hf hgM hgB hsub
    hriem hY₁
  have h₂ := oneillA_horizontalLiftField_self_eq_zero (Y := Y₂) (p := p) hn hn' hf hgM hgB hsub
    hriem hY₂
  have hS := oneillA_horizontalLiftField_self_eq_zero (Y := Y₁ + Y₂) (p := p) hn hn' hf hgM hgB
    hsub hriem fun q ↦ (hY₁ q).add_section (hY₂ q)
  rw [horizontalLiftField_add] at hS
  -- the four-term expansion, performed on `∇` rather than on `A`
  have hexpand : oneillA I J f (horizontalLiftField I J f Y₁ + horizontalLiftField I J f Y₂)
        (horizontalLiftField I J f Y₁ + horizontalLiftField I J f Y₂) p
      = oneillA I J f (horizontalLiftField I J f Y₁) (horizontalLiftField I J f Y₁) p
        + oneillA I J f (horizontalLiftField I J f Y₂) (horizontalLiftField I J f Y₁) p
        + (oneillA I J f (horizontalLiftField I J f Y₁) (horizontalLiftField I J f Y₂) p
          + oneillA I J f (horizontalLiftField I J f Y₂) (horizontalLiftField I J f Y₂) p) := by
    rw [oneillA_horizontal_horizontal hShor hShor,
      oneillA_horizontal_horizontal hX₁hor hX₁hor, oneillA_horizontal_horizontal hX₂hor hX₁hor,
      oneillA_horizontal_horizontal hX₁hor hX₂hor, oneillA_horizontal_horizontal hX₂hor hX₂hor,
      leviCivita_add_section isSymm_tangentMetric isNondegenerate_tangentMetric hgm hX₁d hX₂d]
    simp only [Pi.add_apply, add_apply, map_add]
    abel
  have h := hexpand.symm.trans hS
  rw [h₁, h₂, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

/-! ## `𝓥[X, Y] = A_X Y − A_Y X`, and Lemma 2 -/

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B]
  [Bundle.RiemannianBundle (TangentSpace J : B → Type _)] in
/-- **`𝓥[X, Y] = A_X Y − A_Y X`** for `X`, `Y` horizontal and differentiable at `p`.

Torsion-freeness and nothing else. `leviCivita_sub_swap` is `∇_X Y − ∇_Y X = [X, Y]` in applied
form; pushing `𝓥` through the difference and reading each summand with
`oneillA_horizontal_horizontal` gives the statement. Both the subtraction and its direction are
inherited from `leviCivita_sub_swap` and match the source.

Stated for arbitrary horizontal fields, not only for basic ones: this half of Lemma 2 needs no
relatedness, no submersion condition and no vertical bracket. -/
theorem verticalProjection_mlieBracket_eq_oneillA_sub {X W : Π z : M, TangentSpace I z}
    (hgm : IsMDiffMetric E (tangentMetric I M)) (hXhor : IsHorizontalField I J f X)
    (hWhor : IsHorizontalField I J f W) (hXd : MDiffAt (T% X) p) (hWd : MDiffAt (T% W) p) :
    verticalProjection I J f p (mlieBracket I X W p)
      = oneillA I J f X W p - oneillA I J f W X p := by
  have hswap := leviCivita_sub_swap (g := tangentMetric I M) (X := X) (Y := W) (x := p)
    isSymm_tangentMetric isNondegenerate_tangentMetric hgm hXd hWd
  rw [oneillA_horizontal_horizontal hXhor hWhor, oneillA_horizontal_horizontal hWhor hXhor,
    ← hswap, map_sub]

/-- **O'Neill's LEMMA 2** (ON1966, p. 461): `A_X Y = ½ 𝓥[X, Y]` for basic `X`, `Y`.

    oneillA I J f Y₁ᴴ Y₂ᴴ p = (2 : ℝ)⁻¹ • 𝓥_p [Y₁ᴴ, Y₂ᴴ]_p

The `½` is a scalar action on `TangentSpace I p`, written `(2 : ℝ)⁻¹ •` — the spelling
`Foundations.LeviCivita` already uses for the half in the definition of the connection.

The two inputs are `verticalProjection_mlieBracket_eq_oneillA_sub` (torsion-freeness) and
`oneillA_horizontalLiftField_swap_neg` (property 3′), and the `2` that gets inverted is produced by
`two_smul` out of `A_X Y − A_Y X = A_X Y + A_X Y`. Neither the constant nor the sign was adjusted
at any point: see "Where the `½` comes from, and the sign" in the module docstring. 

-/
theorem oneillA_horizontalLiftField_eq_two_inv_smul_verticalProjection_mlieBracket {n : ℕ∞}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z)
    (hY₁ : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y₁) q)
    (hY₂ : ∀ q, ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y₂) q) :
    oneillA I J f (horizontalLiftField I J f Y₁) (horizontalLiftField I J f Y₂) p
      = (2 : ℝ)⁻¹ • verticalProjection I J f p
          (mlieBracket I (horizontalLiftField I J f Y₁) (horizontalLiftField I J f Y₂) p) := by
  have hn0 := coe_ne_zero_of_minSmoothness_two_le hn
  have hgm : IsMDiffMetric E (tangentMetric I M) :=
    IsContMDiffMetricSection.isMDiffMetric hn0 hgM
  have hX₁d : MDiffAt (T% (horizontalLiftField I J f Y₁)) p :=
    (contMDiffAt_horizontalLiftField isOpen_univ (Set.mem_univ p) hf.contMDiffOn (hgM p)
      (hgB (f p)) (hY₁ (f p))).mdifferentiableAt hn0
  have hX₂d : MDiffAt (T% (horizontalLiftField I J f Y₂)) p :=
    (contMDiffAt_horizontalLiftField isOpen_univ (Set.mem_univ p) hf.contMDiffOn (hgM p)
      (hgB (f p)) (hY₂ (f p))).mdifferentiableAt hn0
  have hbr := verticalProjection_mlieBracket_eq_oneillA_sub hgm
    (isHorizontalField_horizontalLiftField (Y := Y₁))
    (isHorizontalField_horizontalLiftField (Y := Y₂)) hX₁d hX₂d
  have hsw := oneillA_horizontalLiftField_swap_neg (Y₁ := Y₂) (Y₂ := Y₁) (p := p) hn hn' hf hgM
    hgB hsub hriem hY₂ hY₁
  rw [hbr, hsw, sub_neg_eq_add, ← two_smul ℝ, smul_smul]
  norm_num

/-! ## Property 3: symmetry of `T` -/

omit [Bundle.RiemannianBundle (TangentSpace J : B → Type _)] in
/-- **O'Neill's property 3: `T_V W = T_W V` for `V`, `W` vertical.**

`oneillT_vertical_vertical` twice gives `T_V W − T_W V = 𝓗(∇_V W − ∇_W V)`, torsion-freeness turns
the bracketed difference into `[V, W]`, and `mem_verticalSpace_mlieBracket` makes that vertical, so
its horizontal projection vanishes.

This is **not** O'Neill's proof, which derives property 3 from integrability of the vertical
distribution; this development has no theory of integrability, and the substitute is the verticality
of the bracket of two vertical fields, which `Foundations.VerticalBracket` proves with **no
submersion hypothesis** — `f` need only be `C^n` at `p`. The two facts are equivalent in content
(involutivity of `ker dπ`), but the route is different and is recorded rather than passed off as a
transcription. 

-/
theorem oneillT_symm_of_isVerticalField {n : ℕ∞} {V W : Π z : M, TangentSpace I z}
    (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hgm : IsMDiffMetric E (tangentMetric I M)) (hf : ContMDiffAt I J ((n : ℕ∞ω)) f p)
    (hV : IsVerticalField I J f V) (hW : IsVerticalField I J f W)
    (hVe : ∀ᶠ z in 𝓝 p, ContMDiffAt I I.tangent ((n : ℕ∞ω)) (T% V) z)
    (hWe : ∀ᶠ z in 𝓝 p, ContMDiffAt I I.tangent ((n : ℕ∞ω)) (T% W) z) :
    oneillT I J f V W p = oneillT I J f W V p := by
  have hn0 := coe_ne_zero_of_minSmoothness_two_le hn
  have hswap := leviCivita_sub_swap (g := tangentMetric I M) (X := V) (Y := W) (x := p)
    isSymm_tangentMetric isNondegenerate_tangentMetric hgm
    (hVe.self_of_nhds.mdifferentiableAt hn0) (hWe.self_of_nhds.mdifferentiableAt hn0)
  have h0 : horizontalProjection I J f p (mlieBracket I V W p) = 0 :=
    horizontalProjection_eq_zero_of_mem_verticalSpace
      (mem_verticalSpace_mlieBracket hn hn' hf hV hW hVe hWe)
  rw [oneillT_vertical_vertical hV hW, oneillT_vertical_vertical hW hV, ← sub_eq_zero, ← map_sub,
    hswap, h0]

end RiemannianGeometry
