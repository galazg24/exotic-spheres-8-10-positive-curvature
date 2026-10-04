/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Curvature.Southern.Potential

/-! # Infrastructure: gradients, unit normals and second fundamental forms of level sets

For a metric section `g` on a manifold `M` (`RiemannianGeometry`'s conventions) and a smooth `f : M → ℝ`:

* `gradAt hnd f x`: the gradient, `g(grad f, ·) = df` (via `RiemannianGeometry`'s `gDual`);
* `unitNormal hnd f`: `grad f / |grad f|`, the unit normal to the level sets of `f` pointing
  towards increasing `f`, i.e. **outward** for the sublevel set `{f ≤ c}`;
* `sff hnd f x v w = g(∇_v ν, w)`, the second fundamental form of the level set through `x`
  with respect to `ν`, for `v, w ∈ ker df_x`. With this sign the boundary of a round ball is
  positive, which is [GG]'s and Reiser–Wraith's convention.

* **`RWGluing`**: [GG] `prop:gluing` (Reiser–Wraith, Theorem A(i), `k = 1`) as a named hypothesis,
  for a closed manifold cut along a regular level set.
-/

open RiemannianGeometry Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Real

open scoped Manifold ContDiff

noncomputable section

section SFF

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {g : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}

/-- The gradient of `f` at `x`: the vector with `g_x(grad f, w) = df_x(w)`. -/
def gradAt (hnd : IsNondegenerate g) (f : M → ℝ) (x : M) : TangentSpace I x :=
  (gDual (hnd x)).symm (mvfderiv I f x)

theorem g_gradAt (hnd : IsNondegenerate g) (f : M → ℝ) (x : M) (w : TangentSpace I x) :
    g x (gradAt hnd f x) w = mvfderiv I f x w := by
  rw [← gDual_apply (hnd x), gradAt, ContinuousLinearEquiv.apply_symm_apply]

/-- The gradient is characterised by `g(grad f, ·) = df`. -/
theorem eq_gradAt (hnd : IsNondegenerate g) (f : M → ℝ) (x : M) {v : TangentSpace I x}
    (hv : ∀ w, g x v w = mvfderiv I f x w) : v = gradAt hnd f x := by
  have h := hnd x (v - gradAt hnd f x) fun w => by
    rw [map_sub, ContinuousLinearMap.sub_apply, hv, g_gradAt, sub_self]
  exact sub_eq_zero.1 h

/-- The unit normal `grad f / |grad f|`. -/
def unitNormal (hnd : IsNondegenerate g) (f : M → ℝ) : Π x : M, TangentSpace I x :=
  fun x => (√(g x (gradAt hnd f x) (gradAt hnd f x)))⁻¹ • gradAt hnd f x

/-- **The second fundamental form** of the level set of `f` through `x`, with respect to the unit
normal `ν = grad f/|grad f|`: `B(v, w) = g(∇_v ν, w)`. -/
def sff (hnd : IsNondegenerate g) (f : M → ℝ) (x : M) (v w : TangentSpace I x) : ℝ :=
  g x (leviCivita g (unitNormal hnd f) x v) w

end SFF

/-! ## The Reiser–Wraith gluing theorem, as a hypothesis -/

theorem IsContMDiffMetricSection.of_le' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ} {m n : ℕ∞ω}
    (hg : IsContMDiffMetricSection E n g) (hmn : m ≤ n) : IsContMDiffMetricSection E m g :=
  ContMDiff.of_le hg hmn

theorem two_le_infty_ω : ((2 : ℕ∞) : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top

section RW

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (X : Type) [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]

/-- A **smooth** (`C^∞`) metric of positive sectional curvature on a manifold. -/
def HasPosCurvMetric : Prop :=
  ∃ (g : Π x : X, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (hs : IsSymm g)
    (hp : IsPosDef g) (hg : IsContMDiffMetricSection E ∞ g),
    ∀ (x : X) (u v : TangentSpace I x), LinearIndependent ℝ ![u, v] →
      0 < sectionalCurvatureAt hs hp (IsContMDiffMetricSection.of_le' hg two_le_infty_ω) x u v

/-- **Data of a Reiser–Wraith gluing** on a closed manifold `X`, cut along the regular level set
`Σ = f⁻¹(c)` into `X_N = {f ≤ c}` and `X_S = {f ≥ c}`. The metrics are defined on open
neighbourhoods `U_N ⊇ X_N` and `U_S ⊇ X_S`; they carry positive curvature on the closed pieces,
induce the same metric on `Σ`, and have second fundamental forms (outward normals) with
`B_N + B_S ≥ 0` on `TΣ`. -/
structure RWData where
  f : X → ℝ
  c : ℝ
  f_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f
  UN : TopologicalSpace.Opens X
  US : TopologicalSpace.Opens X
  subN : {x | f x ≤ c} ⊆ UN
  subS : {x | c ≤ f x} ⊆ US
  gN : Π x : UN, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ
  gS : Π x : US, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ
  sN : IsSymm gN
  sS : IsSymm gS
  pN : IsPosDef gN
  pS : IsPosDef gS
  hN : IsContMDiffMetricSection E ∞ gN
  hS : IsContMDiffMetricSection E ∞ gS
  /-- `Σ` is a regular level set. -/
  regular : ∀ x, f x = c → mvfderiv I f x ≠ 0
  /-- Positive curvature of `g_N` on `X_N`. -/
  posN : ∀ (x : UN), f x ≤ c → ∀ u v : TangentSpace I x, LinearIndependent ℝ ![u, v] →
    0 < sectionalCurvatureAt sN pN (IsContMDiffMetricSection.of_le' hN two_le_infty_ω) x u v
  /-- Positive curvature of `g_S` on `X_S`. -/
  posS : ∀ (x : US), c ≤ f x → ∀ u v : TangentSpace I x, LinearIndependent ℝ ![u, v] →
    0 < sectionalCurvatureAt sS pS (IsContMDiffMetricSection.of_le' hS two_le_infty_ω) x u v
  /-- The induced metrics on `Σ` agree (`φ = id`). -/
  bdry_metric : ∀ (x : X) (hx : f x = c) (v w : E), mvfderiv I f x v = 0 →
    mvfderiv I f x w = 0 →
    gN ⟨x, subN (le_of_eq hx)⟩ v w = gS ⟨x, subS (ge_of_eq hx)⟩ v w
  /-- `B_N + B_S ≥ 0` on `TΣ`, for the outward normals `grad f/|grad f|` of `X_N` and
  `grad(−f)/|grad(−f)|` of `X_S`. -/
  bdry_sff : ∀ (x : X) (hx : f x = c) (v : E), mvfderiv I f x v = 0 →
    0 ≤ sff pN.isNondegenerate (fun y : UN => f y) ⟨x, subN (le_of_eq hx)⟩ v v +
      sff pS.isNondegenerate (fun y : US => -f y) ⟨x, subS (ge_of_eq hx)⟩ v v

/-- **[GG] `prop:gluing` (Reiser–Wraith, Theorem A(i), `k = 1`)**, as a hypothesis on `X`:
every gluing datum yields a smooth metric of positive sectional curvature on `X`. -/
def RWGluing [CompactSpace X] : Prop := RWData I X → HasPosCurvMetric I X

end RW

end

end ExoticSpheres8And10
