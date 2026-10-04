/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import RiemannianGeometry.KoszulBundled
import RiemannianGeometry.CovariantDerivativeSmooth
import RiemannianGeometry.HomBundleComp
import RiemannianGeometry.HomBundleInverse
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Existence of the Levi-Civita connection

## The construction

Read the Koszul identity as a definition rather than a consequence. `RiemannianGeometry.KoszulBundled`
bundles the right-hand side into a field of bilinear forms `koszulSection g Y`, so the pointwise
formula

  `∇_· Y = ½ · (g x)⁻¹ ∘ koszulSection g Y x`

makes sense as a continuous linear map `T_xM →L[ℝ] T_xM`, and the whole content of this file is
that it satisfies the four things a Levi-Civita connection must.

## Main results

* `leviCivita` — the connection.
* `g_leviCivita_apply` — `g(∇_v Y, w) = ½ κ(v, Y, w)`, the defining property. Needs no
  differentiability: it is pure linear algebra given invertibility of `g x`.
* `isCovariantDerivativeOn_leviCivita` — it is a covariant derivative (additivity and Leibniz).
* `isCompatibleWith_leviCivita` — it is metric-compatible.
* `leviCivita_torsion_eq_zero` — it is torsion-free.
* `leviCivita_apply_add_direction`, `leviCivita_apply_smul_direction`, and — the substantive
  form — `koszulRHS_add_direction`, `koszulRHS_smul_direction`: linearity in the direction.
* `contMDiffAt_leviCivita` — it takes `C^(m+1)` sections to `C^m` sections.
* `mdiffAtCovSection_leviCivita` — the local regularity the curvature layer consumes, at the
  strength this construction can supply.
* `eq_leviCivita` — with `RiemannianGeometry.Koszul`'s uniqueness: **the fundamental theorem of
  (pseudo-)Riemannian geometry.** Only symmetry, nondegeneracy and differentiability of `g` are
  used, never positive-definiteness, so the theorem is pseudo-Riemannian in generality and the
  Riemannian case is the special case where `g` is positive-definite.

## Every property is derived from the specification, not from the definition

Deliberately. `leviCivita_spec` is proved once from the pointwise formula; after that the formula is
not used again. Additivity, Leibniz, torsion-freeness and metric compatibility are each
`leviCivita_spec` plus one identity for `κ` plus nondegeneracy, so a reader can check each against
the corresponding classical computation without re-deriving the inverse-metric bookkeeping.
Linearity in the direction is the one exception in kind: it holds *by the type*, since
`leviCivita g Y x` is a `ContinuousLinearMap`. That is not a shortcut but a consequence of
`tensorial_koszulRHS_direction`, which is what makes the bundled form exist at all, and the
substantive statements at the `κ` level are given alongside so the content is visible.

## The connection loses one derivative — and the curvature layer's hypothesis was repaired for it

`RiemannianGeometry.CurvaturePointwise` carries a local-regularity hypothesis on the connection. When this
construction was finished it read

  `CovLocalMDiffAt F cov x : ∀ s, (∀ᶠ y in 𝓝 x, MDiffAt (T% s) y) → MDiffAt (T% (cov s)) x`

— "sections differentiable near `x` go to `Hom`-sections differentiable at `x`" — and it could not
be discharged here. The reason was not a missing lemma: **no covariant derivative satisfies it.** A
connection is a first-order operator, `∇s = ds + Γ·s` in a trivialisation, so differentiability of
`∇s` at `x` forces `s` to be *twice* differentiable at `x`. Over `ℝ`, a section built from
`t ↦ t|t|` in a chart coordinate times a fixed nonzero fibre vector is a counterexample for every
`cov`, whenever the base has positive dimension and the fibre is nonzero.

`contMDiffAt_leviCivita` below is the general statement (`C^(m+1)` on an open set gives `C^m` at a
point); `mdiffAtCovSection_leviCivita` is its `m := 1` case, and
`RiemannianGeometry.RiemannCurvature.covC2LocalMDiffAt_leviCivita` packages that into the repaired
hypothesis, as a theorem.

-/

noncomputable section

open Bundle VectorField Set
open scoped RiemannianGeometry.ManifoldOrder
open scoped Manifold ContDiff Topology

namespace RiemannianGeometry

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {g : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
  {X Y Y' Z : Π x : M, TangentSpace I x} {f : M → ℝ} {x : M}

/-! ## The four algebraic identities -/

omit [FiniteDimensional ℝ E] in
/-- **Additivity in the differentiated slot.** `κ(X, Y + Y', Z) = κ(X,Y,Z) + κ(X,Y',Z)`. -/
theorem koszulRHS_add_section
    (hgd : ∀ {U W : Π z : M, TangentSpace I z}, MDiffAt (T% U) x → MDiffAt (T% W) x →
      MDiffAt (fun z ↦ g z (U z) (W z)) x)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hY' : MDiffAt (T% Y') x)
    (hZ : MDiffAt (T% Z) x) :
    koszulRHS g X (Y + Y') x Z = koszulRHS g X Y x Z + koszulRHS g X Y' x Z := by
  simp only [koszulRHS, Pi.add_apply, map_add,
    mvfderiv_fun_add (hgd hY hZ) (hgd hY' hZ),
    mvfderiv_fun_add (hgd hX hY) (hgd hX hY'),
    mlieBracket_add_right hY hY', mlieBracket_add_left hY hY', add_apply]
  ring

omit [FiniteDimensional ℝ E] in
/-- **Leibniz law in the differentiated slot.**
`κ(X, f•Y, Z) = f(x) κ(X,Y,Z) + 2 (Xf) g(Y,Z)`.

The factor `2` is what survives the `½` in the definition of `leviCivita` to become the
`(d% f x).smulRight (Y x)` term of Mathlib's `leibniz` field. One instance of symmetry of `g` is
used. -/
theorem koszulRHS_smul_section
    (hsymm : ∀ (y : M) (u v : TangentSpace I y), g y u v = g y v u)
    (hgd : ∀ {U W : Π z : M, TangentSpace I z}, MDiffAt (T% U) x → MDiffAt (T% W) x →
      MDiffAt (fun z ↦ g z (U z) (W z)) x)
    (hf : MDiffAt f x) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    koszulRHS g X (f • Y) x Z
      = f x * koszulRHS g X Y x Z + 2 * (d% f x (X x)) * g x (Y x) (Z x) := by
  simp only [koszulRHS, Pi.smul_apply', map_smul, smul_eq_mul,
    mvfderiv_fun_mul hf (hgd hY hZ), mvfderiv_fun_mul hf (hgd hX hY),
    mlieBracket_smul_right hf hY, mlieBracket_smul_left hf hY,
    map_add, add_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [hsymm x (X x) (Y x)]
  ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- **The torsion identity.** `κ(X,Y,Z) − κ(Y,X,Z) = 2 g([X,Y],Z)`.

Swapping `X` and `Y` fixes the three derivative terms up to symmetry of `g`, cancels the two
brackets involving `Z` outright, and doubles the `[X,Y]` term by antisymmetry — which is the whole
of torsion-freeness. No differentiability hypothesis: the symmetry rewrites act on the function
being differentiated, not through the derivative. -/
theorem koszulRHS_sub_swap (hsymm : ∀ (y : M) (u v : TangentSpace I y), g y u v = g y v u) :
    koszulRHS g X Y x Z - koszulRHS g Y X x Z = 2 * g x (mlieBracket I X Y x) (Z x) := by
  have eYZ : (fun y ↦ g y (Z y) (Y y)) = fun y ↦ g y (Y y) (Z y) :=
    funext fun y ↦ hsymm y (Z y) (Y y)
  have eZX : (fun y ↦ g y (X y) (Z y)) = fun y ↦ g y (Z y) (X y) :=
    funext fun y ↦ hsymm y (X y) (Z y)
  have eXY : (fun y ↦ g y (Y y) (X y)) = fun y ↦ g y (X y) (Y y) :=
    funext fun y ↦ hsymm y (Y y) (X y)
  simp only [koszulRHS]
  rw [eYZ, eZX, eXY,
    show mlieBracket I Y X x = - mlieBracket I X Y x from mlieBracket_swap_apply]
  simp only [map_neg, neg_apply]
  ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- **The compatibility identity.** `κ(X,Y,Z) + κ(X,Z,Y) = 2 X g(Y,Z)`.

Swapping the last two slots doubles the `X`-derivative term, cancels the `Y`- and `Z`-derivative
terms and the `[X,Y]`, `[X,Z]` brackets, and kills the last pair by antisymmetry. Antisymmetry is
used exactly once, on `[Y,Z]` against `[Z,Y]`. -/
theorem koszulRHS_add_swap_right
    (hsymm : ∀ (y : M) (u v : TangentSpace I y), g y u v = g y v u) :
    koszulRHS g X Y x Z + koszulRHS g X Z x Y
      = 2 * d% (fun y ↦ g y (Y y) (Z y)) x (X x) := by
  have eYZ : (fun y ↦ g y (Z y) (Y y)) = fun y ↦ g y (Y y) (Z y) :=
    funext fun y ↦ hsymm y (Z y) (Y y)
  have eZX : (fun y ↦ g y (X y) (Z y)) = fun y ↦ g y (Z y) (X y) :=
    funext fun y ↦ hsymm y (X y) (Z y)
  have eXY : (fun y ↦ g y (Y y) (X y)) = fun y ↦ g y (X y) (Y y) :=
    funext fun y ↦ hsymm y (Y y) (X y)
  simp only [koszulRHS]
  rw [eYZ, eZX, eXY,
    show mlieBracket I Z Y x = - mlieBracket I Y Z x from mlieBracket_swap_apply]
  simp only [map_neg, neg_apply]
  ring

/-! ## The connection -/

/-- **The Levi-Civita connection** of a metric supplied as data: read the Koszul identity as a
definition, `∇_· Y = ½ (g x)⁻¹ ∘ κ(·, Y, ·)`.

No hypothesis appears in the definition. Where `g x` is not invertible,
`ContinuousLinearMap.inverse` takes its junk value `0`; where the Koszul form is not tensorial,
`koszulSection` takes its junk value `0`. Every theorem below supplies what it needs. -/
def leviCivita (g : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (Y : Π x : M, TangentSpace I x) (x : M) : TangentSpace I x →L[ℝ] TangentSpace I x :=
  (2⁻¹ : ℝ) • ((ContinuousLinearMap.inverse (g x)) ∘L (koszulSection g Y x))

omit [CompleteSpace E] in
/-- **The defining property.** `g(∇_v Y, w) = ½ κ(v, Y, w)` for *all* `v` and `w`.

Pure linear algebra: no differentiability, and no tensoriality of the Koszul form is needed, since
the right-hand side is stated through `koszulSection` rather than through `koszulRHS`. -/
theorem g_leviCivita_apply (hinv : (g x).IsInvertible)
    (v w : TangentSpace I x) :
    g x (leviCivita g Y x v) w = 2⁻¹ * koszulSection g Y x v w := by
  simp only [leviCivita]
  rw [show ((2⁻¹ : ℝ) • ((ContinuousLinearMap.inverse (g x)) ∘L (koszulSection g Y x))) v
        = (2⁻¹ : ℝ) • (ContinuousLinearMap.inverse (g x)) (koszulSection g Y x v) from rfl,
    map_smul, hinv.self_apply_inverse]
  rfl

omit [CompleteSpace E] in
/-- The defining property in terms of `koszulRHS`, for differentiable sections. -/
theorem two_g_leviCivita_apply (hinv : (g x).IsInvertible) (hten : IsKoszulTensorialAt g Y x)
    (hX : MDiffAt (T% X) x) (hZ : MDiffAt (T% Z) x) :
    2 * g x (leviCivita g Y x (X x)) (Z x) = koszulRHS g X Y x Z := by
  rw [g_leviCivita_apply hinv, koszulSection_apply hten hX hZ]
  ring


/-! ## Nondegeneracy gives invertibility

So that the whole construction runs on the *same* hypothesis as the uniqueness theorem — weak
nondegeneracy — rather than on invertibility supplied separately. -/

/-! ## `∇0 = 0`
-/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- The Koszul right-hand side vanishes on the zero field, with no hypothesis: every derivative
term differentiates the zero function or is evaluated at the zero vector, and every bracket term
has a zero argument. -/
theorem koszulRHS_zero_section {g : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {X Z : Π x : M, TangentSpace I x} {x : M} :
    koszulRHS g X (0 : Π x : M, TangentSpace I x) x Z = 0 := by
  simp only [koszulRHS, Pi.zero_apply, map_zero, zero_apply,
    mlieBracket_zero_left, mlieBracket_zero_right, mvfderiv_const]
  simp

omit [CompleteSpace E] in
/-- The bundled Koszul form vanishes on the zero field. Both branches of the definition give `0`:
the junk branch outright, and the tensorial branch by `koszulRHS_zero_section` on the extensions of
arbitrary tangent vectors. -/
theorem koszulSection_zero_section
    {g : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ} {x : M} :
    koszulSection g (0 : Π x : M, TangentSpace I x) x = 0 := by
  by_cases h : IsKoszulTensorialAt g (0 : Π x : M, TangentSpace I x) x
  · ext v w
    rw [koszulSection_apply_extend h, koszulRHS_zero_section]
    simp
  · simp [koszulSection, h]

omit [CompleteSpace E] in
/-- **`∇0 = 0`**, with no symmetry, nondegeneracy or differentiability hypothesis — and not even
completeness of `E`: `leviCivita` is the inverse metric composed with `koszulSection`, the latter
already vanishes, and composing with `0` needs nothing of the inverse. -/
theorem leviCivita_zero_section
    {g : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ} {x : M} :
    leviCivita g (0 : Π x : M, TangentSpace I x) x = 0 := by
  simp [leviCivita, koszulSection_zero_section]

section Nondegeneracy

/-- `g x`, viewed as a continuous linear equivalence `T_xM ≃L (T_xM →L ℝ)`, from weak
nondegeneracy alone.

Three instances have to be supplied by hand — `FiniteDimensional`, `T2Space` and the finite-rank
continuity of a linear map — exactly the manoeuvre `TensorialAt.mkHom` makes internally. Note the
hypothesis is precisely `LinearMap.SeparatingLeft` for the associated bilinear form, which is
literally the nondegeneracy already assumed by `eq_of_isCompatible_of_torsion_eq_zero`: nothing has
to be strengthened, and positive-definiteness is not needed. -/
def gDual (hnd : ∀ v : TangentSpace I x, (∀ w, g x v w = 0) → v = 0) :
    TangentSpace I x ≃L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  have _ : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
  have _ : T2Space (TangentSpace I x) := FiberBundle.t2Space E (TangentSpace I) x
  let B : LinearMap.BilinForm ℝ (TangentSpace I x) := (g x).toBilinForm
  have hsl : B.SeparatingLeft := fun v hv ↦ hnd v (fun w ↦ hv w)
  have hnB : B.Nondegenerate := LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft hsl
  ((LinearMap.BilinForm.toDual B hnB).trans
      (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := TangentSpace I x) (F' := ℝ)))
    |>.toContinuousLinearEquiv

omit [CompleteSpace E] in
theorem gDual_apply (hnd : ∀ v : TangentSpace I x, (∀ w, g x v w = 0) → v = 0)
    (v w : TangentSpace I x) : gDual hnd v w = g x v w := by
  simp [gDual, LinearMap.BilinForm.toDual_def]

omit [CompleteSpace E] in
/-- `gDual`, as a continuous linear map, **is** `g x`: the equivalence structure is only the
assertion that `g x` is bijective, which is the sole reason `BilinForm.toDual` appears at all. -/
theorem gDual_toCLM (hnd : ∀ v : TangentSpace I x, (∀ w, g x v w = 0) → v = 0) :
    ((gDual hnd : TangentSpace I x ≃L[ℝ] (TangentSpace I x →L[ℝ] ℝ)) :
      TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)) = g x := by
  ext v w
  exact gDual_apply hnd v w

omit [CompleteSpace E] in
/-- **Weak nondegeneracy gives invertibility.** -/
theorem isInvertible_g (hnd : ∀ v : TangentSpace I x, (∀ w, g x v w = 0) → v = 0) :
    (g x).IsInvertible := by
  rw [← gDual_toCLM hnd]
  exact ⟨gDual hnd, rfl⟩

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- Nondegeneracy in the form in which it is used: `g` separates points of `T_xM`. -/
theorem eq_of_g_eq (hnd : ∀ v : TangentSpace I x, (∀ w, g x v w = 0) → v = 0)
    {a b : TangentSpace I x} (h : ∀ w, g x a w = g x b w) : a = b := by
  refine sub_eq_zero.mp (hnd (a - b) fun w ↦ ?_)
  rw [map_sub, sub_apply, h w, sub_self]

end Nondegeneracy

/-- `g`, as data, differentiable at every point as a section of `Hom(TM, Hom(TM, ℝ))`.

The differentiability form of `IsContMDiffMetricSection`. Every binder is explicit because an
implicit model fibre leaves `VectorBundle ℝ ?F _` unresolved at each use site. -/
def IsMDiffMetric (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) : Prop :=
  ∀ y : M, MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ))
    (fun z ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun (z : M) ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ) z (g z)) y

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The bridge between the two metric-regularity notions in this development: from the `C^n`
section of `RiemannianGeometry.KoszulRegularity` to the differentiable section this file consumes.

Stated for any `n ≠ 0` and for an explicit `g`, because callers arrive at every order.
`RiemannianGeometry.RiemannSymmetries` has a section-variable specialisation of the same fact, fixed at
that file's `C²` hypothesis. -/
theorem IsContMDiffMetricSection.isMDiffMetric {n : ℕ∞ω} (hn : n ≠ 0)
    {g : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    (hg : IsContMDiffMetricSection E n g) : IsMDiffMetric E g :=
  fun y ↦ (hg y).mdifferentiableAt hn

/-- Nondegeneracy at every point, in the weak form. -/
def IsNondegenerate {H : Type*} [TopologicalSpace H] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) : Prop :=
  ∀ (y : M) (v : TangentSpace I y), (∀ w, g y v w = 0) → v = 0

/-- Symmetry at every point. -/
def IsSymm {H : Type*} [TopologicalSpace H] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) : Prop :=
  ∀ (y : M) (u v : TangentSpace I y), g y u v = g y v u

/-! ## The canonical specification theorem -/

/-- **The specification theorem for the constructed connection.**

  `g(∇_X Y, Z) = ½ κ(X, Y, Z)`

This is the canonical characterisation: every property of `leviCivita` below is derived from it
together with an identity for `κ`, and **not** from the pointwise definition. Compare
`two_apply_cov_eq_koszulRHS`, which is the same equation read as a *consequence* for an arbitrary
torsion-free compatible connection; here it is the *definition* discharged. -/
theorem leviCivita_spec (hsymm : IsSymm g) (hnd : IsNondegenerate g) (hgm : IsMDiffMetric E g)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    g x (leviCivita g Y x (X x)) (Z x) = (1 / 2 : ℝ) * koszulRHS g X Y x Z := by
  rw [g_leviCivita_apply (isInvertible_g (hnd x)),
    koszulSection_apply (isKoszulTensorialAt_of_mdifferentiableAt hsymm (hgm x) hY) hX hZ]
  ring

/-- The specification theorem on *arbitrary* tangent vectors, through `FiberBundle.extend`. This is
the form used to derive the identities below, since it quantifies over all of `T_xM`. -/
theorem leviCivita_spec_extend (hsymm : IsSymm g) (hnd : IsNondegenerate g)
    (hgm : IsMDiffMetric E g)
    (hY : MDiffAt (T% Y) x) (v w : TangentSpace I x) :
    g x (leviCivita g Y x v) w
      = (1 / 2 : ℝ) * koszulRHS g (FiberBundle.extend E v) Y x (FiberBundle.extend E w) := by
  rw [g_leviCivita_apply (isInvertible_g (hnd x)),
    koszulSection_apply_extend (isKoszulTensorialAt_of_mdifferentiableAt hsymm (hgm x) hY) v w]
  ring

/-! ## Additivity and Leibniz in the differentiated slot

Each is derived from the specification theorem plus the corresponding identity for `κ`, and then
nondegeneracy. Neither is read off the pointwise definition. -/

/-- **Additivity.** `∇(Y + Y') = ∇Y + ∇Y'`. -/
theorem leviCivita_add_section (hsymm : IsSymm g) (hnd : IsNondegenerate g)
    (hgm : IsMDiffMetric E g) (hY : MDiffAt (T% Y) x) (hY' : MDiffAt (T% Y') x) :
    leviCivita g (Y + Y') x = leviCivita g Y x + leviCivita g Y' x := by
  ext v
  refine eq_of_g_eq (hnd x) fun w ↦ ?_
  have h1 := leviCivita_spec_extend hsymm hnd hgm (mdifferentiableAt_add_section hY hY') v w
  have h2 := leviCivita_spec_extend hsymm hnd hgm hY v w
  have h3 := leviCivita_spec_extend hsymm hnd hgm hY' v w
  have h4 := koszulRHS_add_section (g := g) (mdiffAt_pairing (hgm x))
    (FiberBundle.mdifferentiableAt_extend I E v) hY hY'
    (FiberBundle.mdifferentiableAt_extend I E w)
  have h5 : g x ((leviCivita g Y x + leviCivita g Y' x) v) w
      = g x (leviCivita g Y x v) w + g x (leviCivita g Y' x v) w := by simp
  rw [h5]
  linarith

/-- **The Leibniz rule.** `∇(f • Y) = f • ∇Y + df ⊗ Y`, in Mathlib's exact field shape.

The factor `2` of `koszulRHS_smul_section` is what the `½` of the definition turns into the single
`(d% f x).smulRight (Y x)` term. -/
theorem leviCivita_smul_section (hsymm : IsSymm g) (hnd : IsNondegenerate g)
    (hgm : IsMDiffMetric E g) (hf : MDiffAt f x) (hY : MDiffAt (T% Y) x) :
    leviCivita g (f • Y) x = f x • leviCivita g Y x + (d% f x).smulRight (Y x) := by
  ext v
  refine eq_of_g_eq (hnd x) fun w ↦ ?_
  have h1 := leviCivita_spec_extend hsymm hnd hgm (MDifferentiableAt.smul_section hf hY) v w
  have h2 := koszulRHS_smul_section hsymm (mdiffAt_pairing (hgm x)) hf
    (FiberBundle.mdifferentiableAt_extend I E v) hY
    (FiberBundle.mdifferentiableAt_extend I E w)
  have h3 := leviCivita_spec_extend hsymm hnd hgm hY v w
  have h4 : g x ((f x • leviCivita g Y x + (d% f x).smulRight (Y x)) v) w
      = f x * g x (leviCivita g Y x v) w + (d% f x v) * g x (Y x) w := by
    simp [ContinuousLinearMap.smulRight_apply]
  rw [h4, h1, h2, h3]
  simp only [FiberBundle.extend_apply_self]
  ring

/-- **`leviCivita` is a covariant derivative.** -/
theorem isCovariantDerivativeOn_leviCivita (hsymm : IsSymm g) (hnd : IsNondegenerate g)
    (hgm : IsMDiffMetric E g) :
    IsCovariantDerivativeOn E (leviCivita g) univ where
  add hY hY' _ := leviCivita_add_section hsymm hnd hgm hY hY'
  leibniz hY hf _ := leviCivita_smul_section hsymm hnd hgm hf hY

/-! ## Linearity in the direction

`leviCivita g Y x` is a `ContinuousLinearMap` by construction, so linearity in the direction is
immediate *at the level of the connection*. The content is one level down: that the Koszul
right-hand side is **tensorial** in its direction slot, which is what allows the bundled form to
exist at all. Both levels are stated, so that the substantive one is visible and not hidden behind
the type. -/

omit [FiniteDimensional ℝ E] in
/-- Additivity of `κ` in the direction slot — the substantive form of direction-linearity. -/
theorem koszulRHS_add_direction (hsymm : IsSymm g)
    (hgd : ∀ {U W : Π z : M, TangentSpace I z}, MDiffAt (T% U) x → MDiffAt (T% W) x →
      MDiffAt (fun z ↦ g z (U z) (W z)) x)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x)
    {X X' : Π z : M, TangentSpace I z} (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x) :
    koszulRHS g (X + X') Y x Z = koszulRHS g X Y x Z + koszulRHS g X' Y x Z :=
  (tensorial_koszulRHS_direction hsymm hgd hY hZ).add hX hX'

omit [FiniteDimensional ℝ E] in
/-- Homogeneity of `κ` in the direction slot. -/
theorem koszulRHS_smul_direction (hsymm : IsSymm g)
    (hgd : ∀ {U W : Π z : M, TangentSpace I z}, MDiffAt (T% U) x → MDiffAt (T% W) x →
      MDiffAt (fun z ↦ g z (U z) (W z)) x)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x)
    {X : Π z : M, TangentSpace I z} (hf : MDiffAt f x) (hX : MDiffAt (T% X) x) :
    koszulRHS g (f • X) Y x Z = f x • koszulRHS g X Y x Z :=
  (tensorial_koszulRHS_direction hsymm hgd hY hZ).smul hf hX

omit [CompleteSpace E] in
/-- Direction-linearity at the level of the connection: `∇_· Y` really is additive in the
direction, and its value at `X x` depends on `X` only through `X x`. -/
theorem leviCivita_apply_add_direction (v v' : TangentSpace I x) :
    leviCivita g Y x (v + v') = leviCivita g Y x v + leviCivita g Y x v' :=
  map_add _ _ _

omit [CompleteSpace E] in
theorem leviCivita_apply_smul_direction (c : ℝ) (v : TangentSpace I x) :
    leviCivita g Y x (c • v) = c • leviCivita g Y x v :=
  map_smul _ _ _

/-! ## Torsion-freeness -/

/-- `∇_X Y − ∇_Y X = [X, Y]`, from `koszulRHS_sub_swap`. -/
theorem leviCivita_sub_swap (hsymm : IsSymm g) (hnd : IsNondegenerate g) (hgm : IsMDiffMetric E g)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    leviCivita g Y x (X x) - leviCivita g X x (Y x) = mlieBracket I X Y x := by
  refine eq_of_g_eq (hnd x) fun w ↦ ?_
  have hw := FiberBundle.mdifferentiableAt_extend I E w
  have e : (FiberBundle.extend E w) x = w := FiberBundle.extend_apply_self E w
  rw [map_sub, sub_apply]
  rw [show g x (leviCivita g Y x (X x)) w
        = g x (leviCivita g Y x (X x)) ((FiberBundle.extend E w) x) by rw [e],
    show g x (leviCivita g X x (Y x)) w
        = g x (leviCivita g X x (Y x)) ((FiberBundle.extend E w) x) by rw [e],
    show g x (mlieBracket I X Y x) w
        = g x (mlieBracket I X Y x) ((FiberBundle.extend E w) x) by rw [e],
    leviCivita_spec hsymm hnd hgm hX hY hw, leviCivita_spec hsymm hnd hgm hY hX hw]
  have := koszulRHS_sub_swap (g := g) (X := X) (Y := Y) (x := x)
    (Z := FiberBundle.extend E w) hsymm
  linarith

/-- **`leviCivita` is torsion-free.** -/
theorem leviCivita_torsion_eq_zero (hsymm : IsSymm g) (hnd : IsNondegenerate g)
    (hgm : IsMDiffMetric E g) :
    (isCovariantDerivativeOn_leviCivita hsymm hnd hgm).torsion = 0 := by
  funext y
  ext u v
  have hu := FiberBundle.mdifferentiableAt_extend I E u
  have hv := FiberBundle.mdifferentiableAt_extend I E v
  have h := IsCovariantDerivativeOn.torsion_apply
    (isCovariantDerivativeOn_leviCivita hsymm hnd hgm) hu hv
  have hswap := leviCivita_sub_swap hsymm hnd hgm hu hv
  rw [FiberBundle.extend_apply_self, FiberBundle.extend_apply_self] at h hswap
  rw [h, hswap, sub_self]
  simp

/-! ## Metric compatibility -/

/-- **`leviCivita` is compatible with `g`.** `X g(Y,Z) = g(∇_X Y, Z) + g(Y, ∇_X Z)`. -/
theorem isCompatibleWith_leviCivita (hsymm : IsSymm g) (hnd : IsNondegenerate g)
    (hgm : IsMDiffMetric E g) :
    IsCompatibleWith (leviCivita g) g := by
  intro X Y Z y hY hZ
  have hX' : MDiffAt (T% (FiberBundle.extend E (X y))) y :=
    FiberBundle.mdifferentiableAt_extend I E (X y)
  have hval : (FiberBundle.extend E (X y)) y = X y := FiberBundle.extend_apply_self E (X y)
  have h1 := leviCivita_spec hsymm hnd hgm hX' hY hZ
  have h2 := leviCivita_spec hsymm hnd hgm hX' hZ hY
  have h3 := koszulRHS_add_swap_right (g := g) (X := FiberBundle.extend E (X y))
    (Y := Y) (Z := Z) (x := y) hsymm
  rw [hval] at h1 h2 h3
  rw [hsymm y (Y y) (leviCivita g Z y (X y))]
  linarith

/-! ## Smoothness -/

/-- **The connection is as smooth as the data allows.**

With the metric-as-data and `Y` of class `C^(m+1)` on an open `u ∋ x`, the section `∇Y` of
`Hom(TM, TM)` is `C^m` at `x`. This is the property `ContMDiffCovariantDerivativeOn` demands, and
the one order lost is intrinsic: the Koszul formula differentiates the metric and the section once.
-/
theorem contMDiffAt_leviCivita {m : ℕ∞} {u : Set M} (hu : IsOpen u) (hxu : x ∈ u)
    (hsymm : IsSymm g) (hnd : IsNondegenerate g)
    (hg : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ((m + 1 : ℕ∞))
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun (y : M) ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) y (g y)) u)
    (hY : CMDiff[u] ((m + 1 : ℕ∞)) (T% Y)) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ((m : ℕ∞ω))
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M ↦ (TangentSpace I y →L[ℝ] TangentSpace I y)) y (leviCivita g Y y)) x := by
  have hml : ((m : ℕ∞ω)) ≤ ((m + 1 : ℕ∞) : ℕ∞ω) := by push_cast; exact le_self_add
  have hgx : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ((m : ℕ∞ω))
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ (TangentSpace I y →L[ℝ] (TangentSpace I y →L[ℝ] Bundle.Trivial M ℝ y)))
        y (g y)) x := ((hg x hxu).contMDiffAt (hu.mem_nhds hxu)).of_le hml
  exact ContMDiffAt.const_smul_section
    ((hgx.clm_bundle_inverse (isInvertible_g (hnd x))).clm_bundle_comp
      (contMDiffAt_koszulSection hu hxu hsymm hg hY))

/--
This is the `m := 1` case of `contMDiffAt_leviCivita`, and it is what
`RiemannianGeometry.RiemannCurvature.covC2LocalMDiffAt_leviCivita` turns into the curvature layer's
`CovC2LocalMDiffAt` hypothesis. See the module docstring for why that hypothesis had to be repaired
before it could be discharged at all. -/
theorem mdiffAtCovSection_leviCivita {u : Set M} (hu : IsOpen u) (hxu : x ∈ u)
    (hsymm : IsSymm g) (hnd : IsNondegenerate g)
    (hg : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ((2 : ℕ∞))
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun (y : M) ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) y (g y)) u)
    (hY : CMDiff[u] ((2 : ℕ∞)) (T% Y)) :
    MDiffAtCovSection E (leviCivita g) Y x :=
  (contMDiffAt_leviCivita (m := 1) hu hxu hsymm hnd hg hY).mdifferentiableAt (by simp)

/-! ## The fundamental theorem of Riemannian geometry -/

/-- **The fundamental theorem.** A torsion-free connection compatible with a symmetric
nondegenerate metric-as-data *is* `leviCivita g`.
-/
theorem eq_leviCivita (hsymm : IsSymm g) (hnd : IsNondegenerate g) (hgm : IsMDiffMetric E g)
    {cov : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)}
    (hcov : IsCovariantDerivativeOn E cov univ) (hmc : IsCompatibleWith cov g)
    (htf : hcov.torsion = 0) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    cov Y x (X x) = leviCivita g Y x (X x) :=
  eq_of_isCompatible_of_torsion_eq_zero hcov (isCovariantDerivativeOn_leviCivita hsymm hnd hgm)
    hsymm hnd hmc (isCompatibleWith_leviCivita hsymm hnd hgm) htf
    (leviCivita_torsion_eq_zero hsymm hnd hgm) hX hY

end RiemannianGeometry

