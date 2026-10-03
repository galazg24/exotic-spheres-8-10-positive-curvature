/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import RiemannianGeometry.Koszul
import RiemannianGeometry.MLieBracketDerivation

/-!
# Regularity of the Koszul form

## Main results

* `koszulRHS` — the six-term right-hand side of the Koszul identity, named.
* `two_apply_cov_eq_koszulRHS` — the Koszul identity, restated through that name, so that
  `koszulRHS` is an abbreviation and not a second source of truth.
* `contMDiff_koszulRHS` — all six terms are `C^m` when the data is `C^(m+1)`.

## What is deliberately *not* here

## Two conventions that decide everything

* the direction is the **last** argument: `cov Y x (X x)` is `(∇_X Y)(x)`;
* one order of differentiability is genuinely lost. `d% f y (Y y)` differentiates `f`, so the
  hypotheses are at `m + 1` and the conclusion at `m`. That is not slack: it is why
  `ContMDiffCovariantDerivativeOn` takes `C^(k+1)` sections in.

## Localisation

The results are stated at a point of an open set (`contMDiffAt_koszulRHS`), with the global forms as
corollaries on `univ`. The local form is what the eventual construction needs, since the vector
fields it feeds in are `FiberBundle.extend` sections and a trivialisation's local frame, smooth only
on a trivialisation base set.

An earlier draft of this file recorded the localisation as blocked, on the grounds that
`ContMDiffOn.mlieBracketWithin_vectorField` produces `mlieBracketWithin` rather than `mlieBracket`.
That was wrong: `ContMDiffAt.mlieBracket_vectorField` is already stated at a point, so the bracket
terms need no set at all, and only the three derivative terms — which go through
`contMDiffAt_mvfderiv_apply_of_contMDiffOn` — need `u` to be open.

-/

noncomputable section

open Bundle VectorField Set
open scoped Manifold ContDiff Topology

namespace RiemannianGeometry

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {g : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
  {X Y Z : Π x : M, TangentSpace I x}

/-- A metric supplied as **data** being a `C^n` section of `Hom(TM, Hom(TM, ℝ))`.

This is the data-form analogue of `IsContMDiffRiemannianBundle`. It is stated as a separate
definition only to keep the hypothesis legible; every binder is explicit because an implicit model
fibre leaves `VectorBundle ℝ ?F _` unresolved at each use site. -/
def IsContMDiffMetricSection (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (n : ℕ∞ω) (g : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) : Prop :=
  ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n
    (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun (y : M) ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) y (g y))

/-- **The pairing is as smooth as its inputs**, at a point.

`y ↦ g y (X y) (Y y)` is `C^n` at `x` when `g`, `X` and `Y` are. Mathlib's
`ContMDiffAt.inner_bundle` says this for `⟪·,·⟫` under a `RiemannianBundle` instance; the metric
here is data, so the proof goes through `ContMDiffAt.clm_bundle_apply₂` directly — the same route
Mathlib takes internally, with the target read as the trivial line bundle and the section's fibre
component extracted. -/
theorem contMDiffAt_pairing {n : ℕ∞ω} {x : M}
    (hg : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun (y : M) ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) y (g y)) x)
    (hX : CMDiffAt n (T% X) x) (hY : CMDiffAt n (T% Y) x) :
    ContMDiffAt I 𝓘(ℝ) n (fun y ↦ g y (X y) (Y y)) x := by
  have h : ContMDiffAt I (I.prod 𝓘(ℝ, ℝ)) n
      (fun z ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) z (g z (X z) (Y z))) x :=
    ContMDiffAt.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ) hg hX hY
  simp only [Bundle.contMDiffAt_totalSpace] at h
  exact h.2

/-- The pairing is as smooth as its inputs, on a set. -/
theorem contMDiffOn_pairing {n : ℕ∞ω} {u : Set M}
    (hg : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun (y : M) ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) y (g y)) u)
    (hX : CMDiff[u] n (T% X)) (hY : CMDiff[u] n (T% Y)) :
    ContMDiffOn I 𝓘(ℝ) n (fun y ↦ g y (X y) (Y y)) u := by
  intro y hy
  have h : ContMDiffWithinAt I (I.prod 𝓘(ℝ, ℝ)) n
      (fun z ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) z (g z (X z) (Y z))) u y :=
    ContMDiffWithinAt.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ) (hg y hy) (hX y hy) (hY y hy)
  simp only [Bundle.contMDiffWithinAt_totalSpace] at h
  exact h.2

/-- The pairing is as smooth as its inputs, globally. -/
theorem contMDiff_pairing {n : ℕ∞ω} (hg : IsContMDiffMetricSection E n g)
    (hX : ContMDiff I I.tangent n (T% X)) (hY : ContMDiff I I.tangent n (T% Y)) :
    ContMDiff I 𝓘(ℝ) n (fun y ↦ g y (X y) (Y y)) :=
  fun y ↦ contMDiffAt_pairing (hg y) (hX y) (hY y)

/-- **The Koszul right-hand side, named.**
-/
def koszulRHS (g : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (X Y : Π x : M, TangentSpace I x) (x : M) : (Π x : M, TangentSpace I x) → ℝ :=
  fun Z ↦
        d% (fun y ↦ g y (Y y) (Z y)) x (X x)
      + d% (fun y ↦ g y (Z y) (X y)) x (Y x)
      - d% (fun y ↦ g y (X y) (Y y)) x (Z x)
      + g x (mlieBracket I X Y x) (Z x)
      - g x (mlieBracket I X Z x) (Y x)
      - g x (mlieBracket I Y Z x) (X x)

section Identity

variable [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M]
  {cov : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)} {x : M}

/-- The Koszul identity of `two_apply_cov_eq_koszul`, restated through `koszulRHS`.

Stated so that `koszulRHS` is an *abbreviation* for the right-hand side rather than an independent
definition that could drift away from it. -/
theorem two_apply_cov_eq_koszulRHS (hcov : IsCovariantDerivativeOn E cov univ)
    (hsymm : ∀ (x : M) (u v : TangentSpace I x), g x u v = g x v u)
    (hmc : IsCompatibleWith cov g) (htf : hcov.torsion = 0)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    2 * g x (cov Y x (X x)) (Z x) = koszulRHS g X Y x Z :=
  two_apply_cov_eq_koszul hcov hsymm hmc htf hX hY hZ

end Identity

section Regularity

variable {m : ℕ∞} [CompleteSpace E]
  [IsManifold I (minSmoothness ℝ 2) M] [IsManifold I (((m + 1 : ℕ∞) : ℕ∞ω) + 1) M]

/-- **Regularity of the Koszul right-hand side**, at a point of an open set.

The local form is the one the construction needs, because the vector fields it feeds in are
`FiberBundle.extend` sections and a trivialisation's local frame, which are smooth only on a
trivialisation base set. Only the three derivative terms need the set at all — the brackets are
handled pointwise, since Mathlib's `ContMDiffAt.mlieBracket_vectorField` is already stated at a
point.

The three ingredients are exactly one apiece:

* the derivative terms — `contMDiffAt_mvfderiv_apply_of_contMDiffOn`, which needs its function
  `C^(m+1)` on an open set and costs the one order of differentiability;
* the bracket terms — Mathlib's `ContMDiffAt.mlieBracket_vectorField`, which costs the same order,
  and whose `minSmoothness ℝ (m+1) ≤ m + 1` side condition is an equality over `ℝ`;
* the pairings — `contMDiffAt_pairing` and `contMDiffOn_pairing` above.

Both `IsManifold` instances are inherited from Mathlib's bracket lemma, which carries
`[IsManifold I (minSmoothness 𝕜 2) M]` ambiently and `[IsManifold I (n + 1) M]` on the statement,
here with `n := m + 1`. The second must be written in exactly that shape —
`(((m + 1 : ℕ∞) : ℕ∞ω) + 1)`, not `((m : ℕ∞) + 1 + 1)` — since instance search matches
syntactically and the two coercions differ. `CompleteSpace E` comes from the same place. -/
theorem contMDiffAt_koszulRHS {u : Set M} {x : M} (hu : IsOpen u) (hxu : x ∈ u)
    (hg : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ((m + 1 : ℕ∞))
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun (y : M) ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) y (g y)) u)
    (hX : CMDiff[u] ((m + 1 : ℕ∞)) (T% X))
    (hY : CMDiff[u] ((m + 1 : ℕ∞)) (T% Y))
    (hZ : CMDiff[u] ((m + 1 : ℕ∞)) (T% Z)) :
    ContMDiffAt I 𝓘(ℝ) ((m : ℕ∞ω)) (fun y ↦ koszulRHS g X Y y Z) x := by
  have hmn : ((m : ℕ∞ω)) + 1 ≤ ((m + 1 : ℕ∞) : ℕ∞ω) := by push_cast; exact le_refl _
  have hml : ((m : ℕ∞ω)) ≤ ((m + 1 : ℕ∞) : ℕ∞ω) := by push_cast; exact le_self_add
  have hmin : minSmoothness ℝ ((m : ℕ∞) + 1) ≤ (m + 1 : ℕ∞) := by simp
  have hux : u ∈ 𝓝 x := hu.mem_nhds hxu
  -- the three pairings, at order `m + 1`, on `u`
  have p1 := contMDiffOn_pairing hg hY hZ
  have p2 := contMDiffOn_pairing hg hZ hX
  have p3 := contMDiffOn_pairing hg hX hY
  -- the data, pointwise at `x`
  have hgx := (hg x hxu).contMDiffAt hux
  have hXx := (hX x hxu).contMDiffAt hux
  have hYx := (hY x hxu).contMDiffAt hux
  have hZx := (hZ x hxu).contMDiffAt hux
  -- the three brackets, at order `m`
  have b1 : CMDiffAt ((m : ℕ∞ω)) (T% (mlieBracket I X Y)) x :=
    hXx.mlieBracket_vectorField hYx hmin
  have b2 : CMDiffAt ((m : ℕ∞ω)) (T% (mlieBracket I X Z)) x :=
    hXx.mlieBracket_vectorField hZx hmin
  have b3 : CMDiffAt ((m : ℕ∞ω)) (T% (mlieBracket I Y Z)) x :=
    hYx.mlieBracket_vectorField hZx hmin
  refine ContMDiffAt.sub (ContMDiffAt.sub (ContMDiffAt.add (ContMDiffAt.sub
    (ContMDiffAt.add ?_ ?_) ?_) ?_) ?_) ?_
  · exact contMDiffAt_mvfderiv_apply_of_contMDiffOn hu hxu p1 hmn (hXx.of_le hml)
  · exact contMDiffAt_mvfderiv_apply_of_contMDiffOn hu hxu p2 hmn (hYx.of_le hml)
  · exact contMDiffAt_mvfderiv_apply_of_contMDiffOn hu hxu p3 hmn (hZx.of_le hml)
  · exact contMDiffAt_pairing (hgx.of_le hml) b1 (hZx.of_le hml)
  · exact contMDiffAt_pairing (hgx.of_le hml) b2 (hYx.of_le hml)
  · exact contMDiffAt_pairing (hgx.of_le hml) b3 (hXx.of_le hml)

/-- The global form of `contMDiffAt_koszulRHS`, taken on `univ`. -/
theorem contMDiff_koszulRHS
    (hg : IsContMDiffMetricSection E ((m + 1 : ℕ∞)) g)
    (hX : ContMDiff I I.tangent ((m + 1 : ℕ∞)) (T% X))
    (hY : ContMDiff I I.tangent ((m + 1 : ℕ∞)) (T% Y))
    (hZ : ContMDiff I I.tangent ((m + 1 : ℕ∞)) (T% Z)) :
    ContMDiff I 𝓘(ℝ) ((m : ℕ∞ω)) (fun y ↦ koszulRHS g X Y y Z) := fun y ↦
  contMDiffAt_koszulRHS isOpen_univ (mem_univ y)
    (ContMDiff.contMDiffOn hg) hX.contMDiffOn hY.contMDiffOn hZ.contMDiffOn

end Regularity

end RiemannianGeometry
