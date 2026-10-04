/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import RiemannianGeometry.CurvaturePointwise
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion

/-!
# The first Bianchi identity

For a **torsion-free** connection on the tangent bundle,

  `R(X,Y)Z + R(Y,Z)X + R(Z,X)Y = 0`.

Stated at that level of generality — no metric, no Levi-Civita, no positive definiteness — because
that is where the identity lives. The Levi-Civita case is a specialisation.

## Main results

* `IsTorsionFreePointwise` — torsion-freeness in the form the proof consumes, with
  `isTorsionFreePointwise_of_torsion_eq_zero` as the bridge from Mathlib's `hcov.torsion = 0`.
* `bianchi_group` — one cyclic group: `∇_U∇_P Q − ∇_U∇_Q P − ∇_{[P,Q]}U = [U, [P,Q]]`.
* `curvature_cyclic_eq_zero` — the identity, at general order.
* `curvature_cyclic_eq_zero_two` — its `C²` form over `ℝ` or `ℂ`.

## Proof architecture

Two mechanisms, each used three times. **Torsion-freeness twice per cyclic group**: first as an
identity of *sections* near `x` (`∇_P Q =ᶠ ∇_Q P + [P,Q]`, pushed through
`IsCovariantDerivativeOn.congr_of_eventuallyEq` and split by additivity), then pointwise to turn
`∇_U[P,Q] − ∇_{[P,Q]}U` into `[U,[P,Q]]`. That leaves the cyclic sum equal to
`[X,[Y,Z]] + [Y,[Z,X]] + [Z,[X,Y]]`, which **Jacobi** telescopes to zero from Mathlib's Leibniz
form `[U,[V,W]] = [[U,V],W] + [V,[U,W]]`.

Only the outer bracket swap `[Z,[X,Y]] = −[[X,Y],Z]` is unconditional
(`mlieBracket_swap_apply`). The inner one, `[Y,[Z,X]] = −[Y,[X,Z]]`, is right-slot antilinearity
and needs differentiability of both inner brackets — obtained from `mlieBracket_add_right` together
with `mlieBracket_zero_right`.

## Regularity: `C²` on the fields, `C³` on the *manifold*

The base manifold, however, must be `C³`. That is forced twice over by Mathlib and not by the
connection: `ContMDiffAt.mlieBracket_vectorField` at `m := 1, n := 2` needs `[IsManifold I 3 M]`,
and `leibniz_identity_mlieBracket_apply` sits in a section with
`[IsManifold I (minSmoothness 𝕜 3) M] [CompleteSpace E]`. Recorded explicitly because it is easy to
misreport as a `C³` requirement on the geometry: it is a requirement on the *charts*. Downstream,
where `[IsManifold I ∞ M]` is assumed as usual, it costs nothing.

One further generality point. `minSmoothness 𝕜 2 = 2` only over an `IsRCLikeNormedField`; over other
fields it is `ω`. So the general statement carries `{n : ℕ∞}` with `hn : minSmoothness 𝕜 2 ≤ n`, the
idiom already used in `RiemannianGeometry.CurvaturePointwise`, and the literal `C²` version is the
`n = 2` corollary over `ℝ` and `ℂ`. Keeping torsion-freeness as `IsTorsionFreePointwise` rather than
`hcov.torsion = 0` also keeps `CompleteSpace 𝕜` and `FiniteDimensional 𝕜 E` off the main theorem —
`IsCovariantDerivativeOn.torsion` needs them merely to exist.
-/

noncomputable section

open Bundle Set VectorField Filter
open scoped Manifold ContDiff Topology

namespace RiemannianGeometry

section Bianchi

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞} [IsManifold I 1 M] [IsManifold I (n + 1) M]
  {cov : (Π y : M, TangentSpace I y) → (Π y : M, TangentSpace I y →L[𝕜] TangentSpace I y)}
  {X Y Z : Π y : M, TangentSpace I y} {x : M}

/-- Torsion-freeness of a connection on `TM`, in pointwise form:
`∇_U W - ∇_W U = [U, W]` for vector fields differentiable at the point. -/
def IsTorsionFreePointwise
    (cov : (Π y : M, TangentSpace I y) → (Π y : M, TangentSpace I y →L[𝕜] TangentSpace I y)) :
    Prop :=
  ∀ (U W : Π y : M, TangentSpace I y) (y : M), MDiffAt (T% U) y → MDiffAt (T% W) y →
    cov W y (U y) - cov U y (W y) = mlieBracket I U W y

/-- `hcov.torsion = 0` gives the pointwise form of torsion-freeness. -/
theorem isTorsionFreePointwise_of_torsion_eq_zero [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
    [IsManifold I 2 M] (hcov : IsCovariantDerivativeOn E cov Set.univ)
    (htor : hcov.torsion = 0) : IsTorsionFreePointwise cov := by
  intro U W y hU hW
  have h0 : hcov.torsion y (U y) (W y) = 0 := by rw [htor]; simp
  rw [hcov.torsion_apply hU hW] at h0
  exact eq_of_sub_eq_zero h0

/-- Bracket of two `C^n` fields is differentiable at the point. -/
private theorem mdiffAt_mlieBracket (hn : minSmoothness 𝕜 2 ≤ (n : ℕ∞ω))
    (A B : Π y : M, TangentSpace I y) (hA : CMDiffAt (n : ℕ∞ω) (T% A) x)
    (hB : CMDiffAt (n : ℕ∞ω) (T% B) x) : MDiffAt (T% (mlieBracket I A B)) x := by
  have : IsManifold I (minSmoothness 𝕜 2) M :=
    IsManifold.of_le (n := (n : ℕ∞ω) + 1) (le_trans hn le_self_add)
  have hmn : minSmoothness 𝕜 (((1 : ℕ∞) : ℕ∞ω) + 1) ≤ (n : ℕ∞ω) := by
    rw [show ((1 : ℕ∞) : ℕ∞ω) + 1 = 2 by norm_num]; exact hn
  exact (ContMDiffAt.mlieBracket_vectorField (m := 1) hA hB hmn).mdifferentiableAt (by simp)

/-- **One cyclic group of the first Bianchi identity.**
`∇_U ∇_P Q - ∇_U ∇_Q P - ∇_{[P,Q]} U = [U, [P, Q]]` for a torsion-free connection. -/
theorem bianchi_group (hcov : IsCovariantDerivativeOn E cov Set.univ)
    (hcovloc : CovC2LocalMDiffAt E cov x) (htf : IsTorsionFreePointwise cov)
    (hn : minSmoothness 𝕜 2 ≤ (n : ℕ∞ω)) {U P Q : Π y : M, TangentSpace I y}
    (hU : CMDiffAt (n : ℕ∞ω) (T% U) x)
    (hP : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% P) y)
    (hQ : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% Q) y) :
    cov (fun y ↦ cov Q y (P y)) x (U x) - cov (fun y ↦ cov P y (Q y)) x (U x)
        - cov U x (mlieBracket I P Q x)
      = mlieBracket I U (mlieBracket I P Q) x := by
  have h2n : (2 : ℕ∞ω) ≤ (n : ℕ∞ω) := le_minSmoothness.trans hn
  have hn0 : (n : ℕ∞ω) ≠ 0 := by
    intro h; rw [h] at h2n; simp at h2n
  have hPd : ∀ᶠ y in 𝓝 x, MDiffAt (T% P) y := hP.mono fun _ hy ↦ hy.mdifferentiableAt hn0
  have hQd : ∀ᶠ y in 𝓝 x, MDiffAt (T% Q) y := hQ.mono fun _ hy ↦ hy.mdifferentiableAt hn0
  have hUd : MDiffAt (T% U) x := hU.mdifferentiableAt hn0
  have hBd : MDiffAt (T% (mlieBracket I P Q)) x :=
    mdiffAt_mlieBracket hn P Q hP.self_of_nhds hQ.self_of_nhds
  -- the two iterated sections are differentiable at `x`
  have hcQP : MDiffAt (T% fun y ↦ cov Q y (P y)) x :=
    mdiffAt_cov_apply (hcovloc Q (hQ.mono fun _ hy ↦ hy.of_le h2n)) hPd.self_of_nhds
  have hcPQ : MDiffAt (T% fun y ↦ cov P y (Q y)) x :=
    mdiffAt_cov_apply (hcovloc P (hP.mono fun _ hy ↦ hy.of_le h2n)) hQd.self_of_nhds
  -- torsion-freeness as an identity of *sections* near `x`
  have hsec : ∀ᶠ y in 𝓝 x, (fun y ↦ cov Q y (P y)) y
      = ((fun y ↦ cov P y (Q y)) + mlieBracket I P Q) y := by
    filter_upwards [hPd, hQd] with y hy hy'
    have h := htf P Q y hy hy'
    simp only [Pi.add_apply]
    rw [← h]; abel
  have hsum : MDiffAt (T% ((fun y ↦ cov P y (Q y)) + mlieBracket I P Q)) x :=
    mdifferentiableAt_add_section hcPQ hBd
  have key : cov (fun y ↦ cov Q y (P y)) x
      = cov (fun y ↦ cov P y (Q y)) x + cov (mlieBracket I P Q) x := by
    rw [hcov.congr_of_eventuallyEq hcQP hsum univ_mem hsec, hcov.add hcPQ hBd]
  have keyU : cov (fun y ↦ cov Q y (P y)) x (U x)
      = cov (fun y ↦ cov P y (Q y)) x (U x) + cov (mlieBracket I P Q) x (U x) := by
    rw [key]; simp
  have hlast : cov (mlieBracket I P Q) x (U x) - cov U x (mlieBracket I P Q x)
      = mlieBracket I U (mlieBracket I P Q) x := htf U (mlieBracket I P Q) x hUd hBd
  rw [keyU, ← hlast]; abel

/-- **First Bianchi identity.** For a torsion-free connection on the tangent bundle, the cyclic
sum of the curvature operator vanishes. -/
theorem curvature_cyclic_eq_zero (hcov : IsCovariantDerivativeOn E cov Set.univ)
    (hcovloc : CovC2LocalMDiffAt E cov x) (htf : IsTorsionFreePointwise cov)
    (hn : minSmoothness 𝕜 2 ≤ (n : ℕ∞ω))
    (hX : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% X) y)
    (hY : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% Y) y)
    (hZ : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% Z) y) :
    curvature cov X Y Z x + curvature cov Y Z X x + curvature cov Z X Y x = 0 := by
  have h2n : (2 : ℕ∞ω) ≤ (n : ℕ∞ω) := le_minSmoothness.trans hn
  have : IsManifold I 2 M := by
    refine IsManifold.of_le (n := (n : ℕ∞ω) + 1) ?_
    exact le_trans h2n le_self_add
  have : IsManifold I (minSmoothness 𝕜 3) M := by
    refine IsManifold.of_le (n := (n : ℕ∞ω) + 1) ?_
    rw [show (3 : ℕ∞ω) = 2 + 1 by norm_num, minSmoothness_add]
    exact add_le_add hn le_rfl
  -- the three cyclic groups
  have g1 := bianchi_group hcov hcovloc htf hn hX.self_of_nhds hY hZ
  have g2 := bianchi_group hcov hcovloc htf hn hY.self_of_nhds hZ hX
  have g3 := bianchi_group hcov hcovloc htf hn hZ.self_of_nhds hX hY
  have main : curvature cov X Y Z x + curvature cov Y Z X x + curvature cov Z X Y x
      = mlieBracket I X (mlieBracket I Y Z) x + mlieBracket I Y (mlieBracket I Z X) x
        + mlieBracket I Z (mlieBracket I X Y) x := by
    rw [← g1, ← g2, ← g3]
    simp only [curvature_apply]
    abel
  -- Jacobi identity, in Mathlib's Leibniz form
  have hjac := VectorField.leibniz_identity_mlieBracket_apply (I := I) (U := X) (V := Y) (W := Z)
    (hX.self_of_nhds.of_le hn) (hY.self_of_nhds.of_le hn) (hZ.self_of_nhds.of_le hn)
  -- inner swap: `[Y, [Z, X]] = - [Y, [X, Z]]`
  have hZX : MDiffAt (T% (mlieBracket I Z X)) x :=
    mdiffAt_mlieBracket hn Z X hZ.self_of_nhds hX.self_of_nhds
  have hXZ : MDiffAt (T% (mlieBracket I X Z)) x :=
    mdiffAt_mlieBracket hn X Z hX.self_of_nhds hZ.self_of_nhds
  have hswapin : mlieBracket I Y (mlieBracket I Z X) x
      = - mlieBracket I Y (mlieBracket I X Z) x := by
    rw [eq_neg_iff_add_eq_zero, ← mlieBracket_add_right hZX hXZ]
    have hzero : (mlieBracket I Z X) + (mlieBracket I X Z) = 0 := by
      funext y
      rw [Pi.add_apply, mlieBracket_swap_apply (I := I) (V := Z) (W := X)]
      simp
    rw [hzero, mlieBracket_zero_right]
    rfl
  -- outer swap: `[Z, [X, Y]] = - [[X, Y], Z]`
  have hswapout : mlieBracket I Z (mlieBracket I X Y) x
      = - mlieBracket I (mlieBracket I X Y) Z x := mlieBracket_swap_apply
  rw [main, hjac, hswapin, hswapout]
  abel

/-- **First Bianchi identity, `C²` form.** Over `ℝ`, `ℂ` (any `IsRCLikeNormedField`) the
hypotheses are exactly: the connection, its local `C²`-regularity at `x`, torsion-freeness, and
`X`, `Y`, `Z` of class `C²` on a neighbourhood of `x`. The base manifold must be `C³`
(`IsManifold I 3 M`) — that is forced by Mathlib's Lie-bracket smoothness and Jacobi lemmas, not
by the connection. -/
theorem curvature_cyclic_eq_zero_two [IsRCLikeNormedField 𝕜] [IsManifold I 3 M]
    (hcov : IsCovariantDerivativeOn E cov Set.univ)
    (hcovloc : CovC2LocalMDiffAt E cov x) (htf : IsTorsionFreePointwise cov)
    (hX : ∀ᶠ y in 𝓝 x, CMDiffAt (2 : ℕ∞ω) (T% X) y)
    (hY : ∀ᶠ y in 𝓝 x, CMDiffAt (2 : ℕ∞ω) (T% Y) y)
    (hZ : ∀ᶠ y in 𝓝 x, CMDiffAt (2 : ℕ∞ω) (T% Z) y) :
    curvature cov X Y Z x + curvature cov Y Z X x + curvature cov Z X Y x = 0 := by
  have hc : (((2 : ℕ∞) : ℕ∞ω)) = (2 : ℕ∞ω) := by norm_num
  have : IsManifold I (((2 : ℕ∞) : ℕ∞ω) + 1) M := by
    rw [hc]; exact IsManifold.of_le (n := (3 : ℕ∞ω)) (by norm_num)
  refine curvature_cyclic_eq_zero (n := (2 : ℕ∞)) hcov hcovloc htf (by rw [hc]; simp) ?_ ?_ ?_
  · exact hX.mono fun _ h ↦ by rwa [hc]
  · exact hY.mono fun _ h ↦ by rwa [hc]
  · exact hZ.mono fun _ h ↦ by rwa [hc]

end Bianchi

end RiemannianGeometry
