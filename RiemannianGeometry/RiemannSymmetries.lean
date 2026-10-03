/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import RiemannianGeometry.RiemannTensor
import RiemannianGeometry.SectionalCurvature
import RiemannianGeometry.CurvatureMetric
import RiemannianGeometry.CurvatureBianchi
import RiemannianGeometry.LeviCivita
import RiemannianGeometry.KoszulRegularity
import RiemannianGeometry.CurvatureBundled

/-!
# The remaining curvature symmetries of the Riemann tensor of a metric

`Foundations.RiemannTensor` records first-pair antisymmetry. This file adds the remaining
symmetries, all at `C²` regularity of the metric:

* `isMetricCompatibleWith_leviCivita` — the bridge from `IsCompatibleWith` (tangent bundle) to
  `IsMetricCompatibleWith` (general bundle), so that `curvature_skewAdjoint_two` is instantiable.
* `riemannTensorAt_swap_right`, `riemannTensorAt_self_right` — last-pair antisymmetry.
* `riemannCurvatureAt_cyclic`, `riemannTensorAt_bianchi` — the first Bianchi identity, bundled and
  lowered.
* `riemannTensorAt_pair_symm` — pair symmetry `Rm(u,v,w,z) = Rm(w,z,u,v)`, pure algebra from the
  two antisymmetries and Bianchi.
* `riemannTensorAt_reparam`, `gramDet_reparam`, `sectionalCurvatureAt_reparam` — invariance of
  sectional curvature under an invertible reparametrisation of the pair.

## Regularity

`C²` on the metric throughout: every hypothesis is `IsContMDiffMetricSection E ((2 : ℕ∞)) g`, or
`IsMDiffMetric E g` derived from it. `IsManifold I 3 M` is used (via
`curvature_skewAdjoint_two` and `curvature_cyclic_eq_zero_two`) but it is a condition on the
*charts* and free from the ambient `[IsManifold I ∞ M]`. Nothing here differentiates the metric a
third time.
-/

noncomputable section

open Bundle Set VectorField Filter
open scoped Manifold ContDiff Topology

namespace RiemannianGeometry

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {g : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
  {x : M}

/-- The two spellings of the order `2` used by the project's regularity hypotheses agree. -/
theorem coe_two_eq_two : ((2 : ℕ∞) : ℕ∞ω) = (2 : ℕ∞ω) := by norm_num

/-! ## (1) The compatibility bridge -/

/-- **`leviCivita g` is metric compatible in the general-bundle sense.** -/
theorem isMetricCompatibleWith_leviCivita (hsymm : IsSymm g) (hnd : IsNondegenerate g)
    (hgm : IsMDiffMetric E g) : IsMetricCompatibleWith E (leviCivita g) g := by
  intro X σ τ y hσ hτ
  exact isCompatibleWith_leviCivita hsymm hnd hgm hσ hτ

section Tensor

variable (hsymm : IsSymm g) (hnd : IsNondegenerate g)
  (hg : IsContMDiffMetricSection E ((2 : ℕ∞)) g)

include hsymm hnd hg

omit [CompleteSpace E] [FiniteDimensional ℝ E] hsymm hnd in
/-- The metric is a differentiable section, from the `C²` hypothesis. -/
theorem isMDiffMetric_of_isContMDiffMetricSection : IsMDiffMetric E g :=
  fun y ↦ (hg y).mdifferentiableAt (by simp)

/-! ## (2) Last-pair antisymmetry -/

/-- **Antisymmetry in the last pair.** `Rm(u,v,w,z) = −Rm(u,v,z,w)`. -/
theorem riemannTensorAt_swap_right (u v w z : TangentSpace I x) :
    riemannTensorAt hsymm hnd hg x u v w z = - riemannTensorAt hsymm hnd hg x u v z w := by
  have hgm : IsMDiffMetric E g := isMDiffMetric_of_isContMDiffMetricSection hg
  have hmc : IsMetricCompatibleWith E (leviCivita g) g :=
    isMetricCompatibleWith_leviCivita hsymm hnd hgm
  -- the four extensions, at both spellings of the order
  have hu : ∀ᶠ y in 𝓝 x, CMDiffAt (2 : ℕ∞ω)
      (T% (FiberBundle.extend E u : Π y : M, TangentSpace I y)) y :=
    eventually_contMDiffAt_extendTangent (I := I) (k := (2 : ℕ∞ω)) u
  have hv : ∀ᶠ y in 𝓝 x, CMDiffAt (2 : ℕ∞ω)
      (T% (FiberBundle.extend E v : Π y : M, TangentSpace I y)) y :=
    eventually_contMDiffAt_extendTangent (I := I) (k := (2 : ℕ∞ω)) v
  have hw : ∀ᶠ y in 𝓝 x, CMDiffAt (2 : ℕ∞ω)
      (T% (FiberBundle.extend E w : Π y : M, TangentSpace I y)) y :=
    eventually_contMDiffAt_extendTangent (I := I) (k := (2 : ℕ∞ω)) w
  have hz : ∀ᶠ y in 𝓝 x, CMDiffAt (2 : ℕ∞ω)
      (T% (FiberBundle.extend E z : Π y : M, TangentSpace I y)) y :=
    eventually_contMDiffAt_extendTangent (I := I) (k := (2 : ℕ∞ω)) z
  have hu' : ∀ᶠ y in 𝓝 x, CMDiffAt ((2 : ℕ∞) : ℕ∞ω)
      (T% (FiberBundle.extend E u : Π y : M, TangentSpace I y)) y :=
    eventually_contMDiffAt_extendTangent (I := I) (k := ((2 : ℕ∞) : ℕ∞ω)) u
  have hv' : ∀ᶠ y in 𝓝 x, CMDiffAt ((2 : ℕ∞) : ℕ∞ω)
      (T% (FiberBundle.extend E v : Π y : M, TangentSpace I y)) y :=
    eventually_contMDiffAt_extendTangent (I := I) (k := ((2 : ℕ∞) : ℕ∞ω)) v
  have hw' : ∀ᶠ y in 𝓝 x, CMDiffAt ((2 : ℕ∞) : ℕ∞ω)
      (T% (FiberBundle.extend E w : Π y : M, TangentSpace I y)) y :=
    eventually_contMDiffAt_extendTangent (I := I) (k := ((2 : ℕ∞) : ℕ∞ω)) w
  have hz' : ∀ᶠ y in 𝓝 x, CMDiffAt ((2 : ℕ∞) : ℕ∞ω)
      (T% (FiberBundle.extend E z : Π y : M, TangentSpace I y)) y :=
    eventually_contMDiffAt_extendTangent (I := I) (k := ((2 : ℕ∞) : ℕ∞ω)) z
  -- the metric section at the uncast order
  have hgc : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (2 : ℕ∞ω)
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun (y : M) ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) y (g y)) x := by
    rw [← coe_two_eq_two]; exact hg x
  have hf : CMDiffAt (2 : ℕ∞ω)
      (fun y ↦ g y ((FiberBundle.extend E w : Π y : M, TangentSpace I y) y)
        ((FiberBundle.extend E z : Π y : M, TangentSpace I y) y)) x :=
    contMDiffAt_pairing hgc hw.self_of_nhds hz.self_of_nhds
  have key := curvature_skewAdjoint_two (F := E) (V := fun y : M ↦ TangentSpace I y)
    (cov := leviCivita g) (g := g)
    (X := (FiberBundle.extend E u : Π y : M, TangentSpace I y))
    (Y := (FiberBundle.extend E v : Π y : M, TangentSpace I y))
    (Z := (FiberBundle.extend E w : Π y : M, TangentSpace I y))
    (W := (FiberBundle.extend E z : Π y : M, TangentSpace I y)) (x := x)
    hmc (covC2LocalMDiffAt_leviCivita hsymm hnd hg x) (hgm x) hw hz hu hv hf
  rw [FiberBundle.extend_apply_self, FiberBundle.extend_apply_self] at key
  have hrw : riemannCurvatureAt hsymm hnd hg x u v w
      = curvature (leviCivita g) (FiberBundle.extend E u) (FiberBundle.extend E v)
          (FiberBundle.extend E w) x := by
    have h := riemannCurvatureAt_apply hsymm hnd hg
      (X := (FiberBundle.extend E u : Π y : M, TangentSpace I y))
      (Y := (FiberBundle.extend E v : Π y : M, TangentSpace I y))
      (Z := (FiberBundle.extend E w : Π y : M, TangentSpace I y)) hu' hv' hw'.self_of_nhds
    rwa [FiberBundle.extend_apply_self, FiberBundle.extend_apply_self,
      FiberBundle.extend_apply_self] at h
  have hrz : riemannCurvatureAt hsymm hnd hg x u v z
      = curvature (leviCivita g) (FiberBundle.extend E u) (FiberBundle.extend E v)
          (FiberBundle.extend E z) x := by
    have h := riemannCurvatureAt_apply hsymm hnd hg
      (X := (FiberBundle.extend E u : Π y : M, TangentSpace I y))
      (Y := (FiberBundle.extend E v : Π y : M, TangentSpace I y))
      (Z := (FiberBundle.extend E z : Π y : M, TangentSpace I y)) hu' hv' hz'.self_of_nhds
    rwa [FiberBundle.extend_apply_self, FiberBundle.extend_apply_self,
      FiberBundle.extend_apply_self] at h
  rw [riemannTensorAt_apply, riemannTensorAt_apply, hrw, hrz, key,
    hsymm x w (curvature (leviCivita g) (FiberBundle.extend E u) (FiberBundle.extend E v)
      (FiberBundle.extend E z) x)]

/-- The diagonal case of `riemannTensorAt_swap_right`. -/
theorem riemannTensorAt_self_right (u v w : TangentSpace I x) :
    riemannTensorAt hsymm hnd hg x u v w w = 0 := by
  have h := riemannTensorAt_swap_right hsymm hnd hg u v w w
  linarith

/-! ## (3) First Bianchi identity -/

/-- **First Bianchi identity for the bundled curvature operator.** -/
theorem riemannCurvatureAt_cyclic (u v w : TangentSpace I x) :
    riemannCurvatureAt hsymm hnd hg x u v w + riemannCurvatureAt hsymm hnd hg x v w u
      + riemannCurvatureAt hsymm hnd hg x w u v = 0 := by
  have hgm : IsMDiffMetric E g := isMDiffMetric_of_isContMDiffMetricSection hg
  have hcov := isCovariantDerivativeOn_leviCivita hsymm hnd hgm
  have htf : IsTorsionFreePointwise (leviCivita g) :=
    isTorsionFreePointwise_of_torsion_eq_zero hcov (leviCivita_torsion_eq_zero hsymm hnd hgm)
  have hu : ∀ᶠ y in 𝓝 x, CMDiffAt (2 : ℕ∞ω)
      (T% (FiberBundle.extend E u : Π y : M, TangentSpace I y)) y :=
    eventually_contMDiffAt_extendTangent (I := I) (k := (2 : ℕ∞ω)) u
  have hv : ∀ᶠ y in 𝓝 x, CMDiffAt (2 : ℕ∞ω)
      (T% (FiberBundle.extend E v : Π y : M, TangentSpace I y)) y :=
    eventually_contMDiffAt_extendTangent (I := I) (k := (2 : ℕ∞ω)) v
  have hw : ∀ᶠ y in 𝓝 x, CMDiffAt (2 : ℕ∞ω)
      (T% (FiberBundle.extend E w : Π y : M, TangentSpace I y)) y :=
    eventually_contMDiffAt_extendTangent (I := I) (k := (2 : ℕ∞ω)) w
  have hu' : ∀ᶠ y in 𝓝 x, CMDiffAt ((2 : ℕ∞) : ℕ∞ω)
      (T% (FiberBundle.extend E u : Π y : M, TangentSpace I y)) y :=
    eventually_contMDiffAt_extendTangent (I := I) (k := ((2 : ℕ∞) : ℕ∞ω)) u
  have hv' : ∀ᶠ y in 𝓝 x, CMDiffAt ((2 : ℕ∞) : ℕ∞ω)
      (T% (FiberBundle.extend E v : Π y : M, TangentSpace I y)) y :=
    eventually_contMDiffAt_extendTangent (I := I) (k := ((2 : ℕ∞) : ℕ∞ω)) v
  have hw' : ∀ᶠ y in 𝓝 x, CMDiffAt ((2 : ℕ∞) : ℕ∞ω)
      (T% (FiberBundle.extend E w : Π y : M, TangentSpace I y)) y :=
    eventually_contMDiffAt_extendTangent (I := I) (k := ((2 : ℕ∞) : ℕ∞ω)) w
  have key := curvature_cyclic_eq_zero_two hcov
    (covC2LocalMDiffAt_leviCivita hsymm hnd hg x) htf hu hv hw
  have c1 : riemannCurvatureAt hsymm hnd hg x u v w
      = curvature (leviCivita g) (FiberBundle.extend E u) (FiberBundle.extend E v)
          (FiberBundle.extend E w) x := by
    have h := riemannCurvatureAt_apply hsymm hnd hg
      (X := (FiberBundle.extend E u : Π y : M, TangentSpace I y))
      (Y := (FiberBundle.extend E v : Π y : M, TangentSpace I y))
      (Z := (FiberBundle.extend E w : Π y : M, TangentSpace I y)) hu' hv' hw'.self_of_nhds
    rwa [FiberBundle.extend_apply_self, FiberBundle.extend_apply_self,
      FiberBundle.extend_apply_self] at h
  have c2 : riemannCurvatureAt hsymm hnd hg x v w u
      = curvature (leviCivita g) (FiberBundle.extend E v) (FiberBundle.extend E w)
          (FiberBundle.extend E u) x := by
    have h := riemannCurvatureAt_apply hsymm hnd hg
      (X := (FiberBundle.extend E v : Π y : M, TangentSpace I y))
      (Y := (FiberBundle.extend E w : Π y : M, TangentSpace I y))
      (Z := (FiberBundle.extend E u : Π y : M, TangentSpace I y)) hv' hw' hu'.self_of_nhds
    rwa [FiberBundle.extend_apply_self, FiberBundle.extend_apply_self,
      FiberBundle.extend_apply_self] at h
  have c3 : riemannCurvatureAt hsymm hnd hg x w u v
      = curvature (leviCivita g) (FiberBundle.extend E w) (FiberBundle.extend E u)
          (FiberBundle.extend E v) x := by
    have h := riemannCurvatureAt_apply hsymm hnd hg
      (X := (FiberBundle.extend E w : Π y : M, TangentSpace I y))
      (Y := (FiberBundle.extend E u : Π y : M, TangentSpace I y))
      (Z := (FiberBundle.extend E v : Π y : M, TangentSpace I y)) hw' hu' hv'.self_of_nhds
    rwa [FiberBundle.extend_apply_self, FiberBundle.extend_apply_self,
      FiberBundle.extend_apply_self] at h
  rw [c1, c2, c3]
  exact key

/-- **First Bianchi identity for the `(0,4)` tensor.** -/
theorem riemannTensorAt_bianchi (u v w z : TangentSpace I x) :
    riemannTensorAt hsymm hnd hg x u v w z + riemannTensorAt hsymm hnd hg x v w u z
      + riemannTensorAt hsymm hnd hg x w u v z = 0 := by
  have h : g x (riemannCurvatureAt hsymm hnd hg x u v w
      + riemannCurvatureAt hsymm hnd hg x v w u
      + riemannCurvatureAt hsymm hnd hg x w u v) z = 0 := by
    rw [riemannCurvatureAt_cyclic hsymm hnd hg u v w]; simp
  simpa only [riemannTensorAt_apply, map_add, add_apply] using h

/-! ## (4) Pair symmetry -/

/-- **Pair symmetry.** `Rm(u,v,w,z) = Rm(w,z,u,v)`. Pure algebra from the two antisymmetries and
the first Bianchi identity. -/
theorem riemannTensorAt_pair_symm (u v w z : TangentSpace I x) :
    riemannTensorAt hsymm hnd hg x u v w z = riemannTensorAt hsymm hnd hg x w z u v := by
  have A1 : ∀ a b c d : TangentSpace I x, riemannTensorAt hsymm hnd hg x a b c d
      = - riemannTensorAt hsymm hnd hg x b a c d :=
    fun a b c d ↦ riemannTensorAt_swap_left hsymm hnd hg a b c d
  have A2 : ∀ a b c d : TangentSpace I x, riemannTensorAt hsymm hnd hg x a b c d
      = - riemannTensorAt hsymm hnd hg x a b d c :=
    fun a b c d ↦ riemannTensorAt_swap_right hsymm hnd hg a b c d
  have B : ∀ a b c d : TangentSpace I x, riemannTensorAt hsymm hnd hg x a b c d
      + riemannTensorAt hsymm hnd hg x b c a d + riemannTensorAt hsymm hnd hg x c a b d = 0 :=
    fun a b c d ↦ riemannTensorAt_bianchi hsymm hnd hg a b c d
  have r1 := B u v w z
  have r2 := B v u z w
  have r3 := B w z u v
  have r4 := B z w v u
  have e1 : riemannTensorAt hsymm hnd hg x v u z w
      = riemannTensorAt hsymm hnd hg x u v w z := by
    rw [A1 v u z w, A2 u v z w]; ring
  have e2 : riemannTensorAt hsymm hnd hg x z w v u
      = riemannTensorAt hsymm hnd hg x w z u v := by
    rw [A1 z w v u, A2 w z v u]; ring
  have e3 : riemannTensorAt hsymm hnd hg x w v z u
      = riemannTensorAt hsymm hnd hg x v w u z := by
    rw [A1 w v z u, A2 v w z u]; ring
  have e4 : riemannTensorAt hsymm hnd hg x u w z v
      = riemannTensorAt hsymm hnd hg x w u v z := by
    rw [A1 u w z v, A2 w u z v]; ring
  have e5 : riemannTensorAt hsymm hnd hg x v z w u
      = riemannTensorAt hsymm hnd hg x z v u w := by
    rw [A1 v z w u, A2 z v w u]; ring
  have e6 : riemannTensorAt hsymm hnd hg x z u w v
      = riemannTensorAt hsymm hnd hg x u z v w := by
    rw [A1 z u w v, A2 u z w v]; ring
  linarith [r1, r2, r3, r4, e1, e2, e3, e4, e5, e6]

/-! ## (5) Basis invariance -/

/-- Multilinear collapse in the **first** pair: only the determinant survives. -/
theorem riemannTensorAt_reparam_left (a b c d : ℝ) (u v p q : TangentSpace I x) :
    riemannTensorAt hsymm hnd hg x (a • u + b • v) (c • u + d • v) p q
      = (a * d - b * c) * riemannTensorAt hsymm hnd hg x u v p q := by
  have h0u : riemannTensorAt hsymm hnd hg x u u p q = 0 :=
    riemannTensorAt_self_left hsymm hnd hg u p q
  have h0v : riemannTensorAt hsymm hnd hg x v v p q = 0 :=
    riemannTensorAt_self_left hsymm hnd hg v p q
  have hsw : riemannTensorAt hsymm hnd hg x v u p q
      = - riemannTensorAt hsymm hnd hg x u v p q :=
    riemannTensorAt_swap_left hsymm hnd hg v u p q
  simp only [map_add, map_smul, add_apply,
    smul_apply, smul_eq_mul]
  rw [h0u, h0v, hsw]
  ring

/-- Multilinear collapse in the **last** pair: only the determinant survives. -/
theorem riemannTensorAt_reparam_right (a b c d : ℝ) (u v p q : TangentSpace I x) :
    riemannTensorAt hsymm hnd hg x p q (a • u + b • v) (c • u + d • v)
      = (a * d - b * c) * riemannTensorAt hsymm hnd hg x p q u v := by
  have h0u : riemannTensorAt hsymm hnd hg x p q u u = 0 :=
    riemannTensorAt_self_right hsymm hnd hg p q u
  have h0v : riemannTensorAt hsymm hnd hg x p q v v = 0 :=
    riemannTensorAt_self_right hsymm hnd hg p q v
  have hsw : riemannTensorAt hsymm hnd hg x p q v u
      = - riemannTensorAt hsymm hnd hg x p q u v :=
    riemannTensorAt_swap_right hsymm hnd hg p q v u
  simp only [map_add, map_smul, add_apply,
    smul_apply, smul_eq_mul]
  rw [h0u, h0v, hsw]
  ring

/-- **The numerator of sectional curvature scales by the squared determinant.** -/
theorem riemannTensorAt_reparam (a b c d : ℝ) (u v : TangentSpace I x) :
    riemannTensorAt hsymm hnd hg x (a • u + b • v) (c • u + d • v) (c • u + d • v)
        (a • u + b • v)
      = (a * d - b * c) ^ 2 * riemannTensorAt hsymm hnd hg x u v v u := by
  rw [riemannTensorAt_reparam_left hsymm hnd hg a b c d u v (c • u + d • v) (a • u + b • v),
    riemannTensorAt_reparam_right hsymm hnd hg c d a b u v u v,
    riemannTensorAt_swap_right hsymm hnd hg u v u v]
  ring

end Tensor

/-- Cancelling a nonzero common factor in a quotient of reals. -/
private theorem div_cancel_common {k N D : ℝ} (hk : k ≠ 0) : k * N / (k * D) = N / D := by
  rcases eq_or_ne D 0 with hD | hD
  · simp [hD]
  · rw [div_eq_div_iff (mul_ne_zero hk hD) hD]; ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- **The Gram determinant scales by the squared determinant.** -/
theorem gramDet_reparam (hsymm : IsSymm g) (a b c d : ℝ) (u v : TangentSpace I x) :
    gramDet g x (a • u + b • v) (c • u + d • v) = (a * d - b * c) ^ 2 * gramDet g x u v := by
  simp only [gramDet, map_add, map_smul, add_apply,
    smul_apply, smul_eq_mul]
  rw [hsymm x v u]
  ring

/-- **Sectional curvature depends only on the plane**, in the pair formulation: it is unchanged
by any invertible reparametrisation of the pair. -/
theorem sectionalCurvatureAt_reparam (hsymm : IsSymm g) (hpos : IsPosDef g)
    (hg : IsContMDiffMetricSection E ((2 : ℕ∞)) g) {a b c d : ℝ}
    (hdet : a * d - b * c ≠ 0) (u v : TangentSpace I x) :
    sectionalCurvatureAt hsymm hpos hg x (a • u + b • v) (c • u + d • v)
      = sectionalCurvatureAt hsymm hpos hg x u v := by
  rw [sectionalCurvatureAt_def hsymm hpos hg x (a • u + b • v) (c • u + d • v),
    sectionalCurvatureAt_def hsymm hpos hg x u v,
    riemannTensorAt_reparam hsymm (IsPosDef.isNondegenerate hpos) hg a b c d u v,
    gramDet_reparam hsymm a b c d u v]
  exact div_cancel_common (pow_ne_zero 2 hdet)

end RiemannianGeometry



