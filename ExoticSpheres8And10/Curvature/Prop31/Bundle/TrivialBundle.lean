/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Curvature.Prop31.Bundle.Global
import ExoticSpheres8And10.Curvature.HLYModel.Fields

/-! # The trivial principal `S³`-bundle with its flat connection

Over any base `B` (with corners allowed):
* `trivPB : PrincipalS3Bundle I B (B × S³)`, with action `(b, u)·q = (b, uq)`, one global
  trivialisation, and section `b ↦ (b, 1)`;
* `flatConn`, the Maurer–Cartan connection `ω = ū du` with `u = pr₂`. Its four axioms are proved.
* In every gauge and every frame, its curvature data vanish: `Ω = 0` and `DΩ = 0`
  (`OmSq_flat`, `DΩP_flat`).

This gives the bundle half of a model for the hypotheses of `hly_prop31_global`.
-/

open RiemannianGeometry VectorField Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Module

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Triv

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type} [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B]

theorem contMDiff_trivAct :
    ContMDiff ((I.prod (𝓡 3)).prod (𝓡 3)) (I.prod (𝓡 3)) ∞
      (uncurry fun (p : B × S3) (q : S3) => (p.1, p.2 * q)) := by
  have h1 : ContMDiff ((I.prod (𝓡 3)).prod (𝓡 3)) I ∞ fun x : (B × S3) × S3 => x.1.1 :=
    contMDiff_fst.comp contMDiff_fst
  have h2 : ContMDiff ((I.prod (𝓡 3)).prod (𝓡 3)) (𝓡 3) ∞ fun x : (B × S3) × S3 => x.1.2 * x.2 :=
    ContMDiff.comp (g := fun x : S3 × S3 => x.1 * x.2) (f := fun x : (B × S3) × S3 => (x.1.2, x.2))
      contMDiff_mulS3 ((contMDiff_snd.comp contMDiff_fst).prodMk contMDiff_snd)
  exact h1.prodMk h2

variable (I B) in
/-- **The trivial principal `S³`-bundle** `B × S³ → B`. -/
def trivPB : PrincipalS3Bundle I B (B × S3) where
  proj := Prod.fst
  ract p q := (p.1, p.2 * q)
  proj_smooth := contMDiff_fst
  ract_smooth := contMDiff_trivAct
  ract_one p := by simp
  ract_mul p q q' := by simp [mul_assoc]
  proj_ract p q := rfl
  nbhd _ := univ
  nbhd_open _ := isOpen_univ
  mem_nbhd _ := mem_univ _
  sec _ b := (b, 1)
  sec_smooth _ := (contMDiff_id.prodMk contMDiff_const).contMDiffOn
  proj_sec _ _ _ := rfl
  fib _ p := p.2
  fib_smooth _ := contMDiff_snd.contMDiffOn
  sec_fib _ p _ := by simp
  fib_sec _ _ _ u := by simp

/-- The fibre coordinate `u = pr₂`, as a quaternion. -/
def uq (p : B × S3) : Quaternion ℝ := (p.2 : Quaternion ℝ)

theorem contMDiff_uq : ContMDiff (I.prod (𝓡 3)) 𝓘(ℝ, Quaternion ℝ) ∞ (uq (B := B)) :=
  (contMDiff_coe_sphere (n := 3)).comp contMDiff_snd

theorem mdiffAt_uq (p : B × S3) : MDifferentiableAt (I.prod (𝓡 3)) 𝓘(ℝ, Quaternion ℝ) uq p :=
  (contMDiff_uq p).mdifferentiableAt (by simp)

/-- `ū du` is imaginary: `du` is tangent to the sphere at `u`. -/
theorem re_star_uq_mvfderiv (p : B × S3) (v : TangentSpace (I.prod (𝓡 3)) p) :
    (star (uq p) * mvfderiv (I.prod (𝓡 3)) uq p v).re = 0 := by
  have hval : MDifferentiableAt (𝓡 3) 𝓘(ℝ, Quaternion ℝ) (Subtype.val : S3 → Quaternion ℝ) p.2 :=
    ((contMDiff_coe_sphere (m := 1)) _).mdifferentiableAt one_ne_zero
  have hsnd : MDifferentiableAt (I.prod (𝓡 3)) (𝓡 3) (Prod.snd : B × S3 → S3) p :=
    mdifferentiableAt_snd
  rw [show (uq : B × S3 → Quaternion ℝ) = Subtype.val ∘ Prod.snd from rfl,
    mvfderiv_comp_apply hval hsnd]
  set w := mfderiv (I.prod (𝓡 3)) (𝓡 3) (Prod.snd : B × S3 → S3) p v
  have hmem : mvfderiv (𝓡 3) (Subtype.val : S3 → Quaternion ℝ) p.2 w ∈
      (ℝ ∙ (p.2 : Quaternion ℝ))ᗮ := by
    rw [← range_mfderiv_coe_sphere (n := 3)]; exact ⟨w, rfl⟩
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, Quaternion.inner_def] at hmem
  simp only [Quaternion.re_mul, Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star,
    Quaternion.imK_star, comp_apply] at hmem ⊢
  show (p.2 : Quaternion ℝ).re * _ - _ - _ - _ = 0
  linarith

theorem mvfderiv_uq_fund (p : B × S3) (ζ : E3) :
    mvfderiv (I.prod (𝓡 3)) uq p ((trivPB I B).fund ζ p) = uq p * ι3 ζ := by
  have hv : ∀ q : S3, MDifferentiableAt (𝓡 3) 𝓘(ℝ, Quaternion ℝ)
      (Subtype.val : S3 → Quaternion ℝ) q :=
    fun q => ((contMDiff_coe_sphere (m := 1)) q).mdifferentiableAt one_ne_zero
  have hR : MDifferentiableAt (𝓡 3) (I.prod (𝓡 3)) ((trivPB I B).ract p) 1 :=
    ((trivPB I B).contMDiff_ract_left p 1).mdifferentiableAt (by simp)
  have key : ∀ y (hy : (trivPB I B).ract p 1 = y),
      mvfderiv (𝓡 3) (uq ∘ (trivPB I B).ract p) 1 ζ =
        mvfderiv (I.prod (𝓡 3)) uq y (mfderiv (𝓡 3) (I.prod (𝓡 3)) ((trivPB I B).ract p) 1 ζ) := by
    intro y hy; subst hy; exact mvfderiv_comp' (mdiffAt_uq _) hR ζ
  show mvfderiv (I.prod (𝓡 3)) uq p
    (mfderiv (𝓡 3) (I.prod (𝓡 3)) ((trivPB I B).ract p) 1 ζ) = _
  rw [← key p ((trivPB I B).ract_one p)]
  have e : (uq ∘ (trivPB I B).ract p) =
      (ContinuousLinearMap.mul ℝ (Quaternion ℝ) (p.2 : Quaternion ℝ)) ∘
        (Subtype.val : S3 → Quaternion ℝ) := rfl
  rw [e, mvfderiv_clm_comp _ (hv 1) ζ, mvfderiv_val_one]
  rfl

variable (I B) in
/-- **The flat (Maurer–Cartan) connection** `ω = ū du` on `B × S³`. -/
def flatConn : S3Connection (trivPB I B) where
  conn p := (ContinuousLinearMap.mul ℝ (Quaternion ℝ) (star (uq p))).comp
    (mvfderiv (I.prod (𝓡 3)) uq p)
  im p v := re_star_uq_mvfderiv p v
  smooth V x hV := by
    have h1 : ContMDiffAt (I.prod (𝓡 3)) 𝓘(ℝ, Quaternion ℝ) ∞ (fun p : B × S3 => star (uq p)) x :=
      (((starL' ℝ : Quaternion ℝ ≃L[ℝ] Quaternion ℝ) :
        Quaternion ℝ →L[ℝ] Quaternion ℝ).contMDiff.comp contMDiff_uq) x
    have h2 : ContMDiffAt (I.prod (𝓡 3)) 𝓘(ℝ, Quaternion ℝ) ∞
        (fun p => mvfderiv (I.prod (𝓡 3)) uq p (V p)) x :=
      S3Connection.contMDiffAt_mvfderiv_field (Eventually.of_forall fun p => contMDiff_uq p) hV
    exact contMDiffAt_qmul h1 h2
  vert p ζ := by
    show star (uq p) * mvfderiv (I.prod (𝓡 3)) uq p ((trivPB I B).fund ζ p) = ι3 ζ
    rw [mvfderiv_uq_fund, ← mul_assoc]
    show star (p.2 : Quaternion ℝ) * (p.2 : Quaternion ℝ) * ι3 ζ = ι3 ζ
    rw [star_mul_self_sphere, one_mul]
  equiv p q v := by
    have hRq : MDifferentiableAt (I.prod (𝓡 3)) (I.prod (𝓡 3)) ((trivPB I B).ract · q) p :=
      ((trivPB I B).contMDiff_ract q p).mdifferentiableAt (by simp)
    show star (uq ((trivPB I B).ract p q)) * mvfderiv (I.prod (𝓡 3)) uq ((trivPB I B).ract p q)
      (mfderiv (I.prod (𝓡 3)) (I.prod (𝓡 3)) ((trivPB I B).ract · q) p v) =
        star (q : Quaternion ℝ) * (star (uq p) * mvfderiv (I.prod (𝓡 3)) uq p v) * q
    rw [← mvfderiv_comp_apply (mdiffAt_uq _) hRq]
    have e : (uq ∘ ((trivPB I B).ract · q)) =
        ((ContinuousLinearMap.mul ℝ (Quaternion ℝ)).flip (q : Quaternion ℝ)) ∘ uq := rfl
    rw [e, mvfderiv_clm_comp _ (mdiffAt_uq p) v]
    simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply']
    rw [show uq ((trivPB I B).ract p q) = uq p * (q : Quaternion ℝ) from rfl, star_mul]
    simp only [mul_assoc]

/-! ### The flat connection has no curvature, in any gauge and frame -/

theorem pot_flat (b₀ b : B) (w : TangentSpace I b) : (flatConn I B).pot b₀ b w = 0 := by
  have hs : MDifferentiableAt I (I.prod (𝓡 3)) ((trivPB I B).sec b₀) b :=
    (contMDiff_id.prodMk contMDiff_const : ContMDiff I (I.prod (𝓡 3)) ∞
      fun b : B => (b, (1 : S3))).mdifferentiableAt (by simp)
  show star (uq ((trivPB I B).sec b₀ b)) * mvfderiv (I.prod (𝓡 3)) uq ((trivPB I B).sec b₀ b)
    (mfderiv I (I.prod (𝓡 3)) ((trivPB I B).sec b₀) b w) = 0
  rw [← mvfderiv_comp_apply (mdiffAt_uq _) hs]
  rw [show (uq ∘ (trivPB I B).sec b₀) = fun _ : B => ((1 : S3) : Quaternion ℝ) from rfl]
  rw [show mvfderiv I (fun _ : B => ((1 : S3) : Quaternion ℝ)) b w = 0 by
    simp only [mvfderiv, mfderiv_const, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.zero_apply, map_zero], mul_zero]

theorem curvF_flat (b₀ : B) (e₁ e₂ : Π b : B, TangentSpace I b) (b : B) :
    (flatConn I B).curvF b₀ e₁ e₂ b = 0 := by
  have hz : ∀ e : Π b : B, TangentSpace I b, (flatConn I B).potE b₀ e = fun _ => 0 :=
    fun e => funext fun b => pot_flat b₀ b (e b)
  simp only [S3Connection.curvF, hz, pot_flat, mul_zero, sub_self, add_zero]
  simp [mvfderiv, mfderiv_const]

variable {n : ℕ}

theorem tΩ_flat (b₀ : B) (e : Fin n → Π b : B, TangentSpace I b) (i j : Fin n) (a : Fin 3) :
    (flatConn I B).tΩ b₀ e i j a = fun _ => 0 := by
  funext y
  simp only [S3Connection.tΩ, curvF_flat, mul_zero, zero_mul, inner_zero_left]

theorem OmSq_flat (b₀ : B) (e : Fin n → Π b : B, TangentSpace I b) (y : B × S3) :
    Prop31Algebra.OmSq ((flatConn I B).ΩP e b₀ y) = 0 := by
  simp only [Prop31Algebra.OmSq, S3Connection.ΩP, tΩ_flat]
  simp

theorem DΩP_flat (g : Π b : B, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
    (b₀ : B) (e : Fin n → Π b : B, TangentSpace I b) (r : B → ℝ) (y : B × S3)
    (k i j : Fin n) (a : Fin 3) : (flatConn I B).DΩP g e r b₀ y k i j a = 0 := by
  simp only [S3Connection.DΩP, DΩf, S3Connection.dΩP, tΩ_flat]
  simp [mvfderiv, mfderiv_const]

end Triv

end

end ExoticSpheres8And10
