/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Curvature.Prop31.Bundle.TrivialBundle

/-! # A connection with prescribed potential `f dh ⊗ q` on the trivial bundle

For smooth `f, h : B → ℝ` and an imaginary quaternion `q`, `potConn f h q` is the connection
`ω = ū (f dh ⊗ q) u + ū du` on `B × S³`. All four connection axioms are proved.

In the trivialisation `b ↦ (b, 1)` its potential is `f dh ⊗ q` (`pot_potConn`). Its curvature
is `(df ∧ dh) ⊗ q` (`curvF_potConn`):
`F(e₁, e₂) = (e₁f·e₂h − e₂f·e₁h) q`.
-/

open RiemannianGeometry VectorField Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Module

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Pot

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type} [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B]
  {f h : B → ℝ} {q : Quaternion ℝ}

/-- `d(h ∘ π)` on `B × S³`. -/
def dhP (h : B → ℝ) (p : B × S3) : TangentSpace (I.prod (𝓡 3)) p →L[ℝ] ℝ :=
  mvfderiv (I.prod (𝓡 3)) (fun x : B × S3 => h x.1) p

theorem dhP_eq (hh : ContMDiff I 𝓘(ℝ) ∞ h) (p : B × S3) (v : TangentSpace (I.prod (𝓡 3)) p) :
    dhP h p v = mvfderiv I h p.1 (mfderiv (I.prod (𝓡 3)) I Prod.fst p v) :=
  RiemannianGeometry.mvfderiv_comp_apply ((hh p.1).mdifferentiableAt (by simp))
    mdifferentiableAt_fst v

variable (I B) in
/-- **The connection with potential `f dh ⊗ q`.** -/
def potConn (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ) ∞ h) (hq : q.re = 0) :
    S3Connection (trivPB I B) where
  conn p := (ContinuousLinearMap.mul ℝ (Quaternion ℝ) (star (uq p))).comp
      (((ContinuousLinearMap.mul ℝ (Quaternion ℝ)).flip (uq p)).comp
        ((f p.1 • dhP h p).smulRight q)) + (flatConn I B).conn p
  im p v := by
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.mul_apply', Quaternion.re_add]
    rw [(flatConn I B).im p v, add_zero, ← mul_assoc, re_star_mul_mul]
    simp [hq]
  smooth V x hV := by
    have hu := contMDiff_uq (I := I) (B := B)
    have h1 : ContMDiffAt (I.prod (𝓡 3)) 𝓘(ℝ, Quaternion ℝ) ∞
        (fun p : B × S3 => star (uq p)) x :=
      (((starL' ℝ : Quaternion ℝ ≃L[ℝ] Quaternion ℝ) :
        Quaternion ℝ →L[ℝ] Quaternion ℝ).contMDiff.comp hu) x
    have hdh : ContMDiffAt (I.prod (𝓡 3)) 𝓘(ℝ) ∞ (fun p => dhP h p (V p)) x :=
      S3Connection.contMDiffAt_mvfderiv_field
        (Eventually.of_forall fun p => (hh.comp contMDiff_fst) p) hV
    have hfx : ContMDiffAt (I.prod (𝓡 3)) 𝓘(ℝ) ∞ (fun p : B × S3 => f p.1) x :=
      (hf.comp contMDiff_fst) x
    have hc : ContMDiffAt (I.prod (𝓡 3)) 𝓘(ℝ, Quaternion ℝ) ∞
        (fun p => (f p.1 * dhP h p (V p)) • q) x :=
      ((ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) q).contMDiff.contMDiffAt).comp
        x (hfx.mul hdh)
    have h2 := contMDiffAt_qmul (contMDiffAt_qmul h1 hc) (hu x)
    have h3 := (flatConn I B).smooth V x hV
    refine (h2.add h3).congr_of_eventuallyEq (Eventually.of_forall fun p => ?_)
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.mul_apply', ContinuousLinearMap.smul_apply, smul_eq_mul, Pi.add_apply,
      mul_assoc]
  vert p ζ := by
    have h0 : dhP h p ((trivPB I B).fund ζ p) = 0 := by
      rw [dhP_eq hh]
      show mvfderiv I h p.1 (mfderiv (I.prod (𝓡 3)) I (trivPB I B).proj p _) = 0
      rw [(trivPB I B).mfderiv_proj_fund p ζ]
      exact ContinuousLinearMap.map_zero _
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply, h0, smul_zero,
      zero_smul, ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply', zero_mul,
      mul_zero, zero_add]
    exact (flatConn I B).vert p ζ
  equiv p r v := by
    have hRq : MDifferentiableAt (I.prod (𝓡 3)) (I.prod (𝓡 3)) ((trivPB I B).ract · r) p :=
      ((trivPB I B).contMDiff_ract r p).mdifferentiableAt (by simp)
    have hH : MDifferentiableAt (I.prod (𝓡 3)) 𝓘(ℝ) (fun x : B × S3 => h x.1)
        ((trivPB I B).ract p r) := ((hh.comp contMDiff_fst) _).mdifferentiableAt (by simp)
    have hd : dhP h ((trivPB I B).ract p r)
        (mfderiv (I.prod (𝓡 3)) (I.prod (𝓡 3)) ((trivPB I B).ract · r) p v) = dhP h p v := by
      unfold dhP
      rw [← RiemannianGeometry.mvfderiv_comp_apply
        (f := fun x => (trivPB I B).ract x r) hH hRq]
      rfl
    have hflat := (flatConn I B).equiv p r v
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.mul_apply', ContinuousLinearMap.smul_apply, hd, hflat]
    rw [show uq ((trivPB I B).ract p r) = uq p * (r : Quaternion ℝ) from rfl, star_mul,
      show ((trivPB I B).ract p r).1 = p.1 from rfl]
    simp only [mul_assoc, add_mul, mul_add]

variable (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ) ∞ h) (hq : q.re = 0)

/-- In the trivialisation `b ↦ (b, 1)`, the potential is `f dh ⊗ q`. -/
theorem pot_potConn (b₀ b : B) (w : TangentSpace I b) :
    (potConn I B hf hh hq).pot b₀ b w = (f b * mvfderiv I h b w) • q := by
  have hs : MDifferentiableAt I (I.prod (𝓡 3)) ((trivPB I B).sec b₀) b :=
    (contMDiff_id.prodMk contMDiff_const : ContMDiff I (I.prod (𝓡 3)) ∞
      fun b : B => (b, (1 : S3))).mdifferentiableAt (by simp)
  have hH : MDifferentiableAt (I.prod (𝓡 3)) 𝓘(ℝ) (fun x : B × S3 => h x.1)
      ((trivPB I B).sec b₀ b) := ((hh.comp contMDiff_fst) _).mdifferentiableAt (by simp)
  have hd : dhP h ((trivPB I B).sec b₀ b) (mfderiv I (I.prod (𝓡 3)) ((trivPB I B).sec b₀) b w) =
      mvfderiv I h b w := by
    unfold dhP
    rw [← RiemannianGeometry.mvfderiv_comp_apply hH hs]
    rfl
  have hflat := pot_flat (I := I) b₀ b w
  unfold S3Connection.pot at hflat ⊢
  simp only [potConn, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.mul_apply', ContinuousLinearMap.smul_apply, smul_eq_mul, hd, hflat,
    add_zero]
  rw [show uq ((trivPB I B).sec b₀ b) = 1 from rfl, star_one, one_mul, mul_one]
  rfl

include hf hh in
/-- **The curvature** `F(e₁, e₂) = (e₁f·e₂h − e₂f·e₁h) q`. -/
theorem curvF_potConn (b₀ : B) {e₁ e₂ : Π b : B, TangentSpace I b} {b : B}
    (he₁ : ∀ᶠ z in 𝓝 b, ContMDiffAt I I.tangent ∞ (T% e₁) z)
    (he₂ : ∀ᶠ z in 𝓝 b, ContMDiffAt I I.tangent ∞ (T% e₂) z) :
    (potConn I B hf hh hq).curvF b₀ e₁ e₂ b =
      (mvfderiv I f b (e₁ b) * mvfderiv I h b (e₂ b) -
        mvfderiv I f b (e₂ b) * mvfderiv I h b (e₁ b)) • q := by
  have hpE : ∀ e : Π b : B, TangentSpace I b, (potConn I B hf hh hq).potE b₀ e =
      fun z => (f z * mvfderiv I h z (e z)) • q := fun e => funext fun z => pot_potConn hf hh hq b₀ z (e z)
  set L : ℝ →L[ℝ] Quaternion ℝ := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) q
  have hL : ∀ e : Π b : B, TangentSpace I b, (fun z => (f z * mvfderiv I h z (e z)) • q) =
      L ∘ fun z => f z * mvfderiv I h z (e z) := fun e => funext fun z => by
    simp [L]
  have hdh : ∀ {e : Π b : B, TangentSpace I b}, (∀ᶠ z in 𝓝 b, ContMDiffAt I I.tangent ∞ (T% e) z) →
      MDifferentiableAt I 𝓘(ℝ) (fun z => mvfderiv I h z (e z)) b := fun he =>
    (S3Connection.contMDiffAt_mvfderiv_field (Eventually.of_forall fun z => hh z)
      he.self_of_nhds).mdifferentiableAt (by simp)
  have hfd : MDifferentiableAt I 𝓘(ℝ) f b := (hf b).mdifferentiableAt (by simp)
  have hder : ∀ {e e' : Π b : B, TangentSpace I b},
      (∀ᶠ z in 𝓝 b, ContMDiffAt I I.tangent ∞ (T% e) z) →
      mvfderiv I (fun z => (f z * mvfderiv I h z (e z)) • q) b (e' b) =
        (mvfderiv I f b (e' b) * mvfderiv I h b (e b) +
          f b * mvfderiv I (fun z => mvfderiv I h z (e z)) b (e' b)) • q := by
    intro e e' he
    rw [hL e, mvfderiv_clm_comp L (show MDifferentiableAt I 𝓘(ℝ)
      (fun z => f z * mvfderiv I h z (e z)) b from hfd.mul (hdh he)),
      mvfderiv_mul_real hfd (hdh he)]
    simp only [L, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply]
    congr 1
    ring
  -- `dh([e₁, e₂]) = e₁(dh e₂) − e₂(dh e₁)`
  have hbr := mvfderiv_apply_mlieBracket_of_contMDiffAt (n := 2) (g := h) (x := b)
    (I := I) S3Connection.two_minSmoothness S3Connection.two_ne_infty
    ((hh b).of_le S3Connection.two_le_infty'')
    (he₁.mono fun z hz => hz.of_le S3Connection.two_le_infty'')
    (he₂.mono fun z hz => hz.of_le S3Connection.two_le_infty'')
  unfold S3Connection.curvF
  rw [hpE, hpE, hder he₂, hder he₁, pot_potConn hf hh hq, ← hbr]
  ext <;> simp <;> ring

end Pot

end

end ExoticSpheres8And10
