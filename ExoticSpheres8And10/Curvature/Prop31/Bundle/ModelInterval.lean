/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Curvature.Prop31.Bundle.TrivialBundle
import ExoticSpheres8And10.PolarBundles.AttachingDisks

/-! # A model of the hypotheses of `hly_prop31_global`

The base is the closed interval `B = CDisk 1 1 = [-1, 1]`, a compact manifold **with boundary**,
with the flat metric `g = dt²`, the pullback of the Euclidean metric along `val`. The bundle is
the trivial bundle `B × S³` with the flat connection (`PB_Model`). The warping function is
`φ = −512 t²`.

Then:
* `sec_B ≥ 1` holds vacuously, since `dim B = 1`;
* `Ω = 0` and `DΩ = 0` in every gauge and frame, so `M₀ = M₁ = 0`;
* `−Hess φ = 1024 g` (`hessF_model`), so `Λ = 1024 = 64·0 + 1024·1⁻¹·(0+1)²`.

`hly_prop31_global_model` applies `hly_prop31_global` to this model. Every hypothesis is
discharged, so the hypotheses are satisfiable. The model has genuine boundary, as it must:
on a closed base `−Hess φ ≥ Λ g > 0` is impossible.

The 1-dimensional Hessian computation is general (`hessF_one_dim`). With a unit field `e₀`
and `X = f e₀`, `Hess φ (X, X) = f² e₀(e₀ φ)`, because `∇_{e₀} e₀ = 0`.
-/

open RiemannianGeometry VectorField Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Module

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

section OneDim

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type} [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B]
  {g : Π b : B, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ}
  {e : Fin 1 → Π b : B, TangentSpace I b} {U : Set B} {φ : B → ℝ}
  (hsg : IsSymm g) (hpg : IsPosDef g) (hgs : IsContMDiffMetricSection E ∞ g) (hUo : IsOpen U)
  (he : ∀ i, ∀ b ∈ U, ContMDiffAt I I.tangent ∞ (T% (e i)) b)
  (horthB : ∀ b ∈ U, ∀ i j, g b (e i b) (e j b) = kron i j) (hn : finrank ℝ E = 1)

include hsg hpg hgs hUo he horthB hn in
/-- In dimension 1, `∇_{e₀} e₀ = 0` for a unit field. -/
theorem leviCivita_e0_e0 {b : B} (hb : b ∈ U) : leviCivita g (e 0) b (e 0 b) = 0 := by
  have hgm : IsMDiffMetric E g :=
    (IsContMDiffMetricSection.of_le' hgs two_le_infty_ω).isMDiffMetric (by simp)
  have hFd : ∀ α, ∀ y ∈ U, MDiffAt (T% (e α)) y :=
    fun α y hy => (he α y hy).mdifferentiableAt (by simp)
  have hbr : ∀ α β, ∀ y ∈ U, mlieBracket I (e α) (e β) y =
      ∑ γ, S3Connection.cBb g e α β γ y • e γ y :=
    fun α β y hy => span_base_frame hpg horthB hn hy _
  rw [leviCivita_frame_loc hsg hpg.isNondegenerate hgm hUo hFd (fun α β y hy => horthB y hy α β)
    (fun y hy w => span_base_frame hpg horthB hn hy w) hbr 0 0 hb, Fin.sum_univ_one]
  have hc : S3Connection.cBb g e 0 0 0 b = 0 := by
    simp [S3Connection.cBb, mlieBracket_self]
  simp [frameΓ, hc]

include hsg hpg hgs hUo he horthB hn in
/-- **The Hessian in dimension 1**: `Hess φ (X, X) = g(X, e₀)² · e₀(e₀φ)`. -/
theorem hessF_one_dim (hφ : ContMDiff I 𝓘(ℝ) ∞ φ) {b : B} (hb : b ∈ U)
    (X : Π x : B, TangentSpace I x) (hX : ContMDiffAt I I.tangent ∞ (T% X) b) :
    hessF g φ X X b = g b (X b) (e 0 b) ^ 2 *
      mvfderiv I (fun z => mvfderiv I φ z (e 0 z)) b (e 0 b) := by
  have hgm : IsMDiffMetric E g :=
    (IsContMDiffMetricSection.of_le' hgs two_le_infty_ω).isMDiffMetric (by simp)
  have hf : MDifferentiableAt I 𝓘(ℝ) (fun z => g z (X z) (e 0 z)) b :=
    (contMDiffAt_pairing (hgs b) hX (he 0 b hb)).mdifferentiableAt (by simp)
  have hXe : ∀ z ∈ U, X z = g z (X z) (e 0 z) • e 0 z := fun z hz => by
    have h := span_base_frame hpg horthB hn hz (X z)
    rwa [Fin.sum_univ_one] at h
  have hev : ∀ᶠ z in 𝓝 b, X z = ((fun z => g z (X z) (e 0 z)) • e 0) z := by
    filter_upwards [hUo.mem_nhds hb] with z hz
    exact hXe z hz
  have he0d : MDiffAt (T% (e 0)) b := (he 0 b hb).mdifferentiableAt (by simp)
  have hh0 := mdiffAt_dφ_e he hφ hb 0
  have hT1fun : (fun z => mvfderiv I φ z (X z)) =ᶠ[𝓝 b]
      fun z => g z (X z) (e 0 z) * mvfderiv I φ z (e 0 z) := by
    filter_upwards [hUo.mem_nhds hb] with z hz
    rw [hXe z hz, map_smul, smul_eq_mul, ← hXe z hz]
  obtain ⟨c, hc⟩ : ∃ c, g b (X b) (e 0 b) = c := ⟨_, rfl⟩
  have hXb : X b = c • e 0 b := by rw [← hc]; exact hXe b hb
  have L1 : ∀ L : TangentSpace I b →L[ℝ] ℝ, L (X b) = c * L (e 0 b) := fun L => by
    rw [hXb, map_smul, smul_eq_mul]
  have hT1 : mvfderiv I (fun z => mvfderiv I φ z (X z)) b (X b) =
      c * (c * mvfderiv I (fun z => mvfderiv I φ z (e 0 z)) b (e 0 b)) +
      mvfderiv I φ b (e 0 b) * (c * mvfderiv I (fun z => g z (X z) (e 0 z)) b (e 0 b)) := by
    rw [RiemannianGeometry.mvfderiv_congr_of_eventuallyEq hT1fun,
      mvfderiv_mul_real hf hh0, L1 (mvfderiv I (fun z => mvfderiv I φ z (e 0 z)) b),
      L1 (mvfderiv I (fun z => g z (X z) (e 0 z)) b), hc]
  have hT2 : mvfderiv I φ b (leviCivita g X b (X b)) =
      c * mvfderiv I (fun z => g z (X z) (e 0 z)) b (e 0 b) * mvfderiv I φ b (e 0 b) := by
    rw [leviCivita_congr_of_eventuallyEq hev,
      leviCivita_smul_section hsg hpg.isNondegenerate hgm hf he0d,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, hc, hXb]
    simp only [map_smul, map_add, leviCivita_e0_e0 hsg hpg hgs hUo he horthB hn hb, smul_zero,
      zero_add, smul_eq_mul]
  unfold hessF
  rw [hT1, hT2, hc]
  ring

end OneDim

/-! ## The interval model -/

section Interval

instance fact_zero_lt_one_real : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩

local notation "E1" => EuclideanSpace ℝ (Fin 1)

local notation "Iv" => CDisk 1 (1 : ℝ)

/-- The flat metric `dt²` on the interval, pulled back along `val`. -/
def gIv : Π x : Iv, TangentSpace (𝓡∂ 1) x →L[ℝ] TangentSpace (𝓡∂ 1) x →L[ℝ] ℝ :=
  pullMet (fun _ : E1 => innerSL ℝ) Subtype.val

theorem isSymm_gIv : IsSymm gIv :=
  isSymm_pullMet fun _ a b => by
    show innerSL ℝ a b = innerSL ℝ b a
    rw [innerSL_apply_apply, innerSL_apply_apply, real_inner_comm]

theorem isPosDef_gIv : IsPosDef gIv :=
  isPosDef_pullMet (fun _ a ha => by
    show 0 < innerSL ℝ a a
    rw [innerSL_apply_apply]; exact real_inner_self_pos.2 ha)
    (isInvertible_mfderiv_val_disk 1)

theorem isContMDiffMetricSection_gIv : IsContMDiffMetricSection E1 ∞ gIv :=
  isContMDiffMetricSection_pullMet contDiff_const (contMDiff_val_disk 1)

/-- The coordinate `t`. -/
def tIv (z : Iv) : ℝ := (z.1 : E1) 0

theorem contMDiff_tIv : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ tIv :=
  (EuclideanSpace.proj (0 : Fin 1) : E1 →L[ℝ] ℝ).contMDiff.comp (contMDiff_val_disk 1)

theorem mvfderiv_tIv (z : Iv) (v : TangentSpace (𝓡∂ 1) z) :
    mvfderiv (𝓡∂ 1) tIv z v =
      (EuclideanSpace.proj (0 : Fin 1) : E1 →L[ℝ] ℝ) (mfderiv (𝓡∂ 1) 𝓘(ℝ, E1) Subtype.val z v) := by
  have hv : MDifferentiableAt (𝓡∂ 1) 𝓘(ℝ, E1) (Subtype.val : Iv → E1) z :=
    (contMDiff_val_disk 1 z).mdifferentiableAt (by simp)
  rw [show tIv = (EuclideanSpace.proj (0 : Fin 1) : E1 →L[ℝ] ℝ) ∘ Subtype.val from rfl,
    mvfderiv_clm_comp _ hv v]
  rfl

theorem inner_E1 (x y : E1) : ⟪x, y⟫ = x 0 * y 0 := by
  simp [PiLp.inner_apply, Fin.sum_univ_one, mul_comm]

/-- `g = dt ⊗ dt`. -/
theorem gIv_apply (z : Iv) (u v : TangentSpace (𝓡∂ 1) z) :
    gIv z u v = mvfderiv (𝓡∂ 1) tIv z u * mvfderiv (𝓡∂ 1) tIv z v := by
  rw [mvfderiv_tIv, mvfderiv_tIv]
  show inner ℝ (mfderiv (𝓡∂ 1) 𝓘(ℝ, E1) Subtype.val z u : E1)
    (mfderiv (𝓡∂ 1) 𝓘(ℝ, E1) Subtype.val z v : E1) = _
  exact inner_E1 _ _

/-- The warping function `φ = −512 t²`. -/
def φIv (z : Iv) : ℝ := -512 * tIv z ^ 2

theorem contMDiff_φIv : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ φIv :=
  contMDiff_const.mul (contMDiff_tIv.pow 2)

theorem mvfderiv_φIv (z : Iv) (v : TangentSpace (𝓡∂ 1) z) :
    mvfderiv (𝓡∂ 1) φIv z v = -1024 * tIv z * mvfderiv (𝓡∂ 1) tIv z v := by
  have ht : MDifferentiableAt (𝓡∂ 1) 𝓘(ℝ) tIv z := (contMDiff_tIv z).mdifferentiableAt (by simp)
  rw [show φIv = fun z => -512 * (tIv z * tIv z) from funext fun z => by simp [φIv, sq],
    mvfderiv_const_mul_real (f := fun z => tIv z * tIv z) (ht.mul ht), mvfderiv_mul_real ht ht]
  ring

/-- **`−Hess φ = 1024 g`** on the interval, for every smooth field. -/
theorem hessF_model (b : Iv) (X : Π x : Iv, TangentSpace (𝓡∂ 1) x)
    (hX : ContMDiffAt (𝓡∂ 1) (𝓡∂ 1).tangent ∞ (T% X) b) :
    1024 * gIv b (X b) (X b) ≤ -hessF gIv φIv X X b := by
  have hn : finrank ℝ E1 = 1 := finrank_euclideanSpace_fin
  obtain ⟨U, hUo, hbU, e, he, hor⟩ :=
    exists_orthonormal_frame_near isSymm_gIv isPosDef_gIv isContMDiffMetricSection_gIv hn b
  rw [hessF_one_dim isSymm_gIv isPosDef_gIv isContMDiffMetricSection_gIv hUo he hor hn
    contMDiff_φIv hbU X hX]
  -- `w = dt(e₀)` has `w² = 1` near `b`, so `e₀(w) = 0`
  set w : Iv → ℝ := fun z => mvfderiv (𝓡∂ 1) tIv z (e 0 z) with hwdef
  have hw1 : ∀ z ∈ U, w z * w z = 1 := fun z hz => by
    have h := hor z hz 0 0
    rw [gIv_apply] at h
    simpa [kron] using h
  have hwd : MDifferentiableAt (𝓡∂ 1) 𝓘(ℝ) w b :=
    (S3Connection.contMDiffAt_mvfderiv_field (Eventually.of_forall fun z => contMDiff_tIv z)
      (he 0 b hbU)).mdifferentiableAt (by simp)
  have hdw : mvfderiv (𝓡∂ 1) w b (e 0 b) = 0 := by
    have hc : (fun z => w z * w z) =ᶠ[𝓝 b] fun _ => (1 : ℝ) := by
      filter_upwards [hUo.mem_nhds hbU] with z hz using hw1 z hz
    have h := mvfderiv_mul_real hwd hwd (e 0 b)
    rw [RiemannianGeometry.mvfderiv_congr_of_eventuallyEq hc, mvfderiv_const_real] at h
    have hb1 := hw1 b hbU
    have hne : w b ≠ 0 := fun h0 => by rw [h0, zero_mul] at hb1; exact zero_ne_one hb1
    have h2 : w b * mvfderiv (𝓡∂ 1) w b (e 0 b) = 0 := by linarith
    exact (mul_eq_zero.1 h2).resolve_left hne
  -- `e₀(φ) = −1024 t w`, so `e₀(e₀φ) = −1024`
  have ht : MDifferentiableAt (𝓡∂ 1) 𝓘(ℝ) tIv b := (contMDiff_tIv b).mdifferentiableAt (by simp)
  have hfun : (fun z => mvfderiv (𝓡∂ 1) φIv z (e 0 z)) = fun z => -1024 * (tIv z * w z) :=
    funext fun z => by rw [mvfderiv_φIv]; ring
  have hee : mvfderiv (𝓡∂ 1) (fun z => mvfderiv (𝓡∂ 1) φIv z (e 0 z)) b (e 0 b) = -1024 := by
    rw [hfun, mvfderiv_const_mul_real (f := fun z => tIv z * w z) (ht.mul hwd),
      mvfderiv_mul_real ht hwd, hdw]
    have : mvfderiv (𝓡∂ 1) tIv b (e 0 b) = w b := rfl
    rw [this, hw1 b hbU]
    ring
  rw [hee]
  -- `g(X, X) = g(X, e₀)²`
  have hXe : X b = gIv b (X b) (e 0 b) • e 0 b := by
    have h := span_base_frame isPosDef_gIv hor hn hbU (X b)
    rwa [Fin.sum_univ_one] at h
  have hgX : gIv b (X b) (X b) = gIv b (X b) (e 0 b) ^ 2 := by
    conv_lhs => rw [hXe]
    rw [map_smul, map_smul, ContinuousLinearMap.smul_apply, hor b hbU 0 0]
    simp [kron, sq]
  rw [hgX]
  linarith

/-- In dimension 1 there are no 2-planes, so `sec ≥ κ` holds for every `κ`. -/
theorem sec_model_vacuous (κ : ℝ) (b : Iv) (u v : TangentSpace (𝓡∂ 1) b)
    (h : LinearIndependent ℝ ![u, v]) :
    κ ≤ sectionalCurvatureAt isSymm_gIv isPosDef_gIv
      (IsContMDiffMetricSection.of_le' isContMDiffMetricSection_gIv two_le_infty_ω) b u v := by
  exfalso
  haveI : FiniteDimensional ℝ (TangentSpace (𝓡∂ 1) b) := inferInstanceAs (FiniteDimensional ℝ E1)
  have h1 := h.fintype_card_le_finrank
  have h2 : finrank ℝ (TangentSpace (𝓡∂ 1) b) = 1 := finrank_euclideanSpace_fin
  rw [h2, Fintype.card_fin] at h1
  omega

/-- **Non-vacuity of `hly_prop31_global`.** On the interval model (base with boundary, trivial
bundle, flat connection, `φ = −512 t²`), every hypothesis holds. So the conclusion holds too:
for small `ε`, `G_ε` has positive sectional curvature on `[-1, 1] × S³`, boundary included. -/
theorem hly_prop31_global_model :
    ∃ ε₀ > 0, ∀ (ε : ℝ) (hε : 0 < ε), ε < ε₀ →
      ∀ (y : Iv × S3) (u v : TangentSpace ((𝓡∂ 1).prod (𝓡 3)) y), LinearIndependent ℝ ![u, v] →
        0 < sectionalCurvatureAt ((flatConn (𝓡∂ 1) Iv).isSymm_connMetric isSymm_gIv φIv ε)
          ((flatConn (𝓡∂ 1) Iv).isPosDef_connMetric isPosDef_gIv φIv hε)
          (IsContMDiffMetricSection.of_le'
            ((flatConn (𝓡∂ 1) Iv).isContMDiffMetricSection_connMetric
              isContMDiffMetricSection_gIv contMDiff_φIv ε) two_le_infty_ω) y u v := by
  refine hly_prop31_global (n := 1) isSymm_gIv isPosDef_gIv isContMDiffMetricSection_gIv
    finrank_euclideanSpace_fin one_pos (sec_model_vacuous 1) (flatConn (𝓡∂ 1) Iv)
    contMDiff_φIv (M0 := 0) (M1 := 0) (Λ := 1024) le_rfl le_rfl ?_ ?_ hessF_model (by norm_num)
  · intro b₀ U e _ _ _ _ y _
    rw [OmSq_flat]; norm_num
  · intro b₀ U e _ _ _ _ y _
    simp only [DΩP_flat]; norm_num

end Interval

end

end ExoticSpheres8And10
