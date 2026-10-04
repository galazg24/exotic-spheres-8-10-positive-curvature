/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Geometry.Pullback
import RiemannianGeometry.SectionalCurvature
import ExoticSpheres8And10.PolarBundles.PolarBundle
import ExoticSpheres8And10.Analysis.ParametricIntegral

/-! # §4: the northern metric on `V × S³`, smooth at the centre

[GG]'s northern metric is `G_N = ds² + F(s)² h_{S^{n−1}} + r(s)² h_{S³}` with
`F' = e^{−F²/(2δ²)}`. In the coordinate `Y ∈ V` with `|Y| = F(s)`, `Y/|Y| = x`, one has
`ds = e^{F²/2δ²} dF`, so

  `G_N = |dY|² + ψ(|Y|²) ⟪Y, dY⟫² + r̃(Y)² |du|²`, `ψ(w) = (e^{w/δ²} − 1)/w`,

with `ψ` entire. This expression is **manifestly smooth at the centre `Y = 0`**, and it is how the
northern metric is defined here, on the manifold `V × S³`.

* `ψδ`: `ψ(w) = δ⁻² ∫₀¹ e^{tw/δ²} dt`, smooth and `≥ 0`, with `w ψ(w) = e^{w/δ²} − 1`;
* `northMetric δ r̃`: the metric; `isContMDiffMetricSection_northMetric`, `isSymm_northMetric`,
  `isPosDef_northMetric`.
-/

open RiemannianGeometry Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Real

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

/-! ### The entire function `ψ` -/

/-- `ψ(w) = δ⁻² ∫₀¹ e^{tw/δ²} dt = (e^{w/δ²} − 1)/w`. -/
def ψδ (δ w : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, Real.exp (t * w / δ ^ 2) / δ ^ 2

theorem contDiff_ψδ (δ : ℝ) : ContDiff ℝ ∞ (ψδ δ) := by
  have : ContDiff ℝ ∞ fun p : ℝ × ℝ => Real.exp (p.1 * p.2 / δ ^ 2) / δ ^ 2 := by fun_prop
  exact contDiff_intervalIntegral_param_infty this 0 1

theorem ψδ_nonneg (δ w : ℝ) : 0 ≤ ψδ δ w :=
  intervalIntegral.integral_nonneg zero_le_one fun t _ => by positivity

theorem mul_ψδ {δ : ℝ} (hδ : δ ≠ 0) (w : ℝ) : w * ψδ δ w = Real.exp (w / δ ^ 2) - 1 := by
  unfold ψδ
  rw [← intervalIntegral.integral_const_mul]
  have hd : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun t => Real.exp (t * w / δ ^ 2))
      (w * (Real.exp (t * w / δ ^ 2) / δ ^ 2)) t := fun t _ => by
    have h := (((hasDerivAt_id t).mul_const w).div_const (δ ^ 2)).exp
    refine h.congr_deriv ?_
    simp only [id]; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · simp
  · exact (by fun_prop : Continuous fun t : ℝ => w * (Real.exp (t * w / δ ^ 2) / δ ^ 2)).intervalIntegrable _ _

/-! ### The metric on `V × S³` -/

section Model

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The model `V × ℝ³` of `V × S³`. -/
abbrev IN (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] :=
  (𝓘(ℝ, V)).prod (𝓡 3)

/-- The inner product of a real inner product space, as a bilinear map. -/
def ipL (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℝ K] : K →L[ℝ] K →L[ℝ] ℝ := innerSL ℝ

@[simp] theorem ipL_apply {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℝ K] (a b : K) :
    ipL K a b = ⟪a, b⟫ := rfl

/-- Multiplication on `ℝ`, as a bilinear map. -/
def mulL : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.mul ℝ ℝ

@[simp] theorem mulL_apply (a b : ℝ) : mulL a b = a * b := rfl

/-- The coordinate `Y`. -/
def fY (p : V × S3) : V := p.1

/-- `|Y|²/2`. -/
def fQ (p : V × S3) : ℝ := ‖p.1‖ ^ 2 / 2

/-- The fibre coordinate `u ∈ S³ ⊂ ℍ`. -/
def fU (p : V × S3) : Quaternion ℝ := (p.2 : Quaternion ℝ)

theorem contMDiff_fY : ContMDiff (IN V) 𝓘(ℝ, V) ∞ (fY (V := V)) := contMDiff_fst

theorem contMDiff_fQ : ContMDiff (IN V) 𝓘(ℝ, ℝ) ∞ (fQ (V := V)) := by
  have : ContDiff ℝ ∞ fun y : V => ‖y‖ ^ 2 / 2 := (contDiff_norm_sq ℝ).div_const 2
  exact this.contMDiff.comp contMDiff_fst

theorem contMDiff_fU : ContMDiff (IN V) 𝓘(ℝ, Quaternion ℝ) ∞ (fU (V := V)) :=
  contMDiff_coe_sphere.comp contMDiff_snd

/-- **[GG]'s northern metric** `|dY|² + ψ(|Y|²)⟪Y,dY⟫² + r̃(Y)²|du|²` on `V × S³`. -/
def northMetric (δ : ℝ) (rt : V → ℝ) :
    Π p : V × S3, TangentSpace (IN V) p →L[ℝ] TangentSpace (IN V) p →L[ℝ] ℝ :=
  pullTerm (I := IN V) (fun _ => 1) (ipL V) fY +
    pullTerm (I := IN V) (fun p => ψδ δ (‖p.1‖ ^ 2)) mulL fQ +
    pullTerm (I := IN V) (fun p => rt p.1 ^ 2) (ipL (Quaternion ℝ)) fU

theorem northMetric_apply (δ : ℝ) (rt : V → ℝ) (p : V × S3) (v w : TangentSpace (IN V) p) :
    northMetric δ rt p v w =
      ⟪mvfderiv (IN V) fY p v, mvfderiv (IN V) fY p w⟫ +
      ψδ δ (‖p.1‖ ^ 2) * (mvfderiv (IN V) fQ p v * mvfderiv (IN V) fQ p w) +
      rt p.1 ^ 2 * ⟪mvfderiv (IN V) fU p v, mvfderiv (IN V) fU p w⟫ := by
  simp only [northMetric, Pi.add_apply, ContinuousLinearMap.add_apply, pullTerm_apply, ipL_apply,
    mulL_apply, one_mul]

theorem isContMDiffMetricSection_northMetric {δ : ℝ} {rt : V → ℝ} (hrt : ContDiff ℝ ∞ rt)
    (m : ℕ∞) : IsContMDiffMetricSection (V × EuclideanSpace ℝ (Fin 3)) m (northMetric δ rt) := by
  refine isContMDiffMetricSection_of_scalars _ fun x V₁ W₁ hV hW => ?_
  have h1 := contMDiffAt_pullTerm_apply (I := IN V) (c := fun _ => (1 : ℝ)) (ipL V)
    contMDiff_const contMDiff_fY hV hW
  have hψ : ContMDiff (IN V) 𝓘(ℝ) ∞ fun p : V × S3 => ψδ δ (‖p.1‖ ^ 2) :=
    ((contDiff_ψδ δ).comp (contDiff_norm_sq ℝ)).contMDiff.comp contMDiff_fst
  have h2 := contMDiffAt_pullTerm_apply (I := IN V) mulL hψ contMDiff_fQ hV hW
  have hr : ContMDiff (IN V) 𝓘(ℝ) ∞ fun p : V × S3 => rt p.1 ^ 2 :=
    (hrt.pow 2).contMDiff.comp contMDiff_fst
  have h3 := contMDiffAt_pullTerm_apply (I := IN V) (ipL (Quaternion ℝ)) hr contMDiff_fU hV hW
  exact (h1.add h2).add h3

theorem isSymm_northMetric (δ : ℝ) (rt : V → ℝ) : IsSymm (northMetric δ rt) := fun p v w => by
  rw [northMetric_apply, northMetric_apply, real_inner_comm (mvfderiv (IN V) fY p v),
    real_inner_comm (mvfderiv (IN V) fU p v), mul_comm (mvfderiv (IN V) fQ p v)]

theorem mvfderiv_fY (p : V × S3) (v : TangentSpace (IN V) p) :
    mvfderiv (IN V) fY p v = v.1 := by
  have h : mfderiv (IN V) 𝓘(ℝ, V) (fY (V := V)) p =
      ContinuousLinearMap.fst ℝ V (EuclideanSpace ℝ (Fin 3)) := mfderiv_fst
  simp only [mvfderiv, ContinuousLinearMap.comp_apply, h]
  rfl

theorem mvfderiv_fU_injective (p : V × S3) {v : TangentSpace (IN V) p}
    (h1 : v.1 = 0) (h2 : mvfderiv (IN V) fU p v = 0) : v = 0 := by
  have hc : MDifferentiableAt (𝓡 3) 𝓘(ℝ, Quaternion ℝ) (Subtype.val : S3 → Quaternion ℝ) p.2 :=
    ((contMDiff_coe_sphere (m := 1)) p.2).mdifferentiableAt one_ne_zero
  have hs : MDifferentiableAt (IN V) (𝓡 3) (Prod.snd : V × S3 → S3) p :=
    ((contMDiff_snd (n := 1)) p).mdifferentiableAt one_ne_zero
  have h : mfderiv (IN V) 𝓘(ℝ, Quaternion ℝ) (fU (V := V)) p =
      (mfderiv (𝓡 3) 𝓘(ℝ, Quaternion ℝ) (Subtype.val : S3 → Quaternion ℝ) p.2).comp
        (mfderiv (IN V) (𝓡 3) (Prod.snd : V × S3 → S3) p) := mfderiv_comp p hc hs
  have hcomp : mvfderiv (IN V) fU p v =
      mvfderiv (𝓡 3) (Subtype.val : S3 → Quaternion ℝ) p.2 v.2 := by
    simp only [mvfderiv, ContinuousLinearMap.comp_apply, h, mfderiv_snd]
    rfl
  rw [hcomp] at h2
  have h2' : v.2 = 0 :=
    injective_mvfderiv_subtypeVal_sphere p.2 (h2.trans (map_zero _).symm)
  exact Prod.ext h1 h2'

theorem isPosDef_northMetric (δ : ℝ) {rt : V → ℝ} (hrt : ∀ Y, rt Y ≠ 0) :
    IsPosDef (northMetric δ rt) := fun p v hv => by
  rw [northMetric_apply, mvfderiv_fY]
  have hψ := ψδ_nonneg δ (‖p.1‖ ^ 2)
  have hr2 : 0 < rt p.1 ^ 2 := by have := hrt p.1; positivity
  by_cases h1 : v.1 = 0
  · have h2 : mvfderiv (IN V) fU p v ≠ 0 := fun h => hv (mvfderiv_fU_injective p h1 h)
    rw [h1]
    have := real_inner_self_pos.2 h2
    simp only [inner_zero_left, zero_add]
    nlinarith [mul_self_nonneg (mvfderiv (IN V) fQ p v)]
  · have := real_inner_self_pos.2 h1
    nlinarith [mul_self_nonneg (mvfderiv (IN V) fQ p v),
      real_inner_self_nonneg (x := mvfderiv (IN V) fU p v)]

end Model

end

end ExoticSpheres8And10
