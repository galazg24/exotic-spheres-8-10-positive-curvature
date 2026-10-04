/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Geometry.SFF.Descent

/-! # §4.4: warped source metrics on `V × S³`, for the boundary analysis

`GW β w = β(dY, dY) + w(Y)²|dU|²` on `V × S³`: a base metric `β` on `V` warped with the round
`S³` by `w`, with the **product** connection. Near the gluing boundary both of [GG]'s source
metrics have this form, in the common northern trivialisation:
- `G_N = GW βN r̃` (`northMetric_eq_GW`);
- the southern product-connection metric `GH 0 r_S = GW (ψR⟪,⟫) r_S` (`GH_zero_eq_GW`).

* `GW_apply`, `isSymm_GW`, `isPosDef_GW`, `isContMDiffMetricSection_GW`;
* `hpull_Φc_GW`: the chart `Φc(Y, z) = (Y, σ3 z)` pulls `GW β w` back to `Gwarp β w`;
* `GsW`, `GW_slice`: the slice form at `(Y, 1)`;
* `GW_starN`: star-invariance, for `ρ`-invariant `β` and `w`.
-/

open RiemannianGeometry Bundle VectorField

namespace ExoticSpheres8And10

open Set Function Filter Topology Real

open scoped Manifold ContDiff RealInnerProductSpace

set_option maxSynthPendingDepth 3

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section GW

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The warped source metric** `β(dY, dY) + w(Y)²|dU|²` on `V × S³`. -/
def GW (β : V → V →L[ℝ] V →L[ℝ] ℝ) (w : V → ℝ) (p : V × S3) :
    TangentSpace (IN V) p →L[ℝ] TangentSpace (IN V) p →L[ℝ] ℝ :=
  letI : NormedAddCommGroup (TangentSpace (IN V) p) := inferInstanceAs (NormedAddCommGroup (V × E3))
  letI : NormedSpace ℝ (TangentSpace (IN V) p) := inferInstanceAs (NormedSpace ℝ (V × E3))
  bil (β p.1) (mvfderiv (IN V) fY p) + (w p.1 ^ 2) • bil (ipL (Quaternion ℝ)) (mvfderiv (IN V) fU p)

theorem GW_apply (β : V → V →L[ℝ] V →L[ℝ] ℝ) (w : V → ℝ) (p : V × S3)
    (v v' : TangentSpace (IN V) p) :
    GW β w p v v' = β p.1 (mvfderiv (IN V) fY p v) (mvfderiv (IN V) fY p v') +
      w p.1 ^ 2 * ⟪mvfderiv (IN V) fU p v, mvfderiv (IN V) fU p v'⟫ := rfl

variable {β : V → V →L[ℝ] V →L[ℝ] ℝ} {w : V → ℝ}

theorem isSymm_GW (hβs : ∀ Y a b, β Y a b = β Y b a) : IsSymm (GW β w) := fun p v v' => by
  rw [GW_apply, GW_apply, hβs, real_inner_comm (mvfderiv (IN V) fU p v)]

theorem isPosDef_GW (hβp : ∀ Y a, a ≠ 0 → 0 < β Y a a) (hβn : ∀ Y a, 0 ≤ β Y a a)
    (hw0 : ∀ Y, w Y ≠ 0) : IsPosDef (GW β w) := fun p v hv => by
  rw [GW_apply, mvfderiv_fY]
  have hw2 : 0 < w p.1 ^ 2 := by have := hw0 p.1; positivity
  by_cases h1 : v.1 = 0
  · have h2 : mvfderiv (IN V) fU p v ≠ 0 := fun h => hv (mvfderiv_fU_injective p h1 h)
    rw [h1]
    simp only [map_zero, ContinuousLinearMap.zero_apply, zero_add]
    have := real_inner_self_pos.2 h2
    positivity
  · have h3 := hβp p.1 _ h1
    have : 0 ≤ ⟪mvfderiv (IN V) fU p v, mvfderiv (IN V) fU p v⟫ := real_inner_self_nonneg
    positivity

theorem isContMDiffMetricSection_GW (hβ : ContDiff ℝ ∞ β) (hw : ContDiff ℝ ∞ w) (m : ℕ∞) :
    IsContMDiffMetricSection (V × E3) m (GW β w) := by
  refine isContMDiffMetricSection_of_scalars (m := m) _ fun x V₁ W₁ hV hW => ?_
  have hmn : ((m : ℕ∞) : ℕ∞ω) + 1 ≤ ∞ := by exact_mod_cast le_top
  have dY : ∀ {U : Π y : V × S3, TangentSpace (IN V) y},
      ContMDiffAt (IN V) (IN V).tangent ((m : ℕ∞) : ℕ∞ω)
        (fun y => (⟨y, U y⟩ : TangentBundle (IN V) (V × S3))) x →
      ContMDiffAt (IN V) 𝓘(ℝ, V) ((m : ℕ∞) : ℕ∞ω) (fun y => mvfderiv (IN V) fY y (U y)) x :=
    fun hU => contMDiffAt_mvfderiv_apply_of_contMDiffOn isOpen_univ (mem_univ x)
      contMDiff_fY.contMDiffOn hmn hU
  have dU : ∀ {U : Π y : V × S3, TangentSpace (IN V) y},
      ContMDiffAt (IN V) (IN V).tangent ((m : ℕ∞) : ℕ∞ω)
        (fun y => (⟨y, U y⟩ : TangentBundle (IN V) (V × S3))) x →
      ContMDiffAt (IN V) 𝓘(ℝ, Quaternion ℝ) ((m : ℕ∞) : ℕ∞ω)
        (fun y => mvfderiv (IN V) fU y (U y)) x :=
    fun hU => contMDiffAt_mvfderiv_apply_of_contMDiffOn isOpen_univ (mem_univ x)
      contMDiff_fU.contMDiffOn hmn hU
  have hβx : ContMDiffAt (IN V) 𝓘(ℝ, V →L[ℝ] V →L[ℝ] ℝ) ((m : ℕ∞) : ℕ∞ω)
      (fun y : V × S3 => β y.1) x :=
    ((hβ.contMDiff.comp contMDiff_fY) x).of_le (by exact_mod_cast le_top)
  have hw2 : ContMDiffAt (IN V) 𝓘(ℝ) ((m : ℕ∞) : ℕ∞ω) (fun y : V × S3 => w y.1 ^ 2) x :=
    ((((hw.pow 2).contMDiff).comp contMDiff_fY) x).of_le (by exact_mod_cast le_top)
  have t1 := (hβx.clm_apply (dY hV)).clm_apply (dY hW)
  have t2 := hw2.mul ((contMDiffAt_const (c := ipL (Quaternion ℝ))).clm_apply (dU hV)
    |>.clm_apply (dU hW))
  exact t1.add t2

variable (β w) in
/-- The slice form of `GW` at `(Y, 1)`: `β(a, b) + w(Y)²⟪Dα, Dβ⟫`. -/
def GsW (Y : V) : V × E3 →L[ℝ] V × E3 →L[ℝ] ℝ :=
  bil (β Y) (ContinuousLinearMap.fst ℝ V E3) +
    (w Y ^ 2) • bil (ipL (Quaternion ℝ)) (Dq.comp (ContinuousLinearMap.snd ℝ V E3))

theorem GsW_apply (Y : V) (u u' : V × E3) :
    GsW β w Y u u' = β Y u.1 u'.1 + w Y ^ 2 * ⟪Dq u.2, Dq u'.2⟫ := by
  simp only [GsW, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, bil_apply,
    ipL_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_eq_mul]

theorem GW_slice (Y : V) (u u' : TangentSpace (IN V) (Y, (1 : S3))) :
    GW β w (Y, 1) u u' = GsW β w Y u u' := by
  rw [GW_apply, mvfderiv_fY, mvfderiv_fY, mvfderiv_fU, mvfderiv_fU]
  exact (GsW_apply Y u u').symm

theorem GsW_symm (hβs : ∀ Y a b, β Y a b = β Y b a) (Y : V) (u u' : V × E3) :
    GsW β w Y u u' = GsW β w Y u' u := by
  rw [GsW_apply, GsW_apply, hβs, real_inner_comm (Dq u'.2)]

theorem GsW_pos (hβp : ∀ Y a, a ≠ 0 → 0 < β Y a a) (hβn : ∀ Y a, 0 ≤ β Y a a)
    (hw0 : ∀ Y, w Y ≠ 0) (Y : V) (u : V × E3) (hu : u ≠ 0) : 0 < GsW β w Y u u := by
  have := isPosDef_GW (w := w) hβp hβn hw0 (Y, 1) (v := u) hu
  exact this.trans_eq (GW_slice Y u u)

theorem contDiff_GsW (hβ : ContDiff ℝ ∞ β) (hw : ContDiff ℝ ∞ w) : ContDiff ℝ ∞ (GsW β w) := by
  rw [contDiff_clm_apply_iff]
  intro u
  rw [contDiff_clm_apply_iff]
  intro u'
  have e : (fun Y => GsW β w Y u u') = fun Y => β Y u.1 u'.1 + w Y ^ 2 * ⟪Dq u.2, Dq u'.2⟫ :=
    funext fun Y => GsW_apply Y u u'
  show ContDiff ℝ ∞ fun Y => GsW β w Y u u'
  rw [e]
  exact ((hβ.clm_apply contDiff_const).clm_apply contDiff_const).add
    ((hw.pow 2).mul contDiff_const)

/-- **`Φc` pulls `GW β w` back to the chart form `Gwarp β w`.** -/
theorem hpull_Φc_GW (p : V × E3) (a b : TangentSpace 𝓘(ℝ, V × E3) p) :
    Gwarp β w p a b = GW β w (Φc p) (mfderiv 𝓘(ℝ, V × E3) (IN V) Φc p a)
      (mfderiv 𝓘(ℝ, V × E3) (IN V) Φc p b) := by
  have hΦ : MDifferentiableAt 𝓘(ℝ, V × E3) (IN V) (Φc (V := V)) p :=
    (contMDiff_Φc p).mdifferentiableAt (by simp)
  have hY : ∀ c : TangentSpace 𝓘(ℝ, V × E3) p, mvfderiv (IN V) fY (Φc p)
      (mfderiv 𝓘(ℝ, V × E3) (IN V) Φc p c) = c.1 := fun c => by
    rw [← mvfderiv_comp' ((contMDiff_fY _).mdifferentiableAt (by simp)) hΦ]
    show mvfderiv 𝓘(ℝ, V × E3) (fun p : V × E3 => p.1) p c = _
    rw [mvfderiv_vs]
    have : fderiv ℝ (fun p : V × E3 => p.1) p = ContinuousLinearMap.fst ℝ V E3 := fderiv_fst
    rw [this]; rfl
  have hU : ∀ c : TangentSpace 𝓘(ℝ, V × E3) p, mvfderiv (IN V) fU (Φc p)
      (mfderiv 𝓘(ℝ, V × E3) (IN V) Φc p c) = dst 1 (ι3 p.2) (ι3 c.2) := fun c => by
    rw [← mvfderiv_comp' ((contMDiff_fU _).mdifferentiableAt (by simp)) hΦ]
    show mvfderiv 𝓘(ℝ, V × E3) (fun p : V × E3 => ((σ3 p.2 : S3) : Quaternion ℝ)) p c = _
    rw [mvfderiv_vs]
    have h : HasFDerivAt (fun p : V × E3 => ((σ3 p.2 : S3) : Quaternion ℝ))
        (((dstL 1 (ι3 p.2)).comp ι3).comp (ContinuousLinearMap.snd ℝ V E3)) p :=
      (hasFDerivAt_val_σ3 p.2).comp p hasFDerivAt_snd
    rw [h.fderiv]; rfl
  rw [GW_apply, hY, hY, hU, hU,
    inner_dst_dst norm_one (inner_ι3_one _) _ _ (inner_ι3_one _) (inner_ι3_one _), inner_ι3]
  have hn : ψR (ι3 p.2) = ψR p.2 := by simp only [ψR, norm_ι3]
  rw [hn]
  exact Gwarp_apply β w p a b

variable {ρV : S3 →* (V ≃ₗᵢ[ℝ] V)}

/-- **Star-invariance of `GW`**, for a `ρ`-invariant base metric and warping function. -/
theorem GW_starN
    (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, V →L[ℝ] V) ∞ fun q : S3 => ((ρV q : V ≃L[ℝ] V) : V →L[ℝ] V))
    (hβρ : ∀ (q : S3) Y a b, β (ρV q Y) (ρV q a) (ρV q b) = β Y a b)
    (hwρ : ∀ q Y, w (ρV q Y) = w Y) (q : S3) (p : V × S3) (v v' : TangentSpace (IN V) p) :
    GW β w (starN ρV q p) (mfderiv (IN V) (IN V) (starN ρV q) p v)
      (mfderiv (IN V) (IN V) (starN ρV q) p v') = GW β w p v v' := by
  have hS : MDifferentiableAt (IN V) (IN V) (starN ρV q) p :=
    (contMDiff_starN hρ q p).mdifferentiableAt (by simp)
  have hY : ∀ y, MDifferentiableAt (IN V) 𝓘(ℝ, V) (fY (V := V)) y := fun y =>
    (contMDiff_fY y).mdifferentiableAt (by simp)
  have hU : ∀ y, MDifferentiableAt (IN V) 𝓘(ℝ, Quaternion ℝ) (fU (V := V)) y := fun y =>
    (contMDiff_fU y).mdifferentiableAt (by simp)
  have eY : fY ∘ starN ρV q = ((ρV q : V ≃L[ℝ] V) : V →L[ℝ] V) ∘ fY := rfl
  have eU : fU ∘ starN ρV q =
      (ContinuousLinearMap.mul ℝ (Quaternion ℝ) (q : Quaternion ℝ)) ∘ fU := by
    funext y; simp [fU, starN]
  have tY : ∀ u : TangentSpace (IN V) p,
      mvfderiv (IN V) fY (starN ρV q p) (mfderiv (IN V) (IN V) (starN ρV q) p u) =
        ρV q (mvfderiv (IN V) fY p u) := fun u => by
    rw [← mvfderiv_comp' (hY _) hS, eY, mvfderiv_clm_comp _ (hY p)]; rfl
  have tU : ∀ u : TangentSpace (IN V) p,
      mvfderiv (IN V) fU (starN ρV q p) (mfderiv (IN V) (IN V) (starN ρV q) p u) =
        (q : Quaternion ℝ) * mvfderiv (IN V) fU p u := fun u => by
    rw [← mvfderiv_comp' (hU _) hS, eU, mvfderiv_clm_comp _ (hU p)]; rfl
  rw [GW_apply, GW_apply, tY, tY, tU, tU, inner_mul_left_unit,
    show (starN ρV q p).1 = ρV q p.1 from rfl, hβρ, hwρ]


end GW

end

end ExoticSpheres8And10
