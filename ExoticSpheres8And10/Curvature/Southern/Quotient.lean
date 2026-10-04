/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Curvature.StarQuotientMetric
import ExoticSpheres8And10.Curvature.Southern.Cap

/-! # §4, the southern filling: the quotient disk `D_S` has positive curvature

The connection metric `GH` on `V × S³` is star-invariant when:
- the potential is equivariant, `A(ρ(q)y)(ρ(q)a) = q A(y)(a) q⁻¹` ([GG]: `ρ(q)^*A = qAq⁻¹`);
- the radius is `ρ`-invariant.

Its slice form at `(Y, 1)` is `GsH Y`. So the generic star quotient (`S4_StarQuot`) applies, and
O'Neill carries `southern_cap_pos` down to the quotient metric on `V ≅ D_S` (via the slice
`Y ↦ [(Y, 1)]`).

* `GH_slice`, `GsH_symm`, `GsH_pos`, `contDiff_GsH`: the slice form;
* `GH_starN`: star-invariance of `GH`;
* **`southern_quotient_pos`**: [GG]'s `sec_{g_S} > 0` on the southern cap.
-/

open RiemannianGeometry Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Real

open scoped Manifold ContDiff RealInnerProductSpace

set_option maxSynthPendingDepth 3

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section SouthQuot

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ρV : S3 →* (V ≃ₗᵢ[ℝ] V)}
  (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, V →L[ℝ] V) ∞ fun q : S3 => ((ρV q : V ≃L[ℝ] V) : V →L[ℝ] V))
  {A : V → V →L[ℝ] Quaternion ℝ} {r : V → ℝ}

variable (A r) in
/-- The connection metric at the slice point `(Y, 1)`:
`ψ(Y)⟪a, b⟫ + r(Y)²⟪A(Y)a + Dα, A(Y)b + Dβ⟫`. -/
def GsH (Y : V) : V × E3 →L[ℝ] V × E3 →L[ℝ] ℝ :=
  ψR Y • bil (ipL V) (ContinuousLinearMap.fst ℝ V E3) +
    (r Y ^ 2) • bil (ipL (Quaternion ℝ))
      ((A Y).comp (ContinuousLinearMap.fst ℝ V E3) + Dq.comp (ContinuousLinearMap.snd ℝ V E3))

theorem GsH_apply (Y : V) (u w : V × E3) :
    GsH A r Y u w = ψR Y * ⟪u.1, w.1⟫ + r Y ^ 2 * ⟪A Y u.1 + Dq u.2, A Y w.1 + Dq w.2⟫ := by
  simp only [GsH, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, bil_apply,
    ipL_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_eq_mul]

theorem GH_slice (Y : V) (u w : TangentSpace (IN V) (Y, (1 : S3))) :
    GH A r (Y, 1) u w = GsH A r Y u w := by
  rw [GH_apply, θL_apply, θL_apply, mvfderiv_fY, mvfderiv_fY, mvfderiv_fU, mvfderiv_fU]
  refine Eq.trans ?_ (GsH_apply Y u w).symm
  have h1 : (((Y, (1 : S3)) : V × S3).2 : Quaternion ℝ) = 1 := rfl
  rw [h1, mul_one, mul_one]
  rfl

theorem GsH_symm (Y : V) (u w : V × E3) : GsH A r Y u w = GsH A r Y w u := by
  rw [GsH_apply, GsH_apply, real_inner_comm w.1 u.1, real_inner_comm (A Y w.1 + Dq w.2)]

theorem GsH_pos (hr0 : ∀ x, r x ≠ 0) (Y : V) (u : V × E3) (hu : u ≠ 0) : 0 < GsH A r Y u u := by
  have := isPosDef_GH (A := A) hr0 (Y, 1) (v := u) hu
  exact this.trans_eq (GH_slice Y u u)

theorem conj_mul_cancel {q : Quaternion ℝ} (hq : q ≠ 0) (x y : Quaternion ℝ) :
    q * x * q⁻¹ * (q * y) = q * (x * y) := by
  rw [mul_assoc (q * x), ← mul_assoc q⁻¹, inv_mul_cancel₀ hq, one_mul, mul_assoc]

theorem contDiff_GsH (hA : ContDiff ℝ ∞ A) (hr : ContDiff ℝ ∞ r) : ContDiff ℝ ∞ (GsH A r) := by
  rw [contDiff_clm_apply_iff]
  intro u
  rw [contDiff_clm_apply_iff]
  intro w
  have e : (fun Y => GsH A r Y u w) = fun Y =>
      ψR Y * ⟪u.1, w.1⟫ + r Y ^ 2 * ⟪A Y u.1 + Dq u.2, A Y w.1 + Dq w.2⟫ :=
    funext fun Y => GsH_apply Y u w
  show ContDiff ℝ ∞ fun Y => GsH A r Y u w
  rw [e]
  exact (contDiff_ψR.mul contDiff_const).add ((hr.pow 2).mul
    (((hA.clm_apply contDiff_const).add contDiff_const).inner ℝ
      ((hA.clm_apply contDiff_const).add contDiff_const)))

theorem ψR_ρ (q : S3) (Y : V) : ψR (ρV q Y) = ψR Y := by
  simp [ψR, LinearIsometryEquiv.norm_map]

include hρ in
/-- **Star-invariance of the connection metric.** -/
theorem GH_starN (hAeq : ∀ (q : S3) (y a : V), A (ρV q y) (ρV q a) =
      (q : Quaternion ℝ) * A y a * (q : Quaternion ℝ)⁻¹)
    (hrρ : ∀ q Y, r (ρV q Y) = r Y) (q : S3) (p : V × S3) (v w : TangentSpace (IN V) p) :
    GH A r (starN ρV q p) (mfderiv (IN V) (IN V) (starN ρV q) p v)
      (mfderiv (IN V) (IN V) (starN ρV q) p w) = GH A r p v w := by
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
  have hq : (q : Quaternion ℝ) ≠ 0 := by
    intro h; have := mem_sphere_zero_iff_norm.1 q.2; rw [h, norm_zero] at this; norm_num at this
  have tθ : ∀ u : TangentSpace (IN V) p,
      θL A (starN ρV q p) (mfderiv (IN V) (IN V) (starN ρV q) p u) =
        (q : Quaternion ℝ) * θL A p u := fun u => by
    rw [θL_apply, θL_apply, tY, tU]
    have e2 : ((starN ρV q p).2 : Quaternion ℝ) = (q : Quaternion ℝ) * (p.2 : Quaternion ℝ) := by
      simp [starN]
    rw [e2, show (starN ρV q p).1 = ρV q p.1 from rfl, hAeq, conj_mul_cancel hq, mul_add]
  rw [GH_apply, GH_apply, tY, tY, tθ, tθ, LinearIsometryEquiv.inner_map_map, inner_mul_left_unit,
    show (starN ρV q p).1 = ρV q p.1 from rfl, ψR_ρ, hrρ]

theorem rSy_ρ (ε A0 : ℝ) (q : S3) (Y : V) : rSy ε A0 (ρV q Y) = rSy ε A0 Y := by
  simp [rSy, φS, LinearIsometryEquiv.norm_map]

include hρ in
/-- **[GG] §4: the southern quotient disk has positive curvature.** Take:
- a smooth orthogonal star representation `ρ` on `V`;
- a smooth, imaginary, star-equivariant connection potential `A` on the southern chart;
- the cap `−cos t ≥ c₀ > 0`.

Then [GG]'s parameter order `Λ ≥ Λ₀`, `A₀c₀ ≥ Λ`, `0 < ε < ε_S` makes the quotient metric `g_S`
of `(V × S³, G_S)` by the star action have positive `RiemannianGeometry` sectional curvature on every plane at
every point of the cap. -/
theorem southern_quotient_pos (hA : ContDiff ℝ ∞ A) (hAim : ∀ x v, (A x v).re = 0)
    (hAeq : ∀ (q : S3) (y a : V), A (ρV q y) (ρV q a) =
      (q : Quaternion ℝ) * A y a * (q : Quaternion ℝ)⁻¹) {c0 : ℝ} (hc0 : 0 < c0) :
    ∃ Λ0 : ℝ, ∀ Λ, Λ0 ≤ Λ → ∀ A0 : ℝ, 0 ≤ A0 → Λ ≤ A0 * c0 →
      ∃ εS > 0, ∀ ε (hε : 0 < ε), ε < εS → ∀ Y ∈ capS (K := V) c0,
        ∀ a c : TangentSpace 𝓘(ℝ, V) Y, LinearIndependent ℝ ![a, c] →
          0 < sectionalCurvatureAt (SQ.isSymm_cmet_gB' (ρV := ρV) (GsH_symm (A := A)))
            (SQ.isPosDef_cmet_gB' (GsH_pos (A := A) fun x => (rSy_pos hε A0 x).ne'))
            (isContMDiffMetricSection_cmet ((SQ.contDiff_gB ρV
              (GsH_pos (A := A) fun x => (rSy_pos hε A0 x).ne')
              (contDiff_GsH hA (contDiff_rSy ε A0))).of_le two_le_top_nat)) Y a c := by
  obtain ⟨Λ0, h⟩ := southern_cap_pos (K := V) hA hAim hc0
  refine ⟨Λ0, fun Λ hΛ A0 hA0 hΛA => ?_⟩
  obtain ⟨εS, hεS, h'⟩ := h Λ hΛ A0 hA0 hΛA
  refine ⟨εS, hεS, fun ε hε hεε Y hY a c hac => ?_⟩
  exact SQ.quot_sectionalCurvature_pos hρ (GsH_symm (A := A))
    (GsH_pos (A := A) fun x => (rSy_pos hε A0 x).ne') (contDiff_GsH hA (contDiff_rSy ε A0))
    isSymm_GH (isPosDef_GH fun x => (rSy_pos hε A0 x).ne')
    (isContMDiffMetricSection_GH hA (contDiff_rSy ε A0)) GH_slice
    (GH_starN hρ hAeq (rSy_ρ ε A0)) Y
    (fun u v _ _ hli => h' ε hε hεε Y hY 1 u v hli) a c hac

omit [FiniteDimensional ℝ V] in
/-- The hypotheses of `southern_quotient_pos` are satisfiable: the trivial star representation,
the flat potential, and `c₀ = 1/2`. The cap then contains the south pole. -/
theorem southern_quotient_hyps_satisfiable :
    ContMDiff (𝓡 3) 𝓘(ℝ, V →L[ℝ] V) ∞
        (fun q : S3 => (((1 : S3 →* (V ≃ₗᵢ[ℝ] V)) q : V ≃L[ℝ] V) : V →L[ℝ] V)) ∧
      ContDiff ℝ ∞ (A0 (K := V)) ∧ (∀ x v, (A0 (K := V) x v).re = 0) ∧
      (∀ (q : S3) (y a : V), A0 ((1 : S3 →* (V ≃ₗᵢ[ℝ] V)) q y) ((1 : S3 →* (V ≃ₗᵢ[ℝ] V)) q a) =
        (q : Quaternion ℝ) * A0 y a * (q : Quaternion ℝ)⁻¹) ∧ (0 : ℝ) < 1 / 2 := by
  refine ⟨?_, contDiff_const, fun _ _ => rfl, fun q y a => ?_, by norm_num⟩
  · have e : (fun q : S3 => (((1 : S3 →* (V ≃ₗᵢ[ℝ] V)) q : V ≃L[ℝ] V) : V →L[ℝ] V)) =
        fun _ => ContinuousLinearMap.id ℝ _ := by
      funext q; ext v; simp
    rw [e]; exact contMDiff_const
  · simp [A0]

end SouthQuot

end

end ExoticSpheres8And10
