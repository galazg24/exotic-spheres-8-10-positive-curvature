/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Curvature.Gluing.RWHypotheses

/-! # [GG] `thm:HLYgeneral`: `P_θ/S³_⋆` carries a metric of positive sectional curvature

**`hly_general`**: for every polar datum `D` with `‖K_y‖ ≤ 2` on unit vectors, the
Reiser–Wraith gluing theorem (`RWGluing`, a hypothesis) gives a smooth metric of positive
sectional curvature on `X = QuotSpace D = P_θ/S³_⋆`.

The parameters are chosen as in [GG]:
- `ρ₀ = 1`, so `c₀ = 3/5`, `F_a = 4/5` and `|cos a| = 3/5`;
- a cutoff `χ` with `χ = 1` near `0` and `χ = 0` on `[1/4·2, ∞)`;
- `A₀` from [HLY]'s Prop. 3.1 as proved in `southern_quotient_pos_D`;
- `δ` small for the north;
- `ε` small for both.

`compactSpace_quotSpace`: `X` is compact, being the union of the images of the two closed
hemispheres.
-/

open RiemannianGeometry Bundle VectorField

namespace ExoticSpheres8And10

open Set Function Filter Topology Module PolarData

open scoped Manifold ContDiff RealInnerProductSpace

set_option maxSynthPendingDepth 3

noncomputable section

section HLYGeneral

variable {m : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] {e : W} [Fact (finrank ℝ (Vs e) = m + 1)]
  (D : PolarData (m := m) e)

local notation "Sn" => Metric.sphere (0 : W) 1

namespace PolarData

theorem isCompact_hemi (he : ‖e‖ = 1) : IsCompact {z : UN e | 0 ≤ ⟪ζU z, e⟫} := by
  have hemb : Topology.IsEmbedding (Subtype.val : UN e → Sn) := Topology.IsEmbedding.subtypeVal
  rw [hemb.isCompact_iff]
  have : Subtype.val '' {z : UN e | 0 ≤ ⟪ζU z, e⟫} = {w : Sn | 0 ≤ ⟪(w : W), e⟫} := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩; exact hz
    · intro hw
      refine ⟨⟨w, ?_⟩, hw, rfl⟩
      show (w : W) ≠ -e
      intro h
      rw [Set.mem_setOf_eq, h, inner_neg_left, real_inner_self_eq_norm_sq, he] at hw
      norm_num at hw
  rw [this]
  exact (isClosed_le continuous_const (continuous_subtype_val.inner continuous_const)).isCompact

/-- **`X = P_θ/S³_⋆` is compact.** -/
theorem compactSpace_quotSpace : CompactSpace (QuotSpace D) := by
  haveI := nontrivial_of_polarData D
  refine ⟨?_⟩
  have hu : (univ : Set (QuotSpace D)) =
      ι₁ D.κS '' {z : UN e | 0 ≤ ⟪ζU z, e⟫} ∪ ι₂ D.κS '' {z : UN e | 0 ≤ ⟪ζU z, e⟫} := by
    refine (eq_univ_of_forall fun x => ?_).symm
    induction x using glued_induction with
    | h₁ a =>
      by_cases ha : 0 ≤ ⟪ζU a, e⟫
      · exact Or.inl ⟨a, ha, rfl⟩
      · have hsrc : a ∈ D.κS.source := by
          intro h; apply ha; rw [h, real_inner_self_eq_norm_sq, D.e_norm]; norm_num
        refine Or.inr ⟨D.κS a, ?_, ι₂_apply hsrc⟩
        have h1 : D.fX (ι₂ D.κS (D.κS a)) = D.fX (ι₁ D.κS a) := by rw [ι₂_apply hsrc]
        rw [fX_ι₂, fX_ι₁] at h1
        show 0 ≤ ⟪ζU (D.κS a), e⟫
        linarith
    | h₂ b =>
      by_cases hb : 0 ≤ ⟪ζU b, e⟫
      · exact Or.inr ⟨b, hb, rfl⟩
      · have htgt : b ∈ D.κS.target := by
          intro h; apply hb; rw [h, real_inner_self_eq_norm_sq, D.e_norm]; norm_num
        refine Or.inl ⟨D.κS.symm b, ?_, ι₂_symm htgt⟩
        have h1 : D.fX (ι₁ D.κS (D.κS.symm b)) = D.fX (ι₂ D.κS b) := by rw [ι₂_symm htgt]
        rw [fX_ι₂, fX_ι₁] at h1
        show 0 ≤ ⟪ζU (D.κS.symm b), e⟫
        linarith
  rw [hu]
  exact ((isCompact_hemi D.e_norm).image (continuous_ι₁ D.κS)).union
    ((isCompact_hemi D.e_norm).image (continuous_ι₂ D.κS))

end PolarData

attribute [instance] PolarData.compactSpace_quotSpace

/-- [GG]'s southern cutoff: `χ = 1` on `s < 1/4`, `χ = 0` on `s ≥ 1/2`. -/
def χD (s : ℝ) : ℝ := 1 - Real.smoothTransition (4 * s - 1)

theorem isSouthCutoff_χD : IsSouthCutoff χD := by
  refine ⟨contDiff_const.sub (Real.smoothTransition.contDiff.comp (by fun_prop)), 1 / 4,
    by norm_num, fun s hs => ?_⟩
  rw [χD, Real.smoothTransition.zero_of_nonpos (by linarith), sub_zero]

theorem χD_eq_zero {s : ℝ} (hs : 1 / 2 ≤ s) : χD s = 0 := by
  rw [χD, Real.smoothTransition.one_of_one_le (by linarith), sub_self]

/-- **The Reiser–Wraith datum on `X = P_θ/S³_⋆`, for any bound `‖K_y‖ ≤ L`.** It consists of
two compact caps `X_N`, `X_S` with smooth metrics of positive sectional curvature, equal induced
metrics on `Σ`, and `B_N + B_S ≥ 0`. -/
theorem exists_rwData_L (L : ℝ) (hL : 0 < L) (hK : ∀ y : Vs e, ‖y‖ = 1 → ‖KY D.ρVs y‖ ≤ L) :
    Nonempty (RWData (𝓡 (m + 1)) (QuotSpace D)) := by
  -- the south: [HLY] Prop. 3.1, with `c₀ = 3/5`
  obtain ⟨Λ0, hΛ⟩ := southern_quotient_pos_D D isSouthCutoff_χD (c0 := 3 / 5) (by norm_num)
  set Λ := max Λ0 1
  set A0 := Λ * (5 / 3)
  have hΛ1 : 1 ≤ Λ := le_max_right _ _
  have hA0 : 0 < A0 := by positivity
  obtain ⟨εS, hεS, hS⟩ := hΛ Λ (le_max_left _ _) A0 hA0.le (by simp only [A0]; linarith)
  -- the north
  obtain ⟨Cη, -, -, -, -, -, hC0, hC, -⟩ := northern_quotient_hyps_satisfiable
  set δ := min 1 (1 / (32 * L ^ 2 * A0 * (4 / 5) * (1 + Cη)))
  have hδ : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ3 : δ ^ 3 ≤ 1 / (32 * L ^ 2 * A0 * (4 / 5) * (1 + Cη)) := by
    have h1 : δ ^ 3 ≤ δ := by
      have : δ ^ 3 = δ * δ ^ 2 := by ring
      rw [this]; exact mul_le_of_le_one_right hδ.le (by nlinarith)
    exact h1.trans (min_le_right _ _)
  set G := Gδ δ (4 / 5)
  have hG : 4 / 5 ≤ G := le_G (by norm_num)
  have hη : 1 / 2 ≤ G / δ := by
    rw [le_div_iff₀ hδ]; linarith
  -- `ε`
  set ε := min (εS / 2) (min (1 / (4 * (A0 + 1))) (1 / (A0 * (4 / 5) * G + 1)))
  have hε : 0 < ε := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hεS' : ε < εS := (min_le_left _ _).trans_lt (by linarith)
  have hε1 : ε ≤ 1 / (4 * (A0 + 1)) := (min_le_right _ _).trans (min_le_left _ _)
  have hε2 : ε ≤ 1 / (A0 * (4 / 5) * G + 1) := (min_le_right _ _).trans (min_le_right _ _)
  have hεA : ε * A0 ≤ 1 / 4 := by
    rw [le_div_iff₀ (by positivity)] at hε1
    nlinarith
  have hε1' : ε ≤ 1 := by
    have : 1 / (4 * (A0 + 1)) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    linarith
  set ra := √ε * Real.exp (ε / 2 * (A0 * (4 - 1 ^ 2) / (4 + 1 ^ 2)))
  set qs := ε * A0 * (4 / 5) / 2
  set d := ra * qs
  have hra : 0 < ra := mul_pos (Real.sqrt_pos.2 hε) (Real.exp_pos _)
  set a := Real.arccos (3 / 5)
  have hcos : |Real.cos a| = 3 / 5 := by
    rw [Real.cos_arccos (by norm_num) (by norm_num)]; norm_num
  have hra2 : ra ^ 2 = ε * Real.exp (ε * A0 * |Real.cos a|) := by
    rw [hcos, mul_pow, Real.sq_sqrt hε.le, ← Real.exp_nat_mul]
    congr 2; push_cast; ring
  have hql : qs * G ≤ 1 / 2 := by
    have hx : 0 ≤ A0 * (4 / 5) * G := by positivity
    have : ε * (A0 * (4 / 5) * G + 1) ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at hε2; linarith
    show ε * A0 * (4 / 5) / 2 * G ≤ 1 / 2
    nlinarith
  have hd1 : d < 1 := by
    have hs : √ε ≤ 1 := Real.sqrt_le_one.2 hε1'
    have hexp : Real.exp (ε / 2 * (A0 * (4 - 1 ^ 2) / (4 + 1 ^ 2))) < 3 := by
      have : ε / 2 * (A0 * (4 - 1 ^ 2) / (4 + 1 ^ 2)) ≤ 1 := by nlinarith
      calc Real.exp _ ≤ Real.exp 1 := Real.exp_le_exp.2 this
        _ < 3 := by have := Real.exp_one_lt_d9; linarith
    have hq : qs ≤ 1 / 10 := by show ε * A0 * (4 / 5) / 2 ≤ 1 / 10; nlinarith
    have hq0 : 0 ≤ qs := by positivity
    show √ε * Real.exp _ * qs < 1
    calc √ε * Real.exp _ * qs ≤ 1 * 3 * (1 / 10) := by
          apply mul_le_mul (mul_le_mul hs hexp.le (Real.exp_pos _).le zero_le_one) hq hq0
          positivity
      _ < 1 := by norm_num
  have hw0N : ∀ Y : Vs e, rD ra d δ (4 / 5) Y ≠ 0 := fun Y =>
    (rD_pos hε hA0 (by norm_num) hra rfl rfl hql Y).ne'
  have hr0S : ∀ y : Vs e, rSy ε A0 y ≠ 0 := fun y => (rSy_pos hε A0 y).ne'
  -- the Reiser–Wraith datum
  exact ⟨D.rwData (GN := gB D.ρVs δ (rD ra d δ (4 / 5)))
    (GS := SQ.gB D.ρVs (GsH (D.AS χD) (rSy ε A0)))
    (fun y a b => gB_symm D.ρVs δ y a b) (fun y a ha => gB_pos D.ρVs δ hw0N y ha)
    (contDiff_gB D.ρVs δ hw0N (contDiff_rD hδ))
    (fun y a b => SQ.gB_symm D.ρVs GsH_symm y a b)
    (fun y a ha => SQ.gB_pos D.ρVs (GsH_pos hr0S) y ha)
    (SQ.contDiff_gB D.ρVs (GsH_pos hr0S) (contDiff_GsH (D.contDiff_AS isSouthCutoff_χD)
      (contDiff_rSy ε A0)))
    (fun Y hY a' b' hab => northern_quotient_pos D.contMDiff_ρVs Cη hC0 hC a ε A0 (4 / 5) δ ra qs d
      hε hA0 (by norm_num) hδ hL hδ3 hra hra2 rfl rfl hql hd1 hK Y hY a' b' hab)
    (fun Y hY a' b' hab => hS ε hε hεS' Y (by
      show 3 / 5 * (4 + ‖Y‖ ^ 2) ≤ 4 - ‖Y‖ ^ 2
      nlinarith [norm_nonneg Y]) a' b' hab)
    (fun Y c c' hY hc hc' => D.model_hbm isSouthCutoff_χD (fun s hs => χD_eq_zero hs) hε rfl hw0N
      Y c c' hY hc hc')
    (fun Y c hY hc => D.model_hbs isSouthCutoff_χD (fun s hs => χD_eq_zero hs) hε rfl hw0N hδ rfl
      rfl hη _ _ Y c hY hc)⟩

/-- **`thm:HLYgeneral` for any bound `‖K_y‖ ≤ L`**, assuming the Reiser–Wraith gluing theorem. -/
theorem hly_general_L (L : ℝ) (hL : 0 < L) (hK : ∀ y : Vs e, ‖y‖ = 1 → ‖KY D.ρVs y‖ ≤ L)
    (hRW : RWGluing (𝓡 (m + 1)) (QuotSpace D)) : HasPosCurvMetric (𝓡 (m + 1)) (QuotSpace D) :=
  hRW (exists_rwData_L D L hL hK).some

/-- **[GG] `thm:HLYgeneral`.** Let `P_θ → S^n` be a polar bundle with `‖K_y‖ ≤ 2` for every unit
`y ∈ V`. Assuming the Reiser–Wraith gluing theorem on `X`, the star quotient `P_θ/S³_⋆` carries
a smooth Riemannian metric of positive sectional curvature. -/
theorem hly_general (hK : ∀ y : Vs e, ‖y‖ = 1 → ‖KY D.ρVs y‖ ≤ 2)
    (hRW : RWGluing (𝓡 (m + 1)) (QuotSpace D)) : HasPosCurvMetric (𝓡 (m + 1)) (QuotSpace D) :=
  hly_general_L D 2 two_pos hK hRW

end HLYGeneral

end

end ExoticSpheres8And10
