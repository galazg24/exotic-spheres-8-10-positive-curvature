/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Curvature.Boundary.Values
import ExoticSpheres8And10.ActionField.Bridge
import ExoticSpheres8And10.Curvature.DHZ

/-! # [GG] `eq:compat`: the strict bound `B_N + σ^*B_S ≥ c_B h` with `c_B > 0`

`bdry_model_sff` proves `B_N + B_S ≥ 0` on the boundary (model charts), and that is what the
gluing needs. [GG] states more:

  `B_N + σ^*B_S ≥ c_B h`, with `c_B = (r_a²/(r_a² + 4F_a²)) (μ_N − μ_S) > 0`.

Its proof:
- `eq:shapesum`: the sum is a positive multiple of `|X|²`;
- the boundary horizontal space is a graph `U = −(F_a/r_a)K^*X`;
- `‖K‖ ≤ 2` bounds `|Y|_h² = |X|² + |U|²` by `(1 + 4F_a²/r_a²)|X|²`.

Here the same argument is run in Lean's model charts:
* the sum is at least `μ_N|X|²`, where `X` is the base component of the horizontal lift;
* horizontality gives `r_a²|U|² = −⟪X, K U⟫ ≤ ‖K_Y‖|X||U|`;
* so `h(c, c) = |X|² + r_a²|U|² ≤ (1 + ‖K_Y‖²/r_a²)|X|²`.

Therefore **`B_N + B_S ≥ c_B h` with `c_B = μ_N r_a²/(r_a² + L²) > 0`**, for any bound
`‖K_Y‖ ≤ L` (`bdry_model_sff_cB`). With `L = ‖dρ‖F_a` it is uniform on the boundary sphere
(`bdry_model_compat`). For `‖K_y‖ ≤ 2` on the unit sphere this is `L = 2F_a`, and
`c_B = μ_N r_a²/(r_a² + 4F_a²)`, [GG]'s constant. In Lean's normalisation the southern base term
is a nonnegative extra.
-/

open RiemannianGeometry Bundle VectorField

namespace ExoticSpheres8And10

open Set Function Filter Topology Real

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Model

variable {m : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [Fact (Module.finrank ℝ W = (m + 1) + 1)] {e : W} [Fact (Module.finrank ℝ (Vs e) = m + 1)]

namespace PolarData

theorem μN_pos (δ : ℝ) {s : ℝ} (hs : 0 < s) : 0 < μN δ s := by
  have h1 := one_add_ψδ_pos δ s hs.le
  have h4 : 0 < 4 * s / (1 + ψδ δ s * s) := div_pos (by positivity) h1
  unfold μN
  exact mul_pos (inv_pos.2 (Real.sqrt_pos.2 h4)) (div_pos two_pos h1)

variable {ρV : S3 →* (Vs e ≃ₗᵢ[ℝ] Vs e)}
  (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, Vs e →L[ℝ] Vs e) ∞ fun q : S3 => ((ρV q : Vs e ≃L[ℝ] Vs e) : Vs e →L[ℝ] Vs e))

include hρ in
/-- **The boundary metric is controlled by the base component of the horizontal lift**:
`h(c, c) ≤ (1 + L²/r_a²)|X|²`, i.e. `(r_a²/(r_a² + L²)) h(c, c) ≤ |X|²`. -/
theorem gB_le_base {ra d δ Fa LK : ℝ} (hra0 : 0 < ra) (hw0N : ∀ Y : Vs e, rD ra d δ Fa Y ≠ 0)
    {Y : Vs e} (hY : ‖Y‖ = Fa) (hK : ‖KY ρV Y‖ ≤ LK) {c : Vs e} (hc : ⟪Y, c⟫ = 0) :
    ra ^ 2 / (ra ^ 2 + LK ^ 2) * SQ.gB ρV (GsW (βN δ) (rD ra d δ Fa)) Y c c ≤
      ⟪(SQ.hlift ρV (GsW (βN δ) (rD ra d δ Fa)) Y c).1,
        (SQ.hlift ρV (GsW (βN δ) (rD ra d δ Fa)) Y c).1⟫ := by
  have hGpos := GsW_pos (w := rD ra d δ Fa) (βN_pos δ) (βN_nonneg δ) hw0N
  set Zh := SQ.hlift ρV (GsW (βN δ) (rD ra d δ Fa)) Y c
  have hdπ : Zh.1 - KY ρV Y Zh.2 = c := SQ.dπl_hlift ρV hGpos Y c
  have hZ1 : ⟪Y, Zh.1⟫ = 0 := by
    rw [sub_eq_iff_eq_add.1 hdπ, inner_add_right, hc, inner_Y_KY hρ, add_zero]
  have hKY : ⟪Y, KY ρV Y Zh.2⟫ = 0 := inner_Y_KY hρ Y Zh.2
  have hw : rD ra d δ Fa Y = ra := by rw [rD, hY, rprof_end]
  have hDq : ⟪Dq Zh.2, Dq Zh.2⟫ = ‖Zh.2‖ ^ 2 := by
    rw [Dq_apply, inner_ι3, real_inner_self_eq_norm_sq]
  -- the metric value
  have hgB : SQ.gB ρV (GsW (βN δ) (rD ra d δ Fa)) Y c c = ‖Zh.1‖ ^ 2 + ra ^ 2 * ‖Zh.2‖ ^ 2 := by
    show GsW (βN δ) (rD ra d δ Fa) Y Zh Zh = _
    rw [GsW_apply, βN_apply, hZ1, hw, hDq, real_inner_self_eq_norm_sq]; ring
  -- horizontality: `r_a²|U|² = −⟪X, K U⟫`
  have hhor := SQ.hlift_horizontal ρV hGpos Y c Zh.2
  rw [ιv_apply, GsW_apply, βN_apply, hZ1, hKY, hw, hDq] at hhor
  have hX := norm_nonneg Zh.1
  have hU := norm_nonneg Zh.2
  have hLK : 0 ≤ LK := (norm_nonneg _).trans hK
  have hKU : ‖KY ρV Y Zh.2‖ ≤ LK * ‖Zh.2‖ :=
    ((KY ρV Y).le_opNorm Zh.2).trans (mul_le_mul_of_nonneg_right hK hU)
  have hcs : -⟪Zh.1, KY ρV Y Zh.2⟫ ≤ ‖Zh.1‖ * (LK * ‖Zh.2‖) :=
    (neg_le_abs _).trans ((abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hKU hX))
  have h1 : ra ^ 2 * ‖Zh.2‖ ^ 2 ≤ ‖Zh.1‖ * LK * ‖Zh.2‖ := by nlinarith
  -- so `r_a⁴|U|² ≤ L²|X|²`
  have h2 : (ra ^ 2 * ‖Zh.2‖) ^ 2 ≤ (‖Zh.1‖ * LK) ^ 2 := by
    have ht : 0 ≤ ra ^ 2 * ‖Zh.2‖ := by positivity
    have h3 : ra ^ 2 * ‖Zh.2‖ ≤ ‖Zh.1‖ * LK := by
      rcases hU.lt_or_eq with hpos | hzero
      · have := h1; nlinarith
      · rw [← hzero, mul_zero]; positivity
    exact pow_le_pow_left₀ ht h3 2
  rw [hgB, div_mul_eq_mul_div, div_le_iff₀ (by positivity), real_inner_self_eq_norm_sq]
  nlinarith

include hρ in
/-- **[GG] `eq:compat` in the model charts, with a strictly positive constant**:
`B_N + B_S ≥ c_B h(c, c)` with `c_B = μ_N r_a²/(r_a² + L²)` for any bound `‖K_Y‖ ≤ L`. -/
theorem bdry_model_sff_cB {ε A0 ra qs d δ ρ0 Fa LK : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hρ0 : 0 < ρ0)
    (hρ02 : ρ0 ≤ 2) (hFa : Fa = 4 * ρ0 / (4 + ρ0 ^ 2))
    (hra : ra = √ε * Real.exp (ε / 2 * (A0 * (4 - ρ0 ^ 2) / (4 + ρ0 ^ 2))))
    (hqs : qs = ε * A0 * Fa / 2) (hd : d = ra * qs) (hη : 1 / 2 ≤ Gδ δ Fa / δ)
    (hw0N : ∀ Y : Vs e, rD ra d δ Fa Y ≠ 0) {Y : Vs e} (hY : ‖Y‖ = Fa) (hK : ‖KY ρV Y‖ ≤ LK)
    {c : Vs e} (hc : ⟪Y, c⟫ = 0) :
    μN δ (Fa ^ 2) * ra ^ 2 / (ra ^ 2 + LK ^ 2) * SQ.gB ρV (GsW (βN δ) (rD ra d δ Fa)) Y c c ≤
      sff (SQ.isPosDef_cmet_gB' (ρV := ρV)
          (GsW_pos (w := rD ra d δ Fa) (βN_pos δ) (βN_nonneg δ) hw0N)).isNondegenerate
          (fun y : Vs e => ‖y‖ ^ 2) Y (toTSv Y c) (toTSv Y c) +
        sff (SQ.isPosDef_cmet_gB' (ρV := ρV)
          (GsW_pos (w := rSy ε A0) β0_pos β0_nonneg fun y => (rSy_pos hε A0 y).ne')).isNondegenerate
          (fun y : Vs e => ‖y‖ ^ 2) ((1 + ρ0 ^ 2 / 4) • Y)
          (toTSv ((1 + ρ0 ^ 2 / 4) • Y) ((1 + ρ0 ^ 2 / 4) • c))
          (toTSv ((1 + ρ0 ^ 2 / 4) • Y) ((1 + ρ0 ^ 2 / 4) • c)) := by
  have hFa0 : 0 < Fa := by rw [hFa]; positivity
  have hra0 : 0 < ra := by
    rw [hra]; exact mul_pos (Real.sqrt_pos.2 hε) (Real.exp_pos _)
  have hl : (0 : ℝ) < 1 + ρ0 ^ 2 / 4 := by positivity
  have hnY := norm_bdry hρ0 hFa hY
  have hY0 : Y ≠ 0 := fun h => by rw [h, norm_zero] at hY; linarith
  have hlY0 : (1 + ρ0 ^ 2 / 4) • Y ≠ 0 := smul_ne_zero hl.ne' hY0
  have hnρ : ∀ (q : S3) (y : Vs e), ‖ρV q y‖ ^ 2 = ‖y‖ ^ 2 := fun q y => by
    rw [LinearIsometryEquiv.norm_map]
  have hbase := gB_le_base hρ (δ := δ) hra0 hw0N hY hK hc
  have hμ0 : 0 < μN δ (Fa ^ 2) := μN_pos δ (by positivity)
  have hstep : μN δ (Fa ^ 2) * ra ^ 2 / (ra ^ 2 + LK ^ 2) *
      SQ.gB ρV (GsW (βN δ) (rD ra d δ Fa)) Y c c ≤
      μN δ (Fa ^ 2) * ⟪(SQ.hlift ρV (GsW (βN δ) (rD ra d δ Fa)) Y c).1,
        (SQ.hlift ρV (GsW (βN δ) (rD ra d δ Fa)) Y c).1⟫ := by
    rw [mul_div_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left hbase hμ0.le
  refine hstep.trans ?_
  rw [sff_quot_GW hρ (contDiff_βN δ) (βN_symm δ) (βN_pos δ) (βN_nonneg δ) (contDiff_rD hδ) hw0N
      (βN_ρ ρV δ) (rD_invariant ra d δ Fa ρV) (contDiff_norm_sq ℝ) hnρ (fderiv_normSq_ne hY0)
      (contDiff_vBN δ) (vBN_spec δ) c,
    sff_quot_GW hρ contDiff_β0 β0_symm β0_pos β0_nonneg (contDiff_rSy ε A0)
      (fun y => (rSy_pos hε A0 y).ne') (β0_ρ ρV) (rSy_ρ ε A0) (contDiff_norm_sq ℝ) hnρ
      (fderiv_normSq_ne hlY0) contDiff_vBS vBS_spec ((1 + ρ0 ^ 2 / 4) • c),
    hlift_match hρ (βN_pos δ) (βN_nonneg δ) hw0N β0_pos β0_nonneg
      (fun y => (rSy_pos hε A0 y).ne') (bdry_β_match hρ0 hFa hY) (bdry_w_match hρ0 hFa hra hY) hc]
  set Zh := SQ.hlift ρV (GsW (βN δ) (rD ra d δ Fa)) Y c
  have hZ1 : ⟪Y, Zh.1⟫ = 0 := by
    have hdπ : Zh.1 - KY ρV Y Zh.2 = c :=
      SQ.dπl_hlift ρV (GsW_pos (w := rD ra d δ Fa) (βN_pos δ) (βN_nonneg δ) hw0N) Y c
    rw [sub_eq_iff_eq_add.1 hdπ, inner_add_right, hc, inner_Y_KY hρ, add_zero]
  have hZ1' : ⟪(1 + ρ0 ^ 2 / 4) • Y, (1 + ρ0 ^ 2 / 4) • Zh.1⟫ = 0 := by
    rw [real_inner_smul_left, real_inner_smul_right, hZ1, mul_zero, mul_zero]
  have hs0 : 0 < ‖(1 + ρ0 ^ 2 / 4) • Y‖ := by rw [hnY]; exact hρ0
  rw [baseN_eq hZ1 (differentiableAt_μN δ (by rw [hY]; positivity)), fibreN hδ hFa0 hη hY,
    baseS_eq hZ1' (differentiableAt_μS (by positivity)), fibreS hε hs0]
  have hrS : rSy ε A0 ((1 + ρ0 ^ 2 / 4) • Y) = ra :=
    (bdry_w_match (d := d) (δ := δ) hρ0 hFa hra hY).trans (by rw [rD, hY, rprof_end])
  rw [hrS, hnY]
  dsimp only
  have hfib : ra * d - ra ^ 2 * (2 * ε * A0 * ρ0 / (4 + ρ0 ^ 2)) = 0 := by
    rw [hd, hqs, hFa]; field_simp; ring
  have hb2 := μS_nonneg (ρ0 ^ 2) (by positivity)
  have hb3 := baseS_factor_nonneg (s := ρ0 ^ 2) (by positivity) (by nlinarith)
  have hi2 : 0 ≤ ⟪(1 + ρ0 ^ 2 / 4) • Zh.1, (1 + ρ0 ^ 2 / 4) • Zh.1⟫ := real_inner_self_nonneg
  have key : ∀ x : ℝ, ra * d * x + -(ra ^ 2 * (2 * ε * A0 * ρ0 / (4 + ρ0 ^ 2))) * x = 0 :=
    fun x => by linear_combination x * hfib
  rw [hY]
  calc μN δ (Fa ^ 2) * ⟪Zh.1, Zh.1⟫ ≤ μN δ (Fa ^ 2) * ⟪Zh.1, Zh.1⟫ + μS (ρ0 ^ 2) *
        ⟪(1 + ρ0 ^ 2 / 4) • Zh.1, (1 + ρ0 ^ 2 / 4) • Zh.1⟫ *
          (ψs (ρ0 ^ 2) - 1 / 2 * ρ0 ^ 2 / (1 + ρ0 ^ 2 / 4) ^ 3) :=
        le_add_of_nonneg_right (mul_nonneg (mul_nonneg hb2 hi2) hb3)
    _ = _ := by linear_combination -(key ⟪Zh.2, Zh.2⟫)

include hρ in
/-- **[GG] `eq:compat`, uniform on the boundary sphere**: one constant `c_B > 0` works for every
boundary point `Y` (`‖Y‖ = F_a`) and tangent vector `c`. -/
theorem bdry_model_compat {ε A0 ra qs d δ ρ0 Fa : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hρ0 : 0 < ρ0)
    (hρ02 : ρ0 ≤ 2) (hFa : Fa = 4 * ρ0 / (4 + ρ0 ^ 2))
    (hra : ra = √ε * Real.exp (ε / 2 * (A0 * (4 - ρ0 ^ 2) / (4 + ρ0 ^ 2))))
    (hqs : qs = ε * A0 * Fa / 2) (hd : d = ra * qs) (hη : 1 / 2 ≤ Gδ δ Fa / δ)
    (hw0N : ∀ Y : Vs e, rD ra d δ Fa Y ≠ 0) :
    ∃ cB : ℝ, 0 < cB ∧ ∀ (Y : Vs e), ‖Y‖ = Fa → ∀ c : Vs e, ⟪Y, c⟫ = 0 →
      cB * SQ.gB ρV (GsW (βN δ) (rD ra d δ Fa)) Y c c ≤
        sff (SQ.isPosDef_cmet_gB' (ρV := ρV)
            (GsW_pos (w := rD ra d δ Fa) (βN_pos δ) (βN_nonneg δ) hw0N)).isNondegenerate
            (fun y : Vs e => ‖y‖ ^ 2) Y (toTSv Y c) (toTSv Y c) +
          sff (SQ.isPosDef_cmet_gB' (ρV := ρV)
            (GsW_pos (w := rSy ε A0) β0_pos β0_nonneg fun y => (rSy_pos hε A0 y).ne')).isNondegenerate
            (fun y : Vs e => ‖y‖ ^ 2) ((1 + ρ0 ^ 2 / 4) • Y)
            (toTSv ((1 + ρ0 ^ 2 / 4) • Y) ((1 + ρ0 ^ 2 / 4) • c))
            (toTSv ((1 + ρ0 ^ 2 / 4) • Y) ((1 + ρ0 ^ 2 / 4) • c)) := by
  have hFa0 : 0 < Fa := by rw [hFa]; positivity
  have hra0 : 0 < ra := by
    rw [hra]; exact mul_pos (Real.sqrt_pos.2 hε) (Real.exp_pos _)
  refine ⟨μN δ (Fa ^ 2) * ra ^ 2 / (ra ^ 2 + (‖dρ ρV‖ * Fa) ^ 2),
    div_pos (mul_pos (μN_pos δ (by positivity)) (by positivity)) (by positivity),
    fun Y hY c hc => ?_⟩
  have hK : ‖KY ρV Y‖ ≤ ‖dρ ρV‖ * Fa := by rw [← hY]; exact norm_KY_le_dρ ρV Y
  exact bdry_model_sff_cB hρ hε hδ hρ0 hρ02 hFa hra hqs hd hη hw0N hY hK hc

end PolarData

end Model

end

end ExoticSpheres8And10
