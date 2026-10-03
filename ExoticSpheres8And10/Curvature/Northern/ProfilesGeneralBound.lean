/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Curvature.Northern.ProfilesExistence

/-! # The northern filling for an arbitrary bound `‖K‖ ≤ L` ([DHZ] §5.3)

[D] and [HLY] assume `‖K_y‖ ≤ 2`. [DHZ] Prop. 5.1 needs only *some* bound `L`. The same
argument goes through with:
* `‖T‖ ≤ L F/r`;
* the criterion `(1−F'²)/F² > 2L²FF'r'/r³` and `−F''/F > L²F²(r'')₊/r³`;
* the profile condition `δ³ ≤ 1/(32L²A₀F_a(1+C_η))`. For `L = 2` this is [D]'s `eq:delta`.

[D]'s profile `F' = e^{−F²/2δ²}` is kept. [DHZ] uses `s = F + F³/3δ²`; any profile with these
inequalities serves, and `northern_filling_pos_L` proves the needed ones.

* `area_ineqs_graph_L`, `criterion_scalar_L`, `northNumerator_pos_L`, `norm_graphT_le_L`;
* `angular_chain_L`, `radial_chain_L`;
* **`northern_filling_pos_L`**.
-/

namespace ExoticSpheres8And10

open Set Function

open scoped RealInnerProductSpace

section L

variable {H Vv : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup Vv] [InnerProductSpace ℝ Vv]

theorem area_ineqs_graph_L (T : H →L[ℝ] Vv) (F r L : ℝ) (hT : ‖T‖ ≤ L * F / r) (X Y : H)
    (lam mu : ℝ) :
    ‖lam • T Y - mu • T X‖ ^ 2 ≤ L ^ 2 * F ^ 2 / r ^ 2 * ‖lam • Y - mu • X‖ ^ 2 ∧
      tensorSq X Y (T X) (T Y) ≤ 2 * L ^ 2 * F ^ 2 / r ^ 2 * wedgeSq X Y := by
  have e1 : (L * F / r) ^ 2 = L ^ 2 * F ^ 2 / r ^ 2 := by ring
  have e2 : 2 * (L * F / r) ^ 2 = 2 * L ^ 2 * F ^ 2 / r ^ 2 := by ring
  refine ⟨?_, ?_⟩
  · rw [← e1]; exact area_ineq_a T hT X Y lam mu
  · rw [← e2]; exact area_ineq_b T hT X Y

/-- The scalar criterion with bound `L`. -/
theorem criterion_scalar_L (F r Fp rp Fpp rpp L A B W UV Tn : ℝ)
    (hF : 0 < F) (hr : 0 < r) (hFp : 0 ≤ Fp) (hrp : 0 ≤ rp) (hrp1 : rp < 1)
    (hc1 : 2 * L ^ 2 * F * Fp * rp / r ^ 3 < (1 - Fp ^ 2) / F ^ 2)
    (hc2 : L ^ 2 * F ^ 2 * max rpp 0 / r ^ 3 < -Fpp / F)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hW : 0 ≤ W) (hUV : 0 ≤ UV)
    (hBA : B ≤ L ^ 2 * F ^ 2 / r ^ 2 * A) (hTW : Tn ≤ 2 * L ^ 2 * F ^ 2 / r ^ 2 * W)
    (hpos : 0 < A ∨ 0 < W) :
    0 < -(Fpp / F) * A - rpp / r * B + (1 - Fp ^ 2) / F ^ 2 * W + (1 - rp ^ 2) / r ^ 2 * UV
      - Fp * rp / (F * r) * Tn := by
  have s1 : rpp / r * B ≤ L ^ 2 * F ^ 2 * max rpp 0 / r ^ 3 * A := by
    calc rpp / r * B ≤ max rpp 0 / r * B :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_max_left _ _) hr.le) hB
      _ ≤ max rpp 0 / r * (L ^ 2 * F ^ 2 / r ^ 2 * A) :=
          mul_le_mul_of_nonneg_left hBA (div_nonneg (le_max_right _ _) hr.le)
      _ = L ^ 2 * F ^ 2 * max rpp 0 / r ^ 3 * A := by ring
  have s2 : Fp * rp / (F * r) * Tn ≤ 2 * L ^ 2 * F * Fp * rp / r ^ 3 * W := by
    calc Fp * rp / (F * r) * Tn ≤ Fp * rp / (F * r) * (2 * L ^ 2 * F ^ 2 / r ^ 2 * W) :=
          mul_le_mul_of_nonneg_left hTW (by positivity)
      _ = 2 * L ^ 2 * F * Fp * rp / r ^ 3 * W := by field_simp
  have s3 : 0 ≤ (1 - rp ^ 2) / r ^ 2 * UV := by
    have : 0 ≤ 1 - rp ^ 2 := by nlinarith
    positivity
  have hα : 0 < -Fpp / F - L ^ 2 * F ^ 2 * max rpp 0 / r ^ 3 := by linarith
  have hβ : 0 < (1 - Fp ^ 2) / F ^ 2 - 2 * L ^ 2 * F * Fp * rp / r ^ 3 := by linarith
  have s4 : 0 < (-Fpp / F - L ^ 2 * F ^ 2 * max rpp 0 / r ^ 3) * A +
      ((1 - Fp ^ 2) / F ^ 2 - 2 * L ^ 2 * F * Fp * rp / r ^ 3) * W := by
    rcases hpos with h | h
    · have := mul_pos hα h
      have := mul_nonneg hβ.le hW
      linarith
    · have := mul_nonneg hα.le hA
      have := mul_pos hβ h
      linarith
  have e : -(Fpp / F) = -Fpp / F := by ring
  rw [e]
  linarith

theorem northNumerator_pos_L (F r Fp rp Fpp rpp L : ℝ)
    (hF : 0 < F) (hr : 0 < r) (hFp : 0 ≤ Fp) (hrp : 0 ≤ rp) (hrp1 : rp < 1)
    (hc1 : 2 * L ^ 2 * F * Fp * rp / r ^ 3 < (1 - Fp ^ 2) / F ^ 2)
    (hc2 : L ^ 2 * F ^ 2 * max rpp 0 / r ^ 3 < -Fpp / F)
    (T : H →L[ℝ] Vv) (hT : ‖T‖ ≤ L * F / r) (X Y : H) (lam mu : ℝ)
    (hind : LinearIndependent ℝ ![((lam, X, T X) : ℝ × H × Vv), (mu, Y, T Y)]) :
    0 < northNumerator F r Fp rp Fpp rpp T X Y lam mu := by
  obtain ⟨ha, hb⟩ := area_ineqs_graph_L T F r L hT X Y lam mu
  exact criterion_scalar_L F r Fp rp Fpp rpp L _ _ _ _ _ hF hr hFp hrp hrp1 hc1 hc2
    (sq_nonneg _) (sq_nonneg _) (wedgeSq_nonneg _ _) (wedgeSq_nonneg _ _) ha hb
    (base_areas_pos_of_independent T X Y lam mu hind)

end L

section Adj

variable {E F' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F'] [InnerProductSpace ℝ F'] [CompleteSpace F']

theorem norm_graphT_le_L (K : E →L[ℝ] F') {L : ℝ} (hK : ‖K‖ ≤ L) {F r : ℝ} (hF : 0 ≤ F)
    (hr : 0 < r) : ‖-(F / r) • ContinuousLinearMap.adjoint K‖ ≤ L * F / r := by
  rw [norm_smul, LinearIsometryEquiv.norm_map, norm_neg, Real.norm_of_nonneg (by positivity)]
  calc F / r * ‖K‖ ≤ F / r * L := mul_le_mul_of_nonneg_left hK (by positivity)
    _ = L * F / r := by ring

end Adj

/-- **The angular chain** with bound `L`: `(1−F'²)/F² > 2L²FF'r'/r³`. -/
theorem angular_chain_L (F Fp δ A0 Fa Ceta d r rp L : ℝ) (hF : 0 < F) (hδ : 0 < δ)
    (hA0 : 0 < A0) (hFa : 0 < Fa) (hC : 0 ≤ Ceta) (hr : 0 < r) (hL : 0 < L)
    (hFp : Fp = Real.exp (-F ^ 2 / (2 * δ ^ 2)))
    (hδ3 : δ ^ 3 ≤ 1 / (32 * L ^ 2 * A0 * Fa * (1 + Ceta)))
    (hd : d / r ^ 3 ≤ 4 * A0 * Fa) (hrpd : rp ≤ d) :
    2 * L ^ 2 * F * Fp * rp / r ^ 3 < (1 - Fp ^ 2) / F ^ 2 := by
  have hstep := angular_step F δ hF hδ
  rw [← hFp] at hstep
  have hFp0 : 0 ≤ Fp := by rw [hFp]; exact (Real.exp_pos _).le
  have h0 : δ ^ 3 * (32 * L ^ 2 * A0 * Fa * (1 + Ceta)) ≤ 1 :=
    (le_div_iff₀ (by positivity)).1 hδ3
  have hc : 8 * L ^ 2 * A0 * Fa ≤ 1 / (2 * δ ^ 3) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hA0.le hFa.le) (pow_pos hδ 3).le) hC)
      (sq_nonneg L)]
  have h1 : rp / r ^ 3 ≤ d / r ^ 3 := div_le_div_of_nonneg_right hrpd (by positivity)
  have h2 : 2 * L ^ 2 * (rp / r ^ 3) ≤ 1 / (2 * δ ^ 3) := by
    have : 2 * L ^ 2 * (rp / r ^ 3) ≤ 2 * L ^ 2 * (4 * A0 * Fa) :=
      mul_le_mul_of_nonneg_left (h1.trans hd) (by positivity)
    linarith
  have h3 : F * Fp * (2 * L ^ 2 * (rp / r ^ 3)) ≤ F * Fp * (1 / (2 * δ ^ 3)) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have e1 : 2 * L ^ 2 * F * Fp * rp / r ^ 3 = F * Fp * (2 * L ^ 2 * (rp / r ^ 3)) := by ring
  have e2 : F * Fp * (1 / (2 * δ ^ 3)) = F * Fp / (2 * δ ^ 3) := by ring
  rw [e1]
  linarith

/-- **The radial chain** with bound `L`: `−F''/F > L²F²r''/r³`. -/
theorem radial_chain_L (F Fp Fpp s δ A0 Fa Ceta d r rpp L : ℝ) (hF : 0 < F) (hδ : 0 < δ)
    (hA0 : 0 < A0) (hFa : 0 < Fa) (hC : 0 ≤ Ceta) (hr : 0 < r) (hL : 0 < L)
    (hFp : Fp = Real.exp (-F ^ 2 / (2 * δ ^ 2)))
    (hδ3 : δ ^ 3 ≤ 1 / (32 * L ^ 2 * A0 * Fa * (1 + Ceta)))
    (hd : d / r ^ 3 ≤ 4 * A0 * Fa) (hFs : F ≤ s) (hs : s ≤ δ / 2)
    (hrpp : rpp ≤ d / δ * Ceta)
    (hFpp : Fpp = -(F / δ ^ 2) * Fp ^ 2) :
    L ^ 2 * F ^ 2 * rpp / r ^ 3 < -Fpp / F := by
  have hFδ : F ^ 2 ≤ δ ^ 2 / 4 := by nlinarith
  have hLq : -Fpp / F = Fp ^ 2 / δ ^ 2 := by rw [hFpp]; field_simp
  have hFp2 : 3 / 4 ≤ Fp ^ 2 := by
    have hq : F ^ 2 / δ ^ 2 ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have e : Fp ^ 2 = Real.exp (-(F ^ 2 / δ ^ 2)) := by
      rw [sq, hFp, ← Real.exp_add]; congr 1; ring
    have h1 : Real.exp (-(1 / 4 : ℝ)) ≤ Real.exp (-(F ^ 2 / δ ^ 2)) :=
      Real.exp_le_exp.2 (by linarith)
    have h2 := Real.add_one_le_exp (-(1 / 4 : ℝ))
    rw [e]; linarith
  have h0 : δ ^ 3 * (32 * L ^ 2 * A0 * Fa * (1 + Ceta)) ≤ 1 :=
    (le_div_iff₀ (by positivity)).1 hδ3
  have hCAF : 0 ≤ Ceta * A0 * Fa := by positivity
  have h1 : L ^ 2 * F ^ 2 * rpp / r ^ 3 ≤ L ^ 2 * F ^ 2 * (d / δ * Ceta) / r ^ 3 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hrpp (by positivity)) (by positivity)
  have h2 : L ^ 2 * F ^ 2 * (d / δ * Ceta) / r ^ 3 = L ^ 2 * F ^ 2 * Ceta / δ * (d / r ^ 3) := by
    ring
  have h3 : L ^ 2 * F ^ 2 * Ceta / δ * (d / r ^ 3) ≤ L ^ 2 * F ^ 2 * Ceta / δ * (4 * A0 * Fa) :=
    mul_le_mul_of_nonneg_left hd (by positivity)
  have h4 : L ^ 2 * F ^ 2 * Ceta / δ * (4 * A0 * Fa) ≤ L ^ 2 * δ * (Ceta * A0 * Fa) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hδ]
    nlinarith [mul_le_mul_of_nonneg_right hFδ (mul_nonneg (sq_nonneg L) hCAF)]
  have h5 : L ^ 2 * δ * (Ceta * A0 * Fa) < 3 / 4 / δ ^ 2 := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hA0.le hFa.le) (pow_pos hδ 3).le) hC)
      (sq_nonneg L),
      mul_nonneg (mul_nonneg (mul_nonneg hA0.le hFa.le) (pow_pos hδ 3).le) (sq_nonneg L)]
  have h6 : 3 / 4 / δ ^ 2 ≤ Fp ^ 2 / δ ^ 2 := div_le_div_of_nonneg_right hFp2 (by positivity)
  rw [hLq]
  linarith

section Fill

variable {H Vv : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup Vv] [InnerProductSpace ℝ Vv] [CompleteSpace Vv]

/-- **The northern filling with bound `L`** ([DHZ] §5.3): at every `s ∈ (0, ℓ_N]`, every `K`
with `‖K‖ ≤ L` and every independent star-horizontal pair, the numerator
`eq:fullcurvature` is positive, under `δ³ ≤ 1/(32L²A₀F_a(1+C_η))`. -/
theorem northern_filling_pos_L (Cη : ℝ) (hC0 : 0 ≤ Cη) (hC : ∀ x, |deriv etaCut x| ≤ Cη)
    (a ε A0 Fa δ ra qs d L : ℝ) (hε : 0 < ε) (hA0 : 0 < A0) (hFa : 0 < Fa) (hδ : 0 < δ)
    (hL : 0 < L) (hδ3 : δ ^ 3 ≤ 1 / (32 * L ^ 2 * A0 * Fa * (1 + Cη))) (hra : 0 < ra)
    (hra2 : ra ^ 2 = ε * Real.exp (ε * A0 * |Real.cos a|)) (hqs : qs = ε * A0 * Fa / 2)
    (hd : d = ra * qs) (hql : qs * Gδ δ Fa ≤ 1 / 2) (hd1 : d < 1)
    (s : ℝ) (hs : s ∈ Ioc 0 (Gδ δ Fa))
    (K : Vv →L[ℝ] H) (hK : ‖K‖ ≤ L) (X Y : H) (lam mu : ℝ)
    (hind : LinearIndependent ℝ
      ![((lam, X, (-(Fprof δ s / rprof ra d δ (Gδ δ Fa) s) • ContinuousLinearMap.adjoint K) X) :
          ℝ × H × Vv),
        (mu, Y, (-(Fprof δ s / rprof ra d δ (Gδ δ Fa) s) • ContinuousLinearMap.adjoint K) Y)]) :
    0 < northNumerator (Fprof δ s) (rprof ra d δ (Gδ δ Fa) s)
      (Real.exp (-(Fprof δ s) ^ 2 / (2 * δ ^ 2))) (d * etaCut (s / δ))
      (-(Fprof δ s / δ ^ 2) * Real.exp (-(Fprof δ s) ^ 2 / (2 * δ ^ 2)) ^ 2)
      (d * (deriv etaCut (s / δ) * (1 / δ)))
      (-(Fprof δ s / rprof ra d δ (Gδ δ Fa) s) • ContinuousLinearMap.adjoint K) X Y lam mu := by
  set ℓ := Gδ δ Fa
  set F := Fprof δ s
  set r := rprof ra d δ ℓ s
  set Fp := Real.exp (-F ^ 2 / (2 * δ ^ 2))
  set Fpp := -(F / δ ^ 2) * Fp ^ 2
  set rp := d * etaCut (s / δ)
  set rpp := d * (deriv etaCut (s / δ) * (1 / δ))
  have hqs0 : 0 ≤ qs := by rw [hqs]; positivity
  have hd0 : 0 ≤ d := by rw [hd]; positivity
  have hF : 0 < F := Fprof_pos hs.1
  have hdl : d * ℓ ≤ ra / 2 := by rw [hd]; nlinarith
  obtain ⟨hr1, hr2⟩ := rprof_bounds (δ := δ) hd0 hs.1.le hs.2 hdl
  have hr : 0 < r := by linarith
  have hdr := (d_over_r_cubed_bound ε A0 Fa a ra r d qs hε hA0 hFa hra hr1 hd hqs hra2)
  have hdr3 : d / r ^ 3 ≤ 4 * A0 * Fa := hdr.1.trans (hdr.2.1 ▸ hdr.2.2)
  have hrp0 : 0 ≤ rp := mul_nonneg hd0 (etaCut_nonneg _)
  have hrpd : rp ≤ d := by
    have := etaCut_le_one (s / δ); nlinarith
  have hFp0 : 0 ≤ Fp := (Real.exp_pos _).le
  have hc1 := angular_chain_L F Fp δ A0 Fa Cη d r rp L hF hδ hA0 hFa hC0 hr hL rfl hδ3 hdr3 hrpd
  have hc2 : L ^ 2 * F ^ 2 * max rpp 0 / r ^ 3 < -Fpp / F := by
    have hpos : 0 < -Fpp / F := by
      have e : -Fpp / F = Fp ^ 2 / δ ^ 2 := by simp only [Fpp]; field_simp
      rw [e]; have : 0 < Fp := Real.exp_pos _; positivity
    by_cases h0 : rpp ≤ 0
    · rw [max_eq_right h0]; simpa using hpos
    · push Not at h0
      rw [max_eq_left h0.le]
      have hne : deriv etaCut (s / δ) ≠ 0 := by
        intro h; simp [rpp, h] at h0
      have hsup := (deriv_etaCut_support hne).2
      have hsδ : s ≤ δ / 2 := by
        rw [div_le_iff₀ hδ] at hsup; linarith
      have hrppb : rpp ≤ d / δ * Cη := by
        have := (abs_le.1 (hC (s / δ))).2
        have e : rpp = d / δ * deriv etaCut (s / δ) := by simp only [rpp]; ring
        rw [e]
        exact mul_le_mul_of_nonneg_left this (by positivity)
      exact radial_chain_L F Fp Fpp s δ A0 Fa Cη d r rpp L hF hδ hA0 hFa hC0 hr hL rfl hδ3 hdr3
        (Fprof_le hs.1.le) hsδ hrppb rfl
  exact northNumerator_pos_L F r Fp rp Fpp rpp L hF hr hFp0 hrp0 (by linarith) hc1 hc2 _
    (norm_graphT_le_L K hK hF.le hr) X Y lam mu hind

end Fill

end ExoticSpheres8And10
