/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.StarBundles.Skeleton
import ExoticSpheres8And10.ActionField.Bound
import ExoticSpheres8And10.ActionField.Chains

/-! # B3, strengthened: parallel transport for a connection on a trivial `S³`-bundle

[GG] `prop:polar`, Steps 3 and 6 use horizontal lifts of curves for a principal connection. B3
took their existence, uniqueness and right-invariance as an interface (`HorizontalLifts`) with the
flat model. Here the interface is **constructed** for an arbitrary (curved) connection on the
trivial bundle `E × ℍ` over a normed space `E`, with connection potential `A : E → (E →L ℍ)`
taking values in `Im ℍ` (the Lie algebra of `S³`): in the gauge `ω = u⁻¹Au + u⁻¹du`
(`eq:potentials`), a lift `t ↦ (c t, u t)` is horizontal iff `u' = −A_{c}(c') u`.

* `sat`: a bounded, Lipschitz radial truncation (`sat x = 2x/(1+‖x‖²)`, `sat x = x` on `‖x‖ = 1`);
* `exists_transport`: for continuous imaginary `M`, a solution of `u' = Mu` on `[0,1]` with
  `u(t₀) = 1` (Picard–Lindelöf for the truncated field, then norm preservation);
* `transport_unique`: uniqueness (Grönwall, forward and backward from `t₀`);
* `transportLifts A`: the `HorizontalLifts` structure for `C¹` curves on `[0,1]`.

Not covered: connections on a non-trivial bundle, smooth dependence of the lift on parameters
(Mathlib has no smooth dependence of ODE solutions on parameters), Haar averaging (Step 1).
-/

namespace ExoticSpheres8And10

open Quaternion Set Metric Filter Topology

open scoped RealInnerProductSpace NNReal

/-! ## The truncation -/

/-- `sat x = (2/(1+‖x‖²)) x`. -/
noncomputable def sat (x : ℍ[ℝ]) : ℍ[ℝ] := (2 / (1 + ‖x‖ ^ 2)) • x

theorem norm_sat_le (x : ℍ[ℝ]) : ‖sat x‖ ≤ 1 := by
  rw [sat, norm_smul, Real.norm_of_nonneg (by positivity), div_mul_eq_mul_div,
    div_le_one (by positivity)]
  nlinarith [sq_nonneg (‖x‖ - 1), norm_nonneg x]

theorem sat_of_norm_one {x : ℍ[ℝ]} (h : ‖x‖ = 1) : sat x = x := by
  rw [sat, h]; norm_num

/-- The derivative of `sat`. -/
noncomputable def satD (x : ℍ[ℝ]) : ℍ[ℝ] →L[ℝ] ℍ[ℝ] :=
  (2 / (1 + ‖x‖ ^ 2)) • ContinuousLinearMap.id ℝ ℍ[ℝ] +
    ((-(2 / (1 + ‖x‖ ^ 2) ^ 2)) • ((2 : ℝ) • innerSL ℝ x)).smulRight x

theorem hasFDerivAt_sat (x : ℍ[ℝ]) : HasFDerivAt sat (satD x) x := by
  have hn : HasFDerivAt (fun y : ℍ[ℝ] => ‖y‖ ^ 2) ((2 : ℝ) • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt.congr_fderiv (by simp [two_smul])
  have hg : HasDerivAt (fun s : ℝ => 2 / (1 + s)) (-(2 / (1 + ‖x‖ ^ 2) ^ 2)) (‖x‖ ^ 2) := by
    have h1 : (1 + ‖x‖ ^ 2) ≠ 0 := by positivity
    have := (((hasDerivAt_id' (‖x‖ ^ 2)).const_add 1).inv h1).const_mul 2
    refine (this.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    · field_simp
    · simp only [div_eq_mul_inv, Pi.inv_apply]
  have hl := hg.comp_hasFDerivAt x hn
  exact (hl.smul (hasFDerivAt_id x)).congr_fderiv (by simp [satD])

theorem norm_satD_le (x : ℍ[ℝ]) : ‖satD x‖ ≤ 3 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun v => ?_
  have hd : 0 < 1 + ‖x‖ ^ 2 := by positivity
  simp only [satD, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    smul_eq_mul]
  calc _ ≤ ‖(2 / (1 + ‖x‖ ^ 2)) • v‖ +
        ‖(-(2 / (1 + ‖x‖ ^ 2) ^ 2) * (2 * ⟪x, v⟫)) • x‖ := norm_add_le _ _
    _ ≤ 2 * ‖v‖ + (4 * ‖x‖ ^ 2 / (1 + ‖x‖ ^ 2) ^ 2) * ‖v‖ := by
        refine add_le_add ?_ ?_
        · rw [norm_smul, Real.norm_of_nonneg (by positivity)]
          gcongr
          rw [div_le_iff₀ hd]; nlinarith [sq_nonneg ‖x‖]
        · rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (by positivity), abs_mul,
            abs_two]
          have hc := abs_real_inner_le_norm x v
          calc 2 / (1 + ‖x‖ ^ 2) ^ 2 * (2 * |⟪x, v⟫|) * ‖x‖
              ≤ 2 / (1 + ‖x‖ ^ 2) ^ 2 * (2 * (‖x‖ * ‖v‖)) * ‖x‖ := by gcongr
            _ = 4 * ‖x‖ ^ 2 / (1 + ‖x‖ ^ 2) ^ 2 * ‖v‖ := by ring
    _ ≤ 2 * ‖v‖ + 1 * ‖v‖ := by
        gcongr
        rw [div_le_one (by positivity)]
        nlinarith [sq_nonneg (‖x‖ ^ 2 - 1)]
    _ = 3 * ‖v‖ := by ring

theorem lipschitz_sat : LipschitzWith 3 sat := by
  refine lipschitzWith_of_nnnorm_fderiv_le (fun x => (hasFDerivAt_sat x).differentiableAt)
    fun x => ?_
  rw [(hasFDerivAt_sat x).fderiv, ← NNReal.coe_le_coe, coe_nnnorm]
  exact norm_satD_le x

/-! ## Existence and uniqueness for `u' = M u` on `[0,1]`, `M` imaginary -/

theorem inner_self_mul_pure (x M : ℍ[ℝ]) (hM : M.re = 0) : ⟪x, M * x⟫ = 0 := by
  rw [Quaternion.inner_def]
  simp only [Quaternion.re_mul, Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star,
    Quaternion.imK_star, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, hM]
  ring

/-- **Existence of parallel transport.** For `M` continuous on `[0,1]` with values in `Im ℍ` and
`t₀ ∈ [0,1]`, there is `u` with `u(t₀) = 1`, `‖u‖ ≡ 1` and `u' = M u` on `[0,1]`. -/
theorem exists_transport (M : ℝ → ℍ[ℝ]) (hM : ContinuousOn M (Icc 0 1))
    (hpure : ∀ t, (M t).re = 0) (t₀ : ℝ) (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) :
    ∃ u : ℝ → ℍ[ℝ], u t₀ = 1 ∧ (∀ t ∈ Icc (0 : ℝ) 1, ‖u t‖ = 1) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt u (M t * u t) (Icc 0 1) t := by
  obtain ⟨mR, hmR⟩ := isCompact_Icc.exists_bound_of_continuousOn hM
  set m : ℝ≥0 := ⟨max mR 0, le_max_right _ _⟩
  have hm : ∀ t ∈ Icc (0 : ℝ) 1, ‖M t‖ ≤ m := fun t ht => (hmR t ht).trans (le_max_left _ _)
  let f : ℝ → ℍ[ℝ] → ℍ[ℝ] := fun t x => M t * sat x
  have hPL : IsPicardLindelof f (⟨t₀, ht₀⟩ : Icc (0 : ℝ) 1) (1 : ℍ[ℝ]) (m + 1) 0 m (m * 3) := by
    refine ⟨fun t ht => ?_, fun x _ => ?_, fun t ht x _ => ?_, ?_⟩
    · have hl : LipschitzWith m (fun y : ℍ[ℝ] => M t * y) := by
        refine LipschitzWith.of_dist_le_mul fun y z => ?_
        rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul]
        exact mul_le_mul_of_nonneg_right (hm t ht) (norm_nonneg _)
      exact (hl.comp lipschitz_sat).lipschitzOnWith
    · exact hM.mul continuousOn_const
    · calc ‖f t x‖ = ‖M t‖ * ‖sat x‖ := norm_mul _ _
        _ ≤ m * 1 := by gcongr; exacts [hm t ht, norm_sat_le x]
        _ = m := mul_one _
    · simp only [NNReal.coe_add, NNReal.coe_one, NNReal.coe_zero, tsub_zero]
      have h1 : max (1 - t₀) t₀ ≤ 1 := max_le (by linarith [ht₀.1]) (by linarith [ht₀.2])
      calc (m : ℝ) * max (1 - t₀) t₀ ≤ m * 1 := by gcongr
        _ ≤ m + 1 := by linarith
  obtain ⟨α, hα0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt (mem_closedBall_self le_rfl)
  -- the norm of `α` is constant
  have hsq : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun s => ‖α s‖ ^ 2) 0 (Icc 0 1) t := by
    intro t ht
    have h := (hα t ht).norm_sq
    refine h.congr_deriv ?_
    simp only [f, sat, mul_smul_comm, inner_smul_right, inner_self_mul_pure _ _ (hpure t),
      mul_zero]
  have hconst : ∀ t ∈ Icc (0 : ℝ) 1, ‖α t‖ ^ 2 = ‖α 0‖ ^ 2 :=
    constant_of_derivWithin_zero (fun t ht => (hsq t ht).differentiableWithinAt)
      (fun t ht => (hsq t (Ico_subset_Icc_self ht)).derivWithin
        (uniqueDiffOn_Icc zero_lt_one t (Ico_subset_Icc_self ht)))
  have hnorm : ∀ t ∈ Icc (0 : ℝ) 1, ‖α t‖ = 1 := by
    intro t ht
    have h1 := hconst t ht
    have h2 := hconst t₀ ht₀
    rw [show α t₀ = 1 from hα0, norm_one, one_pow] at h2
    have : ‖α t‖ ^ 2 = 1 := by rw [h1, ← h2]
    have h3 := norm_nonneg (α t)
    nlinarith [sq_nonneg (‖α t‖ - 1)]
  refine ⟨α, hα0, hnorm, fun t ht => ?_⟩
  have := hα t ht
  simp only [f, sat_of_norm_one (hnorm t ht)] at this
  exact this

theorem hasDerivWithinAt_Ici_of_Icc {u : ℝ → ℍ[ℝ]} {u' : ℍ[ℝ]} {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1)
    (h : HasDerivWithinAt u u' (Icc 0 1) t) : HasDerivWithinAt u u' (Ici t) t :=
  h.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)

theorem hasDerivWithinAt_Iic_of_Icc {u : ℝ → ℍ[ℝ]} {u' : ℍ[ℝ]} {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1)
    (h : HasDerivWithinAt u u' (Icc 0 1) t) : HasDerivWithinAt u u' (Iic t) t :=
  h.mono_of_mem_nhdsWithin (Icc_mem_nhdsLE_of_mem ht)

/-- **Uniqueness of parallel transport.** -/
theorem transport_unique (M : ℝ → ℍ[ℝ]) (m : ℝ≥0) (hm : ∀ t ∈ Icc (0 : ℝ) 1, ‖M t‖ ≤ m)
    (u v : ℝ → ℍ[ℝ]) (hu : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt u (M t * u t) (Icc 0 1) t)
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt v (M t * v t) (Icc 0 1) t)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) (h0 : u t₀ = v t₀) : ∀ t ∈ Icc (0 : ℝ) 1, u t = v t := by
  have hL : ∀ t ∈ Icc (0 : ℝ) 1, LipschitzOnWith m (fun y : ℍ[ℝ] => M t * y) univ := by
    intro t ht
    refine (LipschitzWith.of_dist_le_mul fun y z => ?_).lipschitzOnWith
    rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul]
    exact mul_le_mul_of_nonneg_right (hm t ht) (norm_nonneg _)
  have huc : ContinuousOn u (Icc 0 1) := fun t ht => (hu t ht).continuousWithinAt
  have hvc : ContinuousOn v (Icc 0 1) := fun t ht => (hv t ht).continuousWithinAt
  intro t ht
  rcases le_total t₀ t with h | h
  · -- forward on `[t₀, 1]`
    have := ODE_solution_unique_of_mem_Icc_right (v := fun t y => M t * y) (s := fun _ => univ)
      (K := m) (a := t₀) (b := 1)
      (fun s hs => hL s ⟨ht₀.1.trans hs.1, hs.2.le⟩)
      (huc.mono (Icc_subset_Icc ht₀.1 le_rfl))
      (fun s hs => hasDerivWithinAt_Ici_of_Icc ⟨ht₀.1.trans hs.1, hs.2⟩
        (hu s ⟨ht₀.1.trans hs.1, hs.2.le⟩))
      (fun _ _ => mem_univ _)
      (hvc.mono (Icc_subset_Icc ht₀.1 le_rfl))
      (fun s hs => hasDerivWithinAt_Ici_of_Icc ⟨ht₀.1.trans hs.1, hs.2⟩
        (hv s ⟨ht₀.1.trans hs.1, hs.2.le⟩))
      (fun _ _ => mem_univ _) h0
    exact this ⟨h, ht.2⟩
  · -- backward on `[0, t₀]`
    have := ODE_solution_unique_of_mem_Icc_left (v := fun t y => M t * y) (s := fun _ => univ)
      (K := m) (a := 0) (b := t₀)
      (fun s hs => hL s ⟨hs.1.le, hs.2.trans ht₀.2⟩)
      (huc.mono (Icc_subset_Icc le_rfl ht₀.2))
      (fun s hs => hasDerivWithinAt_Iic_of_Icc ⟨hs.1, hs.2.trans ht₀.2⟩
        (hu s ⟨hs.1.le, hs.2.trans ht₀.2⟩))
      (fun _ _ => mem_univ _)
      (hvc.mono (Icc_subset_Icc le_rfl ht₀.2))
      (fun s hs => hasDerivWithinAt_Iic_of_Icc ⟨hs.1, hs.2.trans ht₀.2⟩
        (hv s ⟨hs.1.le, hs.2.trans ht₀.2⟩))
      (fun _ _ => mem_univ _) h0
    exact this ⟨ht.1, h⟩

/-! ## The horizontal-lift structure on `E × S³` -/

section Lifts

local notation "S3" => sphere (0 : ℍ[ℝ]) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_nnbound {M : ℝ → ℍ[ℝ]} (hM : ContinuousOn M (Icc 0 1)) :
    ∃ m : ℝ≥0, ∀ t ∈ Icc (0 : ℝ) 1, ‖M t‖ ≤ m := by
  obtain ⟨mR, hmR⟩ := isCompact_Icc.exists_bound_of_continuousOn hM
  exact ⟨⟨max mR 0, le_max_right _ _⟩, fun t ht => (hmR t ht).trans (le_max_left _ _)⟩

/-- `M_c(t) = −A_{c(t)}(c'(t))`: the horizontal-lift equation along `c` is `u' = M_c u`. -/
noncomputable def potAlong (A : E → E →L[ℝ] ℍ[ℝ]) (c : ℝ → E) (t : ℝ) : ℍ[ℝ] :=
  -(A (c t) (deriv c t))

theorem continuous_potAlong {A : E → E →L[ℝ] ℍ[ℝ]} (hA : Continuous A) {c : ℝ → E}
    (hc : ContDiff ℝ 1 c) : Continuous (potAlong A c) :=
  ((hA.comp hc.continuous).clm_apply (hc.continuous_deriv le_rfl)).neg

/-- **Parallel transport as a `HorizontalLifts` structure.** Base `E`, total space `E × S³`,
right action `(b, s)·g = (b, s g)`, curves the `C¹` maps `ℝ → E`, parameter interval `[0,1]`.
A lift `ℓ` of `c` is horizontal iff its `S³`-component `u` solves `u' = −A_{c}(c') u` on `[0,1]`
(i.e. `ω(ℓ') = u⁻¹A(c')u + u⁻¹u' = 0` for `ω = u⁻¹Au + u⁻¹du`). -/
noncomputable def transportLifts (A : E → E →L[ℝ] ℍ[ℝ]) (hA : Continuous A)
    (hpure : ∀ x v, (A x v).re = 0) :
    HorizontalLifts S3 (E × S3) E Prod.fst (fun p g => (p.1, p.2 * g))
      {c | ContDiff ℝ 1 c} (Icc 0 1) where
  IsLift c ℓ := ∃ u : ℝ → ℍ[ℝ], (∀ t ∈ Icc (0 : ℝ) 1, (ℓ t).1 = c t ∧ ((ℓ t).2 : ℍ[ℝ]) = u t) ∧
    ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt u (potAlong A c t * u t) (Icc 0 1) t
  proj c _ ℓ h t ht := by obtain ⟨u, hu, -⟩ := h; exact (hu t ht).1
  exists_lift c hc t₀ ht₀ p hp := by
    have hMc := (continuous_potAlong hA hc).continuousOn (s := Icc 0 1)
    obtain ⟨α, hα0, hαn, hα⟩ := exists_transport (potAlong A c) hMc
      (fun t => by simp [potAlong, hpure]) t₀ ht₀
    have hmem : ∀ t ∈ Icc (0 : ℝ) 1, α t * (p.2 : ℍ[ℝ]) ∈ S3 := fun t ht => by
      rw [mem_sphere_zero_iff_norm, norm_mul, hαn t ht, one_mul]
      exact mem_sphere_zero_iff_norm.1 p.2.2
    classical
    refine ⟨fun t => (c t, if h : α t * (p.2 : ℍ[ℝ]) ∈ S3 then ⟨_, h⟩ else 1),
      ⟨fun t => α t * p.2, fun t ht => ⟨rfl, by beta_reduce; rw [dif_pos (hmem t ht)]⟩, fun t ht => ?_⟩, ?_⟩
    · exact ((hα t ht).mul_const _).congr_deriv (mul_assoc _ _ _)
    · refine Prod.ext hp.symm ?_
      simp only [dif_pos (hmem t₀ ht₀)]
      exact Subtype.ext (by simp [hα0])
  unique c hc ℓ ℓ' h h' t₀ ht₀ e t ht := by
    obtain ⟨u, hu, hu'⟩ := h
    obtain ⟨v, hv, hv'⟩ := h'
    obtain ⟨m, hm⟩ := exists_nnbound ((continuous_potAlong hA hc).continuousOn (s := Icc 0 1))
    have h0 : u t₀ = v t₀ := by rw [← (hu t₀ ht₀).2, ← (hv t₀ ht₀).2, e]
    have huv := transport_unique _ m hm u v hu' hv' t₀ ht₀ h0 t ht
    exact Prod.ext ((hu t ht).1.trans (hv t ht).1.symm)
      (Subtype.ext ((hu t ht).2.trans (huv.trans (hv t ht).2.symm)))
  ract_lift c _ ℓ h g := by
    obtain ⟨u, hu, hu'⟩ := h
    refine ⟨fun t => u t * g, fun t ht => ⟨(hu t ht).1, ?_⟩, fun t ht => ?_⟩
    · change ((ℓ t).2 : ℍ[ℝ]) * g = u t * g
      rw [(hu t ht).2]
    · exact ((hu' t ht).mul_const _).congr_deriv (mul_assoc _ _ _)

/-- **[GG] Step 6 for genuine parallel transport.** If `s_N = s_S · θ` and both sections are
parallel along a `C¹` curve `c` for the connection `A`, then `θ` is constant along `c`. -/
theorem transport_theta_const (A : E → E →L[ℝ] ℍ[ℝ]) (hA : Continuous A)
    (hpure : ∀ x v, (A x v).re = 0) (sN sS : E → E × S3) (θ : E → S3)
    (hθ : ∀ ζ, sN ζ = ((sS ζ).1, (sS ζ).2 * θ ζ)) {c : ℝ → E} (hc : ContDiff ℝ 1 c)
    (hN : (transportLifts A hA hpure).IsLift c (sN ∘ c))
    (hS : (transportLifts A hA hpure).IsLift c (sS ∘ c))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) : ∀ t ∈ Icc (0 : ℝ) 1, θ (c t) = θ (c t₀) :=
  theta_const_along (transportLifts A hA hpure)
    (fun p g g' e => mul_left_cancel (Prod.ext_iff.1 e).2) sN sS θ hθ hc hN hS ht₀

end Lifts

/-! ## Non-vacuity: a non-constant connection on `ℝ²` -/

set_option synthInstance.maxHeartbeats 200000 in
/-- `A_{(x,y)} = x · dy ⊗ i` (curvature `dx ∧ dy ⊗ i ≠ 0`). -/
noncomputable def modelPot (x : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℍ[ℝ] :=
  x.1 • (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (qmk 0 1 0 0)

set_option synthInstance.maxHeartbeats 200000 in
theorem continuous_modelPot : Continuous modelPot := by
  unfold modelPot; fun_prop

set_option synthInstance.maxHeartbeats 200000 in
theorem modelPot_pure (x v : ℝ × ℝ) : (modelPot x v).re = 0 := by
  simp [modelPot, ContinuousLinearMap.smulRight_apply]

/-- The hypotheses of `transport_theta_const` are jointly satisfiable, for the non-constant
potential `modelPot` and the curve `t ↦ (t, t)`: take any horizontal lift `ℓ` through a point
(which `transportLifts` provides), `s_S = ℓ`, `s_N = ℓ · g`, `θ ≡ g`. -/
theorem transport_theta_model (g : sphere (0 : ℍ[ℝ]) 1) :
    ∃ (sN sS : ℝ × ℝ → (ℝ × ℝ) × sphere (0 : ℍ[ℝ]) 1) (θ : ℝ × ℝ → sphere (0 : ℍ[ℝ]) 1),
      (∀ ζ, sN ζ = ((sS ζ).1, (sS ζ).2 * θ ζ)) ∧
      (transportLifts modelPot continuous_modelPot modelPot_pure).IsLift
        (fun t => (t, t)) (sN ∘ fun t => (t, t)) ∧
      (transportLifts modelPot continuous_modelPot modelPot_pure).IsLift
        (fun t => (t, t)) (sS ∘ fun t => (t, t)) := by
  set L := transportLifts modelPot continuous_modelPot modelPot_pure
  have hc : ContDiff ℝ 1 (fun t : ℝ => (t, t)) := contDiff_id.prodMk contDiff_id
  obtain ⟨ℓ, hℓ, -⟩ := L.exists_lift _ hc 0 ⟨le_rfl, zero_le_one⟩ ((0, 0), 1) rfl
  refine ⟨fun ζ => ((ℓ ζ.1).1, (ℓ ζ.1).2 * g), fun ζ => ℓ ζ.1, fun _ => g,
    fun _ => rfl, L.ract_lift _ hc ℓ hℓ g, hℓ⟩

/-! ## Gauge covariance

A change of trivialisation `(b, s) ↦ (b, γ(b)⁻¹ s)` by a unit-valued `C¹` gauge `γ : E → S³`
transforms the potential to `A^γ = γ⁻¹Aγ + γ⁻¹dγ` ([GG] `eq:potentials`), and maps
`A`-horizontal lifts to `A^γ`-horizontal lifts. This is the compatibility needed to patch the
local transports of a non-trivial bundle across overlapping charts. -/

section Gauge

local notation "S3" => sphere (0 : ℍ[ℝ]) 1

/-- `ℍ` is a star module over `ℝ` (not found by instance search in the pinned Mathlib). -/
instance : StarModule ℝ ℍ[ℝ] :=
  ⟨fun r a => by ext <;> simp [star_trivial]⟩

theorem norm_qj : ‖qmk 0 0 1 0‖ = 1 := by
  have h : Quaternion.normSq (qmk 0 0 1 0) = 1 := by simp [Quaternion.normSq_def']
  rw [Quaternion.normSq_eq_norm_mul_self] at h
  nlinarith [norm_nonneg (qmk 0 0 1 0)]

theorem inv_eq_star_of_norm_one {q : ℍ[ℝ]} (h : ‖q‖ = 1) : q⁻¹ = star q := by
  rw [Quaternion.inv_def, Quaternion.normSq_eq_norm_mul_self, h, one_mul, inv_one, one_smul]

theorem ne_zero_of_norm_one {q : ℍ[ℝ]} (h : ‖q‖ = 1) : q ≠ 0 := by
  rintro rfl; simp at h

theorem mul_star_of_norm_one {q : ℍ[ℝ]} (h : ‖q‖ = 1) : q * star q = 1 := by
  rw [← inv_eq_star_of_norm_one h, mul_inv_cancel₀ (ne_zero_of_norm_one h)]

theorem star_mul_of_norm_one {q : ℍ[ℝ]} (h : ‖q‖ = 1) : star q * q = 1 := by
  rw [← inv_eq_star_of_norm_one h, inv_mul_cancel₀ (ne_zero_of_norm_one h)]

theorem re_mul_comm (a b : ℍ[ℝ]) : (a * b).re = (b * a).re := by
  simp only [Quaternion.re_mul]; ring

/-- For `g` unit-valued on `[0,1]`: `g'^* g + g^* g' = 0`. -/
theorem star_deriv_mul_add (g g' : ℝ → ℍ[ℝ])
    (hg : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt g (g' t) (Icc 0 1) t)
    (hgn : ∀ t ∈ Icc (0 : ℝ) 1, ‖g t‖ = 1) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    star (g' t) * g t + star (g t) * g' t = 0 := by
  have h1 := ((hg t ht).star).mul (hg t ht)
  have h2 : HasDerivWithinAt (fun _ : ℝ => (1 : ℍ[ℝ])) (star (g' t) * g t + star (g t) * g' t)
      (Icc 0 1) t :=
    h1.congr (fun s hs => (star_mul_of_norm_one (hgn s hs)).symm)
      (star_mul_of_norm_one (hgn t ht)).symm
  exact UniqueDiffWithinAt.eq_deriv _ (uniqueDiffOn_Icc zero_lt_one t ht) h2
    (hasDerivWithinAt_const _ _ _)

/-- **Gauge covariance of the transport equation.** If `u' = M u` and `g` is unit-valued, then
`w = g⁻¹u` solves `w' = (g⁻¹Mg − g⁻¹g') w`. -/
theorem gauge_ode (M g g' u : ℝ → ℍ[ℝ])
    (hg : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt g (g' t) (Icc 0 1) t)
    (hgn : ∀ t ∈ Icc (0 : ℝ) 1, ‖g t‖ = 1)
    (hu : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt u (M t * u t) (Icc 0 1) t) :
    ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun s => (g s)⁻¹ * u s)
      (((g t)⁻¹ * M t * g t - (g t)⁻¹ * g' t) * ((g t)⁻¹ * u t)) (Icc 0 1) t := by
  intro t ht
  have h1 := ((hg t ht).star).mul (hu t ht)
  have h0 := star_deriv_mul_add g g' hg hgn t ht
  have hgs := mul_star_of_norm_one (hgn t ht)
  have key : star (g' t) = -(star (g t) * g' t * star (g t)) := by
    have : star (g' t) * g t = -(star (g t) * g' t) := eq_neg_of_add_eq_zero_left h0
    calc star (g' t) = star (g' t) * (g t * star (g t)) := by rw [hgs, mul_one]
      _ = -(star (g t) * g' t * star (g t)) := by rw [← mul_assoc, this, neg_mul]
  refine (h1.congr (fun s hs => by simp only [inv_eq_star_of_norm_one (hgn s hs), Pi.mul_apply])
    (by simp only [inv_eq_star_of_norm_one (hgn t ht), Pi.mul_apply])).congr_deriv ?_
  rw [inv_eq_star_of_norm_one (hgn t ht), key]
  have hgs' : ∀ x, g t * (star (g t) * x) = x := fun x => by rw [← mul_assoc, hgs, one_mul]
  simp only [sub_mul, mul_assoc, hgs', neg_mul]
  abel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `A'` is the gauge transform `γ⁻¹Aγ + γ⁻¹dγ` of `A`. -/
def IsGaugeTransform (A A' : E → E →L[ℝ] ℍ[ℝ]) (γ : E → ℍ[ℝ]) (Dγ : E → E →L[ℝ] ℍ[ℝ]) :
    Prop :=
  ∀ x v, A' x v = (γ x)⁻¹ * A x v * γ x + (γ x)⁻¹ * Dγ x v

/-- The gauge transform of an `Im ℍ`-valued potential is `Im ℍ`-valued. -/
theorem gauge_pure {A A' : E → E →L[ℝ] ℍ[ℝ]} {γ : E → ℍ[ℝ]} {Dγ : E → E →L[ℝ] ℍ[ℝ]}
    (hpure : ∀ x v, (A x v).re = 0) (hγ : ∀ x, HasFDerivAt γ (Dγ x) x)
    (hunit : ∀ x, ‖γ x‖ = 1) (hG : IsGaugeTransform A A' γ Dγ) (x : E) (v : E) :
    (A' x v).re = 0 := by
  rw [hG, Quaternion.re_add, re_mul_comm, ← mul_assoc, mul_inv_cancel₀ (ne_zero_of_norm_one
    (hunit x)), one_mul, hpure, re_mul_comm, re_dtheta_mul_inv γ (Dγ x) x (hγ x) hunit v,
    add_zero]

/-- The change of trivialisation `(b, s) ↦ (b, γ(b)⁻¹ s)`. -/
noncomputable def gaugeMap (γ : E → ℍ[ℝ]) (hunit : ∀ x, ‖γ x‖ = 1) (p : E × S3) : E × S3 :=
  (p.1, ⟨(γ p.1)⁻¹ * p.2, by
    rw [mem_sphere_zero_iff_norm, norm_mul, norm_inv, hunit, inv_one, one_mul]
    exact mem_sphere_zero_iff_norm.1 p.2.2⟩)

/-- **Horizontal lifts are gauge-covariant.** A change of trivialisation by `γ` maps the
`A`-horizontal lifts of a `C¹` curve to `A^γ`-horizontal lifts. -/
theorem gauge_isLift {A A' : E → E →L[ℝ] ℍ[ℝ]} (hA : Continuous A) (hpure : ∀ x v, (A x v).re = 0)
    (hA' : Continuous A') (hpure' : ∀ x v, (A' x v).re = 0) {γ : E → ℍ[ℝ]}
    {Dγ : E → E →L[ℝ] ℍ[ℝ]} (hγ : ∀ x, HasFDerivAt γ (Dγ x) x) (hunit : ∀ x, ‖γ x‖ = 1)
    (hG : IsGaugeTransform A A' γ Dγ) {c : ℝ → E} (hc : ContDiff ℝ 1 c) {ℓ : ℝ → E × S3}
    (h : (transportLifts A hA hpure).IsLift c ℓ) :
    (transportLifts A' hA' hpure').IsLift c (gaugeMap γ hunit ∘ ℓ) := by
  obtain ⟨u, hu, hu'⟩ := h
  have hgd : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s => γ (c s)) (Dγ (c t) (deriv c t)) (Icc 0 1) t := fun t _ =>
    ((hγ (c t)).comp_hasDerivAt t ((hc.differentiable (by norm_num) t).hasDerivAt)).hasDerivWithinAt
  refine ⟨fun t => (γ (c t))⁻¹ * u t, fun t ht => ⟨(hu t ht).1, ?_⟩, fun t ht => ?_⟩
  · show (γ (ℓ t).1)⁻¹ * ((ℓ t).2 : ℍ[ℝ]) = _
    rw [(hu t ht).1, (hu t ht).2]
  · refine (gauge_ode _ _ _ u hgd (fun s _ => hunit _) hu' t ht).congr_deriv ?_
    simp only [potAlong, hG (c t) (deriv c t)]
    noncomm_ring

end Gauge

set_option synthInstance.maxHeartbeats 200000 in
/-- Non-vacuity of `gauge_isLift`: the constant gauge `γ ≡ j` applied to `modelPot`. -/
theorem gauge_model :
    ∃ (A' : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℍ[ℝ]) (hA' : Continuous A') (hpure' : ∀ x v, (A' x v).re = 0),
      IsGaugeTransform modelPot A' (fun _ => qmk 0 0 1 0) (fun _ => 0) ∧
      ∃ ℓ, (transportLifts modelPot continuous_modelPot modelPot_pure).IsLift (fun t => (t, t)) ℓ ∧
        (transportLifts A' hA' hpure').IsLift (fun t => (t, t))
          (gaugeMap (fun _ => qmk 0 0 1 0) (fun _ => norm_qj) ∘ ℓ) := by
  have hj := norm_qj
  let A' : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℍ[ℝ] := fun x =>
    (ContinuousLinearMap.mulLeftRight ℝ ℍ[ℝ] (qmk 0 0 1 0)⁻¹ (qmk 0 0 1 0)).comp (modelPot x)
  have hG : IsGaugeTransform modelPot A' (fun _ => qmk 0 0 1 0) (fun _ => 0) := fun x v => by
    simp [A', ContinuousLinearMap.mulLeftRight_apply]
  have hA' : Continuous A' := continuous_const.clm_comp continuous_modelPot
  have hpure' := gauge_pure modelPot_pure (fun _ => hasFDerivAt_const _ _) (fun _ => hj) hG
  have hc : ContDiff ℝ 1 (fun t : ℝ => (t, t)) := contDiff_id.prodMk contDiff_id
  obtain ⟨ℓ, hℓ, -⟩ := (transportLifts modelPot continuous_modelPot modelPot_pure).exists_lift
    _ hc 0 ⟨le_rfl, zero_le_one⟩ ((0, 0), 1) rfl
  exact ⟨A', hA', hpure', hG, ℓ, hℓ, gauge_isLift continuous_modelPot modelPot_pure hA' hpure'
    (fun _ => hasFDerivAt_const _ _) (fun _ => hj) hG hc hℓ⟩

end ExoticSpheres8And10
