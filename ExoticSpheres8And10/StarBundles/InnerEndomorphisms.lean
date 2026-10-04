/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.StarBundles.CircleEndomorphisms
import ExoticSpheres8And10.StarBundles.Skeleton
import ExoticSpheres8And10.ActionField.Bound

/-! # B1, stage 1: every injective continuous endomorphism of `S³` is inner

Discharges the named hypothesis `InjContEndoInner` of B1 for `S³ = sphere (0 : ℍ) 1`, the group
of unit quaternions ([GG] `prop:polar`, Step 2: "An injective Lie group homomorphism `S³ → S³` is
an automorphism [...]. Every automorphism of `S³` is inner").

Route (no Lie theory): for an injective continuous endomorphism `φ`,
1. `φ(−1) = −1`, so `φ` maps pure units (`u² = −1`) to pure units;
2. for a pure unit `u`, `φ` maps the circle `{a + bu}` into the circle through `φ(u)`; by
   `circle_endo` (stage 2) the induced circle map is the identity (it fixes `i ↦ i`), so
   `φ(a + bu) = a + bφ(u)`; hence `φ` preserves real parts and inner products of pure units;
3. a frame rotation (`frame_rotation`) gives `c ≠ 0` with `c i c⁻¹ = φ(i)`, `c j c⁻¹ = φ(j)`;
4. coordinates then force `φ(u) = c u c⁻¹` for every pure unit `u`, hence `φ = Ad_c`.
-/

namespace ExoticSpheres8And10

open Quaternion Metric

/-! ## Quaternion algebra lemmas -/

section Alg

theorem normSq_eq_one_iff (x : ℍ[ℝ]) : normSq x = 1 ↔ ‖x‖ = 1 := by
  rw [normSq_eq_norm_mul_self]
  constructor
  · intro h
    rcases mul_self_eq_one_iff.1 h with h | h
    · exact h
    · linarith [norm_nonneg x]
  · intro h; rw [h, one_mul]

theorem sq_eq_one_quat {x : ℍ[ℝ]} (hx : normSq x = 1) (h : x * x = 1) : x = 1 ∨ x = -1 := by
  rw [normSq_def'] at hx
  have e0 := congrArg (fun q : ℍ[ℝ] => q.re) h
  simp only [Quaternion.re_mul, Quaternion.re_one] at e0
  have hs : x.imI ^ 2 + x.imJ ^ 2 + x.imK ^ 2 = 0 := by nlinarith
  have hI : x.imI = 0 := by nlinarith [sq_nonneg x.imI, sq_nonneg x.imJ, sq_nonneg x.imK]
  have hJ : x.imJ = 0 := by nlinarith [sq_nonneg x.imI, sq_nonneg x.imJ, sq_nonneg x.imK]
  have hK : x.imK = 0 := by nlinarith [sq_nonneg x.imI, sq_nonneg x.imJ, sq_nonneg x.imK]
  have hr : x.re * x.re = 1 := by nlinarith
  rcases mul_self_eq_one_iff.1 hr with h1 | h1
  · left; exact Quaternion.ext _ _ (by simp [h1]) (by simp [hI]) (by simp [hJ]) (by simp [hK])
  · right; exact Quaternion.ext _ _ (by simp [h1]) (by simp [hI]) (by simp [hJ]) (by simp [hK])

theorem sq_eq_neg_one_iff_quat {x : ℍ[ℝ]} (hx : normSq x = 1) : x * x = -1 ↔ x.re = 0 := by
  rw [normSq_def'] at hx
  constructor
  · intro h
    have e0 := congrArg (fun q : ℍ[ℝ] => q.re) h
    simp only [Quaternion.re_mul, Quaternion.re_neg, Quaternion.re_one] at e0
    nlinarith [sq_nonneg x.re]
  · intro h
    ext <;> simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
      h] <;> nlinarith

theorem re_mul_comm_quat (x y : ℍ[ℝ]) : (x * y).re = (y * x).re := by
  simp only [Quaternion.re_mul]; ring

theorem re_pure_mul {u w : ℍ[ℝ]} (hu : u.re = 0) (hw : w.re = 0) : (u * w).re = -qdot u w := by
  simp only [Quaternion.re_mul, qdot, hu, hw]; ring

theorem anticomm_of_orth {u w : ℍ[ℝ]} (hu : u.re = 0) (hw : w.re = 0) (h : qdot u w = 0) :
    u * w = -(w * u) := by
  simp only [qdot] at h
  ext
  · simp only [Quaternion.re_mul, Quaternion.re_neg, hu, hw]; linear_combination (-2 : ℝ) * h
  · simp only [Quaternion.imI_mul, Quaternion.imI_neg, hu, hw]; ring
  · simp only [Quaternion.imJ_mul, Quaternion.imJ_neg, hu, hw]; ring
  · simp only [Quaternion.imK_mul, Quaternion.imK_neg, hu, hw]; ring

theorem re_conj_quat {c : ℍ[ℝ]} (hc : c ≠ 0) (x : ℍ[ℝ]) : (c * x * c⁻¹).re = x.re := by
  rw [re_mul_comm_quat, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem normSq_conj_quat {c : ℍ[ℝ]} (hc : c ≠ 0) (x : ℍ[ℝ]) :
    normSq (c * x * c⁻¹) = normSq x := by
  have hn : normSq c ≠ 0 := fun h => hc (normSq_eq_zero.1 h)
  rw [map_mul, map_mul, map_inv₀]
  field_simp

theorem qdot_comm (u w : ℍ[ℝ]) : qdot u w = qdot w u := by simp only [qdot]; ring

/-- A quaternion commuting with a pure unit `u` lies in `span{1, u}`. -/
theorem centralizer_pure {u q : ℍ[ℝ]} (hu : u.re = 0) (hn : normSq u = 1) (h : q * u = u * q) :
    q = q.re • (1 : ℍ[ℝ]) + qdot q u • u := by
  rw [normSq_def', hu] at hn
  have hn' : u.imI ^ 2 + u.imJ ^ 2 + u.imK ^ 2 - 1 = 0 := by linarith
  have eI := congrArg (fun q : ℍ[ℝ] => q.imI) h
  have eJ := congrArg (fun q : ℍ[ℝ] => q.imJ) h
  have eK := congrArg (fun q : ℍ[ℝ] => q.imK) h
  simp only [Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, hu] at eI eJ eK
  have rI : q.imJ * u.imK - q.imK * u.imJ = 0 := by linarith
  have rJ : q.imK * u.imI - q.imI * u.imK = 0 := by linarith
  have rK : q.imI * u.imJ - q.imJ * u.imI = 0 := by linarith
  ext
  · simp [hu]
  · simp only [Quaternion.imI_add, Quaternion.imI_smul, Quaternion.imI_one, smul_eq_mul, qdot]
    linear_combination u.imJ * rK - u.imK * rJ - q.imI * hn'
  · simp only [Quaternion.imJ_add, Quaternion.imJ_smul, Quaternion.imJ_one, smul_eq_mul, qdot]
    linear_combination -u.imI * rK + u.imK * rI - q.imJ * hn'
  · simp only [Quaternion.imK_add, Quaternion.imK_smul, Quaternion.imK_one, smul_eq_mul, qdot]
    linear_combination u.imI * rJ - u.imJ * rI - q.imK * hn'

/-- The rotation `c = 1 − ba` conjugates the pure unit `a` to the pure unit `b` (`a ≠ −b`). -/
theorem rotation_pair {a b : ℍ[ℝ]} (ha : a * a = -1) (hb : b * b = -1) (hab : a ≠ -b) :
    (1 - b * a) ≠ 0 ∧ (1 - b * a) * a = b * (1 - b * a) := by
  constructor
  · intro h
    have h1 : b * a = 1 := by rw [sub_eq_zero] at h; exact h.symm
    apply hab
    have : b * a * a = a := by rw [h1, one_mul]
    rw [mul_assoc, ha, mul_neg, mul_one] at this
    exact this.symm
  · simp only [sub_mul, mul_sub, one_mul, mul_one, mul_assoc, ha, ← mul_assoc b b a, hb]
    noncomm_ring

/-- **Frame rotation.** For orthonormal pure units `e₁, e₂` there is `c ≠ 0` with
`c i = e₁ c` and `c j = e₂ c`. -/
theorem frame_rotation {e1 e2 : ℍ[ℝ]} (h1r : e1.re = 0) (h1n : normSq e1 = 1) (h2r : e2.re = 0)
    (h2n : normSq e2 = 1) (h12 : qdot e1 e2 = 0) :
    ∃ c : ℍ[ℝ], c ≠ 0 ∧ c * qmk 0 1 0 0 = e1 * c ∧ c * qmk 0 0 1 0 = e2 * c := by
  set I := qmk 0 1 0 0
  set J := qmk 0 0 1 0
  have hII : I * I = -1 := by ext <;> simp [I, Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul]
  have hJJ : J * J = -1 := by ext <;> simp [J, Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul]
  have he1 : e1 * e1 = -1 := (sq_eq_neg_one_iff_quat h1n).2 h1r
  have he2 : e2 * e2 = -1 := (sq_eq_neg_one_iff_quat h2n).2 h2r
  -- step A: `c₁ i = e₁ c₁`
  obtain ⟨c1, hc1, hc1i⟩ : ∃ c1 : ℍ[ℝ], c1 ≠ 0 ∧ c1 * I = e1 * c1 := by
    by_cases hA : I = -e1
    · refine ⟨J, fun h => by simpa [J] using congrArg (fun q : ℍ[ℝ] => q.imJ) h, ?_⟩
      have : e1 = -I := by rw [hA, neg_neg]
      rw [this]
      ext <;> simp [I, J, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
        Quaternion.imK_mul]
    · exact ⟨_, (rotation_pair hII he1 hA).1, (rotation_pair hII he1 hA).2⟩
  set x := c1 * J * c1⁻¹ with hx
  have hxc : x * c1 = c1 * J := by rw [hx, mul_assoc, inv_mul_cancel₀ hc1, mul_one]
  have hxr : x.re = 0 := by rw [hx, re_conj_quat hc1]; simp [J]
  have hxn : normSq x = 1 := by
    rw [hx, normSq_conj_quat hc1, normSq_def']; simp [J]
  have he1c : e1 = c1 * I * c1⁻¹ := by rw [hc1i, mul_assoc, mul_inv_cancel₀ hc1, mul_one]
  have hxe1 : qdot x e1 = 0 := by
    have hre : (x * e1).re = 0 := by
      rw [hx, he1c]
      have : c1 * J * c1⁻¹ * (c1 * I * c1⁻¹) = c1 * (J * I) * c1⁻¹ := by
        simp only [mul_assoc, inv_mul_cancel_left₀ hc1]
      rw [this, re_conj_quat hc1]
      simp [I, J, Quaternion.re_mul]
    have := re_pure_mul hxr h1r
    linarith
  have hxx : x * x = -1 := (sq_eq_neg_one_iff_quat hxn).2 hxr
  -- step B: `c₂ x = e₂ c₂` and `c₂ e₁ = e₁ c₂`
  obtain ⟨c2, hc2, hc2x, hc2e⟩ : ∃ c2 : ℍ[ℝ], c2 ≠ 0 ∧ c2 * x = e2 * c2 ∧ c2 * e1 = e1 * c2 := by
    have hax : x * e1 = -(e1 * x) := anticomm_of_orth hxr h1r hxe1
    have hae : e2 * e1 = -(e1 * e2) := anticomm_of_orth h2r h1r (by rw [qdot_comm]; exact h12)
    by_cases hB : x = -e2
    · refine ⟨e1, fun h => by rw [h] at h1n; simp at h1n, ?_, rfl⟩
      have : e2 = -x := by rw [hB, neg_neg]
      rw [this, neg_mul, hax, neg_neg]
    · refine ⟨_, (rotation_pair hxx he2 hB).1, (rotation_pair hxx he2 hB).2, ?_⟩
      simp only [sub_mul, mul_sub, one_mul, mul_one, mul_assoc, hax]
      rw [mul_neg, ← mul_assoc e2 e1 x, hae]
      noncomm_ring
  refine ⟨c2 * c1, mul_ne_zero hc2 hc1, ?_, ?_⟩
  · rw [mul_assoc, hc1i, ← mul_assoc, hc2e, mul_assoc]
  · rw [mul_assoc, ← hxc, ← mul_assoc, hc2x, mul_assoc]

/-- Conjugation by `t • c` equals conjugation by `c` (`t ≠ 0` real). -/
theorem conj_smul_quat {c : ℍ[ℝ]} (hc : c ≠ 0) {t : ℝ} (ht : t ≠ 0) (x : ℍ[ℝ]) :
    (t • c) * x * (t • c)⁻¹ = c * x * c⁻¹ := by
  have hct : t • c = (t : ℍ[ℝ]) * c := (Quaternion.coe_mul_eq_smul t c).symm
  have htq : (t : ℍ[ℝ]) ≠ 0 := by
    intro h; apply ht; have := congrArg (fun q : ℍ[ℝ] => q.re) h; simpa using this
  rw [hct, mul_inv_rev]
  have e : (t : ℍ[ℝ]) * c * x * (c⁻¹ * (t : ℍ[ℝ])⁻¹) = ((t : ℍ[ℝ]) * (c * x * c⁻¹)) * (t : ℍ[ℝ])⁻¹ := by
    simp only [mul_assoc]
  rw [e, Quaternion.coe_commutes, mul_assoc, mul_inv_cancel₀ htq, mul_one]

end Alg

/-! ## Circles in `S³` -/

section Circles

/-- `z ↦ Re z · 1 + Im z · u`, the circle through the pure unit `u`. -/
noncomputable def eU (u : ℍ[ℝ]) (z : ℂ) : ℍ[ℝ] := z.re • (1 : ℍ[ℝ]) + z.im • u

theorem eU_mul {u : ℍ[ℝ]} (hu : u.re = 0) (hn : normSq u = 1) (z w : ℂ) :
    eU u (z * w) = eU u z * eU u w := by
  have hu2 : u * u = -1 := (sq_eq_neg_one_iff_quat hn).2 hu
  simp only [eU, Complex.mul_re, Complex.mul_im, add_mul, mul_add, smul_mul_smul, one_mul,
    mul_one, hu2, smul_neg, smul_mul_assoc, mul_smul_comm]
  module

theorem normSq_eU {u : ℍ[ℝ]} (hu : u.re = 0) (hn : normSq u = 1) (z : ℂ) :
    normSq (eU u z) = Complex.normSq z := by
  rw [normSq_def'] at hn ⊢
  rw [hu] at hn
  simp only [eU, Quaternion.re_add, Quaternion.re_smul, Quaternion.imI_add, Quaternion.imI_smul,
    Quaternion.imJ_add, Quaternion.imJ_smul, Quaternion.imK_add, Quaternion.imK_smul,
    Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one, hu,
    smul_eq_mul, Complex.normSq_apply]
  linear_combination z.im ^ 2 * hn

/-- Coordinates along the circle through `v`: `q ↦ Re q + ⟨q, v⟩ i`. -/
def rC (v q : ℍ[ℝ]) : ℂ := ⟨q.re, qdot q v⟩

theorem rC_eU {v : ℍ[ℝ]} (hv : v.re = 0) (hn : normSq v = 1) (z : ℂ) : rC v (eU v z) = z := by
  rw [normSq_def', hv] at hn
  apply Complex.ext
  · simp [rC, eU, Quaternion.re_smul, hv]
  · simp only [rC, eU, qdot, Quaternion.imI_add, Quaternion.imI_smul, Quaternion.imJ_add,
      Quaternion.imJ_smul, Quaternion.imK_add, Quaternion.imK_smul, Quaternion.imI_one,
      Quaternion.imJ_one, Quaternion.imK_one, smul_eq_mul]
    linear_combination z.im * hn

theorem eU_rC {v q : ℍ[ℝ]} (hv : v.re = 0) (hn : normSq v = 1) (h : q * v = v * q) :
    eU v (rC v q) = q := by
  rw [centralizer_pure hv hn h]
  conv_rhs => rw [centralizer_pure hv hn h]
  simp only [eU, rC]

theorem eU_injective {u : ℍ[ℝ]} (hu : u.re = 0) (hn : normSq u = 1) :
    Function.Injective (eU u) := fun z w h => by
  have := congrArg (rC u) h
  rwa [rC_eU hu hn, rC_eU hu hn] at this

theorem eU_commutes {u : ℍ[ℝ]} (z : ℂ) : eU u z * u = u * eU u z := by
  simp only [eU, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

theorem continuous_eU (u : ℍ[ℝ]) : Continuous (eU u) := by
  unfold eU
  fun_prop

theorem continuous_rC (v : ℍ[ℝ]) : Continuous (rC v) := by
  have e : rC v = fun q : ℍ[ℝ] => ((q.re : ℂ) + ((qdot q v : ℝ) : ℂ) * Complex.I) := by
    funext q; apply Complex.ext <;> simp [rC]
  rw [e]
  unfold qdot
  have h0 := Quaternion.continuous_re
  have h1 := Quaternion.continuous_imI
  have h2 := Quaternion.continuous_imJ
  have h3 := Quaternion.continuous_imK
  have hr : Continuous fun q : ℍ[ℝ] => q.imI * v.imI + q.imJ * v.imJ + q.imK * v.imK := by
    fun_prop
  exact (Complex.continuous_ofReal.comp h0).add
    ((Complex.continuous_ofReal.comp hr).mul continuous_const)

end Circles

/-! ## The main theorem -/

local notation "S3" => sphere (0 : ℍ[ℝ]) 1

theorem normSq_coe_S3 (q : S3) : normSq (q : ℍ[ℝ]) = 1 :=
  (normSq_eq_one_iff _).2 (mem_sphere_zero_iff_norm.1 q.2)

/-- An element of `S³` from a quaternion of norm one. -/
def mkS (x : ℍ[ℝ]) (hx : normSq x = 1) : S3 := ⟨x, mem_sphere_zero_iff_norm.2 ((normSq_eq_one_iff x).1 hx)⟩

/-- An element of the circle group from a complex number of norm one. -/
def mkC (w : ℂ) (hw : Complex.normSq w = 1) : Circle :=
  ⟨w, mem_sphere_zero_iff_norm.2 (by
    have := Complex.normSq_eq_norm_sq w
    rw [hw] at this
    nlinarith [norm_nonneg w, sq_nonneg (‖w‖ - 1)])⟩

theorem coe_mul_S3 (a b : S3) : ((a * b : S3) : ℍ[ℝ]) = a * b := rfl
theorem coe_one_S3 : ((1 : S3) : ℍ[ℝ]) = 1 := rfl
theorem coe_inv_S3 (a : S3) : ((a⁻¹ : S3) : ℍ[ℝ]) = (a : ℍ[ℝ])⁻¹ := Metric.unitSphere.coe_inv a

/-- Every unit quaternion is `±1` or lies on the circle through some pure unit. -/
theorem unit_decomp {q : ℍ[ℝ]} (hq : normSq q = 1) :
    (q = 1 ∨ q = -1) ∨ ∃ u : ℍ[ℝ], u.re = 0 ∧ normSq u = 1 ∧
      ∃ z : ℂ, Complex.normSq z = 1 ∧ q = eU u z := by
  rw [normSq_def'] at hq
  set s := Real.sqrt (q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2) with hs
  have hs2 : s ^ 2 = q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 := Real.sq_sqrt (by positivity)
  by_cases h0 : s = 0
  · left
    have hsum : q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 = 0 := by rw [← hs2, h0]; ring
    have hI : q.imI = 0 := by nlinarith [sq_nonneg q.imI, sq_nonneg q.imJ, sq_nonneg q.imK]
    have hJ : q.imJ = 0 := by nlinarith [sq_nonneg q.imI, sq_nonneg q.imJ, sq_nonneg q.imK]
    have hK : q.imK = 0 := by nlinarith [sq_nonneg q.imI, sq_nonneg q.imJ, sq_nonneg q.imK]
    have hr : q.re * q.re = 1 := by nlinarith
    rcases mul_self_eq_one_iff.1 hr with h1 | h1
    · left; exact Quaternion.ext _ _ (by simp [h1]) (by simp [hI]) (by simp [hJ]) (by simp [hK])
    · right; exact Quaternion.ext _ _ (by simp [h1]) (by simp [hI]) (by simp [hJ]) (by simp [hK])
  · right
    refine ⟨qmk 0 (q.imI / s) (q.imJ / s) (q.imK / s), rfl, ?_, ⟨q.re, s⟩, ?_, ?_⟩
    · rw [normSq_def']; simp only [qmk_re, qmk_imI, qmk_imJ, qmk_imK]
      field_simp; linarith
    · rw [Complex.normSq_apply]; simp only; nlinarith
    · ext <;> simp [eU, Quaternion.re_smul] <;> field_simp

section Main

variable (φ : S3 →* S3) (hinj : Function.Injective φ) (hcont : Continuous φ)

theorem phi_mul_coe (a b : S3) : ((φ (a * b) : S3) : ℍ[ℝ]) = (φ a : ℍ[ℝ]) * φ b := by
  rw [map_mul, coe_mul_S3]

include hinj in
theorem phi_neg_one (m1 : S3) (hm : (m1 : ℍ[ℝ]) = -1) : ((φ m1 : S3) : ℍ[ℝ]) = -1 := by
  have hm1 : m1 * m1 = 1 := Subtype.ext (by rw [coe_mul_S3, hm, coe_one_S3]; norm_num)
  have h := phi_mul_coe φ m1 m1
  rw [hm1, map_one, coe_one_S3] at h
  rcases sq_eq_one_quat (normSq_coe_S3 (φ m1)) h.symm with h1 | h1
  · exfalso
    have : φ m1 = φ 1 := Subtype.ext (by rw [map_one, coe_one_S3]; exact h1)
    have h2 := congrArg (fun a : S3 => (a : ℍ[ℝ])) (hinj this)
    simp only [hm, coe_one_S3] at h2
    have := congrArg (fun q : ℍ[ℝ] => q.re) h2
    norm_num at this
  · exact h1

include hinj in
theorem phi_pure (p : S3) (hp : (p : ℍ[ℝ]).re = 0) : ((φ p : S3) : ℍ[ℝ]).re = 0 := by
  have hpp : ((p * p : S3) : ℍ[ℝ]) = -1 := by
    rw [coe_mul_S3]; exact (sq_eq_neg_one_iff_quat (normSq_coe_S3 p)).2 hp
  have h := phi_mul_coe φ p p
  rw [phi_neg_one φ hinj _ hpp] at h
  exact (sq_eq_neg_one_iff_quat (normSq_coe_S3 _)).1 h.symm

theorem phi_commute (a b : S3) (h : (a : ℍ[ℝ]) * b = b * a) :
    ((φ a : S3) : ℍ[ℝ]) * φ b = (φ b : ℍ[ℝ]) * φ a := by
  have hab : a * b = b * a := Subtype.ext (by rw [coe_mul_S3, coe_mul_S3]; exact h)
  rw [← phi_mul_coe, ← phi_mul_coe, hab]

include hinj hcont in
/-- **The circle maps.** On the circle through a pure unit `u`, `φ(a + bu) = a + bφ(u)`. -/
theorem phi_circle (u : S3) (hu : (u : ℍ[ℝ]).re = 0) (z : ℂ) (hz : Complex.normSq z = 1)
    (q : S3) (hq : (q : ℍ[ℝ]) = eU u z) : ((φ q : S3) : ℍ[ℝ]) = eU (φ u) z := by
  have hun := normSq_coe_S3 u
  set v : ℍ[ℝ] := (φ u : ℍ[ℝ]) with hvdef
  have hv : v.re = 0 := phi_pure φ hinj u hu
  have hvn : normSq v = 1 := normSq_coe_S3 _
  -- the circle as a subgroup of `S³`
  let eS : Circle → S3 := fun w => mkS (eU u w) (by rw [normSq_eU hu hun, Circle.normSq_coe])
  have heS_comm : ∀ w : Circle, ((φ (eS w) : S3) : ℍ[ℝ]) * v = v * φ (eS w) := fun w =>
    phi_commute φ (eS w) u (eU_commutes w)
  have heS_mul : ∀ w w' : Circle, eS (w * w') = eS w * eS w' := fun w w' =>
    Subtype.ext (by simp only [eS, mkS, coe_mul_S3, Circle.coe_mul]; exact eU_mul hu hun _ _)
  have hr_norm : ∀ w : Circle, Complex.normSq (rC v (φ (eS w))) = 1 := fun w => by
    rw [← normSq_eU hv hvn, eU_rC hv hvn (heS_comm w)]; exact normSq_coe_S3 _
  let χ : Circle →* Circle :=
    { toFun := fun w => mkC (rC v (φ (eS w))) (hr_norm w)
      map_one' := by
        apply Subtype.ext
        have h1 : eS 1 = 1 := Subtype.ext (by
          simp only [eS, mkS, Circle.coe_one, coe_one_S3]
          ext <;> simp [eU, Quaternion.re_smul])
        simp only [mkC, h1, map_one, coe_one_S3, Circle.coe_one]
        apply Complex.ext <;> simp [rC, qdot]
      map_mul' := fun w w' => by
        apply Subtype.ext
        show rC v (φ (eS (w * w'))) = rC v (φ (eS w)) * rC v (φ (eS w'))
        rw [heS_mul, phi_mul_coe]
        have ha := eU_rC hv hvn (heS_comm w)
        have hb := eU_rC hv hvn (heS_comm w')
        conv_lhs => rw [← ha, ← hb, ← eU_mul hv hvn]
        rw [rC_eU hv hvn] }
  have hχ : ∀ w, (χ w : ℂ) = rC v (φ (eS w)) := fun w => rfl
  have hχc : Continuous χ := by
    apply Continuous.subtype_mk
    exact (continuous_rC v).comp (continuous_subtype_val.comp (hcont.comp
      (Continuous.subtype_mk (continuous_eU u |>.comp continuous_subtype_val) _)))
  have hχi : Function.Injective χ := by
    intro w w' h
    have h1 := congrArg (fun a : Circle => (a : ℂ)) h
    simp only [hχ] at h1
    have h2 : ((φ (eS w) : S3) : ℍ[ℝ]) = φ (eS w') := by
      rw [← eU_rC hv hvn (heS_comm w), ← eU_rC hv hvn (heS_comm w'), h1]
    have h3 := hinj (Subtype.ext h2)
    have h4 := congrArg (fun a : S3 => (a : ℍ[ℝ])) h3
    simp only [eS, mkS] at h4
    exact Subtype.ext (eU_injective hu hun h4)
  -- `χ(i) = i`, so `χ = id`
  have hI : Complex.normSq Complex.I = 1 := by simp
  have heSI : eS (mkC Complex.I hI) = u := Subtype.ext (by
    simp only [eS, mkS, mkC]; ext <;> simp [eU, Quaternion.re_smul])
  have hχI : (χ (mkC Complex.I hI) : ℂ) = Complex.I := by
    rw [hχ, heSI, ← hvdef]
    have hvv : qdot v v = 1 := by rw [normSq_def', hv] at hvn; simp only [qdot]; linarith
    apply Complex.ext <;> simp [rC, hv, hvv]
  have hid : ∀ w, χ w = w := by
    rcases circle_endo χ hχc hχi with h | h
    · exact h
    · exfalso
      have h4 := hχI
      rw [h, Circle.coe_inv] at h4
      have h5 : (Complex.I)⁻¹ = Complex.I := h4
      rw [Complex.inv_I] at h5
      have := congrArg Complex.im h5
      simp at this
      norm_num at this
  -- conclude
  have hq' : q = eS (mkC z hz) := Subtype.ext (by simp only [eS, mkS, mkC]; exact hq)
  have h6 : rC v (φ (eS (mkC z hz))) = z := congrArg (fun a : Circle => (a : ℂ)) (hid (mkC z hz))
  rw [hq', ← eU_rC hv hvn (heS_comm _), h6]

include hinj hcont in
/-- `φ` preserves real parts. -/
theorem phi_re (q : S3) : ((φ q : S3) : ℍ[ℝ]).re = (q : ℍ[ℝ]).re := by
  rcases unit_decomp (normSq_coe_S3 q) with (h | h) | ⟨u, hu, hun, z, hz, hq⟩
  · have : q = 1 := Subtype.ext (by rw [h, coe_one_S3])
    rw [this, map_one, coe_one_S3]
  · rw [phi_neg_one φ hinj q h, h]
  · rw [phi_circle φ hinj hcont (mkS u hun) hu z hz q hq, hq]
    simp [eU, Quaternion.re_smul, phi_pure φ hinj (mkS u hun) hu, hu]

include hinj hcont in
/-- `φ` preserves inner products of pure units. -/
theorem phi_qdot (u w : S3) (hu : (u : ℍ[ℝ]).re = 0) (hw : (w : ℍ[ℝ]).re = 0) :
    qdot (φ u : ℍ[ℝ]) (φ w) = qdot (u : ℍ[ℝ]) w := by
  have h1 := re_pure_mul (phi_pure φ hinj u hu) (phi_pure φ hinj w hw)
  have h2 := re_pure_mul hu hw
  have h3 := phi_re φ hinj hcont (u * w)
  rw [phi_mul_coe, coe_mul_S3] at h3
  linarith

end Main

/-- **B1's named hypothesis, discharged for `S³`.** Every injective continuous endomorphism of
the group of unit quaternions is conjugation by a unit quaternion. -/
theorem injContEndoInner_S3 : InjContEndoInner S3 := by
  intro φ hinj hcont
  let iS := mkS (qmk 0 1 0 0) (by rw [normSq_def']; simp)
  let jS := mkS (qmk 0 0 1 0) (by rw [normSq_def']; simp)
  let kS := mkS (qmk 0 0 0 1) (by rw [normSq_def']; simp)
  have hiR : (iS : ℍ[ℝ]).re = 0 := rfl
  have hjR : (jS : ℍ[ℝ]).re = 0 := rfl
  have hkR : (kS : ℍ[ℝ]).re = 0 := rfl
  have hij : iS * jS = kS := Subtype.ext (by
    simp only [coe_mul_S3, iS, jS, kS, mkS]
    ext <;> simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul])
  set e1 : ℍ[ℝ] := (φ iS : ℍ[ℝ])
  set e2 : ℍ[ℝ] := (φ jS : ℍ[ℝ])
  have h12 : qdot e1 e2 = 0 := by
    rw [phi_qdot φ hinj hcont iS jS hiR hjR]; simp [iS, jS, mkS, qdot]
  obtain ⟨c, hc, hci, hcj⟩ := frame_rotation (phi_pure φ hinj iS hiR) (normSq_coe_S3 _)
    (phi_pure φ hinj jS hjR) (normSq_coe_S3 _) h12
  have hck : c * qmk 0 0 0 1 = (φ kS : ℍ[ℝ]) * c := by
    have : qmk 0 0 0 1 = qmk 0 1 0 0 * qmk 0 0 1 0 := by
      ext <;> simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
    rw [← hij, phi_mul_coe, this, ← mul_assoc, hci, mul_assoc, hcj, ← mul_assoc]
  have hc' : c⁻¹ ≠ 0 := inv_ne_zero hc
  -- every pure unit is conjugated by `c`
  have hpure_conj : ∀ u : S3, (u : ℍ[ℝ]).re = 0 → (φ u : ℍ[ℝ]) = c * u * c⁻¹ := by
    intro u hu
    set w := c⁻¹ * (φ u : ℍ[ℝ]) * c with hw
    have hwr : w.re = 0 := by
      have := re_conj_quat hc' (φ u : ℍ[ℝ])
      rw [inv_inv] at this
      rw [hw, this, phi_pure φ hinj u hu]
    have coord : ∀ (b : S3) (hbR : (b : ℍ[ℝ]).re = 0),
        c * (b : ℍ[ℝ]) = (φ b : ℍ[ℝ]) * c → qdot w b = qdot (u : ℍ[ℝ]) b := by
      intro b hbR hcb
      have hwb : (w * b).re = ((φ u : ℍ[ℝ]) * φ b).re := by
        rw [hw, mul_assoc, mul_assoc, hcb, ← mul_assoc, ← mul_assoc]
        have := re_conj_quat hc' ((φ u : ℍ[ℝ]) * φ b)
        rw [inv_inv] at this
        rw [← this]; simp only [mul_assoc]
      have e1' := re_pure_mul hwr hbR
      have e2' := re_pure_mul (phi_pure φ hinj u hu) (phi_pure φ hinj b hbR)
      have e3 := phi_qdot φ hinj hcont u b hu hbR
      linarith
    have cI := coord iS hiR hci
    have cJ := coord jS hjR hcj
    have cK := coord kS hkR hck
    simp only [iS, jS, kS, mkS, qdot, qmk_imI, qmk_imJ, qmk_imK] at cI cJ cK
    have hwu : w = u := Quaternion.ext _ _ (by rw [hwr, hu]) (by linarith) (by linarith)
      (by linarith)
    rw [← hwu, hw]
    simp only [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
    rw [mul_assoc, mul_inv_cancel₀ hc, mul_one]
  -- all of `S³`
  have hall : ∀ q : S3, (φ q : ℍ[ℝ]) = c * q * c⁻¹ := by
    intro q
    rcases unit_decomp (normSq_coe_S3 q) with (h | h) | ⟨u, hu, hun, z, hz, hq⟩
    · have : q = 1 := Subtype.ext (by rw [h, coe_one_S3])
      rw [this, map_one, coe_one_S3, mul_one, mul_inv_cancel₀ hc]
    · rw [phi_neg_one φ hinj q h, h, mul_neg, mul_one, neg_mul, mul_inv_cancel₀ hc]
    · rw [phi_circle φ hinj hcont (mkS u hun) hu z hz q hq, hq,
        hpure_conj (mkS u hun) hu]
      simp only [eU, mkS, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one,
        mul_inv_cancel₀ hc]
  -- normalise `c`
  have hcn : 0 < ‖c‖ := norm_pos_iff.2 hc
  refine ⟨mkS ((‖c‖)⁻¹ • c) (by
    rw [normSq_eq_one_iff, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hcn.ne']), fun q => ?_⟩
  apply Subtype.ext
  rw [coe_mul_S3, coe_mul_S3, coe_inv_S3, hall]
  simp only [mkS]
  rw [conj_smul_quat hc (inv_ne_zero hcn.ne')]

set_option synthInstance.maxHeartbeats 200000 in
/-- **B1 for `S³`, with the imported fact discharged.** [GG] Step 2's model point exists for any
right action of `S³` on `P` free on the orbit of `p₀`, a commuting left action preserving that
orbit and free at `p₀`, provided `φ` is continuous (in [GG], `φ` is smooth). The hypothesis
`InjContEndoInner` of `exists_model_point` is now a theorem. -/
theorem exists_model_point_S3 {P : Type*} [MulAction S3 P] [MulAction S3ᵐᵒᵖ P]
    [SMulCommClass S3 S3ᵐᵒᵖ P] (p₀ : P)
    (hfib : ∀ q : S3, ∃ h : S3, q • p₀ = ract p₀ h)
    (hfree : ∀ h h' : S3, ract p₀ h = ract p₀ h' → h = h')
    (hfreeS : ∀ q : S3, q • p₀ = p₀ → q = 1)
    (hcont : Continuous (phiHom p₀ hfib hfree)) :
    ∃ c : S3, ∀ q : S3, q • ract p₀ c = ract (ract p₀ c) q :=
  exists_model_point injContEndoInner_S3 p₀ hfib hfree hfreeS hcont

set_option synthInstance.maxHeartbeats 200000 in
/-- Non-vacuity: the model `P = S³` (left and right multiplication, `p₀ = 1`) fires. -/
example : ∃ c : S3, ∀ q : S3, q • ract (1 : S3) c = ract (ract (1 : S3) c) q :=
  exists_model_point_S3 (1 : S3) (left_right_hyps S3).1 (left_right_hyps S3).2.1
    (left_right_hyps S3).2.2 (by
      have : (phiHom (1 : S3) (left_right_hyps S3).1 (left_right_hyps S3).2.1 : S3 → S3) = id := by
        funext q
        have h := phiHom_spec (1 : S3) (left_right_hyps S3).1 (left_right_hyps S3).2.1 q
        simp only [ract, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, one_mul,
          smul_eq_mul, mul_one] at h
        exact h.symm
      rw [this]; exact continuous_id)

end ExoticSpheres8And10
