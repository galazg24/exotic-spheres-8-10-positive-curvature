/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import Mathlib

/-! # B1, stage 2: continuous injective endomorphisms of the circle group

The topological input for B1. Mathlib (pinned `0df444a`) has no classification of continuous
endomorphisms of the circle group; this file proves the part we need, by lifting through the
covering map `Circle.exp : ℝ → S¹` (`Circle.isCoveringMap_exp`) with Mathlib's lifting theorem for
simply connected domains (`IsCoveringMap.existsUnique_continuousMap_lifts`).

* `circle_char`: every continuous homomorphism `g : ℝ → S¹` is `t ↦ exp(ct)`.
* `circle_endo`: every continuous injective endomorphism of `S¹` is `z ↦ z` or `z ↦ z⁻¹`.
-/

namespace ExoticSpheres8And10

open Real

theorem circle_exp_neg (t : ℝ) : Circle.exp (-t) = (Circle.exp t)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← Circle.exp_add, neg_add_cancel, Circle.exp_zero])

theorem circle_exp_two_pi : Circle.exp (2 * π) = 1 := by
  simpa using Circle.periodic_exp 0

/-- **Continuous characters of `ℝ` into the circle.** -/
theorem circle_char (g : ℝ → Circle) (hg : Continuous g) (hmul : ∀ s t, g (s + t) = g s * g t) :
    ∃ c : ℝ, ∀ t, g t = Circle.exp (c * t) := by
  have hg0 : g 0 = 1 := by
    have h := hmul 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := g 0) (by rw [mul_one]; exact h.symm)
  obtain ⟨F, ⟨hF0, hFl⟩, -⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
    (⟨g, hg⟩ : C(ℝ, Circle)) 0 0 (by simp [hg0])
  have hFt : ∀ t, Circle.exp (F t) = g t := fun t => congrFun hFl t
  -- additivity, from uniqueness of lifts
  have hadd : ∀ s t, F (s + t) = F s + F t := by
    intro s t
    obtain ⟨H, -, hu⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
      (⟨fun t => g (s + t), hg.comp (continuous_const.add continuous_id)⟩ : C(ℝ, Circle)) 0 (F s)
      (by simp [hFt])
    have h1 := hu ⟨fun t => F (s + t), F.continuous.comp (continuous_const.add continuous_id)⟩
      ⟨by simp, funext fun t => by simp [hFt]⟩
    have h2 := hu ⟨fun t => F s + F t, continuous_const.add F.continuous⟩
      ⟨by simp [hF0], funext fun t => by simp [Circle.exp_add, hFt, hmul]⟩
    have := congrArg (fun G : C(ℝ, ℝ) => G t) (h1.trans h2.symm)
    simpa using this
  let A : ℝ →+ ℝ := AddMonoidHom.mk' F hadd
  refine ⟨F 1, fun t => ?_⟩
  have hl := map_real_smul A F.continuous t 1
  simp only [smul_eq_mul, mul_one, A, AddMonoidHom.mk'_apply] at hl
  rw [← hFt, hl, mul_comm]

/-- **Continuous injective endomorphisms of the circle group are `z ↦ z^{±1}`.** -/
theorem circle_endo (χ : Circle →* Circle) (hc : Continuous χ) (hinj : Function.Injective χ) :
    (∀ z, χ z = z) ∨ (∀ z, χ z = z⁻¹) := by
  obtain ⟨c, hcg⟩ := circle_char (fun t => χ (Circle.exp t)) (hc.comp Circle.exp.continuous)
    (fun s t => by simp only [Circle.exp_add, map_mul])
  -- `c` is an integer
  have h1 : Circle.exp (c * (2 * π)) = Circle.exp 0 := by
    rw [← hcg, circle_exp_two_pi, map_one, Circle.exp_zero]
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.1 h1
  have hπ : 0 < 2 * π := by positivity
  have hcm : c = m := by
    have : c * (2 * π) = m * (2 * π) := by linarith
    exact mul_right_cancel₀ hπ.ne' this
  -- `m ≠ 0`
  have hm0 : m ≠ 0 := by
    rintro rfl
    have e : χ (Circle.exp π) = χ (Circle.exp 0) := by
      rw [hcg, hcg, hcm]; simp
    obtain ⟨k, hk⟩ := Circle.exp_eq_exp.1 (hinj e)
    have : (2 * k - 1 : ℝ) * π = 0 := by linarith
    have hk' : (2 * k - 1 : ℝ) = 0 := (mul_eq_zero.1 this).resolve_right Real.pi_ne_zero
    have : (2 * k - 1 : ℤ) = 0 := by exact_mod_cast hk'
    omega
  -- `m = ±1`: `exp(2π/m)` lies in the kernel
  have hmpm : m = 1 ∨ m = -1 := by
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm0
    have e : χ (Circle.exp (2 * π / m)) = χ (Circle.exp 0) := by
      rw [hcg, hcg, hcm, mul_div_cancel₀ _ hmR, circle_exp_two_pi]; simp
    obtain ⟨k, hk⟩ := Circle.exp_eq_exp.1 (hinj e)
    have hk1 : (k : ℝ) * m = 1 := by
      field_simp at hk
      nlinarith [Real.pi_pos]
    have hk2 : k * m = 1 := by exact_mod_cast hk1
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hk2 with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  rcases hmpm with h | h
  · left; intro z
    rw [← Circle.exp_arg z, hcg, hcm, h]; simp
  · right; intro z
    rw [← Circle.exp_arg z, hcg, hcm, h, ← circle_exp_neg]; simp

end ExoticSpheres8And10
