/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Main.TheoremsAB
import ExoticSpheres8And10.Main.GroupTheory

/-! # [D] Corollary C: logical bookkeeping, not geometry

[D] Corollary C: "Every smooth homotopy 8-sphere admits positive sectional curvature. A smooth
homotopy 10-sphere admits positive sectional curvature if and only if it admits positive scalar
curvature."

Mathlib has no `Θₙ`. So this file states the deduction for an abstract group `Θ` and two
predicates on it:
- `SEC` (admits `sec > 0`);
- `PSC` (admits `scal > 0`).

Every input is a named hypothesis:
- `Θ₁₀ ≃ ℤ/6` and `Θ₈ ≃ ℤ/2` (Kervaire–Milnor);
- `α : Θ₁₀ → ℤ/2` is a nonzero homomorphism, and `PSC → α = 0` (Hitchin);
- `SEC → PSC` (trace);
- `SEC 0` (the round sphere);
- `SEC` for the class `g` of Sperança's quotient. That class is a generator of the order-3
  subgroup, resp. the exotic 8-sphere, and carries `sec > 0` by **`theoremB`** (resp.
  **`theoremA`**) together with RW;
- `SEC` is invariant under orientation reversal, `x ↦ −x`.

The group theory is A9.
-/

namespace ExoticSpheres8And10

/-- **[D] Corollary C, dimension 10.** -/
theorem corollaryC_dim10 {Θ : Type*} [AddCommGroup Θ] (eΘ : Θ ≃+ ZMod 6) (α : Θ →+ ZMod 2)
    (hα : α ≠ 0) (PSC SEC : Θ → Prop) (hsec : ∀ x, SEC x → PSC x)
    (hpsc : ∀ x, PSC x → α x = 0) (h0 : SEC 0) (g : Θ) (hg : eΘ g ∈ zmod6Order3)
    (hg0 : g ≠ 0) (hSg : SEC g) (hneg : ∀ x, SEC x → SEC (-x)) :
    ∀ x, SEC x ↔ PSC x := by
  intro x
  refine ⟨hsec x, fun hx => ?_⟩
  set f : ZMod 6 →+ ZMod 2 := α.comp eΘ.symm.toAddMonoidHom
  have hf : f ≠ 0 := by
    intro h; apply hα
    ext y
    have := DFunLike.congr_fun h (eΘ y)
    simpa [f] using this
  have hker := ker_eq_order3 f hf
  have hxk : eΘ x ∈ zmod6Order3 := by
    rw [← hker, AddMonoidHom.mem_ker]
    simp [f, hpsc x hx]
  rw [mem_zmod6Order3_iff] at hg hxk
  have hge : eΘ g ≠ 0 := fun h => hg0 (eΘ.injective (h.trans (map_zero eΘ).symm))
  have key : ∀ a b : ZMod 6, a ∈ ({0, 2, 4} : Finset (ZMod 6)) → a ≠ 0 →
      b ∈ ({0, 2, 4} : Finset (ZMod 6)) → b = 0 ∨ b = a ∨ b = -a := by decide
  rcases key _ _ hg hge hxk with h | h | h
  · rw [show x = 0 from eΘ.injective (h.trans (map_zero eΘ).symm)]; exact h0
  · rw [show x = g from eΘ.injective h]; exact hSg
  · rw [show x = -g from eΘ.injective (h.trans (map_neg eΘ g).symm)]; exact hneg g hSg

/-- **[D] Corollary C, dimension 8.** -/
theorem corollaryC_dim8 {Θ : Type*} [AddCommGroup Θ] (eΘ : Θ ≃+ ZMod 2) (SEC : Θ → Prop)
    (h0 : SEC 0) (g : Θ) (hg0 : g ≠ 0) (hSg : SEC g) : ∀ x, SEC x := by
  intro x
  have hge : eΘ g ≠ 0 := fun h => hg0 (eΘ.injective (h.trans (map_zero eΘ).symm))
  have key : ∀ a b : ZMod 2, a ≠ 0 → b = 0 ∨ b = a := by decide
  rcases key _ (eΘ x) hge with h | h
  · rw [show x = 0 from eΘ.injective (h.trans (map_zero eΘ).symm)]; exact h0
  · rw [show x = g from eΘ.injective h]; exact hSg

/-- **Non-vacuity** of `corollaryC_dim10`: `Θ = ℤ/6`, `α` the reduction, `PSC = SEC =
"in the order-3 subgroup"`, `g = 2`. -/
theorem corollaryC_dim10_satisfiable :
    ∃ (α : ZMod 6 →+ ZMod 2) (PSC SEC : ZMod 6 → Prop), α ≠ 0 ∧ (∀ x, SEC x → PSC x) ∧
      (∀ x, PSC x → α x = 0) ∧ SEC 0 ∧ (2 : ZMod 6) ∈ zmod6Order3 ∧ (2 : ZMod 6) ≠ 0 ∧
      SEC 2 ∧ ∀ x, SEC x → SEC (-x) := by
  refine ⟨(ZMod.castHom (by norm_num : 2 ∣ 6) (ZMod 2)).toAddMonoidHom,
    fun x => x ∈ zmod6Order3, fun x => x ∈ zmod6Order3, castHom_ne_zero, fun _ h => h,
    fun x hx => ?_, zmod6Order3.zero_mem, ?_, by decide, ?_, fun x hx => zmod6Order3.neg_mem hx⟩
  · have hx' : x ∈ zmod6Order3 := hx
    rw [mem_zmod6Order3_iff] at hx'
    have key : ∀ y : ZMod 6, y ∈ ({0, 2, 4} : Finset (ZMod 6)) →
        (ZMod.castHom (by norm_num : 2 ∣ 6) (ZMod 2)) y = 0 := by decide
    exact key x hx'
  · rw [mem_zmod6Order3_iff]; decide
  · show (2 : ZMod 6) ∈ zmod6Order3
    rw [mem_zmod6Order3_iff]; decide

end ExoticSpheres8And10
