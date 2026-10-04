/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import Mathlib

/-! # A9. Group theory in Corollary C and Theorem B

* (a) [GG] proof of Corollary C: "`α : Θ₁₀ → KO₁₀ ≅ ℤ/2` ... is nonzero in dimension ten,
  so its kernel in `ℤ/6` is exactly the subgroup of order three."
* (b) [GG] proof of Theorem B: "This identifies a generator of the order-three subgroup,
  without fixing a preferred sign. Reversing its orientation represents the other generator."
  (In `ℤ/3`, `g` generates iff `−g` does, and `g ≠ −g` for `g ≠ 0`.)
* (c) [GG] Corollary C, dimension 8: `|Θ₈| = 2`, so there is exactly one exotic class.

Only the group theory is formalised: the identifications `Θ₁₀ ≅ ℤ/6`, `Θ₈ ≅ ℤ/2`,
`KO₁₀ ≅ ℤ/2`, and that `α` is a nonzero homomorphism, are imported inputs.
-/

namespace ExoticSpheres8And10

/-- The subgroup `{0, 2, 4}` of `ZMod 6`, i.e. `3 • x = 0`. -/
def zmod6Order3 : AddSubgroup (ZMod 6) := AddSubgroup.zmultiples 2

theorem mem_zmod6Order3_iff (x : ZMod 6) : x ∈ zmod6Order3 ↔ x ∈ ({0, 2, 4} : Finset (ZMod 6)) := by
  rw [zmod6Order3, AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨k, rfl⟩
    have : ∀ k : ZMod 6, k * 2 ∈ ({0, 2, 4} : Finset (ZMod 6)) := by decide
    rw [zsmul_eq_mul]
    exact this (k : ZMod 6)
  · intro hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨0, by decide⟩
    · exact ⟨1, by decide⟩
    · exact ⟨2, by decide⟩

theorem nat_card_zmod6Order3 : Nat.card zmod6Order3 = 3 := by
  have : (zmod6Order3 : Set (ZMod 6)) = ↑({0, 2, 4} : Finset (ZMod 6)) := by
    ext x; exact mem_zmod6Order3_iff x
  rw [← SetLike.coe_sort_coe, this, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  decide

/-- `zmod6Order3` is the unique subgroup of `ZMod 6` of order `3`. -/
theorem eq_zmod6Order3_of_card (H : AddSubgroup (ZMod 6)) (hH : Nat.card H = 3) :
    H = zmod6Order3 := by
  have hle : H ≤ zmod6Order3 := by
    intro h hh
    have h3 : 3 • h = 0 := by
      have := card_nsmul_eq_zero' (G := H) (x := ⟨h, hh⟩)
      rw [hH] at this
      simpa using congrArg Subtype.val this
    rw [mem_zmod6Order3_iff]
    clear hh
    revert h3
    revert h
    decide
  exact AddSubgroup.eq_of_le_of_card_ge hle (by rw [nat_card_zmod6Order3, hH])

/-- **A9(a).** Every nonzero additive homomorphism `ZMod 6 →+ ZMod 2` has kernel equal to
the unique subgroup of order `3`. -/
theorem ker_eq_order3 (f : ZMod 6 →+ ZMod 2) (hf : f ≠ 0) : f.ker = zmod6Order3 := by
  have key : ∀ n : ℕ, f (n : ZMod 6) = n • f 1 := by
    intro n
    rw [← map_nsmul, nsmul_one]
  have h1 : f 1 = 1 := by
    have h10 : f 1 ≠ 0 := by
      intro h0
      apply hf
      ext x
      rw [← ZMod.natCast_zmod_val x, key, h0, smul_zero]
      rfl
    revert h10
    generalize f 1 = z
    revert z
    decide
  ext x
  rw [AddMonoidHom.mem_ker, mem_zmod6Order3_iff, ← ZMod.natCast_zmod_val x, key, h1,
    nsmul_one]
  generalize hv : x.val = v
  have hv6 : v < 6 := hv ▸ ZMod.val_lt x
  interval_cases v <;> decide

theorem nat_card_ker (f : ZMod 6 →+ ZMod 2) (hf : f ≠ 0) : Nat.card f.ker = 3 := by
  rw [ker_eq_order3 f hf, nat_card_zmod6Order3]

/-- Non-vacuity of A9(a): the reduction map `ZMod 6 → ZMod 2` is a nonzero homomorphism. -/
theorem castHom_ne_zero : (ZMod.castHom (by norm_num : 2 ∣ 6) (ZMod 2)).toAddMonoidHom ≠ 0 := by
  intro h
  have := DFunLike.congr_fun h 1
  revert this
  decide

/-- **A9(b).** If `g` generates `ZMod 3`, so does `−g`. -/
theorem neg_generates_zmod3 (g : ZMod 3) (hg : AddSubgroup.zmultiples g = ⊤) :
    AddSubgroup.zmultiples (-g) = ⊤ := by
  rwa [AddSubgroup.zmultiples_neg]

/-- In `ZMod 3` the generators are exactly the nonzero elements, and `−g ≠ g` for them: so
the two generators are `g` and `−g`. -/
theorem zmod3_generators (g : ZMod 3) (hg : g ≠ 0) :
    AddSubgroup.zmultiples g = ⊤ ∧ -g ≠ g ∧ ∀ h : ZMod 3, h ≠ 0 → h = g ∨ h = -g := by
  refine ⟨?_, ?_, ?_⟩
  · rw [eq_top_iff]
    intro x _
    rw [AddSubgroup.mem_zmultiples_iff]
    have : ∀ g x : ZMod 3, g ≠ 0 → x = 0 * g ∨ x = 1 * g ∨ x = 2 * g := by decide
    rcases this g x hg with h | h | h
    · exact ⟨0, by rw [h, zsmul_eq_mul]; push_cast; ring⟩
    · exact ⟨1, by rw [h, zsmul_eq_mul]; push_cast; ring⟩
    · exact ⟨2, by rw [h, zsmul_eq_mul]; push_cast; ring⟩
  · revert hg; revert g; decide
  · revert hg; revert g; decide

/-- **A9(c).** `ZMod 2` has exactly one non-zero element. -/
theorem zmod2_unique_nonzero : ∃! z : ZMod 2, z ≠ 0 :=
  ⟨1, by decide, fun y hy => by revert hy; revert y; decide⟩

end ExoticSpheres8And10
