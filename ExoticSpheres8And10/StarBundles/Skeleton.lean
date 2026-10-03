/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import Mathlib

/-! # The logical skeleton of [D] `prop:polar`

* **B1** (Step 2, group theory). A group `H` acts on the right on `P`, freely on the orbit of a
  point `p₀` (the fibre `P₀ = p₀ · H`); a group `S` acts on the left, commuting with it, and
  preserves `P₀`. Then `q ⋆ p₀ = p₀ · φ(q)` defines a homomorphism `φ : S →* H`, injective when
  `⋆` is free at `p₀`; and if `φ q = c q c⁻¹` then `s₀ = p₀ · c` satisfies `q ⋆ s₀ = s₀ · q`.
  "Every injective continuous endomorphism of `S³` is inner" is a **hypothesis**
  (`InjContEndoInner`), and so is the continuity of `φ`.
* **B2** (Steps 4 ⇒ 6). From `s_N(ρ q ζ) = (q ⋆ s_N ζ) · q⁻¹`, the same for `s_S`, and
  `s_N = s_S · θ`: `θ(ρ q ζ) = q θ(ζ) q⁻¹`.
* **B3** (Step 6). An interface `HorizontalLifts`; two lifts of one curve differ by a constant
  right translation; hence `θ` is constant along each meridian. Vacuity check: the trivial
  bundle with constant lifts.

The right action of `H` is a left action of `Hᵐᵒᵖ`; `ract p h := op h • p` is `p · h`.
-/

namespace ExoticSpheres8And10

open MulOpposite

section RightAction

variable {H P : Type*} [Group H] [MulAction Hᵐᵒᵖ P]

/-- The right action `p · h`. -/
def ract (p : P) (h : H) : P := op h • p

@[simp] theorem ract_one (p : P) : ract p (1 : H) = p := by simp [ract]

theorem ract_ract (p : P) (h₁ h₂ : H) : ract (ract p h₁) h₂ = ract p (h₁ * h₂) := by
  simp [ract, smul_smul]

theorem smul_ract {S : Type*} [Group S] [MulAction S P] [SMulCommClass S Hᵐᵒᵖ P]
    (q : S) (p : P) (h : H) : q • ract p h = ract (q • p) h := by
  simp only [ract]
  exact smul_comm q (op h) p

end RightAction

/-! ## B1 -/

section B1

variable {S H P : Type*} [Group S] [Group H] [MulAction S P] [MulAction Hᵐᵒᵖ P]
  [SMulCommClass S Hᵐᵒᵖ P]
  (p₀ : P) (hfib : ∀ q : S, ∃ h : H, q • p₀ = ract p₀ h)
  (hfree : ∀ h h' : H, ract p₀ h = ract p₀ h' → h = h')

/-- `φ(q)`: the unique `h` with `q ⋆ p₀ = p₀ · h`. -/
noncomputable def phiFun (q : S) : H := (hfib q).choose

omit [SMulCommClass S Hᵐᵒᵖ P] in
theorem phiFun_spec (q : S) : q • p₀ = ract p₀ (phiFun p₀ hfib q) := (hfib q).choose_spec

/-- **B1(i).** `φ` is a homomorphism: `(q₁q₂) ⋆ p₀ = p₀ · φ(q₁)φ(q₂)`. -/
noncomputable def phiHom : S →* H where
  toFun := phiFun p₀ hfib
  map_one' := hfree _ _ (by rw [← phiFun_spec, one_smul, ract_one])
  map_mul' q₁ q₂ := hfree _ _ (by
    rw [← phiFun_spec, mul_smul, phiFun_spec p₀ hfib q₂, smul_ract, phiFun_spec p₀ hfib q₁,
      ract_ract])

theorem phiHom_spec (q : S) : q • p₀ = ract p₀ (phiHom p₀ hfib hfree q) :=
  phiFun_spec p₀ hfib q

/-- **B1(ii).** `φ` is injective when `⋆` is free at `p₀`. -/
theorem phiHom_injective (hfreeS : ∀ q : S, q • p₀ = p₀ → q = 1) :
    Function.Injective (phiHom p₀ hfib hfree) :=
  (injective_iff_map_eq_one _).2 fun q hq =>
    hfreeS q (by rw [phiHom_spec p₀ hfib hfree, hq, ract_one])

end B1

section B1model

variable {G P : Type*} [Group G] [MulAction G P] [MulAction Gᵐᵒᵖ P] [SMulCommClass G Gᵐᵒᵖ P]

/-- **B1(iii).** If `φ(q) = c q c⁻¹` for all `q`, then `s₀ = p₀ · c` satisfies
`q ⋆ s₀ = s₀ · q` ([D] `eq:model`). -/
theorem model_point (p₀ : P) (φ : G → G) (hφ : ∀ q : G, q • p₀ = ract p₀ (φ q)) (c : G)
    (hc : ∀ q, φ q = c * q * c⁻¹) (q : G) :
    q • ract p₀ c = ract (ract p₀ c) q := by
  rw [smul_ract, hφ, ract_ract, ract_ract, hc]
  congr 1
  group

/-- The imported fact of Step 2, as a named hypothesis (Mathlib lacks it for `S³`):
every injective continuous endomorphism is inner. -/
def InjContEndoInner (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∀ f : G →* G, Function.Injective f → Continuous f → ∃ c : G, ∀ q, f q = c * q * c⁻¹

/-- **B1, assembled.** Under `InjContEndoInner` and continuity of `φ`, there is a model point
`s₀ ∈ p₀ · G` with `q ⋆ s₀ = s₀ · q` for all `q`. -/
theorem exists_model_point [TopologicalSpace G] (hinner : InjContEndoInner G) (p₀ : P)
    (hfib : ∀ q : G, ∃ h : G, q • p₀ = ract p₀ h)
    (hfree : ∀ h h' : G, ract p₀ h = ract p₀ h' → h = h')
    (hfreeS : ∀ q : G, q • p₀ = p₀ → q = 1)
    (hcont : Continuous (phiHom p₀ hfib hfree)) :
    ∃ c : G, ∀ q : G, q • ract p₀ c = ract (ract p₀ c) q := by
  obtain ⟨c, hc⟩ := hinner _ (phiHom_injective p₀ hfib hfree hfreeS) hcont
  exact ⟨c, model_point p₀ _ (phiHom_spec p₀ hfib hfree) c hc⟩

end B1model

/-! ### B1 non-vacuity

`P = G` with `⋆` = left and `·` = right multiplication, `p₀ = 1`: all hypotheses of B1 hold
(`φ = id`). `InjContEndoInner` holds for the discrete group `Multiplicative (ZMod 2)`, whose
only injective endomorphism is the identity `= conjugation by 1`; so `exists_model_point`
fires there. (For `G = S³` the hypothesis is a true theorem not available in Mathlib.) -/

section B1vacuity

theorem left_right_hyps (G : Type*) [Group G] :
    (∀ q : G, ∃ h : G, q • (1 : G) = ract (1 : G) h) ∧
    (∀ h h' : G, ract (1 : G) h = ract (1 : G) h' → h = h') ∧
    (∀ q : G, q • (1 : G) = 1 → q = 1) := by
  refine ⟨fun q => ⟨q, by simp [ract]⟩, fun h h' e => by simpa [ract] using e,
    fun q e => by simpa using e⟩

abbrev Z2 := Multiplicative (ZMod 2)

instance : TopologicalSpace Z2 := ⊥
instance : DiscreteTopology Z2 := ⟨rfl⟩

theorem injContEndoInner_Z2 : InjContEndoInner Z2 := by
  intro f hf _
  refine ⟨1, fun q => ?_⟩
  have h2 : ∀ x : Z2, x = 1 ∨ x = Multiplicative.ofAdd 1 := by decide
  rcases h2 q with rfl | rfl
  · simp
  · have hne : f (Multiplicative.ofAdd 1) ≠ 1 := by
      intro h
      have := hf (h.trans (map_one f).symm)
      exact absurd this (by decide)
    rcases h2 (f (Multiplicative.ofAdd 1)) with h | h
    · exact absurd h hne
    · simpa using h

example : ∃ c : Z2, ∀ q : Z2, q • ract (1 : Z2) c = ract (ract (1 : Z2) c) q :=
  exists_model_point injContEndoInner_Z2 (1 : Z2) (left_right_hyps Z2).1 (left_right_hyps Z2).2.1
    (left_right_hyps Z2).2.2 continuous_of_discreteTopology

end B1vacuity

/-! ## B2 -/

section B2

variable {G P Z : Type*} [Group G] [MulAction G P] [MulAction Gᵐᵒᵖ P] [SMulCommClass G Gᵐᵒᵖ P]
  [MulAction G Z]

/-- **B2.** Equivariance of `θ` from equivariance of the two sections ([D] Step 6, last display).
`hfree`: the principal right action is free. -/
theorem theta_equivariant (sN sS : Z → P) (θ : Z → G)
    (hN : ∀ (q : G) ζ, sN (q • ζ) = ract (q • sN ζ) q⁻¹)
    (hS : ∀ (q : G) ζ, sS (q • ζ) = ract (q • sS ζ) q⁻¹)
    (hθ : ∀ ζ, sN ζ = ract (sS ζ) (θ ζ))
    (hfree : ∀ (p : P) (g g' : G), ract p g = ract p g' → g = g') (q : G) (ζ : Z) :
    θ (q • ζ) = q * θ ζ * q⁻¹ := by
  have hS' : q • sS ζ = ract (sS (q • ζ)) q := by
    rw [hS, ract_ract, inv_mul_cancel, ract_one]
  apply hfree (sS (q • ζ))
  rw [← hθ, hN, hθ, smul_ract, hS', ract_ract, ract_ract, mul_assoc]

/-- B2 non-vacuity: `Z = Unit`, `P = G`, `s_N = s_S = 1`, `θ = 1`. -/
example (G : Type*) [Group G] (q : G) :
    (fun _ : Unit => (1 : G)) (q • ()) = q * (fun _ : Unit => (1 : G)) () * q⁻¹ :=
  theta_equivariant (P := G) (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (fun q _ => by simp [ract]) (fun q _ => by simp [ract]) (fun _ => by simp [ract])
    (fun p g g' e => by simpa [ract] using e) q ()

end B2

/-! ## B3 -/

section B3

/-- **B3 interface.** Horizontal lifts of the curves `c : ℝ → B` of a family `Curves`, on a
parameter set `I ∋ t₀`, in a bundle `π : P → B` with right action `ract`. Its fields are
hypotheses of every theorem that uses it (a structure argument), not axioms. -/
structure HorizontalLifts (G P B : Type*) (π : P → B) (ract : P → G → P)
    (Curves : Set (ℝ → B)) (I : Set ℝ) where
  /-- `IsLift c ℓ`: `ℓ` is a horizontal lift of `c` on `I`. -/
  IsLift : (ℝ → B) → (ℝ → P) → Prop
  proj : ∀ c ∈ Curves, ∀ ℓ, IsLift c ℓ → ∀ t ∈ I, π (ℓ t) = c t
  exists_lift : ∀ c ∈ Curves, ∀ t₀ ∈ I, ∀ p, π p = c t₀ → ∃ ℓ, IsLift c ℓ ∧ ℓ t₀ = p
  unique : ∀ c ∈ Curves, ∀ ℓ ℓ', IsLift c ℓ → IsLift c ℓ' →
    ∀ t₀ ∈ I, ℓ t₀ = ℓ' t₀ → ∀ t ∈ I, ℓ t = ℓ' t
  ract_lift : ∀ c ∈ Curves, ∀ ℓ, IsLift c ℓ → ∀ g, IsLift c (fun t => ract (ℓ t) g)

variable {G P B : Type*} {π : P → B} {ract' : P → G → P} {Curves : Set (ℝ → B)} {I : Set ℝ}

/-- **B3(i).** Two horizontal lifts of one curve differ by a *constant* right translation. -/
theorem lifts_differ_by_constant (L : HorizontalLifts G P B π ract' Curves I)
    {c : ℝ → B} (hc : c ∈ Curves) {ℓ₁ ℓ₂ : ℝ → P} (h₁ : L.IsLift c ℓ₁) (h₂ : L.IsLift c ℓ₂)
    {t₀ : ℝ} (ht₀ : t₀ ∈ I) (g : G) (hg : ℓ₁ t₀ = ract' (ℓ₂ t₀) g) :
    ∀ t ∈ I, ℓ₁ t = ract' (ℓ₂ t) g :=
  L.unique c hc ℓ₁ _ h₁ (L.ract_lift c hc ℓ₂ h₂ g) t₀ ht₀ hg

/-- **B3(ii).** Hence `θ`, defined by `s_N = s_S · θ` with a free right action, is constant
along each curve whose `s_N`- and `s_S`-images are horizontal lifts ([D] Step 6). -/
theorem theta_const_along (L : HorizontalLifts G P B π ract' Curves I)
    (hfree : ∀ (p : P) (g g' : G), ract' p g = ract' p g' → g = g')
    (sN sS : B → P) (θ : B → G) (hθ : ∀ ζ, sN ζ = ract' (sS ζ) (θ ζ))
    {c : ℝ → B} (hc : c ∈ Curves) (hN : L.IsLift c (sN ∘ c)) (hS : L.IsLift c (sS ∘ c))
    {t₀ : ℝ} (ht₀ : t₀ ∈ I) : ∀ t ∈ I, θ (c t) = θ (c t₀) := by
  intro t ht
  have h := lifts_differ_by_constant L hc hN hS ht₀ (θ (c t₀)) (hθ (c t₀)) t ht
  exact hfree (sS (c t)) _ _ ((hθ (c t)).symm.trans h)

/-! ### B3 non-vacuity: the trivial bundle `B × G` with constant (flat) lifts -/

/-- The trivial-bundle model: lifts are `t ↦ (c t, u)` for a constant `u`. -/
def trivialLifts (G B : Type*) [Group G] (Curves : Set (ℝ → B)) (I : Set ℝ) :
    HorizontalLifts G (B × G) B Prod.fst (fun p g => (p.1, p.2 * g)) Curves I where
  IsLift c ℓ := ∃ u : G, ∀ t ∈ I, ℓ t = (c t, u)
  proj c _ ℓ h t ht := by obtain ⟨u, hu⟩ := h; rw [hu t ht]
  exists_lift c _ t₀ _ p hp := ⟨fun t => (c t, p.2), ⟨p.2, fun _ _ => rfl⟩,
    Prod.ext hp.symm rfl⟩
  unique c _ ℓ ℓ' h h' t₀ ht₀ e t ht := by
    obtain ⟨u, hu⟩ := h
    obtain ⟨u', hu'⟩ := h'
    rw [hu t₀ ht₀, hu' t₀ ht₀] at e
    have huu : u = u' := congrArg Prod.snd e
    rw [hu t ht, hu' t ht, huu]
  ract_lift c _ ℓ h g := by
    obtain ⟨u, hu⟩ := h
    exact ⟨u * g, fun t ht => by show ((ℓ t).1, (ℓ t).2 * g) = (c t, u * g); rw [hu t ht]⟩

/-- `theta_const_along` fires in the model: with `s_S ζ = (ζ, 1)` and `s_N ζ = (ζ, g)` both
constant-lift sections, `θ ≡ g` is constant along every curve. -/
example (G B : Type*) [Group G] (g : G) (c : ℝ → B) (t : ℝ) :
    (fun _ : B => g) (c t) = (fun _ : B => g) (c 0) :=
  theta_const_along (trivialLifts G B {c} Set.univ)
    (fun p g g' e => mul_left_cancel (Prod.ext_iff.1 e).2)
    (fun ζ => (ζ, g)) (fun ζ => (ζ, 1)) (fun _ => g) (fun ζ => by simp)
    rfl ⟨g, fun _ _ => rfl⟩ ⟨1, fun _ _ => rfl⟩ (Set.mem_univ 0) t (Set.mem_univ t)

end B3

end ExoticSpheres8And10
