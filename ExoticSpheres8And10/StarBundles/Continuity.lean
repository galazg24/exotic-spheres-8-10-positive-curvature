/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.StarBundles.InnerEndomorphisms

/-! # B1, completed: continuity of `φ`

[D] Step 2: "there is a unique map `φ : S³ → S³` with `q ⋆ p₀ = p₀ φ(q)`. It is a smooth
homomorphism". The continuity needed by `exists_model_point_S3` follows from continuity of the
two actions alone: the orbit map `h ↦ p₀ · h` is a continuous injection of the compact group `S³`
into a Hausdorff space, hence a closed embedding, and `(p₀ · −) ∘ φ = (− ⋆ p₀)` is continuous.
-/

namespace ExoticSpheres8And10

open Metric Quaternion

/-- **`φ` is continuous** when both actions are continuous in the group variable, the right
action is free on the orbit of `p₀`, the group is compact and `P` is Hausdorff. -/
theorem phiHom_continuous {S H P : Type*} [Group S] [Group H] [MulAction S P]
    [MulAction Hᵐᵒᵖ P] [SMulCommClass S Hᵐᵒᵖ P] [TopologicalSpace S] [TopologicalSpace H]
    [CompactSpace H] [TopologicalSpace P] [T2Space P] (p₀ : P)
    (hfib : ∀ q : S, ∃ h : H, q • p₀ = ract p₀ h)
    (hfree : ∀ h h' : H, ract p₀ h = ract p₀ h' → h = h')
    (hcl : Continuous fun q : S => q • p₀) (hcr : Continuous fun h : H => ract p₀ h) :
    Continuous (phiHom p₀ hfib hfree) := by
  have hemb := hcr.isClosedEmbedding (fun h h' e => hfree h h' e)
  rw [hemb.isEmbedding.continuous_iff]
  have : ((fun h : H => ract p₀ h) ∘ phiHom p₀ hfib hfree) = fun q : S => q • p₀ := by
    funext q; exact (phiHom_spec p₀ hfib hfree q).symm
  rw [this]; exact hcl

local notation "S3" => sphere (0 : ℍ[ℝ]) 1

set_option synthInstance.maxHeartbeats 200000 in
/-- **B1 for `S³`, with no imported hypothesis.** [D] `prop:polar` Step 2 (`eq:model`): for a
right action of `S³` on a Hausdorff space `P`, free on the orbit of `p₀`, and a commuting left
action preserving that orbit and free at `p₀`, both continuous in the group variable, there is a
model point `s₀ = p₀ · c` with `q ⋆ s₀ = s₀ · q`. -/
theorem exists_model_point_S3_top {P : Type*} [MulAction S3 P] [MulAction S3ᵐᵒᵖ P]
    [SMulCommClass S3 S3ᵐᵒᵖ P] [TopologicalSpace P] [T2Space P] (p₀ : P)
    (hfib : ∀ q : S3, ∃ h : S3, q • p₀ = ract p₀ h)
    (hfree : ∀ h h' : S3, ract p₀ h = ract p₀ h' → h = h')
    (hfreeS : ∀ q : S3, q • p₀ = p₀ → q = 1)
    (hcl : Continuous fun q : S3 => q • p₀) (hcr : Continuous fun h : S3 => ract p₀ h) :
    ∃ c : S3, ∀ q : S3, q • ract p₀ c = ract (ract p₀ c) q :=
  exists_model_point_S3 p₀ hfib hfree hfreeS (phiHom_continuous p₀ hfib hfree hcl hcr)

set_option synthInstance.maxHeartbeats 200000 in
/-- Non-vacuity: `P = S³` with left and right multiplication, `p₀ = 1`. -/
example : ∃ c : S3, ∀ q : S3, q • ract (1 : S3) c = ract (ract (1 : S3) c) q :=
  exists_model_point_S3_top (1 : S3) (left_right_hyps S3).1 (left_right_hyps S3).2.1
    (left_right_hyps S3).2.2 (by simpa using continuous_id')
    (by simpa [ract] using continuous_id')

end ExoticSpheres8And10
