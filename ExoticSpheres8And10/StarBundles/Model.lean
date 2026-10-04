/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.StarBundles.Equivariant
import ExoticSpheres8And10.PolarBundles.Summary

/-! # §3: non-vacuity of `prop_polar`

The hypotheses of `StarBundle.prop_polar` are satisfiable: the trivial bundle
`S^n × S³ → S^n` with trivial `ρ`, principal action `(ζ, u)h = (ζ, uh)` and star action
`q ⋆ (ζ, u) = (ζ, qu)` is a star bundle, in every dimension.
-/

namespace ExoticSpheres8And10

open Set Metric Function Module

open scoped Manifold ContDiff

noncomputable section

local notation "S3" => sphere (0 : Quaternion ℝ) 1

section Model

variable (m : ℕ)

local notation "Sn" => sphere (0 : Wm m) 1

/-- The trivial representation, with pole `e₀`. -/
def trivRep : StarRep (e0 m) where
  e_norm := norm_e0 m
  ρ := 1
  ρ_e _ := rfl
  ρ_smooth := by simp only [MonoidHom.one_apply]; exact contMDiff_const

/-- **The trivial star bundle** `S^n × S³`. -/
def trivBundle : StarBundle (m := m) (trivRep m) (Sn × S3) where
  proj p := p.1
  ract p h := (p.1, p.2 * h)
  star q p := (p.1, q * p.2)
  proj_smooth := contMDiff_fst
  ract_smooth := (contMDiff_fst.comp contMDiff_fst).prodMk
    (ContMDiff.comp (g := fun p : S3 × S3 => p.1 * p.2)
      (f := fun x : (Sn × S3) × S3 => (x.1.2, x.2)) contMDiff_mulS3
      ((contMDiff_snd.comp contMDiff_fst).prodMk contMDiff_snd))
  star_smooth := (contMDiff_fst.comp contMDiff_snd).prodMk
    (ContMDiff.comp (g := fun p : S3 × S3 => p.1 * p.2)
      (f := fun x : S3 × (Sn × S3) => (x.1, x.2.2)) contMDiff_mulS3
      (contMDiff_fst.prodMk (contMDiff_snd.comp contMDiff_snd)))
  ract_one p := by simp
  ract_mul p h h' := by simp [mul_assoc]
  star_one p := by simp
  star_mul q q' p := by simp [mul_assoc]
  proj_ract _ _ := rfl
  star_ract q p h := by simp [mul_assoc]
  proj_star q p := by apply Subtype.ext; simp [StarRep.ρS, trivRep]
  star_free q p h := by
    have h2 := congrArg Prod.snd h
    simpa using h2
  nbhd _ := univ
  nbhd_open _ := isOpen_univ
  mem_nbhd _ := mem_univ _
  sec _ z := (z, 1)
  sec_smooth _ := (contMDiff_id.prodMk contMDiff_const).contMDiffOn
  proj_sec _ _ _ := rfl
  fib _ p := p.2
  fib_smooth _ := contMDiff_snd.contMDiffOn
  sec_fib _ p _ := by simp
  fib_sec _ _ _ u := by simp

/-- **Non-vacuity**: `prop_polar` applies to the trivial star bundle. -/
theorem prop_polar_trivBundle :
    letI := (trivRep m).factVs m
    ∃ D : PolarData (m := m) (e0 m), D.ρ = (trivRep m).ρ ∧
      ∃ Φ : Diffeomorph (IP m) (IP m) (PolarBundle D) (Sn × S3) ∞,
        (∀ x, (trivBundle m).proj (Φ x) = D.proj x) ∧
        (∀ x h, Φ (D.ract x h) = (trivBundle m).ract (Φ x) h) ∧
        (∀ (q : S3) x, Φ (q • x) = (trivBundle m).star q (Φ x)) ∧
        Nonempty (Quotient (EquivSections.starSetoid (trivBundle m)) ≃ₜ D.OrbitSpace) :=
  (trivBundle m).prop_polar

end Model

end

end ExoticSpheres8And10
