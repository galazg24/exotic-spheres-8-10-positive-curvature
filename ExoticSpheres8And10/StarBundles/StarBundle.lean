/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.PolarBundles.Summary

/-! # §3: general star bundles

[GG] §2 `def:starbundle` / §3 `prop:polar`: a *star bundle* is a smooth principal right
`S³`-bundle `π : E → S^n = S(W)` with a smooth free left `S³`-action `⋆` commuting with the
principal action and covering `ρ`.

`StarRep e` is the representation data (`ρ` orthogonal, fixing `e`, smooth); `StarBundle R E`
is a star bundle structure on a smooth manifold `E` (model `ℝⁿ × ℝ³`), with local
trivialisations given by local sections `sec ζ₀` over open sets `nbhd ζ₀ ∋ ζ₀` and fibre
coordinates `fib ζ₀` (so `(z, u) ↦ sec ζ₀ z · u` is a diffeomorphism onto `π⁻¹(nbhd ζ₀)`).

* `ract_free`, `exists_ract`: the principal action is free and transitive on fibres;
* `divE`: the division map (`p' = p · divE p p'`), smooth on pairs of smooth maps with the same
  projection (`contMDiff_divE`).
-/

namespace ExoticSpheres8And10

open Set Metric Function Module Real

open scoped Manifold ContDiff RealInnerProductSpace

open Quaternion

noncomputable section

local notation "S3" => sphere (0 : ℍ[ℝ]) 1

section Defs

variable {m : ℕ} {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)]

local notation "Sn" => sphere (0 : W) 1

/-- Representation data of a star bundle ([GG] `def:starbundle` (1)–(2)). -/
structure StarRep (e : W) where
  e_norm : ‖e‖ = 1
  ρ : S3 →* (W ≃ₗᵢ[ℝ] W)
  ρ_e : ∀ q, ρ q e = e
  ρ_smooth : ContMDiff (𝓡 3) 𝓘(ℝ, W →L[ℝ] W) ∞ fun q => ((ρ q : W ≃L[ℝ] W) : W →L[ℝ] W)

variable {e : W}

/-- `ρ(q)` on the sphere. -/
def StarRep.ρS (R : StarRep e) (q : S3) (ζ : Sn) : Sn :=
  ⟨R.ρ q ζ, by
    rw [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map]
    exact mem_sphere_zero_iff_norm.1 ζ.2⟩

/-- **A star bundle** ([GG] `def:starbundle` (3)) on a smooth manifold `E`. -/
structure StarBundle (R : StarRep e) (E : Type*) [TopologicalSpace E]
    [ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin (m + 1))) (EuclideanSpace ℝ (Fin 3))) E] where
  proj : E → Sn
  ract : E → S3 → E
  star : S3 → E → E
  proj_smooth : ContMDiff (IP m) (𝓡 (m + 1)) ∞ proj
  ract_smooth : ContMDiff ((IP m).prod (𝓡 3)) (IP m) ∞ fun x : E × S3 => ract x.1 x.2
  star_smooth : ContMDiff ((𝓡 3).prod (IP m)) (IP m) ∞ fun x : S3 × E => star x.1 x.2
  ract_one : ∀ p, ract p 1 = p
  ract_mul : ∀ p h h', ract (ract p h) h' = ract p (h * h')
  star_one : ∀ p, star 1 p = p
  star_mul : ∀ q q' p, star (q * q') p = star q (star q' p)
  proj_ract : ∀ p h, proj (ract p h) = proj p
  star_ract : ∀ q p h, star q (ract p h) = ract (star q p) h
  proj_star : ∀ q p, proj (star q p) = R.ρS q (proj p)
  star_free : ∀ q p, star q p = p → q = 1
  /-- trivialising neighbourhoods -/
  nbhd : Sn → Set Sn
  nbhd_open : ∀ ζ₀, IsOpen (nbhd ζ₀)
  mem_nbhd : ∀ ζ₀, ζ₀ ∈ nbhd ζ₀
  /-- local sections -/
  sec : Sn → Sn → E
  sec_smooth : ∀ ζ₀, ContMDiffOn (𝓡 (m + 1)) (IP m) ∞ (sec ζ₀) (nbhd ζ₀)
  proj_sec : ∀ ζ₀, ∀ z ∈ nbhd ζ₀, proj (sec ζ₀ z) = z
  /-- fibre coordinates -/
  fib : Sn → E → S3
  fib_smooth : ∀ ζ₀, ContMDiffOn (IP m) (𝓡 3) ∞ (fib ζ₀) (proj ⁻¹' nbhd ζ₀)
  sec_fib : ∀ ζ₀ p, proj p ∈ nbhd ζ₀ → ract (sec ζ₀ (proj p)) (fib ζ₀ p) = p
  fib_sec : ∀ ζ₀, ∀ z ∈ nbhd ζ₀, ∀ u, fib ζ₀ (ract (sec ζ₀ z) u) = u

end Defs

namespace StarBundle

variable {m : ℕ} {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] {e : W} {R : StarRep e} {E : Type*} [TopologicalSpace E]
  [ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin (m + 1))) (EuclideanSpace ℝ (Fin 3))) E]
  [IsManifold (IP m) ∞ E] (B : StarBundle (m := m) R E)

local notation "Sn" => sphere (0 : W) 1

theorem fib_ract (ζ₀ : Sn) (p : E) (hp : B.proj p ∈ B.nbhd ζ₀) (h : S3) :
    B.fib ζ₀ (B.ract p h) = B.fib ζ₀ p * h := by
  conv_lhs => rw [← B.sec_fib ζ₀ p hp, B.ract_mul]
  exact B.fib_sec ζ₀ _ hp _

/-- **The principal action is free.** -/
theorem ract_free (p : E) (h : S3) (hh : B.ract p h = p) : h = 1 := by
  have h1 := B.fib_ract (B.proj p) p (B.mem_nbhd _) h
  rw [hh] at h1
  exact (mul_eq_left.1 h1.symm)

/-- The division map: `divE p p' = fib(p)⁻¹ fib(p')` in the trivialisation at `π(p)`. -/
def divE (p p' : E) : S3 := (B.fib (B.proj p) p)⁻¹ * B.fib (B.proj p) p'

/-- **The principal action is transitive on fibres**: `p' = p · divE p p'`. -/
theorem ract_divE (p p' : E) (h : B.proj p' = B.proj p) : B.ract p (B.divE p p') = p' := by
  have hp := B.mem_nbhd (B.proj p)
  have hp' : B.proj p' ∈ B.nbhd (B.proj p) := h ▸ hp
  have e1 : B.ract (B.sec (B.proj p) (B.proj p)) (B.fib (B.proj p) p) = p := B.sec_fib _ p hp
  have e2 : B.ract (B.sec (B.proj p) (B.proj p)) (B.fib (B.proj p) p') = p' := by
    have := B.sec_fib (B.proj p) p' hp'; rwa [h] at this
  calc B.ract p (B.divE p p')
      = B.ract (B.ract (B.sec (B.proj p) (B.proj p)) (B.fib (B.proj p) p)) (B.divE p p') := by
        rw [e1]
    _ = p' := by rw [B.ract_mul, divE, mul_inv_cancel_left, e2]

theorem divE_unique (p p' : E) (h : S3) (hh : B.ract p h = p') : B.divE p p' = h := by
  have hp := B.mem_nbhd (B.proj p)
  rw [divE, ← hh, B.fib_ract _ p hp, inv_mul_cancel_left]

/-- `divE` computed in any trivialisation containing the base point. -/
theorem divE_eq (ζ₀ : Sn) (p p' : E) (hp : B.proj p ∈ B.nbhd ζ₀) (h : B.proj p' = B.proj p) :
    B.divE p p' = (B.fib ζ₀ p)⁻¹ * B.fib ζ₀ p' := by
  apply B.divE_unique
  have hp' : B.proj p' ∈ B.nbhd ζ₀ := h ▸ hp
  have e1 : B.ract (B.sec ζ₀ (B.proj p)) (B.fib ζ₀ p) = p := B.sec_fib _ p hp
  have e2 : B.ract (B.sec ζ₀ (B.proj p)) (B.fib ζ₀ p') = p' := by
    have := B.sec_fib ζ₀ p' hp'; rwa [h] at this
  calc B.ract p ((B.fib ζ₀ p)⁻¹ * B.fib ζ₀ p')
      = B.ract (B.ract (B.sec ζ₀ (B.proj p)) (B.fib ζ₀ p)) ((B.fib ζ₀ p)⁻¹ * B.fib ζ₀ p') := by
        rw [e1]
    _ = p' := by rw [B.ract_mul, mul_inv_cancel_left, e2]

end StarBundle

theorem contMDiff_invMulS3 : ContMDiff ((𝓡 3).prod (𝓡 3)) (𝓡 3) ∞ fun p : S3 × S3 => p.1⁻¹ * p.2 := by
  have hc : ContMDiff ((𝓡 3).prod (𝓡 3)) 𝓘(ℝ, ℍ[ℝ] × ℍ[ℝ]) ∞
      fun p : S3 × S3 => (((p.1⁻¹ : S3) : ℍ[ℝ]), ((p.2 : S3) : ℍ[ℝ])) :=
    (contMDiff_coe_sphere.comp (contMDiff_invS3.comp contMDiff_fst)).prodMk_space
      (contMDiff_coe_sphere.comp contMDiff_snd)
  exact contMDiff_sphere_of_coe ((contDiff_mul (𝕜 := ℝ) (𝔸 := ℍ[ℝ])).comp_contMDiff hc)

theorem contMDiff_mulS3 : ContMDiff ((𝓡 3).prod (𝓡 3)) (𝓡 3) ∞ fun p : S3 × S3 => p.1 * p.2 := by
  have hc : ContMDiff ((𝓡 3).prod (𝓡 3)) 𝓘(ℝ, ℍ[ℝ] × ℍ[ℝ]) ∞
      fun p : S3 × S3 => (((p.1 : S3) : ℍ[ℝ]), ((p.2 : S3) : ℍ[ℝ])) :=
    (contMDiff_coe_sphere.comp contMDiff_fst).prodMk_space
      (contMDiff_coe_sphere.comp contMDiff_snd)
  exact contMDiff_sphere_of_coe ((contDiff_mul (𝕜 := ℝ) (𝔸 := ℍ[ℝ])).comp_contMDiff hc)

theorem ContMDiffOn.invMulS3 {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N]
    [ChartedSpace H' N] {a b : N → S3} {s : Set N} (ha : ContMDiffOn I' (𝓡 3) ∞ a s)
    (hb : ContMDiffOn I' (𝓡 3) ∞ b s) : ContMDiffOn I' (𝓡 3) ∞ (fun y => (a y)⁻¹ * b y) s := by
  have hab : ContMDiffOn I' ((𝓡 3).prod (𝓡 3)) ∞ (fun y => (a y, b y)) s := ha.prodMk hb
  have := ContMDiff.comp_contMDiffOn (g := fun p : S3 × S3 => p.1⁻¹ * p.2)
    (f := fun y => (a y, b y)) contMDiff_invMulS3 hab
  exact this

namespace StarBundle

variable {m : ℕ} {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] {e : W} {R : StarRep e} {E : Type*} [TopologicalSpace E]
  [ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin (m + 1))) (EuclideanSpace ℝ (Fin 3))) E]
  [IsManifold (IP m) ∞ E] (B : StarBundle (m := m) R E)

local notation "Sn" => sphere (0 : W) 1

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I' ∞ N]

/-- **The division map is smooth** on pairs of smooth maps with the same projection. -/
theorem contMDiffOn_divE {f f' : N → E} {s : Set N} (hs : IsOpen s)
    (hf : ContMDiffOn I' (IP m) ∞ f s) (hf' : ContMDiffOn I' (IP m) ∞ f' s)
    (h : ∀ x ∈ s, B.proj (f' x) = B.proj (f x)) :
    ContMDiffOn I' (𝓡 3) ∞ (fun x => B.divE (f x) (f' x)) s := by
  intro x hx
  obtain ⟨ζ₀, hζ₀⟩ : ∃ ζ₀, B.proj (f x) = ζ₀ := ⟨_, rfl⟩
  -- the set where both points lie over `nbhd ζ₀`
  have hU : IsOpen (s ∩ f ⁻¹' (B.proj ⁻¹' B.nbhd ζ₀)) :=
    (hf.continuousOn.isOpen_inter_preimage hs ((B.nbhd_open ζ₀).preimage
      B.proj_smooth.continuous))
  have hxU : x ∈ s ∩ f ⁻¹' (B.proj ⁻¹' B.nbhd ζ₀) := ⟨hx, by
    show B.proj (f x) ∈ B.nbhd ζ₀
    rw [hζ₀]; exact B.mem_nbhd ζ₀⟩
  have h1 : ContMDiffOn I' (𝓡 3) ∞ (fun y => B.fib ζ₀ (f y)) (s ∩ f ⁻¹' (B.proj ⁻¹' B.nbhd ζ₀)) :=
    (B.fib_smooth ζ₀).comp (hf.mono inter_subset_left) fun y hy => hy.2
  have h2 : ContMDiffOn I' (𝓡 3) ∞ (fun y => B.fib ζ₀ (f' y))
      (s ∩ f ⁻¹' (B.proj ⁻¹' B.nbhd ζ₀)) :=
    (B.fib_smooth ζ₀).comp (hf'.mono inter_subset_left) fun y hy => by
      show B.proj (f' y) ∈ B.nbhd ζ₀
      rw [h y hy.1]; exact hy.2
  have h3 : ContMDiffOn I' (𝓡 3) ∞ (fun y => (B.fib ζ₀ (f y))⁻¹ * B.fib ζ₀ (f' y))
      (s ∩ f ⁻¹' (B.proj ⁻¹' B.nbhd ζ₀)) :=
    ContMDiffOn.invMulS3 h1 h2
  refine ((h3.contMDiffAt (hU.mem_nhds hxU)).congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [hU.mem_nhds hxU] with y hy
  exact B.divE_eq ζ₀ _ _ hy.2 (h y hy.1)

end StarBundle

end

end ExoticSpheres8And10
