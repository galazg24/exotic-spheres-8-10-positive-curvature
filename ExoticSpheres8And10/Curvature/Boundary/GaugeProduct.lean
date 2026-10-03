/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Curvature.Boundary.Gauge

/-! # §4.4: near the boundary, the southern quotient metric is the product-connection quotient

Where `χ = 0`: `τ^*g_A = g_0` pointwise (**`gB_τ`**). Here `g_A` is the star quotient of [D]'s
southern metric `G_S = GH(A_S, r)`, and `g_0` that of the product-connection metric
`GW(ψR⟪,⟫, r)`.

The proof is at the slice point, by linear algebra:
- `dΛ` is an isometry of slice forms (`Λ_isometry`).
- `dπ ∘ dΛ = dτ ∘ dπ` (`π_Λ`), so `dΛ` maps the vertical space into the vertical space. It is
  onto because it is injective and `ℝ³` is finite-dimensional.
- Hence `dΛ` maps horizontal lifts to horizontal lifts.
-/

open RiemannianGeometry Bundle VectorField

namespace ExoticSpheres8And10

open Set Function Filter Topology Real Module

open scoped Manifold ContDiff RealInnerProductSpace

set_option maxSynthPendingDepth 3

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Gauge2

variable {m : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] {e : W} [Fact (finrank ℝ (Vs e) = m + 1)]
  (D : PolarData (m := m) e)

namespace PolarData

/-- The product base metric `ψR⟪,⟫` of the southern chart. -/
def β0 (y : Vs e) : Vs e →L[ℝ] Vs e →L[ℝ] ℝ := ψR y • ipL (Vs e)

theorem β0_apply (y a b : Vs e) : β0 y a b = ψR y * ⟪a, b⟫ := rfl

theorem β0_pos (y a : Vs e) (ha : a ≠ 0) : 0 < β0 y a a := by
  rw [β0_apply]; have := ψR_pos y; have := real_inner_self_pos.2 ha; positivity

theorem β0_nonneg (y a : Vs e) : 0 ≤ β0 y a a := by
  rw [β0_apply]; have := ψR_pos y; have : 0 ≤ ⟪a, a⟫ := real_inner_self_nonneg; positivity

/-- **Near the boundary, `τ^*g_A = g_0`** at every point where `χ = 0`. -/
theorem gB_τ {χt : ℝ → ℝ} (hχ : IsSouthCutoff χt) {r : Vs e → ℝ} (hr0 : ∀ y, r y ≠ 0)
    (hrρ : ∀ q y, r (D.ρVs q y) = r y) {y : Vs e} (hy : y ≠ 0) (hχ0 : χt (‖y‖ ^ 2) = 0)
    (c c' : Vs e) :
    SQ.gB D.ρVs (GsH (D.AS χt) r) (D.τ y) (fderiv ℝ D.τ y c) (fderiv ℝ D.τ y c') =
      SQ.gB D.ρVs (GsW β0 r) y c c' := by
  have hρ := D.contMDiff_ρVs
  have hGA := GsH_pos (A := D.AS χt) hr0
  have hG0 := GsW_pos (w := r) (β := β0) β0_pos β0_nonneg hr0
  set q₀ := (D.θS y)⁻¹
  set L := mfderiv (IN (Vs e)) (IN (Vs e)) (D.Λ q₀) (y, 1)
  have hΛp : D.Λ q₀ (y, 1) = (D.τ y, 1) := D.Λ_slice y
  -- (1) `L` is an isometry of the slice forms
  have hiso : ∀ u u' : Vs e × E3, GsH (D.AS χt) r (D.τ y) (L u) (L u') = GsW β0 r y u u' := by
    intro u u'
    have h := D.Λ_isometry hχ hrρ q₀ (p := (y, 1)) hy hχ0 u u'
    have hF : GH (D.AS χt) r (D.Λ q₀ (y, 1)) (L u) (L u') =
        GH (D.AS χt) r (D.τ y, 1) (L u) (L u') :=
      congrArg (fun q : Vs e × S3 => GH (D.AS χt) r q (L u) (L u')) hΛp
    calc GsH (D.AS χt) r (D.τ y) (L u) (L u') = GH (D.AS χt) r (D.τ y, 1) (L u) (L u') :=
          (GH_slice (D.τ y) (L u) (L u')).symm
      _ = GH (D.AS χt) r (D.Λ q₀ (y, 1)) (L u) (L u') := hF.symm
      _ = GW β0 r (y, 1) u u' := h
      _ = GsW β0 r y u u' := GW_slice y u u'
  -- (2) the chain rule at the slice: `dπl ∘ L = dτ ∘ dπl`
  have hΛd : MDifferentiableAt (IN (Vs e)) (IN (Vs e)) (D.Λ q₀) (y, 1) :=
    (D.contMDiffAt_Λ q₀ hy).mdifferentiableAt (by simp)
  have hπd : ∀ z, MDifferentiableAt (IN (Vs e)) 𝓘(ℝ, Vs e) (πN D.ρVs) z := fun z =>
    (contMDiff_πN hρ z).mdifferentiableAt (by simp)
  have hτd : DifferentiableAt ℝ D.τ y := (D.contDiffAt_τ hy).differentiableAt (by simp)
  have hτd' : MDifferentiableAt 𝓘(ℝ, Vs e) 𝓘(ℝ, Vs e) D.τ (πN D.ρVs (y, 1)) := by
    rw [πN_slice]; exact hτd.mdifferentiableAt
  have hcomp : πN D.ρVs ∘ D.Λ q₀ = D.τ ∘ πN D.ρVs := funext (D.π_Λ q₀)
  have hchain : ∀ u : TangentSpace (IN (Vs e)) (y, 1),
      dπl D.ρVs (D.τ y) (L u) = fderiv ℝ D.τ y (dπl D.ρVs y u) := by
    intro u
    have h1 : mfderiv (IN (Vs e)) 𝓘(ℝ, Vs e) (πN D.ρVs ∘ D.Λ q₀) (y, 1) u =
        mfderiv (IN (Vs e)) 𝓘(ℝ, Vs e) (D.τ ∘ πN D.ρVs) (y, 1) u := by rw [hcomp]
    rw [mfderiv_comp (y, 1) (hπd _) hΛd, mfderiv_comp (y, 1) hτd' (hπd _),
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply] at h1
    have hF1 : mfderiv (IN (Vs e)) 𝓘(ℝ, Vs e) (πN D.ρVs) (D.Λ q₀ (y, 1)) (L u) =
        mfderiv (IN (Vs e)) 𝓘(ℝ, Vs e) (πN D.ρVs) (D.τ y, 1) (L u) :=
      congrArg (fun q : Vs e × S3 => mfderiv (IN (Vs e)) 𝓘(ℝ, Vs e) (πN D.ρVs) q (L u)) hΛp
    have hF2 : mfderiv 𝓘(ℝ, Vs e) 𝓘(ℝ, Vs e) D.τ (πN D.ρVs (y, 1))
        (mfderiv (IN (Vs e)) 𝓘(ℝ, Vs e) (πN D.ρVs) (y, 1) u) =
        mfderiv 𝓘(ℝ, Vs e) 𝓘(ℝ, Vs e) D.τ y
          (mfderiv (IN (Vs e)) 𝓘(ℝ, Vs e) (πN D.ρVs) (y, 1) u) :=
      congrArg (fun z : Vs e => mfderiv 𝓘(ℝ, Vs e) 𝓘(ℝ, Vs e) D.τ z
        (mfderiv (IN (Vs e)) 𝓘(ℝ, Vs e) (πN D.ρVs) (y, 1) u)) (πN_slice y)
    rw [hF1, hF2, mfderiv_eq_fderiv] at h1
    have e1 : mfderiv (IN (Vs e)) 𝓘(ℝ, Vs e) (πN D.ρVs) (D.τ y, 1) (L u) =
        dπl D.ρVs (D.τ y) (L u) := by
      rw [← dπN_eq hρ]; rfl
    have e2 : mfderiv (IN (Vs e)) 𝓘(ℝ, Vs e) (πN D.ρVs) (y, 1) u = dπl D.ρVs y u := by
      rw [← dπN_eq hρ]; rfl
    rw [e1, e2] at h1
    exact h1
  -- (3) `L` maps vertical vectors to vertical vectors, and onto
  have hker : ∀ b : E3, L (ιv D.ρVs y b) = ιv D.ρVs (D.τ y) ((L (ιv D.ρVs y b)).2) := by
    intro b
    have h0 := hchain (ιv D.ρVs y b)
    have hz : dπl D.ρVs y (ιv D.ρVs y b) = 0 := by rw [dπl_apply, ιv_apply]; simp
    rw [hz, map_zero] at h0
    have h0' : (L (ιv D.ρVs y b)).1 - KY D.ρVs (D.τ y) (L (ιv D.ρVs y b)).2 = 0 := h0
    exact Prod.ext (sub_eq_zero.1 h0') rfl
  let T : E3 →L[ℝ] E3 := (ContinuousLinearMap.snd ℝ (Vs e) E3).comp (L.comp (ιv D.ρVs y))
  have hT : ∀ b, T b = (L (ιv D.ρVs y b)).2 := fun b => rfl
  have hinj : Injective T := by
    refine (injective_iff_map_eq_zero T).2 fun b hb => ?_
    have h1 : L (ιv D.ρVs y b) = 0 :=
      (hker b).trans (show ιv D.ρVs (D.τ y) (T b) = 0 by rw [hb, map_zero])
    have h2 := hiso (ιv D.ρVs y b) (ιv D.ρVs y b)
    rw [h1] at h2
    have h0 : GsH (D.AS χt) r (D.τ y) (0 : Vs e × E3) (0 : Vs e × E3) = 0 := by simp
    rw [show GsH (D.AS χt) r (D.τ y) (0 : TangentSpace (IN (Vs e)) (D.Λ q₀ (y, 1)))
      (0 : TangentSpace (IN (Vs e)) (D.Λ q₀ (y, 1))) = 0 from h0] at h2
    by_contra hne
    have hne' : ιv D.ρVs y b ≠ 0 := fun h => hne (by
      have := congrArg Prod.snd h; simpa [ιv_apply] using this)
    have := hG0 y _ hne'
    linarith
  have hsurj : Surjective T :=
    (LinearMap.injective_iff_surjective (f := (T : E3 →ₗ[ℝ] E3))).mp hinj
  -- (4) `L` maps horizontal lifts to horizontal lifts
  have hL : ∀ c₁ : Vs e, L (SQ.hlift D.ρVs (GsW β0 r) y c₁) =
      SQ.hlift D.ρVs (GsH (D.AS χt) r) (D.τ y) (fderiv ℝ D.τ y c₁) := by
    intro c₁
    have hhor : ∀ b', GsH (D.AS χt) r (D.τ y) (L (SQ.hlift D.ρVs (GsW β0 r) y c₁))
        (ιv D.ρVs (D.τ y) b') = 0 := by
      intro b'
      obtain ⟨b, hb⟩ := hsurj b'
      have : ιv D.ρVs (D.τ y) b' = L (ιv D.ρVs y b) := by rw [hker b, ← hT, hb]
      rw [this, hiso]
      exact SQ.hlift_horizontal D.ρVs hG0 y c₁ b
    have := SQ.eq_hlift D.ρVs hGA (D.τ y) hhor
    rw [hchain (SQ.hlift D.ρVs (GsW β0 r) y c₁), SQ.dπl_hlift D.ρVs hG0] at this
    exact this
  show GsH (D.AS χt) r (D.τ y) (SQ.hlift D.ρVs (GsH (D.AS χt) r) (D.τ y) (fderiv ℝ D.τ y c))
      (SQ.hlift D.ρVs (GsH (D.AS χt) r) (D.τ y) (fderiv ℝ D.τ y c')) =
    GsW β0 r y (SQ.hlift D.ρVs (GsW β0 r) y c) (SQ.hlift D.ρVs (GsW β0 r) y c')
  rw [← hL c, ← hL c', hiso]

end PolarData

end Gauge2

end

end ExoticSpheres8And10
