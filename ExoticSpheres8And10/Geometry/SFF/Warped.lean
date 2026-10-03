/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Geometry.SFF.Naturality
import ExoticSpheres8And10.Curvature.Northern.Centre

/-! # Second fundamental forms of warped products, in the chart `V × ℝ³`

`Gwarp β w (Y, z) = β(Y) ⊕ w(Y)² HR(z)`: a base metric `β` on `V`, warped with the round `S³`
(in its stereographic chart) by `w`. Both of [D]'s source metrics have this form near the
gluing boundary:
- `G_N` in the chart `Φc` (`Gw = Gwarp βN r̃`);
- `G_S` in the chart `Φc` after the gauge `u = θ̂u'`, with `β = ψR` the round metric.

For a base level function `hb`, with base unit normal `ν_B`:

  **`sff_warp`**: `sff(Z, Z) = [β(Dν_B·Z₁, Z₁) + ½ Dβ(ν_B)(Z₁, Z₁)] + w·Dw(ν_B)·HR(Z₂, Z₂)`,

the warped-product formula `B = B_base ⊕ (ν_B log w)·g_fibre`.
-/

open RiemannianGeometry Bundle VectorField

namespace ExoticSpheres8And10

open Set Function Filter Topology Real

open scoped Manifold ContDiff RealInnerProductSpace

set_option maxSynthPendingDepth 3

noncomputable section

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Warp

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The warped metric `β(Y) ⊕ w(Y)² HR(z)` on `V × ℝ³`. -/
def Gwarp (β : V → V →L[ℝ] V →L[ℝ] ℝ) (w : V → ℝ) (p : V × E3) :
    (V × E3) →L[ℝ] (V × E3) →L[ℝ] ℝ :=
  bil (β p.1) (ContinuousLinearMap.fst ℝ V E3) +
    (w p.1 ^ 2) • bil (HR p.2) (ContinuousLinearMap.snd ℝ V E3)

theorem Gwarp_apply (β : V → V →L[ℝ] V →L[ℝ] ℝ) (w : V → ℝ) (p a b : V × E3) :
    Gwarp β w p a b = β p.1 a.1 b.1 + w p.1 ^ 2 * (ψR p.2 * ⟪a.2, b.2⟫) := by
  simp only [Gwarp, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, bil_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul, HR_apply]

theorem contDiff_Gwarp {β : V → V →L[ℝ] V →L[ℝ] ℝ} {w : V → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hw : ContDiff ℝ ∞ w) : ContDiff ℝ ∞ (Gwarp β w) := by
  rw [contDiff_clm_apply_iff]
  intro a
  rw [contDiff_clm_apply_iff]
  intro b
  have e : (fun p => Gwarp β w p a b) = fun p : V × E3 =>
      β p.1 a.1 b.1 + w p.1 ^ 2 * (ψR p.2 * ⟪a.2, b.2⟫) := funext fun p => Gwarp_apply β w p a b
  show ContDiff ℝ ∞ fun p => Gwarp β w p a b
  rw [e]
  exact (((hβ.comp contDiff_fst).clm_apply contDiff_const).clm_apply contDiff_const).add
    (((hw.comp contDiff_fst).pow 2).mul ((contDiff_ψR.comp contDiff_snd).mul contDiff_const))

/-- The derivative of the metric in a base direction. -/
theorem fderiv_Gwarp_base {β : V → V →L[ℝ] V →L[ℝ] ℝ} {w : V → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hw : ContDiff ℝ ∞ w) (p : V × E3) (n : V) (Z : V × E3) :
    fderiv ℝ (Gwarp β w) p (n, 0) Z Z =
      fderiv ℝ β p.1 n Z.1 Z.1 + 2 * w p.1 * fderiv ℝ w p.1 n * (ψR p.2 * ⟪Z.2, Z.2⟫) := by
  have hG := (contDiff_Gwarp hβ hw).differentiable (by simp) p
  have hβd := (hβ.differentiable (by simp)) p.1
  have hwd := (hw.differentiable (by simp)) p.1
  have hψd := (contDiff_ψR (K := E3)).differentiable (by simp) p.2
  -- `fderiv G p v Z Z` is the derivative of the scalar `y ↦ G y Z Z`
  have h1 := fderiv_pair (G := Gwarp β w) (A := fun _ => Z) (B := fun _ => Z) hG
    (differentiableAt_const Z) (differentiableAt_const Z) (n, 0)
  simp only [fderiv_const_apply, ContinuousLinearMap.zero_apply, map_zero, add_zero] at h1
  rw [← h1]
  have e : (fun y : V × E3 => Gwarp β w y Z Z) = fun y : V × E3 =>
      β y.1 Z.1 Z.1 + w y.1 ^ 2 * (ψR y.2 * ⟪Z.2, Z.2⟫) := funext fun y => Gwarp_apply β w y Z Z
  rw [e]
  have hb1 : HasFDerivAt (fun y : V × E3 => β y.1 Z.1 Z.1)
      ((((fderiv ℝ β p.1).flip Z.1).flip Z.1).comp (ContinuousLinearMap.fst ℝ V E3)) p := by
    have := ((hβd.hasFDerivAt.comp p hasFDerivAt_fst).clm_apply
      (hasFDerivAt_const Z.1 p)).clm_apply (hasFDerivAt_const Z.1 p)
    refine this.congr_fderiv ?_
    ext v <;> simp
  have hw1 := (hwd.hasFDerivAt.comp p hasFDerivAt_fst).pow 2
  have hψ1 := (hψd.hasFDerivAt.comp p hasFDerivAt_snd).mul_const ⟪Z.2, Z.2⟫
  have h := (hb1.add (hw1.mul hψ1)).congr_of_eventuallyEq
    (f₁ := fun y : V × E3 => β y.1 Z.1 Z.1 + w y.1 ^ 2 * (ψR y.2 * ⟪Z.2, Z.2⟫))
    (Eventually.of_forall fun y => rfl)
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, map_zero, zero_mul, add_zero, mul_zero]
  simp only [Function.comp_apply, Nat.cast_ofNat]
  ring

theorem isSymm_cmet_Gwarp {β : V → V →L[ℝ] V →L[ℝ] ℝ} {w : V → ℝ}
    (hβs : ∀ Y a b, β Y a b = β Y b a) : IsSymm (cmet (Gwarp β w)) := fun p a b => by
  simp only [cmet_ts, Gwarp_apply, hβs p.1 (fromTS a).1, real_inner_comm (fromTS a).2]

theorem isPosDef_cmet_Gwarp {β : V → V →L[ℝ] V →L[ℝ] ℝ} {w : V → ℝ}
    (hβp : ∀ Y a, a ≠ 0 → 0 < β Y a a) (hβn : ∀ Y a, 0 ≤ β Y a a) (hw0 : ∀ Y, w Y ≠ 0) :
    IsPosDef (cmet (Gwarp β w)) := fun p v hv => by
  rw [cmet_ts, Gwarp_apply]
  set a := (fromTS v).1
  set c := (fromTS v).2
  have hw2 : 0 < w p.1 ^ 2 := by have := hw0 p.1; positivity
  have hψ := ψR_pos p.2
  by_cases ha : a = 0
  · have hc : c ≠ 0 := fun hc => hv (Prod.ext ha hc)
    have : 0 < ⟪c, c⟫ := real_inner_self_pos.2 hc
    rw [ha]; simp only [map_zero, ContinuousLinearMap.zero_apply, zero_add]; positivity
  · have h1 := hβp p.1 a ha
    have : 0 ≤ ⟪c, c⟫ := real_inner_self_nonneg
    positivity

/-- The unit normal of a base level function, from the base gradient `vB`
(`β(vB, ·) = d hb`). -/
theorem unitNormal_Gwarp {β : V → V →L[ℝ] V →L[ℝ] ℝ} {w : V → ℝ}
    (hnd : IsNondegenerate (cmet (Gwarp β w))) {hb : V → ℝ} {p : V × E3} {vB : V}
    (hhb : DifferentiableAt ℝ hb p.1) (hv : ∀ c, β p.1 vB c = fderiv ℝ hb p.1 c) :
    unitNormal hnd (hb ∘ Prod.fst) p =
      toTSv p (((√(β p.1 vB vB))⁻¹ • vB, (0 : E3))) := by
  have hd : ∀ c : V × E3, fderiv ℝ (hb ∘ Prod.fst) p c = fderiv ℝ hb p.1 c.1 := fun c => by
    rw [fderiv_comp p hhb differentiableAt_fst, ContinuousLinearMap.comp_apply, fderiv_fst]; rfl
  rw [unitNormal_cmet hnd (v := (vB, 0)) fun c => by rw [Gwarp_apply, hd, ← hv]; simp]
  congr 1
  simp [Gwarp_apply]

/-- **The warped-product formula for the second fundamental form.** -/
theorem sff_warp {β : V → V →L[ℝ] V →L[ℝ] ℝ} {w : V → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hw : ContDiff ℝ ∞ w) (hβs : ∀ Y a b, β Y a b = β Y b a)
    (hnd : IsNondegenerate (cmet (Gwarp β w))) {hb : V → ℝ} {νB : V → V} {p : V × E3}
    (hνB : ContDiffAt ℝ 1 νB p.1)
    (hνeq : ∀ᶠ q in 𝓝 p, unitNormal hnd (hb ∘ Prod.fst) q = toTS (fun q => (νB q.1, (0 : E3))) q)
    (Z : V × E3) :
    sff hnd (hb ∘ Prod.fst) p (toTSv p Z) (toTSv p Z) =
      β p.1 (fderiv ℝ νB p.1 Z.1) Z.1 + (1 / 2) * fderiv ℝ β p.1 (νB p.1) Z.1 Z.1 +
        w p.1 * fderiv ℝ w p.1 (νB p.1) * (ψR p.2 * ⟪Z.2, Z.2⟫) := by
  have hν : ContDiffAt ℝ 1 (fun q : V × E3 => (νB q.1, (0 : E3))) p :=
    (hνB.comp p contDiffAt_fst).prodMk contDiffAt_const
  rw [sff_cmet (isSymm_cmet_Gwarp hβs) hnd ((contDiff_Gwarp hβ hw).of_le (by simp)) hν hνeq Z]
  have hdν : fderiv ℝ (fun q : V × E3 => (νB q.1, (0 : E3))) p Z = (fderiv ℝ νB p.1 Z.1, 0) := by
    have h := ((hνB.differentiableAt one_ne_zero).hasFDerivAt.comp p hasFDerivAt_fst).prodMk
      (hasFDerivAt_const (0 : E3) p)
    rw [show (fun q : V × E3 => (νB q.1, (0 : E3))) = fun x => ((νB ∘ Prod.fst) x, (0 : E3)) from
      rfl, h.fderiv]; rfl
  rw [hdν, Gwarp_apply, fderiv_Gwarp_base hβ hw]
  simp only [inner_zero_left, mul_zero, add_zero]
  ring

end Warp

end

end ExoticSpheres8And10
