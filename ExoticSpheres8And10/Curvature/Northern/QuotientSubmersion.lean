/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Curvature.Northern.Quotient
import RiemannianGeometry.EquivariantSubmersion

/-! # §4: the northern quotient `(V × S³, G_N) → (V, g_N)` is a Riemannian submersion

Derivatives at the slice points `(Y, 1)`:

* `K_Y = d/dq|₁ ρ(q)Y : T₁S³ → V` and `D = d/dq|₁ (q ∈ ℍ) : T₁S³ → ℍ`;
* `mfderiv_πN_slice`: `dπ_{(Y,1)}(a, α) = a − K_Y α`;
* `inner_Y_KY`: `⟪Y, K_Y β⟫ = 0`;
* `northMetric_slice`: `G_N` at `(Y, 1)` is `⟪a,b⟫ + ψ(|Y|²)⟪Y,a⟫⟪Y,b⟫ + r̃(Y)²⟪Dα, Dβ⟫`.
-/

open RiemannianGeometry Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Real

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Slice

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ρV : S3 →* (V ≃ₗᵢ[ℝ] V)}
  (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, V →L[ℝ] V) ∞ fun q : S3 => ((ρV q : V ≃L[ℝ] V) : V →L[ℝ] V))

/-- `ρ` as a map to `L(V)`. -/
def ρhat (ρV : S3 →* (V ≃ₗᵢ[ℝ] V)) (q : S3) : V →L[ℝ] V := ((ρV q : V ≃L[ℝ] V) : V →L[ℝ] V)

/-- `dρ₁ : T₁S³ → L(V)`. -/
def dρ (ρV : S3 →* (V ≃ₗᵢ[ℝ] V)) : E3 →L[ℝ] (V →L[ℝ] V) :=
  mfderiv (𝓡 3) 𝓘(ℝ, V →L[ℝ] V) (ρhat ρV) 1

/-- The infinitesimal action at `Y`, `K_Y β = dρ₁(β) Y`. -/
def KY (ρV : S3 →* (V ≃ₗᵢ[ℝ] V)) (Y : V) : E3 →L[ℝ] V :=
  (ContinuousLinearMap.apply ℝ V Y).comp (dρ ρV)

/-- `D = d(ι)₁ : T₁S³ → ℍ`. -/
def Dq : E3 →L[ℝ] Quaternion ℝ :=
  mfderiv (𝓡 3) 𝓘(ℝ, Quaternion ℝ) (Subtype.val : S3 → Quaternion ℝ) 1

omit [FiniteDimensional ℝ V] in
include hρ in
theorem mfderiv_orbit (Y : V) :
    mfderiv (𝓡 3) 𝓘(ℝ, V) (fun q : S3 => ρV q Y) 1 = KY ρV Y := by
  have hd : MDifferentiableAt (𝓡 3) 𝓘(ℝ, V →L[ℝ] V) (ρhat ρV) 1 :=
    (hρ 1).mdifferentiableAt (by simp)
  have e : (fun q : S3 => ρV q Y) = (ContinuousLinearMap.apply ℝ V Y) ∘ ρhat ρV := rfl
  rw [e, mfderiv_comp (1 : S3) (ContinuousLinearMap.apply ℝ V Y).mdifferentiableAt hd,
    (ContinuousLinearMap.apply ℝ V Y).hasMFDerivAt.mfderiv]
  rfl

include hρ in
theorem mdifferentiableAt_orbit (Y : V) :
    MDifferentiableAt (𝓡 3) 𝓘(ℝ, V) (fun q : S3 => ρV q Y) 1 :=
  ((hρ.clm_apply contMDiff_const) 1).mdifferentiableAt (by simp)

theorem ρV_one_apply (Y : V) : ρV 1 Y = Y := by rw [map_one]; rfl

include hρ in
theorem hasMFDerivAt_orbit (Y : V) :
    HasMFDerivAt (𝓡 3) 𝓘(ℝ, V) (fun q : S3 => ρV q Y) 1 (KY (V := V) ρV Y) := by
  have := (mdifferentiableAt_orbit hρ Y).hasMFDerivAt
  rw [mfderiv_orbit hρ] at this
  exact this

include hρ in
/-- `⟪Y, K_Y β⟫ = 0`: the orbits of an orthogonal representation lie on spheres. -/
theorem inner_Y_KY (Y : V) (β : E3) : ⟪Y, KY ρV Y β⟫ = 0 := by
  have e : ((fun y : V => ‖y‖ ^ 2) ∘ fun q : S3 => ρV q Y) = fun _ => ‖Y‖ ^ 2 := by
    funext q; simp
  have hn : HasMFDerivAt 𝓘(ℝ, V) 𝓘(ℝ, ℝ) (fun y : V => ‖y‖ ^ 2) (ρV 1 Y)
      (2 • innerSL ℝ Y) := by
    rw [ρV_one_apply]; exact (hasStrictFDerivAt_norm_sq Y).hasFDerivAt.hasMFDerivAt
  have c := (HasMFDerivAt.comp (f := fun q : S3 => ρV q Y) 1 hn (hasMFDerivAt_orbit hρ Y)).mfderiv
  rw [e, mfderiv_const] at c
  have h := DFunLike.congr_fun c β
  have h' : (0 : ℝ) = (2 • innerSL ℝ Y) (KY ρV Y β) := h
  rw [ContinuousLinearMap.smul_apply, innerSL_apply_apply, two_smul] at h'
  linarith

/-- `dπ` at the slice point `(Y, 1)`, as a linear map `V × ℝ³ → V`. -/
def dπN (ρV : S3 →* (V ≃ₗᵢ[ℝ] V)) (Y : V) : V × E3 →L[ℝ] V :=
  mfderiv (IN V) 𝓘(ℝ, V) (πN ρV) (Y, 1)

include hρ in
/-- **The differential of the orbit map at a slice point**: `dπ_{(Y,1)}(a, α) = a − K_Y α`. -/
theorem dπN_apply (Y a : V) (α : E3) : dπN ρV Y (a, α) = a - KY ρV Y α := by
  have hπ : ∀ p, MDifferentiableAt (IN V) 𝓘(ℝ, V) (πN ρV) p := fun p =>
    (contMDiff_πN hρ p).mdifferentiableAt (by simp)
  -- the slice `y ↦ (y, 1)` is a section of `π`
  have hs : HasMFDerivAt 𝓘(ℝ, V) (IN V) (fun y : V => (y, (1 : S3))) Y
      ((ContinuousLinearMap.id ℝ V).prod (0 : V →L[ℝ] E3)) :=
    (hasMFDerivAt_id Y).prodMk (hasMFDerivAt_const _ _)
  have es : πN ρV ∘ (fun y : V => (y, (1 : S3))) = id := by
    funext y; show ρV 1⁻¹ y = y; rw [inv_one, ρV_one_apply]
  have hπ1 : HasMFDerivAt (IN V) 𝓘(ℝ, V) (πN ρV) (Y, 1) (dπN ρV Y) := (hπ _).hasMFDerivAt
  have h1 : ∀ b : V, dπN ρV Y (b, 0) = b := fun b => by
    have c := (hπ1.comp Y hs).mfderiv
    rw [es, mfderiv_id] at c
    have := DFunLike.congr_fun c b
    exact this.symm
  -- the orbit `q ↦ q ⋆ (Y, 1)` is collapsed by `π`
  have ho : HasMFDerivAt (𝓡 3) (IN V) (fun q : S3 => (ρV q Y, q)) 1
      ((KY (V := V) ρV Y).prod (ContinuousLinearMap.id ℝ E3)) :=
    (hasMFDerivAt_orbit hρ Y).prodMk (hasMFDerivAt_id (I := 𝓡 3) (1 : S3))
  have eo : πN ρV ∘ (fun q : S3 => (ρV q Y, q)) = fun _ => Y := by
    funext q
    show ρV q⁻¹ (ρV q Y) = Y
    rw [show ρV q⁻¹ (ρV q Y) = (ρV q⁻¹ * ρV q) Y from rfl, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have hπ1' : HasMFDerivAt (IN V) 𝓘(ℝ, V) (πN ρV) (ρV 1 Y, 1) (dπN ρV Y) := by
    rw [ρV_one_apply]; exact hπ1
  have h2 : ∀ β : E3, dπN ρV Y (KY ρV Y β, β) = 0 := fun β => by
    have c := (HasMFDerivAt.comp (f := fun q : S3 => (ρV q Y, q)) 1 hπ1' ho).mfderiv
    rw [eo, mfderiv_const] at c
    have := DFunLike.congr_fun c β
    exact this.symm
  calc dπN ρV Y (a, α) = dπN ρV Y ((a - KY ρV Y α, 0) + (KY ρV Y α, α)) := by
        congr 1; ext <;> simp
    _ = dπN ρV Y (a - KY ρV Y α, 0) + dπN ρV Y (KY ρV Y α, α) := map_add _ _ _
    _ = a - KY ρV Y α := by rw [h1, h2, add_zero]

end Slice

/-! ### The northern metric at slice points -/

section SliceMetric

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- `(u, w) ↦ q(Lu, Lw)`, as a bilinear form. -/
def bil {T F : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (q : F →L[ℝ] F →L[ℝ] ℝ) (L : T →L[ℝ] F) : T →L[ℝ] T →L[ℝ] ℝ :=
  ((q.comp L).flip.comp L).flip

@[simp] theorem bil_apply {T F : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (q : F →L[ℝ] F →L[ℝ] ℝ) (L : T →L[ℝ] F) (u w : T) :
    bil q L u w = q (L u) (L w) := rfl

theorem mvfderiv_fQ (p : V × S3) (v : TangentSpace (IN V) p) :
    mvfderiv (IN V) fQ p v = ⟪p.1, (v.1 : V)⟫ := by
  have hf : HasFDerivAt (fun y : V => ‖y‖ ^ 2 / 2) (innerSL ℝ p.1) p.1 := by
    have h := HasFDerivAt.const_smul (hasStrictFDerivAt_norm_sq p.1).hasFDerivAt (1 / 2 : ℝ)
    have e : (fun y : V => ‖y‖ ^ 2 / 2) = fun y => (1 / 2 : ℝ) • ‖y‖ ^ 2 := by
      funext y; rw [smul_eq_mul]; ring
    rw [show (1 / 2 : ℝ) • (2 • innerSL ℝ p.1) = innerSL ℝ p.1 by
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]; norm_num] at h
    rw [e]; exact h
  have hQ : HasMFDerivAt (IN V) 𝓘(ℝ, ℝ) (fQ (V := V)) p
      ((innerSL ℝ p.1).comp (ContinuousLinearMap.fst ℝ V E3)) :=
    hf.hasMFDerivAt.comp p (hasMFDerivAt_fst p)
  simp only [mvfderiv, ContinuousLinearMap.comp_apply, hQ.mfderiv]
  rfl

theorem mvfderiv_fU (p : V × S3) (v : TangentSpace (IN V) p) :
    mvfderiv (IN V) fU p v = mvfderiv (𝓡 3) (Subtype.val : S3 → Quaternion ℝ) p.2 v.2 := by
  have hc : MDifferentiableAt (𝓡 3) 𝓘(ℝ, Quaternion ℝ) (Subtype.val : S3 → Quaternion ℝ) p.2 :=
    ((contMDiff_coe_sphere (m := 1)) p.2).mdifferentiableAt one_ne_zero
  have hs : MDifferentiableAt (IN V) (𝓡 3) (Prod.snd : V × S3 → S3) p :=
    ((contMDiff_snd (n := 1)) p).mdifferentiableAt one_ne_zero
  have h : mfderiv (IN V) 𝓘(ℝ, Quaternion ℝ) (fU (V := V)) p =
      (mfderiv (𝓡 3) 𝓘(ℝ, Quaternion ℝ) (Subtype.val : S3 → Quaternion ℝ) p.2).comp
        (mfderiv (IN V) (𝓡 3) (Prod.snd : V × S3 → S3) p) := mfderiv_comp p hc hs
  simp only [mvfderiv, ContinuousLinearMap.comp_apply, h, mfderiv_snd]
  rfl

/-- **The northern metric at the slice point `(Y, 1)`**, as a bilinear form on `V × ℝ³`:
`⟪a, b⟫ + ψ(|Y|²)⟪Y, a⟫⟪Y, b⟫ + r̃(Y)²⟪Dα, Dβ⟫`. -/
def Gs (δ : ℝ) (rt : V → ℝ) (Y : V) : V × E3 →L[ℝ] V × E3 →L[ℝ] ℝ :=
  bil (ipL V) (ContinuousLinearMap.fst ℝ V E3) +
    ψδ δ (‖Y‖ ^ 2) • bil mulL ((innerSL ℝ Y).comp (ContinuousLinearMap.fst ℝ V E3)) +
    (rt Y ^ 2) • bil (ipL (Quaternion ℝ)) (Dq.comp (ContinuousLinearMap.snd ℝ V E3))

theorem Gs_apply (δ : ℝ) (rt : V → ℝ) (Y : V) (u w : V × E3) :
    Gs δ rt Y u w = ⟪u.1, w.1⟫ + ψδ δ (‖Y‖ ^ 2) * (⟪Y, u.1⟫ * ⟪Y, w.1⟫) +
      rt Y ^ 2 * ⟪Dq u.2, Dq w.2⟫ := by
  simp only [Gs, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, bil_apply,
    ipL_apply, mulL_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', innerSL_apply_apply, smul_eq_mul]

theorem northMetric_slice (δ : ℝ) (rt : V → ℝ) (Y : V) (u w : TangentSpace (IN V) (Y, (1 : S3))) :
    northMetric δ rt (Y, 1) u w = Gs δ rt Y u w := by
  rw [northMetric_apply, mvfderiv_fY, mvfderiv_fY, mvfderiv_fQ, mvfderiv_fQ, mvfderiv_fU,
    mvfderiv_fU]
  exact (Gs_apply δ rt Y u w).symm

theorem Gs_symm (δ : ℝ) (rt : V → ℝ) (Y : V) (u w : V × E3) : Gs δ rt Y u w = Gs δ rt Y w u := by
  rw [Gs_apply, Gs_apply, real_inner_comm w.1 u.1, real_inner_comm (Dq w.2) (Dq u.2)]
  ring

theorem Gs_pos (δ : ℝ) {rt : V → ℝ} (hrt : ∀ Y, rt Y ≠ 0) (Y : V) {u : V × E3} (hu : u ≠ 0) :
    0 < Gs δ rt Y u u := by
  have := isPosDef_northMetric δ hrt (Y, 1) (v := u) hu
  exact this.trans_eq (northMetric_slice δ rt Y u u)

theorem contDiff_Gs_apply (δ : ℝ) {rt : V → ℝ} (hrt : ContDiff ℝ ∞ rt) {f g : V → V × E3}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ fun Y => Gs δ rt Y (f Y) (g Y) := by
  have e : (fun Y => Gs δ rt Y (f Y) (g Y)) = fun Y => ⟪(f Y).1, (g Y).1⟫ +
      ψδ δ (‖Y‖ ^ 2) * (⟪Y, (f Y).1⟫ * ⟪Y, (g Y).1⟫) + rt Y ^ 2 * ⟪Dq (f Y).2, Dq (g Y).2⟫ :=
    funext fun Y => Gs_apply δ rt Y _ _
  rw [e]
  have hψ : ContDiff ℝ ∞ fun Y : V => ψδ δ (‖Y‖ ^ 2) := (contDiff_ψδ δ).comp (contDiff_norm_sq ℝ)
  exact ((hf.fst.inner ℝ hg.fst).add (hψ.mul ((contDiff_id.inner ℝ hf.fst).mul
    (contDiff_id.inner ℝ hg.fst)))).add ((hrt.pow 2).mul
      ((Dq.contDiff.comp hf.snd).inner ℝ (Dq.contDiff.comp hg.snd)))

end SliceMetric

/-! ### The horizontal lift at slice points, and the quotient metric on `V` -/

section Lift

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (ρV : S3 →* (V ≃ₗᵢ[ℝ] V)) (δ : ℝ) (rt : V → ℝ)

/-- The standard orthonormal basis of `ℝ³`. -/
abbrev bE : OrthonormalBasis (Fin 3) ℝ E3 := EuclideanSpace.basisFun (Fin 3) ℝ

/-- The vertical vectors at `(Y, 1)`: `β ↦ (K_Y β, β)`. -/
def ιv (Y : V) : E3 →L[ℝ] V × E3 := (KY ρV Y).prod (ContinuousLinearMap.id ℝ E3)

/-- `dπ` at `(Y, 1)`, written out: `(a, α) ↦ a − K_Y α`. -/
def dπl (Y : V) : V × E3 →L[ℝ] V :=
  ContinuousLinearMap.fst ℝ V E3 - (KY ρV Y).comp (ContinuousLinearMap.snd ℝ V E3)

/-- The obstruction to horizontality: `u ↦ Σᵢ G(u, (K eᵢ, eᵢ)) eᵢ`. -/
def hz (Y : V) : V × E3 →L[ℝ] E3 :=
  ∑ i : Fin 3, ((Gs δ rt Y).flip (ιv ρV Y (bE i))).smulRight (bE i)

theorem hz_apply (Y : V) (u : V × E3) :
    hz ρV δ rt Y u = ∑ i : Fin 3, Gs δ rt Y u (ιv ρV Y (bE i)) • bE i := by
  simp [hz, ContinuousLinearMap.smulRight_apply]

/-- `Φ_Y = (dπ, hz) : V × ℝ³ → V × ℝ³`; its kernel is `vertical ∩ vertical^⊥ = 0`. -/
def Φs (Y : V) : V × E3 →L[ℝ] V × E3 := (dπl ρV Y).prod (hz ρV δ rt Y)

theorem forall_basis_eq_zero {ℓ : E3 →L[ℝ] ℝ} (h : ∀ i, ℓ (bE i) = 0) (β : E3) : ℓ β = 0 := by
  have h' : ∀ i, ℓ (EuclideanSpace.single i 1) = 0 := fun i => by simpa using h i
  rw [← (bE).sum_repr β, map_sum]
  simp [h']

theorem hz_eq_zero_iff (Y : V) (u : V × E3) :
    hz ρV δ rt Y u = 0 ↔ ∀ β, Gs δ rt Y u (ιv ρV Y β) = 0 := by
  constructor
  · intro h β
    have hc : ∀ i, Gs δ rt Y u (ιv ρV Y (bE i)) = 0 := by
      intro i
      have := congrArg (fun x : E3 => x i) h
      simpa [hz_apply, Pi.single_apply] using this
    exact forall_basis_eq_zero (ℓ := (Gs δ rt Y u).comp (ιv ρV Y)) hc β
  · intro h
    rw [hz_apply]
    simp [h]

theorem ιv_apply (Y : V) (β : E3) : ιv ρV Y β = (KY ρV Y β, β) := rfl

theorem dπl_apply (Y : V) (u : V × E3) : dπl ρV Y u = u.1 - KY ρV Y u.2 := rfl

variable {rt}

theorem Φs_injective (hrt : ∀ Y, rt Y ≠ 0) (Y : V) : Function.Injective (Φs ρV δ rt Y) := by
  refine (injective_iff_map_eq_zero _).2 fun u hu => ?_
  have h1 : dπl ρV Y u = 0 := congrArg Prod.fst hu
  have h2 : hz ρV δ rt Y u = 0 := congrArg Prod.snd hu
  rw [hz_eq_zero_iff] at h2
  have hv : u = ιv ρV Y u.2 := by
    rw [dπl_apply, sub_eq_zero] at h1
    rw [ιv_apply, ← h1]
  -- `u = ιv u.2`, so `G(u, u) = G(u, ιv u.2) = 0`
  by_contra hne
  have hpos := Gs_pos δ hrt Y hne
  have h3 := h2 u.2
  rw [← hv] at h3
  linarith

/-- `Φ_Y` as a continuous linear equivalence. -/
def Φe (hrt : ∀ Y, rt Y ≠ 0) (Y : V) : (V × E3) ≃L[ℝ] (V × E3) :=
  (LinearEquiv.ofInjectiveEndo (Φs ρV δ rt Y).toLinearMap (Φs_injective ρV δ hrt Y)).toContinuousLinearEquiv

theorem coe_Φe (hrt : ∀ Y, rt Y ≠ 0) (Y : V) : (Φe ρV δ hrt Y : V × E3 →L[ℝ] V × E3) = Φs ρV δ rt Y := by
  ext u <;> rfl

theorem isInvertible_Φs (hrt : ∀ Y, rt Y ≠ 0) (Y : V) : (Φs ρV δ rt Y).IsInvertible :=
  ⟨Φe ρV δ hrt Y, coe_Φe ρV δ hrt Y⟩

variable (rt)

/-- **The horizontal lift** at `(Y, 1)`: `c ↦ Φ_Y⁻¹(c, 0)`. -/
def hlift (Y : V) : V →L[ℝ] V × E3 :=
  (ContinuousLinearMap.inverse (Φs ρV δ rt Y)).comp (ContinuousLinearMap.inl ℝ V E3)

variable {rt}

theorem Φs_hlift (hrt : ∀ Y, rt Y ≠ 0) (Y c : V) : Φs ρV δ rt Y (hlift ρV δ rt Y c) = (c, 0) := by
  simp only [hlift, ContinuousLinearMap.comp_apply, ← coe_Φe ρV δ hrt Y,
    ContinuousLinearMap.inverse_equiv, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.inl_apply]

theorem dπl_hlift (hrt : ∀ Y, rt Y ≠ 0) (Y c : V) : dπl ρV Y (hlift ρV δ rt Y c) = c :=
  congrArg Prod.fst (Φs_hlift ρV δ hrt Y c)

theorem hlift_horizontal (hrt : ∀ Y, rt Y ≠ 0) (Y c : V) (β : E3) :
    Gs δ rt Y (hlift ρV δ rt Y c) (ιv ρV Y β) = 0 :=
  (hz_eq_zero_iff ρV δ rt Y _).1 (congrArg Prod.snd (Φs_hlift ρV δ hrt Y c)) β

/-- **Uniqueness of horizontal lifts.** -/
theorem eq_hlift (hrt : ∀ Y, rt Y ≠ 0) (Y : V) {u : V × E3}
    (hu : ∀ β, Gs δ rt Y u (ιv ρV Y β) = 0) : u = hlift ρV δ rt Y (dπl ρV Y u) := by
  apply Φs_injective ρV δ hrt Y
  rw [Φs_hlift ρV δ hrt]
  show (dπl ρV Y u, hz ρV δ rt Y u) = _
  rw [(hz_eq_zero_iff ρV δ rt Y u).2 hu]

variable (rt)

/-- **The quotient metric on `V`**: `g_B(Y)(c, c') = G_{(Y,1)}(h c, h c')`. -/
def gB (Y : V) : V →L[ℝ] V →L[ℝ] ℝ := bil (Gs δ rt Y) (hlift ρV δ rt Y)

variable {rt}

theorem gB_symm (Y c c' : V) : gB ρV δ rt Y c c' = gB ρV δ rt Y c' c := Gs_symm δ rt Y _ _

theorem gB_pos (hrt : ∀ Y, rt Y ≠ 0) (Y : V) {c : V} (hc : c ≠ 0) : 0 < gB ρV δ rt Y c c := by
  refine Gs_pos δ hrt Y fun h => hc ?_
  rw [← dπl_hlift ρV δ hrt Y c]
  exact (congrArg (dπl ρV Y) h).trans (map_zero _)

theorem contDiff_Φs (hrt : ContDiff ℝ ∞ rt) : ContDiff ℝ ∞ (Φs ρV δ rt) := by
  rw [contDiff_clm_apply_iff]
  intro u
  have hK : ∀ β : E3, ContDiff ℝ ∞ fun Y : V => KY ρV Y β := fun β =>
    (dρ ρV β).contDiff
  refine ContDiff.prodMk ?_ ?_
  · exact contDiff_const.sub (hK u.2)
  · have e : (fun Y => hz ρV δ rt Y u) =
        fun Y => ∑ i : Fin 3, Gs δ rt Y u (ιv ρV Y (bE i)) • bE i :=
      funext fun Y => hz_apply ρV δ rt Y u
    show ContDiff ℝ ∞ fun Y => hz ρV δ rt Y u
    rw [e]
    refine ContDiff.sum fun i _ => ?_
    have h := contDiff_Gs_apply δ hrt (contDiff_const (c := u))
      ((hK (bE i)).prodMk (contDiff_const (c := (bE i : E3))))
    exact h.smul contDiff_const

theorem contDiff_hlift_apply (hrt0 : ∀ Y, rt Y ≠ 0) (hrt : ContDiff ℝ ∞ rt) (c : V) :
    ContDiff ℝ ∞ fun Y => hlift ρV δ rt Y c := by
  have hinv : ContDiff ℝ ∞ fun Y => ContinuousLinearMap.inverse (Φs ρV δ rt Y) := by
    rw [contDiff_iff_contDiffAt]
    intro Y
    exact (isInvertible_Φs ρV δ hrt0 Y).contDiffAt_map_inverse.comp Y
      (contDiff_Φs ρV δ hrt).contDiffAt
  exact hinv.clm_apply contDiff_const

theorem contDiff_gB (hrt0 : ∀ Y, rt Y ≠ 0) (hrt : ContDiff ℝ ∞ rt) :
    ContDiff ℝ ∞ (gB ρV δ rt) := by
  rw [contDiff_clm_apply_iff]
  intro c
  rw [contDiff_clm_apply_iff]
  intro c'
  exact contDiff_Gs_apply δ hrt (contDiff_hlift_apply ρV δ hrt0 hrt c)
    (contDiff_hlift_apply ρV δ hrt0 hrt c')

end Lift

end

end ExoticSpheres8And10
