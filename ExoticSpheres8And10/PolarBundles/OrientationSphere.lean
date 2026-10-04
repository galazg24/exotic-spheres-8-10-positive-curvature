/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.PolarBundles.OrientationDerivative

/-! # A3/A2 for `ρ₈`: `σ` on the sphere, its smoothness, and the orientation convention

[GG] `lem:attaching`: "The map `σ` is a diffeomorphism of `S^{n−1}` with inverse `σ̂` [...]
`Dσ_y = ρ(θ(y)⁻¹)(Id − K_yβ_y)` [...] The first factor preserves the ambient orientation and sends
the normal `y` to `σ(y)`, so `σ` preserves the standard sphere orientation."

With the ambient Euclidean inner product `dot2` on `ℍ × ℍ` (the metric of `S⁷ ⊂ ℍ²`):

* `rho8_dot`, `sigma8_norm`: `ρ₈(q)` is orthogonal for unit `q`, so `σ` maps `S⁷` to `S⁷`;
* `contDiff_sigma8`: `σ` (and `σ̂`) is `C^∞` where `θ` is `C^∞` and nonzero (ambient smoothness);
* `K8_dot_self`: `K_yη ⊥ y` for imaginary `η` (action fields are tangent);
* `dtheta_radial_zero`: `dθ_y(y) = 0` for `0`-homogeneous `θ`;
* `Dsigma8_normal`, `Dsigma8_tangent`: the ambient map `A = ρ₈(θ⁻¹)∘(Id − Kβ)` sends the normal
  `y` to `σ(y)` and `T_yS⁷ = y^⊥` into `σ(y)^⊥ = T_{σ(y)}S⁷`.

Together with `det_Dsigma8_ambient` (`det A = 1`) this is [GG]'s orientation argument: the sphere
orientation at `y` is the one for which `(y, positive basis of T_y)` is positive in `ℍ²`, so `A`
restricts to an orientation-preserving map `T_y → T_{σ(y)}` exactly when `det A > 0`.
-/

namespace ExoticSpheres8And10

open Quaternion

open scoped RealInnerProductSpace

/-- The Euclidean inner product on `ℍ × ℍ`. -/
noncomputable def dot2 (y z : ℍ[ℝ] × ℍ[ℝ]) : ℝ := ⟪y.1, z.1⟫ + ⟪y.2, z.2⟫

/-! ## Orthogonality of `ρ₈` -/

theorem inner_of_norm_pres {f : ℍ[ℝ] → ℍ[ℝ]} (hadd : ∀ a b, f (a + b) = f a + f b)
    (hn : ∀ a, ‖f a‖ = ‖a‖) (a b : ℍ[ℝ]) : ⟪f a, f b⟫ = ⟪a, b⟫ := by
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two, ← hadd, hn, hn,
    hn]

theorem rho8_dot (q : ℍ[ℝ]) (hq : ‖q‖ = 1) (y z : ℍ[ℝ] × ℍ[ℝ]) :
    dot2 (rho8 q y) (rho8 q z) = dot2 y z := by
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  simp only [dot2, rho8]
  rw [inner_of_norm_pres (f := fun a => q * a) (fun a b => mul_add q a b)
      (fun a => by rw [norm_mul, hq, one_mul]),
    inner_of_norm_pres (f := fun a => q * a * q⁻¹) (fun a b => by simp [mul_add, add_mul])
      (fun a => by rw [norm_mul, norm_mul, norm_inv, hq, inv_one, one_mul, mul_one])]

/-- `σ` maps `S⁷` to `S⁷`: `‖σ(y)‖ = ‖y‖` for the ambient norm. -/
theorem sigma8_norm (θy : ℍ[ℝ]) (hθ : ‖θy‖ = 1) (y : ℍ[ℝ] × ℍ[ℝ]) :
    dot2 (rho8 θy⁻¹ y) (rho8 θy⁻¹ y) = dot2 y y :=
  rho8_dot θy⁻¹ (by rw [norm_inv, hθ, inv_one]) y y

/-! ## Smoothness of `σ` and `σ̂` (ambient) -/

theorem contDiffAt_quat_inv {x : ℍ[ℝ]} (hx : x ≠ 0) {n : ℕ∞} :
    ContDiffAt ℝ n (fun q : ℍ[ℝ] => q⁻¹) x := by
  have h := contDiffAt_ringInverse ℝ (Units.mk0 x hx) (n := n)
  rw [Units.val_mk0, Ring.inverse_eq_inv'] at h
  exact h

/-- **`σ(y) = (θ(y)⁻¹x, θ(y)⁻¹wθ(y))` is `C^n`** at every point where `θ` is `C^n` and nonzero. -/
theorem contDiffAt_sigma8 {n : ℕ∞} (θ : ℍ[ℝ] × ℍ[ℝ] → ℍ[ℝ]) (y : ℍ[ℝ] × ℍ[ℝ])
    (hθ : ContDiffAt ℝ n θ y) (hne : θ y ≠ 0) :
    ContDiffAt ℝ n (fun z : ℍ[ℝ] × ℍ[ℝ] => ((θ z)⁻¹ * z.1, (θ z)⁻¹ * z.2 * θ z)) y := by
  have hinv : ContDiffAt ℝ n (fun z => (θ z)⁻¹) y := (contDiffAt_quat_inv hne).comp y hθ
  exact (hinv.mul contDiffAt_fst).prodMk ((hinv.mul contDiffAt_snd).mul hθ)

/-- **`σ̂(y) = (θ(y)x, θ(y)wθ(y)⁻¹)` is `C^n`** likewise. -/
theorem contDiffAt_sigmaHat8 {n : ℕ∞} (θ : ℍ[ℝ] × ℍ[ℝ] → ℍ[ℝ]) (y : ℍ[ℝ] × ℍ[ℝ])
    (hθ : ContDiffAt ℝ n θ y) (hne : θ y ≠ 0) :
    ContDiffAt ℝ n (fun z : ℍ[ℝ] × ℍ[ℝ] => (θ z * z.1, θ z * z.2 * (θ z)⁻¹)) y := by
  have hinv : ContDiffAt ℝ n (fun z => (θ z)⁻¹) y := (contDiffAt_quat_inv hne).comp y hθ
  exact (hθ.mul contDiffAt_fst).prodMk ((hθ.mul contDiffAt_snd).mul hinv)

/-! ## Tangency of the action fields and radial derivative of `θ` -/

/-- `K_yη ⊥ y` for imaginary `η`. -/
theorem K8_dot_self (y : ℍ[ℝ] × ℍ[ℝ]) (η : ℍ[ℝ]) (hη : η.re = 0) : dot2 (K8 y η) y = 0 := by
  simp only [dot2, K8, Quaternion.inner_def, Quaternion.re_mul, Quaternion.re_sub,
    Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.imI_sub,
    Quaternion.imJ_sub, Quaternion.imK_sub, Quaternion.re_star, Quaternion.imI_star,
    Quaternion.imJ_star, Quaternion.imK_star, hη]
  ring

/-- `dθ_y(y) = 0` when `θ` is `0`-homogeneous (`θ(ty) = θ(y)` for `t > 0`), e.g. the radial
extension of [GG]'s `θ : S^{n−1} → S³`. -/
theorem dtheta_radial_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (θ : E → ℍ[ℝ]) (Dθ : E →L[ℝ] ℍ[ℝ]) (y : E) (hθ : HasFDerivAt θ Dθ y)
    (hhom : ∀ t : ℝ, 0 < t → θ (t • y) = θ y) : Dθ y = 0 := by
  have hcurve : HasDerivAt (fun t : ℝ => t • y) y 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const y
  have h1 : HasDerivAt (fun t : ℝ => θ (t • y)) (Dθ y) 1 := by
    have := hθ
    rw [show y = (1 : ℝ) • y by simp] at this
    exact this.comp_hasDerivAt (x := (1 : ℝ)) hcurve
  have h2 : HasDerivAt (fun t : ℝ => θ (t • y)) 0 1 := by
    apply (hasDerivAt_const (1 : ℝ) (θ y)).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact hhom t ht
  exact h1.unique h2

/-! ## The ambient map sends the normal to the normal and tangent spaces to tangent spaces -/

/-- `K_y` for `ρ₈` as a linear map on `Im ℍ` in coordinates. -/
noncomputable def K8lin (y : ℍ[ℝ] × ℍ[ℝ]) : (Fin 3 → ℝ) →ₗ[ℝ] (ℍ[ℝ] × ℍ[ℝ]) where
  toFun v := K8 y (imEmb v)
  map_add' v w := by
    refine Prod.ext ?_ ?_ <;> (ext <;> simp [K8, imEmb, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring)
  map_smul' c v := by
    refine Prod.ext ?_ ?_ <;> (ext <;> simp [K8, imEmb, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_smul] <;> ring)

/-- **The normal goes to the normal.** If `dθ_y(y) = 0` then `A y = σ(y)`. -/
theorem Dsigma8_normal (Dθ : (ℍ[ℝ] × ℍ[ℝ]) →L[ℝ] ℍ[ℝ]) (θy : ℍ[ℝ]) (y : ℍ[ℝ] × ℍ[ℝ])
    (hrad : Dθ y = 0) :
    (rho8Lin θy⁻¹ ∘ₗ (LinearMap.id - K8lin y ∘ₗ betaCoord Dθ θy)) y = rho8 θy⁻¹ y := by
  have hb : betaCoord Dθ θy y = 0 := by
    funext i; fin_cases i <;> simp [betaCoord, hrad]
  simp [hb, rho8Lin_apply]

/-- **Tangent spaces go to tangent spaces.** For `v ⊥ y`, `A v ⊥ A y = σ(y)`. -/
theorem Dsigma8_tangent (Dθ : (ℍ[ℝ] × ℍ[ℝ]) →L[ℝ] ℍ[ℝ]) (θy : ℍ[ℝ]) (hθ : ‖θy‖ = 1)
    (y : ℍ[ℝ] × ℍ[ℝ]) (hrad : Dθ y = 0) (v : ℍ[ℝ] × ℍ[ℝ]) (hv : dot2 v y = 0) :
    dot2 ((rho8Lin θy⁻¹ ∘ₗ (LinearMap.id - K8lin y ∘ₗ betaCoord Dθ θy)) v)
      ((rho8Lin θy⁻¹ ∘ₗ (LinearMap.id - K8lin y ∘ₗ betaCoord Dθ θy)) y) = 0 := by
  rw [Dsigma8_normal Dθ θy y hrad]
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, rho8Lin_apply]
  rw [rho8_dot θy⁻¹ (by rw [norm_inv, hθ, inv_one])]
  have hK := K8_dot_self y (imEmb (betaCoord Dθ θy v)) rfl
  simp only [K8lin, LinearMap.coe_mk, AddHom.coe_mk] at *
  simp only [dot2, Prod.fst_sub, Prod.snd_sub, inner_sub_left] at hv hK ⊢
  linarith

/-! ### Non-vacuity -/

example : dot2 (K8 (qmk 0 1 0 0, qmk 0 0 1 0) (qmk 0 0 0 1)) (qmk 0 1 0 0, qmk 0 0 1 0) = 0 :=
  K8_dot_self _ _ rfl

/-- `θ ≡ 1` is `0`-homogeneous, so `dtheta_radial_zero` fires. -/
example (y : ℍ[ℝ] × ℍ[ℝ]) : (0 : (ℍ[ℝ] × ℍ[ℝ]) →L[ℝ] ℍ[ℝ]) y = 0 :=
  dtheta_radial_zero (fun _ => 1) 0 y (hasFDerivAt_const _ _) (fun _ _ => rfl)

end ExoticSpheres8And10
