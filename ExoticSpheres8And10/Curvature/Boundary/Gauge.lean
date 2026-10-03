/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Geometry.NaturalityLocal

/-! # §4.4: near the gluing boundary the southern metric is a warped product (gauge)

Where the cutoff vanishes (`χ = 0`, near `t = a`), [D]'s southern potential is the pure gauge
`A_S = −dθ̂ θ̂⁻¹`. For fixed `q₀ ∈ S³` the map

  `Λ_{q₀}(y, u) = (ρ(q₀) y, q₀ θ̂(y) u)`

is then a local isometry from the product-connection metric `GW(ψR⟪,⟫, r_S)` to
`G_S = GH(A_S, r_S)`: `θL_A(dΛ u) = q₀θ̂ · dU(u)` (`Λ_isometry`). Also
`π ∘ Λ_{q₀} = τ ∘ π`, where `τ(y) = ρ(θ̂(y)⁻¹) y` (`π_Λ`).

* `θS`: `θ̂` as an `S³`-valued map; `τ`, `σh` with `τ ∘ σh = σh ∘ τ = id`; `norm_τ`.
-/

open RiemannianGeometry Bundle VectorField

namespace ExoticSpheres8And10

open Set Function Filter Topology Real Module

open scoped Manifold ContDiff RealInnerProductSpace

set_option maxSynthPendingDepth 3

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Gauge

variable {m : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] {e : W} [Fact (finrank ℝ (Vs e) = m + 1)]
  (D : PolarData (m := m) e)

namespace PolarData

open scoped Classical in
/-- `θ̂` with values in `S³` (and `1` at the south pole, where it is never used). -/
def θS (y : Vs e) : S3 := if h : y = 0 then 1 else D.θ (nrmV ⟨y, h⟩)

theorem coe_θS (y : Vs e) : ((D.θS y : S3) : Quaternion ℝ) = D.θh y := by
  classical
  by_cases hy : y = 0
  · simp [θS, hy, D.θh_zero]
  · simp [θS, hy, D.θh_of_ne hy]

theorem θS_ρ (q : S3) (y : Vs e) : D.θS (D.ρVs q y) = q * D.θS y * q⁻¹ := by
  apply Subtype.ext
  rw [coe_θS, D.θh_ρ]
  simp [coe_θS, coe_inv_S3']

/-- `τ(y) = ρ(θ̂(y)⁻¹) y`: the change of quotient slice between the two trivialisations. -/
def τ (y : Vs e) : Vs e := D.ρVs (D.θS y)⁻¹ y

/-- `σ̂(y) = ρ(θ̂(y)) y`, the inverse of `τ`. -/
def σh (y : Vs e) : Vs e := D.ρVs (D.θS y) y

theorem norm_τ (y : Vs e) : ‖D.τ y‖ = ‖y‖ := LinearIsometryEquiv.norm_map _ _

theorem θS_τ (y : Vs e) : D.θS (D.τ y) = D.θS y := by
  rw [τ, θS_ρ]; group

theorem θS_σh (y : Vs e) : D.θS (D.σh y) = D.θS y := by
  rw [σh, θS_ρ]; group

theorem ρVs_mul_apply (a b : S3) (y : Vs e) : D.ρVs a (D.ρVs b y) = D.ρVs (a * b) y := by
  rw [show D.ρVs a (D.ρVs b y) = (D.ρVs a * D.ρVs b) y from rfl, ← map_mul]

theorem σh_τ (y : Vs e) : D.σh (D.τ y) = y := by
  rw [σh, θS_τ, τ, ρVs_mul_apply, mul_inv_cancel, map_one]; rfl

theorem τ_σh (y : Vs e) : D.τ (D.σh y) = y := by
  rw [τ, θS_σh, σh, ρVs_mul_apply, inv_mul_cancel, map_one]; rfl

theorem τ_ρ (q : S3) (y : Vs e) : D.τ (D.ρVs q y) = D.ρVs q (D.τ y) := by
  rw [τ, τ, θS_ρ, ρVs_mul_apply, ρVs_mul_apply]
  congr 1
  group

/-- `Λ_{q₀}(y, u) = (ρ(q₀)y, q₀ θ̂(y) u)`. -/
def Λ (q₀ : S3) (p : Vs e × S3) : Vs e × S3 := (D.ρVs q₀ p.1, q₀ * D.θS p.1 * p.2)

theorem π_Λ (q₀ : S3) (p : Vs e × S3) : πN D.ρVs (D.Λ q₀ p) = D.τ (πN D.ρVs p) := by
  simp only [πN, Λ]
  rw [τ_ρ, τ, ρVs_mul_apply, ρVs_mul_apply]
  congr 1
  group

theorem Λ_slice (y : Vs e) : D.Λ (D.θS y)⁻¹ (y, 1) = (D.τ y, 1) := by
  simp only [Λ, mul_one, inv_mul_cancel]; rfl

end PolarData

end Gauge

section QuatMul

variable {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] {H₀ : Type*} [TopologicalSpace H₀]
  {I₀ : ModelWithCorners ℝ E₀ H₀} {N : Type*} [TopologicalSpace N] [ChartedSpace H₀ N]

/-- The product rule for quaternion-valued functions on a manifold. -/
theorem mvfderiv_mul_quat {f g : N → Quaternion ℝ} {x : N}
    (hf : MDifferentiableAt I₀ 𝓘(ℝ, Quaternion ℝ) f x)
    (hg : MDifferentiableAt I₀ 𝓘(ℝ, Quaternion ℝ) g x) (v : TangentSpace I₀ x) :
    mvfderiv I₀ (fun y => f y * g y) x v =
      mvfderiv I₀ f x v * g x + f x * mvfderiv I₀ g x v := by
  have hm := hf.hasMFDerivAt.mul' hg.hasMFDerivAt
  have h2 : mvfderiv I₀ (fun y => f y * g y) x =
      f x • mvfderiv I₀ g x + MulOpposite.op (g x) • mvfderiv I₀ f x := by
    unfold mvfderiv
    rw [show (fun y => f y * g y) = f * g from rfl, hm.mfderiv]
    exact ContinuousLinearMap.ext fun w => rfl
  rw [h2]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    op_smul_eq_mul]
  rw [add_comm]

end QuatMul

section FYFU

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem mdiffAt_fY (p : V × S3) : MDifferentiableAt (IN V) 𝓘(ℝ, V) fY p :=
  (contMDiff_fY p).mdifferentiableAt (by simp)

theorem mdiffAt_fU (p : V × S3) : MDifferentiableAt (IN V) 𝓘(ℝ, Quaternion ℝ) fU p :=
  (contMDiff_fU p).mdifferentiableAt (by simp)

end FYFU

section SphereLocal

variable {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] {H₀ : Type*} [TopologicalSpace H₀]
  {I₀ : ModelWithCorners ℝ E₀ H₀} {N : Type*} [TopologicalSpace N] [ChartedSpace H₀ N]
  [IsManifold I₀ ∞ N]

/-- A sphere-valued map is smooth at `x` if its ambient values are smooth on an open set
around `x`. -/
theorem contMDiffAt_sphere_of_coe_loc {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {k : ℕ} [Fact (finrank ℝ F = k + 1)] {f : N → Metric.sphere (0 : F) 1} (U : TopologicalSpace.Opens N)
    {x : N} (hx : x ∈ U) (h : ContMDiffOn I₀ 𝓘(ℝ, F) ∞ (fun y => (f y : F)) U) :
    ContMDiffAt I₀ (𝓡 k) ∞ f x := by
  have hg : ContMDiff I₀ (𝓡 k) ∞ fun y : U => f y := by
    refine contMDiff_sphere_of_coe fun y => ?_
    exact contMDiffAt_subtype_iff.2 ((h y y.2).contMDiffAt (U.isOpen.mem_nhds y.2))
  exact contMDiffAt_subtype_iff.1 (hg ⟨x, hx⟩)

end SphereLocal

section LambdaSmooth

variable {m : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] {e : W} [Fact (finrank ℝ (Vs e) = m + 1)]
  (D : PolarData (m := m) e)

namespace PolarData

/-- The punctured source `(V ∖ {0}) × S³`. -/
def Upunct (e : W) : TopologicalSpace.Opens (Vs e × S3) :=
  ⟨{p | p.1 ≠ 0}, isOpen_ne_fun continuous_fst continuous_const⟩

theorem coe_Λ2 (q₀ : S3) (p : Vs e × S3) :
    (((D.Λ q₀ p).2 : S3) : Quaternion ℝ) = (q₀ : Quaternion ℝ) * D.θh p.1 * (p.2 : Quaternion ℝ) := by
  show ((q₀ * D.θS p.1 * p.2 : S3) : Quaternion ℝ) = _
  rw [show ((q₀ * D.θS p.1 * p.2 : S3) : Quaternion ℝ) =
    (q₀ : Quaternion ℝ) * (D.θS p.1 : Quaternion ℝ) * (p.2 : Quaternion ℝ) from rfl, coe_θS]

theorem contMDiffAt_θh_fst {p : Vs e × S3} (hp : p.1 ≠ 0) :
    ContMDiffAt (IN (Vs e)) 𝓘(ℝ, Quaternion ℝ) ∞ (fun p : Vs e × S3 => D.θh p.1) p :=
  (D.contDiffAt_θh hp).contMDiffAt.comp p (contMDiff_fY p)

theorem contMDiffAt_Λ (q₀ : S3) {p : Vs e × S3} (hp : p.1 ≠ 0) :
    ContMDiffAt (IN (Vs e)) (IN (Vs e)) ∞ (D.Λ q₀) p := by
  refine ContMDiffAt.prodMk ?_ ?_
  · exact ((((D.ρVs q₀ : Vs e ≃L[ℝ] Vs e) : Vs e →L[ℝ] Vs e).contDiff.contMDiff).comp
      contMDiff_fY) p
  · refine contMDiffAt_sphere_of_coe_loc (f := fun p' => (D.Λ q₀ p').2) (Upunct e) hp
      fun p' hp' => ?_
    have e1 : (fun p' : Vs e × S3 => (((D.Λ q₀ p').2 : S3) : Quaternion ℝ)) = fun p' =>
        (q₀ : Quaternion ℝ) * D.θh p'.1 * (p'.2 : Quaternion ℝ) := funext (D.coe_Λ2 q₀)
    rw [e1]
    have h1 : ContMDiffAt (IN (Vs e)) 𝓘(ℝ, Quaternion ℝ) ∞
        (fun p : Vs e × S3 => (q₀ : Quaternion ℝ) * D.θh p.1) p' :=
      contDiff_mul.comp_contMDiffAt (contMDiffAt_const.prodMk_space (D.contMDiffAt_θh_fst hp'))
    exact (contDiff_mul.comp_contMDiffAt (h1.prodMk_space (contMDiff_fU p'))).contMDiffWithinAt

theorem mvfderiv_fY_Λ (q₀ : S3) {p : Vs e × S3} (hp : p.1 ≠ 0) (v : TangentSpace (IN (Vs e)) p) :
    mvfderiv (IN (Vs e)) fY (D.Λ q₀ p) (mfderiv (IN (Vs e)) (IN (Vs e)) (D.Λ q₀) p v) =
      D.ρVs q₀ (mvfderiv (IN (Vs e)) fY p v) := by
  have hΛ := (D.contMDiffAt_Λ q₀ hp).mdifferentiableAt (by simp)
  have eY : fY ∘ D.Λ q₀ = ((D.ρVs q₀ : Vs e ≃L[ℝ] Vs e) : Vs e →L[ℝ] Vs e) ∘ fY := rfl
  rw [← mvfderiv_comp' ((contMDiff_fY _).mdifferentiableAt (by simp)) hΛ, eY,
    mvfderiv_clm_comp _ ((contMDiff_fY p).mdifferentiableAt (by simp))]
  rfl

theorem mvfderiv_fU_Λ (q₀ : S3) {p : Vs e × S3} (hp : p.1 ≠ 0) (v : TangentSpace (IN (Vs e)) p) :
    mvfderiv (IN (Vs e)) fU (D.Λ q₀ p) (mfderiv (IN (Vs e)) (IN (Vs e)) (D.Λ q₀) p v) =
      (q₀ : Quaternion ℝ) * fderiv ℝ D.θh p.1 (mvfderiv (IN (Vs e)) fY p v) * (p.2 : Quaternion ℝ) +
        (q₀ : Quaternion ℝ) * D.θh p.1 * mvfderiv (IN (Vs e)) fU p v := by
  have hΛ := (D.contMDiffAt_Λ q₀ hp).mdifferentiableAt (by simp)
  rw [← mvfderiv_comp' ((contMDiff_fU _).mdifferentiableAt (by simp)) hΛ]
  have hfe : fU ∘ D.Λ q₀ = fun p' : Vs e × S3 =>
      ((q₀ : Quaternion ℝ) * D.θh p'.1) * fU p' := funext fun p' => D.coe_Λ2 q₀ p'
  rw [hfe]
  have hθ := (D.contDiffAt_θh hp).differentiableAt (by simp)
  have hθq := hθ.const_mul (q₀ : Quaternion ℝ)
  rw [mvfderiv_mul_quat (f := fun p' : Vs e × S3 => (q₀ : Quaternion ℝ) * D.θh p'.1) (g := fU)
    (hθq.hasFDerivAt.hasMFDerivAt.mdifferentiableAt.comp p (mdiffAt_fY p)) (mdiffAt_fU p) v]
  rw [show (fun p' : Vs e × S3 => (q₀ : Quaternion ℝ) * D.θh p'.1) =
    (fun y : Vs e => (q₀ : Quaternion ℝ) * D.θh y) ∘ fY from rfl]
  rw [mvfderiv_comp' (g := fun y : Vs e => (q₀ : Quaternion ℝ) * D.θh y) (f := fY)
    hθq.hasFDerivAt.hasMFDerivAt.mdifferentiableAt (mdiffAt_fY p),
    mvfderiv_vs, show fY p = p.1 from rfl, fderiv_const_mul hθ]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, fU]
  rw [mul_assoc]
  rfl

/-- **Where `χ = 0`, `Λ_{q₀}` is a local isometry** from the product-connection metric to
[D]'s southern metric: `θL_A(dΛ u) = q₀θ̂·dU(u)`. -/
theorem Λ_isometry {χt : ℝ → ℝ} (hχ : IsSouthCutoff χt) {r : Vs e → ℝ}
    (hrρ : ∀ q y, r (D.ρVs q y) = r y) (q₀ : S3) {p : Vs e × S3} (hp : p.1 ≠ 0)
    (hχ0 : χt (‖p.1‖ ^ 2) = 0) (v v' : TangentSpace (IN (Vs e)) p) :
    GH (D.AS χt) r (D.Λ q₀ p) (mfderiv (IN (Vs e)) (IN (Vs e)) (D.Λ q₀) p v)
      (mfderiv (IN (Vs e)) (IN (Vs e)) (D.Λ q₀) p v') =
      GW (fun y => ψR y • ipL (Vs e)) r p v v' := by
  have hq : (q₀ : Quaternion ℝ) ≠ 0 := fun h => by
    have := mem_sphere_zero_iff_norm.1 q₀.2; rw [h, norm_zero] at this; norm_num at this
  have hθ0 := D.θh_ne_zero p.1
  have hθL : ∀ u : TangentSpace (IN (Vs e)) p,
      θL (D.AS χt) (D.Λ q₀ p) (mfderiv (IN (Vs e)) (IN (Vs e)) (D.Λ q₀) p u) =
        ((q₀ * D.θS p.1 : S3) : Quaternion ℝ) * mvfderiv (IN (Vs e)) fU p u := fun u => by
    rw [θL_apply, mvfderiv_fY_Λ D q₀ hp, mvfderiv_fU_Λ D q₀ hp, D.coe_Λ2,
      show (D.Λ q₀ p).1 = D.ρVs q₀ p.1 from rfl, D.AS_equiv hχ, AS_apply, hχ0,
      show ((q₀ * D.θS p.1 : S3) : Quaternion ℝ) = (q₀ : Quaternion ℝ) * D.θh p.1 by
        rw [show ((q₀ * D.θS p.1 : S3) : Quaternion ℝ) =
          (q₀ : Quaternion ℝ) * (D.θS p.1 : Quaternion ℝ) from rfl, coe_θS]]
    set a := fderiv ℝ D.θh p.1 (mvfderiv (IN (Vs e)) fY p u)
    set t := D.θh p.1
    set x := (p.2 : Quaternion ℝ)
    set q := (q₀ : Quaternion ℝ)
    simp only [zero_sub, neg_one_smul]
    have h1 : q * -(a * t⁻¹) * q⁻¹ * (q * t * x) = -(q * a * x) := by
      simp only [mul_assoc, neg_mul, mul_neg, inv_mul_cancel_left₀ hq, inv_mul_cancel_left₀ hθ0]
    rw [h1]
    abel
  rw [GH_apply, GW_apply, hθL, hθL, inner_mul_left_unit, mvfderiv_fY_Λ D q₀ hp,
    mvfderiv_fY_Λ D q₀ hp, show (D.Λ q₀ p).1 = D.ρVs q₀ p.1 from rfl,
    LinearIsometryEquiv.inner_map_map, ψR_ρ, hrρ]
  simp only [ContinuousLinearMap.smul_apply, ipL_apply, smul_eq_mul]

theorem contMDiffAt_θS {y : Vs e} (hy : y ≠ 0) :
    ContMDiffAt 𝓘(ℝ, Vs e) (𝓡 3) ∞ D.θS y := by
  refine contMDiffAt_sphere_of_coe_loc (f := D.θS) (Vpunct e) hy fun y' hy' => ?_
  have e1 : (fun y' => ((D.θS y' : S3) : Quaternion ℝ)) = D.θh := funext D.coe_θS
  rw [e1]
  exact (D.contDiffAt_θh hy').contMDiffAt.contMDiffWithinAt

theorem contDiffAt_τ {y : Vs e} (hy : y ≠ 0) : ContDiffAt ℝ ∞ D.τ y := by
  have h1 : ContMDiffAt 𝓘(ℝ, Vs e) 𝓘(ℝ, Vs e →L[ℝ] Vs e) ∞
      (fun y' => ((D.ρVs (D.θS y')⁻¹ : Vs e ≃L[ℝ] Vs e) : Vs e →L[ℝ] Vs e)) y :=
    (D.contMDiff_ρVs ((D.θS y)⁻¹)).comp y ((contMDiff_invS3 (D.θS y)).comp y (D.contMDiffAt_θS hy))
  have h2 := (contMDiffAt_iff_contDiffAt.1 h1).clm_apply contDiffAt_id
  exact h2

end PolarData

end LambdaSmooth

end

end ExoticSpheres8And10
