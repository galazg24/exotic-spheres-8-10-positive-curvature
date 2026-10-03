/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Curvature.Prop31.Bundle.Frame

/-! # Principal `S³`-bundles: the bracket table of the connection-metric frame

Helpers:
* `mvfderiv_mul_apply`: the product rule for `ℍ`-valued functions on a manifold;
* `mvfderiv_mlieBracket_quat`: the derivation identity `X(Yg) − Y(Xg) = [X,Y]g` for `ℍ`-valued
  `g`, from `RiemannianGeometry`'s scalar identity applied to the four coordinate functionals.
-/

open RiemannianGeometry VectorField Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Module

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Helpers

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [FiniteDimensional ℝ E'] {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold J ∞ M]

/-- **The product rule** for `ℍ`-valued functions. -/
theorem mvfderiv_mul_apply {p q : M → Quaternion ℝ} {z : M} (hp : MDifferentiableAt J 𝓘(ℝ, Quaternion ℝ) p z)
    (hq : MDifferentiableAt J 𝓘(ℝ, Quaternion ℝ) q z) (v : TangentSpace J z) :
    mvfderiv J (fun x => p x * q x) z v = p z * mvfderiv J q z v + mvfderiv J p z v * q z := by
  have h := (hp.hasMFDerivAt.mul' hq.hasMFDerivAt).mfderiv
  have h' := congrArg (fun L => L v) h
  exact h'

/-- The coordinate test: quaternions agreeing against `1, i, j, k` are equal. -/
theorem quat_ext_inner {x y : Quaternion ℝ} (h1 : ⟪(1 : Quaternion ℝ), x⟫ = ⟪(1 : Quaternion ℝ), y⟫)
    (hI : ⟪qI, x⟫ = ⟪qI, y⟫) (hJ : ⟪qJ, x⟫ = ⟪qJ, y⟫) (hK : ⟪qK, x⟫ = ⟪qK, y⟫) : x = y := by
  simp only [inner_quat] at h1 hI hJ hK
  simp only [Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
    one_mul, zero_mul, add_zero] at h1
  simp at hI hJ hK
  ext <;> assumption

/-- **The derivation identity for `ℍ`-valued functions.** -/
theorem mvfderiv_mlieBracket_quat {g : M → Quaternion ℝ} {X Y : Π y : M, TangentSpace J y} {x : M}
    (hg : ContMDiffAt J 𝓘(ℝ, Quaternion ℝ) ((2 : ℕ∞) : ℕ∞ω) g x)
    (hX : ∀ᶠ y in 𝓝 x, ContMDiffAt J J.tangent ((2 : ℕ∞) : ℕ∞ω) (T% X) y)
    (hY : ∀ᶠ y in 𝓝 x, ContMDiffAt J J.tangent ((2 : ℕ∞) : ℕ∞ω) (T% Y) y) :
    mvfderiv J (fun y => mvfderiv J g y (Y y)) x (X x) -
        mvfderiv J (fun y => mvfderiv J g y (X y)) x (Y x) =
      mvfderiv J g x (mlieBracket J X Y x) := by
  have hn : minSmoothness ℝ 2 ≤ (2 : ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]; norm_num
  have hn' : ((2 : ℕ∞) : ℕ∞ω) ≠ ∞ := by simp
  have h2 : ((2 : ℕ∞) : ℕ∞ω) ≠ 0 := by simp
  have h1 : (1 : ℕ∞ω) ≤ ((2 : ℕ∞) : ℕ∞ω) := by exact_mod_cast (by norm_num : (1 : ℕ∞) ≤ 2)
  have key : ∀ w : Quaternion ℝ,
      ⟪w, mvfderiv J (fun y => mvfderiv J g y (Y y)) x (X x) -
        mvfderiv J (fun y => mvfderiv J g y (X y)) x (Y x)⟫ =
      ⟪w, mvfderiv J g x (mlieBracket J X Y x)⟫ := by
    intro w
    set L : Quaternion ℝ →L[ℝ] ℝ := innerSL ℝ w
    have hLg : ContMDiffAt J 𝓘(ℝ, ℝ) ((2 : ℕ∞) : ℕ∞ω) (L ∘ g) x :=
      L.contMDiff.contMDiffAt.comp x hg
    have hid := mvfderiv_apply_mlieBracket_of_contMDiffAt (I := J) (g := L ∘ g) (X := X) (Y := Y)
      (x := x) hn hn' hLg hX hY
    have hgd : ∀ᶠ y in 𝓝 x, MDifferentiableAt J 𝓘(ℝ, Quaternion ℝ) g y :=
      ((contMDiffAt_iff_contMDiffAt_nhds hn').1 hg).mono fun _ hy => hy.mdifferentiableAt h2
    have hcomp : ∀ (Z : Π y : M, TangentSpace J y),
        (fun y => mvfderiv J (L ∘ g) y (Z y)) =ᶠ[𝓝 x] L ∘ fun y => mvfderiv J g y (Z y) := by
      intro Z
      filter_upwards [hgd] with y hy using mvfderiv_clm_comp L hy (Z y)
    have hYd : MDifferentiableAt J 𝓘(ℝ, Quaternion ℝ) (fun y => mvfderiv J g y (Y y)) x :=
      mdifferentiableAt_mvfderiv_apply_of_contMDiffAt hg (le_refl _) hn'
        (hY.self_of_nhds.of_le h1)
    have hXd : MDifferentiableAt J 𝓘(ℝ, Quaternion ℝ) (fun y => mvfderiv J g y (X y)) x :=
      mdifferentiableAt_mvfderiv_apply_of_contMDiffAt hg (le_refl _) hn'
        (hX.self_of_nhds.of_le h1)
    rw [mvfderiv_congr_of_eventuallyEq (hcomp Y), mvfderiv_congr_of_eventuallyEq (hcomp X),
      mvfderiv_clm_comp L hYd, mvfderiv_clm_comp L hXd,
      mvfderiv_clm_comp L hgd.self_of_nhds] at hid
    rw [inner_sub_right]
    exact hid
  exact quat_ext_inner (key 1) (key qI) (key qJ) (key qK)

end Helpers

section Tests

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type} [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B]
  {P : Type} [TopologicalSpace P] [ChartedSpace (ModelProd H E3) P] [IsManifold (I.prod (𝓡 3)) ∞ P]
  {Pb : PrincipalS3Bundle I B P} (C : S3Connection Pb)

namespace S3Connection

include C in
/-- **Tangent vectors are determined by `dπ` and `du`.** -/
theorem eq_of_tests (b₀ : B) {p : P} (hp : Pb.proj p ∈ Pb.nbhd b₀)
    {v w : TangentSpace (I.prod (𝓡 3)) p}
    (h1 : mfderiv (I.prod (𝓡 3)) I Pb.proj p v = mfderiv (I.prod (𝓡 3)) I Pb.proj p w)
    (h2 : mvfderiv (I.prod (𝓡 3)) (Pb.fU b₀) p v = mvfderiv (I.prod (𝓡 3)) (Pb.fU b₀) p w) :
    v = w := by
  have hd1 : mfderiv (I.prod (𝓡 3)) I Pb.proj p (v - w) = 0 := by rw [map_sub, h1, sub_self]
  have hd2 : mvfderiv (I.prod (𝓡 3)) (Pb.fU b₀) p (v - w) = 0 := by rw [map_sub, h2, sub_self]
  have hc : C.conn p (v - w) = 0 := by
    have h := C.conn_local b₀ hp (v - w)
    rw [hd1, show C.pot b₀ (Pb.proj p) 0 = 0 by simp [pot], mul_zero, zero_mul, zero_add] at h
    rw [h]
    have hd2' : mvfderiv (I.prod (𝓡 3)) (fun x => (Pb.fib b₀ x : Quaternion ℝ)) p (v - w) = 0 := hd2
    rw [hd2', mul_zero]
  exact sub_eq_zero.1 (C.eq_zero_of_proj_conn hd1 hc)

/-- The vertical frame field `E_a = r⁻¹ (qe a)^#`. -/
def vfield (r : B → ℝ) (a : Fin 3) : Π p : P, TangentSpace (I.prod (𝓡 3)) p :=
  fun p => (r (Pb.proj p))⁻¹ • Pb.fund (ζq a) p

theorem mfderiv_proj_vfield (r : B → ℝ) (a : Fin 3) (p : P) :
    mfderiv (I.prod (𝓡 3)) I Pb.proj p (vfield (Pb := Pb) r a p) = 0 := by
  rw [vfield, map_smul, Pb.mfderiv_proj_fund, smul_zero]

include C in
/-- `du(E_a) = r⁻¹ u qe_a`. -/
theorem mvfderiv_fU_vfield (b₀ : B) {p : P} (hp : Pb.proj p ∈ Pb.nbhd b₀) (r : B → ℝ) (a : Fin 3) :
    mvfderiv (I.prod (𝓡 3)) (Pb.fU b₀) p (vfield (Pb := Pb) r a p) =
      (r (Pb.proj p))⁻¹ • (Pb.fU b₀ p * qe a) := by
  rw [vfield, map_smul, C.mvfderiv_fU_fund b₀ hp, ι3_ζq]

theorem contMDiffAt_vfield {r : B → ℝ} {p : P} (hr : ContMDiffAt I 𝓘(ℝ) ∞ r (Pb.proj p))
    (hr0 : r (Pb.proj p) ≠ 0) (a : Fin 3) :
    ContMDiffAt (I.prod (𝓡 3)) (I.prod (𝓡 3)).tangent ∞ (T% (vfield (Pb := Pb) r a)) p := by
  have hri : ContMDiffAt (I.prod (𝓡 3)) 𝓘(ℝ) ∞ (fun x => (r (Pb.proj x))⁻¹) p :=
    (hr.comp p (Pb.proj_smooth p)).inv₀ hr0
  exact hri.smul_section (Pb.contMDiffAt_fund (ζq a) p)

/-- The local potential applied to a field, `b ↦ A_b(e_b)`. -/
def potE (b₀ : B) (e : Π b : B, TangentSpace I b) (b : B) : Quaternion ℝ := C.pot b₀ b (e b)

theorem fib_sec_one (b₀ : B) {b : B} (hb : b ∈ Pb.nbhd b₀) : Pb.fib b₀ (Pb.sec b₀ b) = 1 := by
  have h := Pb.fib_sec b₀ b hb 1
  rwa [Pb.ract_one] at h

/-- On the section, the base lift is the differential of the section. -/
theorem trivΦ_sec (b₀ : B) {b : B} (hb : b ∈ Pb.nbhd b₀) :
    Pb.trivΦ b₀ (Pb.sec b₀ b) = Pb.sec b₀ := by
  funext b'
  rw [PrincipalS3Bundle.trivΦ, fib_sec_one b₀ hb, Pb.ract_one]

include C in
/-- **The local potential is smooth** where `e` is. -/
theorem contMDiffAt_potE (b₀ : B) {b : B} (hb : b ∈ Pb.nbhd b₀) {e : Π b : B, TangentSpace I b}
    (he : ContMDiffAt I I.tangent ∞ (T% e) b) :
    ContMDiffAt I 𝓘(ℝ, Quaternion ℝ) ∞ (C.potE b₀ e) b := by
  have hsb : Pb.proj (Pb.sec b₀ b) = b := Pb.proj_sec b₀ b hb
  have hp : Pb.proj (Pb.sec b₀ b) ∈ Pb.nbhd b₀ := by rw [hsb]; exact hb
  have he' : ContMDiffAt I I.tangent ∞ (T% e) (Pb.proj (Pb.sec b₀ b)) := by rw [hsb]; exact he
  have hω := C.smooth _ _ (Pb.contMDiffAt_liftB b₀ hp he')
  have hsec : ContMDiffAt I (I.prod (𝓡 3)) ∞ (Pb.sec b₀) b :=
    (Pb.sec_smooth b₀).contMDiffAt ((Pb.nbhd_open b₀).mem_nhds hb)
  have h := hω.comp b hsec
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [(Pb.nbhd_open b₀).mem_nhds hb] with b' hb'
  have hs' : Pb.proj (Pb.sec b₀ b') = b' := Pb.proj_sec b₀ b' hb'
  show C.pot b₀ b' (e b') = C.conn (Pb.sec b₀ b') (Pb.liftB b₀ e (Pb.sec b₀ b'))
  have key : ∀ y (hy : Pb.proj (Pb.sec b₀ b') = y),
      C.conn (Pb.sec b₀ b') (Pb.liftB b₀ e (Pb.sec b₀ b')) =
        C.conn (Pb.sec b₀ b') (mfderiv I (I.prod (𝓡 3)) (Pb.sec b₀) y (e y)) := by
    intro y hy
    show C.conn (Pb.sec b₀ b') (mfderiv I (I.prod (𝓡 3)) (Pb.trivΦ b₀ (Pb.sec b₀ b'))
      (Pb.proj (Pb.sec b₀ b')) (e (Pb.proj (Pb.sec b₀ b')))) = _
    rw [trivΦ_sec b₀ hb', hy]
  rw [key b' hs']
  rfl

end S3Connection

end Tests

section Vertical

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type} [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B]
  {P : Type} [TopologicalSpace P] [ChartedSpace (ModelProd H E3) P] [IsManifold (I.prod (𝓡 3)) ∞ P]
  {Pb : PrincipalS3Bundle I B P} (C : S3Connection Pb)

namespace S3Connection

theorem two_minSmoothness : minSmoothness ℝ 2 ≤ (2 : ℕ∞) := by
  rw [minSmoothness_of_isRCLikeNormedField]; norm_num

theorem two_ne_infty : ((2 : ℕ∞) : ℕ∞ω) ≠ ∞ := by simp

theorem two_le_infty'' : ((2 : ℕ∞) : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top

/-- `t ↦ t • q` as a continuous linear map `ℝ → ℍ`. -/
def smulL (q : Quaternion ℝ) : ℝ →L[ℝ] Quaternion ℝ :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight q

@[simp] theorem smulL_apply (q : Quaternion ℝ) (t : ℝ) : smulL q t = t • q := rfl

theorem contMDiffAt_fU (b₀ : B) {p : P} (hp : Pb.proj p ∈ Pb.nbhd b₀) :
    ContMDiffAt (I.prod (𝓡 3)) 𝓘(ℝ, Quaternion ℝ) ∞ (Pb.fU b₀) p :=
  (contMDiff_coe_sphere (n := 3)).contMDiffAt.comp p
    ((Pb.fib_smooth b₀).contMDiffAt (Pb.nhds_preimage b₀ hp))

variable {r : B → ℝ}

/-- The function `ρ = r⁻¹ ∘ π`. -/
def rinv (r : B → ℝ) (p : P) : ℝ := (r (Pb.proj p))⁻¹

theorem contMDiffAt_rinv (hr : ContMDiff I 𝓘(ℝ) ∞ r) (hr0 : ∀ b, r b ≠ 0) (p : P) :
    ContMDiffAt (I.prod (𝓡 3)) 𝓘(ℝ) ∞ (rinv (Pb := Pb) r) p :=
  ((hr _).comp p (Pb.proj_smooth p)).inv₀ (hr0 _)

theorem mvfderiv_rinv_vfield (hr : ContMDiff I 𝓘(ℝ) ∞ r) (hr0 : ∀ b, r b ≠ 0) (p : P)
    (a : Fin 3) :
    mvfderiv (I.prod (𝓡 3)) (rinv (Pb := Pb) r) p (vfield (Pb := Pb) r a p) = 0 := by
  have hd : MDifferentiableAt I 𝓘(ℝ) (fun b => (r b)⁻¹) (Pb.proj p) :=
    (((hr _).inv₀ (hr0 _)).mdifferentiableAt (by simp))
  rw [show rinv (Pb := Pb) r = (fun b => (r b)⁻¹) ∘ Pb.proj from rfl,
    mvfderiv_comp_apply hd (Pb.mdiffAt_proj p), mfderiv_proj_vfield, map_zero]

include C in
/-- `E_b u = u · (r⁻¹ qe_b)` near `p`. -/
theorem fU_vfield_eventually (b₀ : B) {p : P} (hp : Pb.proj p ∈ Pb.nbhd b₀) (b : Fin 3) :
    (fun y => mvfderiv (I.prod (𝓡 3)) (Pb.fU b₀) y (vfield (Pb := Pb) r b y)) =ᶠ[𝓝 p]
      fun y => Pb.fU b₀ y * smulL (qe b) (rinv (Pb := Pb) r y) := by
  filter_upwards [Pb.nhds_preimage b₀ hp] with y hy
  rw [C.mvfderiv_fU_vfield b₀ hy, smulL_apply, rinv, mul_smul_comm]

include C in
/-- **The vertical bracket**: `[E_a, E_b] = r⁻¹ Σ_c c_abc E_c`. -/
theorem mlieBracket_vfield (hr : ContMDiff I 𝓘(ℝ) ∞ r) (hr0 : ∀ b, r b ≠ 0) (b₀ : B) {p : P}
    (hp : Pb.proj p ∈ Pb.nbhd b₀) (a b : Fin 3) :
    mlieBracket (I.prod (𝓡 3)) (vfield (Pb := Pb) r a) (vfield (Pb := Pb) r b) p =
      ∑ c, ((r (Pb.proj p))⁻¹ * Prop31Algebra.cst a b c) • vfield (Pb := Pb) r c p := by
  have hV : ∀ c : Fin 3, ∀ᶠ y in 𝓝 p, ContMDiffAt (I.prod (𝓡 3)) (I.prod (𝓡 3)).tangent
      ((2 : ℕ∞) : ℕ∞ω) (T% (vfield (Pb := Pb) r c)) y :=
    fun c => Eventually.of_forall fun y => (contMDiffAt_vfield ((hr _)) (hr0 _) c).of_le two_le_infty''
  apply C.eq_of_tests b₀ hp
  · -- `dπ`: both sides vanish
    have h0 : ∀ᶠ q in 𝓝 (Pb.proj p), ContMDiffAt I I.tangent ((2 : ℕ∞) : ℕ∞ω)
        (T% (0 : Π b : B, TangentSpace I b)) q :=
      Eventually.of_forall fun q => (contMDiff_zeroSection ℝ (TangentSpace I : B → Type _)) q
    have hrel := mfderiv_mlieBracket_of_related (I := I.prod (𝓡 3)) (J := I) (f := Pb.proj)
      (X' := vfield (Pb := Pb) r a) (Y' := vfield (Pb := Pb) r b) (X := 0) (Y := 0) (p := p)
      two_minSmoothness two_ne_infty ((Pb.proj_smooth p).of_le two_le_infty'')
      (Eventually.of_forall fun z => mfderiv_proj_vfield r a z)
      (Eventually.of_forall fun z => mfderiv_proj_vfield r b z) (hV a) (hV b) h0 h0
    rw [hrel, mlieBracket_zero_left, map_sum]
    simp only [map_smul, mfderiv_proj_vfield, smul_zero, Finset.sum_const_zero]
    rfl
  · -- `du`
    have hg : ContMDiffAt (I.prod (𝓡 3)) 𝓘(ℝ, Quaternion ℝ) ((2 : ℕ∞) : ℕ∞ω) (Pb.fU b₀) p :=
      (contMDiffAt_fU b₀ hp).of_le two_le_infty''
    have hid := mvfderiv_mlieBracket_quat hg (hV a) (hV b)
    rw [← hid, mvfderiv_congr_of_eventuallyEq (C.fU_vfield_eventually b₀ hp b),
      mvfderiv_congr_of_eventuallyEq (C.fU_vfield_eventually b₀ hp a)]
    have hfd : MDifferentiableAt (I.prod (𝓡 3)) 𝓘(ℝ, Quaternion ℝ) (Pb.fU b₀) p :=
      (contMDiffAt_fU b₀ hp).mdifferentiableAt (by simp)
    have hρd : MDifferentiableAt (I.prod (𝓡 3)) 𝓘(ℝ) (rinv (Pb := Pb) r) p :=
      (contMDiffAt_rinv hr hr0 p).mdifferentiableAt (by simp)
    have hLd : ∀ c : Fin 3, MDifferentiableAt (I.prod (𝓡 3)) 𝓘(ℝ, Quaternion ℝ)
        (fun y => smulL (qe c) (rinv (Pb := Pb) r y)) p :=
      fun c => (smulL (qe c)).mdifferentiableAt.comp p hρd
    have hcl : ∀ (c : Fin 3) (v : TangentSpace (I.prod (𝓡 3)) p),
        mvfderiv (I.prod (𝓡 3)) (fun y => smulL (qe c) (rinv (Pb := Pb) r y)) p v =
          smulL (qe c) (mvfderiv (I.prod (𝓡 3)) (rinv (Pb := Pb) r) p v) :=
      fun c v => mvfderiv_clm_comp (smulL (qe c)) hρd v
    rw [mvfderiv_mul_apply hfd (hLd b), mvfderiv_mul_apply hfd (hLd a), hcl, hcl,
      mvfderiv_rinv_vfield hr hr0, mvfderiv_rinv_vfield hr hr0,
      C.mvfderiv_fU_vfield b₀ hp, C.mvfderiv_fU_vfield b₀ hp, map_sum]
    simp only [map_zero, mul_zero, zero_add, smulL_apply, rinv, map_smul,
      C.mvfderiv_fU_vfield b₀ hp]
    set t := (r (Pb.proj p))⁻¹
    set u := Pb.fU b₀ p
    have hc := qe_comm a b
    calc t • (u * qe a) * t • qe b - t • (u * qe b) * t • qe a
        = (t * t) • (u * (qe a * qe b - qe b * qe a)) := by
          simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_sub, smul_sub, mul_assoc]
      _ = ∑ c, (t * Prop31Algebra.cst a b c) • t • (u * qe c) := by
          rw [hc, Finset.mul_sum, Finset.smul_sum]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [mul_smul_comm, smul_smul, smul_smul]
          ring_nf

end S3Connection

end Vertical

section Mixed

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type} [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B]
  {P : Type} [TopologicalSpace P] [ChartedSpace (ModelProd H E3) P] [IsManifold (I.prod (𝓡 3)) ∞ P]
  {Pb : PrincipalS3Bundle I B P} (C : S3Connection Pb)

namespace S3Connection

variable {r : B → ℝ}

/-- `d(c⁻¹) = −c⁻² dc`. -/
theorem mvfderiv_inv_apply {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} {M : Type*} [TopologicalSpace M]
    [ChartedSpace H' M] {c : M → ℝ} {z : M} (hc : MDifferentiableAt J 𝓘(ℝ) c z) (hc0 : c z ≠ 0)
    (v : TangentSpace J z) :
    mvfderiv J (fun y => (c y)⁻¹) z v = -((c z ^ 2)⁻¹) * mvfderiv J c z v := by
  have hinv : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ) (fun t : ℝ => t⁻¹) (c z) :=
    ((hasDerivAt_inv hc0).differentiableAt).mdifferentiableAt
  rw [show (fun y => (c y)⁻¹) = (fun t : ℝ => t⁻¹) ∘ c from rfl, mvfderiv_comp_apply hinv hc,
    mvfderiv_vs, (hasDerivAt_inv hc0).hasFDerivAt.fderiv]
  show (mvfderiv J c z v) * (-(c z ^ 2)⁻¹) = -((c z ^ 2)⁻¹) * mvfderiv J c z v
  rw [mul_comm]

theorem mvfderiv_rinv_hlift (hr : ContMDiff I 𝓘(ℝ) ∞ r) (hr0 : ∀ b, r b ≠ 0) (b₀ : B) {p : P}
    (hp : Pb.proj p ∈ Pb.nbhd b₀) (e : Π b : B, TangentSpace I b) :
    mvfderiv (I.prod (𝓡 3)) (rinv (Pb := Pb) r) p (C.hlift b₀ e p) =
      -((r (Pb.proj p) ^ 2)⁻¹) * mvfderiv I r (Pb.proj p) (e (Pb.proj p)) := by
  have hd : MDifferentiableAt I 𝓘(ℝ) r (Pb.proj p) := (hr _).mdifferentiableAt (by simp)
  have hdi : MDifferentiableAt I 𝓘(ℝ) (fun b => (r b)⁻¹) (Pb.proj p) :=
    ((hr _).inv₀ (hr0 _)).mdifferentiableAt (by simp)
  rw [show rinv (Pb := Pb) r = (fun b => (r b)⁻¹) ∘ Pb.proj from rfl,
    mvfderiv_comp_apply hdi (Pb.mdiffAt_proj p), C.mfderiv_proj_hlift b₀ hp,
    mvfderiv_inv_apply hd (hr0 _)]

/-- Near `p`, the horizontal lift is smooth. -/
theorem hlift_smooth_eventually (b₀ : B) {p : P} (hp : Pb.proj p ∈ Pb.nbhd b₀)
    {e : Π b : B, TangentSpace I b} (he : ∀ᶠ q in 𝓝 (Pb.proj p), ContMDiffAt I I.tangent ∞ (T% e) q) :
    ∀ᶠ y in 𝓝 p, ContMDiffAt (I.prod (𝓡 3)) (I.prod (𝓡 3)).tangent ∞ (T% (C.hlift b₀ e)) y := by
  have h1 : ∀ᶠ y in 𝓝 p, ContMDiffAt I I.tangent ∞ (T% e) (Pb.proj y) :=
    (Pb.proj_smooth.continuous.continuousAt (x := p)).eventually he
  filter_upwards [h1, Pb.nhds_preimage b₀ hp] with y hy1 hy2
  exact C.contMDiffAt_hlift b₀ hy2 hy1

/-- **The mixed bracket**: `[X, E_a] = −ϑ E_a`, `ϑ = e(r)/r`. -/
theorem mlieBracket_hlift_vfield (hr : ContMDiff I 𝓘(ℝ) ∞ r) (hr0 : ∀ b, r b ≠ 0) (b₀ : B) {p : P}
    (hp : Pb.proj p ∈ Pb.nbhd b₀) {e : Π b : B, TangentSpace I b}
    (he : ∀ᶠ q in 𝓝 (Pb.proj p), ContMDiffAt I I.tangent ∞ (T% e) q) (a : Fin 3) :
    mlieBracket (I.prod (𝓡 3)) (C.hlift b₀ e) (vfield (Pb := Pb) r a) p =
      (-(mvfderiv I r (Pb.proj p) (e (Pb.proj p)) / r (Pb.proj p))) • vfield (Pb := Pb) r a p := by
  have hV : ∀ᶠ y in 𝓝 p, ContMDiffAt (I.prod (𝓡 3)) (I.prod (𝓡 3)).tangent
      ((2 : ℕ∞) : ℕ∞ω) (T% (vfield (Pb := Pb) r a)) y :=
    Eventually.of_forall fun y => (contMDiffAt_vfield ((hr _)) (hr0 _) a).of_le two_le_infty''
  have hX : ∀ᶠ y in 𝓝 p, ContMDiffAt (I.prod (𝓡 3)) (I.prod (𝓡 3)).tangent
      ((2 : ℕ∞) : ℕ∞ω) (T% (C.hlift b₀ e)) y :=
    (C.hlift_smooth_eventually b₀ hp he).mono fun y hy => hy.of_le two_le_infty''
  apply C.eq_of_tests b₀ hp
  · have he2 : ∀ᶠ q in 𝓝 (Pb.proj p), ContMDiffAt I I.tangent ((2 : ℕ∞) : ℕ∞ω) (T% e) q :=
      he.mono fun q hq => hq.of_le two_le_infty''
    have h0 : ∀ᶠ q in 𝓝 (Pb.proj p), ContMDiffAt I I.tangent ((2 : ℕ∞) : ℕ∞ω)
        (T% (0 : Π b : B, TangentSpace I b)) q :=
      Eventually.of_forall fun q => (contMDiff_zeroSection ℝ (TangentSpace I : B → Type _)) q
    have hrel := mfderiv_mlieBracket_of_related (I := I.prod (𝓡 3)) (J := I) (f := Pb.proj)
      (X' := C.hlift b₀ e) (Y' := vfield (Pb := Pb) r a) (X := e) (Y := 0) (p := p)
      two_minSmoothness two_ne_infty ((Pb.proj_smooth p).of_le two_le_infty'')
      (by filter_upwards [Pb.nhds_preimage b₀ hp] with z hz using C.mfderiv_proj_hlift b₀ hz e)
      (Eventually.of_forall fun z => mfderiv_proj_vfield r a z) hX hV he2 h0
    rw [hrel, mlieBracket_zero_right, map_smul, mfderiv_proj_vfield, smul_zero]
    rfl
  · have hg : ContMDiffAt (I.prod (𝓡 3)) 𝓘(ℝ, Quaternion ℝ) ((2 : ℕ∞) : ℕ∞ω) (Pb.fU b₀) p :=
      (contMDiffAt_fU b₀ hp).of_le two_le_infty''
    have hid := mvfderiv_mlieBracket_quat hg hX hV
    have hXe : (fun y => mvfderiv (I.prod (𝓡 3)) (Pb.fU b₀) y (C.hlift b₀ e y)) =ᶠ[𝓝 p]
        fun y => -(C.potE b₀ e (Pb.proj y) * Pb.fU b₀ y) := by
      filter_upwards [Pb.nhds_preimage b₀ hp] with y hy using C.mvfderiv_fU_hlift b₀ hy e
    rw [← hid, mvfderiv_congr_of_eventuallyEq (C.fU_vfield_eventually b₀ hp a),
      mvfderiv_congr_of_eventuallyEq hXe]
    have hfd : MDifferentiableAt (I.prod (𝓡 3)) 𝓘(ℝ, Quaternion ℝ) (Pb.fU b₀) p :=
      (contMDiffAt_fU b₀ hp).mdifferentiableAt (by simp)
    have hρd : MDifferentiableAt (I.prod (𝓡 3)) 𝓘(ℝ) (rinv (Pb := Pb) r) p :=
      (contMDiffAt_rinv hr hr0 p).mdifferentiableAt (by simp)
    have hLd : MDifferentiableAt (I.prod (𝓡 3)) 𝓘(ℝ, Quaternion ℝ)
        (fun y => smulL (qe a) (rinv (Pb := Pb) r y)) p := (smulL (qe a)).mdifferentiableAt.comp p hρd
    have hPd : MDifferentiableAt I 𝓘(ℝ, Quaternion ℝ) (C.potE b₀ e) (Pb.proj p) :=
      (C.contMDiffAt_potE b₀ hp he.self_of_nhds).mdifferentiableAt (by simp)
    have hPπ : MDifferentiableAt (I.prod (𝓡 3)) 𝓘(ℝ, Quaternion ℝ)
        (fun y => C.potE b₀ e (Pb.proj y)) p := hPd.comp p (Pb.mdiffAt_proj p)
    have hcl : ∀ v : TangentSpace (I.prod (𝓡 3)) p,
        mvfderiv (I.prod (𝓡 3)) (fun y => smulL (qe a) (rinv (Pb := Pb) r y)) p v =
          smulL (qe a) (mvfderiv (I.prod (𝓡 3)) (rinv (Pb := Pb) r) p v) :=
      fun v => mvfderiv_clm_comp (smulL (qe a)) hρd v
    have hneg : ∀ v : TangentSpace (I.prod (𝓡 3)) p,
        mvfderiv (I.prod (𝓡 3)) (fun y => -(C.potE b₀ e (Pb.proj y) * Pb.fU b₀ y)) p v =
          -(C.potE b₀ e (Pb.proj p) * mvfderiv (I.prod (𝓡 3)) (Pb.fU b₀) p v +
            mvfderiv (I.prod (𝓡 3)) (fun y => C.potE b₀ e (Pb.proj y)) p v * Pb.fU b₀ p) := by
      intro v
      have h := mvfderiv_clm_comp (-(ContinuousLinearMap.id ℝ (Quaternion ℝ)))
        (f := fun y => C.potE b₀ e (Pb.proj y) * Pb.fU b₀ y) (hPπ.mul hfd) v
      rw [show (fun y => -(C.potE b₀ e (Pb.proj y) * Pb.fU b₀ y)) =
        ⇑(-(ContinuousLinearMap.id ℝ (Quaternion ℝ))) ∘ (fun y => C.potE b₀ e (Pb.proj y) * Pb.fU b₀ y)
        from rfl, h, mvfderiv_mul_apply hPπ hfd]
      rfl
    have hPv : mvfderiv (I.prod (𝓡 3)) (fun y => C.potE b₀ e (Pb.proj y)) p
        (vfield (Pb := Pb) r a p) = 0 := by
      rw [show (fun y => C.potE b₀ e (Pb.proj y)) = C.potE b₀ e ∘ Pb.proj from rfl,
        mvfderiv_comp_apply hPd (Pb.mdiffAt_proj p), mfderiv_proj_vfield, map_zero]
    rw [mvfderiv_mul_apply hfd hLd, hcl, hneg, hPv, C.mvfderiv_rinv_hlift hr hr0 b₀ hp,
      C.mvfderiv_fU_hlift b₀ hp, C.mvfderiv_fU_vfield b₀ hp, map_smul, C.mvfderiv_fU_vfield b₀ hp]
    simp only [smulL_apply, rinv, zero_mul, add_zero]
    set t := (r (Pb.proj p))⁻¹
    set u := Pb.fU b₀ p
    set A := C.potE b₀ e (Pb.proj p)
    set dr := mvfderiv I r (Pb.proj p) (e (Pb.proj p))
    have ht : (r (Pb.proj p) ^ 2)⁻¹ = t * t := by rw [sq, mul_inv]
    rw [ht]
    have hA : C.pot b₀ (Pb.proj p) (e (Pb.proj p)) = A := rfl
    rw [hA]
    have hdiv : -(dr / r (Pb.proj p)) = -(dr * t) := by rw [div_eq_mul_inv]
    rw [hdiv]
    simp only [mul_smul_comm, smul_smul, neg_mul, mul_neg, smul_neg, neg_smul, mul_assoc]
    abel_nf
    congr 1
    ring_nf

end S3Connection

end Mixed

section Horiz

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type} [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B]
  {P : Type} [TopologicalSpace P] [ChartedSpace (ModelProd H E3) P] [IsManifold (I.prod (𝓡 3)) ∞ P]
  {Pb : PrincipalS3Bundle I B P} (C : S3Connection Pb)

namespace S3Connection

/-- **The curvature of the connection**, in the gauge of `sec b₀`, on the fields `e₁, e₂`:
`F = e₁(A e₂) − e₂(A e₁) − A[e₁,e₂] + [A e₁, A e₂]`. -/
def curvF (b₀ : B) (e₁ e₂ : Π b : B, TangentSpace I b) (b : B) : Quaternion ℝ :=
  mvfderiv I (C.potE b₀ e₂) b (e₁ b) - mvfderiv I (C.potE b₀ e₁) b (e₂ b) -
    C.pot b₀ b (mlieBracket I e₁ e₂ b) +
    (C.potE b₀ e₁ b * C.potE b₀ e₂ b - C.potE b₀ e₂ b * C.potE b₀ e₁ b)

theorem re_commutator (x y : Quaternion ℝ) : (x * y - y * x).re = 0 := by
  simp only [Quaternion.re_sub, Quaternion.re_mul]; ring

include C in
/-- Derivatives of the potential are imaginary. -/
theorem re_mvfderiv_potE (b₀ : B) {e : Π b : B, TangentSpace I b} {b : B}
    (hd : MDifferentiableAt I 𝓘(ℝ, Quaternion ℝ) (C.potE b₀ e) b) (v : TangentSpace I b) :
    (mvfderiv I (C.potE b₀ e) b v).re = 0 := by
  have h0 : ⇑(innerSL ℝ (1 : Quaternion ℝ)) ∘ C.potE b₀ e = fun _ => (0 : ℝ) := by
    funext b'
    simp only [comp_apply, innerSL_apply_apply, inner_quat, Quaternion.re_one, Quaternion.imI_one,
      Quaternion.imJ_one, Quaternion.imK_one, one_mul, zero_mul, add_zero]
    exact C.im _ _
  have h := mvfderiv_clm_comp (innerSL ℝ (1 : Quaternion ℝ)) hd v
  rw [h0] at h
  have hz : mvfderiv I (fun _ : B => (0 : ℝ)) b v = 0 := by simp [mvfderiv, mfderiv_const]
  rw [hz, innerSL_apply_apply, inner_quat] at h
  simp only [Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one, one_mul,
    zero_mul, add_zero] at h
  exact h.symm

theorem re_curvF (b₀ : B) {e₁ e₂ : Π b : B, TangentSpace I b} {b : B}
    (hd₁ : MDifferentiableAt I 𝓘(ℝ, Quaternion ℝ) (C.potE b₀ e₁) b)
    (hd₂ : MDifferentiableAt I 𝓘(ℝ, Quaternion ℝ) (C.potE b₀ e₂) b) :
    (C.curvF b₀ e₁ e₂ b).re = 0 := by
  have hp0 : (C.pot b₀ b (mlieBracket I e₁ e₂ b)).re = 0 := C.im _ _
  rw [curvF, Quaternion.re_add, Quaternion.re_sub, Quaternion.re_sub, C.re_mvfderiv_potE b₀ hd₂,
    C.re_mvfderiv_potE b₀ hd₁, hp0, re_commutator]
  ring

/-- **The horizontal bracket**: `[X_{e₁}, X_{e₂}] = X_{[e₁,e₂]} − Σ_a ⟪ū F u, qe_a⟫ (qe_a)^#`. -/
theorem mlieBracket_hlift (b₀ : B) {p : P} (hp : Pb.proj p ∈ Pb.nbhd b₀)
    {e₁ e₂ : Π b : B, TangentSpace I b}
    (he₁ : ∀ᶠ q in 𝓝 (Pb.proj p), ContMDiffAt I I.tangent ∞ (T% e₁) q)
    (he₂ : ∀ᶠ q in 𝓝 (Pb.proj p), ContMDiffAt I I.tangent ∞ (T% e₂) q) :
    mlieBracket (I.prod (𝓡 3)) (C.hlift b₀ e₁) (C.hlift b₀ e₂) p =
      C.hlift b₀ (mlieBracket I e₁ e₂) p -
        ∑ a, ⟪star (Pb.fU b₀ p) * C.curvF b₀ e₁ e₂ (Pb.proj p) * Pb.fU b₀ p, qe a⟫ •
          Pb.fund (ζq a) p := by
  have hX₁ := (C.hlift_smooth_eventually b₀ hp he₁).mono fun y hy => hy.of_le two_le_infty''
  have hX₂ := (C.hlift_smooth_eventually b₀ hp he₂).mono fun y hy => hy.of_le two_le_infty''
  apply C.eq_of_tests b₀ hp
  · have hrel := mfderiv_mlieBracket_of_related (I := I.prod (𝓡 3)) (J := I) (f := Pb.proj)
      (X' := C.hlift b₀ e₁) (Y' := C.hlift b₀ e₂) (X := e₁) (Y := e₂) (p := p)
      two_minSmoothness two_ne_infty ((Pb.proj_smooth p).of_le two_le_infty'')
      (by filter_upwards [Pb.nhds_preimage b₀ hp] with z hz using C.mfderiv_proj_hlift b₀ hz e₁)
      (by filter_upwards [Pb.nhds_preimage b₀ hp] with z hz using C.mfderiv_proj_hlift b₀ hz e₂)
      hX₁ hX₂ (he₁.mono fun q hq => hq.of_le two_le_infty'')
      (he₂.mono fun q hq => hq.of_le two_le_infty'')
    rw [hrel, map_sub, C.mfderiv_proj_hlift b₀ hp, map_sum]
    simp only [map_smul, Pb.mfderiv_proj_fund, smul_zero, Finset.sum_const_zero, sub_zero]
  · have hg : ContMDiffAt (I.prod (𝓡 3)) 𝓘(ℝ, Quaternion ℝ) ((2 : ℕ∞) : ℕ∞ω) (Pb.fU b₀) p :=
      (contMDiffAt_fU b₀ hp).of_le two_le_infty''
    have hid := mvfderiv_mlieBracket_quat hg hX₁ hX₂
    have hXe : ∀ e : Π b : B, TangentSpace I b,
        (fun y => mvfderiv (I.prod (𝓡 3)) (Pb.fU b₀) y (C.hlift b₀ e y)) =ᶠ[𝓝 p]
          fun y => -(C.potE b₀ e (Pb.proj y) * Pb.fU b₀ y) := fun e => by
      filter_upwards [Pb.nhds_preimage b₀ hp] with y hy using C.mvfderiv_fU_hlift b₀ hy e
    rw [← hid, mvfderiv_congr_of_eventuallyEq (hXe e₂), mvfderiv_congr_of_eventuallyEq (hXe e₁)]
    have hfd : MDifferentiableAt (I.prod (𝓡 3)) 𝓘(ℝ, Quaternion ℝ) (Pb.fU b₀) p :=
      (contMDiffAt_fU b₀ hp).mdifferentiableAt (by simp)
    have hPd : ∀ {e : Π b : B, TangentSpace I b},
        (∀ᶠ q in 𝓝 (Pb.proj p), ContMDiffAt I I.tangent ∞ (T% e) q) →
          MDifferentiableAt I 𝓘(ℝ, Quaternion ℝ) (C.potE b₀ e) (Pb.proj p) := fun he =>
      (C.contMDiffAt_potE b₀ hp he.self_of_nhds).mdifferentiableAt (by simp)
    have hneg : ∀ {e : Π b : B, TangentSpace I b},
        (∀ᶠ q in 𝓝 (Pb.proj p), ContMDiffAt I I.tangent ∞ (T% e) q) →
        ∀ v : TangentSpace (I.prod (𝓡 3)) p,
        mvfderiv (I.prod (𝓡 3)) (fun y => -(C.potE b₀ e (Pb.proj y) * Pb.fU b₀ y)) p v =
          -(C.potE b₀ e (Pb.proj p) * mvfderiv (I.prod (𝓡 3)) (Pb.fU b₀) p v +
            mvfderiv I (C.potE b₀ e) (Pb.proj p) (mfderiv (I.prod (𝓡 3)) I Pb.proj p v) *
              Pb.fU b₀ p) := by
      intro e he v
      have hPπ : MDifferentiableAt (I.prod (𝓡 3)) 𝓘(ℝ, Quaternion ℝ)
          (fun y => C.potE b₀ e (Pb.proj y)) p := (hPd he).comp p (Pb.mdiffAt_proj p)
      have h := mvfderiv_clm_comp (-(ContinuousLinearMap.id ℝ (Quaternion ℝ)))
        (f := fun y => C.potE b₀ e (Pb.proj y) * Pb.fU b₀ y) (hPπ.mul hfd) v
      rw [show (fun y => -(C.potE b₀ e (Pb.proj y) * Pb.fU b₀ y)) =
        ⇑(-(ContinuousLinearMap.id ℝ (Quaternion ℝ))) ∘
          (fun y => C.potE b₀ e (Pb.proj y) * Pb.fU b₀ y) from rfl, h, mvfderiv_mul_apply hPπ hfd,
        show (fun y => C.potE b₀ e (Pb.proj y)) = C.potE b₀ e ∘ Pb.proj from rfl,
        mvfderiv_comp_apply (hPd he) (Pb.mdiffAt_proj p)]
      rfl
    rw [hneg he₂, hneg he₁, C.mvfderiv_fU_hlift b₀ hp, C.mvfderiv_fU_hlift b₀ hp,
      C.mfderiv_proj_hlift b₀ hp, C.mfderiv_proj_hlift b₀ hp, map_sub,
      C.mvfderiv_fU_hlift b₀ hp, map_sum]
    simp only [map_smul, C.mvfderiv_fU_fund b₀ hp, ι3_ζq]
    set u := Pb.fU b₀ p
    set b := Pb.proj p
    have hre : (star u * C.curvF b₀ e₁ e₂ b * u).re = 0 := by
      rw [re_star_mul_mul, C.re_curvF b₀ (hPd he₁) (hPd he₂), zero_mul]
    have hsum : ∑ a, ⟪star u * C.curvF b₀ e₁ e₂ b * u, qe a⟫ • (u * qe a) =
        C.curvF b₀ e₁ e₂ b * u := by
      have h1 := sum_inner_qe hre
      have hu : u * star u = 1 := mul_star_self_sphere _
      calc ∑ a, ⟪star u * C.curvF b₀ e₁ e₂ b * u, qe a⟫ • (u * qe a)
          = u * ∑ a, ⟪star u * C.curvF b₀ e₁ e₂ b * u, qe a⟫ • qe a := by
            rw [Finset.mul_sum]; simp only [mul_smul_comm]
        _ = u * (star u * C.curvF b₀ e₁ e₂ b * u) := by rw [h1]
        _ = C.curvF b₀ e₁ e₂ b * u := by simp only [← mul_assoc, hu, one_mul]
    rw [hsum]
    show _ = -(C.pot b₀ b (mlieBracket I e₁ e₂ b) * u) - C.curvF b₀ e₁ e₂ b * u
    simp only [curvF, potE]
    noncomm_ring

end S3Connection

end Horiz

end

end ExoticSpheres8And10
