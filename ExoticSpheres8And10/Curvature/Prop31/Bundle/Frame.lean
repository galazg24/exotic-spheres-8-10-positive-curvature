/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Curvature.Prop31.Bundle.Local

/-! # Principal `S³`-bundles: base lifts, horizontal lifts and the vertical fields

Fix a trivialising neighbourhood `nbhd b₀` and a vector field `e` on `B`.
* `liftB b₀ e`: `p ↦ d(Φ_p)_{π p}(e(π p))`, with `Φ_p(b) = ract(sec b₀ b, fib b₀ p)`. This is
  the lift of `e` that is constant in the fibre coordinate.
* `hlift b₀ e = liftB b₀ e − Σ_a ⟪ω(liftB b₀ e), qe a⟫ (qe a)^#`: the **horizontal lift** of
  `e`, with `dπ = e` and `ω = 0`.

Values used by the bracket table (with `u = fib b₀ p`, `A = s^*ω`):
* `dπ(liftB) = e`, `ω(liftB) = ū A(e) u`;
* `dπ(ζ^#) = 0`, `d u(ζ^#) = u ι(ζ)`;
* `dπ(hlift) = e`, `ω(hlift) = 0`, `d u(hlift) = −A(e) u`.
-/

open RiemannianGeometry VectorField Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Module

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section FieldsAt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

set_option maxHeartbeats 2000000 in
/-- **`p ↦ d(Φ_p)_{n(p)}(ζ(p))` is a smooth field**, at a point, when `Φ_p(n(p)) = p` near it. -/
theorem contMDiffAt_mfderivField' {Φ : M → N → M} {n : M → N} {ζ : Π p : M, TangentSpace J (n p)}
    {p₀ : M} (hΦ : ContMDiffAt (I.prod J) I ∞ (uncurry Φ) (p₀, n p₀))
    (hn : ContMDiffAt I J ∞ n p₀) (hnp : ∀ᶠ p in 𝓝 p₀, Φ p (n p) = p)
    (hζ : ContMDiffAt I J.tangent ∞ (fun p => (⟨n p, ζ p⟩ : TangentBundle J N)) p₀) :
    ContMDiffAt I I.tangent ∞
      (T% (fun p : M => (show TangentSpace I p from mfderiv J I (Φ p) (n p) (ζ p)))) p₀ := by
  have hϕ := ContMDiffAt.mfderiv (I := J) (I' := I) (n := ∞) (m := ∞) Φ n hΦ hn (by simp)
  have hb₂ : ContMDiffAt I I ∞ (fun y : M => Φ y (n y)) p₀ :=
    contMDiffAt_id.congr_of_eventuallyEq hnp
  have hres := ContMDiffAt.clm_apply_of_inCoordinates (F₁ := E') (E₁ := TangentSpace J)
    (F₂ := E) (E₂ := TangentSpace I) (b₁ := n) (b₂ := fun y : M => Φ y (n y))
    (ϕ := fun y : M => mfderiv J I (Φ y) (n y)) (v := ζ) hϕ hζ hb₂
  refine hres.congr_of_eventuallyEq ?_
  filter_upwards [hnp] with m hm
  exact congrArg (fun z : M => (⟨z, mfderiv J I (Φ m) (n m) (ζ m)⟩ : TangentBundle I M)) hm.symm

end FieldsAt

section Lifts

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type} [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B]
  {P : Type} [TopologicalSpace P] [ChartedSpace (ModelProd H E3) P] [IsManifold (I.prod (𝓡 3)) ∞ P]
  {Pb : PrincipalS3Bundle I B P} (C : S3Connection Pb)

namespace PrincipalS3Bundle

variable (Pb)

/-- The local trivialisation map through `p`: `Φ_p(b) = ract(sec b₀ b, fib b₀ p)`. -/
def trivΦ (b₀ : B) (p : P) (b : B) : P := Pb.ract (Pb.sec b₀ b) (Pb.fib b₀ p)

/-- **The base lift** of a field `e` on `B`. -/
def liftB (b₀ : B) (e : Π b : B, TangentSpace I b) : Π p : P, TangentSpace (I.prod (𝓡 3)) p :=
  fun p => show TangentSpace (I.prod (𝓡 3)) p from
    mfderiv I (I.prod (𝓡 3)) (Pb.trivΦ b₀ p) (Pb.proj p) (e (Pb.proj p))

/-- The fibre coordinate in `ℍ`. -/
def fU (b₀ : B) (p : P) : Quaternion ℝ := (Pb.fib b₀ p : Quaternion ℝ)

theorem trivΦ_proj (b₀ : B) {p : P} (hp : Pb.proj p ∈ Pb.nbhd b₀) :
    Pb.trivΦ b₀ p (Pb.proj p) = p := Pb.sec_fib b₀ p hp

theorem trivΦ_eq (b₀ : B) (p : P) :
    Pb.trivΦ b₀ p = (Pb.ract · (Pb.fib b₀ p)) ∘ Pb.sec b₀ := rfl

theorem mdiffAt_ract_right (s : P) (u : S3) :
    MDifferentiableAt (I.prod (𝓡 3)) (I.prod (𝓡 3)) (Pb.ract · u) s :=
  (Pb.contMDiff_ract u s).mdifferentiableAt (by simp)

theorem mdiffAt_trivΦ (b₀ : B) {p : P} (hp : Pb.proj p ∈ Pb.nbhd b₀) :
    MDifferentiableAt I (I.prod (𝓡 3)) (Pb.trivΦ b₀ p) (Pb.proj p) :=
  (Pb.mdiffAt_ract_right _ _).comp _ (Pb.mdiffAt_sec b₀ hp)

/-- `dπ` of the base lift. -/
theorem mfderiv_proj_liftB (b₀ : B) {p : P} (hp : Pb.proj p ∈ Pb.nbhd b₀)
    (e : Π b : B, TangentSpace I b) :
    mfderiv (I.prod (𝓡 3)) I Pb.proj p (Pb.liftB b₀ e p) = e (Pb.proj p) := by
  have hid : Pb.proj ∘ Pb.trivΦ b₀ p =ᶠ[𝓝 (Pb.proj p)] id := by
    filter_upwards [(Pb.nbhd_open b₀).mem_nhds hp] with b hb
    exact Pb.proj_ract _ _ |>.trans (Pb.proj_sec b₀ b hb)
  have key : ∀ y (hy : Pb.trivΦ b₀ p (Pb.proj p) = y),
      mfderiv I I (Pb.proj ∘ Pb.trivΦ b₀ p) (Pb.proj p) (e (Pb.proj p)) =
        mfderiv (I.prod (𝓡 3)) I Pb.proj y
          (mfderiv I (I.prod (𝓡 3)) (Pb.trivΦ b₀ p) (Pb.proj p) (e (Pb.proj p))) := by
    intro y hy; subst hy
    rw [mfderiv_comp _ (Pb.mdiffAt_proj _) (Pb.mdiffAt_trivΦ b₀ hp)]; rfl
  have h := key p (Pb.trivΦ_proj b₀ hp)
  rw [hid.mfderiv_eq, mfderiv_id] at h
  exact h.symm

/-- `dπ` of a fundamental field vanishes. -/
theorem mfderiv_proj_fund (p : P) (ζ : E3) :
    mfderiv (I.prod (𝓡 3)) I Pb.proj p (Pb.fund ζ p) = 0 := by
  have hc : Pb.proj ∘ Pb.ract p = fun _ => Pb.proj p := funext fun q => Pb.proj_ract p q
  have key : ∀ y (hy : Pb.ract p 1 = y),
      mfderiv (𝓡 3) I (Pb.proj ∘ Pb.ract p) 1 ζ =
        mfderiv (I.prod (𝓡 3)) I Pb.proj y (mfderiv (𝓡 3) (I.prod (𝓡 3)) (Pb.ract p) 1 ζ) := by
    intro y hy; subst hy
    rw [mfderiv_comp _ (Pb.mdiffAt_proj _)
      ((Pb.contMDiff_ract_left p 1).mdifferentiableAt (by simp))]; rfl
  have h := key p (Pb.ract_one p)
  rw [hc, mfderiv_const] at h
  exact h.symm

end PrincipalS3Bundle

namespace S3Connection

/-- `ω` of the base lift: `ū A(e) u`. -/
theorem conn_liftB (b₀ : B) {p : P} (hp : Pb.proj p ∈ Pb.nbhd b₀) (e : Π b : B, TangentSpace I b) :
    C.conn p (Pb.liftB b₀ e p) = star (Pb.fU b₀ p) * C.pot b₀ (Pb.proj p) (e (Pb.proj p)) * Pb.fU b₀ p := by
  have hd : mfderiv I (I.prod (𝓡 3)) (Pb.trivΦ b₀ p) (Pb.proj p) (e (Pb.proj p)) =
      mfderiv (I.prod (𝓡 3)) (I.prod (𝓡 3)) (Pb.ract · (Pb.fib b₀ p)) (Pb.sec b₀ (Pb.proj p))
        (mfderiv I (I.prod (𝓡 3)) (Pb.sec b₀) (Pb.proj p) (e (Pb.proj p))) := by
    rw [Pb.trivΦ_eq, mfderiv_comp _ (Pb.mdiffAt_ract_right _ _) (Pb.mdiffAt_sec b₀ hp)]; rfl
  have hpp := Pb.trivΦ_proj b₀ hp
  calc C.conn p (Pb.liftB b₀ e p) =
      C.conn (Pb.ract (Pb.sec b₀ (Pb.proj p)) (Pb.fib b₀ p))
        (mfderiv I (I.prod (𝓡 3)) (Pb.trivΦ b₀ p) (Pb.proj p) (e (Pb.proj p))) := by
          rw [show Pb.ract (Pb.sec b₀ (Pb.proj p)) (Pb.fib b₀ p) = p from hpp]; rfl
    _ = _ := by rw [hd, C.conn_mfderiv_ract_right]; rfl

end S3Connection

end Lifts

section Horizontal

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type} [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B]
  {P : Type} [TopologicalSpace P] [ChartedSpace (ModelProd H E3) P] [IsManifold (I.prod (𝓡 3)) ∞ P]
  {Pb : PrincipalS3Bundle I B P} (C : S3Connection Pb)

namespace S3Connection

theorem fU_mul_star (b₀ : B) (p : P) : Pb.fU b₀ p * star (Pb.fU b₀ p) = 1 :=
  mul_star_self_sphere _

/-- **The derivative of the fibre coordinate**: `du = u ω − A(dπ ·) u`. -/
theorem mvfderiv_fU (b₀ : B) {p : P} (hp : Pb.proj p ∈ Pb.nbhd b₀)
    (v : TangentSpace (I.prod (𝓡 3)) p) :
    mvfderiv (I.prod (𝓡 3)) (Pb.fU b₀) p v =
      Pb.fU b₀ p * C.conn p v - C.pot b₀ (Pb.proj p) (mfderiv (I.prod (𝓡 3)) I Pb.proj p v) *
        Pb.fU b₀ p := by
  have h := C.conn_local b₀ hp v
  have hu : (Pb.fib b₀ p : Quaternion ℝ) * star (Pb.fib b₀ p : Quaternion ℝ) = 1 :=
    mul_star_self_sphere _
  show mvfderiv (I.prod (𝓡 3)) (fun x => (Pb.fib b₀ x : Quaternion ℝ)) p v =
    (Pb.fib b₀ p : Quaternion ℝ) * C.conn p v -
      C.pot b₀ (Pb.proj p) (mfderiv (I.prod (𝓡 3)) I Pb.proj p v) * (Pb.fib b₀ p : Quaternion ℝ)
  rw [h, mul_add]
  simp only [← mul_assoc, hu, one_mul]
  abel

include C in
/-- `du(ζ^#) = u ι(ζ)`. -/
theorem mvfderiv_fU_fund (b₀ : B) {p : P} (hp : Pb.proj p ∈ Pb.nbhd b₀) (ζ : E3) :
    mvfderiv (I.prod (𝓡 3)) (Pb.fU b₀) p (Pb.fund ζ p) = Pb.fU b₀ p * ι3 ζ := by
  rw [C.mvfderiv_fU b₀ hp, C.vert, Pb.mfderiv_proj_fund]
  simp [pot]

include C in
/-- `du(liftB e) = 0`. -/
theorem mvfderiv_fU_liftB (b₀ : B) {p : P} (hp : Pb.proj p ∈ Pb.nbhd b₀)
    (e : Π b : B, TangentSpace I b) :
    mvfderiv (I.prod (𝓡 3)) (Pb.fU b₀) p (Pb.liftB b₀ e p) = 0 := by
  rw [C.mvfderiv_fU b₀ hp, C.conn_liftB b₀ hp, Pb.mfderiv_proj_liftB b₀ hp]
  have hu : (Pb.fib b₀ p : Quaternion ℝ) * star (Pb.fib b₀ p : Quaternion ℝ) = 1 :=
    mul_star_self_sphere _
  simp only [PrincipalS3Bundle.fU, ← mul_assoc, hu, one_mul, sub_self]

/-- **The horizontal lift** of a field `e` on `B`. -/
def hlift (b₀ : B) (e : Π b : B, TangentSpace I b) : Π p : P, TangentSpace (I.prod (𝓡 3)) p :=
  fun p => Pb.liftB b₀ e p - ∑ a, ⟪C.conn p (Pb.liftB b₀ e p), qe a⟫ • Pb.fund (ζq a) p

theorem mfderiv_proj_hlift (b₀ : B) {p : P} (hp : Pb.proj p ∈ Pb.nbhd b₀)
    (e : Π b : B, TangentSpace I b) :
    mfderiv (I.prod (𝓡 3)) I Pb.proj p (C.hlift b₀ e p) = e (Pb.proj p) := by
  simp only [hlift, map_sub, map_sum, map_smul, Pb.mfderiv_proj_fund, smul_zero,
    Finset.sum_const_zero, sub_zero, Pb.mfderiv_proj_liftB b₀ hp]

/-- **The horizontal lift is horizontal**: `ω(hlift e) = 0`. -/
theorem conn_hlift (b₀ : B) (p : P) (e : Π b : B, TangentSpace I b) :
    C.conn p (C.hlift b₀ e p) = 0 := by
  simp only [hlift, map_sub, map_sum, map_smul, C.vert, ι3_ζq]
  rw [sum_inner_qe (C.im p _), sub_self]

/-- `du(hlift e) = −A(e) u`. -/
theorem mvfderiv_fU_hlift (b₀ : B) {p : P} (hp : Pb.proj p ∈ Pb.nbhd b₀)
    (e : Π b : B, TangentSpace I b) :
    mvfderiv (I.prod (𝓡 3)) (Pb.fU b₀) p (C.hlift b₀ e p) =
      -(C.pot b₀ (Pb.proj p) (e (Pb.proj p)) * Pb.fU b₀ p) := by
  rw [C.mvfderiv_fU b₀ hp, C.conn_hlift, C.mfderiv_proj_hlift b₀ hp, mul_zero, zero_sub]

end S3Connection

end Horizontal

section Smooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type} [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B]
  {P : Type} [TopologicalSpace P] [ChartedSpace (ModelProd H E3) P] [IsManifold (I.prod (𝓡 3)) ∞ P]
  {Pb : PrincipalS3Bundle I B P} (C : S3Connection Pb)

namespace PrincipalS3Bundle

variable (Pb)

theorem contMDiffAt_fund (ζ : E3) (p : P) :
    ContMDiffAt (I.prod (𝓡 3)) (I.prod (𝓡 3)).tangent ∞ (T% (Pb.fund ζ)) p :=
  contMDiffAt_mfderivField' (Φ := Pb.ract) (n := fun _ => (1 : S3)) (ζ := fun _ => ζ)
    (Pb.ract_smooth _) contMDiffAt_const (Eventually.of_forall Pb.ract_one) contMDiffAt_const

theorem contMDiffAt_liftB (b₀ : B) {p : P} (hp : Pb.proj p ∈ Pb.nbhd b₀)
    {e : Π b : B, TangentSpace I b} (he : ContMDiffAt I I.tangent ∞ (T% e) (Pb.proj p)) :
    ContMDiffAt (I.prod (𝓡 3)) (I.prod (𝓡 3)).tangent ∞ (T% (Pb.liftB b₀ e)) p := by
  have hsec : ContMDiffAt I (I.prod (𝓡 3)) ∞ (Pb.sec b₀) (Pb.proj p) :=
    (Pb.sec_smooth b₀).contMDiffAt ((Pb.nbhd_open b₀).mem_nhds hp)
  have hfib : ContMDiffAt (I.prod (𝓡 3)) (𝓡 3) ∞ (Pb.fib b₀) p :=
    (Pb.fib_smooth b₀).contMDiffAt (Pb.nhds_preimage b₀ hp)
  have hΦ : ContMDiffAt ((I.prod (𝓡 3)).prod I) (I.prod (𝓡 3)) ∞ (uncurry (Pb.trivΦ b₀))
      (p, Pb.proj p) := by
    have h1 : ContMDiffAt ((I.prod (𝓡 3)).prod I) ((I.prod (𝓡 3)).prod (𝓡 3)) ∞
        (fun z : P × B => (Pb.sec b₀ z.2, Pb.fib b₀ z.1)) (p, Pb.proj p) :=
      (ContMDiffAt.comp (x := (p, Pb.proj p)) (g := Pb.sec b₀) (f := Prod.snd) hsec
        contMDiffAt_snd).prodMk
        (ContMDiffAt.comp (x := (p, Pb.proj p)) (g := Pb.fib b₀) (f := Prod.fst) hfib contMDiffAt_fst)
    exact (Pb.ract_smooth _).comp _ h1
  have hnp : ∀ᶠ x in 𝓝 p, Pb.trivΦ b₀ x (Pb.proj x) = x := by
    filter_upwards [Pb.nhds_preimage b₀ hp] with x hx using Pb.trivΦ_proj b₀ hx
  exact contMDiffAt_mfderivField' (Φ := Pb.trivΦ b₀) (n := Pb.proj) (ζ := fun x => e (Pb.proj x))
    hΦ (Pb.proj_smooth p) hnp (he.comp p (Pb.proj_smooth p))

end PrincipalS3Bundle

namespace S3Connection

theorem contMDiffAt_conn_coef (b₀ : B) {p : P} (hp : Pb.proj p ∈ Pb.nbhd b₀)
    {e : Π b : B, TangentSpace I b} (he : ContMDiffAt I I.tangent ∞ (T% e) (Pb.proj p))
    (a : Fin 3) :
    ContMDiffAt (I.prod (𝓡 3)) 𝓘(ℝ) ∞ (fun x => ⟪C.conn x (Pb.liftB b₀ e x), qe a⟫) p := by
  have hω := C.smooth _ p (Pb.contMDiffAt_liftB b₀ hp he)
  have h := ((innerSL ℝ (qe a)).contMDiff.contMDiffAt).comp p hω
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
  simp only [comp_apply, innerSL_apply_apply, real_inner_comm]

/-- **The horizontal lift is smooth** where `e` is. -/
theorem contMDiffAt_hlift (b₀ : B) {p : P} (hp : Pb.proj p ∈ Pb.nbhd b₀)
    {e : Π b : B, TangentSpace I b} (he : ContMDiffAt I I.tangent ∞ (T% e) (Pb.proj p)) :
    ContMDiffAt (I.prod (𝓡 3)) (I.prod (𝓡 3)).tangent ∞ (T% (C.hlift b₀ e)) p := by
  have hL := Pb.contMDiffAt_liftB b₀ hp he
  have hS : ContMDiffAt (I.prod (𝓡 3)) (I.prod (𝓡 3)).tangent ∞
      (T% (fun x => ∑ a, ⟪C.conn x (Pb.liftB b₀ e x), qe a⟫ • Pb.fund (ζq a) x)) p :=
    ContMDiffAt.sum_section fun a _ =>
      (C.contMDiffAt_conn_coef b₀ hp he a).smul_section (Pb.contMDiffAt_fund (ζq a) p)
  exact hL.sub_section hS

end S3Connection

end Smooth

end

end ExoticSpheres8And10
