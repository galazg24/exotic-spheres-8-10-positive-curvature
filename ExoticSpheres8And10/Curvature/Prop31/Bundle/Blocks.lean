/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Curvature.Prop31.Bundle.Brackets
import ExoticSpheres8And10.Curvature.Prop31.Bundle.BlockAlgebra

/-! # The connection-metric frame on `P` and its bracket table in HLY form

Data:
* a field of frames `e : Fin n → fields on B`, orthonormal on an open `U ⊆ nbhd b₀`;
* the fibre radius `r : B → ℝ`.

The frame on `P` is `X_i = hlift(e_i)`, `E_a = r⁻¹ (qe_a)^#`. Its table functions are:
* `c^B_{ijk} = g([e_i,e_j], e_k) ∘ π`;
* `Ω_{ij}^a = ⟪ū F(e_i,e_j) u, qe_a⟫`;
* `r ∘ π`;
* `ϑ_i = e_i(r)/r ∘ π`.

The horizontal lift is pointwise linear in the base field (`hlift_linear`).
**`mlieBracket_Fr`**: the bracket table of the frame is exactly `cT` on `π⁻¹(U)`.
-/

open RiemannianGeometry VectorField Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Module

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Lin

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type} [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B]
  {P : Type} [TopologicalSpace P] [ChartedSpace (ModelProd H E3) P] [IsManifold (I.prod (𝓡 3)) ∞ P]
  {Pb : PrincipalS3Bundle I B P} (C : S3Connection Pb)

namespace S3Connection

/-- **The horizontal lift is pointwise linear** in the base field. -/
theorem hlift_linear (b₀ : B) {ι : Type*} (s : Finset ι) (p : P)
    (e : Π b : B, TangentSpace I b) (f : ι → Π b : B, TangentSpace I b) (c : ι → ℝ)
    (he : e (Pb.proj p) = ∑ k ∈ s, c k • f k (Pb.proj p)) :
    C.hlift b₀ e p = ∑ k ∈ s, c k • C.hlift b₀ (f k) p := by
  have hL : Pb.liftB b₀ e p = ∑ k ∈ s, c k • Pb.liftB b₀ (f k) p := by
    show mfderiv I (I.prod (𝓡 3)) (Pb.trivΦ b₀ p) (Pb.proj p) (e (Pb.proj p)) = _
    rw [he, map_sum]
    simp only [map_smul]
    rfl
  simp only [hlift]
  rw [hL, map_sum]
  simp only [map_smul, smul_sub, Finset.smul_sum, smul_smul, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [sum_inner, Finset.sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [real_inner_smul_left]

end S3Connection

end Lin

section Table

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type} [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B]
  {P : Type} [TopologicalSpace P] [ChartedSpace (ModelProd H E3) P] [IsManifold (I.prod (𝓡 3)) ∞ P]
  {Pb : PrincipalS3Bundle I B P} (C : S3Connection Pb) {n : ℕ}

namespace S3Connection

/-- **The connection-metric frame** on `P`: `X_i = hlift(e_i)`, `E_a = r⁻¹ (qe_a)^#`. -/
def Fr (b₀ : B) (e : Fin n → Π b : B, TangentSpace I b) (r : B → ℝ) :
    Fin n ⊕ Fin 3 → Π p : P, TangentSpace (I.prod (𝓡 3)) p :=
  Sum.elim (fun i => C.hlift b₀ (e i)) (fun a => vfield (Pb := Pb) r a)

/-- `c^B_{ijk} ∘ π`. -/
def tcB (g : Π b : B, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
    (e : Fin n → Π b : B, TangentSpace I b) (i j k : Fin n) (p : P) : ℝ :=
  g (Pb.proj p) (mlieBracket I (e i) (e j) (Pb.proj p)) (e k (Pb.proj p))

/-- `Ω_{ij}^a = ⟪ū F(e_i, e_j) u, qe_a⟫`. -/
def tΩ (b₀ : B) (e : Fin n → Π b : B, TangentSpace I b) (i j : Fin n) (a : Fin 3) (p : P) : ℝ :=
  ⟪star (Pb.fU b₀ p) * C.curvF b₀ (e i) (e j) (Pb.proj p) * Pb.fU b₀ p, qe a⟫

/-- `r ∘ π`. -/
def trf (r : B → ℝ) (p : P) : ℝ := r (Pb.proj p)

/-- `ϑ_i = e_i(r)/r ∘ π`. -/
def tϑ (r : B → ℝ) (e : Fin n → Π b : B, TangentSpace I b) (i : Fin n) (p : P) : ℝ :=
  mvfderiv I r (Pb.proj p) (e i (Pb.proj p)) / r (Pb.proj p)

variable {r : B → ℝ} {g : Π b : B, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ}
  {e : Fin n → Π b : B, TangentSpace I b} {U : Set B}

theorem vfield_eq_smul_fund (hr0 : ∀ b, r b ≠ 0) (a : Fin 3) (p : P) :
    Pb.fund (ζq a) p = r (Pb.proj p) • vfield (Pb := Pb) r a p := by
  rw [vfield, smul_smul, mul_inv_cancel₀ (hr0 _), one_smul]

/-- **The bracket table of the frame is HLY's `cT`** on `π⁻¹(U)`. -/
theorem mlieBracket_Fr (hr : ContMDiff I 𝓘(ℝ) ∞ r) (hr0 : ∀ b, r b ≠ 0) (b₀ : B)
    (hUo : IsOpen U) (hUn : U ⊆ Pb.nbhd b₀)
    (he : ∀ i, ∀ b ∈ U, ContMDiffAt I I.tangent ∞ (T% (e i)) b)
    (hspanB : ∀ b ∈ U, ∀ w : TangentSpace I b, w = ∑ k, g b w (e k b) • e k b)
    {y : P} (hy : Pb.proj y ∈ U) (α β : Fin n ⊕ Fin 3) :
    mlieBracket (I.prod (𝓡 3)) (C.Fr b₀ e r α) (C.Fr b₀ e r β) y =
      ∑ γ, cT (tcB (Pb := Pb) g e) (C.tΩ b₀ e) (trf (Pb := Pb) r) (tϑ (Pb := Pb) r e) α β γ y •
        C.Fr b₀ e r γ y := by
  have hp : Pb.proj y ∈ Pb.nbhd b₀ := hUn hy
  have heev : ∀ i, ∀ᶠ q in 𝓝 (Pb.proj y), ContMDiffAt I I.tangent ∞ (T% (e i)) q := fun i => by
    filter_upwards [hUo.mem_nhds hy] with q hq using he i q hq
  rw [Fintype.sum_sum_type]
  rcases α with i | a <;> rcases β with j | b
  · -- horizontal–horizontal
    show mlieBracket (I.prod (𝓡 3)) (C.hlift b₀ (e i)) (C.hlift b₀ (e j)) y = _
    rw [C.mlieBracket_hlift b₀ hp (heev i) (heev j)]
    have hlin := C.hlift_linear b₀ Finset.univ y (mlieBracket I (e i) (e j)) e
      (fun k => g (Pb.proj y) (mlieBracket I (e i) (e j) (Pb.proj y)) (e k (Pb.proj y)))
      (hspanB _ hy _)
    rw [hlin]
    simp only [cT, Fr, Sum.elim_inl, Sum.elim_inr, tΩ, trf]
    rw [sub_eq_add_neg]
    congr 1
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [vfield_eq_smul_fund hr0, smul_smul, ← neg_smul]
    congr 1
    ring
  · -- horizontal–vertical
    show mlieBracket (I.prod (𝓡 3)) (C.hlift b₀ (e i)) (vfield (Pb := Pb) r b) y = _
    rw [C.mlieBracket_hlift_vfield hr hr0 b₀ hp (heev i) b]
    simp only [cT, Fr, Sum.elim_inr, zero_smul, Finset.sum_const_zero, zero_add, tϑ]
    rw [Finset.sum_eq_single b]
    · simp [kron]
    · intro c _ hc; simp [kron, Ne.symm hc]
    · simp
  · -- vertical–horizontal
    show mlieBracket (I.prod (𝓡 3)) (vfield (Pb := Pb) r a) (C.hlift b₀ (e j)) y = _
    rw [mlieBracket_swap_apply, C.mlieBracket_hlift_vfield hr hr0 b₀ hp (heev j) a]
    simp only [cT, Fr, Sum.elim_inr, zero_smul, Finset.sum_const_zero, zero_add, tϑ]
    rw [Finset.sum_eq_single a]
    · simp [kron]
    · intro c _ hc; simp [kron, Ne.symm hc]
    · simp
  · -- vertical–vertical
    show mlieBracket (I.prod (𝓡 3)) (vfield (Pb := Pb) r a) (vfield (Pb := Pb) r b) y = _
    rw [C.mlieBracket_vfield hr hr0 b₀ hp a b]
    simp only [cT, Fr, Sum.elim_inr, zero_smul, Finset.sum_const_zero, zero_add, trf]

end S3Connection

end Table

section Orth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type} [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B]
  {P : Type} [TopologicalSpace P] [ChartedSpace (ModelProd H E3) P] [IsManifold (I.prod (𝓡 3)) ∞ P]
  {Pb : PrincipalS3Bundle I B P} (C : S3Connection Pb) {n : ℕ}

/-- **An orthonormal family of `dim` vectors spans**, at one point. -/
theorem span_of_orthonormal_at {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E'] {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
    {g : Π x : M, TangentSpace J x →L[ℝ] TangentSpace J x →L[ℝ] ℝ}
    {ι : Type*} [Fintype ι] [DecidableEq ι] {F : ι → Π y : M, TangentSpace J y}
    (hp : IsPosDef g) {y : M} (horth : ∀ α β, g y (F α y) (F β y) = kron α β)
    (hcard : Fintype.card ι = Module.finrank ℝ E') (w : TangentSpace J y) :
    w = ∑ γ, g y w (F γ y) • F γ y := by
  have : FiniteDimensional ℝ (TangentSpace J y) := inferInstanceAs (FiniteDimensional ℝ E')
  have hli : LinearIndependent ℝ fun γ => F γ y := by
    rw [Fintype.linearIndependent_iff]
    intro a ha δ
    have := congrArg (fun v => g y v (F δ y)) ha
    simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      horth, smul_eq_mul, map_zero, ContinuousLinearMap.zero_apply] at this
    rw [sum_smul_kron (V := ℝ) a δ] at this
    exact this
  have hspan : Submodule.span ℝ (Set.range fun γ => F γ y) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hli, hcard]
    rfl
  set v := w - ∑ γ, g y w (F γ y) • F γ y with hv
  have horthv : ∀ δ, g y v (F δ y) = 0 := fun δ => by
    simp only [hv, map_sub, map_sum, map_smul, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, horth, smul_eq_mul]
    rw [sum_smul_kron (V := ℝ) (fun γ => g y w (F γ y)) δ, sub_self]
  have hmem : v ∈ Submodule.span ℝ (Set.range fun γ => F γ y) := by rw [hspan]; trivial
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hmem
  have hvv : g y v v = 0 := by
    conv_lhs => arg 2; rw [← hb]
    simp only [map_sum, map_smul, smul_eq_mul, horthv, mul_zero, Finset.sum_const_zero]
  by_contra hne
  have h0 : v ≠ 0 := fun h => hne (sub_eq_zero.1 h)
  exact absurd hvv (hp y v h0).ne'

namespace S3Connection

variable {r : B → ℝ} {g : Π b : B, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ}
  {e : Fin n → Π b : B, TangentSpace I b} {U : Set B} {φ : B → ℝ} {ε : ℝ}

theorem conn_vfield (r : B → ℝ) (a : Fin 3) (p : P) :
    C.conn p (vfield (Pb := Pb) r a p) = (r (Pb.proj p))⁻¹ • qe a := by
  rw [vfield, map_smul, C.vert, ι3_ζq]

theorem kron_inl {α β : Type*} [DecidableEq α] [DecidableEq β] (i j : α) :
    kron (Sum.inl i : α ⊕ β) (Sum.inl j) = kron i j := by
  simp [kron, Sum.inl.injEq]

theorem kron_inr {α β : Type*} [DecidableEq α] [DecidableEq β] (a b : β) :
    kron (Sum.inr a : α ⊕ β) (Sum.inr b) = kron a b := by
  simp [kron, Sum.inr.injEq]

theorem kron_inl_inr {α β : Type*} [DecidableEq α] [DecidableEq β] (i : α) (a : β) :
    kron (Sum.inl i : α ⊕ β) (Sum.inr a) = 0 := by simp [kron]

theorem kron_inr_inl {α β : Type*} [DecidableEq α] [DecidableEq β] (i : α) (a : β) :
    kron (Sum.inr a : α ⊕ β) (Sum.inl i) = 0 := by simp [kron]

/-- **The frame is `G_ε`-orthonormal** over `U`, when `r² = ε e^{εφ}`. -/
theorem connMetric_Fr (hr0 : ∀ b, r b ≠ 0) (hr2 : ∀ b, r b ^ 2 = ε * Real.exp (ε * φ b))
    (b₀ : B) (hUn : U ⊆ Pb.nbhd b₀) (horthB : ∀ b ∈ U, ∀ i j, g b (e i b) (e j b) = kron i j)
    {y : P} (hy : Pb.proj y ∈ U) (α β : Fin n ⊕ Fin 3) :
    C.connMetric g φ ε y (C.Fr b₀ e r α y) (C.Fr b₀ e r β y) = kron α β := by
  have hp := hUn hy
  rw [C.connMetric_apply]
  rcases α with i | a <;> rcases β with j | b
  · simp only [Fr, Sum.elim_inl, C.mfderiv_proj_hlift b₀ hp, C.conn_hlift, inner_zero_left,
      mul_zero, add_zero, kron_inl]
    exact horthB _ hy i j
  · simp only [Fr, Sum.elim_inl, Sum.elim_inr, C.mfderiv_proj_hlift b₀ hp, mfderiv_proj_vfield,
      map_zero, C.conn_hlift, inner_zero_left, mul_zero, add_zero, kron_inl_inr]
  · simp only [Fr, Sum.elim_inl, Sum.elim_inr, C.mfderiv_proj_hlift b₀ hp, mfderiv_proj_vfield,
      map_zero, ContinuousLinearMap.zero_apply, C.conn_hlift, inner_zero_right, mul_zero,
      zero_add, kron_inr_inl]
  · simp only [Fr, Sum.elim_inr, mfderiv_proj_vfield, map_zero, ContinuousLinearMap.zero_apply,
      zero_add, C.conn_vfield, real_inner_smul_left, real_inner_smul_right, inner_qe, kron_inr]
    rw [← hr2]
    field_simp [hr0 (Pb.proj y)]

end S3Connection

end Orth

section TabSmooth

/-- `ℍ` is a star module over `ℝ` (as in `B3_Transport`, which is not imported here). -/
instance instStarModuleQuatPB : StarModule ℝ (Quaternion ℝ) :=
  ⟨fun r a => by ext <;> simp [star_trivial]⟩

theorem contMDiffAt_qmul {M' : Type*} [TopologicalSpace M'] {H' : Type*}
    [TopologicalSpace H'] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {J : ModelWithCorners ℝ E' H'} [ChartedSpace H' M'] {f h : M' → Quaternion ℝ} {x : M'}
    (hf : ContMDiffAt J 𝓘(ℝ, Quaternion ℝ) ∞ f x) (hh : ContMDiffAt J 𝓘(ℝ, Quaternion ℝ) ∞ h x) :
    ContMDiffAt J 𝓘(ℝ, Quaternion ℝ) ∞ (fun y => f y * h y) x :=
  ((ContinuousLinearMap.mul ℝ (Quaternion ℝ)).contMDiff.contMDiffAt.comp x hf).clm_apply hh

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type} [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B]
  {P : Type} [TopologicalSpace P] [ChartedSpace (ModelProd H E3) P] [IsManifold (I.prod (𝓡 3)) ∞ P]
  {Pb : PrincipalS3Bundle I B P} (C : S3Connection Pb) {n : ℕ}

namespace S3Connection

/-- `c^B_{ijk}` on the base. -/
def cBb (g : Π b : B, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
    (e : Fin n → Π b : B, TangentSpace I b) (i j k : Fin n) (b : B) : ℝ :=
  g b (mlieBracket I (e i) (e j) b) (e k b)

/-- `ϑ_i = e_i(r)/r` on the base. -/
def ϑb (r : B → ℝ) (e : Fin n → Π b : B, TangentSpace I b) (i : Fin n) (b : B) : ℝ :=
  mvfderiv I r b (e i b) / r b

theorem tcB_eq (g : Π b : B, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
    (e : Fin n → Π b : B, TangentSpace I b) (i j k : Fin n) :
    tcB (Pb := Pb) g e i j k = cBb g e i j k ∘ Pb.proj := rfl

theorem tϑ_eq (r : B → ℝ) (e : Fin n → Π b : B, TangentSpace I b) (i : Fin n) :
    tϑ (Pb := Pb) r e i = ϑb r e i ∘ Pb.proj := rfl

variable {g : Π b : B, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ}
  {e : Fin n → Π b : B, TangentSpace I b} {U : Set B} {r : B → ℝ}

theorem contMDiffAt_bracket_e (hUo : IsOpen U)
    (he : ∀ i, ∀ b ∈ U, ContMDiffAt I I.tangent ∞ (T% (e i)) b) {b : B} (hb : b ∈ U)
    (i j : Fin n) :
    ContMDiffAt I I.tangent ∞ (T% (mlieBracket I (e i) (e j))) b := by
  haveI : IsManifold I (minSmoothness ℝ 2) B :=
    IsManifold.of_le (n := ∞) (by rw [minSmoothness_of_isRCLikeNormedField]; exact two_le_infty')
  have := ContMDiffAt.mlieBracket_vectorField (m := ⊤) (n := ⊤) (he i b hb) (he j b hb)
    (by simp)
  exact this

theorem contMDiffAt_cBb (hg : IsContMDiffMetricSection E ∞ g) (hUo : IsOpen U)
    (he : ∀ i, ∀ b ∈ U, ContMDiffAt I I.tangent ∞ (T% (e i)) b) {b : B} (hb : b ∈ U)
    (i j k : Fin n) : ContMDiffAt I 𝓘(ℝ) ∞ (cBb g e i j k) b :=
  contMDiffAt_pairing (hg b) (contMDiffAt_bracket_e hUo he hb i j) (he k b hb)

/-- `b ↦ df_b(V_b)` is smooth for smooth `f` near `b` and smooth `V`. -/
theorem contMDiffAt_mvfderiv_field {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {f : B → F'} {V : Π b : B, TangentSpace I b} {b : B}
    (hf : ∀ᶠ b' in 𝓝 b, ContMDiffAt I 𝓘(ℝ, F') ∞ f b')
    (hV : ContMDiffAt I I.tangent ∞ (T% V) b) :
    ContMDiffAt I 𝓘(ℝ, F') ∞ (fun b' => mvfderiv I f b' (V b')) b := by
  obtain ⟨u, hu, huo, hbu⟩ := mem_nhds_iff.1 hf
  exact contMDiffAt_mvfderiv_apply_of_contMDiffOn huo hbu (fun y hy => (hu hy).contMDiffWithinAt)
    (by simp) hV

theorem contMDiffAt_ϑb (hr : ContMDiff I 𝓘(ℝ) ∞ r) (hr0 : ∀ b, r b ≠ 0)
    (he : ∀ i, ∀ b ∈ U, ContMDiffAt I I.tangent ∞ (T% (e i)) b) {b : B} (hb : b ∈ U)
    (i : Fin n) : ContMDiffAt I 𝓘(ℝ) ∞ (ϑb r e i) b :=
  ((contMDiffAt_mvfderiv_field (Eventually.of_forall fun b' => hr b') (he i b hb)).mul
    ((hr b).inv₀ (hr0 b))).congr_of_eventuallyEq
    (Eventually.of_forall fun b' => by simp only [ϑb, div_eq_mul_inv]; rfl)

include C in
theorem contMDiffAt_curvF (b₀ : B) (hUo : IsOpen U) (hUn : U ⊆ Pb.nbhd b₀)
    (he : ∀ i, ∀ b ∈ U, ContMDiffAt I I.tangent ∞ (T% (e i)) b) {b : B} (hb : b ∈ U)
    (i j : Fin n) : ContMDiffAt I 𝓘(ℝ, Quaternion ℝ) ∞ (C.curvF b₀ (e i) (e j)) b := by
  have hP : ∀ (V : Π b : B, TangentSpace I b),
      (∀ b' ∈ U, ContMDiffAt I I.tangent ∞ (T% V) b') →
        ∀ᶠ b' in 𝓝 b, ContMDiffAt I 𝓘(ℝ, Quaternion ℝ) ∞ (C.potE b₀ V) b' := fun V hV => by
    filter_upwards [hUo.mem_nhds hb] with b' hb' using C.contMDiffAt_potE b₀ (hUn hb') (hV b' hb')
  have hbr : ∀ b' ∈ U, ContMDiffAt I I.tangent ∞ (T% (mlieBracket I (e i) (e j))) b' :=
    fun b' hb' => contMDiffAt_bracket_e hUo he hb' i j
  have h1 := contMDiffAt_mvfderiv_field (hP (e j) (he j)) (he i b hb)
  have h2 := contMDiffAt_mvfderiv_field (hP (e i) (he i)) (he j b hb)
  have h3 := (hP _ hbr).self_of_nhds
  have h4 := (hP (e i) (he i)).self_of_nhds
  have h5 := (hP (e j) (he j)).self_of_nhds
  exact ((h1.sub h2).sub h3).add ((contMDiffAt_qmul h4 h5).sub (contMDiffAt_qmul h5 h4))

theorem contMDiffAt_starL'_comp {M' : Type*} [TopologicalSpace M'] {H' : Type*}
    [TopologicalSpace H'] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {J : ModelWithCorners ℝ E' H'} [ChartedSpace H' M'] {f : M' → Quaternion ℝ} {x : M'}
    (hf : ContMDiffAt J 𝓘(ℝ, Quaternion ℝ) ∞ f x) :
    ContMDiffAt J 𝓘(ℝ, Quaternion ℝ) ∞ (fun y => star (f y)) x :=
  ((starL' ℝ : Quaternion ℝ ≃L[ℝ] Quaternion ℝ) : Quaternion ℝ →L[ℝ] Quaternion ℝ).contMDiff.contMDiffAt.comp
    x hf

theorem contMDiffAt_tΩ (b₀ : B) (hUo : IsOpen U) (hUn : U ⊆ Pb.nbhd b₀)
    (he : ∀ i, ∀ b ∈ U, ContMDiffAt I I.tangent ∞ (T% (e i)) b) {y : P} (hy : Pb.proj y ∈ U)
    (i j : Fin n) (a : Fin 3) : ContMDiffAt (I.prod (𝓡 3)) 𝓘(ℝ) ∞ (C.tΩ b₀ e i j a) y := by
  have hu := contMDiffAt_fU b₀ (hUn hy)
  have hF := (C.contMDiffAt_curvF b₀ hUo hUn he hy i j).comp y (Pb.proj_smooth y)
  have hprod := contMDiffAt_qmul (contMDiffAt_qmul (contMDiffAt_starL'_comp hu) hF) hu
  have h := ((innerSL ℝ (qe a)).contMDiff.contMDiffAt).comp y hprod
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
  simp only [tΩ, comp_apply, innerSL_apply_apply, real_inner_comm]

end S3Connection

end TabSmooth

section TabDeriv

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type} [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B]
  {P : Type} [TopologicalSpace P] [ChartedSpace (ModelProd H E3) P] [IsManifold (I.prod (𝓡 3)) ∞ P]
  {Pb : PrincipalS3Bundle I B P} (C : S3Connection Pb) {n : ℕ}

namespace S3Connection

variable {g : Π b : B, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ}
  {e : Fin n → Π b : B, TangentSpace I b} {U : Set B} {r : B → ℝ}

/-- Derivatives of base functions pulled back by `π`. -/
theorem mvfderiv_comp_proj {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] {h : B → F'}
    {y : P} (hh : MDifferentiableAt I 𝓘(ℝ, F') h (Pb.proj y))
    (v : TangentSpace (I.prod (𝓡 3)) y) :
    mvfderiv (I.prod (𝓡 3)) (h ∘ Pb.proj) y v =
      mvfderiv I h (Pb.proj y) (mfderiv (I.prod (𝓡 3)) I Pb.proj y v) :=
  mvfderiv_comp_apply hh (Pb.mdiffAt_proj y) v

theorem mvfderiv_comp_proj_Fr_H {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {h : B → F'} (b₀ : B) {y : P} (hy : Pb.proj y ∈ Pb.nbhd b₀)
    (hh : MDifferentiableAt I 𝓘(ℝ, F') h (Pb.proj y)) (k : Fin n) :
    mvfderiv (I.prod (𝓡 3)) (h ∘ Pb.proj) y (C.Fr b₀ e r (.inl k) y) =
      mvfderiv I h (Pb.proj y) (e k (Pb.proj y)) := by
  rw [mvfderiv_comp_proj hh]
  show mvfderiv I h (Pb.proj y) (mfderiv (I.prod (𝓡 3)) I Pb.proj y (C.hlift b₀ (e k) y)) = _
  rw [C.mfderiv_proj_hlift b₀ hy]

theorem mvfderiv_comp_proj_Fr_V {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {h : B → F'} (b₀ : B) {y : P} (hh : MDifferentiableAt I 𝓘(ℝ, F') h (Pb.proj y)) (a : Fin 3) :
    mvfderiv (I.prod (𝓡 3)) (h ∘ Pb.proj) y (C.Fr b₀ e r (.inr a) y) = 0 := by
  rw [mvfderiv_comp_proj hh]
  show mvfderiv I h (Pb.proj y) (mfderiv (I.prod (𝓡 3)) I Pb.proj y (vfield (Pb := Pb) r a y)) = 0
  rw [mfderiv_proj_vfield, map_zero]

theorem cBb_anti (i j l : Fin n) (b : B) : cBb g e j i l b = -cBb g e i j l b := by
  simp only [cBb]
  rw [mlieBracket_swap_apply (V := e j), map_neg, ContinuousLinearMap.neg_apply]

theorem curvF_anti (b₀ : B) (e₁ e₂ : Π b : B, TangentSpace I b) (b : B) :
    C.curvF b₀ e₂ e₁ b = -C.curvF b₀ e₁ e₂ b := by
  have hp : C.pot b₀ b (mlieBracket I e₂ e₁ b) = -C.pot b₀ b (mlieBracket I e₁ e₂ b) := by
    rw [mlieBracket_swap_apply, pot, pot, map_neg, map_neg]
  simp only [curvF, hp]
  noncomm_ring

theorem tΩ_anti (b₀ : B) (i j : Fin n) (a : Fin 3) (y : P) :
    C.tΩ b₀ e j i a y = -C.tΩ b₀ e i j a y := by
  simp only [tΩ, C.curvF_anti b₀ (e i) (e j), mul_neg, neg_mul, inner_neg_left]

/-- **The vertical derivative of `Ω`**: `E_a(Ω_{ij}^c) = r⁻¹ Σ_d Ω_{ij}^d cst_{dac}`. -/
theorem mvfderiv_tΩ_V (hr : ContMDiff I 𝓘(ℝ) ∞ r) (hr0 : ∀ b, r b ≠ 0) (b₀ : B)
    (hUo : IsOpen U) (hUn : U ⊆ Pb.nbhd b₀)
    (he : ∀ i, ∀ b ∈ U, ContMDiffAt I I.tangent ∞ (T% (e i)) b) {y : P} (hy : Pb.proj y ∈ U)
    (i j : Fin n) (a c : Fin 3) :
    mvfderiv (I.prod (𝓡 3)) (C.tΩ b₀ e i j c) y (C.Fr b₀ e r (.inr a) y) =
      (trf (Pb := Pb) r y)⁻¹ * ∑ d, C.tΩ b₀ e i j d y * Prop31Algebra.cst d a c := by
  have hp := hUn hy
  set Fb := C.curvF b₀ (e i) (e j)
  have hFd : MDifferentiableAt I 𝓘(ℝ, Quaternion ℝ) Fb (Pb.proj y) :=
    (C.contMDiffAt_curvF b₀ hUo hUn he hy i j).mdifferentiableAt (by simp)
  have hud : MDifferentiableAt (I.prod (𝓡 3)) 𝓘(ℝ, Quaternion ℝ) (Pb.fU b₀) y :=
    (contMDiffAt_fU b₀ hp).mdifferentiableAt (by simp)
  have hsd : MDifferentiableAt (I.prod (𝓡 3)) 𝓘(ℝ, Quaternion ℝ) (fun x => star (Pb.fU b₀ x)) y :=
    ((starL' ℝ : Quaternion ℝ ≃L[ℝ] Quaternion ℝ) : Quaternion ℝ →L[ℝ] Quaternion ℝ).mdifferentiableAt.comp y hud
  have hFπ : MDifferentiableAt (I.prod (𝓡 3)) 𝓘(ℝ, Quaternion ℝ) (fun x => Fb (Pb.proj x)) y :=
    hFd.comp y (Pb.mdiffAt_proj y)
  set W : P → Quaternion ℝ := fun x => star (Pb.fU b₀ x) * Fb (Pb.proj x) * Pb.fU b₀ x
  have hWd : MDifferentiableAt (I.prod (𝓡 3)) 𝓘(ℝ, Quaternion ℝ) W y := (hsd.mul hFπ).mul hud
  have hΩ : C.tΩ b₀ e i j c = ⇑(innerSL ℝ (qe c)) ∘ W := by
    funext x; simp only [tΩ, comp_apply, innerSL_apply_apply, real_inner_comm, W, Fb]
  set v := C.Fr b₀ e r (.inr a) y
  have hv : v = vfield (Pb := Pb) r a y := rfl
  have hdu : mvfderiv (I.prod (𝓡 3)) (Pb.fU b₀) y v = (r (Pb.proj y))⁻¹ • (Pb.fU b₀ y * qe a) := by
    rw [hv]; exact C.mvfderiv_fU_vfield b₀ hp r a
  have hds : mvfderiv (I.prod (𝓡 3)) (fun x => star (Pb.fU b₀ x)) y v =
      star (mvfderiv (I.prod (𝓡 3)) (Pb.fU b₀) y v) :=
    mvfderiv_clm_comp ((starL' ℝ : Quaternion ℝ ≃L[ℝ] Quaternion ℝ) : Quaternion ℝ →L[ℝ] Quaternion ℝ)
      hud v
  have hdF : mvfderiv (I.prod (𝓡 3)) (fun x => Fb (Pb.proj x)) y v = 0 :=
    C.mvfderiv_comp_proj_Fr_V (h := Fb) b₀ hFd a
  have hdW : mvfderiv (I.prod (𝓡 3)) W y v =
      (r (Pb.proj y))⁻¹ • (star (qe a) * W y + W y * qe a) := by
    show mvfderiv (I.prod (𝓡 3)) (fun x => (star (Pb.fU b₀ x) * Fb (Pb.proj x)) * Pb.fU b₀ x) y v = _
    rw [mvfderiv_mul_apply (p := fun x => star (Pb.fU b₀ x) * Fb (Pb.proj x)) (hsd.mul hFπ) hud,
      mvfderiv_mul_apply hsd hFπ, hds, hdF, hdu]
    simp only [mul_zero, zero_add, star_smul, star_trivial, star_mul, W]
    simp only [smul_mul_assoc, mul_smul_comm, smul_add, mul_assoc]
    abel
  rw [hΩ, mvfderiv_clm_comp _ hWd v, hdW, innerSL_apply_apply]
  -- `W` is imaginary: expand it in `qe`
  have hWre : (W y).re = 0 := by
    show (star (Pb.fU b₀ y) * Fb (Pb.proj y) * Pb.fU b₀ y).re = 0
    rw [re_star_mul_mul, C.re_curvF b₀ ((C.contMDiffAt_potE b₀ hp (he i _ hy)).mdifferentiableAt
      (by simp)) ((C.contMDiffAt_potE b₀ hp (he j _ hy)).mdifferentiableAt (by simp)), zero_mul]
  have hWexp := sum_inner_qe hWre
  have hstar : star (qe a) = -qe a := by
    have h0 := qe_re a
    ext <;> simp [Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star, h0]
  rw [hstar]
  have hcomm : -qe a * W y + W y * qe a = ∑ d, ⟪W y, qe d⟫ • (qe d * qe a - qe a * qe d) := by
    conv_lhs => rw [← hWexp]
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [mul_smul_comm, smul_mul_assoc, smul_sub, neg_mul, smul_neg]
    abel
  rw [hcomm]
  simp only [inner_smul_right, inner_sum, qe_comm, inner_qe]
  congr 1
  refine Finset.sum_congr rfl fun d _ => ?_
  have hk : ∑ x : Fin 3, Prop31Algebra.cst d a x * kron c x = Prop31Algebra.cst d a c := by
    simp only [kron_comm c]; exact sum_smul_kron (V := ℝ) _ c
  rw [hk]
  simp only [tΩ, real_inner_comm (qe d)]
  rfl

end S3Connection

end TabDeriv

section RmFr

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type} [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B]
  {P : Type} [TopologicalSpace P] [ChartedSpace (ModelProd H E3) P] [IsManifold (I.prod (𝓡 3)) ∞ P]
  {Pb : PrincipalS3Bundle I B P} (C : S3Connection Pb) {n : ℕ}

namespace S3Connection

variable {g : Π b : B, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ}
  {e : Fin n → Π b : B, TangentSpace I b} {U : Set B} {r : B → ℝ} {φ : B → ℝ} {ε : ℝ}

theorem mdiffAt_table (hgs : IsContMDiffMetricSection E ∞ g) (hr : ContMDiff I 𝓘(ℝ) ∞ r)
    (hr0 : ∀ b, r b ≠ 0) (b₀ : B) (hUo : IsOpen U) (hUn : U ⊆ Pb.nbhd b₀)
    (he : ∀ i, ∀ b ∈ U, ContMDiffAt I I.tangent ∞ (T% (e i)) b) {y : P} (hy : Pb.proj y ∈ U)
    (α β γ : Fin n ⊕ Fin 3) :
    MDifferentiableAt (I.prod (𝓡 3)) 𝓘(ℝ)
      (cT (tcB (Pb := Pb) g e) (C.tΩ b₀ e) (trf (Pb := Pb) r) (tϑ (Pb := Pb) r e) α β γ) y := by
  have hcB : ∀ i j k, MDifferentiableAt (I.prod (𝓡 3)) 𝓘(ℝ) (tcB (Pb := Pb) g e i j k) y :=
    fun i j k => ((contMDiffAt_cBb hgs hUo he hy i j k).comp y (Pb.proj_smooth y)).mdifferentiableAt
      (by simp)
  have hΩ : ∀ i j a, MDifferentiableAt (I.prod (𝓡 3)) 𝓘(ℝ) (C.tΩ b₀ e i j a) y :=
    fun i j a => (C.contMDiffAt_tΩ b₀ hUo hUn he hy i j a).mdifferentiableAt (by simp)
  have hr' : MDifferentiableAt (I.prod (𝓡 3)) 𝓘(ℝ) (trf (Pb := Pb) r) y :=
    ((hr _).comp y (Pb.proj_smooth y)).mdifferentiableAt (by simp)
  have hri : MDifferentiableAt (I.prod (𝓡 3)) 𝓘(ℝ) (fun z => (trf (Pb := Pb) r z)⁻¹) y :=
    (((hr _).comp y (Pb.proj_smooth y)).inv₀ (hr0 _)).mdifferentiableAt (by simp)
  have hϑ : ∀ i, MDifferentiableAt (I.prod (𝓡 3)) 𝓘(ℝ) (tϑ (Pb := Pb) r e i) y :=
    fun i => ((contMDiffAt_ϑb hr hr0 he hy i).comp y (Pb.proj_smooth y)).mdifferentiableAt (by simp)
  rcases α with i | a <;> rcases β with j | b <;> rcases γ with k | c <;> simp only [cT]
  · exact hcB i j k
  · exact (hr'.neg).mul (hΩ i j c)
  · exact mdifferentiableAt_const
  · exact (hϑ i).neg.mul mdifferentiableAt_const
  · exact mdifferentiableAt_const
  · exact (hϑ j).mul mdifferentiableAt_const
  · exact mdifferentiableAt_const
  · exact hri.mul mdifferentiableAt_const

/-- **`RiemannianGeometry`'s curvature of `G_ε` on the frame is the frame expression `RmF`.** -/
theorem riemannTensorAt_Fr (hsg : IsSymm g) (hpg : IsPosDef g)
    (hgs : IsContMDiffMetricSection E ∞ g) (hφ : ContMDiff I 𝓘(ℝ) ∞ φ) (hε : 0 < ε)
    (hr : ContMDiff I 𝓘(ℝ) ∞ r) (hr0 : ∀ b, r b ≠ 0)
    (hr2 : ∀ b, r b ^ 2 = ε * Real.exp (ε * φ b)) (b₀ : B) (hUo : IsOpen U)
    (hUn : U ⊆ Pb.nbhd b₀) (he : ∀ i, ∀ b ∈ U, ContMDiffAt I I.tangent ∞ (T% (e i)) b)
    (horthB : ∀ b ∈ U, ∀ i j, g b (e i b) (e j b) = kron i j)
    (hspanB : ∀ b ∈ U, ∀ w : TangentSpace I b, w = ∑ k, g b w (e k b) • e k b)
    (hn : Module.finrank ℝ E = n) {y : P} (hy : Pb.proj y ∈ U) (α β γ δ : Fin n ⊕ Fin 3) :
    riemannTensorAt (C.isSymm_connMetric hsg φ ε) (C.isPosDef_connMetric hpg φ hε).isNondegenerate
        (IsContMDiffMetricSection.of_le' (C.isContMDiffMetricSection_connMetric hgs hφ ε)
          two_le_infty_ω) y
        (C.Fr b₀ e r α y) (C.Fr b₀ e r β y) (C.Fr b₀ e r γ y) (C.Fr b₀ e r δ y) =
      RmF (tcB (Pb := Pb) g e) (C.tΩ b₀ e) (trf (Pb := Pb) r) (tϑ (Pb := Pb) r e) (C.Fr b₀ e r) y
        α β γ δ := by
  have hU' : IsOpen (Pb.proj ⁻¹' U) := hUo.preimage Pb.proj_smooth.continuous
  have hF : ∀ α, ∀ y' ∈ Pb.proj ⁻¹' U, ContMDiffAt (I.prod (𝓡 3)) (I.prod (𝓡 3)).tangent
      ((2 : ℕ∞) : ℕ∞ω) (T% (C.Fr b₀ e r α)) y' := by
    intro α y' hy'
    rcases α with i | a
    · exact (C.contMDiffAt_hlift b₀ (hUn hy') (he i _ hy')).of_le two_le_infty''
    · exact (contMDiffAt_vfield (hr _) (hr0 _) a).of_le two_le_infty''
  have horth : ∀ α β, ∀ y' ∈ Pb.proj ⁻¹' U,
      C.connMetric g φ ε y' (C.Fr b₀ e r α y') (C.Fr b₀ e r β y') = kron α β :=
    fun α β y' hy' => C.connMetric_Fr hr0 hr2 b₀ hUn horthB hy' α β
  have hcard : Fintype.card (Fin n ⊕ Fin 3) = Module.finrank ℝ (E × E3) := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Module.finrank_prod,
      finrank_euclideanSpace_fin, hn]
  have hspan : ∀ y' ∈ Pb.proj ⁻¹' U, ∀ w : TangentSpace (I.prod (𝓡 3)) y',
      w = ∑ γ, C.connMetric g φ ε y' w (C.Fr b₀ e r γ y') • C.Fr b₀ e r γ y' :=
    fun y' hy' w => span_of_orthonormal_at (C.isPosDef_connMetric hpg φ hε)
      (fun α β => horth α β y' hy') hcard w
  exact riemannTensorAt_frame_loc (C.isSymm_connMetric hsg φ ε) (C.isPosDef_connMetric hpg φ hε)
    _ hU' hy hF horth hspan
    (fun α β y' hy' => C.mlieBracket_Fr hr hr0 b₀ hUo hUn he hspanB hy' α β)
    (fun α β γ y' hy' => C.mdiffAt_table hgs hr hr0 b₀ hUo hUn he hy' α β γ) α β γ δ

end S3Connection

end RmFr

end

end ExoticSpheres8And10
