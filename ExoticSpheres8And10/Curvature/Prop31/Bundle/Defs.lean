/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Main.RoundSphere
import ExoticSpheres8And10.Geometry.FrameFields
import ExoticSpheres8And10.Curvature.HLYModel.Frame

/-! # Principal `S³`-bundles with connection, over a base possibly with boundary

The structures behind the general [GG] `fact:prop31` ([HLY] Prop. 3.1). They are modelled on
`StarBundle`, since Mathlib has no smooth principal bundles.

* `PrincipalS3Bundle I B P`: a smooth right `S³`-action on `P` and a smooth projection
  `P → B`, invariant under the action, with local sections and fibre coordinates. Here `B` is a
  manifold with corners (model `I`, boundary allowed) and `P` is modelled on `I.prod (𝓡 3)`.
* `fund ζ`: the fundamental field of `ζ ∈ T₁S³ = ℝ³`, `p ↦ d(ract p)₁ ζ`.
* `S3Connection`: an `ℍ`-valued 1-form `ω` (`conn`) on `P`, imaginary, smooth, with `ω(ζ^#) = ι ζ` and
  `R_q^*ω = q̄ ω q`.
* `connMetric g φ ε`: [GG]'s `G_ε = π^*g_B + ε e^{εφ} Q(ω, ω)`, with `Q = ⟪·,·⟫` on `ℍ`.
-/

open RiemannianGeometry VectorField Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Module

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Defs

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (B : Type) [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B]
  (P : Type) [TopologicalSpace P] [ChartedSpace (ModelProd H E3) P] [IsManifold (I.prod (𝓡 3)) ∞ P]

/-- **A principal right `S³`-bundle** `P → B`. -/
structure PrincipalS3Bundle where
  proj : P → B
  ract : P → S3 → P
  proj_smooth : ContMDiff (I.prod (𝓡 3)) I ∞ proj
  ract_smooth : ContMDiff ((I.prod (𝓡 3)).prod (𝓡 3)) (I.prod (𝓡 3)) ∞ (uncurry ract)
  ract_one : ∀ p, ract p 1 = p
  ract_mul : ∀ p q q', ract (ract p q) q' = ract p (q * q')
  proj_ract : ∀ p q, proj (ract p q) = proj p
  /-- trivialising neighbourhoods -/
  nbhd : B → Set B
  nbhd_open : ∀ b₀, IsOpen (nbhd b₀)
  mem_nbhd : ∀ b₀, b₀ ∈ nbhd b₀
  /-- local sections -/
  sec : B → B → P
  sec_smooth : ∀ b₀, ContMDiffOn I (I.prod (𝓡 3)) ∞ (sec b₀) (nbhd b₀)
  proj_sec : ∀ b₀, ∀ b ∈ nbhd b₀, proj (sec b₀ b) = b
  /-- fibre coordinates -/
  fib : B → P → S3
  fib_smooth : ∀ b₀, ContMDiffOn (I.prod (𝓡 3)) (𝓡 3) ∞ (fib b₀) (proj ⁻¹' nbhd b₀)
  sec_fib : ∀ b₀ p, proj p ∈ nbhd b₀ → ract (sec b₀ (proj p)) (fib b₀ p) = p
  fib_sec : ∀ b₀, ∀ b ∈ nbhd b₀, ∀ u, fib b₀ (ract (sec b₀ b) u) = u

variable {I B P}

namespace PrincipalS3Bundle

variable (Pb : PrincipalS3Bundle I B P)

/-- **The fundamental field** of `ζ ∈ T₁S³`: `ζ^#(p) = d(ract p)₁ ζ`. -/
def fund (ζ : E3) : Π p : P, TangentSpace (I.prod (𝓡 3)) p :=
  mfderivField (I := I.prod (𝓡 3)) (J := 𝓡 3) Pb.ract 1 ζ

theorem contMDiff_fund (ζ : E3) :
    ContMDiff (I.prod (𝓡 3)) (I.prod (𝓡 3)).tangent ((2 : ℕ∞) : ℕ∞ω) (T% (Pb.fund ζ)) :=
  contMDiff_mfderivField Pb.ract Pb.ract_smooth 1 Pb.ract_one ζ

theorem contMDiff_ract (q : S3) : ContMDiff (I.prod (𝓡 3)) (I.prod (𝓡 3)) ∞ (Pb.ract · q) :=
  Pb.ract_smooth.comp (contMDiff_id.prodMk contMDiff_const)

theorem contMDiff_ract_left (p : P) : ContMDiff (𝓡 3) (I.prod (𝓡 3)) ∞ (Pb.ract p) :=
  Pb.ract_smooth.comp (contMDiff_const.prodMk contMDiff_id)

/-- The fibre coordinate is equivariant: `fib(p q) = fib(p) q`. -/
theorem fib_ract (b₀ : B) {p : P} (hp : Pb.proj p ∈ Pb.nbhd b₀) (q : S3) :
    Pb.fib b₀ (Pb.ract p q) = Pb.fib b₀ p * q := by
  conv_lhs => rw [← Pb.sec_fib b₀ p hp, Pb.ract_mul]
  exact Pb.fib_sec b₀ _ hp _

end PrincipalS3Bundle

/-- **A connection** on `P`: an imaginary `ℍ`-valued 1-form with `ω(ζ^#) = ι ζ` and
`R_q^*ω = q̄ ω q`. -/
structure S3Connection (Pb : PrincipalS3Bundle I B P) where
  conn : Π p : P, TangentSpace (I.prod (𝓡 3)) p →L[ℝ] Quaternion ℝ
  im : ∀ p v, (conn p v).re = 0
  smooth : ∀ (V : Π p : P, TangentSpace (I.prod (𝓡 3)) p) (x : P),
    ContMDiffAt (I.prod (𝓡 3)) (I.prod (𝓡 3)).tangent ∞ (T% V) x →
      ContMDiffAt (I.prod (𝓡 3)) 𝓘(ℝ, Quaternion ℝ) ∞ (fun p => conn p (V p)) x
  vert : ∀ p (ζ : E3), conn p (Pb.fund ζ p) = ι3 ζ
  equiv : ∀ p (q : S3) (v : TangentSpace (I.prod (𝓡 3)) p),
    conn (Pb.ract p q) (mfderiv (I.prod (𝓡 3)) (I.prod (𝓡 3)) (Pb.ract · q) p v) =
      star (q : Quaternion ℝ) * conn p v * q

namespace S3Connection

variable {Pb : PrincipalS3Bundle I B P} (C : S3Connection Pb)

/-- **The connection metric** `G_ε = π^*g_B + ε e^{εφ} Q(ω, ω)`. -/
def connMetric (g : Π b : B, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) (φ : B → ℝ)
    (ε : ℝ) : Π p : P, TangentSpace (I.prod (𝓡 3)) p →L[ℝ] TangentSpace (I.prod (𝓡 3)) p →L[ℝ] ℝ :=
  fun p =>
    letI : NormedAddCommGroup (TangentSpace (I.prod (𝓡 3)) p) :=
      inferInstanceAs (NormedAddCommGroup (E × E3))
    letI : NormedSpace ℝ (TangentSpace (I.prod (𝓡 3)) p) := inferInstanceAs (NormedSpace ℝ (E × E3))
    letI : NormedAddCommGroup (TangentSpace I (Pb.proj p)) := inferInstanceAs (NormedAddCommGroup E)
    letI : NormedSpace ℝ (TangentSpace I (Pb.proj p)) := inferInstanceAs (NormedSpace ℝ E)
    bil (g (Pb.proj p)) (mfderiv (I.prod (𝓡 3)) I Pb.proj p) +
      (ε * Real.exp (ε * φ (Pb.proj p))) • bil (ipL (Quaternion ℝ)) (C.conn p)

theorem connMetric_apply (g : Π b : B, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
    (φ : B → ℝ) (ε : ℝ) (p : P) (v w : TangentSpace (I.prod (𝓡 3)) p) :
    C.connMetric g φ ε p v w =
      g (Pb.proj p) (mfderiv (I.prod (𝓡 3)) I Pb.proj p v) (mfderiv (I.prod (𝓡 3)) I Pb.proj p w) +
        ε * Real.exp (ε * φ (Pb.proj p)) * ⟪C.conn p v, C.conn p w⟫ := by
  simp only [connMetric, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, bil_apply,
    ipL_apply, smul_eq_mul]
  rfl

theorem isSymm_connMetric {g : Π b : B, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ}
    (hg : IsSymm g) (φ : B → ℝ) (ε : ℝ) : IsSymm (C.connMetric g φ ε) := fun p v w => by
  rw [C.connMetric_apply, C.connMetric_apply, hg, real_inner_comm]

end S3Connection

end Defs

end

end ExoticSpheres8And10
