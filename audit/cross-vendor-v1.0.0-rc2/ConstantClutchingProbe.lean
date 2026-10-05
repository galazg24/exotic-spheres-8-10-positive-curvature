import ExoticSpheres8And10.Curvature.DHZ
open ExoticSpheres8And10 Module
open scoped Manifold ContDiff
noncomputable section
variable {m : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] [FiniteDimensional ℝ W] {e : W}
  [Fact (finrank ℝ (Vs e) = m + 1)]
local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1
local notation "SV" => Metric.sphere (0 : Vs e) 1

def auditConstantPolar (R : StarRep e) : PolarData (m := m) e :=
  R.polarOf (fun _ : SV => (1 : S3)) contMDiff_const (by intros; simp)

theorem auditConstantRepresentation (R : StarRep e) :
    (auditConstantPolar (m := m) R).ρ = R.ρ := rfl

theorem auditConstantAttaching (R : StarRep e) (y : SV) :
    ((((auditConstantPolar (m := m) R).sigmaV y) : Vs e) : W) = ((y : Vs e) : W) := by
  unfold auditConstantPolar
  rw [sigmaV_eq_J]
  simp

#print axioms auditConstantRepresentation
#print axioms auditConstantAttaching
