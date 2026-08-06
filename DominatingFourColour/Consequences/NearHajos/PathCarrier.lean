import DominatingFourColour.Consequences.NearHajos.PathCarrier.Resolution

namespace Schematic.Math.GraphTheory

universe u

/-- The path-carrier case of the near-Hajos strengthening. -/
theorem ThirdBranchPathAndTailInducedCycleData.tail_k4_carrier_near_hajos_with_two_incident_unsplit_edges
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G) :
    NearHajosStrengtheningConclusion G :=
  PathCarrier.resolve D

end Schematic.Math.GraphTheory
