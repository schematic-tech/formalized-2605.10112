import DominatingFourColour.Consequences.NearHajos.PathCarrier

set_option maxHeartbeats 800000

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

set_option maxHeartbeats 0 in
theorem ThirdBranchPathAndTailInducedCycleData.near_hajos_with_two_incident_unsplit_edges
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G) :
    NearHajosStrengtheningConclusion G := by
  classical
  exact D.tail_k4_carrier_near_hajos_with_two_incident_unsplit_edges

end Schematic.Math.GraphTheory
