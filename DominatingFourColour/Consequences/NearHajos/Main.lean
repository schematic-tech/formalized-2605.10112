import DominatingFourColour.Consequences.NearHajos.PathCycle
import DominatingFourColour.Consequences.NearHajos.Reductions

set_option maxHeartbeats 800000

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

set_option maxHeartbeats 0 in
theorem near_hajos_with_two_incident_unsplit_edges
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    (h_five_chromatic_or_more : FiveChromaticOrMore G) :
    NearHajosStrengtheningConclusion G := by
  classical
  by_cases h_complete : forall u v : V, u ≠ v -> G.Adj u v
  · have hG_eq : G = SimpleGraph.completeGraph V := by
      ext u v
      constructor
      · intro huv
        exact huv.ne
      · intro huv_ne
        exact h_complete u v huv_ne
    subst G
    exact completeGraph_near_hajos_with_two_incident_unsplit_edges_of_five_chromatic
      h_five_chromatic_or_more
  · have h_tail_data : ThirdBranchPathAndTailInducedCycleConclusion G :=
      near_hajos_path_cycle_data G h_five_chromatic_or_more
    rcases h_tail_data with ⟨D⟩
    exact D.near_hajos_with_two_incident_unsplit_edges

end Schematic.Math.GraphTheory
