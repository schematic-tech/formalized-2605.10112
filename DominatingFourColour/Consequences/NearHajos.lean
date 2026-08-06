import DominatingFourColour.Consequences.NearHajos.Main

set_option maxHeartbeats 800000

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

theorem near_hajos
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    (h_five_chromatic_or_more : FiveChromaticOrMore G) :
    ContainsSubdivision K5Graph G ∨ ContainsSubdivision K5Hat G := by
  exact (near_hajos_with_two_incident_unsplit_edges G h_five_chromatic_or_more).containsSubdivision

theorem four_color_theorem_from_near_hajos
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    (h_planar : IsPlanar G) :
    G.Colorable 4 := by
  exact colorable_four_of_noncolorable_contains_K5_or_K5Hat G h_planar
    (fun h_not_colorable => near_hajos G h_not_colorable)

theorem near_hajos_subdivision_has_two_incident_graph_edges
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    (h_five_chromatic_or_more : FiveChromaticOrMore G) :
    Exists fun edge₁ : Sym2 V =>
      Exists fun edge₂ : Sym2 V =>
        (Exists fun v : V => v ∈ edge₁ ∧ v ∈ edge₂) ∧
          edge₁ ∈ G.edgeSet ∧ edge₂ ∈ G.edgeSet := by
  obtain ⟨edge₁, edge₂, _hdistinct, hincident, hedge₁, hedge₂⟩ :=
    five_chromatic_has_two_distinct_incident_graph_edges_from_tail_data
      G h_five_chromatic_or_more
  exact ⟨edge₁, edge₂, hincident, hedge₁, hedge₂⟩

theorem near_hajos_subdivision_has_two_distinct_incident_graph_edges
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    (h_five_chromatic_or_more : FiveChromaticOrMore G) :
    Exists fun edge₁ : Sym2 V =>
      Exists fun edge₂ : Sym2 V =>
        edge₁ ≠ edge₂ ∧
          (Exists fun v : V => v ∈ edge₁ ∧ v ∈ edge₂) ∧
            edge₁ ∈ G.edgeSet ∧ edge₂ ∈ G.edgeSet := by
  exact five_chromatic_has_two_distinct_incident_graph_edges_from_tail_data
    G h_five_chromatic_or_more

end Schematic.Math.GraphTheory
