import DominatingFourColour.Consequences.NearHajos.ModelReductions
import DominatingFourColour.Consequences.Singletons
import Schematic.Math.GraphTheory.Planarity.Basic

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

theorem near_hajos_path_cycle_data
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    (h_five_chromatic_or_more : FiveChromaticOrMore G) :
    ThirdBranchPathAndTailInducedCycleConclusion G := by
  exact dominating_K5_can_choose_third_branch_path_and_tail_induced_cycle G
    h_five_chromatic_or_more

theorem near_hajos_weak_K5_subdivision
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    (h_five_chromatic_or_more : FiveChromaticOrMore G) :
    ContainsWeakSubdivision K5Graph G := by
  exact containsWeakSubdivision_K5_of_not_colorable_four G h_five_chromatic_or_more

theorem five_chromatic_tail_K4_minor
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    (h_five_chromatic_or_more : FiveChromaticOrMore G) :
    ContainsMinor K4Graph G := by
  obtain ⟨T⟩ := five_chromatic_has_dominating_K5_model G h_five_chromatic_or_more
  exact DominatingK5Model.tailK4_contains_K4_minor T

theorem five_chromatic_tail_weak_K4_subdivision
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    (h_five_chromatic_or_more : FiveChromaticOrMore G) :
    ContainsWeakSubdivision K4Graph G := by
  obtain ⟨T⟩ := five_chromatic_has_dominating_K5_model G h_five_chromatic_or_more
  exact DominatingK5Model.tailK4_contains_weak_K4_subdivision T

end Schematic.Math.GraphTheory
