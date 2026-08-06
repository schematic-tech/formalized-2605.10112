import DominatingFourColour.Statements

/-!
The `t = 5` case of the dominating Hadwiger conjecture.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

theorem dominating_hadwiger_conjecture_t5
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    (h_no_model : HasNoDominatingKModel G 5) :
    G.Colorable 4 := by
  exact dominating_four_colour G h_no_model

theorem five_chromatic_contains_K5_minor
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    (h_five_chromatic_or_more : FiveChromaticOrMore G) :
    ContainsMinor K5Graph G := by
  obtain ⟨T⟩ := five_chromatic_has_dominating_K5_model G h_five_chromatic_or_more
  exact T.contains_completeGraph_minor

end Schematic.Math.GraphTheory
