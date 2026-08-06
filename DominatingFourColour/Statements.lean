import DominatingFourColour.Proof.MainInduction

/-!
Named statements from the paper.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

theorem dominating_four_colour
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    (h_no_model : HasNoDominatingKModel G 5) :
    G.Colorable 4 := by
  rcases main_induction_hypothesis G (.nil) with hcolor | hmodel
  · exact hcolor
  · rcases hmodel with ⟨T, _⟩
    exact False.elim (h_no_model ⟨T⟩)

theorem five_chromatic_has_dominating_K5_model
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    (h_five_chromatic_or_more : FiveChromaticOrMore G) :
    HasDominatingKModel G 5 := by
  rcases main_induction_hypothesis G (.nil) with hcolor | hmodel
  · exact False.elim (h_five_chromatic_or_more hcolor)
  · rcases hmodel with ⟨T, _⟩
    exact ⟨T⟩

end Schematic.Math.GraphTheory

namespace DominatingFourColour

open SimpleGraph
open Schematic.Math.GraphTheory

universe u

/-- The Dominating 4-Colour Theorem. -/
theorem dominating_four_colour
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    (h_no_model : HasNoDominatingKModel G 5) :
    G.Colorable 4 :=
  Schematic.Math.GraphTheory.dominating_four_colour G h_no_model

/-- Every graph of chromatic number at least five has a dominating K5 model. -/
theorem five_chromatic_has_dominating_K5_model
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    (h_five_chromatic_or_more : FiveChromaticOrMore G) :
    HasDominatingKModel G 5 :=
  Schematic.Math.GraphTheory.five_chromatic_has_dominating_K5_model
    G h_five_chromatic_or_more

end DominatingFourColour
