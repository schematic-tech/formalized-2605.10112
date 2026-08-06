import DominatingFourColour.Consequences.NearHajos.PathCarrier.CleanResolution
import DominatingFourColour.Consequences.NearHajos.PathCarrier.HiddenResolution

namespace Schematic.Math.GraphTheory

universe u

namespace PathCarrier

/-- Resolve the large-carrier case by separating clean and hidden-contact geometry. -/
theorem resolveLarge
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (C : LargePathCarrier D) :
    NearHajosStrengtheningConclusion G := by
  by_cases hclean : C.Clean
  · exact resolveClean D C hclean
  · exact resolveHidden D C hclean

end PathCarrier

end Schematic.Math.GraphTheory

