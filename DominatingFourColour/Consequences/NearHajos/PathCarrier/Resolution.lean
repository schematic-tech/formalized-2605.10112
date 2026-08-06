import DominatingFourColour.Consequences.NearHajos.PathCarrier.HardResolution
import DominatingFourColour.Consequences.NearHajos.PathCarrier.Preparation

namespace Schematic.Math.GraphTheory

universe u

namespace PathCarrier

theorem resolve
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G) :
    NearHajosStrengtheningConclusion G := by
  rcases prepare D with hdone | hlarge
  · exact hdone
  · rcases hlarge with ⟨C⟩
    exact resolveLarge D C

end PathCarrier

end Schematic.Math.GraphTheory
