import DominatingFourColour.Consequences.NearHajos.PathCarrier.CommonNonrootCross

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

namespace PathCarrier

/-- Resolve a normalized common obstruction by its root and crossing geometry. -/
theorem resolveCommon
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (C : LargePathCarrier D) [DecidableEq C.Btail.verts]
    (N : NormalizedCommonObstruction C) :
    NearHajosStrengtheningConclusion G := by
  by_cases hroot : (N.root : C.Btail.verts) = N.last
  · by_cases hcross : N.NoCross
    · exact commonRootNoCross D C N hroot hcross
    · exact commonRootCross D C N hroot hcross
  · by_cases hcross : N.NoCross
    · exact commonNonrootNoCross D C N hroot hcross
    · exact commonNonrootCross D C N hroot hcross

end PathCarrier

end Schematic.Math.GraphTheory

