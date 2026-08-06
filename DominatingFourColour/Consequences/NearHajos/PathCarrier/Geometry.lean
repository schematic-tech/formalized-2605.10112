import DominatingFourColour.Consequences.NearHajos.PathCarrier.Data

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

namespace PathCarrier

variable {V : Type u} [Fintype V] {G : SimpleGraph V}
variable {D : ThirdBranchPathAndTailInducedCycleData G}

abbrev LargePathCarrier.left (C : LargePathCarrier D) : C.Btail.verts :=
  (C.leftT : C.Btail.verts)

abbrev LargePathCarrier.right (C : LargePathCarrier D) : C.Btail.verts :=
  (C.rightT : C.Btail.verts)

abbrev LargePathCarrier.attachment
    (C : LargePathCarrier D) (a : Fin 4) : C.Btail.verts :=
  ⟨C.attachTail (C.order a), C.hBtail_terminal (C.order a)⟩

abbrev LargePathCarrier.one (C : LargePathCarrier D) : C.Btail.verts :=
  C.attachment (1 : Fin 4)

abbrev LargePathCarrier.three (C : LargePathCarrier D) : C.Btail.verts :=
  C.attachment (3 : Fin 4)

abbrev LargePathCarrier.leftArm (C : LargePathCarrier D) :
    C.Btail.coe.Walk C.left C.one :=
  C.leftStem (1 : Fin 4)

abbrev LargePathCarrier.rightArm (C : LargePathCarrier D) :
    C.Btail.coe.Walk C.right C.three :=
  C.rightStem (3 : Fin 4)

theorem LargePathCarrier.attachment_adj (C : LargePathCarrier D) (a : Fin 4) :
    G.Adj (C.attachment a : V) (C.Ktail.model.branchVertex (C.order a)) := by
  simpa using (C.hattachTail (C.order a)).2

/-- Reindex both attachment vertices and their associated branch order by the
same embedding. -/
abbrev LargePathCarrier.reindexedAttachment
    (C : LargePathCarrier D) (e : Fin 4 ↪ Fin 4) (a : Fin 4) : C.Btail.verts :=
  C.attachment (e a)

abbrev LargePathCarrier.reindexedOrder
    (C : LargePathCarrier D) (e : Fin 4 ↪ Fin 4) : Fin 4 ↪ Fin 4 :=
  e.trans C.order

theorem LargePathCarrier.reindexedAttachment_adj
    (C : LargePathCarrier D) (e : Fin 4 ↪ Fin 4) (a : Fin 4) :
    G.Adj (C.reindexedAttachment e a : V)
      (C.Ktail.model.branchVertex (C.reindexedOrder e a)) :=
  C.attachment_adj (e a)

@[simp] theorem LargePathCarrier.attachment_zero (C : LargePathCarrier D) :
    C.attachment (0 : Fin 4) = C.left := by
  apply Subtype.ext
  exact C.left_eq_zero.symm

@[simp] theorem LargePathCarrier.attachment_two (C : LargePathCarrier D) :
    C.attachment (2 : Fin 4) = C.right := by
  apply Subtype.ext
  exact C.right_eq_two.symm

theorem LargePathCarrier.leftT_ne_rightT (C : LargePathCarrier D) :
    C.leftT ≠ C.rightT := by
  intro h
  exact C.left_ne_right
    (congrArg (fun x : C.TBtail.verts => ((x : C.Btail.verts) : V)) h)

theorem LargePathCarrier.leftArm_isPath (C : LargePathCarrier D) :
    C.leftArm.IsPath :=
  C.leftStem_isPath (1 : Fin 4)

theorem LargePathCarrier.rightArm_isPath (C : LargePathCarrier D) :
    C.rightArm.IsPath :=
  C.rightStem_isPath (3 : Fin 4)

theorem LargePathCarrier.leftArm_le (C : LargePathCarrier D) :
    C.leftArm.toSubgraph ≤ C.TBtail :=
  C.leftStem_le (1 : Fin 4)

theorem LargePathCarrier.rightArm_le (C : LargePathCarrier D) :
    C.rightArm.toSubgraph ≤ C.TBtail :=
  C.rightStem_le (3 : Fin 4)

theorem LargePathCarrier.right_not_leftArm (C : LargePathCarrier D) :
    C.right ∉ C.leftArm.support := by
  intro hright
  exact C.leftStem_avoids_right hright
    (by
      intro h
      exact C.leftT_ne_rightT.symm (Subtype.ext h))
    rfl

theorem LargePathCarrier.left_not_rightArm (C : LargePathCarrier D) :
    C.left ∉ C.rightArm.support := by
  intro hleft
  exact C.rightStem_avoids_left hleft
    (by
      intro h
      exact C.leftT_ne_rightT (Subtype.ext h))
    rfl

end PathCarrier

end Schematic.Math.GraphTheory
