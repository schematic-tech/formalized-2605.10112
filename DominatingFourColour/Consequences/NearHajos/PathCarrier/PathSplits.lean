import DominatingFourColour.Consequences.NearHajos.PathCarrier.CommonData

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

namespace PathCarrier

/-- The two outward paths obtained by splitting a path at an internal vertex. -/
structure InternalSplit
    {V : Type u} {G : SimpleGraph V}
    (T : G.Subgraph) {u v : V} (p : G.Walk u v) (z : T.verts) where
  left : G.Walk (z : V) u
  right : G.Walk (z : V) v
  left_isPath : left.IsPath
  right_isPath : right.IsPath
  left_le : left.toSubgraph ≤ T
  right_le : right.toSubgraph ≤ T
  left_support : forall {x : V}, x ∈ left.support -> x ∈ p.support
  right_support : forall {x : V}, x ∈ right.support -> x ∈ p.support
  right_not_left : v ∉ left.support
  left_not_right : u ∉ right.support

/-- Split a path at an internal vertex, orienting both pieces away from the split. -/
def internalSplit
    {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    {T : G.Subgraph} {u v : V} {p : G.Walk u v}
    (hp : p.IsPath) (hp_le : p.toSubgraph ≤ T)
    (z : T.verts) (hz : (z : V) ∈ Walk.InternalVertices p) :
    InternalSplit T p z := by
  let left : G.Walk (z : V) u :=
    (p.takeUntil (z : V) hz.1).reverse
  let right : G.Walk (z : V) v :=
    p.dropUntil (z : V) hz.1
  refine {
    left := left
    right := right
    left_isPath := by
      simpa [left] using (hp.takeUntil hz.1).reverse
    right_isPath := by
      simpa [right] using hp.dropUntil hz.1
    left_le := by
      simpa [left, SimpleGraph.Walk.toSubgraph_reverse] using
        (le_trans (Walk.toSubgraph_takeUntil_le p hz.1) hp_le)
    right_le := by
      simpa [right] using
        (le_trans (Walk.toSubgraph_dropUntil_le p hz.1) hp_le)
    left_support := ?_
    right_support := ?_
    right_not_left := ?_
    left_not_right := ?_
  }
  · intro x hx
    have hx_take : x ∈ (p.takeUntil (z : V) hz.1).support := by
      simpa [left, SimpleGraph.Walk.support_reverse] using hx
    exact SimpleGraph.Walk.support_takeUntil_subset p hz.1 hx_take
  · intro x hx
    exact SimpleGraph.Walk.support_dropUntil_subset p hz.1
      (by simpa [right] using hx)
  · intro hv
    exact (Walk.IsPath.end_not_mem_reverse_takeUntil_support_of_internal hp hz)
      (by simpa [left] using hv)
  · intro hu
    exact (Walk.IsPath.start_not_mem_dropUntil_support_of_internal hp hz)
      (by simpa [right] using hu)

/-- A path suffix starting at a selected vertex, with its inherited invariants. -/
structure Suffix
    {V : Type u} {G : SimpleGraph V}
    (T : G.Subgraph) {u v : V} (p : G.Walk u v) (z : T.verts) where
  path : G.Walk (z : V) v
  isPath : path.IsPath
  le : path.toSubgraph ≤ T
  support : forall {x : V}, x ∈ path.support -> x ∈ p.support

/-- Extract the suffix of a path beginning at a selected vertex. -/
def suffix
    {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    {T : G.Subgraph} {u v : V} {p : G.Walk u v}
    (hp : p.IsPath) (hp_le : p.toSubgraph ≤ T)
    (z : T.verts) (hz : (z : V) ∈ p.support) :
    Suffix T p z := by
  let q : G.Walk (z : V) v := p.dropUntil (z : V) hz
  exact {
    path := q
    isPath := by simpa [q] using hp.dropUntil hz
    le := by
      simpa [q] using
        (le_trans (Walk.toSubgraph_dropUntil_le p hz) hp_le)
    support := by
      intro x hx
      exact SimpleGraph.Walk.support_dropUntil_subset p hz
        (by simpa [q] using hx)
  }

end PathCarrier

end Schematic.Math.GraphTheory
