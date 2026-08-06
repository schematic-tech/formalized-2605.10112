import Schematic.Math.GraphTheory.PathsTrees.Operations

/-!
Coercion-friendly forms of uniqueness of paths in a tree.

The underlying graph-theory theorem quantifies the inspected vertex in the
tree subgraph.  These wrappers infer that membership from either path, which
keeps carrier arguments at the ambient graph's vertex type.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

theorem Subgraph.tree_mem_support_iff_of_isPath_coe
    {T : G.Subgraph}
    [DecidableEq T.verts]
    {u v x : V}
    {p q : G.Walk u v}
    (hT : T.coe.IsTree)
    (hp_le : p.toSubgraph ≤ T)
    (hq_le : q.toSubgraph ≤ T)
    (hp : p.IsPath)
    (hq : q.IsPath) :
    x ∈ p.support ↔ x ∈ q.support := by
  constructor
  · intro hx
    let uT : T.verts :=
      ⟨u, Walk.support_subset_of_toSubgraph_le hp_le p.start_mem_support⟩
    let vT : T.verts :=
      ⟨v, Walk.support_subset_of_toSubgraph_le hp_le p.end_mem_support⟩
    let xT : T.verts :=
      ⟨x, Walk.support_subset_of_toSubgraph_le hp_le hx⟩
    have hiff : x ∈ p.support ↔ x ∈ q.support := by
      simpa [uT, vT, xT] using
        (Subgraph.tree_mem_support_iff_of_isPath
          (G := G) (T := T) (u := uT) (v := vT)
          (p := p) (q := q) hT hp_le hq_le hp hq xT)
    exact hiff.mp hx
  · intro hx
    let uT : T.verts :=
      ⟨u, Walk.support_subset_of_toSubgraph_le hq_le q.start_mem_support⟩
    let vT : T.verts :=
      ⟨v, Walk.support_subset_of_toSubgraph_le hq_le q.end_mem_support⟩
    let xT : T.verts :=
      ⟨x, Walk.support_subset_of_toSubgraph_le hq_le hx⟩
    have hiff : x ∈ p.support ↔ x ∈ q.support := by
      simpa [uT, vT, xT] using
        (Subgraph.tree_mem_support_iff_of_isPath
          (G := G) (T := T) (u := uT) (v := vT)
          (p := p) (q := q) hT hp_le hq_le hp hq xT)
    exact hiff.mpr hx

theorem Subgraph.tree_mem_support_iff_reverse_of_isPath_coe
    {T : G.Subgraph}
    [DecidableEq T.verts]
    {u v x : V}
    {p : G.Walk u v}
    {q : G.Walk v u}
    (hT : T.coe.IsTree)
    (hp_le : p.toSubgraph ≤ T)
    (hq_le : q.toSubgraph ≤ T)
    (hp : p.IsPath)
    (hq : q.IsPath) :
    x ∈ p.support ↔ x ∈ q.support := by
  have hq_reverse_le : q.reverse.toSubgraph ≤ T := by
    simpa [SimpleGraph.Walk.toSubgraph_reverse] using hq_le
  simpa [SimpleGraph.Walk.support_reverse] using
    (Subgraph.tree_mem_support_iff_of_isPath_coe
      (G := G) (T := T) hT hp_le hq_reverse_le hp hq.reverse (x := x))

/-- Support relations for four paths from a root to the endpoints of three
paths in a tree.  The first path joins the left and right endpoints, while
the other two continue from those endpoints to `one` and `three`. -/
structure Walk.RootedFourPathSupports
    [DecidableEq V]
    {root left right one three : V}
    (base : G.Walk left right)
    (leftOne : G.Walk left one)
    (rightThree : G.Walk right three)
    (pLeft : G.Walk root left)
    (pRight : G.Walk root right)
    (pOne : G.Walk root one)
    (pThree : G.Walk root three)
    (hroot_base : root ∈ base.support)
    (hroot_leftOne : root ∈ leftOne.support)
    (hroot_rightThree : root ∈ rightThree.support) : Prop where
  left_prefix : ∀ {x}, x ∈ pLeft.support ->
    x ∈ (leftOne.takeUntil root hroot_leftOne).support
  right_prefix : ∀ {x}, x ∈ pRight.support ->
    x ∈ (rightThree.takeUntil root hroot_rightThree).support
  one_suffix : ∀ {x}, x ∈ pOne.support ->
    x ∈ (leftOne.dropUntil root hroot_leftOne).support
  three_suffix : ∀ {x}, x ∈ pThree.support ->
    x ∈ (rightThree.dropUntil root hroot_rightThree).support
  left_base_prefix : ∀ {x}, x ∈ pLeft.support ->
    x ∈ (base.takeUntil root hroot_base).support
  right_base_suffix : ∀ {x}, x ∈ pRight.support ->
    x ∈ (base.dropUntil root hroot_base).support

theorem Subgraph.tree_rooted_four_path_supports
    [DecidableEq V]
    {T : G.Subgraph}
    [DecidableEq T.verts]
    {root left right one three : V}
    {base : G.Walk left right}
    {leftOne : G.Walk left one}
    {rightThree : G.Walk right three}
    {pLeft : G.Walk root left}
    {pRight : G.Walk root right}
    {pOne : G.Walk root one}
    {pThree : G.Walk root three}
    (hT : T.coe.IsTree)
    (hbase_le : base.toSubgraph ≤ T)
    (hleftOne_le : leftOne.toSubgraph ≤ T)
    (hrightThree_le : rightThree.toSubgraph ≤ T)
    (hpLeft_le : pLeft.toSubgraph ≤ T)
    (hpRight_le : pRight.toSubgraph ≤ T)
    (hpOne_le : pOne.toSubgraph ≤ T)
    (hpThree_le : pThree.toSubgraph ≤ T)
    (hbase : base.IsPath)
    (hleftOne : leftOne.IsPath)
    (hrightThree : rightThree.IsPath)
    (hpLeft : pLeft.IsPath)
    (hpRight : pRight.IsPath)
    (hpOne : pOne.IsPath)
    (hpThree : pThree.IsPath)
    (hroot_base : root ∈ base.support)
    (hroot_leftOne : root ∈ leftOne.support)
    (hroot_rightThree : root ∈ rightThree.support) :
    Walk.RootedFourPathSupports base leftOne rightThree
      pLeft pRight pOne pThree
      hroot_base hroot_leftOne hroot_rightThree where
  left_prefix := fun {x} hx =>
    (Subgraph.tree_mem_support_iff_reverse_of_isPath_coe
      hT hpLeft_le
      (Walk.toSubgraph_takeUntil_le_of_le
        (H := T) hleftOne_le hroot_leftOne)
      hpLeft (hleftOne.takeUntil hroot_leftOne) (x := x)).mp hx
  right_prefix := fun {x} hx =>
    (Subgraph.tree_mem_support_iff_reverse_of_isPath_coe
      hT hpRight_le
      (Walk.toSubgraph_takeUntil_le_of_le
        (H := T) hrightThree_le hroot_rightThree)
      hpRight (hrightThree.takeUntil hroot_rightThree) (x := x)).mp hx
  one_suffix := fun {x} hx =>
    (Subgraph.tree_mem_support_iff_of_isPath_coe
      hT hpOne_le
      (Walk.toSubgraph_dropUntil_le_of_le
        (H := T) hleftOne_le hroot_leftOne)
      hpOne (hleftOne.dropUntil hroot_leftOne) (x := x)).mp hx
  three_suffix := fun {x} hx =>
    (Subgraph.tree_mem_support_iff_of_isPath_coe
      hT hpThree_le
      (Walk.toSubgraph_dropUntil_le_of_le
        (H := T) hrightThree_le hroot_rightThree)
      hpThree (hrightThree.dropUntil hroot_rightThree) (x := x)).mp hx
  left_base_prefix := fun {x} hx =>
    (Subgraph.tree_mem_support_iff_reverse_of_isPath_coe
      hT hpLeft_le
      (Walk.toSubgraph_takeUntil_le_of_le
        (H := T) hbase_le hroot_base)
      hpLeft (hbase.takeUntil hroot_base) (x := x)).mp hx
  right_base_suffix := fun {x} hx =>
    (Subgraph.tree_mem_support_iff_of_isPath_coe
      hT hpRight_le
      (Walk.toSubgraph_dropUntil_le_of_le
        (H := T) hbase_le hroot_base)
      hpRight (hbase.dropUntil hroot_base) (x := x)).mp hx

end Schematic.Math.GraphTheory
