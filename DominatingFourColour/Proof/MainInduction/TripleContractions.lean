import DominatingFourColour.Proof.Colouring.SeparatorClique
import Schematic.Math.GraphTheory.Contractions.TripleCollapse

/-! Canonical contractions associated to a three-vertex separator. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

def Separation.rightTripleX
    (S : Separation G)
    {x y z : V}
    (hseparator : S.separator = ({x, y, z} : Set V)) : S.right :=
  ⟨x, (S.triple_vertices_mem_right hseparator).1⟩

def Separation.rightTripleY
    (S : Separation G)
    {x y z : V}
    (hseparator : S.separator = ({x, y, z} : Set V)) : S.right :=
  ⟨y, (S.triple_vertices_mem_right hseparator).2.1⟩

def Separation.rightTripleZ
    (S : Separation G)
    {x y z : V}
    (hseparator : S.separator = ({x, y, z} : Set V)) : S.right :=
  ⟨z, (S.triple_vertices_mem_right hseparator).2.2⟩

@[simp]
theorem Separation.coe_rightTripleX
    (S : Separation G)
    {x y z : V}
    (hseparator : S.separator = ({x, y, z} : Set V)) :
    (S.rightTripleX hseparator : V) = x :=
  rfl

@[simp]
theorem Separation.coe_rightTripleY
    (S : Separation G)
    {x y z : V}
    (hseparator : S.separator = ({x, y, z} : Set V)) :
    (S.rightTripleY hseparator : V) = y :=
  rfl

@[simp]
theorem Separation.coe_rightTripleZ
    (S : Separation G)
    {x y z : V}
    (hseparator : S.separator = ({x, y, z} : Set V)) :
    (S.rightTripleZ hseparator : V) = z :=
  rfl

theorem Separation.rightTripleXYAdj
    (S : Separation G)
    {x y z : V}
    (hxy : x ≠ y)
    (hseparator : S.separator = ({x, y, z} : Set V)) :
    S.rightWithSeparatorClique.Adj
      (S.rightTripleX hseparator) (S.rightTripleY hseparator) :=
  S.rightWithSeparatorClique_separator_adj
    (S.triple_vertices_mem_left hseparator).1
    (S.triple_vertices_mem_left hseparator).2.1
    (by
      intro h
      exact hxy (congrArg (fun r : S.right => (r : V)) h))

theorem Separation.rightTripleXZAdj
    (S : Separation G)
    {x y z : V}
    (hxz : x ≠ z)
    (hseparator : S.separator = ({x, y, z} : Set V)) :
    S.rightWithSeparatorClique.Adj
      (S.rightTripleX hseparator) (S.rightTripleZ hseparator) :=
  S.rightWithSeparatorClique_separator_adj
    (S.triple_vertices_mem_left hseparator).1
    (S.triple_vertices_mem_left hseparator).2.2
    (by
      intro h
      exact hxz (congrArg (fun r : S.right => (r : V)) h))

theorem Separation.rightTripleYZAdj
    (S : Separation G)
    {x y z : V}
    (hyz : y ≠ z)
    (hseparator : S.separator = ({x, y, z} : Set V)) :
    S.rightWithSeparatorClique.Adj
      (S.rightTripleY hseparator) (S.rightTripleZ hseparator) :=
  S.rightWithSeparatorClique_separator_adj
    (S.triple_vertices_mem_left hseparator).2.1
    (S.triple_vertices_mem_left hseparator).2.2
    (by
      intro h
      exact hyz (congrArg (fun r : S.right => (r : V)) h))

noncomputable def Separation.rightTripleXYContraction
    (S : Separation G)
    {x y z : V}
    (hxy : x ≠ y)
    (hseparator : S.separator = ({x, y, z} : Set V)) :
    GraphContraction S.rightWithSeparatorClique :=
  GraphContraction.collapseEdge S.rightWithSeparatorClique
    (S.rightTripleXYAdj hxy hseparator)

noncomputable def Separation.rightTripleXZContraction
    (S : Separation G)
    {x y z : V}
    (hxz : x ≠ z)
    (hseparator : S.separator = ({x, y, z} : Set V)) :
    GraphContraction S.rightWithSeparatorClique :=
  GraphContraction.collapseEdge S.rightWithSeparatorClique
    (S.rightTripleXZAdj hxz hseparator)

noncomputable def Separation.rightTripleYZContraction
    (S : Separation G)
    {x y z : V}
    (hyz : y ≠ z)
    (hseparator : S.separator = ({x, y, z} : Set V)) :
    GraphContraction S.rightWithSeparatorClique :=
  GraphContraction.collapseEdge S.rightWithSeparatorClique
    (S.rightTripleYZAdj hyz hseparator)

noncomputable def Separation.rightTripleXYZContraction
    (S : Separation G)
    {x y z : V}
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hseparator : S.separator = ({x, y, z} : Set V)) :
    GraphContraction S.rightWithSeparatorClique :=
  GraphContraction.collapseTriple S.rightWithSeparatorClique
    (S.rightTripleXYAdj hxy hseparator)
    (S.rightTripleXZAdj hxz hseparator)

end Schematic.Math.GraphTheory
