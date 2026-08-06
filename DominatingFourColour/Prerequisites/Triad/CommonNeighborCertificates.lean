import DominatingFourColour.Prerequisites.Triad.TreeConstruction

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

variable {V : Type u} {G : SimpleGraph V}

def Triad.of_common_neighbor
    {feet : Fin 3 -> V}
    {apex : V}
    (hapex_not_foot : forall i : Fin 3, apex ≠ feet i)
    (hadj : forall i : Fin 3, G.Adj apex (feet i)) :
    Triad G feet where
  apex := apex
  apex_not_foot := hapex_not_foot
  leg i := (hadj i).toWalk
  leg_isPath i := SimpleGraph.Walk.IsPath.of_adj (hadj i)
  apex_only_common_vertex := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hx _
    simp [Walk.InternalVertices] at hx
    rcases hx.1 with rfl | rfl
    · exact hx.2.1 rfl
    · exact hx.2.2 rfl
  internal_vertices_avoid_feet := by
    intro i j h
    simp [Walk.InternalVertices] at h
    rcases h.1 with h_eq | h_eq
    · exact h.2.1 h_eq
    · exact h.2.2 h_eq

theorem Triad.common_neighbor_apex_mem_of_mem_carrier_edge
    {feet : Fin 3 -> V}
    {apex : V}
    (hapex_not_foot : forall i : Fin 3, apex ≠ feet i)
    (hadj : forall i : Fin 3, G.Adj apex (feet i))
    {e : Sym2 V}
    (he : e ∈ (Triad.of_common_neighbor
      (G := G) hapex_not_foot hadj).carrier.edgeSet) :
    apex ∈ e := by
  simp [Triad.carrier, Triad.of_common_neighbor] at he
  rcases he with rfl | rfl | rfl <;> simp

theorem Triad.common_neighbor_mem_vertexSet_iff
    {feet : Fin 3 -> V}
    {apex : V}
    (hapex_not_foot : forall i : Fin 3, apex ≠ feet i)
    (hadj : forall i : Fin 3, G.Adj apex (feet i))
    {v : V} :
    v ∈ (Triad.of_common_neighbor
      (G := G) hapex_not_foot hadj).vertexSet ↔
      v = apex ∨ v ∈ Set.range feet := by
  constructor
  · rintro ⟨i, hi⟩
    simp [Triad.of_common_neighbor] at hi
    rcases hi with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr ⟨i, rfl⟩
  · rintro (rfl | ⟨i, rfl⟩)
    · exact (Triad.of_common_neighbor
        (G := G) hapex_not_foot hadj).apex_mem_vertexSet
    · exact (Triad.of_common_neighbor
        (G := G) hapex_not_foot hadj).foot_mem_vertexSet i

theorem Triad.common_neighbor_lean
    {feet : Fin 3 -> V}
    {a : V}
    (hapex_not_foot : forall i : Fin 3, a ≠ feet i)
    (hadj : forall i : Fin 3, G.Adj a (feet i)) :
    (Triad.of_common_neighbor (G := G) hapex_not_foot hadj).Lean := by
  intro T' hT'_subset v hv
  have hv_cases :
      v = a ∨ v ∈ Set.range feet :=
    (Triad.common_neighbor_mem_vertexSet_iff
      (G := G) hapex_not_foot hadj).mp hv
  rcases hv_cases with hv_eq | hvfoot
  · have h_apex'_in_common :
        T'.apex ∈
          (Triad.of_common_neighbor (G := G) hapex_not_foot hadj).vertexSet :=
      hT'_subset T'.apex_mem_vertexSet
    have h_apex'_cases :
        T'.apex = a ∨ T'.apex ∈ Set.range feet :=
      (Triad.common_neighbor_mem_vertexSet_iff
        (G := G) hapex_not_foot hadj).mp h_apex'_in_common
    subst v
    rcases h_apex'_cases with h_apex' | h_apex'_foot
    · simpa [h_apex'] using T'.apex_mem_vertexSet
    · rcases h_apex'_foot with ⟨i, hi⟩
      exact False.elim (T'.apex_not_foot i hi.symm)
  · rcases hvfoot with ⟨i, rfl⟩
    exact T'.foot_mem_vertexSet i

theorem Triad.common_neighbor_not_mem_of_mem_carrier_edge
    {feet : Fin 3 -> V}
    {apex x : V}
    (hapex_not_foot : forall i : Fin 3, apex ≠ feet i)
    (hadj : forall i : Fin 3, G.Adj apex (feet i))
    (hx_ne_apex : x ≠ apex)
    (hx_not_foot : forall i : Fin 3, x ≠ feet i)
    {e : Sym2 V}
    (he : e ∈ (Triad.of_common_neighbor
      (G := G) hapex_not_foot hadj).carrier.edgeSet) :
    x ∉ e := by
  simp [Triad.carrier, Triad.of_common_neighbor] at he
  rcases he with rfl | rfl | rfl <;> simp [hx_ne_apex, hx_not_foot]

theorem Triad.vertexSet_eq_carrier_verts {feet : Fin 3 -> V} (T : Triad G feet) :
    T.vertexSet = T.carrier.verts := by
  ext v
  simp only [Triad.vertexSet, Triad.carrier, SimpleGraph.Subgraph.verts_iSup,
    Set.mem_iUnion, Set.mem_setOf_eq, SimpleGraph.Walk.mem_verts_toSubgraph]

theorem Triad.mem_carrier_verts_iff {feet : Fin 3 -> V} (T : Triad G feet) {v : V} :
    v ∈ T.carrier.verts ↔ v ∈ T.vertexSet := by
  rw [T.vertexSet_eq_carrier_verts]

theorem Triad.carrier_edgeSet_disjoint_of_inter_vertexSet_subset_feet
    {feet : Fin 3 -> V}
    (hfeet_injective : Function.Injective feet)
    (T₁ T₂ : Triad G feet)
    (hinter : T₁.vertexSet ∩ T₂.vertexSet ⊆ Set.range feet) :
    Disjoint T₁.carrier.edgeSet T₂.carrier.edgeSet := by
  rw [Set.disjoint_left]
  intro e he₁ he₂
  obtain ⟨i, hi_sub⟩ :=
    (Triad.mem_carrier_edgeSet_iff (T := T₁)).mp he₁
  obtain ⟨j, hj_sub⟩ :=
    (Triad.mem_carrier_edgeSet_iff (T := T₂)).mp he₂
  have hi_edges : e ∈ (T₁.leg i).edges :=
    (SimpleGraph.Walk.mem_edges_toSubgraph (T₁.leg i)).mp hi_sub
  have hj_edges : e ∈ (T₂.leg j).edges :=
    (SimpleGraph.Walk.mem_edges_toSubgraph (T₂.leg j)).mp hj_sub
  have hsupport₁ := Walk.out_mem_support_of_mem_edges (p := T₁.leg i) hi_edges
  have hsupport₂ := Walk.out_mem_support_of_mem_edges (p := T₂.leg j) hj_edges
  have hfst_range : e.out.1 ∈ Set.range feet :=
    hinter ⟨⟨i, hsupport₁.1⟩, ⟨j, hsupport₂.1⟩⟩
  have hsnd_range : e.out.2 ∈ Set.range feet :=
    hinter ⟨⟨i, hsupport₁.2⟩, ⟨j, hsupport₂.2⟩⟩
  rcases hfst_range with ⟨a, ha⟩
  rcases hsnd_range with ⟨b, hb⟩
  have hfst_foot_support : feet a ∈ (T₁.leg i).support := by
    simpa [ha] using hsupport₁.1
  have hsnd_foot_support : feet b ∈ (T₁.leg i).support := by
    simpa [hb] using hsupport₁.2
  have hai : a = i :=
    (T₁.foot_mem_leg_support_iff hfeet_injective a i).mp hfst_foot_support
  have hbi : b = i :=
    (T₁.foot_mem_leg_support_iff hfeet_injective b i).mp hsnd_foot_support
  have hout_eq : e.out.1 = e.out.2 := by
    calc
      e.out.1 = feet a := ha.symm
      _ = feet i := by rw [hai]
      _ = feet b := by rw [hbi]
      _ = e.out.2 := hb
  have hdiag : e.IsDiag := by
    have heq : e = s(e.out.1, e.out.2) := by
      rw [Sym2.mk, e.out_eq]
    rw [heq]
    exact hout_eq
  exact (G.not_isDiag_of_mem_edgeSet (T₁.carrier.edgeSet_subset he₁)) hdiag

theorem Triad.common_neighbor_punctured_carrier_verts_eq_singleton
    {feet : Fin 3 -> V}
    {apex : V}
    (hapex_not_foot : forall i : Fin 3, apex ≠ feet i)
    (hadj : forall i : Fin 3, G.Adj apex (feet i)) :
    ((Triad.of_common_neighbor
      (G := G) hapex_not_foot hadj).carrier.deleteVerts (Set.range feet)).verts =
        ({apex} : Set V) := by
  ext v
  constructor
  · intro hv
    rw [SimpleGraph.Subgraph.deleteVerts_verts, Set.mem_diff] at hv
    rw [← (Triad.of_common_neighbor
      (G := G) hapex_not_foot hadj).vertexSet_eq_carrier_verts] at hv
    rcases (Triad.common_neighbor_mem_vertexSet_iff
      (G := G) hapex_not_foot hadj).mp hv.1 with rfl | hfeet
    · simp
    · exact False.elim (hv.2 hfeet)
  · intro hv
    rw [Set.mem_singleton_iff] at hv
    subst v
    rw [SimpleGraph.Subgraph.deleteVerts_verts, Set.mem_diff]
    constructor
    · rw [← (Triad.of_common_neighbor
        (G := G) hapex_not_foot hadj).vertexSet_eq_carrier_verts]
      exact (Triad.of_common_neighbor
        (G := G) hapex_not_foot hadj).apex_mem_vertexSet
    · rintro ⟨i, hi⟩
      exact hapex_not_foot i hi.symm

theorem Triad.common_neighbor_inside_neighbors_at_most_three
    {feet : Fin 3 -> V}
    {apex : V}
    (hapex_not_foot : forall i : Fin 3, apex ≠ feet i)
    (hadj : forall i : Fin 3, G.Adj apex (feet i))
    (hfeet_injective : Function.Injective feet) :
    forall v : V,
      v ∈ ((Triad.of_common_neighbor
        (G := G) hapex_not_foot hadj).carrier.deleteVerts (Set.range feet)).verts ->
        (G.neighborSet v ∩
          (Triad.of_common_neighbor
            (G := G) hapex_not_foot hadj).vertexSet).ncard <= 3 := by
  classical
  intro v hv
  have hv_apex : v = apex := by
    have hv' := congrArg (fun S : Set V => v ∈ S)
      (Triad.common_neighbor_punctured_carrier_verts_eq_singleton
        (G := G) hapex_not_foot hadj)
    simpa [Set.mem_singleton_iff] using hv'.mp hv
  subst v
  have hsubset :
      G.neighborSet apex ∩
          (Triad.of_common_neighbor
            (G := G) hapex_not_foot hadj).vertexSet ⊆
        Set.range feet := by
    intro x hx
    rcases (Triad.common_neighbor_mem_vertexSet_iff
      (G := G) hapex_not_foot hadj).mp hx.2 with rfl | hfeet
    · have hxx : G.Adj x x := (SimpleGraph.mem_neighborSet (G := G) x x).mp hx.1
      exact False.elim (hxx.ne rfl)
    · exact hfeet
  have hcard_le :
      (G.neighborSet apex ∩
          (Triad.of_common_neighbor
            (G := G) hapex_not_foot hadj).vertexSet).ncard <=
        (Set.range feet).ncard :=
    Set.ncard_le_ncard hsubset
  have hrange_le : (Set.range feet).ncard <= 3 := by
    rw [ncard_range_fin3_of_injective hfeet_injective]
  exact le_trans hcard_le hrange_le

theorem Triad.common_neighbor_foot_inside_neighbors_at_most_three
    {feet : Fin 3 -> V}
    {apex : V}
    (hapex_not_foot : forall i : Fin 3, apex ≠ feet i)
    (hadj : forall i : Fin 3, G.Adj apex (feet i))
    (hfeet_injective : Function.Injective feet)
    (i : Fin 3) :
    (G.neighborSet (feet i) ∩
      (Triad.of_common_neighbor
        (G := G) hapex_not_foot hadj).vertexSet).ncard <= 3 := by
  classical
  let T : Triad G feet := Triad.of_common_neighbor (G := G) hapex_not_foot hadj
  have hsubset :
      G.neighborSet (feet i) ∩ T.vertexSet ⊆
        insert apex (Set.range feet \ {feet i}) := by
    intro x hx
    rcases (Triad.common_neighbor_mem_vertexSet_iff
      (G := G) hapex_not_foot hadj).mp hx.2 with h_apex | hfoot
    · simp [h_apex]
    · refine Set.mem_insert_of_mem apex ?_
      refine ⟨hfoot, ?_⟩
      intro hx_eq
      have h_adj : G.Adj (feet i) x :=
        (SimpleGraph.mem_neighborSet (G := G) (feet i) x).mp hx.1
      exact h_adj.ne hx_eq.symm
  have hcard_le :
      (G.neighborSet (feet i) ∩ T.vertexSet).ncard <=
        (insert apex (Set.range feet \ {feet i})).ncard :=
    Set.ncard_le_ncard hsubset
  have hdiff_le : (Set.range feet \ {feet i}).ncard <= 2 := by
    have hmem : feet i ∈ Set.range feet := ⟨i, rfl⟩
    have hdiff_add :
        (Set.range feet \ {feet i}).ncard + 1 = (Set.range feet).ncard :=
      Set.ncard_diff_singleton_add_one hmem
    have hrange : (Set.range feet).ncard = 3 :=
      ncard_range_fin3_of_injective hfeet_injective
    omega
  have hinsert_le :
      (insert apex (Set.range feet \ {feet i})).ncard <= 3 := by
    exact ncard_insert_range_fin3_diff_singleton_le_three
      hfeet_injective i apex
  exact le_trans hcard_le hinsert_le

theorem Triad.common_neighbor_root_not_mem_vertexSet_iff
    {feet : Fin 3 -> V}
    {apex root : V}
    (hapex_not_foot : forall i : Fin 3, apex ≠ feet i)
    (hadj : forall i : Fin 3, G.Adj apex (feet i)) :
    root ∉ (Triad.of_common_neighbor
      (G := G) hapex_not_foot hadj).vertexSet ↔
      root ≠ apex ∧ root ∉ Set.range feet := by
  constructor
  · intro hroot
    constructor
    · intro hroot_apex
      exact hroot ((Triad.common_neighbor_mem_vertexSet_iff
        (G := G) hapex_not_foot hadj).mpr (Or.inl hroot_apex))
    · intro hroot_feet
      exact hroot ((Triad.common_neighbor_mem_vertexSet_iff
        (G := G) hapex_not_foot hadj).mpr (Or.inr hroot_feet))
  · rintro ⟨hroot_ne_apex, hroot_not_feet⟩ hroot
    rcases (Triad.common_neighbor_mem_vertexSet_iff
      (G := G) hapex_not_foot hadj).mp hroot with hroot_apex | hroot_feet
    · exact hroot_ne_apex hroot_apex
    · exact hroot_not_feet hroot_feet

def RSTLeanTriadData.of_common_neighbor
    [Fintype V]
    {feet : Fin 3 -> V}
    {apex root : V}
    (hapex_not_foot : forall i : Fin 3, apex ≠ feet i)
    (hadj : forall i : Fin 3, G.Adj apex (feet i))
    (hroot_ne_apex : root ≠ apex)
    (hroot_not_feet : root ∉ Set.range feet)
    (hfeet_injective : Function.Injective feet)
    (hcomplement_connected :
      (G.induce (Triad.of_common_neighbor
        (G := G) hapex_not_foot hadj).vertexSetᶜ).Connected)
    (hfoot_has_neighbor_outside :
      forall i : Fin 3,
        Exists fun u : V =>
          u ∈ ((⊤ : G.Subgraph).deleteVerts
            (Triad.of_common_neighbor
              (G := G) hapex_not_foot hadj).vertexSet).verts ∧
            G.Adj u (feet i)) :
    RSTLeanTriadData G feet root where
  triad := Triad.of_common_neighbor (G := G) hapex_not_foot hadj
  lean := Triad.common_neighbor_lean (G := G) hapex_not_foot hadj
  complement_connected := hcomplement_connected
  root_outside := by
    exact (Triad.common_neighbor_root_not_mem_vertexSet_iff
      (G := G) hapex_not_foot hadj).mpr ⟨hroot_ne_apex, hroot_not_feet⟩
  inside_neighbors_at_most_three :=
    Triad.common_neighbor_inside_neighbors_at_most_three
      (G := G) hapex_not_foot hadj hfeet_injective
  foot_has_neighbor_outside := hfoot_has_neighbor_outside

theorem complete_graph_rst_lean_triad_data
    [Fintype V]
    (h_card : 5 <= Fintype.card V)
    (h_complete : forall u v : V, u ≠ v -> G.Adj u v)
    (feet : Fin 3 -> V)
    (h_triangle : IsTriangle G (feet 0) (feet 1) (feet 2))
    (root : V)
    (hroot_not_feet : root ∉ Set.range feet) :
    Nonempty (RSTLeanTriadData G feet root) := by
  classical
  let forbidden : Set V := insert root (Set.range feet)
  have hfeet_injective : Function.Injective feet :=
    IsTriangle.injective_fin3 h_triangle
  have hforbidden_card : forbidden.ncard <= 4 := by
    simpa [forbidden] using
      ncard_insert_range_fin3_le_four hfeet_injective root
  have hforbidden_compl_nonempty : forbiddenᶜ.Nonempty := by
    by_contra hnonempty
    have hforbidden_univ : forbidden = Set.univ := by
      apply Set.eq_univ_iff_forall.mpr
      intro v
      by_contra hv
      exact hnonempty ⟨v, hv⟩
    have hcard_forbidden : forbidden.ncard = Fintype.card V := by
      rw [hforbidden_univ, Set.ncard_univ, Nat.card_eq_fintype_card]
    omega
  obtain ⟨apex, hapex_forbidden⟩ := hforbidden_compl_nonempty
  have hapex_ne_root : apex ≠ root := by
    intro h
    exact hapex_forbidden (by simp [forbidden, h])
  have hapex_not_foot : forall i : Fin 3, apex ≠ feet i := by
    intro i h
    exact hapex_forbidden (by simp [forbidden, h])
  have hadj : forall i : Fin 3, G.Adj apex (feet i) := by
    intro i
    exact h_complete apex (feet i) (hapex_not_foot i)
  have hroot_ne_apex : root ≠ apex := hapex_ne_root.symm
  have hroot_outside :
      root ∉ (Triad.of_common_neighbor
        (G := G) hapex_not_foot hadj).vertexSet := by
    exact (Triad.common_neighbor_root_not_mem_vertexSet_iff
      (G := G) hapex_not_foot hadj).mpr ⟨hroot_ne_apex, hroot_not_feet⟩
  have hcomplement_connected :
      (G.induce (Triad.of_common_neighbor
        (G := G) hapex_not_foot hadj).vertexSetᶜ).Connected := by
    refine {
      preconnected := ?_
      nonempty := ?_
    }
    · intro x y
      by_cases hxy : x = y
      · subst y
        exact SimpleGraph.Reachable.refl x
      · have hxy_val : (x : V) ≠ y := by
          intro h
          exact hxy (Subtype.ext h)
        exact (show
          (G.induce (Triad.of_common_neighbor
            (G := G) hapex_not_foot hadj).vertexSetᶜ).Adj x y from
          h_complete x y hxy_val).reachable
    · exact ⟨⟨root, hroot_outside⟩⟩
  have hfoot_has_neighbor_outside :
      forall i : Fin 3,
        Exists fun u : V =>
          u ∈ ((⊤ : G.Subgraph).deleteVerts
            (Triad.of_common_neighbor
              (G := G) hapex_not_foot hadj).vertexSet).verts ∧
            G.Adj u (feet i) := by
    intro i
    have hroot_ne_foot : root ≠ feet i := by
      intro h
      exact hroot_not_feet ⟨i, h.symm⟩
    refine ⟨root, ?_, h_complete root (feet i) hroot_ne_foot⟩
    rw [SimpleGraph.Subgraph.deleteVerts_verts, Set.mem_diff]
    exact ⟨by simp, hroot_outside⟩
  exact ⟨RSTLeanTriadData.of_common_neighbor
    (G := G) hapex_not_foot hadj hroot_ne_apex hroot_not_feet
    hfeet_injective hcomplement_connected hfoot_has_neighbor_outside⟩

def CommonNeighborRSTCertificate
    (G : SimpleGraph V) (feet : Fin 3 -> V) (root : V) : Prop :=
  Exists fun apex : V =>
    Exists fun hapex_not_foot : forall i : Fin 3, apex ≠ feet i =>
      Exists fun hadj : forall i : Fin 3, G.Adj apex (feet i) =>
        root ≠ apex ∧
          (G.induce (Triad.of_common_neighbor
            (G := G) hapex_not_foot hadj).vertexSetᶜ).Connected ∧
          (forall i : Fin 3,
            Exists fun u : V =>
              u ∈ ((⊤ : G.Subgraph).deleteVerts
                (Triad.of_common_neighbor
                  (G := G) hapex_not_foot hadj).vertexSet).verts ∧
                G.Adj u (feet i))

theorem CommonNeighborRSTCertificate.of_common_neighbor
    {feet : Fin 3 -> V}
    {root apex : V}
    (hapex_not_foot : forall i : Fin 3, apex ≠ feet i)
    (hadj : forall i : Fin 3, G.Adj apex (feet i))
    (hroot_ne_apex : root ≠ apex)
    (hcomplement_connected :
      (G.induce (Triad.of_common_neighbor
        (G := G) hapex_not_foot hadj).vertexSetᶜ).Connected)
    (hfoot_has_neighbor_outside :
      forall i : Fin 3,
        Exists fun u : V =>
          u ∈ ((⊤ : G.Subgraph).deleteVerts
            (Triad.of_common_neighbor
              (G := G) hapex_not_foot hadj).vertexSet).verts ∧
            G.Adj u (feet i)) :
    CommonNeighborRSTCertificate G feet root :=
  ⟨apex, hapex_not_foot, hadj, hroot_ne_apex,
    hcomplement_connected, hfoot_has_neighbor_outside⟩

theorem CommonNeighborRSTCertificate.of_common_neighbor_four_connected
    [Fintype V]
    [DecidableRel G.Adj]
    (h_four_connected : IsFourConnected G)
    {feet : Fin 3 -> V}
    {root apex : V}
    (hfeet_injective : Function.Injective feet)
    (hapex_not_foot : forall i : Fin 3, apex ≠ feet i)
    (hadj : forall i : Fin 3, G.Adj apex (feet i))
    (hroot_ne_apex : root ≠ apex)
    (hcomplement_connected :
      (G.induce (Triad.of_common_neighbor
        (G := G) hapex_not_foot hadj).vertexSetᶜ).Connected) :
    CommonNeighborRSTCertificate G feet root := by
  refine CommonNeighborRSTCertificate.of_common_neighbor
    (G := G) hapex_not_foot hadj hroot_ne_apex hcomplement_connected ?_
  intro i
  exact exists_neighbor_outside_set_of_degree_atLeast_four_of_inside_neighbors_atMost_three
    (G := G)
    (S := (Triad.of_common_neighbor
      (G := G) hapex_not_foot hadj).vertexSet)
    (v := feet i)
    (four_connected_minDegree_atLeast_four h_four_connected (feet i))
    (Triad.common_neighbor_foot_inside_neighbors_at_most_three
      (G := G) hapex_not_foot hadj hfeet_injective i)

theorem CommonNeighborRSTCertificate.to_rstLeanTriadData
    [Fintype V]
    {feet : Fin 3 -> V}
    {root : V}
    (hcert : CommonNeighborRSTCertificate G feet root)
    (hfeet_injective : Function.Injective feet)
    (hroot_not_feet : root ∉ Set.range feet) :
    Nonempty (RSTLeanTriadData G feet root) := by
  rcases hcert with
    ⟨apex, hapex_not_foot, hadj, hroot_ne_apex,
      hcomplement_connected, hfoot_has_neighbor_outside⟩
  exact ⟨RSTLeanTriadData.of_common_neighbor
    (G := G) hapex_not_foot hadj hroot_ne_apex hroot_not_feet
    hfeet_injective hcomplement_connected hfoot_has_neighbor_outside⟩

end Schematic.Math.GraphTheory
