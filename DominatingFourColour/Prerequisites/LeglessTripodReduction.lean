import DominatingFourColour.Prerequisites.RSTFlaps.SmallComponents

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

variable {V : Type u} {G : SimpleGraph V}
theorem RST31Statement.to_rstLeanTriadData_of_flap_foot_witnesses
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    {root : V}
    (h31 : RST31Statement G feet)
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (T₀ : Triad G feet)
    (B₀ : T₀.Flap)
    (hrootB₀ : root ∈ T₀.flapVertexSet B₀)
    (hfootB₀ :
      forall i : Fin 3,
        Exists fun u : V => u ∈ T₀.flapVertexSet B₀ ∧ G.Adj u (feet i)) :
    Nonempty (RSTLeanTriadData G feet root) := by
  rcases h31 T₀ B₀ hno with ⟨D⟩
  exact ⟨D.to_rstLeanTriadData_of_foot_witnesses_in_W
    hrootB₀ hfeet_injective hfootB₀⟩

theorem Triad.punctured_foot_witnesses_in_flap
    {feet : Fin 3 -> V}
    (source target : Triad G feet)
    (hfeet_injective : Function.Injective feet)
    (B : target.Flap)
    (hsubset :
      (source.carrier.deleteVerts (Set.range feet)).verts ⊆
        target.flapVertexSet B) :
    forall i : Fin 3,
      Exists fun u : V => u ∈ target.flapVertexSet B ∧ G.Adj u (feet i) := by
  intro i
  obtain ⟨u, hu, hui⟩ :=
    source.foot_has_neighbor_in_punctured_carrier hfeet_injective i
  exact ⟨u, hsubset hu, hui⟩

theorem Triad.punctured_subset_flap_of_complement_connected
    {feet : Fin 3 -> V}
    (source target : Triad G feet)
    (hsubset :
      (source.carrier.deleteVerts (Set.range feet)).verts ⊆ target.vertexSetᶜ)
    (hconnected : (G.induce target.vertexSetᶜ).Connected)
    (B : target.Flap) :
    (source.carrier.deleteVerts (Set.range feet)).verts ⊆
      target.flapVertexSet B := by
  intro v hv
  rw [target.flapVertexSet_eq_complement_of_complement_connected hconnected B]
  exact hsubset hv

theorem Triad.punctured_subset_flap_of_walk_to_punctured
    {feet : Fin 3 -> V}
    (source target : Triad G feet)
    (hfeet_injective : Function.Injective feet)
    (hsubset :
      (source.carrier.deleteVerts (Set.range feet)).verts ⊆ target.vertexSetᶜ)
    (B : target.Flap)
    {root x : V}
    (hrootB : root ∈ target.flapVertexSet B)
    (hx : x ∈ (source.carrier.deleteVerts (Set.range feet)).verts)
    (p : G.Walk root x)
    (hp : forall z : V, z ∈ p.support -> z ∉ target.vertexSet) :
    (source.carrier.deleteVerts (Set.range feet)).verts ⊆
      target.flapVertexSet B := by
  let H : G.Subgraph := source.carrier.deleteVerts (Set.range feet)
  have hxB : x ∈ target.flapVertexSet B :=
    target.flapVertexSet_mem_of_walk B hrootB (hsubset hx) p hp
  have hconnected : H.Connected := by
    rw [SimpleGraph.Subgraph.connected_iff']
    simpa [H] using source.punctured_carrier_connected hfeet_injective
  have hwalks :=
    (SimpleGraph.Subgraph.connected_iff_forall_exists_walk_subgraph H).mp hconnected
  intro y hy
  obtain ⟨q, hq_le⟩ := hwalks.2 (by simpa [H] using hx) (by simpa [H] using hy)
  exact target.flapVertexSet_mem_of_walk B hxB (hsubset hy) q (by
    intro z hz
    have hzH : z ∈ H.verts :=
      hq_le.1 (by rwa [SimpleGraph.Walk.mem_verts_toSubgraph])
    exact hsubset (by simpa [H] using hzH))

theorem Triad.punctured_subset_flap_of_walk_to_apex
    {feet : Fin 3 -> V}
    (source target : Triad G feet)
    (hfeet_injective : Function.Injective feet)
    (hsubset :
      (source.carrier.deleteVerts (Set.range feet)).verts ⊆ target.vertexSetᶜ)
    (B : target.Flap)
    {root : V}
    (hrootB : root ∈ target.flapVertexSet B)
    (p : G.Walk root source.apex)
    (hp : forall z : V, z ∈ p.support -> z ∉ target.vertexSet) :
    (source.carrier.deleteVerts (Set.range feet)).verts ⊆
      target.flapVertexSet B := by
  apply source.punctured_subset_flap_of_walk_to_punctured target
    hfeet_injective hsubset B hrootB _ p hp
  rw [source.mem_punctured_carrier_verts_iff]
  exact ⟨source.apex_mem_vertexSet, by
    rintro ⟨i, hi⟩
    exact source.apex_not_foot i hi.symm⟩

theorem LeglessTripod.first_punctured_foot_witnesses_in_second_flap
    {feet : Fin 3 -> V}
    (T : LeglessTripod G feet)
    (hfeet_injective : Function.Injective feet)
    (B : T.second.Flap)
    (hfirst_subset_B :
      (T.first.carrier.deleteVerts (Set.range feet)).verts ⊆
        T.second.flapVertexSet B) :
    forall i : Fin 3,
      Exists fun u : V => u ∈ T.second.flapVertexSet B ∧ G.Adj u (feet i) :=
  T.first.punctured_foot_witnesses_in_flap T.second hfeet_injective B
    hfirst_subset_B

theorem LeglessTripod.second_punctured_foot_witnesses_in_first_flap
    {feet : Fin 3 -> V}
    (T : LeglessTripod G feet)
    (hfeet_injective : Function.Injective feet)
    (B : T.first.Flap)
    (hsecond_subset_B :
      (T.second.carrier.deleteVerts (Set.range feet)).verts ⊆
        T.first.flapVertexSet B) :
    forall i : Fin 3,
      Exists fun u : V => u ∈ T.first.flapVertexSet B ∧ G.Adj u (feet i) :=
  T.second.punctured_foot_witnesses_in_flap T.first hfeet_injective B
    hsecond_subset_B

theorem RST31Statement.to_rstLeanTriadData_of_legless_tripod_second_flap
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    {root : V}
    (h31 : RST31Statement G feet)
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (T : LeglessTripod G feet)
    (B : T.second.Flap)
    (hrootB : root ∈ T.second.flapVertexSet B)
    (hfirst_subset_B :
      (T.first.carrier.deleteVerts (Set.range feet)).verts ⊆
        T.second.flapVertexSet B) :
    Nonempty (RSTLeanTriadData G feet root) :=
  h31.to_rstLeanTriadData_of_flap_foot_witnesses hno hfeet_injective
    T.second B hrootB
    (T.first_punctured_foot_witnesses_in_second_flap
      hfeet_injective B hfirst_subset_B)

theorem RST31Statement.to_rstLeanTriadData_of_legless_tripod_first_flap
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    {root : V}
    (h31 : RST31Statement G feet)
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (T : LeglessTripod G feet)
    (B : T.first.Flap)
    (hrootB : root ∈ T.first.flapVertexSet B)
    (hsecond_subset_B :
      (T.second.carrier.deleteVerts (Set.range feet)).verts ⊆
        T.first.flapVertexSet B) :
    Nonempty (RSTLeanTriadData G feet root) :=
  h31.to_rstLeanTriadData_of_flap_foot_witnesses hno hfeet_injective
    T.first B hrootB
    (T.second_punctured_foot_witnesses_in_first_flap
      hfeet_injective B hsecond_subset_B)

theorem LeglessTripod.first_punctured_subset_second_flap_of_second_complement_connected
    {feet : Fin 3 -> V}
    (T : LeglessTripod G feet)
    (hconnected : (G.induce T.second.vertexSetᶜ).Connected)
    (B : T.second.Flap) :
    (T.first.carrier.deleteVerts (Set.range feet)).verts ⊆
      T.second.flapVertexSet B :=
  T.first.punctured_subset_flap_of_complement_connected T.second
    T.first_punctured_subset_second_complement hconnected B

theorem LeglessTripod.second_punctured_subset_first_flap_of_first_complement_connected
    {feet : Fin 3 -> V}
    (T : LeglessTripod G feet)
    (hconnected : (G.induce T.first.vertexSetᶜ).Connected)
    (B : T.first.Flap) :
    (T.second.carrier.deleteVerts (Set.range feet)).verts ⊆
      T.first.flapVertexSet B :=
  T.second.punctured_subset_flap_of_complement_connected T.first
    T.second_punctured_subset_first_complement hconnected B

theorem RST31Statement.to_rstLeanTriadData_of_legless_tripod_second_connected
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    {root : V}
    (h31 : RST31Statement G feet)
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (T : LeglessTripod G feet)
    (hsecond_connected : (G.induce T.second.vertexSetᶜ).Connected)
    (hroot_second : root ∉ T.second.vertexSet) :
    Nonempty (RSTLeanTriadData G feet root) := by
  obtain ⟨B, hrootB⟩ := T.second.exists_flap_containing_vertex_outside hroot_second
  exact h31.to_rstLeanTriadData_of_legless_tripod_second_flap
    hno hfeet_injective T B hrootB
    (T.first_punctured_subset_second_flap_of_second_complement_connected
      hsecond_connected B)

theorem RST31Statement.to_rstLeanTriadData_of_legless_tripod_first_connected
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    {root : V}
    (h31 : RST31Statement G feet)
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (T : LeglessTripod G feet)
    (hfirst_connected : (G.induce T.first.vertexSetᶜ).Connected)
    (hroot_first : root ∉ T.first.vertexSet) :
    Nonempty (RSTLeanTriadData G feet root) := by
  obtain ⟨B, hrootB⟩ := T.first.exists_flap_containing_vertex_outside hroot_first
  exact h31.to_rstLeanTriadData_of_legless_tripod_first_flap
    hno hfeet_injective T B hrootB
    (T.second_punctured_subset_first_flap_of_first_complement_connected
      hfirst_connected B)

theorem RST31Statement.to_rstLeanTriadData_of_legless_tripod_connected_sides
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    {root : V}
    (h31 : RST31Statement G feet)
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (hroot_not_feet : root ∉ Set.range feet)
    (T : LeglessTripod G feet)
    (hfirst_connected : (G.induce T.first.vertexSetᶜ).Connected)
    (hsecond_connected : (G.induce T.second.vertexSetᶜ).Connected) :
    Nonempty (RSTLeanTriadData G feet root) := by
  rcases T.vertex_avoids_first_or_second hroot_not_feet with hroot_first | hroot_second
  · exact h31.to_rstLeanTriadData_of_legless_tripod_first_connected
      hno hfeet_injective T hfirst_connected hroot_first
  · exact h31.to_rstLeanTriadData_of_legless_tripod_second_connected
      hno hfeet_injective T hsecond_connected hroot_second

theorem RST31Statement.to_rstLeanTriadData_of_legless_tripod_component_choice
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    {root : V}
    (h31 : RST31Statement G feet)
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (T : LeglessTripod G feet)
    (hchoice :
      (Exists fun B : T.first.Flap =>
        root ∈ T.first.flapVertexSet B ∧
          (T.second.carrier.deleteVerts (Set.range feet)).verts ⊆
            T.first.flapVertexSet B) ∨
        (Exists fun B : T.second.Flap =>
          root ∈ T.second.flapVertexSet B ∧
            (T.first.carrier.deleteVerts (Set.range feet)).verts ⊆
              T.second.flapVertexSet B)) :
    Nonempty (RSTLeanTriadData G feet root) := by
  rcases hchoice with hfirst | hsecond
  · rcases hfirst with ⟨B, hrootB, hsecond_subset_B⟩
    exact h31.to_rstLeanTriadData_of_legless_tripod_first_flap
      hno hfeet_injective T B hrootB hsecond_subset_B
  · rcases hsecond with ⟨B, hrootB, hfirst_subset_B⟩
    exact h31.to_rstLeanTriadData_of_legless_tripod_second_flap
      hno hfeet_injective T B hrootB hfirst_subset_B

theorem rst_planar_or_rst_lean_triad_data_of_literal_rst_inputs_and_component_choice
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    {root : V}
    (h31 : RST31Statement G feet)
    (h34 : RST34LeglessTripodStatement G feet)
    (h35 : RST35Statement G feet)
    (hG : IsFourConnected G)
    (hfeet_injective : Function.Injective feet)
    (hchoice :
      forall T : LeglessTripod G feet,
        (Exists fun B : T.first.Flap =>
          root ∈ T.first.flapVertexSet B ∧
            (T.second.carrier.deleteVerts (Set.range feet)).verts ⊆
              T.first.flapVertexSet B) ∨
          (Exists fun B : T.second.Flap =>
            root ∈ T.second.flapVertexSet B ∧
              (T.first.carrier.deleteVerts (Set.range feet)).verts ⊆
                T.second.flapVertexSet B)) :
    IsPlanar G ∨ Nonempty (RSTLeanTriadData G feet root) := by
  by_cases hplanar : IsPlanar G
  · exact Or.inl hplanar
  · obtain ⟨T⟩ :=
      h34.legless_tripod_of_rst35_fourConnected_nonplanar
        h35 hG hfeet_injective hplanar
    exact Or.inr
      (h31.to_rstLeanTriadData_of_legless_tripod_component_choice
        (hG.rst31_noSeparation feet) hfeet_injective T (hchoice T))

theorem LeglessTripod.first_punctured_subset_second_flap_of_walk_to_first_apex
    {feet : Fin 3 -> V}
    (T : LeglessTripod G feet)
    (hfeet_injective : Function.Injective feet)
    (B : T.second.Flap)
    {root : V}
    (hrootB : root ∈ T.second.flapVertexSet B)
    (p : G.Walk root T.first.apex)
    (hp : forall z : V, z ∈ p.support -> z ∉ T.second.vertexSet) :
    (T.first.carrier.deleteVerts (Set.range feet)).verts ⊆
      T.second.flapVertexSet B :=
  T.first.punctured_subset_flap_of_walk_to_apex T.second
    hfeet_injective T.first_punctured_subset_second_complement B
    hrootB p hp

theorem LeglessTripod.first_punctured_subset_second_flap_of_walk_to_first_punctured
    {feet : Fin 3 -> V}
    (T : LeglessTripod G feet)
    (hfeet_injective : Function.Injective feet)
    (B : T.second.Flap)
    {root x : V}
    (hrootB : root ∈ T.second.flapVertexSet B)
    (hx : x ∈ (T.first.carrier.deleteVerts (Set.range feet)).verts)
    (p : G.Walk root x)
    (hp : forall z : V, z ∈ p.support -> z ∉ T.second.vertexSet) :
    (T.first.carrier.deleteVerts (Set.range feet)).verts ⊆
      T.second.flapVertexSet B :=
  T.first.punctured_subset_flap_of_walk_to_punctured T.second
    hfeet_injective T.first_punctured_subset_second_complement B
    hrootB hx p hp

theorem LeglessTripod.second_punctured_subset_first_flap_of_walk_to_second_apex
    {feet : Fin 3 -> V}
    (T : LeglessTripod G feet)
    (hfeet_injective : Function.Injective feet)
    (B : T.first.Flap)
    {root : V}
    (hrootB : root ∈ T.first.flapVertexSet B)
    (p : G.Walk root T.second.apex)
    (hp : forall z : V, z ∈ p.support -> z ∉ T.first.vertexSet) :
    (T.second.carrier.deleteVerts (Set.range feet)).verts ⊆
      T.first.flapVertexSet B :=
  T.second.punctured_subset_flap_of_walk_to_apex T.first
    hfeet_injective T.second_punctured_subset_first_complement B
    hrootB p hp

theorem LeglessTripod.second_punctured_subset_first_flap_of_walk_to_second_punctured
    {feet : Fin 3 -> V}
    (T : LeglessTripod G feet)
    (hfeet_injective : Function.Injective feet)
    (B : T.first.Flap)
    {root x : V}
    (hrootB : root ∈ T.first.flapVertexSet B)
    (hx : x ∈ (T.second.carrier.deleteVerts (Set.range feet)).verts)
    (p : G.Walk root x)
    (hp : forall z : V, z ∈ p.support -> z ∉ T.first.vertexSet) :
    (T.second.carrier.deleteVerts (Set.range feet)).verts ⊆
      T.first.flapVertexSet B :=
  T.second.punctured_subset_flap_of_walk_to_punctured T.first
    hfeet_injective T.second_punctured_subset_first_complement B
    hrootB hx p hp

theorem LeglessTripod.component_choice_of_avoiding_walk_to_apex
    {feet : Fin 3 -> V}
    (T : LeglessTripod G feet)
    (hfeet_injective : Function.Injective feet)
    {root : V}
    (hwalk :
      (Exists fun p : G.Walk root T.second.apex =>
        forall z : V, z ∈ p.support -> z ∉ T.first.vertexSet) ∨
        (Exists fun p : G.Walk root T.first.apex =>
          forall z : V, z ∈ p.support -> z ∉ T.second.vertexSet)) :
    (Exists fun B : T.first.Flap =>
      root ∈ T.first.flapVertexSet B ∧
        (T.second.carrier.deleteVerts (Set.range feet)).verts ⊆
          T.first.flapVertexSet B) ∨
      (Exists fun B : T.second.Flap =>
        root ∈ T.second.flapVertexSet B ∧
          (T.first.carrier.deleteVerts (Set.range feet)).verts ⊆
            T.second.flapVertexSet B) := by
  rcases hwalk with hsecond | hfirst
  · rcases hsecond with ⟨p, hp⟩
    obtain ⟨B, hrootB⟩ :=
      T.first.exists_flap_containing_vertex_outside (hp root p.start_mem_support)
    exact Or.inl ⟨B, hrootB,
      T.second_punctured_subset_first_flap_of_walk_to_second_apex
        hfeet_injective B hrootB p hp⟩
  · rcases hfirst with ⟨p, hp⟩
    obtain ⟨B, hrootB⟩ :=
      T.second.exists_flap_containing_vertex_outside (hp root p.start_mem_support)
    exact Or.inr ⟨B, hrootB,
      T.first_punctured_subset_second_flap_of_walk_to_first_apex
        hfeet_injective B hrootB p hp⟩

theorem LeglessTripod.component_choice_of_avoiding_walk_to_punctured
    {feet : Fin 3 -> V}
    (T : LeglessTripod G feet)
    (hfeet_injective : Function.Injective feet)
    {root : V}
    (hwalk :
      (Exists fun x : V =>
        x ∈ (T.second.carrier.deleteVerts (Set.range feet)).verts ∧
          Exists fun p : G.Walk root x =>
            forall z : V, z ∈ p.support -> z ∉ T.first.vertexSet) ∨
        (Exists fun x : V =>
          x ∈ (T.first.carrier.deleteVerts (Set.range feet)).verts ∧
            Exists fun p : G.Walk root x =>
              forall z : V, z ∈ p.support -> z ∉ T.second.vertexSet)) :
    (Exists fun B : T.first.Flap =>
      root ∈ T.first.flapVertexSet B ∧
        (T.second.carrier.deleteVerts (Set.range feet)).verts ⊆
          T.first.flapVertexSet B) ∨
      (Exists fun B : T.second.Flap =>
        root ∈ T.second.flapVertexSet B ∧
          (T.first.carrier.deleteVerts (Set.range feet)).verts ⊆
            T.second.flapVertexSet B) := by
  rcases hwalk with hsecond | hfirst
  · rcases hsecond with ⟨x, hx, p, hp⟩
    obtain ⟨B, hrootB⟩ :=
      T.first.exists_flap_containing_vertex_outside (hp root p.start_mem_support)
    exact Or.inl ⟨B, hrootB,
      T.second_punctured_subset_first_flap_of_walk_to_second_punctured
        hfeet_injective B hrootB hx p hp⟩
  · rcases hfirst with ⟨x, hx, p, hp⟩
    obtain ⟨B, hrootB⟩ :=
      T.second.exists_flap_containing_vertex_outside (hp root p.start_mem_support)
    exact Or.inr ⟨B, hrootB,
      T.first_punctured_subset_second_flap_of_walk_to_first_punctured
        hfeet_injective B hrootB hx p hp⟩

theorem LeglessTripod.exists_avoiding_walk_to_punctured_of_delete_feet_connected
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : LeglessTripod G feet)
    {root : V}
    (hroot_not_feet : root ∉ Set.range feet)
    (hdelete_connected :
      (((⊤ : G.Subgraph).deleteVerts (Set.range feet)).coe).Connected) :
    (Exists fun x : V =>
      x ∈ (T.second.carrier.deleteVerts (Set.range feet)).verts ∧
        Exists fun p : G.Walk root x =>
          forall z : V, z ∈ p.support -> z ∉ T.first.vertexSet) ∨
      (Exists fun x : V =>
        x ∈ (T.first.carrier.deleteVerts (Set.range feet)).verts ∧
          Exists fun p : G.Walk root x =>
            forall z : V, z ∈ p.support -> z ∉ T.second.vertexSet) := by
  let H : G.Subgraph := (⊤ : G.Subgraph).deleteVerts (Set.range feet)
  have hrootH : root ∈ H.verts := by
    dsimp [H]
    exact ⟨by simp, hroot_not_feet⟩
  have hfirst_apexH : T.first.apex ∈ H.verts := by
    dsimp [H]
    exact ⟨by simp, by
      rintro ⟨i, hi⟩
      exact T.first.apex_not_foot i hi.symm⟩
  obtain ⟨p, hp_path, hpH⟩ :=
    Subgraph.Connected.exists_path_between_support_subset
      (G := G) (H := H) (by simpa [H] using hdelete_connected)
      hrootH hfirst_apexH
  let A : Set V := (T.second.carrier.deleteVerts (Set.range feet)).verts
  let B : Set V := (T.first.carrier.deleteVerts (Set.range feet)).verts
  have hdisjoint : Disjoint A B := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    have hxA' : x ∈ T.second.vertexSet ∧ x ∉ Set.range feet := by
      simpa [A] using (T.second.mem_punctured_carrier_verts_iff).mp hxA
    have hxB' : x ∈ T.first.vertexSet ∧ x ∉ Set.range feet := by
      simpa [B] using (T.first.mem_punctured_carrier_verts_iff).mp hxB
    exact hxA'.2 (T.meet_only_at_feet ⟨hxB'.1, hxA'.1⟩)
  have hfirst_apexB : T.first.apex ∈ B := by
    change T.first.apex ∈ (T.first.carrier.deleteVerts (Set.range feet)).verts
    rw [T.first.mem_punctured_carrier_verts_iff]
    exact ⟨T.first.apex_mem_vertexSet, by
      rintro ⟨i, hi⟩
      exact T.first.apex_not_foot i hi.symm⟩
  have hend : T.first.apex ∈ A ∪ B := Or.inr hfirst_apexB
  rcases Schematic.Math.GraphTheory.Walk.IsPath.exists_takeUntil_first_mem_left_or_right
      (G := G) (p := p) hp_path A B hdisjoint hend with
      hsecond | hfirst
  · rcases hsecond with ⟨x, hx_support, hxA, hpref_avoids_B⟩
    refine Or.inl ⟨x, by simpa [A] using hxA, p.takeUntil x hx_support, ?_⟩
    intro z hz hz_first
    have hz_support : z ∈ p.support :=
      SimpleGraph.Walk.support_takeUntil_subset p hx_support hz
    have hzH : z ∈ H.verts := hpH z hz_support
    have hz_not_feet : z ∉ Set.range feet := by
      dsimp [H] at hzH
      exact hzH.2
    have hzB : z ∈ B := by
      change z ∈ (T.first.carrier.deleteVerts (Set.range feet)).verts
      rw [T.first.mem_punctured_carrier_verts_iff]
      exact ⟨hz_first, hz_not_feet⟩
    exact hpref_avoids_B z hz hzB
  · rcases hfirst with ⟨x, hx_support, hxB, hpref_avoids_A⟩
    refine Or.inr ⟨x, by simpa [B] using hxB, p.takeUntil x hx_support, ?_⟩
    intro z hz hz_second
    have hz_support : z ∈ p.support :=
      SimpleGraph.Walk.support_takeUntil_subset p hx_support hz
    have hzH : z ∈ H.verts := hpH z hz_support
    have hz_not_feet : z ∉ Set.range feet := by
      dsimp [H] at hzH
      exact hzH.2
    have hzA : z ∈ A := by
      change z ∈ (T.second.carrier.deleteVerts (Set.range feet)).verts
      rw [T.second.mem_punctured_carrier_verts_iff]
      exact ⟨hz_second, hz_not_feet⟩
    exact hpref_avoids_A z hz hzA

theorem LeglessTripod.exists_avoiding_walk_to_punctured_of_four_connected
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : LeglessTripod G feet)
    (hG : IsFourConnected G)
    {root : V}
    (hroot_not_feet : root ∉ Set.range feet) :
    (Exists fun x : V =>
      x ∈ (T.second.carrier.deleteVerts (Set.range feet)).verts ∧
        Exists fun p : G.Walk root x =>
          forall z : V, z ∈ p.support -> z ∉ T.first.vertexSet) ∨
      (Exists fun x : V =>
        x ∈ (T.first.carrier.deleteVerts (Set.range feet)).verts ∧
          Exists fun p : G.Walk root x =>
            forall z : V, z ∈ p.support -> z ∉ T.second.vertexSet) := by
  exact T.exists_avoiding_walk_to_punctured_of_delete_feet_connected
    hroot_not_feet (by
      have hconn :=
        isFourConnected_delete_triple_top_connected
          (G := G) hG (feet 0) (feet 1) (feet 2)
      have hrange : ({feet 0, feet 1, feet 2} : Set V) = Set.range feet :=
        (fin3_range_eq_insert feet).symm
      rw [hrange] at hconn
      exact hconn)

theorem LeglessTripod.component_choice_of_delete_feet_connected
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : LeglessTripod G feet)
    (hfeet_injective : Function.Injective feet)
    {root : V}
    (hroot_not_feet : root ∉ Set.range feet)
    (hdelete_connected :
      (((⊤ : G.Subgraph).deleteVerts (Set.range feet)).coe).Connected) :
    (Exists fun B : T.first.Flap =>
      root ∈ T.first.flapVertexSet B ∧
        (T.second.carrier.deleteVerts (Set.range feet)).verts ⊆
          T.first.flapVertexSet B) ∨
      (Exists fun B : T.second.Flap =>
        root ∈ T.second.flapVertexSet B ∧
          (T.first.carrier.deleteVerts (Set.range feet)).verts ⊆
            T.second.flapVertexSet B) :=
  T.component_choice_of_avoiding_walk_to_punctured hfeet_injective
    (T.exists_avoiding_walk_to_punctured_of_delete_feet_connected
      hroot_not_feet hdelete_connected)

theorem LeglessTripod.component_choice_of_four_connected
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : LeglessTripod G feet)
    (hfeet_injective : Function.Injective feet)
    (hG : IsFourConnected G)
    {root : V}
    (hroot_not_feet : root ∉ Set.range feet) :
    (Exists fun B : T.first.Flap =>
      root ∈ T.first.flapVertexSet B ∧
        (T.second.carrier.deleteVerts (Set.range feet)).verts ⊆
          T.first.flapVertexSet B) ∨
      (Exists fun B : T.second.Flap =>
        root ∈ T.second.flapVertexSet B ∧
          (T.first.carrier.deleteVerts (Set.range feet)).verts ⊆
            T.second.flapVertexSet B) :=
  T.component_choice_of_avoiding_walk_to_punctured hfeet_injective
    (T.exists_avoiding_walk_to_punctured_of_four_connected hG hroot_not_feet)

theorem RST31Statement.to_rstLeanTriadData_of_legless_tripod_avoiding_walk_to_apex
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    {root : V}
    (h31 : RST31Statement G feet)
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (T : LeglessTripod G feet)
    (hwalk :
      (Exists fun p : G.Walk root T.second.apex =>
        forall z : V, z ∈ p.support -> z ∉ T.first.vertexSet) ∨
        (Exists fun p : G.Walk root T.first.apex =>
          forall z : V, z ∈ p.support -> z ∉ T.second.vertexSet)) :
    Nonempty (RSTLeanTriadData G feet root) :=
  h31.to_rstLeanTriadData_of_legless_tripod_component_choice
    hno hfeet_injective T
    (T.component_choice_of_avoiding_walk_to_apex hfeet_injective hwalk)

theorem RST31Statement.to_rstLeanTriadData_of_legless_tripod_avoiding_walk_to_punctured
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    {root : V}
    (h31 : RST31Statement G feet)
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (T : LeglessTripod G feet)
    (hwalk :
      (Exists fun x : V =>
        x ∈ (T.second.carrier.deleteVerts (Set.range feet)).verts ∧
          Exists fun p : G.Walk root x =>
            forall z : V, z ∈ p.support -> z ∉ T.first.vertexSet) ∨
        (Exists fun x : V =>
          x ∈ (T.first.carrier.deleteVerts (Set.range feet)).verts ∧
            Exists fun p : G.Walk root x =>
              forall z : V, z ∈ p.support -> z ∉ T.second.vertexSet)) :
    Nonempty (RSTLeanTriadData G feet root) :=
  h31.to_rstLeanTriadData_of_legless_tripod_component_choice
    hno hfeet_injective T
    (T.component_choice_of_avoiding_walk_to_punctured hfeet_injective hwalk)

theorem RST31Statement.to_rstLeanTriadData_of_legless_tripod_delete_feet_connected
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    {root : V}
    (h31 : RST31Statement G feet)
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (T : LeglessTripod G feet)
    (hroot_not_feet : root ∉ Set.range feet)
    (hdelete_connected :
      (((⊤ : G.Subgraph).deleteVerts (Set.range feet)).coe).Connected) :
    Nonempty (RSTLeanTriadData G feet root) :=
  h31.to_rstLeanTriadData_of_legless_tripod_avoiding_walk_to_punctured
    hno hfeet_injective T
    (T.exists_avoiding_walk_to_punctured_of_delete_feet_connected
      hroot_not_feet hdelete_connected)

theorem RST31Statement.to_rstLeanTriadData_of_legless_tripod_four_connected
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    {root : V}
    (h31 : RST31Statement G feet)
    (hG : IsFourConnected G)
    (hfeet_injective : Function.Injective feet)
    (T : LeglessTripod G feet)
    (hroot_not_feet : root ∉ Set.range feet) :
    Nonempty (RSTLeanTriadData G feet root) :=
  h31.to_rstLeanTriadData_of_legless_tripod_avoiding_walk_to_punctured
    (hG.rst31_noSeparation feet) hfeet_injective T
    (T.exists_avoiding_walk_to_punctured_of_four_connected hG hroot_not_feet)

theorem rst_planar_or_rst_lean_triad_data_of_literal_rst_inputs_and_avoiding_walk_choice
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    {root : V}
    (h31 : RST31Statement G feet)
    (h34 : RST34LeglessTripodStatement G feet)
    (h35 : RST35Statement G feet)
    (hG : IsFourConnected G)
    (hfeet_injective : Function.Injective feet)
    (hchoice :
      forall T : LeglessTripod G feet,
        (Exists fun p : G.Walk root T.second.apex =>
          forall z : V, z ∈ p.support -> z ∉ T.first.vertexSet) ∨
          (Exists fun p : G.Walk root T.first.apex =>
            forall z : V, z ∈ p.support -> z ∉ T.second.vertexSet)) :
    IsPlanar G ∨ Nonempty (RSTLeanTriadData G feet root) := by
  by_cases hplanar : IsPlanar G
  · exact Or.inl hplanar
  · obtain ⟨T⟩ :=
      h34.legless_tripod_of_rst35_fourConnected_nonplanar
        h35 hG hfeet_injective hplanar
    exact Or.inr
      (h31.to_rstLeanTriadData_of_legless_tripod_avoiding_walk_to_apex
        (hG.rst31_noSeparation feet) hfeet_injective T (hchoice T))

theorem rst_planar_or_rst_lean_triad_data_of_literal_rst_inputs_and_punctured_walk_choice
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    {root : V}
    (h31 : RST31Statement G feet)
    (h34 : RST34LeglessTripodStatement G feet)
    (h35 : RST35Statement G feet)
    (hG : IsFourConnected G)
    (hfeet_injective : Function.Injective feet)
    (hchoice :
      forall T : LeglessTripod G feet,
        (Exists fun x : V =>
          x ∈ (T.second.carrier.deleteVerts (Set.range feet)).verts ∧
            Exists fun p : G.Walk root x =>
              forall z : V, z ∈ p.support -> z ∉ T.first.vertexSet) ∨
          (Exists fun x : V =>
            x ∈ (T.first.carrier.deleteVerts (Set.range feet)).verts ∧
              Exists fun p : G.Walk root x =>
                forall z : V, z ∈ p.support -> z ∉ T.second.vertexSet)) :
    IsPlanar G ∨ Nonempty (RSTLeanTriadData G feet root) := by
  by_cases hplanar : IsPlanar G
  · exact Or.inl hplanar
  · obtain ⟨T⟩ :=
      h34.legless_tripod_of_rst35_fourConnected_nonplanar
        h35 hG hfeet_injective hplanar
    exact Or.inr
      (h31.to_rstLeanTriadData_of_legless_tripod_avoiding_walk_to_punctured
        (hG.rst31_noSeparation feet) hfeet_injective T (hchoice T))

theorem rst_planar_or_rst_lean_triad_data_of_literal_rst_inputs
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    {root : V}
    (h31 : RST31Statement G feet)
    (h34 : RST34LeglessTripodStatement G feet)
    (h35 : RST35Statement G feet)
    (hG : IsFourConnected G)
    (hfeet_injective : Function.Injective feet)
    (hroot_not_feet : root ∉ Set.range feet) :
    IsPlanar G ∨ Nonempty (RSTLeanTriadData G feet root) :=
  rst_planar_or_rst_lean_triad_data_of_literal_rst_inputs_and_punctured_walk_choice
    (G := G) h31 h34 h35 hG hfeet_injective
    (fun T => T.exists_avoiding_walk_to_punctured_of_four_connected
      hG hroot_not_feet)

theorem rst_planar_or_rst_lean_triad_data_of_literal_rst_oneflap_inputs_and_punctured_walk_choice
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    {root : V}
    (h31 : RST31OneFlapStatement G feet)
    (h34 : RST34LeglessTripodStatement G feet)
    (h35 : RST35Statement G feet)
    (hG : IsFourConnected G)
    (hfeet_injective : Function.Injective feet)
    (hchoice :
      forall T : LeglessTripod G feet,
        (Exists fun x : V =>
          x ∈ (T.second.carrier.deleteVerts (Set.range feet)).verts ∧
            Exists fun p : G.Walk root x =>
              forall z : V, z ∈ p.support -> z ∉ T.first.vertexSet) ∨
          (Exists fun x : V =>
            x ∈ (T.first.carrier.deleteVerts (Set.range feet)).verts ∧
              Exists fun p : G.Walk root x =>
                forall z : V, z ∈ p.support -> z ∉ T.second.vertexSet)) :
    IsPlanar G ∨ Nonempty (RSTLeanTriadData G feet root) :=
  rst_planar_or_rst_lean_triad_data_of_literal_rst_inputs_and_punctured_walk_choice
    (G := G) h31.to_rst31Statement h34 h35 hG hfeet_injective hchoice

theorem rst_planar_or_rst_lean_triad_data_of_literal_rst_oneflap_inputs
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    {root : V}
    (h31 : RST31OneFlapStatement G feet)
    (h34 : RST34LeglessTripodStatement G feet)
    (h35 : RST35Statement G feet)
    (hG : IsFourConnected G)
    (hfeet_injective : Function.Injective feet)
    (hroot_not_feet : root ∉ Set.range feet) :
    IsPlanar G ∨ Nonempty (RSTLeanTriadData G feet root) :=
  rst_planar_or_rst_lean_triad_data_of_literal_rst_inputs
    (G := G) h31.to_rst31Statement h34 h35 hG hfeet_injective
    hroot_not_feet

end Schematic.Math.GraphTheory
