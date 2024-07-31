import tactic          -- standard proof tactics
import data.set.basic        -- basics on sets
import data.set.finite -- basics on finite sets
import data.finset.basic     -- type-level finite sets
import .simplicial_complex
import .simplicial_subcomplex
import .simplicial_map

variables {α β : Type*}
variables [decidable_eq α] [decidable_eq β]

def stellar_subdivision
    (X : simplicial_complex α)
    (s : finset α) [nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : simplicial_complex α
:= (X\St(X, s) s_in_X) ∪ (π₁ (barycenter_join_boundary_disjoint_link X s x s_in_X x_nin_X))[((π₁ (barycenter_disjoint_boundary X s x s_in_X x_nin_X))[(simplex {x} ⋆ ∂s)] ⋆ Lk(X, s) s_in_X)]
notation `σ(` X `, ` s `, ` x `; ` s_ne `, ` s_in_X `, ` x_nin_X `)` := @stellar_subdivision _ _ X s s_ne x s_in_X x_nin_X

instance stellar_subdivision.fintype
    (X : simplicial_complex α) [fintype X.simplices]
    (s : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : fintype (σ(X, s, x; s_ne, s_in_X, x_nin_X)).simplices
:= begin
  simp only [stellar_subdivision, simplicial_union],

  have star_comp_fin : fintype ↥(X\St(X, s) s_in_X).simplices, by apply star_complement.fintype,
  have barycenter_fin : fintype ↥(simplex {x}).simplices, by apply @simplex.fintype α,
  have bd_fin : fintype ↥(∂s).simplices, by apply simplex_boundary.fintype,

  have barycenter_bd_fin : fintype ↥(simplex {x} ⋆ ∂s).simplices, by apply @simplicial_join.fintype _ _ (simplex {x}) barycenter_fin (∂s) bd_fin,
  have proj_bary_bd_fin : fintype ↥((π₁ (barycenter_disjoint_boundary X s x s_in_X x_nin_X))[(simplex {x} ⋆ ∂s)]).simplices, by apply @simplicial_coe.fintype _ _ _ _ _ barycenter_bd_fin,

  have link_fin : fintype ↥(Lk(X, s) s_in_X).simplices, by apply link.fintype,
  have proj_link_fin : fintype ↥(((π₁ (barycenter_disjoint_boundary X s x s_in_X x_nin_X))[(simplex {x} ⋆ ∂s)] ⋆ Lk(X, s) s_in_X)).simplices, by apply @simplicial_join.fintype _ _ _ proj_bary_bd_fin _ link_fin,
  have join_fin : fintype ↥((π₁ (barycenter_join_boundary_disjoint_link X s x s_in_X x_nin_X))[((π₁ (barycenter_disjoint_boundary X s x s_in_X x_nin_X))[(simplex {x} ⋆ ∂s)] ⋆ Lk(X, s) s_in_X)]).simplices, by apply @simplicial_coe.fintype _ _ _ _ _ proj_link_fin,

  apply @set.fintype_union _ _ _ _ star_comp_fin join_fin,
end

lemma stellar_subdiv_preserves_dim
    (X : simplicial_complex α) [X_fin : fintype X.simplices]
    (s : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : dim_of_complex X = dim_of_complex (σ(X, s, x; s_ne, s_in_X, x_nin_X))
:= begin
  simp only [dim_of_complex, le_antisymm_iff],
  split,

  { rw [finset.max'_le_iff],
    intros n n_X_dim,
    rw [finset.mem_image] at n_X_dim,
    choose t t_in_X dim_t_n using n_X_dim,
    rw [set.mem_to_finset] at t_in_X,
    apply finset.le_max',
    rw [finset.mem_image],
    
    by_cases s_ss_t : s ⊆ t,

    { have s_nontriv : ∃ (a : α), a ∈ s, from
      begin
        apply finset.nonempty.bex,
        rw [←finset.nonempty_coe_sort],
        assumption,
      end,
      choose a a_in_s using s_nontriv,

      have a_in_t : a ∈ t, by apply finset.mem_of_subset s_ss_t a_in_s,
      
      use (t \ {a} ∪ {x}), split,
      simp only [set.mem_to_finset],
      unfold stellar_subdivision,
      simp only [simplicial_union, set.mem_union],
      
      right,
      simp only [join_proj_mem],
      use ({x} ∪ s \ {a}), split,
      use {x}, split,
      simp only [simplex, finset.mem_coe],
      apply finset.mem_powerset_self,
      
      use (s \ {a}), split,
      rw [simplex_boundary_mem_iff_subset],
      apply finset.sdiff_ssubset,
      rw [finset.singleton_subset_iff],
      assumption,
      apply finset.singleton_nonempty,
      refl,
      
      use (t \ {a} \ s), split,
      simp only [link, set.mem_sep_iff],
      split,
      apply X.subset_closed t,
      assumption,
      apply @finset.subset.trans _ _ (t \ {a});
      apply finset.sdiff_subset,

      split,
      rw [finset.union_sdiff_self_eq_union],
      apply X.subset_closed t,
      assumption,
      apply finset.union_subset,
      assumption,
      apply finset.sdiff_subset,

      apply finset.inter_sdiff_self,

      rw [finset.union_assoc, finset.sdiff_sdiff_left', finset.union_distrib_left],
      have sa_ta_rw : s \ {a} ∪ t \ {a} = t \ {a}, from
      begin
        rw [finset.union_eq_right_iff_subset],
        apply finset.sdiff_subset_sdiff,
        assumption,
        refl,
      end,

      have ts_inter_ta_rw : t \ s ∩ (t \ {a}) = t \ s, from
      begin
        rw [finset.inter_eq_left_iff_subset],
        apply finset.sdiff_subset_sdiff,
        refl,
        rw [finset.singleton_subset_iff],
        assumption,
      end,

      have tsa_rw : (t ∩ s) \ {a} = s \ {a}, from
      begin
        have ts_rw : t ∩ s = s, from
        begin
          rw [finset.inter_eq_right_iff_subset],
          assumption,
        end,
        rw [ts_rw],
      end,

      have ts_union_sa_rw : t \ s ∪ s \ {a} = t \ {a}, from
      begin
        apply finset.sdiff_union_sdiff_cancel,
        assumption,
        rw [finset.singleton_subset_iff],
        assumption,
      end,

      have sa_ts_rw : s \ {a} ∪ t \ s = t \ {a}, from
      begin
        conv_rhs {
          rw [←@finset.sdiff_union_inter _ _ t s, finset.union_sdiff_distrib, finset.sdiff_sdiff_left', ts_inter_ta_rw, tsa_rw, ts_union_sa_rw],
        },
        rw [finset.union_comm],
        apply finset.sdiff_union_sdiff_cancel,
        assumption,
        rw [finset.singleton_subset_iff],
        assumption,
      end,
      rw [sa_ta_rw, sa_ts_rw, finset.inter_self, finset.union_comm],
      
      rw [dim] at dim_t_n,
      rw [dim, finset.card_disjoint_union, finset.card_sdiff, finset.card_singleton, finset.card_singleton, ←dim_t_n],
      simp only [nat.cast_add, nat.cast_one, add_tsub_cancel_right],
      have t_nontriv : t.card > 0, from
      begin
        apply finset.nonempty.card_pos,
        apply finset.nonempty.mono s_ss_t,
        rw [←finset.nonempty_coe_sort],
        assumption,
      end,
      apply nat.cast_pred t_nontriv,
      
      rw [finset.singleton_subset_iff],
      assumption,
      
      rw [finset.disjoint_iff_ne],
      intros b b_in_ta c c_eq_x,
      rw [finset.mem_sdiff, finset.mem_singleton] at b_in_ta,
      rw [finset.mem_singleton] at c_eq_x,
      subst c_eq_x,
      
      revert x_nin_X,
      contrapose,
      simp only [not_not],
      intros b_eq_c,
      subst b_eq_c,
      
      rw [vertex_iff_in_simplex],
      use t, split, assumption,
      choose b_in_t b_ne_a using b_in_ta,
      assumption, },
      
    { use t, split,
      rw [set.mem_to_finset, stellar_subdivision],
      simp only [simplicial_union, set.mem_union],

      left,
      simp only [star_complement, set.mem_sep_iff],
      split; assumption,
      assumption, }, },

  { rw [finset.max'_le_iff],
    intros n n_X_dim,
    rw [finset.mem_image] at n_X_dim,
    choose t t_in_subdiv dim_t_n using n_X_dim,
    rw [set.mem_to_finset] at t_in_subdiv,
    apply finset.le_max',
    rw [finset.mem_image],
    
    simp only [stellar_subdivision, simplicial_union, set.mem_union] at t_in_subdiv,
    cases t_in_subdiv with t_in_star_comp t_in_join,
    
    simp only [star_complement, set.mem_sep_iff] at t_in_star_comp,
    choose t_in_X s_nss_t using t_in_star_comp,
    use t, split,
    rw [set.mem_to_finset],
    assumption,
    assumption,
    
    simp only [join_proj_mem] at t_in_join,
    choose t' t'_in_join t₁ t₁_in_link t_decomp using t_in_join,
    choose t₃ t₃_in_barycenter t₂ t₂_in_bd t'_decomp using t'_in_join,
    subst t'_decomp,
    simp only [simplex, finset.mem_coe, finset.mem_powerset, finset.subset_singleton_iff] at t₃_in_barycenter,
    cases t₃_in_barycenter with t₃_empty t₃_eq_x,
    
    { use (t₁ ∪ t₂), split,
      rw [set.mem_to_finset],
      apply X.subset_closed (s ∪ t₁),
      
      simp only [link, set.mem_sep_iff] at t₁_in_link,
      choose t₁_in_link st₁_in_link st₁_disj using t₁_in_link,
      assumption,
      
      rw [finset.union_comm],
      apply finset.union_subset_union_left,
      rw [simplex_boundary_mem_iff_subset, finset.ssubset_iff_subset_ne] at t₂_in_bd,
      choose t₂_ss_s t₂_ne_s using t₂_in_bd,
      assumption,
      
      rw [t₃_empty, finset.empty_union, finset.union_comm] at t_decomp,
      rw [←t_decomp],
      assumption, },
    
    { rw [simplex_boundary_mem_iff_subset, finset.ssubset_iff] at t₂_in_bd,
      choose a a_nin_t₂ at₂_ss_s using t₂_in_bd,

      simp only [link, set.mem_sep_iff] at t₁_in_link,
      choose t₁_in_X st₁_in_X st₁_disj using t₁_in_link,
      
      use (t₁ ∪ insert a t₂), split,
      rw [set.mem_to_finset],
      apply X.subset_closed (s ∪ t₁),
      assumption,
      
      rw [finset.union_comm],
      apply finset.union_subset_union_left,
      assumption,
      
      rw [←dim_t_n, t_decomp, t₃_eq_x],
      simp only [dim, finset.union_insert, finset.union_assoc, sub_left_inj, nat.cast_inj],
      rw [finset.card_insert_of_not_mem, @finset.card_disjoint_union _ {x}, finset.card_singleton, nat.add_comm, finset.union_comm],
      
      rw [finset.disjoint_singleton_left],
      by_contradiction x_in_t,
      have contra : x ∈ vertices X, from
      begin
        rw [vertex_iff_in_simplex],
        use (s ∪ t₁), split, assumption,
        apply @finset.mem_of_subset _ (t₂ ∪ t₁),
        apply finset.union_subset_union_left,
        apply @finset.subset.trans _ _ (insert a t₂),
        apply finset.subset_insert,
        assumption,
        assumption,
      end,
      contradiction,
      
      rw [finset.mem_union, not_or_distrib],
      split,
      
      simp only [finset.eq_empty_iff_forall_not_mem, finset.mem_inter, not_and] at st₁_disj,
      have a_in_s : a ∈ s, from
      begin
        apply finset.mem_of_subset at₂_ss_s,
        apply finset.mem_insert_self,
      end,
      specialize st₁_disj a a_in_s,
      assumption,
      
      assumption, }, },
end

lemma stellar_subdiv_of_singleton_vertices
    (X : simplicial_complex α)
    (x y : α)
    (y_in_X : {y} ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : vertices (σ(X, {y}, x; (by { apply finset.nonempty.coe_sort, apply finset.singleton_nonempty, }), y_in_X, x_nin_X))
      = (vertices X \ {y}) ∪ {x}
:= begin
  simp only [set.ext_iff, stellar_subdivision, simplicial_union, join_proj_mem, vertex_iff_in_simplex, set.mem_union, set.mem_diff, set.mem_singleton_iff],
  intros a,
  split,

  { intro a_in_subdiv,
    choose s s_in_subdiv a_in_s using a_in_subdiv,
    cases s_in_subdiv with s_in_star_comp s_in_join,
    
    simp only [star_complement, set.mem_sep_iff, finset.singleton_subset_iff] at s_in_star_comp,
    choose s_in_X y_nin_s using s_in_star_comp,
    use s, split; assumption,
    by_cases a_eq_y : a = y,
    rw [a_eq_y] at a_in_s,
    contradiction,
    assumption,
    
    choose s' s'_in_join s₁ s₁_in_link s_decomp using s_in_join,
    choose s₃ s₃_in_barycenter s₂ s₂_in_bd s'_decomp using s'_in_join,
    subst s'_decomp,
    
    have s₂_empty : s₂ = ∅, from
    begin
      simp only [simplex_boundary, set.mem_union, set.mem_diff, set.mem_singleton_iff, finset.mem_coe, finset.mem_powerset, finset.subset_singleton_iff] at s₂_in_bd,
      cases s₂_in_bd with s₂_in_bd s₂_empty,

      choose s₂_ss_y s₂_ne_y using s₂_in_bd,
      cases s₂_ss_y with s₂_empty contra,
      assumption,
      contradiction,

      assumption,
    end,
    subst s₂_empty,
    rw [finset.union_empty] at s_decomp,
    
    by_cases a_eq_x : a = x,
    right, assumption,
    
    have a_nin_s₃ : a ∉ s₃, from
    begin
      simp only [simplex, finset.mem_coe, finset.mem_powerset, finset.subset_singleton_iff] at s₃_in_barycenter,
      cases s₃_in_barycenter with s₃_empty s₃_eq_x,
      rw [s₃_empty],
      apply finset.not_mem_empty,
      rw [s₃_eq_x, finset.mem_singleton],
      assumption,
    end,
    
    have a_in_s₁ : a ∈ s₁, from
    begin
      rw [s_decomp, finset.mem_union] at a_in_s,
      cases a_in_s with contra a_in_s₁,
      contradiction,
      assumption,
    end,
    
    simp only [link, set.mem_sep_iff] at s₁_in_link,
    choose s₁_in_X ys₁_in_X ys₁_disj using s₁_in_link,
    use s₁, split; assumption,
    
    rw [finset.eq_empty_iff_forall_not_mem] at ys₁_disj,
    specialize ys₁_disj a,
    rw [finset.mem_inter, finset.mem_singleton, not_and] at ys₁_disj,
    
    by_cases a_eq_y : a = y,
    specialize ys₁_disj a_eq_y,
    contradiction,
    assumption, },

  { intro a_in_union,
    cases a_in_union with a_in_X a_eq_x,
    
    choose a_in_s a_ne_y using a_in_X,
    choose s s_in_X a_in_s using a_in_s,
    use (s \ {y}), split, left,
    simp only [star_complement, set.mem_sep_iff],
    split,
    
    apply X.subset_closed s,
    assumption,
    apply finset.sdiff_subset,
    
    rw [finset.singleton_subset_iff, finset.mem_sdiff, not_and, finset.mem_singleton, not_not],
    intros y_in_s,
    refl,
    
    rw [finset.mem_sdiff, finset.mem_singleton],
    split; assumption,
    
    use {x}, split, right,
    use {x}, split,
    use {x}, split,
    simp only [simplex, finset.mem_coe],
    apply finset.mem_powerset_self,
    
    use ∅, split,
    apply simplicial_complex_empty_simplex,
    rw [finset.union_empty],
    
    use ∅, split,
    apply simplicial_complex_empty_simplex,
    rw [finset.union_empty],
    
    rw [a_eq_x],
    apply finset.mem_singleton_self, },
end

lemma stellar_subdiv_subset_vertices
    (X : simplicial_complex α)
    (s : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : vertices (σ(X, s, x; s_ne, s_in_X, x_nin_X)) ⊆ vertices X ∪ {x}
:= begin
  simp only [vertices_set_of, set.subset_def, stellar_subdivision, simplicial_union, set.mem_union, set.mem_set_of, join_proj_mem],
  intros a a_in_subdiv,
  choose t t_in_subdiv a_in_t using a_in_subdiv,
  cases t_in_subdiv with t_in_star_comp t_in_join,
  
  left,
  use t, split,
  apply simplex_if_in_subcomplex (X\St(X, s) s_in_X),
  assumption,
  apply star_complement_subcomplex,
  assumption,
  
  choose t' t'_in_join t₁ t₁_in_link t_decomp using t_in_join,
  choose t₃ t₃_in_barycenter t₂ t₂_in_bd t'_decomp using t'_in_join,
  subst t'_decomp,
  subst t_decomp,
  simp only [finset.mem_union] at a_in_t,
  cases a_in_t with a_in_t a_in_t₁,
  cases a_in_t with a_in_t₃ a_in_t₂,
  
  right,
  have a_in_x : a ∈ vertices (simplex {x}), from
  begin
    rw [vertex_iff_in_simplex],
    use t₃, split; assumption,
  end,
  rw [simplex_vertices, finset.mem_coe, finset.mem_singleton] at a_in_x,
  simp only [set.mem_singleton_iff],
  assumption,
  
  left,
  use t₂, split,
  apply simplex_if_in_subcomplex (∂s),
  assumption,
  apply simplex_boundary_subcomplex,
  assumption,
  assumption,
  
  use t₁, split,
  apply simplex_if_in_subcomplex (Lk(X, s) s_in_X),
  assumption,
  apply link_subcomplex,
  assumption,
end

lemma stellar_subdiv_vertices
    (X : simplicial_complex α)
    (s : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : s.card > 1 → vertices (σ(X, s, x; s_ne, s_in_X, x_nin_X)) = vertices X ∪ {x}
:= begin
  intros s_nontriv,
  rw [set.subset.antisymm_iff],
  split,

  apply stellar_subdiv_subset_vertices,

  rw [set.subset_def],
  intros a a_in_union,
  rw [set.mem_union, set.mem_singleton_iff, vertex_iff_in_simplex] at a_in_union,
  simp only [vertex_iff_in_simplex, stellar_subdivision, simplicial_union, set.mem_union, join_proj_mem],
  cases a_in_union with a_in_X a_eq_x,

  choose t t_in_X a_in_t using a_in_X,
  use {a}, split, left,
  simp only [star_complement, set.mem_sep_iff],
  split,

  apply X.subset_closed t,
  assumption,
  rw [finset.singleton_subset_iff],
  assumption,

  have a_le_s : ¬s.card ≤ 1, by exact not_le.mpr s_nontriv,
  rw [←finset.card_singleton a] at a_le_s,
  revert a_le_s,
  contrapose,
  simp only [not_not],
  apply finset.card_le_of_subset,

  apply finset.mem_singleton_self,

  use {x}, split, right,
  use {x}, split,
  use {x}, split,
  simp only [simplex, finset.mem_coe],
  apply finset.mem_powerset_self,

  use ∅, split,
  apply simplicial_complex_empty_simplex,
  rw [finset.union_empty],

  use ∅, split,
  apply simplicial_complex_empty_simplex,
  rw [finset.union_empty],

  rw [a_eq_x],
  apply finset.mem_singleton_self,
end

def barycenter_star
    (X : simplicial_complex α)
    (s : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : set (finset α)
:= {t ∈ (σ(X, s, x; s_ne, s_in_X, x_nin_X)).simplices | x ∈ t}

instance barycenter_star.fintype
    (X : simplicial_complex α)
    (s : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    [fintype (σ(X, s, x; s_ne, s_in_X, x_nin_X)).simplices]
  : fintype (barycenter_star X s x s_in_X x_nin_X)
:= begin
  simp only [barycenter_star],
  apply set.fintype_sep,
end

def barycenter_weld
    (X : simplicial_complex α)
    (s : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : set (finset α)
:= {(s ∪ (t \ {x})) | (t ∈ barycenter_star X s x s_in_X x_nin_X)}

lemma barycenter_weld_as_union
    (X : simplicial_complex α)
    (s : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : barycenter_weld X s x s_in_X x_nin_X = ⋃ (t ∈ barycenter_star X s x s_in_X x_nin_X), {s ∪ (t \ {x})}
:= begin
  simp only [barycenter_weld, set.ext_iff, set.mem_Union, set.mem_set_of, set.mem_singleton_iff],
  intro t,
  split,

  intro t_in_weld,
  choose u u_in_star t_su using t_in_weld,
  use u, split, assumption,
  symmetry, assumption,

  intro t_in_union,
  choose u u_in_star t_su using t_in_union,
  use u, split, assumption,
  symmetry, assumption,
end

instance barycenter_weld.fintype
    (X : simplicial_complex α)
    (s : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    [fintype (σ(X, s, x; s_ne, s_in_X, x_nin_X)).simplices]
  : fintype (barycenter_weld X s x s_in_X x_nin_X)
:= begin
  rw [barycenter_weld_as_union],
  apply set.fintype_bUnion,
  intros t t_in_star,
  apply unique.fintype,
end

lemma stellar_weld_simplices
    (X : simplicial_complex α)
    (s : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : X.simplices = {t ∈ (σ(X, s, x; s_ne, s_in_X, x_nin_X)).simplices | x ∉ t} ∪ (barycenter_weld X s x s_in_X x_nin_X)
:= begin
  simp only [barycenter_weld, set.ext_iff, set.mem_union, set.mem_sep_iff, set.mem_set_of],
  intros t,
  split,

  { intros t_in_X,
    by_cases s_ss_t : s ⊆ t,
    
    right,
    use ((t \ s) ∪ {x}), split,
    simp only [barycenter_star, set.mem_sep_iff, stellar_subdivision, simplicial_union, set.mem_union, join_proj_mem],
    split, right,
    
    use ({x} ∪ ∅), split,
    use {x}, split,
    simp only [simplex, finset.mem_coe],
    apply finset.mem_powerset_self,
    
    use ∅, split, apply simplicial_complex_empty_simplex,
    refl,
    
    use (t \ s), split,
    simp only [link, set.mem_sep_iff],
    split,
    apply X.subset_closed t,
    assumption,
    apply finset.sdiff_subset,
    
    split,
    rw [finset.union_sdiff_of_subset],
    assumption,
    assumption,
    
    apply finset.inter_sdiff_self,
    
    rw [finset.union_empty, finset.union_comm],
    
    rw [finset.mem_union],
    right,
    apply finset.mem_singleton_self,
    
    rw [finset.union_sdiff_distrib, finset.sdiff_self, finset.union_empty, finset.sdiff_sdiff_left', finset.union_distrib_left],
    rw [finset.union_sdiff_of_subset, finset.sdiff_eq_self_of_disjoint],
    have st_rw : s ∪ t = t, from
    begin
      rw [finset.union_eq_right_iff_subset],
      assumption,
    end,
    rw [st_rw, finset.inter_self],
    
    rw [finset.disjoint_singleton_right],
    revert x_nin_X,
    contrapose,
    simp only [not_not],
    intros x_in_t,
    rw [vertex_iff_in_simplex],
    use t, split; assumption,
    
    assumption,
    
    left, split,
    simp only [stellar_subdivision, simplicial_union, set.mem_union],
    left,
    simp only [star_complement, set.mem_sep_iff],
    split; assumption,
    
    revert x_nin_X,
    contrapose,
    simp only [not_not],
    intros x_in_t,
    rw [vertex_iff_in_simplex],
    use t, split; assumption, },

  { intros t_in_union,
    cases t_in_union with t_in_subdiv t_join_s,
    
    choose t_in_subdiv x_nin_t using t_in_subdiv,
    simp only [stellar_subdivision, simplicial_union, set.mem_union] at t_in_subdiv,
    cases t_in_subdiv with t_in_star_comp t_in_join,
    
    simp only [star_complement, set.mem_sep_iff] at t_in_star_comp,
    choose t_in_X s_nss_t using t_in_star_comp,
    assumption,
    
    simp only [join_proj_mem] at t_in_join,
    choose t' t'_in_join t₁ t₁_in_link t_decomp using t_in_join,
    choose t₃ t₃_in_barycenter t₂ t₂_in_bd t'_decomp using t'_in_join,
    subst t'_decomp,
    
    have t₃_empty : t₃ = ∅, from
    begin
      simp only [simplex, finset.mem_coe, finset.mem_powerset, finset.subset_singleton_iff] at t₃_in_barycenter,
      cases t₃_in_barycenter with t₃_empty t₃_eq_x,
      assumption,

      have contra : x ∈ t, from
      begin
        simp only [t_decomp, finset.mem_union, t₃_eq_x],
        left, left,
        apply finset.mem_singleton_self,
      end,
      contradiction,
    end,
    subst t₃_empty,
    rw [finset.empty_union] at t_decomp,
    
    simp only [link, set.mem_sep_iff] at t₁_in_link,
    choose t₁_in_X st₁_in_X st₁_disj using t₁_in_link,
    rw [simplex_boundary_mem_iff_subset, finset.ssubset_iff_subset_ne] at t₂_in_bd,
    choose t₂_ss_s t₂_ne_s using t₂_in_bd,
    rw [t_decomp],
    
    apply X.subset_closed (s ∪ t₁),
    assumption,
    apply finset.union_subset_union_left,
    assumption,
    
    choose u u_in_star su_eq_t using t_join_s,
    simp only [barycenter_star, set.mem_sep_iff] at u_in_star,
    choose u_in_subdiv x_in_u using u_in_star,
    simp only [stellar_subdivision, simplicial_union, set.mem_union] at u_in_subdiv,
    cases u_in_subdiv with u_in_star_comp u_in_join,
    
    simp only [star_complement, set.mem_sep_iff] at u_in_star_comp,
    choose u_in_X s_nss_u using u_in_star_comp,
    have contra : x ∈ vertices X, from
    begin
      rw [vertex_iff_in_simplex],
      use u, split; assumption,
    end,
    contradiction,
    
    simp only [join_proj_mem] at u_in_join,
    choose u' u'_in_join u₁ u₁_in_link u_decomp using u_in_join,
    choose u₃ u₃_in_barycenter u₂ u₂_in_bd u'_decomp using u'_in_join,
    subst u'_decomp,

    simp only [link, set.mem_sep_iff] at u₁_in_link,
    choose u₁_in_X su₁_in_X su₁_disj using u₁_in_link,
    rw [simplex_boundary_mem_iff_subset, finset.ssubset_iff_subset_ne] at u₂_in_bd,
    choose u₂_ss_s u₂_ne_s using u₂_in_bd,

    have xu₁_rw : u₁ \ {x} = u₁, from
    begin
      rw [finset.sdiff_eq_self_iff_disjoint, finset.disjoint_singleton_right],
      by_contradiction,

      have contra : x ∈ vertices X, from
      begin
        rw [vertex_iff_in_simplex],
        use u₁, split; assumption,
      end,
      contradiction,
    end,

    have xu₂_rw : u₂ \ {x} = u₂, from
    begin
      rw [finset.sdiff_eq_self_iff_disjoint, finset.disjoint_singleton_right],
      by_contradiction,

      have contra : x ∈ vertices X, from
      begin
        rw [vertex_iff_in_simplex],
        use u₂, split,
        apply X.subset_closed s;
        assumption,
        assumption,
      end,
      contradiction,
    end,

    rw [←su_eq_t, u_decomp],
    simp only [finset.union_sdiff_distrib],
    rw [xu₁_rw, xu₂_rw],

    have su₂_rw : s ∪ u₂ = s, from
    begin
      rw [finset.union_eq_left_iff_subset],
      assumption,
    end,
    
    simp only [simplex, finset.mem_coe, finset.mem_powerset, finset.subset_singleton_iff] at u₃_in_barycenter,
    cases u₃_in_barycenter with u₃_empty u₃_eq_x,
    rw [u₃_empty, finset.empty_sdiff, finset.empty_union, ←finset.union_assoc, su₂_rw],
    assumption,
    
    rw [u₃_eq_x, finset.sdiff_self, finset.empty_union, ←finset.union_assoc, su₂_rw],
    assumption, },
end

instance stellar_subdivision.fintype_converse
    (X : simplicial_complex α)
    (s : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    [fintype (σ(X, s, x; s_ne, s_in_X, x_nin_X)).simplices]
  : fintype X.simplices
:= begin
  rw [stellar_weld_simplices X s x s_in_X x_nin_X],
  apply set.fintype_union,
end

lemma barycenter_vertex_stellar_subdiv
    (X : simplicial_complex α)
    (s : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : x ∈ vertices (σ(X, s, x; s_ne, s_in_X, x_nin_X))
:= begin
  rw [vertex_iff_singleton],
  simp only [stellar_subdivision, simplicial_union, set.mem_union, join_proj_mem],
  right,

  use {x}, split,
  use {x}, split,
  simp only [simplex, finset.mem_coe],
  apply finset.mem_powerset_self,

  use ∅, split,
  apply simplicial_complex_empty_simplex,
  rw [finset.union_empty],

  use ∅, split,
  apply simplicial_complex_empty_simplex,
  rw [finset.union_empty],
end

lemma stellar_subdiv_iso_simp
    (X : simplicial_complex α)
    (Y : simplicial_complex β)
    (s : finset α) [s_ne : nonempty s]
    (t : finset β) [t_ne : nonempty t]
    (x : α) (y : β)
    (s_in_X : s ∈ X.simplices)
    (t_in_Y : t ∈ Y.simplices)
    (x_nin_X : x ∉ vertices X)
    (y_nin_Y : y ∉ vertices Y)
    (f : simplicial_map X Y)
    (f_iso : is_simplicial_iso f)
  : finset.image f.map s = t → f.map x = y →
      is_simplicial_map σ(X, s, x; s_ne, s_in_X, x_nin_X) σ(Y, t, y; t_ne, t_in_Y, y_nin_Y) f.map
:= begin
  intros fs_t fx_y,
  let f_iso' := f_iso,
  unfold is_simplicial_iso at f_iso',
  choose g gf_inv using f_iso',

  have g_iso : is_simplicial_iso g, from
  begin
    apply iso_inv_is_iso f g f_iso gf_inv,
  end,

  unfold is_inverse_simplicial_iso at gf_inv,
  simp only [set.restrict_eq_restrict_iff, set.eq_on, simplicial_map.comp, function.comp_app, id.def] at gf_inv,
  choose gf_id fg_id using gf_inv,

  have f_inj : set.inj_on f.map s, from
  begin
    apply @set.left_inv_on.inj_on _ _ _ _ g.map,
    simp only [set.left_inv_on],
    intros x x_in_s,
    have x_in_vert : x ∈ vertices X, from
    begin
      rw [vertex_iff_in_simplex],
      use s, split, assumption,
      rw [←finset.mem_coe],
      assumption,
    end,
    specialize gf_id x_in_vert,
    assumption,
  end,

  simp only [is_simplicial_map],
  intros u u_in_subdiv_X,

  simp only [stellar_subdivision, simplicial_union, set.mem_union] at u_in_subdiv_X ⊢,
  cases u_in_subdiv_X with u_in_star_comp u_in_join,

  left,
  simp only [star_complement, set.mem_sep_iff] at u_in_star_comp ⊢,
  choose u_in_X s_nss_u using u_in_star_comp,
  split,

  apply f.is_simplicial,
  assumption,

  simp only [←fs_t, finset.image_subset_iff, not_forall, finset.mem_image, not_exists],
  simp only [finset.subset_iff, not_forall] at s_nss_u,
  choose z z_in_s z_nin_u using s_nss_u,
  use z, split,
  use z_in_s,

  intros w w_in_u,
  rw [@set.inj_on.eq_iff _ _ (vertices X)],
  revert w_in_u z_nin_u,
  contrapose,
  simp only [not_forall, not_not, exists_prop, and_imp],
  intros z_nin_u w_eq_z,
  rw [w_eq_z],
  assumption,

  apply iso_is_injective_vertices,
  assumption,

  rw [vertex_iff_in_simplex],
  use u, split; assumption,

  rw [vertex_iff_in_simplex],
  use s, split; assumption,

  right,
  simp only [join_proj_mem] at u_in_join ⊢,
  choose u' u'_in_join u₁ u₁_in_link u_decomp using u_in_join,
  choose u₃ u₃_in_barycenter u₂ u₂_in_bd u'_decomp using u'_in_join,
  subst u'_decomp,

  use (finset.image f.map (u₃ ∪ u₂)), split,
  use (finset.image f.map u₃), split,
  simp only [simplex, finset.mem_coe, finset.mem_powerset, finset.subset_singleton_iff] at u₃_in_barycenter ⊢,
  cases u₃_in_barycenter with u₃_empty u₃_x,
  left,
  rw [u₃_empty],
  apply finset.image_empty,
  right,
  rw [u₃_x, ←fx_y],
  apply finset.image_singleton,

  use (finset.image f.map u₂), split,
  simp only [simplex_boundary, set.mem_union, set.mem_diff, set.mem_singleton_iff, finset.mem_coe, finset.mem_powerset] at u₂_in_bd ⊢,
  cases u₂_in_bd with u₂_in_bd u₂_empty,

  left,
  choose u₂_ss_s u₂_ne_s using u₂_in_bd,
  simp only [←fs_t],
  split,

  apply finset.image_subset_image,
  assumption,

  revert u₂_ne_s,
  contrapose,
  simp only [not_not, finset.ext_iff, finset.mem_image],
  intros fu_eq_fs a,
  specialize fu_eq_fs (f.map a),
  cases fu_eq_fs with fu_ss_fs fs_ss_fu,
  split,

  intro a_in_u,
  rw [finset.subset_iff] at u₂_ss_s,
  specialize u₂_ss_s a_in_u,
  assumption,

  intro a_in_s,
  apply set.inj_on.mem_of_mem_image f_inj u₂_ss_s,
  rw [finset.mem_coe],
  assumption,
  have Hs : ∃ (x : α) (H : x ∈ s), f.map x = f.map a, from
  begin
    use a, split, assumption,
    refl,
  end,
  specialize fs_ss_fu Hs,
  simp only [finset.mem_val, set.mem_image, ←exists_prop],
  assumption,

  simp only [u₂_empty, finset.image_empty],
  right, refl,

  apply finset.image_union,

  use (finset.image f.map u₁), split,
  simp only [link, set.mem_sep_iff] at u₁_in_link ⊢,
  choose u₁_in_X su₁_in_X su₁_disj using u₁_in_link,
  split,

  apply f.is_simplicial,
  assumption,

  split,
  rw [←fs_t, ←finset.image_union],
  apply f.is_simplicial,
  assumption,

  rw [←fs_t, ←finset.image_inter_of_inj_on, su₁_disj, finset.image_eq_empty],
  rw [←finset.coe_union],
  apply iso_is_injective_simplices f f_iso (s ∪ u₁),
  assumption,

  rw [u_decomp, finset.image_union],
end

lemma stellar_subdiv_iso
    (X : simplicial_complex α)
    (Y : simplicial_complex β)
    (s : finset α) [s_ne : nonempty s]
    (t : finset β) [t_ne : nonempty t]
    (x : α) (y : β)
    (s_in_X : s ∈ X.simplices)
    (t_in_Y : t ∈ Y.simplices)
    (x_nin_X : x ∉ vertices X)
    (y_nin_Y : y ∉ vertices Y)
    (f : simplicial_map X Y)
    (f_iso : is_simplicial_iso f)
    (g : simplicial_map Y X)
    (gf_inv : is_inverse_simplicial_iso f g)
  : finset.image f.map s = t → f.map x = y → g.map y = x →
      σ(X, s, x; s_ne, s_in_X, x_nin_X) ≅ σ(Y, t, y; t_ne, t_in_Y, y_nin_Y)
:= begin
  intros fs_t fx_y gy_x,
  have g_iso : is_simplicial_iso g, from
  begin
    apply iso_inv_is_iso f g f_iso gf_inv,
  end,

  unfold is_inverse_simplicial_iso at gf_inv,
  simp only [set.restrict_eq_restrict_iff, set.eq_on, simplicial_map.comp, function.comp_app, id.def] at gf_inv,
  choose gf_id fg_id using gf_inv,

  have gt_s : finset.image g.map t = s, from
  begin
    simp only [←fs_t, finset.ext_iff, finset.mem_image],
    intro a,
    split,

    intro a_in_img,
    choose b b_in_t gb_a using a_in_img,
    choose c c_in_s fc_b using b_in_t,
    subst fc_b,
    have c_in_X : c ∈ vertices X, from
    begin
      rw [vertex_iff_in_simplex],
      use s, split; assumption,
    end,
    specialize gf_id c_in_X,
    rw [gf_id] at gb_a,
    rw [gb_a] at c_in_s,
    assumption,

    intro a_in_s,
    use (f.map a), split,
    use a, split,
    assumption,
    refl,
    have a_in_X : a ∈ vertices X, from
    begin
      rw [vertex_iff_in_simplex],
      use s, split; assumption,
    end,
    specialize gf_id a_in_X,
    assumption,
  end,

  let f_subdiv := simplicial_map.mk f.map (stellar_subdiv_iso_simp X Y s t x y s_in_X t_in_Y x_nin_X y_nin_Y f f_iso fs_t fx_y),
  let g_subdiv := simplicial_map.mk g.map (stellar_subdiv_iso_simp Y X t s y x t_in_Y s_in_X y_nin_Y x_nin_X g g_iso gt_s gy_x),

  unfold is_simplicially_iso,
  use f_subdiv,

  unfold is_simplicial_iso,
  use g_subdiv,

  unfold is_inverse_simplicial_iso,
  simp only [set.restrict_eq_restrict_iff, set.eq_on, simplicial_map.comp, function.comp_app, id.def],
  split,

  { intros a a_in_X,
    have a_in_union : a ∈ vertices X ∪ {x}, from
    begin
      apply stellar_subdiv_subset_vertices X s,
      apply a_in_X,
    end,
    rw [set.mem_union, set.mem_singleton_iff] at a_in_union,
    cases a_in_union with a_in_X a_eq_x,
    
    specialize gf_id a_in_X,
    assumption,
    
    subst a_eq_x,
    rw [fx_y, gy_x], },

  { intros a a_in_Y,
    have a_in_union : a ∈ vertices Y ∪ {y}, from
    begin
      apply stellar_subdiv_subset_vertices Y t,
      apply a_in_Y,
    end,
    rw [set.mem_union, set.mem_singleton_iff] at a_in_union,
    cases a_in_union with a_in_Y a_eq_y,
    
    specialize fg_id a_in_Y,
    assumption,
    
    subst a_eq_y,
    rw [gy_x, fx_y], },
end

def stellar_subdiv_of_singleton_map
    (x y : α)
  : α → α
:= λ (a : α), if (a = x) then y else a

lemma stellar_subdiv_of_singleton_forward_simp
    (X : simplicial_complex α)
    (x y : α)
    (y_in_X : {y} ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : is_simplicial_map σ(X, {y}, x; (by { apply finset.nonempty.coe_sort, apply finset.singleton_nonempty, }), y_in_X, x_nin_X) X (stellar_subdiv_of_singleton_map x y)
:= begin
  simp only [is_simplicial_map, stellar_subdivision, simplicial_union, set.mem_union],
  intros s s_in_subdiv,
  cases s_in_subdiv with s_in_star_comp s_in_join,

  -- star complement case.
  have id_s : finset.image (stellar_subdiv_of_singleton_map x y) s = s, from
  begin
    simp only [stellar_subdiv_of_singleton_map, finset.ext_iff],
    intros a,
    split,

    intros a_in_img,
    rw [finset.mem_image] at a_in_img,
    choose b b_in_s fb_a using a_in_img,
    have b_ne_x : b ≠ x, from
    begin
      by_cases b_eq_x : b = x,

      rw [b_eq_x] at b_in_s,
      have contra : x ∈ vertices X, from
      begin
        rw [vertex_iff_in_simplex],
        use s, split,
        apply simplex_if_in_subcomplex,
        apply s_in_star_comp,
        apply star_complement_subcomplex,
        assumption,
      end,
      contradiction,

      assumption,
    end,
    simp only [b_ne_x, if_false] at fb_a,
    rw [fb_a] at b_in_s,
    assumption,

    intros a_in_s,
    rw [finset.mem_image],
    use a, split, assumption,

    have a_ne_x : a ≠ x, from
    begin
      by_cases a_eq_x : a = x,

      rw [a_eq_x] at a_in_s,
      have contra : x ∈ vertices X, from
      begin
        rw [vertex_iff_in_simplex],
        use s, split,
        apply simplex_if_in_subcomplex,
        apply s_in_star_comp,
        apply star_complement_subcomplex,
        assumption,
      end,
      contradiction,

      assumption,
    end,
    simp only [a_ne_x, if_false],
  end,

  rw [id_s],
  apply simplex_if_in_subcomplex,
  apply s_in_star_comp,
  apply star_complement_subcomplex,

  -- join case.
  simp only [join_proj_mem] at s_in_join,
  choose s' s'_in_join s₁ s₁_in_link s_decomp using s_in_join,
  choose s₃ s₃_in_barycenter s₂ s₂_in_bd s'_decomp using s'_in_join,
  subst s'_decomp,

  simp only [simplex_boundary, set.mem_union, set.mem_diff, set.mem_singleton_iff, finset.mem_coe, finset.mem_powerset] at s₂_in_bd,
  have s₂_empty : s₂ = ∅, from
  begin
    cases s₂_in_bd with s₂_in_bd s₂_empty,

    choose s₂_ss_y s₂_ne_y using s₂_in_bd,
    rw [finset.subset_singleton_iff] at s₂_ss_y,
    cases s₂_ss_y with s₂_empty contra,
    assumption,
    contradiction,

    assumption,
  end,
  subst s₂_empty,
  rw [finset.union_empty] at s_decomp,
  
  simp only [link, set.mem_sep_iff] at s₁_in_link,
  choose s₁_in_X ys₁_in_X ys₁_disj using s₁_in_link,

  simp only [simplex, finset.mem_coe, finset.mem_powerset, finset.subset_singleton_iff] at s₃_in_barycenter,
  cases s₃_in_barycenter with s₃_empty s₃_eq_x,

  { subst s₃_empty,
    rw [finset.empty_union] at s_decomp,
    subst s_decomp,
    
    have id_s : finset.image (stellar_subdiv_of_singleton_map x y) s = s, from
    begin
      simp only [stellar_subdiv_of_singleton_map, finset.ext_iff],
      intros a,
      split,

      intros a_in_img,
      rw [finset.mem_image] at a_in_img,
      choose b b_in_s fb_a using a_in_img,
      have b_ne_x : b ≠ x, from
      begin
        by_cases b_eq_x : b = x,

        rw [b_eq_x] at b_in_s,
        have contra : x ∈ vertices X, from
        begin
          rw [vertex_iff_in_simplex],
          use s, split; assumption,
        end,
        contradiction,

        assumption,
      end,
      simp only [b_ne_x, if_false] at fb_a,
      rw [fb_a] at b_in_s,
      assumption,

      intros a_in_s,
      rw [finset.mem_image],
      use a, split, assumption,

      have a_ne_x : a ≠ x, from
      begin
        by_cases a_eq_x : a = x,

        rw [a_eq_x] at a_in_s,
        have contra : x ∈ vertices X, from
        begin
          rw [vertex_iff_in_simplex],
          use s, split; assumption,
        end,
        contradiction,

        assumption,
      end,
      simp only [a_ne_x, if_false],
    end,
    rw [id_s],
    assumption, },

  { subst s₃_eq_x,
    subst s_decomp,
    have id_s : finset.image (stellar_subdiv_of_singleton_map x y) ({x} ∪ s₁) = {y} ∪ s₁, from
    begin
      simp only [stellar_subdiv_of_singleton_map, finset.ext_iff, finset.mem_image, finset.mem_union, finset.mem_singleton],
      intros a,
      split,

      intros a_in_img,
      choose b b_in_union fb_a using a_in_img,
      cases b_in_union with b_eq_x b_in_s₁,

      left,
      simp only [b_eq_x, eq_self_iff_true, if_true] at fb_a,
      symmetry,
      assumption,

      right,
      have b_ne_x : b ≠ x, from
      begin
        by_cases b_eq_x : b = x,

        rw [b_eq_x] at b_in_s₁,
        have contra : x ∈ vertices X, from
        begin
          rw [vertex_iff_in_simplex],
          use s₁, split; assumption,
        end,
        contradiction,

        assumption,
      end,
      simp only [b_ne_x, if_false] at fb_a,
      rw [fb_a] at b_in_s₁,
      assumption,

      intros a_in_union,
      cases a_in_union with a_eq_y a_in_s₁,

      subst a_eq_y,
      use x, split,
      left, refl,
      simp only [eq_self_iff_true, if_true],

      have a_ne_x : a ≠ x, from
      begin
        by_cases a_eq_x : a = x,

        rw [a_eq_x] at a_in_s₁,
        have contra : x ∈ vertices X, from
        begin
          rw [vertex_iff_in_simplex],
          use s₁, split; assumption,
        end,
        contradiction,

        assumption,
      end,
      use a, split,
      right, assumption,
      simp only [a_ne_x, if_false],
    end,
    
    rw [id_s],
    assumption, },
end

lemma stellar_subdiv_of_singleton_inverse_simp
    (X : simplicial_complex α)
    (x y : α)
    (y_in_X : {y} ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : is_simplicial_map X σ(X, {y}, x; (by { apply finset.nonempty.coe_sort, apply finset.singleton_nonempty, }), y_in_X, x_nin_X) (stellar_subdiv_of_singleton_map y x)
:= begin
  simp only [is_simplicial_map, stellar_subdivision, simplicial_union, set.mem_union],
  intros s s_in_X,
  by_cases y_in_s : y ∈ s,

  -- y ∈ s case.
  right,
  simp only [join_proj_mem],
  use {x}, split,
  use {x}, split,
  simp only [simplex, finset.mem_coe],
  apply finset.mem_powerset_self,

  use ∅, split,
  apply simplicial_complex_empty_simplex,
  rw [finset.union_empty],

  use (s \ {y}), split,
  simp only [link, set.mem_sep_iff],
  split,

  apply X.subset_closed s,
  assumption,
  apply finset.sdiff_subset,

  split,
  rw [finset.union_sdiff_of_subset],
  assumption,
  rw [finset.singleton_subset_iff],
  assumption,

  rw [finset.inter_comm],
  apply finset.sdiff_inter_self,

  have s_decomp : s = {y} ∪ s \ {y}, from
  begin
    rw [finset.union_sdiff_of_subset],
    rw [finset.singleton_subset_iff],
    assumption,
  end,
  rw [s_decomp, stellar_subdiv_of_singleton_map, finset.ext_iff],

  intros a,
  simp only [finset.mem_image, finset.mem_union, finset.mem_sdiff, finset.mem_singleton],
  split,

  { intros a_in_img,
    choose b b_in_union fb_a using a_in_img,
    cases b_in_union with b_eq_y b_ne_y,
    
    left,
    simp only [b_eq_y, eq_self_iff_true, if_true] at fb_a,
    symmetry,
    assumption,
    
    right,
    choose b_in_s b_ne_y using b_ne_y,
    simp only [b_ne_y, if_false] at fb_a,
    rw [fb_a] at b_ne_y b_in_s,
    split,
    right, split; assumption,
    assumption, },

  { intros a_in_union,
    cases a_in_union with a_eq_x a_in_s,
    
    use y, split,
    left, refl,
    simp only [eq_self_iff_true, if_true],
    symmetry,
    assumption,
    
    choose a_in_s a_ne_y using a_in_s,
    cases a_in_s with contra a_in_s,
    contradiction,
    choose a_in_s a_ne_y using a_in_s,
    
    use a, split,
    right, split; assumption,
    simp only [a_ne_y, if_false], },

  -- y ∉ s case.
  left,
  have id_s : finset.image (stellar_subdiv_of_singleton_map y x) s = s, from
  begin
    simp only [stellar_subdiv_of_singleton_map, finset.ext_iff],
    intros a,
    split,

    intros a_in_img,
    rw [finset.mem_image] at a_in_img,
    choose b b_in_s fb_a using a_in_img,
    have b_ne_y : b ≠ y, from
    begin
      by_cases b_eq_y : b = y,
      rw [b_eq_y] at b_in_s,
      contradiction,
      assumption,
    end,
    simp only [b_ne_y, if_false] at fb_a,
    rw [fb_a] at b_in_s,
    assumption,

    intros a_in_s,
    rw [finset.mem_image],
    use a, split, assumption,

    have a_ne_y : a ≠ y, from
    begin
      by_cases a_eq_y : a = y,
      rw [a_eq_y] at a_in_s,
      contradiction,
      assumption,
    end,
    simp only [a_ne_y, if_false],
  end,

  simp only [id_s, star_complement, set.mem_sep_iff],
  split,
  assumption,

  rw [finset.singleton_subset_iff],
  assumption,
end

lemma stellar_subdiv_of_singleton
    (X : simplicial_complex α)
    (x y : α)
    (y_in_X : {y} ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : σ(X, {y}, x; (by { apply finset.nonempty.coe_sort, apply finset.singleton_nonempty, }), y_in_X, x_nin_X) ≅ X
:= begin
  let f_subdiv : simplicial_map σ(X, {y}, x; (by { apply finset.nonempty.coe_sort, apply finset.singleton_nonempty, }), y_in_X, x_nin_X) X :=
    simplicial_map.mk
      (stellar_subdiv_of_singleton_map x y)
      (stellar_subdiv_of_singleton_forward_simp X x y y_in_X x_nin_X),

  let g_subdiv : simplicial_map X σ(X, {y}, x; (by { apply finset.nonempty.coe_sort, apply finset.singleton_nonempty, }), y_in_X, x_nin_X) :=
    simplicial_map.mk
      (stellar_subdiv_of_singleton_map y x)
      (stellar_subdiv_of_singleton_inverse_simp X x y y_in_X x_nin_X),

  unfold is_simplicially_iso,
  use f_subdiv, use g_subdiv,
  unfold is_inverse_simplicial_iso,
  simp only [set.restrict_eq_restrict_iff, set.eq_on, simplicial_map.comp, function.comp_app, id.def],
  split,

  { intros a a_in_subdiv,
    simp only [stellar_subdiv_of_singleton_map],
    split_ifs,
    
    symmetry,
    assumption,
    
    rw [stellar_subdiv_of_singleton_vertices, set.mem_union, set.mem_diff_singleton, set.mem_singleton_iff] at a_in_subdiv,
    cases a_in_subdiv with a_in_X contra,
    choose a_in_X contra using a_in_X,
    contradiction,
    contradiction,
    
    refl, },

  { intros a a_in_X,
    simp only [stellar_subdiv_of_singleton_map],
    split_ifs,
    
    symmetry,
    assumption,
    
    rw [h_1] at a_in_X,
    contradiction,
    
    refl, },
end

@[simp]
def stellar_move
  : simplicial_complex α → simplicial_complex α → Prop
:= λ X Y : simplicial_complex α,
      (∃ (t : finset α) (Ht : t ∈ Y.simplices) [Ht_ne : nonempty t]
        (y : α) (Hy : y ∉ vertices Y),
        X ≅ @stellar_subdivision _ _ Y t Ht_ne y Ht Hy)
      ∨
      (∃ (s : finset α) (Hs : s ∈ X.simplices) [Hs_ne : nonempty s]
        (x : α) (Hx : x ∉ vertices X),
        Y ≅ @stellar_subdivision _ _ X s Hs_ne x Hs Hx)
      ∨ (X ≅ Y)

noncomputable
instance stellar_move.weld.fintype
    (X Y : simplicial_complex α) [fintype X.simplices]
    (X_weld_Y : ∃ (t : finset α) (Ht : t ∈ Y.simplices) [Ht_ne : nonempty t]
      (y : α) (Hy : y ∉ vertices Y),
      X ≅ @stellar_subdivision _ _ Y t Ht_ne y Ht Hy)
  : fintype Y.simplices
:= begin
  choose t t_in_Y t_ne y y_nin_Y X_weld_Y using X_weld_Y,
  apply @stellar_subdivision.fintype_converse _ _ Y t t_ne y t_in_Y y_nin_Y
    (is_simplicially_iso.fintype X σ(Y, t, y; t_ne, t_in_Y, y_nin_Y) X_weld_Y),
end

noncomputable
instance stellar_move.subdiv.fintype
    (X Y : simplicial_complex α) [X_fin : fintype X.simplices]
    (X_subdiv_Y : ∃ (s : finset α) (Hs : s ∈ X.simplices) [Hs_ne : nonempty s]
      (x : α) (Hx : x ∉ vertices X),
      Y ≅ @stellar_subdivision _ _ X s Hs_ne x Hs Hx)
  : fintype Y.simplices
:= begin
  choose s s_in_X s_ne x x_nin_X X_subdiv_Y using X_subdiv_Y,
  rw [simplicial_iso_symm] at X_subdiv_Y,
  apply @is_simplicially_iso.fintype _ _ _ _ σ(X, s, x; s_ne, s_in_X, x_nin_X)
    (@stellar_subdivision.fintype _ _ X X_fin s s_ne x s_in_X x_nin_X)
    Y X_subdiv_Y,
end

noncomputable
instance stellar_move.fintype
    (X Y : simplicial_complex α) [fintype X.simplices]
    (X_move_Y : stellar_move X Y)
  : fintype Y.simplices
:= begin
  simp only [stellar_move] at X_move_Y,

  by_cases X_weld_Y :
    ∃ (t : finset α) (Ht : t ∈ Y.simplices) [Ht_ne : nonempty t]
      (y : α) (Hy : y ∉ vertices Y),
      X ≅ @stellar_subdivision _ _ Y t Ht_ne y Ht Hy,
  apply stellar_move.weld.fintype X Y X_weld_Y,

  by_cases X_subdiv_Y :
    ∃ (s : finset α) (Hs : s ∈ X.simplices) [Hs_ne : nonempty s]
      (x : α) (Hx : x ∉ vertices X),
      Y ≅ @stellar_subdivision _ _ X s Hs_ne x Hs Hx,
  apply stellar_move.subdiv.fintype X Y X_subdiv_Y,

  by_cases X_iso_Y : X ≅ Y,
  apply is_simplicially_iso.fintype X Y X_iso_Y,

  have contra : ¬stellar_move X Y, from
  begin
    simp only [stellar_move, not_or_distrib],
    split, assumption,
    split, assumption,
    assumption,
  end,
  contradiction,
end

lemma stellar_move_preserves_dim
    (X Y : simplicial_complex α) [X_fin : fintype X.simplices] [Y_fin : fintype Y.simplices]
    (X_move_Y : stellar_move X Y)
  : dim_of_complex X = dim_of_complex Y
:= begin
  simp only [stellar_move] at X_move_Y,
  cases X_move_Y with Y_subdiv_X X_move_Y,

  choose t t_in_Y t_ne y y_nin_Y Y_subdiv_X using Y_subdiv_X,
  rw [@simplicial_iso_preserves_dim α α _ _ X _ σ(Y, t, y; t_ne, t_in_Y, y_nin_Y) Y_subdiv_X],
  symmetry,
  rw [@stellar_subdiv_preserves_dim α _ Y Y_fin t t_ne y t_in_Y y_nin_Y],

  rotate,
  cases X_move_Y with X_subdiv_Y X_iso_Y,
  choose s s_in_X s_ne x x_nin_X X_subdiv_Y using X_subdiv_Y,
  rw [@simplicial_iso_preserves_dim α α _ _ Y Y_fin σ(X, s, x; s_ne, s_in_X, x_nin_X) X_subdiv_Y],
  rw [@stellar_subdiv_preserves_dim _ _ X X_fin s s_ne x s_in_X x_nin_X],

  rotate,
  rw [@simplicial_iso_preserves_dim α α _ _ X _ Y X_iso_Y],

  all_goals {
    unfold dim_of_complex,
    apply le_antisymm;

    { apply finset.max'_le,
      intros z z_in_img,
      simp only [finset.mem_image, set.mem_to_finset] at z_in_img,
      choose u u_in_K dim_u_z using z_in_img,
      apply finset.le_max',
      simp only [finset.mem_image, set.mem_to_finset],
      use u, split; assumption, },
  },
end

def stellar_equiv
    (X : simplicial_complex α)
  : simplicial_complex α → Prop
:= relation.refl_trans_gen stellar_move X
infixl ` ≅ₛₜ `:50 := stellar_equiv

noncomputable
instance stellar_equiv.fintype
    (X Y : simplicial_complex α) [X_fin : fintype X.simplices]
    (X_eq_Y : X ≅ₛₜ Y)
  : fintype Y.simplices
:= begin
  apply set.finite.fintype,
  induction X_eq_Y with K L X_eq_K K_move_L L_dec,
  apply set.finite.intro,
  assumption,

  apply set.finite.intro,
  have K_fin : fintype K.simplices, from
  begin
    apply set.finite.fintype,
    assumption,
  end,
  apply @stellar_move.fintype _ _ K L K_fin K_move_L,
end

lemma stellar_equiv_preserves_dim
    (X Y : simplicial_complex α) [X_fin : fintype X.simplices]
    (X_eq_Y : X ≅ₛₜ Y)
  : dim_of_complex X = @dim_of_complex _ Y (@stellar_equiv.fintype α _ X Y X_fin X_eq_Y)
:= begin
  induction X_eq_Y with K L X_eq_K K_move_L H_ind,
  
  { unfold dim_of_complex,
    apply le_antisymm;

    { rw [finset.max'_le_iff],
      intros y y_max,
      apply finset.le_max',
      simp only [finset.mem_image, set.mem_to_finset] at y_max ⊢,
      choose s s_in_img dim_s_y using y_max,
      use s, split; assumption, }, },

  { transitivity (@dim_of_complex _ K (@stellar_equiv.fintype α _ X K X_fin X_eq_K)),
    assumption,
    apply @stellar_move_preserves_dim _ _ K L (@stellar_equiv.fintype α _ X K X_fin X_eq_K),
    assumption, },
end

@[refl]
lemma stellar_equiv_refl
    (X : simplicial_complex α)
  : X ≅ₛₜ X
:= begin
  unfold stellar_equiv,
end

@[symm]
lemma stellar_equiv_symm
    (X Y : simplicial_complex α)
  : X ≅ₛₜ Y ↔ Y ≅ₛₜ X
:= begin
  unfold stellar_equiv,
  split;
  { apply relation.refl_trans_gen.symmetric,
    rw [←swap_eq_iff],
    simp only[stellar_move, function.swap],
    apply funext, intro K,
    apply funext, intro L,
    apply propext,
    split,
    
    intro L_move_K,
    cases L_move_K,
    
    right, left,
    choose s Hs Hs_ne x Hx L_subdiv_K using L_move_K,
    use s, use Hs, use Hs_ne, use x, use Hx,
    assumption,
    
    cases L_move_K,
    left,
    choose t Ht Ht_ne y Hy K_subdiv_L using L_move_K,
    use t, use Ht, use Ht_ne, use y, use Hy,
    assumption,
    
    right, right,
    rw [simplicial_iso_symm],
    assumption,
    
    intro K_move_L,
    cases K_move_L,
    
    right, left,
    choose s Hs Hs_ne x Hx K_subdiv_L using K_move_L,
    use s, use Hs, use Hs_ne, use x, use Hx,
    assumption,
    
    cases K_move_L,
    left,
    choose t Ht Ht_ne y Hy L_subdiv_K using K_move_L,
    use t, use Ht, use Ht_ne, use y, use Hy,
    assumption,
    
    right, right,
    rw [simplicial_iso_symm],
    assumption, }
end

@[trans]
lemma stellar_equiv_trans
    (X Y Z : simplicial_complex α)
  : X ≅ₛₜ Y → Y ≅ₛₜ Z → X ≅ₛₜ Z
:= begin
  unfold stellar_equiv,
  apply relation.transitive_refl_trans_gen,
end

lemma stellar_equiv_neg_trans
    (X Y Z : simplicial_complex α)
  : X ≅ₛₜ Y → ¬Y ≅ₛₜ Z → ¬X ≅ₛₜ Z
:= begin
  intros X_eq_Y Y_neq_Z,
  revert Y_neq_Z,
  contrapose,
  simp only [not_not],
  intro X_eq_Z,
  rw [stellar_equiv_symm] at X_eq_Y,
  revert X_eq_Y X_eq_Z,
  apply stellar_equiv_trans,
end

lemma stellar_equiv_preserves_iso
    (X Y : simplicial_complex α)
  : X ≅ Y → X ≅ₛₜ Y
:= begin
  intro X_iso_Y,
  simp only[stellar_equiv],
  apply relation.refl_trans_gen.single,
  simp only[stellar_move],
  right, right,
  assumption,
end

@[simp]
def stellar_coe_map
    (f : α → β)
    (x : α) (y : β)
  : α → β
:= λ (a : α), if (a = x) then y else f a

lemma stellar_coe_simplex_image
    (s : finset α) (x : α) (y : β)
    (f : α → β)
  : x ∉ s → finset.image (stellar_coe_map f x y) s = finset.image f s
:= begin
  rw [finset.ext_iff],
  intros x_nin_s b,
  simp only [finset.mem_image, stellar_coe_map],
  split,

  { intros b_in_coe,
    choose a a_in_s coe_a_b using b_in_coe,
    revert coe_a_b,
    split_ifs,
    
    rw [h] at a_in_s,
    contradiction,
    
    intros fa_b,
    use a, split;
    assumption, },

  { intros b_in_img,
    choose a a_in_s fa_b using b_in_img,
    use a, split, assumption,
    split_ifs,
    
    rw [h] at a_in_s,
    contradiction,
    
    assumption, },
end

lemma stellar_coe_forward_simplicial
    [nonempty α]
    (X : simplicial_complex α)
    (φ : simplicial_coe X β)
    (s : finset α) [s_ne : nonempty s]
    (x : α) (y : β)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (y_nin_coe : y ∉ vertices (φ[X]))
  : is_simplicial_map
      σ(X, s, x; s_ne, s_in_X, x_nin_X)
      σ(φ[X], finset.image φ.coe s, y; _, by { apply map_is_simplicial_onto_image, assumption, }, y_nin_coe)
      (stellar_coe_map φ.coe x y)
:= begin
  simp only [is_simplicial_map, stellar_subdivision, simplicial_union, set.mem_union],
  intros t t_in_subdiv,
  cases t_in_subdiv with t_in_star_comp t_in_join,

  left,
  rw [star_complement_coe_image X s s_in_X φ, stellar_coe_simplex_image],
  apply map_is_simplicial_onto_image,
  assumption,
  
  revert x_nin_X,
  contrapose,
  simp only [not_not],
  revert x,
  simp only [←finset.mem_coe, ←set.subset_def],
  apply simplex_subset_vertices,
  apply simplex_if_in_subcomplex,
  apply t_in_star_comp,
  apply star_complement_subcomplex,

  right,
  simp only [join_proj_mem] at t_in_join ⊢,
  choose t' t'_in_join t₁ t₁_in_link t_decomp using t_in_join,
  choose t₃ t₃_in_barycenter t₂ t₂_in_bd t'_decomp using t'_in_join,
  subst t'_decomp,

  use (finset.image (stellar_coe_map φ.coe x y) (t₃ ∪ t₂)), split,
  use (finset.image (stellar_coe_map φ.coe x y) t₃), split,
  simp only [simplex, finset.mem_coe, finset.mem_powerset, finset.subset_singleton_iff] at t₃_in_barycenter ⊢,
  cases t₃_in_barycenter with t₃_empty t₃_x,

  left,
  rw [t₃_empty],
  apply finset.image_empty,

  right,
  rw [t₃_x, finset.image_singleton],
  simp only [stellar_coe_map, eq_self_iff_true, if_true],

  use (finset.image (stellar_coe_map φ.coe x y) t₂), split,
  rw [simplex_boundary_coe_image, stellar_coe_simplex_image],
  apply map_is_simplicial_onto_image,
  assumption,

  revert x_nin_X,
  contrapose,
  simp only [not_not, ←finset.mem_coe],
  have t₂_in_X : ↑t₂ ⊆ vertices X, from
  begin
    apply simplex_subset_vertices,
    apply simplex_if_in_subcomplex,
    apply t₂_in_bd,
    apply simplex_boundary_subcomplex,
    assumption,
  end,
  rw [set.subset_def] at t₂_in_X,
  specialize t₂_in_X x,
  assumption,

  assumption,
  rw [finset.image_union],

  use (finset.image (stellar_coe_map φ.coe x y) t₁), split,
  rw [link_coe_image, stellar_coe_simplex_image],
  apply map_is_simplicial_onto_image,
  assumption,

  revert x_nin_X,
  contrapose,
  simp only [not_not, ←finset.mem_coe],
  have t₁_in_X : ↑t₁ ⊆ vertices X, from
  begin
    apply simplex_subset_vertices,
    apply simplex_if_in_subcomplex,
    apply t₁_in_link,
    apply link_subcomplex,
  end,
  rw [set.subset_def] at t₁_in_X,
  specialize t₁_in_X x,
  assumption,

  rw [t_decomp, ←finset.image_union],
end

lemma stellar_coe_inverse_simplicial
    [nonempty α]
    (X : simplicial_complex α)
    (φ : simplicial_coe X β)
    (s : finset α) [s_ne : nonempty s]
    (x : α) (y : β)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (y_nin_coe : y ∉ vertices (φ[X]))
  : is_simplicial_map
      σ(φ[X], finset.image φ.coe s, y; _, by { apply map_is_simplicial_onto_image, assumption, }, y_nin_coe)
      σ(X, s, x; s_ne, s_in_X, x_nin_X)
      (stellar_coe_map (φ⁻ᶜ.map) y x)
:= begin
  simp only [is_simplicial_map, stellar_subdivision, simplicial_union, set.mem_union],
  intros t t_in_subdiv,
  cases t_in_subdiv with t_in_star_comp t_in_join,

  left,
  rw [stellar_coe_simplex_image],
  rw [star_complement_coe_image, simplicial_image_is_lift_image (X\St(X, s) s_in_X), set.mem_image] at t_in_star_comp,
  choose u u_in_star_comp φu_t using t_in_star_comp,
  simp only [simplicial_map_lift] at φu_t,
  rw [←φu_t],
  have inv_u : finset.image (φ⁻ᶜ.map) (finset.image φ.coe u) = u, from
  begin
    simp only [←finset.coe_inj, finset.coe_image],
    apply set.inj_on.inv_fun_on_image,
    apply φ.injective,
    apply simplex_subset_vertices,
    apply simplex_if_in_subcomplex,
    apply u_in_star_comp,
    apply star_complement_subcomplex,
  end,
  rw [inv_u],
  assumption,

  revert y_nin_coe,
  contrapose,
  simp only [not_not],
  revert y,
  simp only [←finset.mem_coe, ←set.subset_def],
  apply simplex_subset_vertices,
  apply simplex_if_in_subcomplex,
  apply t_in_star_comp,
  apply star_complement_subcomplex,

  right,
  simp only [join_proj_mem] at t_in_join ⊢,
  choose t' t'_in_join t₁ t₁_in_link t_decomp using t_in_join,
  choose t₃ t₃_in_barycenter t₂ t₂_in_bd t'_decomp using t'_in_join,
  subst t'_decomp,

  use (finset.image (stellar_coe_map (φ⁻ᶜ.map) y x) (t₃ ∪ t₂)), split,
  use (finset.image (stellar_coe_map (φ⁻ᶜ.map) y x) t₃), split,
  simp only [simplex, finset.mem_coe, finset.mem_powerset, finset.subset_singleton_iff] at t₃_in_barycenter ⊢,
  cases t₃_in_barycenter with t₃_empty t₃_x,

  left,
  rw [t₃_empty],
  apply finset.image_empty,

  right,
  rw [t₃_x, finset.image_singleton],
  simp only [stellar_coe_map, eq_self_iff_true, if_true],

  use (finset.image (stellar_coe_map (φ⁻ᶜ.map) y x) t₂), split,
  rw [stellar_coe_simplex_image],
  rw [simplex_boundary_coe_image, simplicial_image_is_lift_image, set.mem_image] at t₂_in_bd,
  choose u u_in_bd φu_t₂ using t₂_in_bd,
  simp only [simplicial_map_lift] at φu_t₂,
  rw [←φu_t₂],
  have inv_u : finset.image (φ⁻ᶜ.map) (finset.image φ.coe u) = u, from
  begin
    simp only [←finset.coe_inj, finset.coe_image],
    apply set.inj_on.inv_fun_on_image,
    apply φ.injective,
    apply simplex_subset_vertices,
    apply simplex_if_in_subcomplex,
    apply u_in_bd,
    apply simplex_boundary_subcomplex,
    assumption,
  end,
  rw [inv_u],
  assumption,
  assumption,

  revert y_nin_coe,
  contrapose,
  simp only [not_not, ←finset.mem_coe],
  have t₂_in_X : ↑t₂ ⊆ vertices (φ[X]), from
  begin
    apply simplex_subset_vertices,
    apply simplex_if_in_subcomplex,
    apply t₂_in_bd,
    apply simplex_boundary_subcomplex,
    apply map_is_simplicial_onto_image,
    assumption,
  end,
  rw [set.subset_def] at t₂_in_X,
  specialize t₂_in_X y,
  assumption,

  rw [finset.image_union],

  use (finset.image (stellar_coe_map (φ⁻ᶜ.map) y x) t₁), split,
  rw [stellar_coe_simplex_image],
  rw [link_coe_image, simplicial_image_is_lift_image (Lk(X, s) s_in_X), set.mem_image] at t₁_in_link,
  choose u u_in_link φu_t₁ using t₁_in_link,
  simp only [simplicial_map_lift] at φu_t₁,
  rw [←φu_t₁],
  have inv_u : finset.image (φ⁻ᶜ.map) (finset.image φ.coe u) = u, from
  begin
    simp only [←finset.coe_inj, finset.coe_image],
    apply set.inj_on.inv_fun_on_image,
    apply φ.injective,
    apply simplex_subset_vertices,
    apply simplex_if_in_subcomplex,
    apply u_in_link,
    apply link_subcomplex,
  end,
  rw [inv_u],
  assumption,

  revert y_nin_coe,
  contrapose,
  simp only [not_not, ←finset.mem_coe],
  have t₁_in_X : ↑t₁ ⊆ vertices (φ[X]), from
  begin
    apply simplex_subset_vertices,
    apply simplex_if_in_subcomplex,
    apply t₁_in_link,
    apply link_subcomplex,
  end,
  rw [set.subset_def] at t₁_in_X,
  specialize t₁_in_X y,
  assumption,

  rw [t_decomp, ←finset.image_union],
end

def stellar_coe_forward
    [nonempty α]
    (X : simplicial_complex α)
    (φ : simplicial_coe X β)
    (s : finset α) [s_ne : nonempty s]
    (x : α) (y : β)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (y_nin_coe : y ∉ vertices (φ[X]))
  : simplicial_map
      σ(X, s, x; s_ne, s_in_X, x_nin_X)
      σ(φ[X], finset.image φ.coe s, y; _, by { apply map_is_simplicial_onto_image, assumption, }, y_nin_coe)
:= simplicial_map.mk
    (stellar_coe_map φ.coe x y)
    (stellar_coe_forward_simplicial X φ s x y s_in_X x_nin_X y_nin_coe)

noncomputable
def stellar_coe_inverse
    [nonempty α]
    (X : simplicial_complex α)
    (φ : simplicial_coe X β)
    (s : finset α) [s_ne : nonempty s]
    (x : α) (y : β)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (y_nin_coe : y ∉ vertices (φ[X]))
  : simplicial_map
      σ(φ[X], finset.image φ.coe s, y; _, by { apply map_is_simplicial_onto_image, assumption, }, y_nin_coe)
      σ(X, s, x; s_ne, s_in_X, x_nin_X)
:= simplicial_map.mk
    (stellar_coe_map (φ⁻ᶜ.map) y x)
    (stellar_coe_inverse_simplicial X φ s x y s_in_X x_nin_X y_nin_coe)

lemma stellar_subdiv_congr_simplices
    (X Y : simplicial_complex α)
    (s : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (X_eq_Y : X.simplices = Y.simplices)
  : (σ(X, s, x; s_ne, s_in_X, x_nin_X)).simplices
      = (σ(Y, s, x; s_ne, by { rw [←X_eq_Y], assumption, }, by { rw [←vertices_congr X Y X_eq_Y], assumption, })).simplices
:= begin
  simp only [stellar_subdivision, simplicial_union, star_complement, link, simplex, simplex_boundary, X_eq_Y],
  refl,
end

lemma stellar_coe_vertices
    (X : simplicial_complex α)
    (φ : simplicial_coe X β)
    (s : finset α) [s_ne : nonempty s]
    (x : α) (y : β)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (y_nin_coe : y ∉ vertices (φ[X]))
  : vertices (simplicial_image X (stellar_coe_map φ.coe x y)) = vertices (φ[X])
:= begin
  simp only [simplicial_image_vertices, set.ext_iff, set.mem_image],
  intros t,
  split;

  { intros t_in_img,
    choose u u_in_X coe_u_t using t_in_img,
    
    use u, split, assumption,
    rw [←coe_u_t],
    
    have u_ne_x : u ≠ x, from
    begin
      by_contradiction u_eq_x,
      rw [u_eq_x] at u_in_X,
      contradiction,
    end,
    simp only [stellar_coe_map, u_ne_x, if_false], },
end

lemma stellar_coe_image
    (X : simplicial_complex α)
    (φ : simplicial_coe X β)
    (s : finset α) [s_ne : nonempty s]
    (x : α) (y : β)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (y_nin_coe : y ∉ vertices (φ[X]))
  : σ(simplicial_image X (stellar_coe_map φ.coe x y), finset.image (stellar_coe_map φ.coe x y) s, (stellar_coe_map φ.coe x y) x;
        _,
        by { apply map_is_simplicial_onto_image, assumption, },
        (begin
          simp only [stellar_coe_map, eq_self_iff_true, if_true],
          rw [←stellar_coe_map, stellar_coe_vertices X φ s x y];
          assumption,
        end))
      ≅ σ(simplicial_image X φ.coe, finset.image φ.coe s, y; _, by { apply map_is_simplicial_onto_image, assumption, }, y_nin_coe)
:= begin
  apply simplicial_iso_preserves_equiv,
  have x_nin_s : x ∉ s, from
  begin
    revert x_nin_X,
    contrapose,
    simp only [not_not, ←finset.mem_coe],
    have s_ss_X : ↑s ⊆ vertices X, from
    begin
      apply simplex_subset_vertices,
      assumption,
    end,
    rw [set.subset_def] at s_ss_X,
    specialize s_ss_X x,
    assumption,
  end,

  simp only [stellar_coe_simplex_image s x y φ.coe x_nin_s], -- Borked: introducing proofs means Lean doesn't know how to do the rw.
  simp only [stellar_coe_map, eq_self_iff_true, if_true],
  apply stellar_subdiv_congr_simplices,
  apply simplicial_image_congr,

  simp only [set.eq_on],
  intros z z_in_X,
  split_ifs,
  rw [h] at z_in_X,
  contradiction,
  refl,
end

lemma stellar_coe_inv_iso
    [nonempty α]
    (X : simplicial_complex α)
    (φ : simplicial_coe X β)
    (s : finset α) [s_ne : nonempty s]
    (x : α) (y : β)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (y_nin_coe : y ∉ vertices (φ[X]))
  : is_inverse_simplicial_iso
      (stellar_coe_forward X φ s x y s_in_X x_nin_X y_nin_coe)
      (stellar_coe_inverse X φ s x y s_in_X x_nin_X y_nin_coe)
:= begin
  unfold is_inverse_simplicial_iso,
  simp only [set.restrict_eq_restrict_iff, set.eq_on, simplicial_map.comp, function.comp_app, id.def],
  simp only [stellar_coe_inverse, stellar_coe_forward],
  split,

  { intros a a_in_subdiv,
    have a_in_union : a ∈ vertices X ∪ {x}, from
    begin
      apply set.mem_of_mem_of_subset a_in_subdiv,
      apply stellar_subdiv_subset_vertices,
    end,
    rw [set.mem_union, set.mem_singleton_iff] at a_in_union,
    cases a_in_union with a_in_X a_eq_x,
    
    have a_ne_x : ¬a = x, from
    begin
      by_cases a_eq_x : a = x,
      rw [a_eq_x] at a_in_X,
      contradiction,
      assumption,
    end,

    have φa_ne_y : ¬φ.coe a = y, from
    begin
      by_cases φa_eq_y : φ.coe a = y,

      have contra : y ∈ vertices (φ[X]), from
      begin
        rw [simplicial_image_vertices, set.mem_image],
        use a, split; assumption,
      end,
      contradiction,

      assumption,
    end,

    simp only [stellar_coe_map, a_ne_x, φa_ne_y, if_false],
    apply set.inj_on.left_inv_on_inv_fun_on,
    apply φ.injective,
    assumption,
    
    simp only [stellar_coe_map, a_eq_x, eq_self_iff_true, if_true], },

  { intros b b_in_coe,
    have b_in_union : b ∈ vertices (φ[X]) ∪ {y}, from
    begin
      apply set.mem_of_mem_of_subset,
      apply b_in_coe,
      apply stellar_subdiv_subset_vertices,
    end,
    rw [set.mem_union, set.mem_singleton_iff] at b_in_union,
    cases b_in_union with b_in_X b_eq_y,
    
    have b_ne_y : ¬b = y, from
    begin
      by_cases b_eq_y : b = y,
      rw [b_eq_y] at b_in_X,
      contradiction,
      assumption,
    end,
    
    have φb_ne_x : ¬(φ⁻ᶜ.map) b = x, from
    begin
      by_cases φb_eq_x : (φ⁻ᶜ.map) b = x,

      rw [simplicial_image_vertices, set.mem_image] at b_in_X,
      choose a a_in_X φa_b using b_in_X,
      rw [←φa_b] at φb_eq_x,
      have inv_a : (φ⁻ᶜ.map) (φ.coe a) = a, from
      begin
        simp only [simplicial_coe_inv],
        apply set.inj_on.left_inv_on_inv_fun_on,
        apply φ.injective,
        assumption,
      end,
      rw [inv_a] at φb_eq_x,
      rw [φb_eq_x] at a_in_X,
      contradiction,

      assumption,
    end,

    simp only [stellar_coe_map, b_ne_y, φb_ne_x, if_false],
    simp only [simplicial_coe_inv],
    apply function.inv_fun_on_eq,
    simp only [simplicial_image_vertices, set.mem_image, ←exists_prop] at b_in_X,
    assumption,
    
    simp only [stellar_coe_map, b_eq_y, eq_self_iff_true, if_true], },
end

lemma stellar_coe_iso
    [nonempty α]
    (X : simplicial_complex α)
    (φ : simplicial_coe X β)
    (s : finset α) [s_ne : nonempty s]
    (x : α) (y : β)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (y_nin_coe : y ∉ vertices (φ[X]))
  : is_simplicial_iso (stellar_coe_forward X φ s x y s_in_X x_nin_X y_nin_coe)
:= begin
  use (stellar_coe_inverse X φ s x y s_in_X x_nin_X y_nin_coe),
  apply stellar_coe_inv_iso,
end

lemma stellar_weld_exists_iso
    [nonempty α]
    (X Y : simplicial_complex α)
    (Z : simplicial_complex β)
    (t : finset α) [t_ne : nonempty t]
    (y : α)
    (t_in_Y : t ∈ Y.simplices)
    (y_nin_Y : y ∉ vertices Y)
  : X ≅ Z → X ≅ σ(Y, t, y; t_ne, t_in_Y, y_nin_Y) →
      ∃ (W : simplicial_complex β), Y ≅ W ∧ Z ≅ₛₜ W
:= begin
  intros X_iso_Z Y_subdiv_X,
  have Z_iso_subdiv : Z ≅ σ(Y, t, y; t_ne, t_in_Y, y_nin_Y), from
  begin
    apply simplicial_iso_trans Z X,
    rw [simplicial_iso_symm],
    assumption,
    assumption,
  end,

  let Z_iso_subdiv' := Z_iso_subdiv,
  unfold is_simplicially_iso at Z_iso_subdiv',
  choose f f_iso using Z_iso_subdiv',

  let f_iso' := f_iso,
  unfold is_simplicial_iso at f_iso',
  choose g gf_inv using f_iso',

  let gf_inv' := gf_inv,
  unfold is_inverse_simplicial_iso at gf_inv',
  simp only [set.restrict_eq_restrict_iff, set.eq_on, simplicial_map.comp, function.comp_app, id.def] at gf_inv',
  choose gf_id fg_id using gf_inv',

  have g_iso : is_simplicial_iso g, from
  begin
    apply iso_inv_is_iso f g f_iso gf_inv,
  end,

  by_cases t_singleton : t.card = 1,
  
  rw [finset.card_eq_one] at t_singleton,
  choose a t_eq_a using t_singleton,
  unfreezingI { subst t_eq_a },
  rw [stellar_subdiv_of_singleton_vertices] at fg_id,
  
  use Z, split,
  apply simplicial_iso_trans Y (σ(Y, {a}, y; t_ne, t_in_Y, y_nin_Y)),
  rw [simplicial_iso_symm],
  apply stellar_subdiv_of_singleton,
  rw [simplicial_iso_symm],
  assumption,

  apply relation.refl_trans_gen.single,
  unfold stellar_move,
  right, right,
  apply simplicial_iso_refl,
  
  have t_nonsingleton : t.card > 1, from
  begin
    rw [finset.nonempty_coe_sort, finset.nonempty_iff_ne_empty, ne.def, ←finset.card_eq_zero] at t_ne,
    omega,
  end,
  
  have g_inj : set.inj_on g.map (vertices Y), from
  begin
    apply @set.inj_on.mono _ _ (vertices Y) (vertices Y ∪ {y}),
    apply set.subset_union_left,
    rw [←stellar_subdiv_vertices Y t y t_in_Y y_nin_Y t_nonsingleton],
    apply iso_is_injective_vertices g g_iso,
  end,
  let g_coe : simplicial_coe Y β :=
    simplicial_coe.mk g.map g_inj,

  have gy_nin_gY : g.map y ∉ vertices (g_coe[Y]), from
  begin
    by_cases gy_in_Y : g.map y ∈ vertices (g_coe[Y]),

    rw [simplicial_image_vertices] at gy_in_Y,
    have contra : y ∈ vertices Y, from
    begin
      apply set.inj_on.mem_of_mem_image,
      apply iso_is_injective_vertices g g_iso,
      rw [stellar_subdiv_vertices Y t y t_in_Y y_nin_Y t_nonsingleton],
      apply set.subset_union_left,
      apply barycenter_vertex_stellar_subdiv,
      assumption,
    end,
    contradiction,

    assumption,
  end,

  let φ := stellar_coe_forward Y g_coe t y (g.map y) t_in_Y y_nin_Y gy_nin_gY,

  have φ_inj : set.inj_on φ.map (vertices Y ∪ {y}), from
  begin
    rw [←stellar_subdiv_vertices Y t y t_in_Y y_nin_Y t_nonsingleton],
    apply iso_is_injective_vertices φ (stellar_coe_iso Y g_coe t y (g.map y) t_in_Y y_nin_Y gy_nin_gY),
  end,

  have φy_nin_φY : φ.map y ∉ vertices (simplicial_image Y φ.map), from
  begin
    by_cases φy_in_Y : φ.map y ∈ vertices (simplicial_image Y φ.map),

    rw [simplicial_image_vertices] at φy_in_Y,
    have contra : y ∈ vertices Y, from
    begin
      apply set.inj_on.mem_of_mem_image,
      apply φ_inj,
      apply set.subset_union_left,

      rw [set.mem_union, set.mem_singleton_iff],
      right, refl,

      assumption,
    end,
    contradiction,

    assumption,
  end,
    
  use (simplicial_image Y φ.map), split,
  have φY_inj : set.inj_on φ.map (vertices Y), from
  begin
    apply @set.inj_on.mono _ _ _ (vertices Y ∪ {y}),
    apply set.subset_union_left,
    assumption,
  end,
  let φY := simplicial_coe.mk φ.map φY_inj,
  apply simplicial_iso_trans _ (φY[Y]),
  apply φY.iso_onto_image,
  apply simplicial_iso_preserves_equiv,
  apply simplicial_image_congr,
  simp only,

  apply relation.refl_trans_gen.single,
  unfold stellar_move,
  left,
  use (finset.image φ.map t),

  have φt_in_φY : finset.image φ.map t ∈ (simplicial_image Y φ.map).simplices, from
  begin
    apply map_is_simplicial_onto_image Y φ.map,
    assumption,
  end,
  use φt_in_φY,

  have φt_ne : nonempty ↥(finset.image φ.map t), from
  begin
    rw [finset.nonempty_coe_sort] at t_ne ⊢,
    apply finset.nonempty.image t_ne,
  end,
  use φt_ne,

  use (φ.map y),
  use φy_nin_φY,

  apply simplicial_iso_trans Z σ(Y, t, y; t_ne, t_in_Y, y_nin_Y),
  assumption,

  apply simplicial_iso_trans _
    σ(simplicial_image Y g_coe.coe, finset.image g_coe.coe t, g.map y;
      _,
      (by { apply map_is_simplicial_onto_image, assumption, }),
      gy_nin_gY),
  unfold is_simplicially_iso,
  use φ,
  apply stellar_coe_iso,

  rw [simplicial_iso_symm],
  apply stellar_coe_image;
  assumption,
end

lemma barycenter_injective_image
    {X : simplicial_complex α}
    {x : α}
    {f : α → β}
  : x ∉ vertices X → function.injective f → f x ∉ vertices (simplicial_image X f)
:= begin
  intros x_nin_X f_inj,
  by_contradiction fx_in_X,

  rw [simplicial_image_vertices] at fx_in_X,
  have contra : x ∈ vertices X, from
  begin
    apply set.inj_on.mem_of_mem_image,
    apply function.injective.inj_on f_inj set.univ,
    apply set.subset_univ,
    apply set.mem_univ,
    assumption,
  end,
  contradiction,
end

lemma stellar_subdiv_injective_image_simplices_left
    (X : simplicial_complex α)
    (s : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (f : α → β) (f_inj : function.injective f)
  : (simplicial_image σ(X, s, x; s_ne, s_in_X, x_nin_X) f).simplices ⊆
      (σ(simplicial_image X f, finset.image f s, f x;
        _,
        (by { apply map_is_simplicial_onto_image, assumption, }),
        (barycenter_injective_image x_nin_X f_inj))).simplices
:= begin
  rw [set.subset_def],
  intros t t_in_img,
  simp only [simplicial_image, set.mem_set_of] at t_in_img,
  simp only [stellar_subdivision, simplicial_union, set.mem_union] at t_in_img ⊢,
  choose u u_in_subdiv fu_t using t_in_img,
  cases u_in_subdiv with u_in_star_comp u_in_join,
  
  left,
  simp only [star_complement, set.mem_sep_iff] at u_in_star_comp ⊢,
  choose u_in_X s_nss_u using u_in_star_comp,
  
  split,
  simp only [simplicial_image, set.mem_set_of],
  use u, split; assumption,
  
  rw [←fu_t],
  revert s_nss_u,
  contrapose,
  simp only [not_not, finset.subset_iff],
  intros fs_ss_fu a a_in_s,
  
  have fa_in_fs : f a ∈ finset.image f s, by apply finset.mem_image_of_mem f a_in_s,
  specialize fs_ss_fu fa_in_fs,
  rw [function.injective.mem_finset_image f_inj] at fs_ss_fu,
  assumption,
  
  right,
  simp only [join_proj_mem] at u_in_join ⊢,
  choose u' u'_in_join u₁ u₁_in_link u_decomp using u_in_join,
  choose u₃ u₃_in_barycenter u₂ u₂_in_bd u'_decomp using u'_in_join,
  subst u'_decomp,
  
  use (finset.image f (u₃ ∪ u₂)), split,
  use (finset.image f u₃), split,
  simp only [simplex, finset.mem_coe, finset.mem_powerset, finset.subset_singleton_iff] at u₃_in_barycenter ⊢,
  cases u₃_in_barycenter with u₃_empty u₃_eq_x,

  left,
  rw [u₃_empty],
  apply finset.image_empty,
  
  right,
  rw [u₃_eq_x],
  apply finset.image_singleton,
  
  use (finset.image f u₂), split,
  simp only [simplex_boundary, set.mem_union, set.mem_diff, finset.mem_coe, finset.mem_powerset, set.mem_singleton_iff] at u₂_in_bd ⊢,
  cases u₂_in_bd with u₂_in_bd u₂_empty,
  
  left,
  choose u₂_ss_s u₂_ne_s using u₂_in_bd,
  split,
  apply finset.image_subset_image,
  assumption,
  
  revert u₂_ne_s,
  contrapose,
  simp only [not_not, finset.ext_iff],
  intros fu₂_eq_fs a,
  specialize fu₂_eq_fs (f a),
  cases fu₂_eq_fs with fu₂_ss_fs fs_ss_fu₂,
  split,
  
  intros a_in_u₂,
  have fa_in_fu₂ : f a ∈ finset.image f u₂, by apply finset.mem_image_of_mem f a_in_u₂,
  specialize fu₂_ss_fs fa_in_fu₂,
  rw [function.injective.mem_finset_image f_inj] at fu₂_ss_fs,
  assumption,
  
  intros a_in_s,
  have fa_in_fs : f a ∈ finset.image f s, by apply finset.mem_image_of_mem f a_in_s,
  specialize fs_ss_fu₂ fa_in_fs,
  rw [function.injective.mem_finset_image f_inj] at fs_ss_fu₂,
  assumption,
  
  right,
  rw [u₂_empty],
  apply finset.image_empty,
  
  rw [finset.image_union],
  
  use (finset.image f u₁), split,
  simp only [link, set.mem_sep_iff] at u₁_in_link ⊢,
  choose u₁_in_X su₁_in_X su₁_disj using u₁_in_link,
  
  split,
  apply map_is_simplicial_onto_image,
  assumption,
  
  split,
  rw [←finset.image_union],
  apply map_is_simplicial_onto_image,
  assumption,
  
  rw [←finset.image_inter s u₁ f_inj, finset.image_eq_empty],
  assumption,
  
  rw [←finset.image_union, ←fu_t, u_decomp],
end

lemma stellar_subdiv_injective_image_simplices_right_ac
    [nonempty α]
    (X : simplicial_complex α)
    (s : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (f : α → β) (f_inj : function.injective f)
  : ∀ (t : finset β),
      (∃ (t₁ t₂ t₃ : finset β),
        t₁ ∈ (Lk(simplicial_image X f, finset.image f s) (by { apply map_is_simplicial_onto_image, assumption, })).simplices ∧
        t₂ ⊆ finset.image f s ∧ ¬t₂ = finset.image f s ∧
        t₃ = ∅ ∧
        t = t₃ ∪ t₂ ∪ t₁)
      → (t ∈ (simplicial_image σ(X, s, x; s_ne, s_in_X, x_nin_X) f).simplices)
:= begin
  intros t t_decomp,
  choose t₁ t₂ t₃ t₁_in_link t₂_ss_fs t₂_ne_fs t₃_empty t_decomp using t_decomp,
  simp only [simplicial_image, set.mem_set_of],
  simp only [stellar_subdivision, simplicial_union, set.mem_union],

  simp only [link, set.mem_sep_iff, simplicial_image, set.mem_set_of] at t₁_in_link,
  choose t₁_in_fX fst₁_in_fX fst₁_disj using t₁_in_link,
  choose u₁ u₁_in_X fu₁_t₁ using t₁_in_fX,
  choose v v_in_X fv_fsu₁ using fst₁_in_fX,
  subst fu₁_t₁,

  subst t₃_empty,
  set u₂ := finset.image (function.inv_fun_on f set.univ) t₂,
  use (∅ ∪ u₂ ∪ u₁), split, right,
  simp only [join_proj_mem],

  use (∅ ∪ u₂), split,
  use ∅, split, apply simplicial_complex_empty_simplex,
  use u₂, split,
  simp only [simplex_boundary, set.mem_union, set.mem_diff, set.mem_singleton_iff, finset.mem_coe, finset.mem_powerset],
  left, split,
  
  rw [finset.subset_iff] at t₂_ss_fs ⊢,
  intros a a_in_u₂,
  have fa_in_t₂ : f a ∈ t₂, from
  begin
    rw [finset.mem_image] at a_in_u₂,
    choose b b_in_t₂ fb_a using a_in_u₂,
    rw [←fb_a, @function.inv_fun_on_eq _ _ _ set.univ f],
    assumption,
    specialize t₂_ss_fs b_in_t₂,
    rw [finset.mem_image] at t₂_ss_fs,
    choose c c_in_s fc_b using t₂_ss_fs,
    use c, split, apply set.mem_univ,
    assumption,
  end,
  specialize t₂_ss_fs fa_in_t₂,
  rw [function.injective.mem_finset_image f_inj] at t₂_ss_fs,
  assumption,
  
  revert t₂_ne_fs,
  contrapose,
  simp only [not_not, finset.ext_iff],
  intros u₂_eq_s b,
  split,
  
  intros b_in_t₂,
  specialize u₂_eq_s ((function.inv_fun_on f set.univ) b),
  cases u₂_eq_s with u₂_ss_s s_ss_u₂,
  have fb_in_u₂ : (function.inv_fun_on f set.univ) b ∈ u₂, by apply finset.mem_image_of_mem (function.inv_fun_on f set.univ) b_in_t₂,
  specialize u₂_ss_s fb_in_u₂,
  rw [finset.mem_image],
  use ((function.inv_fun_on f set.univ) b), split,
  assumption,
  rw [@function.inv_fun_on_eq _ _ _ set.univ f],
  simp only [finset.subset_iff, finset.mem_image] at t₂_ss_fs,
  specialize t₂_ss_fs b_in_t₂,
  choose c c_in_s fc_b using t₂_ss_fs,
  use c, split, apply set.mem_univ,
  assumption,
  
  intros b_in_fs,
  rw [finset.mem_image] at b_in_fs,
  choose a a_in_s fa_b using b_in_fs,
  specialize u₂_eq_s a,
  cases u₂_eq_s with u₂_ss_s s_ss_u₂,
  specialize s_ss_u₂ a_in_s,
  rw [finset.mem_image] at s_ss_u₂,
  choose c c_in_t₂ fc_a using s_ss_u₂,
  rw [←fc_a] at fa_b,
  rw [@function.inv_fun_on_eq _ _ _ set.univ f] at fa_b,
  rw [←fa_b],
  assumption,

  simp only [finset.subset_iff, finset.mem_image] at t₂_ss_fs,
  specialize t₂_ss_fs c_in_t₂,
  choose d d_in_s fd_c using t₂_ss_fs,
  use d, split, apply set.mem_univ,
  assumption,
  
  refl,
  
  use u₁, split,
  simp only [link, set.mem_sep_iff],
  split, assumption,
  
  split,
  have v_su₁ : v = s ∪ u₁, from
  begin
    rw [←finset.image_union] at fv_fsu₁,
    rw [finset.ext_iff] at fv_fsu₁ ⊢,
    intros a,
    specialize fv_fsu₁ (f a),
    cases fv_fsu₁ with fv_ss_fsu₁ fsu₁_ss_fv,
    split,

    intros a_in_v,
    specialize fv_ss_fsu₁ (by apply finset.mem_image_of_mem f a_in_v),
    rw [function.injective.mem_finset_image f_inj] at fv_ss_fsu₁,
    assumption,

    intros a_in_su₁,
    specialize fsu₁_ss_fv (by apply finset.mem_image_of_mem f a_in_su₁),
    rw [function.injective.mem_finset_image f_inj] at fsu₁_ss_fv,
    assumption,
  end,
  rw [v_su₁] at v_in_X,
  assumption,
  
  rw [←finset.image_inter s u₁ f_inj, finset.image_eq_empty] at fst₁_disj,
  assumption,
  
  refl,
  
  simp only [finset.image_union],
  have fu₂_t₂ : finset.image f u₂ = t₂, from
  begin
    simp only [finset.ext_iff, finset.mem_image],
    intros a,
    split,

    intros a_in_img,
    choose c c_in_inv fc_a using a_in_img,
    choose b b_in_t₂ fb_c using c_in_inv,
    rw [←fb_c, @function.inv_fun_on_eq _ _ _ set.univ f] at fc_a,
    rw [←fc_a],
    assumption,

    simp only [finset.subset_iff, finset.mem_image] at t₂_ss_fs,
    specialize t₂_ss_fs b_in_t₂,
    choose d d_in_s fd_b using t₂_ss_fs,
    use d, split, apply set.mem_univ,
    assumption,

    intros a_in_t₂,
    simp only [finset.subset_iff, finset.mem_image] at t₂_ss_fs,
    specialize t₂_ss_fs a_in_t₂,
    choose b b_in_s fb_a using t₂_ss_fs,
    use b, split,
    use a, split, assumption,
    rw [←fb_a],
    apply set.inj_on.left_inv_on_inv_fun_on,
    apply function.injective.inj_on f_inj,
    apply set.mem_univ,
    assumption,
  end,
  rw [fu₂_t₂, finset.image_empty],
  symmetry,
  assumption,
end

lemma stellar_subdiv_injective_image_simplices_right_ad
    [nonempty α]
    (X : simplicial_complex α)
    (s : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (f : α → β) (f_inj : function.injective f)
  : ∀ (t : finset β),
      (∃ (t₁ t₂ t₃ : finset β),
        t₁ ∈ (Lk(simplicial_image X f, finset.image f s) (by { apply map_is_simplicial_onto_image, assumption, })).simplices ∧
        t₂ ⊆ finset.image f s ∧ ¬t₂ = finset.image f s ∧
        t₃ = {f x} ∧
        t = t₃ ∪ t₂ ∪ t₁)
      → (t ∈ (simplicial_image σ(X, s, x; s_ne, s_in_X, x_nin_X) f).simplices)
:= begin
  intros t t_decomp,
  choose t₁ t₂ t₃ t₁_in_link t₂_ss_fs t₂_ne_fs t₃_eq_fx t_decomp using t_decomp,
  simp only [simplicial_image, set.mem_set_of],
  simp only [stellar_subdivision, simplicial_union, set.mem_union],

  simp only [link, set.mem_sep_iff, simplicial_image, set.mem_set_of] at t₁_in_link,
  choose t₁_in_fX fst₁_in_fX fst₁_disj using t₁_in_link,
  choose u₁ u₁_in_X fu₁_t₁ using t₁_in_fX,
  choose v v_in_X fv_fsu₁ using fst₁_in_fX,
  subst fu₁_t₁,

  subst t₃_eq_fx,
  set u₂ := finset.image (function.inv_fun_on f set.univ) t₂,
  use ({x} ∪ u₂ ∪ u₁), split, right,
  simp only [join_proj_mem],

  use ({x} ∪ u₂), split,
  use {x}, split,
  simp only [simplex, finset.mem_coe],
  apply finset.mem_powerset_self,

  use u₂, split,
  simp only [simplex_boundary, set.mem_union, set.mem_diff, set.mem_singleton_iff, finset.mem_coe, finset.mem_powerset],
  left, split,
  
  rw [finset.subset_iff] at t₂_ss_fs ⊢,
  intros a a_in_u₂,
  have fa_in_t₂ : f a ∈ t₂, from
  begin
    rw [finset.mem_image] at a_in_u₂,
    choose b b_in_t₂ fb_a using a_in_u₂,
    rw [←fb_a, @function.inv_fun_on_eq _ _ _ set.univ f],
    assumption,
    specialize t₂_ss_fs b_in_t₂,
    rw [finset.mem_image] at t₂_ss_fs,
    choose c c_in_s fc_b using t₂_ss_fs,
    use c, split, apply set.mem_univ,
    assumption,
  end,
  specialize t₂_ss_fs fa_in_t₂,
  rw [function.injective.mem_finset_image f_inj] at t₂_ss_fs,
  assumption,
  
  revert t₂_ne_fs,
  contrapose,
  simp only [not_not, finset.ext_iff],
  intros u₂_eq_s b,
  split,
  
  intros b_in_t₂,
  specialize u₂_eq_s ((function.inv_fun_on f set.univ) b),
  cases u₂_eq_s with u₂_ss_s s_ss_u₂,
  have fb_in_u₂ : (function.inv_fun_on f set.univ) b ∈ u₂, by apply finset.mem_image_of_mem (function.inv_fun_on f set.univ) b_in_t₂,
  specialize u₂_ss_s fb_in_u₂,
  rw [finset.mem_image],
  use ((function.inv_fun_on f set.univ) b), split,
  assumption,
  rw [@function.inv_fun_on_eq _ _ _ set.univ f],
  simp only [finset.subset_iff, finset.mem_image] at t₂_ss_fs,
  specialize t₂_ss_fs b_in_t₂,
  choose c c_in_s fc_b using t₂_ss_fs,
  use c, split, apply set.mem_univ,
  assumption,
  
  intros b_in_fs,
  rw [finset.mem_image] at b_in_fs,
  choose a a_in_s fa_b using b_in_fs,
  specialize u₂_eq_s a,
  cases u₂_eq_s with u₂_ss_s s_ss_u₂,
  specialize s_ss_u₂ a_in_s,
  rw [finset.mem_image] at s_ss_u₂,
  choose c c_in_t₂ fc_a using s_ss_u₂,
  rw [←fc_a] at fa_b,
  rw [@function.inv_fun_on_eq _ _ _ set.univ f] at fa_b,
  rw [←fa_b],
  assumption,

  simp only [finset.subset_iff, finset.mem_image] at t₂_ss_fs,
  specialize t₂_ss_fs c_in_t₂,
  choose d d_in_s fd_c using t₂_ss_fs,
  use d, split, apply set.mem_univ,
  assumption,
  
  refl,
  
  use u₁, split,
  simp only [link, set.mem_sep_iff],
  split, assumption,
  
  split,
  have v_su₁ : v = s ∪ u₁, from
  begin
    rw [←finset.image_union] at fv_fsu₁,
    rw [finset.ext_iff] at fv_fsu₁ ⊢,
    intros a,
    specialize fv_fsu₁ (f a),
    cases fv_fsu₁ with fv_ss_fsu₁ fsu₁_ss_fv,
    split,

    intros a_in_v,
    specialize fv_ss_fsu₁ (by apply finset.mem_image_of_mem f a_in_v),
    rw [function.injective.mem_finset_image f_inj] at fv_ss_fsu₁,
    assumption,

    intros a_in_su₁,
    specialize fsu₁_ss_fv (by apply finset.mem_image_of_mem f a_in_su₁),
    rw [function.injective.mem_finset_image f_inj] at fsu₁_ss_fv,
    assumption,
  end,
  rw [v_su₁] at v_in_X,
  assumption,
  
  rw [←finset.image_inter s u₁ f_inj, finset.image_eq_empty] at fst₁_disj,
  assumption,
  
  refl,
  
  simp only [finset.image_union],
  have fu₂_t₂ : finset.image f u₂ = t₂, from
  begin
    simp only [finset.ext_iff, finset.mem_image],
    intros a,
    split,

    intros a_in_img,
    choose c c_in_inv fc_a using a_in_img,
    choose b b_in_t₂ fb_c using c_in_inv,
    rw [←fb_c, @function.inv_fun_on_eq _ _ _ set.univ f] at fc_a,
    rw [←fc_a],
    assumption,

    simp only [finset.subset_iff, finset.mem_image] at t₂_ss_fs,
    specialize t₂_ss_fs b_in_t₂,
    choose d d_in_s fd_b using t₂_ss_fs,
    use d, split, apply set.mem_univ,
    assumption,

    intros a_in_t₂,
    simp only [finset.subset_iff, finset.mem_image] at t₂_ss_fs,
    specialize t₂_ss_fs a_in_t₂,
    choose b b_in_s fb_a using t₂_ss_fs,
    use b, split,
    use a, split, assumption,
    rw [←fb_a],
    apply set.inj_on.left_inv_on_inv_fun_on,
    apply function.injective.inj_on f_inj,
    apply set.mem_univ,
    assumption,
  end,
  rw [fu₂_t₂, finset.image_singleton],
  symmetry,
  assumption,
end

lemma stellar_subdiv_injective_image_simplices_right_bc
    (X : simplicial_complex α)
    (s : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (f : α → β) (f_inj : function.injective f)
  : ∀ (t : finset β),
      (∃ (t₁ t₂ t₃ : finset β),
        t₁ ∈ (Lk(simplicial_image X f, finset.image f s) (by { apply map_is_simplicial_onto_image, assumption, })).simplices ∧
        t₂ = ∅ ∧
        t₃ = ∅ ∧
        t = t₃ ∪ t₂ ∪ t₁)
      → (t ∈ (simplicial_image σ(X, s, x; s_ne, s_in_X, x_nin_X) f).simplices)
:= begin
  intros t t_decomp,
  choose t₁ t₂ t₃ t₁_in_link t₂_empty t₃_empty t_decomp using t_decomp,
  simp only [simplicial_image, set.mem_set_of],
  simp only [stellar_subdivision, simplicial_union, set.mem_union],

  simp only [link, set.mem_sep_iff, simplicial_image, set.mem_set_of] at t₁_in_link,
  choose t₁_in_fX fst₁_in_fX fst₁_disj using t₁_in_link,
  choose u₁ u₁_in_X fu₁_t₁ using t₁_in_fX,
  choose v v_in_X fv_fsu₁ using fst₁_in_fX,
  subst fu₁_t₁,

  use (∅ ∪ ∅ ∪ u₁), split, right,
  simp only [join_proj_mem],

  use (∅ ∪ ∅), split,
  use ∅, split, apply simplicial_complex_empty_simplex,
  use ∅, split, apply simplicial_complex_empty_simplex,
  refl,

  use u₁, split,
  simp only [link, set.mem_sep_iff],
  split, assumption,
  
  split,
  have v_su₁ : v = s ∪ u₁, from
  begin
    rw [←finset.image_union] at fv_fsu₁,
    rw [finset.ext_iff] at fv_fsu₁ ⊢,
    intros a,
    specialize fv_fsu₁ (f a),
    cases fv_fsu₁ with fv_ss_fsu₁ fsu₁_ss_fv,
    split,

    intros a_in_v,
    specialize fv_ss_fsu₁ (by apply finset.mem_image_of_mem f a_in_v),
    rw [function.injective.mem_finset_image f_inj] at fv_ss_fsu₁,
    assumption,

    intros a_in_su₁,
    specialize fsu₁_ss_fv (by apply finset.mem_image_of_mem f a_in_su₁),
    rw [function.injective.mem_finset_image f_inj] at fsu₁_ss_fv,
    assumption,
  end,
  rw [v_su₁] at v_in_X,
  assumption,
  
  rw [←finset.image_inter s u₁ f_inj, finset.image_eq_empty] at fst₁_disj,
  assumption,
  
  refl,
  
  simp only [finset.image_union, finset.image_singleton, finset.image_empty],
  subst t₃_empty,
  subst t₂_empty,
  symmetry,
  assumption,
end

lemma stellar_subdiv_injective_image_simplices_right_bd
    (X : simplicial_complex α)
    (s : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (f : α → β) (f_inj : function.injective f)
  : ∀ (t : finset β),
      (∃ (t₁ t₂ t₃ : finset β),
        t₁ ∈ (Lk(simplicial_image X f, finset.image f s) (by { apply map_is_simplicial_onto_image, assumption, })).simplices ∧
        t₂ = ∅ ∧
        t₃ = {f x} ∧
        t = t₃ ∪ t₂ ∪ t₁)
      → (t ∈ (simplicial_image σ(X, s, x; s_ne, s_in_X, x_nin_X) f).simplices)
:= begin
  intros t t_decomp,
  choose t₁ t₂ t₃ t₁_in_link t₂_empty t₃_eq_fx t_decomp using t_decomp,
  simp only [simplicial_image, set.mem_set_of],
  simp only [stellar_subdivision, simplicial_union, set.mem_union],

  simp only [link, set.mem_sep_iff, simplicial_image, set.mem_set_of] at t₁_in_link,
  choose t₁_in_fX fst₁_in_fX fst₁_disj using t₁_in_link,
  choose u₁ u₁_in_X fu₁_t₁ using t₁_in_fX,
  choose v v_in_X fv_fsu₁ using fst₁_in_fX,
  subst fu₁_t₁,

  use ({x} ∪ ∅ ∪ u₁), split, right,
  simp only [join_proj_mem],

  use ({x} ∪ ∅), split,
  use {x}, split,
  simp only [simplex, finset.mem_coe],
  apply finset.mem_powerset_self,

  use ∅, split, apply simplicial_complex_empty_simplex,
  refl,

  use u₁, split,
  simp only [link, set.mem_sep_iff],
  split, assumption,
  
  split,
  have v_su₁ : v = s ∪ u₁, from
  begin
    rw [←finset.image_union] at fv_fsu₁,
    rw [finset.ext_iff] at fv_fsu₁ ⊢,
    intros a,
    specialize fv_fsu₁ (f a),
    cases fv_fsu₁ with fv_ss_fsu₁ fsu₁_ss_fv,
    split,

    intros a_in_v,
    specialize fv_ss_fsu₁ (by apply finset.mem_image_of_mem f a_in_v),
    rw [function.injective.mem_finset_image f_inj] at fv_ss_fsu₁,
    assumption,

    intros a_in_su₁,
    specialize fsu₁_ss_fv (by apply finset.mem_image_of_mem f a_in_su₁),
    rw [function.injective.mem_finset_image f_inj] at fsu₁_ss_fv,
    assumption,
  end,
  rw [v_su₁] at v_in_X,
  assumption,
  
  rw [←finset.image_inter s u₁ f_inj, finset.image_eq_empty] at fst₁_disj,
  assumption,
  
  refl,
  
  simp only [finset.image_union, finset.image_singleton, finset.image_empty, ←t₃_eq_fx, ←t₂_empty],
  symmetry,
  assumption,
end

lemma stellar_subdiv_injective_image_simplices_right
    [nonempty α]
    (X : simplicial_complex α)
    (s : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (f : α → β) (f_inj : function.injective f)
  : (σ(simplicial_image X f, finset.image f s, f x;
        _,
        (by { apply map_is_simplicial_onto_image, assumption, }),
        (barycenter_injective_image x_nin_X f_inj))).simplices
      ⊆ (simplicial_image σ(X, s, x; s_ne, s_in_X, x_nin_X) f).simplices
:= begin
  rw [set.subset_def],
  intros t t_in_subdiv,
  simp only [stellar_subdivision, simplicial_union, set.mem_union] at t_in_subdiv,
  cases t_in_subdiv with t_in_star_comp t_in_join,
  
  simp only [star_complement, set.mem_sep_iff, simplicial_image, set.mem_set_of] at t_in_star_comp,
  choose t_in_fX fs_nss_t using t_in_star_comp,
  choose u u_in_X fu_t using t_in_fX,
  use u, split, left,
  
  simp only [star_complement, set.mem_sep_iff],
  split, assumption,
  revert fs_nss_t,
  contrapose,
  simp only [not_not, ←fu_t],
  apply finset.image_subset_image,
  assumption,
  
  simp only [join_proj_mem] at t_in_join ⊢,
  choose t' t'_in_join t₁ t₁_in_link t_decomp using t_in_join,
  choose t₃ t₃_in_barycenter t₂ t₂_in_bd t'_decomp using t'_in_join,
  subst t'_decomp,
  
  simp only [simplex_boundary, set.mem_union, set.mem_diff, set.mem_singleton_iff, finset.mem_coe, finset.mem_powerset] at t₂_in_bd,
  simp only [simplex, finset.mem_coe, finset.mem_powerset, finset.subset_singleton_iff] at t₃_in_barycenter,
  
  cases t₂_in_bd with t₂_in_bd t₂_empty;        -- Cases A, B resp.
  cases t₃_in_barycenter with t₃_empty t₃_eq_x, -- Cases C, D resp.
  
  choose t₂_ss_fs t₂_ne_fs using t₂_in_bd,
  apply stellar_subdiv_injective_image_simplices_right_ac,
  assumption,
  use t₁, use t₂, use t₃,
  repeat { split, assumption },
  assumption,

  choose t₂_ss_fs t₂_ne_fs using t₂_in_bd,
  apply stellar_subdiv_injective_image_simplices_right_ad,
  assumption,
  use t₁, use t₂, use t₃,
  repeat { split, assumption },
  assumption,

  apply stellar_subdiv_injective_image_simplices_right_bc,
  assumption,
  use t₁, use t₂, use t₃,
  repeat { split, assumption },
  assumption,

  apply stellar_subdiv_injective_image_simplices_right_bd,
  assumption,
  use t₁, use t₂, use t₃,
  repeat { split, assumption },
  assumption,
end

lemma stellar_subdiv_injective_image_simplices
    [nonempty α]
    (X : simplicial_complex α)
    (s : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (f : α → β) (f_inj : function.injective f)
  : (simplicial_image σ(X, s, x; s_ne, s_in_X, x_nin_X) f).simplices =
      (σ(simplicial_image X f, finset.image f s, f x;
        _,
        (by { apply map_is_simplicial_onto_image, assumption, }),
        (barycenter_injective_image x_nin_X f_inj))).simplices
:= begin
  rw [set.subset.antisymm_iff],
  split,

  apply stellar_subdiv_injective_image_simplices_left,
  apply stellar_subdiv_injective_image_simplices_right,
end

lemma stellar_subdiv_injective_image
    [nonempty α]
    (X : simplicial_complex α)
    (s : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (f : α → β) (f_inj : function.injective f)
  : simplicial_image σ(X, s, x; s_ne, s_in_X, x_nin_X) f ≅
      σ(simplicial_image X f, finset.image f s, f x;
        _,
        (by { apply map_is_simplicial_onto_image, assumption, }),
        (barycenter_injective_image x_nin_X f_inj))
:= begin
  apply simplicial_iso_preserves_equiv,
  apply stellar_subdiv_injective_image_simplices,
end

lemma stellar_subdiv_exists_iso
    [nonempty α]
    (X Y : simplicial_complex α)
    (Z : simplicial_complex β)
    (s : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (τ : α → β) (τ_inj : function.injective τ)
  : X ≅ Z → Y ≅ σ(X, s, x; s_ne, s_in_X, x_nin_X) →
      ∃ (W : simplicial_complex β), Y ≅ W ∧ Z ≅ₛₜ W
:= begin
  intros X_iso_Z X_subdiv_Y,
  
  have τ_inj_subdiv : set.inj_on τ (vertices σ(X, s, x; s_ne, s_in_X, x_nin_X)), from
  begin
    apply set.inj_on_of_injective τ_inj,
  end,
  let τσ := simplicial_coe.mk τ τ_inj_subdiv,

  have τ_inj_X : set.inj_on τ (vertices X), from
  begin
    apply set.inj_on_of_injective τ_inj,
  end,
  let τX := simplicial_coe.mk τ τ_inj_X,

  use (τσ[σ(X, s, x; s_ne, s_in_X, x_nin_X)]), split,
  apply simplicial_iso_trans _ σ(X, s, x; s_ne, s_in_X, x_nin_X),
  assumption,
  apply τσ.iso_onto_image,

  have τX_iso_Z : Z ≅ τX[X], from
  begin
    apply simplicial_iso_trans _ X,
    rw [simplicial_iso_symm],
    assumption,
    apply τX.iso_onto_image,
  end,

  apply @relation.refl_trans_gen.tail _ _ _ (τX[X]),
  apply relation.refl_trans_gen.single,
  right, right,
  assumption,

  right, left,
  use (finset.image τX.coe s),

  have τs_in_img : finset.image τX.coe s ∈ (τX[X]).simplices, from
  begin
    apply map_is_simplicial_onto_image X τX.coe,
    assumption,
  end,
  use τs_in_img,

  have τs_ne : nonempty (finset.image τX.coe s), from
  begin
    rw [finset.nonempty_coe_sort] at s_ne ⊢,
    apply finset.nonempty.image s_ne,
  end,
  use τs_ne,

  use (τX.coe x),
  have τx_nin_τX : τX.coe x ∉ vertices (τX[X]), from
  begin
    by_cases τx_in_X : τX.coe x ∈ vertices (τX[X]),

    rw [simplicial_image_vertices] at τx_in_X,
    have contra : x ∈ vertices X, from
    begin
      rw [set.mem_image] at τx_in_X,
      choose y y_in_X τy_eq_τx using τx_in_X,
      rw [function.injective.eq_iff τ_inj] at τy_eq_τx,
      rw [τy_eq_τx] at y_in_X,
      assumption,
    end,
    contradiction,

    assumption,
  end,
  use τx_nin_τX,

  apply stellar_subdiv_injective_image,
  assumption,
end

lemma stellar_move_exists_iso
    [nonempty α]
    (X Y : simplicial_complex α)
    (Z : simplicial_complex β)
    (f : α → β) (f_inj : function.injective f)
  : X ≅ Z → stellar_move X Y →
      ∃ (W : simplicial_complex β),Y ≅ W ∧ Z ≅ₛₜ W
:= begin
  intros X_iso_Z X_move_Y,
  unfold stellar_move at X_move_Y,
  cases X_move_Y with Y_subdiv_X X_move_Y,

  choose t t_in_Y t_ne y y_nin_Y Y_subdiv_X using Y_subdiv_X,
  apply @stellar_weld_exists_iso _ _ _ _ _ X Y Z t t_ne y t_in_Y y_nin_Y X_iso_Z Y_subdiv_X,

  cases X_move_Y with X_subdiv_Y X_iso_Y,
  choose s s_in_X s_ne x x_nin_X X_subdiv_Y using X_subdiv_Y,
  apply @stellar_subdiv_exists_iso _ _ _ _ _ X Y Z s s_ne x s_in_X x_nin_X f f_inj X_iso_Z X_subdiv_Y,

  use Z, split,
  apply simplicial_iso_trans Y X,
  rw [simplicial_iso_symm],
  assumption,
  assumption,
  refl,
end

lemma stellar_equiv_exists_iso
    [nonempty α]
    (X Y : simplicial_complex α)
    (Z : simplicial_complex β)
    (f : α → β) (f_inj : function.injective f)
  : X ≅ Z → X ≅ₛₜ Y →
      ∃ (W : simplicial_complex β), Y ≅ W ∧ Z ≅ₛₜ W
:= begin
  intros X_iso_Z X_eq_Y,
  induction X_eq_Y with K Y X_eq_K K_move_Y H_ind,

  use Z, split,
  assumption,
  apply stellar_equiv_refl,

  choose L K_iso_L Z_eq_L using H_ind,
  have Z_move_W : ∃ (W : simplicial_complex β), Y ≅ W ∧ L ≅ₛₜ W, from
  begin
    apply stellar_move_exists_iso,
    apply f_inj,
    apply K_iso_L,
    apply K_move_Y,
  end,
  choose W Y_iso_W L_move_W using Z_move_W,
  use W, split,
  assumption,

  apply stellar_equiv_trans Z L,
  assumption,
  assumption,
end

lemma stellar_move_iso
    [nonempty α]
    (X Y : simplicial_complex α)
    (Z W : simplicial_complex β)
    (f : α → β) (f_inj : function.injective f)
  : X ≅ Z → Y ≅ W → stellar_move X Y → Z ≅ₛₜ W
:= begin
  intros X_iso_Z Y_iso_W X_move_Y,
  have Y_iso_L : ∃ (L : simplicial_complex β), Y ≅ L ∧ Z ≅ₛₜ L, from
  begin
    apply stellar_move_exists_iso,
    apply f_inj,
    apply X_iso_Z,
    apply X_move_Y,
  end,

  choose L Y_iso_L Z_eq_L using Y_iso_L,
  apply @relation.refl_trans_gen.tail _ _ _ L,
  assumption,

  right, right,
  apply simplicial_iso_trans _ Y,
  rw [simplicial_iso_symm],
  assumption,
  assumption,
end

lemma stellar_equiv_iso
    [nonempty α]
    (X Y : simplicial_complex α)
    (Z W : simplicial_complex β)
    (f : α → β) (f_inj : function.injective f)
  : X ≅ Z → Y ≅ W → X ≅ₛₜ Y → Z ≅ₛₜ W
:= begin
  intros X_iso_Z Y_iso_W X_eq_Y,
  induction X_eq_Y with K Y X_eq_K K_move_Y H_ind,

  rw [simplicial_iso_symm] at X_iso_Z,
  apply stellar_equiv_preserves_iso,
  apply simplicial_iso_trans Z X;
  assumption,

  have K_iso_L : ∃ (L : simplicial_complex β), K ≅ L ∧ Z ≅ₛₜ L, from
  begin
    apply stellar_equiv_exists_iso,
    apply f_inj,
    apply X_iso_Z,
    apply X_eq_K,
  end,
  choose L K_iso_L Z_eq_L using K_iso_L,
  apply stellar_equiv_trans Z L,
  assumption,

  apply stellar_move_iso K Y L W;
  assumption,
end

/-
# Properties of Stellar Subdivision
-/

lemma barycenter_join_left
    {X Y : simplicial_complex α}
    {x : α}
  : x ∉ vertices X → (x, 0) ∉ vertices (X ⋆ Y)
:= begin
  contrapose,
  simp only [not_not, simplicial_join_vertices_mem_left],
  exact set.mem_of_eq_of_mem rfl,
end

lemma stellar_join_distr_join_left
    (X Y : simplicial_complex α)
    (s : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : ((π₁ (barycenter_join_boundary_disjoint_link X s x s_in_X x_nin_X))[(π₁ (barycenter_disjoint_boundary X s x s_in_X x_nin_X))[simplex {x} ⋆ ∂s] ⋆ Lk(X, s) s_in_X] ⋆ Y).simplices
      ⊆ ((π₁ (barycenter_join_boundary_disjoint_link (X ⋆ Y) (s ⊔ₛ ∅) (x, 0) (by { apply simplicial_join_incl_left, assumption, }) (barycenter_join_left x_nin_X)))
          [(π₁ (barycenter_disjoint_boundary (X ⋆ Y) (s ⊔ₛ ∅) (x, 0) (by { apply simplicial_join_incl_left, assumption, }) (barycenter_join_left x_nin_X)))
            [simplex {(x, 0)} ⋆ ∂(s ⊔ₛ ∅)] ⋆ Lk(X ⋆ Y, s ⊔ₛ ∅) (by { apply simplicial_join_incl_left, assumption, })]).simplices
:= begin
  simp only [set.subset_def, simplicial_join_mem, join_proj_mem],
  intros t t_in_join,
  choose u u_in_join v v_in_Y t_eq_uv using t_in_join,
  choose u' u'_in_join u₁ u₁_in_link u_decomp using u_in_join,
  choose u₃ u₃_in_barycenter u₂ u₂_in_bd u'_decomp using u'_in_join,
  subst u'_decomp,
  
  use ((u₃ ⊔ₛ ∅) ∪ (u₂ ⊔ₛ ∅)), split,
  use (u₃ ⊔ₛ ∅), split,
  simp only [simplex, finset.mem_coe, finset.mem_powerset, finset.subset_singleton_iff] at u₃_in_barycenter ⊢,
  cases u₃_in_barycenter with u₃_empty u₃_eq_x,

  left,
  rw [u₃_empty],
  simp only [simplex_disjoint_union, finset.product_singleton, finset.map_empty, finset.empty_union],
  
  right,
  rw [u₃_eq_x],
  simp only [simplex_disjoint_union, finset.product_singleton, finset.map_singleton, function.embedding.coe_fn_mk, finset.map_empty, finset.union_empty],
  
  use (u₂ ⊔ₛ ∅), split,
  rw [simplex_boundary_mem_iff_subset, finset.ssubset_iff_subset_ne] at u₂_in_bd ⊢,
  choose u₂_ss_s u₂_ne_s using u₂_in_bd,
  simp only [ne.def, simplex_disjoint_subset_unique, simplex_disjoint_eq_unique, not_and],
  split, split, assumption, refl,
  intros contra, contradiction,
  refl,
  
  use (u₁ ⊔ₛ v), split,
  simp only [link, set.mem_sep_iff] at u₁_in_link ⊢,
  choose u₁_in_X su₁_in_X su₁_disj using u₁_in_link,
  split,
  
  rw [simplicial_join_mem],
  use u₁, split, assumption,
  use v, split, assumption,
  refl,
  
  split,
  rw [simplex_disjoint_distr_union, finset.empty_union, simplicial_join_mem],
  use (s ∪ u₁), split, assumption,
  use v, split, assumption,
  refl,
  
  rw [simplex_disjoint_distr_inter, finset.empty_inter, su₁_disj],
  simp only [simplex_disjoint_union, finset.product_singleton, finset.map_empty, finset.empty_union],
  
  simp only [simplex_disjoint_distr_union, finset.empty_union, ←u_decomp],
  assumption,
end

lemma stellar_join_distr_join_right
    (X Y : simplicial_complex α)
    (s : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : ((π₁ (barycenter_join_boundary_disjoint_link (X ⋆ Y) (s ⊔ₛ ∅) (x, 0) (by { apply simplicial_join_incl_left, assumption, }) (barycenter_join_left x_nin_X)))
      [(π₁ (barycenter_disjoint_boundary (X ⋆ Y) (s ⊔ₛ ∅) (x, 0) (by { apply simplicial_join_incl_left, assumption, }) (barycenter_join_left x_nin_X)))
        [simplex {(x, 0)} ⋆ ∂(s ⊔ₛ ∅)] ⋆ Lk(X ⋆ Y, s ⊔ₛ ∅) (by { apply simplicial_join_incl_left, assumption, })]).simplices
      ⊆ ((π₁ (barycenter_join_boundary_disjoint_link X s x s_in_X x_nin_X))[(π₁ (barycenter_disjoint_boundary X s x s_in_X x_nin_X))[simplex {x} ⋆ ∂s] ⋆ Lk(X, s) s_in_X] ⋆ Y).simplices
:= begin
  simp only [set.subset_def, simplicial_join_mem, join_proj_mem],
  intros t t_in_img,
  choose t' t'_in_join t₁ t₁_in_link t_decomp using t_in_img,
  choose t₃ t₃_in_barycenter t₂ t₂_in_bd t'_decomp using t'_in_join,
  subst t'_decomp,

  simp only [link, set.mem_sep_iff] at t₁_in_link,
  choose t₁_in_XY st₁_in_XY st₁_disj using t₁_in_link,
  rw [simplicial_join_mem] at t₁_in_XY,
  choose u₁ u₁_in_X v₁ v₁_in_Y t₁_eq_uv₁ using t₁_in_XY,
  subst t₁_eq_uv₁,

  have s_zero : ∀ (a : α × ℕ), a ∈ s ⊔ₛ ∅ → a.snd = 0, from
  begin
    intros a a_in_s,
    rw [simplex_disjoint_mem] at a_in_s,
    cases a_in_s with a_in_s contra,
    choose a_in_s a_zero using a_in_s,
    assumption,

    choose contra a_one using contra,
    have H : a.fst ∉ ∅, by apply finset.not_mem_empty,
    contradiction,
  end,

  rw [simplex_boundary_mem_iff_subset, finset.ssubset_iff] at t₂_in_bd,
  choose a a_nin_t₂ at₂_ss_s using t₂_in_bd,
  
  use (finset.image prod.fst (t₃ ∪ t₂) ∪ u₁), split,
  use (finset.image prod.fst (t₃ ∪ t₂)), split,
  use (finset.image prod.fst t₃), split,
  simp only [simplex, finset.mem_coe, finset.mem_powerset, finset.subset_singleton_iff] at t₃_in_barycenter ⊢,
  cases t₃_in_barycenter with t₃_empty t₃_eq_x,
  
  left,
  rw [t₃_empty],
  apply finset.image_empty,
  
  right,
  simp only [t₃_eq_x, finset.image_singleton, prod.fst],
  
  use (finset.image prod.fst t₂), split,
  rw [simplex_boundary_mem_iff_subset, finset.ssubset_iff],
  use (prod.fst a),

  have a_zero : a.snd = 0, from
  begin
    have a_in_s : a ∈ s ⊔ₛ ∅, from
    begin
      apply finset.mem_of_subset at₂_ss_s,
      apply finset.mem_insert_self,
    end,
    specialize s_zero a a_in_s,
    assumption,
  end,
  
  split,
  simp only [finset.mem_image, exists_prop, prod.exists, exists_and_distrib_right, exists_eq_right, not_exists],
  intros n,

  by_cases n_zero : n = 0,
  rw [n_zero, ←a_zero, prod.mk.eta],
  assumption,
  
  have a_nin_s : (a.fst, n) ∉ s ⊔ₛ ∅, from
  begin
    revert n_zero,
    contrapose,
    simp only [not_not],
    specialize s_zero (a.fst, n),
    assumption,
  end,
  
  revert a_nin_s,
  contrapose,
  simp only [not_not],
  intros a_in_t₂,
  apply @finset.mem_of_subset _ t₂,
  apply @finset.subset.trans _ _ (insert a t₂),
  apply finset.subset_insert,
  assumption,
  assumption,
  
  rw [finset.subset_iff] at at₂_ss_s ⊢,
  intros b b_in_at₂,
  rw [finset.mem_insert] at b_in_at₂,
  cases b_in_at₂ with b_eq_a b_in_t₂,

  subst b_eq_a,
  specialize at₂_ss_s (finset.mem_insert_self a t₂),
  rw [←@prod.mk.eta _ _ a, a_zero, simplex_disjoint_mem_left] at at₂_ss_s,
  assumption,
  
  rw [finset.mem_image] at b_in_t₂,
  choose c c_in_t₂ proj_c_b using b_in_t₂,
  
  have c_in_s : c ∈ s ⊔ₛ ∅, from
  begin
    apply finset.mem_of_subset at₂_ss_s,
    rw [finset.mem_insert],
    right, assumption,
  end,
  specialize s_zero c c_in_s,
  rw [←@prod.mk.eta _ _ c, s_zero, simplex_disjoint_mem_left, proj_c_b] at c_in_s,
  assumption,
  
  rw [finset.image_union],
  
  use u₁, split,
  simp only [link, set.mem_sep_iff],
  split, assumption,
  
  split,
  rw [simplex_disjoint_distr_union, simplicial_join_sep] at st₁_in_XY,
  choose su₁_in_X sv₁_in_Y using st₁_in_XY,
  assumption,
  
  rw [simplex_disjoint_distr_inter, simplex_disjoint_empty] at st₁_disj,
  choose su₁_disj sv₁_disj using st₁_disj,
  assumption,
  refl,
  
  use v₁, split, assumption,
  rw [←finset.empty_union v₁, ←finset.empty_union ∅, ←simplex_disjoint_distr_union, finset.image_union, ←simplex_disjoint_distr_union],
  
  have t₂_lift : finset.image prod.fst t₂ ⊔ₛ ∅ = t₂, from
  begin
    simp only [finset.ext_iff, simplex_disjoint_mem, finset.mem_image],
    intros b,
    split,

    intros b_in_img,
    cases b_in_img with b_in_t₂ contra,
    choose proj_c_b b_zero using b_in_t₂,
    choose c c_in_t₂ proj_c_b using proj_c_b,
    have c_in_s : c ∈ s ⊔ₛ ∅, from
    begin
      apply finset.mem_of_subset at₂_ss_s,
      rw [finset.mem_insert],
      right, assumption,
    end,
    specialize s_zero c c_in_s,
    rw [←@prod.mk.eta _ _ c, s_zero, proj_c_b, ←b_zero, prod.mk.eta] at c_in_t₂,
    assumption,

    choose contra b_one using contra,
    have H : b.fst ∉ ∅, by apply finset.not_mem_empty,
    contradiction,

    intros b_in_t₂,
    left,
    use b, split, assumption,
    refl,

    have b_in_s : b ∈ s ⊔ₛ ∅, from
    begin
      apply finset.mem_of_subset at₂_ss_s,
      rw [finset.mem_insert],
      right, assumption,
    end,
    specialize s_zero b b_in_s,
    assumption,
  end,
  
  have t₃_lift : finset.image prod.fst t₃ ⊔ₛ ∅ = t₃, from
  begin
    simp only [simplex, finset.mem_coe, finset.mem_powerset, finset.subset_singleton_iff] at t₃_in_barycenter,
    cases t₃_in_barycenter with t₃_empty t₃_eq_x,

    rw [t₃_empty, finset.image_empty, simplex_disjoint_empty],
    split; refl,

    rw [t₃_eq_x],
    simp only [simplex_disjoint_union, finset.image_singleton, finset.product_singleton, finset.map_singleton, function.embedding.coe_fn_mk, finset.map_empty, finset.union_empty],
  end,
  
  rw [t₂_lift, t₃_lift],
  assumption,
end

lemma stellar_join_distr_join
    (X Y : simplicial_complex α)
    (s : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : ((π₁ (barycenter_join_boundary_disjoint_link X s x s_in_X x_nin_X))[(π₁ (barycenter_disjoint_boundary X s x s_in_X x_nin_X))[simplex {x} ⋆ ∂s] ⋆ Lk(X, s) s_in_X] ⋆ Y).simplices
      = ((π₁ (barycenter_join_boundary_disjoint_link (X ⋆ Y) (s ⊔ₛ ∅) (x, 0) (by { apply simplicial_join_incl_left, assumption, }) (barycenter_join_left x_nin_X)))
          [(π₁ (barycenter_disjoint_boundary (X ⋆ Y) (s ⊔ₛ ∅) (x, 0) (by { apply simplicial_join_incl_left, assumption, }) (barycenter_join_left x_nin_X)))
            [simplex {(x, 0)} ⋆ ∂(s ⊔ₛ ∅)] ⋆ Lk(X ⋆ Y, s ⊔ₛ ∅) (by { apply simplicial_join_incl_left, assumption, })]).simplices
:= begin
  rw [set.subset.antisymm_iff],
  split,

  apply stellar_join_distr_join_left,
  apply stellar_join_distr_join_right,
end

lemma stellar_subdiv_distr_join_left
    (X Y : simplicial_complex α)
    (s : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : σ(X, s, x; s_ne, s_in_X, x_nin_X) ⋆ Y
      ≅ σ((X ⋆ Y), (s ⊔ₛ ∅), (x, 0);
          _,
          (by { apply simplicial_join_incl_left, assumption, }),
          (barycenter_join_left x_nin_X))
:= begin
  apply simplicial_iso_trans
    (σ(X, s, x; s_ne, s_in_X, x_nin_X) ⋆ Y)
    (((X\St(X, s) s_in_X) ⋆ Y) ∪ ((π₁ _)[(π₁ _)[simplex {x} ⋆ ∂s] ⋆ Lk(X, s) _] ⋆ Y)),
  apply simplicial_iso_preserves_equiv,
  apply simplicial_join_distr_union_right,

  apply simplicial_iso_preserves_equiv,
  simp only [stellar_subdivision, simplicial_union],
  rw [join_distr_star_complement_simplices, stellar_join_distr_join],
end

lemma barycenter_join_right
    {X Y : simplicial_complex α}
    {x : α}
  : x ∉ vertices Y → (x, 1) ∉ vertices (X ⋆ Y)
:= begin
  contrapose,
  simp only [not_not, simplicial_join_vertices_mem_right],
  exact set.mem_of_eq_of_mem rfl,
end

lemma stellar_subdiv_distr_join_right
    (X Y : simplicial_complex α)
    (t : finset α) [t_ne : nonempty t]
    (y : α)
    (t_in_Y : t ∈ Y.simplices)
    (y_nin_Y : y ∉ vertices Y)
  : X ⋆ σ(Y, t, y; t_ne, t_in_Y, y_nin_Y)
      ≅ σ((X ⋆ Y), (∅ ⊔ₛ t), (y, 1);
          _,
          (by { apply simplicial_join_incl_right, assumption, }),
          (barycenter_join_right y_nin_Y))
:= begin
  apply simplicial_iso_trans
    (X ⋆ σ(Y, t, y; t_ne, t_in_Y, y_nin_Y))
    (σ(Y, t, y; t_ne, t_in_Y, y_nin_Y) ⋆ X),
  apply simplicial_join_comm,

  apply simplicial_iso_trans
    (σ(Y, t, y; t_ne, t_in_Y, y_nin_Y) ⋆ X)
    (σ((Y ⋆ X), (t ⊔ₛ ∅), (y, 0);
      _,
      (by { apply simplicial_join_incl_left, assumption, }),
      (barycenter_join_left y_nin_Y))),
  apply stellar_subdiv_distr_join_left;
  assumption,

  let f : simplicial_map (Y ⋆ X) (X ⋆ Y) :=
    simplicial_map.mk (simplicial_join_comm_map) (simplicial_join_comm_simplicial Y X),
  let g : simplicial_map (X ⋆ Y) (Y ⋆ X) :=
    simplicial_map.mk (simplicial_join_comm_map) (simplicial_join_comm_simplicial X Y),

  have gf_inv : is_inverse_simplicial_iso f g, from
  begin
    unfold is_inverse_simplicial_iso,
    split;

    { simp only [set.restrict_eq_restrict_iff, set.eq_on],
      intros x x_in_XY,
      rw [simplicial_join_mem_vertices] at x_in_XY,
      simp only [f, g, simplicial_map.comp, simplicial_join_comm_map, id.def, function.comp_app],
      cases x_in_XY with x_in_X x_in_Y,
      
      choose x_in_X x_zero using x_in_X,
      simp only [x_zero, eq_self_iff_true, if_true, nat.one_ne_zero, if_false],
      simp only [←x_zero, prod.ext_iff, prod.fst, prod.snd],
      split; refl,
      
      choose x_in_Y x_one using x_in_Y,
      simp only [x_one, eq_self_iff_true, if_true, nat.one_ne_zero, if_false],
      simp only [←x_one, prod.ext_iff, prod.fst, prod.snd],
      split; refl, },
  end,

  have f_iso : is_simplicial_iso f, from
  begin
    unfold is_simplicial_iso,
    use g,
    apply gf_inv,
  end,

  apply stellar_subdiv_iso,
  apply f_iso,
  apply gf_inv,
  
  simp only [finset.ext_iff, finset.mem_image, simplex_disjoint_mem],
  intros a,
  split,

  { intros a_in_img,
    choose b b_in_disj fb_a using a_in_img,
    cases b_in_disj with b_in_t contra,
    
    choose b_in_t b_zero using b_in_t,
    simp only [simplicial_join_comm_map, b_zero, eq_self_iff_true, if_true, prod.ext_iff] at fb_a,
    choose b_eq_a a_one using fb_a,
    rw [@comm _ eq] at a_one,
    rw [b_eq_a] at b_in_t,
    right, split; assumption,
    
    choose contra b_one using contra,
    have H : b.fst ∉ ∅, by apply finset.not_mem_empty,
    contradiction, },

  { intros a_in_disj,
    cases a_in_disj with contra a_in_t,
    choose contra a_zero using contra,
    have H : a.fst ∉ ∅, by apply finset.not_mem_empty,
    contradiction,
    
    choose a_in_t a_one using a_in_t,
    use (a.fst, 0), split,
    simp only [prod.fst, prod.snd],
    left, split,
    assumption,
    refl,
    
    simp only [simplicial_join_comm_map, eq_self_iff_true, if_true, ←a_one, prod.ext_iff, true_and], },

  simp only [simplicial_join_comm_map, eq_self_iff_true, if_true],
  simp only [simplicial_join_comm_map, nat.one_ne_zero, if_false],
end

-- Lemma 3.1, p.10
lemma simplicial_join_stellar_equiv
    (X Y Z W : simplicial_complex α)
  : X ≅ₛₜ Y → Z ≅ₛₜ W → X ⋆ Z ≅ₛₜ Y ⋆ W
:= begin
  intros X_eq_Y Z_eq_W,
  transitivity (Y ⋆ Z),

  unfold stellar_equiv at *,
  induction X_eq_Y with K L X_eq_K K_move_L H_ind,
  refl,

  apply @relation.refl_trans_gen.tail _ _ _ (K ⋆ Z) (L ⋆ Z),
  apply H_ind,

  simp only[stellar_move] at K_move_L ⊢,
  cases K_move_L,

  left,
  choose t Ht Ht_ne y Hy K_subdiv_L using K_move_L,
  
  use (t ⊔ₛ ∅),
  have Ht_empty : (t ⊔ₛ ∅) ∈ (L ⋆ Z).simplices, from
  begin
    rw [simplicial_join_sep],
    split,
    assumption,
    apply simplicial_complex_empty_simplex,
  end,
  use Ht_empty,

  let Ht_empty_ne := @simplex_disjoint.nonempty.left _ _ t Ht_ne,
  use Ht_empty_ne,

  use (y, 0),
  have Hy_0 : (y, 0) ∉ vertices (L ⋆ Z), from
  begin
    rw [simplicial_join_vertices_mem_left],
    assumption,
  end,
  use Hy_0,

  rw [simplicial_iso_symm],
  apply simplicial_iso_trans
    (@stellar_subdivision _ _ (L ⋆ Z) (t ⊔ₛ ∅) Ht_empty_ne (y, 0) Ht_empty Hy_0)
    ((@stellar_subdivision _ _ L t Ht_ne y Ht Hy) ⋆ Z),
  rw [simplicial_iso_symm],
  apply @stellar_subdiv_distr_join_left _ _ _ _ _ Ht_ne;
  assumption,

  apply simplicial_join_iso_left,
  rw [simplicial_iso_symm],
  assumption,

  cases K_move_L,
  right, left,
  choose s Hs Hs_ne x Hx L_subdiv_K using K_move_L,

  use (s ⊔ₛ ∅),
  have Hs_empty : (s ⊔ₛ ∅) ∈ (K ⋆ Z).simplices, from
  begin
    rw [simplicial_join_sep],
    split,
    assumption,
    apply simplicial_complex_empty_simplex,
  end,
  use Hs_empty,

  let Hs_empty_ne := @simplex_disjoint.nonempty.left _ _ s Hs_ne,
  use Hs_empty_ne,

  use (x, 0),
  have Hx_0 : (x, 0) ∉ vertices (K ⋆ Z), from
  begin
    rw [simplicial_join_vertices_mem_left],
    assumption,
  end,
  use Hx_0,

  rw [simplicial_iso_symm],
  apply simplicial_iso_trans
    (@stellar_subdivision _ _ (K ⋆ Z) (s ⊔ₛ ∅) Hs_empty_ne (x, 0) Hs_empty Hx_0)
    ((@stellar_subdivision _ _ K s Hs_ne x Hs Hx) ⋆ Z),
  rw [simplicial_iso_symm],
  apply @stellar_subdiv_distr_join_left _ _ _ _ _ Hs_ne;
  assumption,

  apply simplicial_join_iso_left,
  rw [simplicial_iso_symm],
  assumption,

  right, right,
  apply simplicial_join_iso_left,
  assumption,

  unfold stellar_equiv at *,
  induction Z_eq_W with K L Z_eq_K K_move_L H_ind,
  refl,

  apply @relation.refl_trans_gen.tail _ _ _ (Y ⋆ K) (Y ⋆ L),
  apply H_ind,

  simp only[stellar_move] at K_move_L ⊢,
  cases K_move_L,

  left,
  choose t Ht Ht_ne y Hy K_subdiv_L using K_move_L,

  use (∅ ⊔ₛ t),
  have Ht_empty : (∅ ⊔ₛ t) ∈ (Y ⋆ L).simplices, from
  begin
    rw [simplicial_join_sep],
    split,
    apply simplicial_complex_empty_simplex,
    assumption,
  end,
  use Ht_empty,

  let Ht_empty_ne := @simplex_disjoint.nonempty.right _ _ t Ht_ne,
  use Ht_empty_ne,

  use (y, 1),
  have Hy_1 : (y, 1) ∉ vertices (Y ⋆ L), from
  begin
    rw [simplicial_join_vertices_mem_right],
    assumption,
  end,
  use Hy_1,

  rw [simplicial_iso_symm],
  apply simplicial_iso_trans
    (@stellar_subdivision _ _ (Y ⋆ L) (∅ ⊔ₛ t) Ht_empty_ne (y, 1) Ht_empty Hy_1)
    (Y ⋆ @stellar_subdivision _ _ L t Ht_ne y Ht Hy),
  rw [simplicial_iso_symm],
  apply @stellar_subdiv_distr_join_right _ _ _ _ _ Ht_ne;
  assumption,

  apply simplicial_join_iso_right,
  rw [simplicial_iso_symm],
  assumption,

  cases K_move_L,
  right, left,
  choose s Hs Hs_ne x Hx L_subdiv_K using K_move_L,

  use (∅ ⊔ₛ s),
  have Hs_empty : (∅ ⊔ₛ s) ∈ (Y ⋆ K).simplices, from
  begin
    rw [simplicial_join_sep],
    split,
    apply simplicial_complex_empty_simplex,
    assumption,
  end,
  use Hs_empty,

  let Hs_empty_ne := @simplex_disjoint.nonempty.right _ _ s Hs_ne,
  use Hs_empty_ne,

  use (x, 1),
  have Hx_1 : (x, 1) ∉ vertices (Y ⋆ K), from
  begin
    rw [simplicial_join_vertices_mem_right],
    assumption,
  end,
  use Hx_1,

  rw [simplicial_iso_symm],
  apply simplicial_iso_trans
    (@stellar_subdivision _ _ (Y ⋆ K) (∅ ⊔ₛ s) Hs_empty_ne (x, 1) Hs_empty Hx_1)
    (Y ⋆ @stellar_subdivision _ _ K s Hs_ne x Hs Hx),
  rw [simplicial_iso_symm],
  apply @stellar_subdiv_distr_join_right _ _ _ _ _ Hs_ne;
  assumption,

  apply simplicial_join_iso_right,
  rw [simplicial_iso_symm],
  assumption,

  right, right,
  apply simplicial_join_iso_right,
  assumption,
end

lemma simplicial_join_stellar_equiv_left
    (X Y Z : simplicial_complex α)
  : X ≅ₛₜ Y → X ⋆ Z ≅ₛₜ Y ⋆ Z
:= begin
  intros X_eq_Y,
  apply simplicial_join_stellar_equiv X Y Z Z,
  assumption,
  refl,
end

lemma simplicial_join_stellar_equiv_right
    (X Y Z : simplicial_complex α)
  : X ≅ₛₜ Y → Z ⋆ X ≅ₛₜ Z ⋆ Y
:= begin
  intros X_eq_Y,
  apply simplicial_join_stellar_equiv Z Z X Y,
  refl,
  assumption,
end

lemma stellar_subdiv_link_of_star_complement_left
    (X : simplicial_complex α)
    (s t : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (t_in_star_comp : t ∈ (X\St(X, s) s_in_X).simplices)
  : t ∉ ((π₁ (boundary_disjoint_link X s s_in_X))[Lk(X, s) s_in_X ⋆ ∂s]).simplices →
      (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), t) (by { simp only [stellar_subdivision, simplicial_union, set.mem_union], left, assumption, })).simplices
        ⊆ (Lk(X, t) (by { simp only [star_complement, set.mem_sep_iff] at t_in_star_comp, choose t_in_X H using t_in_star_comp, assumption, })).simplices
:= begin
  intros t_nin_join,
  simp only [star_complement, set.mem_sep_iff] at t_in_star_comp,
  choose t_in_X s_nss_t using t_in_star_comp,

  simp only [set.subset_def, link, stellar_subdivision, simplicial_union, star_complement, set.mem_union, set.mem_sep_iff],
  intros u u_in_link,
  choose u_in_subdiv ut_in_subdiv ut_disj using u_in_link,
  cases ut_in_subdiv with ut_in_star_comp ut_in_join, -- Cases A, B resp.
  cases u_in_subdiv with u_in_star_comp u_in_join,    -- Cases C, D resp.

  -- Case A + C.
  { choose u_in_X s_nss_u using u_in_star_comp,
    choose ut_in_X s_nss_tu using ut_in_star_comp,
    split, assumption,
    split; assumption, },

  -- Case A + D.
  { choose tu_in_X s_nss_tu using ut_in_star_comp,
    split,
    
    apply X.subset_closed (t ∪ u),
    assumption,
    apply finset.subset_union_right,
    
    split; assumption, },

  -- Case B + (C/D).
  { rw [join_proj_disj_union_mem] at ut_in_join,
    choose t' t'_in_join u' u'_in_join t₁ t₁_in_link u₁ u₁_in_link t_decomp u_decomp tu'_in_join tu₁_in_link using ut_in_join,
    rw [join_proj_disj_union_mem] at tu'_in_join,
    choose t₃ t₃_in_barycenter u₃ u₃_in_barycenter t₂ t₂_in_bd u₂ u₂_in_bd t'_decomp u'_decomp tu₃_in_barycenter tu₂_in_bd using tu'_in_join,
    subst t'_decomp,
    subst u'_decomp,
    
    simp only [simplex, finset.mem_coe, finset.mem_powerset, finset.subset_singleton_iff] at t₃_in_barycenter,
    cases t₃_in_barycenter with t₃_empty contra,
    rotate,
    have x_in_X : x ∈ vertices X, from
    begin
      subst contra,
      rw [t_decomp] at t_in_X,
      rw [vertex_iff_singleton],
      apply X.subset_closed ({x} ∪ t₂ ∪ t₁),
      assumption,
      rw [finset.union_assoc],
      apply finset.subset_union_left,
    end,
    contradiction,
    
    subst t₃_empty,
    rw [finset.empty_union] at t_decomp,
    have contra : t ∈ ((π₁ (boundary_disjoint_link X s s_in_X))[Lk(X, s) s_in_X ⋆ ∂s]).simplices, from
    begin
      rw [join_proj_mem],
      use t₁, split, assumption,
      use t₂, split, assumption,
      rw [finset.union_comm],
      assumption,
    end,
    contradiction, },
end

lemma stellar_subdiv_link_of_star_complement_right
    (X : simplicial_complex α)
    (s t : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (t_in_star_comp : t ∈ (X\St(X, s) s_in_X).simplices)
  : t ∉ ((π₁ (boundary_disjoint_link X s s_in_X))[Lk(X, s) s_in_X ⋆ ∂s]).simplices →
      (Lk(X, t) (by { simp only [star_complement, set.mem_sep_iff] at t_in_star_comp, choose t_in_X H using t_in_star_comp, assumption, })).simplices
        ⊆ (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), t) (by { simp only [stellar_subdivision, simplicial_union, set.mem_union], left, assumption, })).simplices
:= begin
  intros t_nin_join,
  simp only [star_complement, set.mem_sep_iff] at t_in_star_comp,
  choose t_in_X s_nss_t using t_in_star_comp,

  simp only [set.subset_def, link, stellar_subdivision, simplicial_union, star_complement, set.mem_union, set.mem_sep_iff],
  intros u u_in_link,
  choose u_in_X tu_in_X tu_disj using u_in_link,

  by_cases s_ss_u : s ⊆ u,

  { have t_in_link : t ∈ (Lk(X, s) s_in_X).simplices, from
    begin
      simp only [link, set.mem_sep_iff],
      split, assumption,

      split,
      apply X.subset_closed (t ∪ u),
      assumption,
      rw [finset.union_comm],
      apply finset.union_subset_union_right,
      assumption,

      rw [←finset.subset_empty],
      apply @finset.subset.trans _ _ (t ∩ u),
      rw [finset.inter_comm],
      apply finset.inter_subset_inter_left,
      assumption,
      rw [finset.subset_empty],
      assumption,
    end,
    
    simp only [join_proj_mem, not_exists] at t_nin_join,
    specialize t_nin_join t t_in_link,
    specialize t_nin_join ∅ (simplicial_complex_empty_simplex ∂s),
    rw [finset.union_empty] at t_nin_join,
    contradiction, },

  split,
  left, split; assumption,

  split,
  left, split, assumption,
  revert t_nin_join,
  contrapose,
  simp only [not_not],
  intros s_ss_tu,

  rw [join_proj_mem],
  use (t \ s), split,
  simp only [link, set.mem_sep_iff],

  split,
  apply X.subset_closed t,
  assumption,
  apply finset.sdiff_subset,

  split,
  rw [finset.union_sdiff_self_eq_union],
  apply X.subset_closed (t ∪ u),
  assumption,
  apply @finset.subset.trans _ _ (s ∪ (t ∪ u)),
  rw [←finset.union_assoc],
  apply finset.subset_union_left,
  rw [←finset.union_eq_right_iff_subset] at s_ss_tu,
  apply finset.subset_of_eq,
  assumption,

  rw [finset.inter_comm],
  apply finset.sdiff_inter_self,

  use (t ∩ s), split,
  rw [simplex_boundary_mem_iff_subset, finset.ssubset_iff_subset_ne],
  split,
  apply finset.inter_subset_right,
  rw [ne.def, finset.inter_eq_right_iff_subset],
  assumption,

  rw [finset.sdiff_union_inter],
  assumption,
end

lemma stellar_subdiv_link_of_star_complement
    (X : simplicial_complex α)
    (s t : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (t_in_star_comp : t ∈ (X\St(X, s) s_in_X).simplices)
  : t ∉ ((π₁ (boundary_disjoint_link X s s_in_X))[Lk(X, s) s_in_X ⋆ ∂s]).simplices →
      (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), t) (by { simp only [stellar_subdivision, simplicial_union, set.mem_union], left, assumption, })).simplices
        = (Lk(X, t) (by { simp only [star_complement, set.mem_sep_iff] at t_in_star_comp, choose t_in_X H using t_in_star_comp, assumption, })).simplices
:= begin
  intros t_nin_join,
  rw [set.subset.antisymm_iff],
  split,

  apply stellar_subdiv_link_of_star_complement_left,
  assumption,

  apply stellar_subdiv_link_of_star_complement_right,
  assumption,
end

lemma stellar_subdiv_link_of_barycenter_left
    (X : simplicial_complex α)
    (s : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), {x}) (by { rw [←vertex_iff_singleton], apply barycenter_vertex_stellar_subdiv, })).simplices
      ⊆ ((π₁ (boundary_disjoint_link X s s_in_X))[Lk(X, s) s_in_X ⋆ ∂s]).simplices
:= begin
  rw [set.subset_def],
  intros a a_in_link,
  simp only [link, set.mem_sep_iff] at a_in_link,
  choose a_in_subdiv xa_in_subdiv xa_disj using a_in_link,
  simp only [stellar_subdivision, simplicial_union, set.mem_union] at xa_in_subdiv,
  cases xa_in_subdiv with xa_in_star_comp xa_in_join,

  simp only [star_complement, set.mem_sep_iff] at xa_in_star_comp,
  choose xa_in_X s_nss_xa using xa_in_star_comp,
  have contra : x ∈ vertices X, from
  begin
    rw [vertex_iff_singleton],
    apply X.subset_closed ({x} ∪ a),
    assumption,
    apply finset.subset_union_left,
  end,
  contradiction,

  rw [join_proj_disj_union_mem] at xa_in_join,
  choose x' x'_in_join a' a'_in_join x₁ x₁_in_link a₁ a₁_in_link x_decomp a_decomp xa'_in_join xa₁_in_link using xa_in_join,
  rw [join_proj_disj_union_mem] at xa'_in_join,
  choose x₃ x₃_in_barycenter a₃ a₃_in_barycenter x₂ x₂_in_bd a₂ a₂_in_bd x'_decomp a'_decomp xa₃_in_barycenter xa₂_in_bd using xa'_in_join,
  subst x'_decomp,
  subst a'_decomp,

  have x₁_empty : x₁ = ∅, from
  begin
    have x₁_ss_x : x₁ ⊆ {x}, from
    begin
      rw [x_decomp],
      apply finset.subset_union_right,
    end,
    rw [finset.subset_singleton_iff] at x₁_ss_x,
    cases x₁_ss_x with x₁_empty x₁_eq_x,
    assumption,

    have contra : x ∈ vertices X, from
    begin
      simp only [x₁_eq_x, link, set.mem_sep_iff] at x₁_in_link,
      choose x_in_X sx_in_X sx_disj using x₁_in_link,
      rw [vertex_iff_singleton],
      assumption,
    end,
    contradiction,
  end,

  have x₂_empty : x₂ = ∅, from
  begin
    have x₂_ss_x : x₂ ⊆ {x}, from
    begin
      rw [x_decomp, finset.union_comm, ←finset.union_assoc],
      apply finset.subset_union_right,
    end,
    rw [finset.subset_singleton_iff] at x₂_ss_x,
    cases x₂_ss_x with x₂_empty x₂_eq_x,
    assumption,

    have contra : x ∈ vertices X, from
    begin
      rw [x₂_eq_x] at x₂_in_bd,
      rw [vertex_iff_singleton],
      apply simplex_if_in_subcomplex,
      apply x₂_in_bd,
      apply simplex_boundary_subcomplex,
      assumption,
    end,
    contradiction,
  end,

  subst x₁_empty,
  subst x₂_empty,
  simp only [finset.union_empty] at x_decomp,
  subst x_decomp,

  have a₃_empty : a₃ = ∅, from
  begin
    simp only [simplex, finset.mem_coe, finset.mem_powerset, finset.subset_singleton_iff] at xa₃_in_barycenter,
    cases xa₃_in_barycenter with xa₃_empty xa₃_eq_x,
    rw [finset.union_eq_empty_iff] at xa₃_empty,
    choose x_empty a₃_empty using xa₃_empty,
    have contra : {(x : α)} ≠ (∅ : finset α), by exact finset.singleton_ne_empty x,
    contradiction,

    have xa₃_disj : {x} ∩ a₃ = ∅, from
    begin
      rw [←finset.subset_empty],
      apply @finset.subset.trans _ _ ({x} ∩ a),
      rw [a_decomp, finset.union_assoc],
      apply finset.inter_subset_inter_left,
      apply finset.subset_union_left,
      rw [finset.subset_empty],
      assumption,
    end,
    rw [singleton_inter_eq_empty_iff_not_mem] at xa₃_disj,
    
    rw [finset.union_eq_left_iff_subset, finset.subset_singleton_iff] at xa₃_eq_x,
    cases xa₃_eq_x with a₃_empty a₃_eq_x,
    assumption,

    have contra : x ∈ a₃, from
    begin
      rw [a₃_eq_x],
      apply finset.mem_singleton_self,
    end,
    contradiction,
  end,
  subst a₃_empty,
  rw [finset.empty_union] at a_decomp,

  rw [join_proj_mem],
  use a₁, split, assumption,
  use a₂, split, assumption,
  rw [finset.union_comm],
  assumption,
end

lemma stellar_subdiv_link_of_barycenter_right
    (X : simplicial_complex α)
    (s : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : ((π₁ (boundary_disjoint_link X s s_in_X))[Lk(X, s) s_in_X ⋆ ∂s]).simplices
      ⊆ (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), {x}) (by { rw [←vertex_iff_singleton], apply barycenter_vertex_stellar_subdiv, })).simplices
:= begin
  rw [set.subset_def],
  intros a a_in_img,
  rw [join_proj_mem] at a_in_img,
  choose a₁ a₁_in_link a₂ a₂_in_bd a_decomp using a_in_img,

  simp only [link, set.mem_sep_iff, stellar_subdivision, simplicial_union, set.mem_union],
  
  split, right,
  simp only [join_proj_mem],
  use (∅ ∪ a₂), split,
  use ∅, split, apply simplicial_complex_empty_simplex,
  use a₂, split, assumption,
  refl,

  use a₁, split, assumption,
  rw [finset.empty_union, finset.union_comm],
  assumption,

  split, right,
  simp only [join_proj_mem],
  use ({x} ∪ a₂), split,

  use {x}, split,
  simp only [simplex, finset.mem_coe],
  apply finset.mem_powerset_self,

  use a₂, split, assumption,
  refl,

  use a₁, split, assumption,
  rw [a_decomp, finset.union_comm a₁ a₂, ←finset.union_assoc],

  rw [singleton_inter_eq_empty_iff_not_mem, a_decomp],
  by_contradiction x_in_a,
  rw [finset.mem_union] at x_in_a,
  
  have contra : x ∈ vertices X, from
  begin
    rw [vertex_iff_in_simplex],
    cases x_in_a with x_in_a₁ x_in_a₂,

    use a₁, split,
    apply simplex_if_in_subcomplex,
    apply a₁_in_link,
    apply link_subcomplex,
    assumption,

    use a₂, split,
    apply simplex_if_in_subcomplex,
    apply a₂_in_bd,
    apply simplex_boundary_subcomplex,
    assumption,
    assumption,
  end,
  contradiction,
end

lemma stellar_subdiv_link_of_barycenter
    (X : simplicial_complex α)
    (s : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), {x}) (by { rw [←vertex_iff_singleton], apply barycenter_vertex_stellar_subdiv, })).simplices
      = ((π₁ (boundary_disjoint_link X s s_in_X))[Lk(X, s) s_in_X ⋆ ∂s]).simplices
:= begin
  rw [set.subset.antisymm_iff],
  split,

  apply stellar_subdiv_link_of_barycenter_left,
  apply stellar_subdiv_link_of_barycenter_right,
end

lemma star_boundary_is_join_left
    (X : simplicial_complex α)
    (s : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : ((X\St(X, s) s_in_X) ∩ (π₁ (barycenter_join_boundary_disjoint_link X s x s_in_X x_nin_X))[((π₁ (barycenter_disjoint_boundary X s x s_in_X x_nin_X))[(simplex {x} ⋆ ∂s)] ⋆ Lk(X, s) s_in_X)]).simplices
      ⊆ ((π₁ (boundary_disjoint_link X s s_in_X))[Lk(X, s) s_in_X ⋆ ∂s]).simplices
:= begin
  rw [set.subset_def],
  intros t t_in_inter,
  simp only [simplicial_inter, set.mem_inter_iff] at t_in_inter,
  choose t_in_star_comp t_in_join using t_in_inter,

  simp only [join_proj_mem] at t_in_join,
  choose t' t'_in_join t₁ t₁_in_link t_decomp using t_in_join,
  choose t₃ t₃_in_barycenter t₂ t₂_in_bd t'_decomp using t'_in_join,
  subst t'_decomp,

  simp only [star_complement, set.mem_sep_iff] at t_in_star_comp,
  choose t_in_X s_nss_t using t_in_star_comp,

  have t₃_empty : t₃ = ∅, from
  begin
    simp only [simplex, finset.mem_coe, finset.mem_powerset, finset.subset_singleton_iff] at t₃_in_barycenter,
    cases t₃_in_barycenter with t₃_empty t₃_eq_x,
    assumption,

    have contra : x ∈ vertices X, from
    begin
      rw [vertex_iff_singleton],
      apply X.subset_closed t,
      assumption,
      rw [←t₃_eq_x, t_decomp, finset.union_assoc],
      apply finset.subset_union_left,
    end,
    contradiction,
  end,
  subst t₃_empty,
  rw [finset.empty_union] at t_decomp,

  rw [join_proj_mem],
  use t₁, split, assumption,
  use t₂, split, assumption,
  rw [finset.union_comm],
  assumption,
end

lemma star_boundary_is_join_right
    (X : simplicial_complex α)
    (s : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : ((π₁ (boundary_disjoint_link X s s_in_X))[Lk(X, s) s_in_X ⋆ ∂s]).simplices
      ⊆ ((X\St(X, s) s_in_X) ∩ (π₁ (barycenter_join_boundary_disjoint_link X s x s_in_X x_nin_X))[((π₁ (barycenter_disjoint_boundary X s x s_in_X x_nin_X))[(simplex {x} ⋆ ∂s)] ⋆ Lk(X, s) s_in_X)]).simplices
:= begin
  rw [set.subset_def],
  intros t t_in_join,
  rw [join_proj_mem] at t_in_join,
  choose t₁ t₁_in_link t₂ t₂_in_bd t_decomp using t_in_join,

  simp only [simplicial_inter, set.mem_inter_iff],
  split,

  simp only [star_complement, set.mem_sep_iff],
  simp only [link, set.mem_sep_iff] at t₁_in_link,
  choose t₁_in_X st₁_in_X st₁_disj using t₁_in_link,
  rw [simplex_boundary_mem_iff_subset] at t₂_in_bd,

  split,
  rw [finset.ssubset_iff_subset_ne] at t₂_in_bd,
  choose t₂_ss_s t₂_ne_s using t₂_in_bd,
  apply X.subset_closed (s ∪ t₁),
  assumption,
  rw [t_decomp, finset.union_comm],
  apply finset.union_subset_union_left,
  assumption,

  simp only [finset.subset_iff, not_forall, not_imp],
  rw [finset.ssubset_iff] at t₂_in_bd,
  choose a a_nin_t₂ at₂_ss_s using t₂_in_bd,
  rw [finset.subset_iff] at at₂_ss_s,
  specialize at₂_ss_s (by exact finset.mem_insert_self a t₂),

  use a, split, assumption,
  simp only [finset.eq_empty_iff_forall_not_mem, finset.mem_inter, not_and] at st₁_disj,
  specialize st₁_disj a at₂_ss_s,
  simp only [t_decomp, finset.mem_union, not_or_distrib],
  split; assumption,

  simp only [join_proj_mem],
  use (∅ ∪ t₂), split,
  use ∅, split, apply simplicial_complex_empty_simplex,
  use t₂, split, assumption,
  refl,

  use t₁, split, assumption,
  rw [finset.empty_union, finset.union_comm, t_decomp],
end

lemma star_boundary_is_join
    (X : simplicial_complex α)
    (s : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : ((X\St(X, s) s_in_X) ∩ (π₁ (barycenter_join_boundary_disjoint_link X s x s_in_X x_nin_X))[((π₁ (barycenter_disjoint_boundary X s x s_in_X x_nin_X))[(simplex {x} ⋆ ∂s)] ⋆ Lk(X, s) s_in_X)]).simplices
      = ((π₁ (boundary_disjoint_link X s s_in_X))[Lk(X, s) s_in_X ⋆ ∂s]).simplices
:= begin
  rw [set.subset.antisymm_iff],
  split,

  apply star_boundary_is_join_left,
  apply star_boundary_is_join_right,
end

lemma star_boundary_diff_ne
    {X : simplicial_complex α}
    {s t : finset α} [s_ne : nonempty s]
    {s_in_X : s ∈ X.simplices}
  : t ∈ (π₁ (boundary_disjoint_link X s s_in_X)[(Lk(X, s) s_in_X) ⋆ ∂s]).simplices
      → nonempty ↥(s \ t)
:= begin
  intros t_in_star_bd,
  rw [join_proj_mem] at t_in_star_bd,
  choose t₁ t₁_in_link t₂ t₂_in_bd t_decomp using t_in_star_bd,

  simp only [link, set.mem_sep_iff] at t₁_in_link,
  choose t₁_in_X st₁_in_X st₁_disj using t₁_in_link,

  rw [simplex_boundary_mem_iff_subset] at t₂_in_bd,

  rw [finset.nonempty_coe_sort, finset.sdiff_nonempty],
  simp only [finset.subset_iff, not_forall, not_imp],
  rw [finset.ssubset_iff] at t₂_in_bd,
  choose a a_nin_t₂ at₂_ss_s using t₂_in_bd,
  rw [finset.subset_iff] at at₂_ss_s,
  specialize at₂_ss_s (by exact finset.mem_insert_self a t₂),

  use a, split, assumption,
  simp only [finset.eq_empty_iff_forall_not_mem, finset.mem_inter, not_and] at st₁_disj,
  specialize st₁_disj a at₂_ss_s,
  simp only [t_decomp, finset.mem_union, not_or_distrib],
  split; assumption,
end

lemma star_boundary_mem_link
    {X : simplicial_complex α}
    {s t : finset α}
    {s_in_X : s ∈ X.simplices}
    {t_in_X : t ∈ X.simplices}
  : t ∈ (π₁ (boundary_disjoint_link X s s_in_X)[(Lk(X, s) s_in_X) ⋆ ∂s]).simplices
      → (s \ t) ∈ (Lk(X, t) t_in_X).simplices
:= begin
  intros t_in_star_bd,
  rw [join_proj_mem] at t_in_star_bd,
  choose t₁ t₁_in_link t₂ t₂_in_bd t_decomp using t_in_star_bd,

  simp only [link, set.mem_sep_iff] at t₁_in_link ⊢,
  choose t₁_in_X st₁_in_X st₁_disj using t₁_in_link,

  split,
  apply X.subset_closed s,
  assumption,
  apply finset.sdiff_subset,

  split,
  rw [finset.union_sdiff_self_eq_union, t_decomp, finset.union_assoc],
  simp only [simplex_boundary, set.mem_union, set.mem_diff, set.mem_singleton_iff, finset.mem_coe, finset.mem_powerset] at t₂_in_bd,
  cases t₂_in_bd with t₂_in_bd t₂_empty,

  choose t₂_ss_s t₂_ne_s using t₂_in_bd,
  have st₂_rw : t₂ ∪ s = s, from
  begin
    rw [finset.union_eq_right_iff_subset],
    assumption,
  end,
  rw [st₂_rw, finset.union_comm],
  assumption,

  rw [t₂_empty, finset.empty_union, finset.union_comm],
  assumption,

  apply finset.inter_sdiff_self,
end

lemma not_mem_link_vertices
    {X : simplicial_complex α}
    {s : finset α}
    {x : α}
    {s_in_X : s ∈ X.simplices}
  : x ∉ vertices X → x ∉ vertices (Lk(X, s) s_in_X)
:= begin
  contrapose,
  simp only [not_not],
  apply is_subcomplex_vertices,
  apply link_subcomplex,
end

lemma stellar_subdiv_anticomm_link_left_ac
    (X : simplicial_complex α)
    (s t : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (t_in_X : t ∈ X.simplices)
    (t_in_star_bd : t ∈ (π₁ (boundary_disjoint_link X s s_in_X)[(Lk(X, s) s_in_X) ⋆ ∂s]).simplices)
  : ∀ (u : finset α),
      (u ∈ (star_complement X s s_in_X).simplices) →
        (t ∪ u ∈ (star_complement X s s_in_X).simplices) →
          (t ∩ u = ∅) →
            u ∈ (σ((Lk(X, t) t_in_X), s\t, x;
                  (star_boundary_diff_ne t_in_star_bd),
                  (star_boundary_mem_link t_in_star_bd),
                  (not_mem_link_vertices x_nin_X))).simplices
:= begin
  intros u u_in_star_comp tu_in_star_comp tu_disj,
  simp only[link, stellar_subdivision, star_complement, simplicial_union] at u_in_star_comp tu_in_star_comp ⊢,
  simp only[set.mem_union, set.mem_sep_iff] at u_in_star_comp tu_in_star_comp ⊢,

  choose u_in_X s_nss_u using u_in_star_comp,
  choose tu_in_X s_nss_tu using tu_in_star_comp,

  have st_nss_u : ¬(s\t ⊆ u), from
  begin
    revert s_nss_tu,
    contrapose,
    simp only[not_not],
    intro st_ss_u,

    apply @finset.union_subset_left _ _ s t,
    rw [←finset.union_sdiff_self_eq_union, finset.union_sdiff_symm],
    apply finset.union_subset_union_right,
    assumption,
  end,
  
  left, split, split,
  assumption,
  split; assumption,
  assumption,
end

lemma stellar_subdiv_anticomm_link_left_ad_tu_in_X
    (X : simplicial_complex α)
    (s t u t₁ u₁ t₂ u₂ : finset α) [s_ne : nonempty ↥s]
    (stu₁_in_X : s ∪ (t₁ ∪ u₁) ∈ X.simplices)
    (t₂_in_bd : t₂ ⊂ s)
    (u₂_in_bd : u₂ ⊂ s)
    (t_decomp : t = t₁ ∪ t₂)
    (u_decomp : u = u₁ ∪ u₂)
  : t ∪ u ∈ X.simplices
:= begin
  rw [u_decomp, t_decomp],
  apply X.subset_closed (t₁ ∪ u₁ ∪ s),
  rw [finset.union_comm],
  exact stu₁_in_X,
  
  have tu_ss_s : t₂ ∪ u₂ ⊆ s, from
  begin
    apply finset.union_subset;
    rw [finset.ssubset_iff_subset_ne] at t₂_in_bd u₂_in_bd,
    choose t₂_ss_s t₂_ne_s using t₂_in_bd,
    exact t₂_ss_s,
    choose u₂_ss_s u₂_ne_s using u₂_in_bd,
    exact u₂_ss_s,
  end,
  rw [finset.union_assoc, finset.union_comm u₁ u₂, ←finset.union_assoc t₂, finset.union_comm (t₂ ∪ u₂), ←finset.union_assoc],
  apply finset.union_subset_union_right,
  exact tu_ss_s,
end

lemma stellar_subdiv_anticomm_link_left_ad_st_nss_u
    (X : simplicial_complex α)
    (s t u t₁ u₁ t₂ u₂ : finset α) [s_ne : nonempty ↥s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (t_in_X : t ∈ X.simplices)
    (u_in_X : u ∈ X.simplices)
    (tu_disj : t ∩ u = ∅)
    (su₁_disj : s ∩ u₁ = ∅)
    (t₂_in_bd : t₂ ⊂ s)
    (tu_in_join : t₂ ∪ u₂ ∈ ((π₁ (barycenter_disjoint_boundary X s x s_in_X x_nin_X))[simplex {x} ⋆ ∂s]).simplices)
    (t_decomp : t = t₁ ∪ t₂)
    (u_decomp : u = u₁ ∪ u₂)
  : ¬s \ t₂ ⊆ u
:= begin
  rw [join_proj_disj_union_mem] at tu_in_join,
  choose t₃ t₃_in_barycenter u₃ u₃_in_barycenter t₂ t₂_in_bd u₂ u₂_in_bd tu₂_decomp using tu_in_join,
  choose t₂_decomp u₂_decomp tu₃_in_barycenter tu₂_in_bd using tu₂_decomp,
  
  have u₃_empty : u₃ = ∅, from
  begin
    simp only [simplex, finset.mem_coe, finset.mem_powerset, finset.subset_singleton_iff] at u₃_in_barycenter,
    cases u₃_in_barycenter with u₃_empty u₃_eq_x,
    exact u₃_empty,

    have contra : x ∈ vertices X, from
    begin
      rw [vertex_iff_singleton],
      apply X.subset_closed u,
      exact u_in_X,
      
      rw [u_decomp, u₂_decomp, u₃_eq_x, ←finset.union_assoc, finset.union_comm u₁ {x}, finset.union_assoc],
      apply finset.subset_union_left,
    end,
    contradiction,
  end,

  have t₃_empty : t₃ = ∅, from
  begin
    simp only [simplex, finset.mem_coe, finset.mem_powerset, finset.subset_singleton_iff] at t₃_in_barycenter,
    cases t₃_in_barycenter with t₃_empty t₃_eq_x,
    exact t₃_empty,

    have contra : x ∈ vertices X, from
    begin
      rw [vertex_iff_singleton],
      apply X.subset_closed t,
      exact t_in_X,
      
      rw [t_decomp, t₂_decomp, t₃_eq_x, ←finset.union_assoc, finset.union_comm t₁ {x}, finset.union_assoc],
      apply finset.subset_union_left,
    end,
    contradiction,
  end,

  subst u₃,
  subst t₃,
  rw [finset.empty_union] at t₂_decomp u₂_decomp tu₃_in_barycenter,
  rw [←u₂_decomp, ←t₂_decomp, simplex_boundary_mem_iff_subset] at tu₂_in_bd,

  subst u₂_decomp,
  subst t₂_decomp,
  
  have u₂_ss_st₂_sdiff : u₂ ⊂ s \ t₂, from
  begin
    rw [finset.ssubset_iff_subset_ne] at tu₂_in_bd ⊢,
    choose tu₂_ss_s tu₂_ne_s using tu₂_in_bd,
    split,

    rw [finset.subset_sdiff],
    split,
    apply @finset.subset.trans _ _ (t₂ ∪ u₂),
    apply finset.subset_union_right,
    exact tu₂_ss_s,
    rw [finset.disjoint_iff_inter_eq_empty, ←finset.subset_empty],
    rw [←tu_disj, t_decomp, u_decomp],
    rw [finset.inter_comm],
    apply finset.inter_subset_inter;
    apply finset.subset_union_right,

    rw [finset.union_comm] at tu₂_ne_s,
    have H1 : s = s ∪ t₂, from
    begin
      symmetry,
      rw [finset.union_eq_left_iff_subset],
      rw [finset.ssubset_def] at t₂_in_bd,
      tauto,
    end,
    rw [H1] at tu₂_ne_s,
    revert tu₂_ne_s,
    contrapose,
    simp only[not_ne_iff],
    rw [←@finset.sdiff_union_self_eq_union _ _ s],
    exact congr_arg (λ (a : finset α), a ∪ t₂),
  end,

  rw [←finset.lt_iff_ssubset, finset.partial_order.lt_iff_le_not_le, finset.le_iff_subset, finset.le_iff_subset] at u₂_ss_st₂_sdiff,
  choose u₂_ss_st₂ st₂_nss_u₂ using u₂_ss_st₂_sdiff,
  
  rw [finset.not_subset] at st₂_nss_u₂ ⊢,
  choose y y_in_st₂ y_nin_u₂ using st₂_nss_u₂,
  use y, use y_in_st₂,
  rw [u_decomp, finset.not_mem_union],
  split,
  
  rw [finset.eq_empty_iff_forall_not_mem] at su₁_disj,
  specialize su₁_disj y,
  simp only[finset.mem_inter, not_and_distrib] at su₁_disj,
  cases su₁_disj with contra y_nin_u₁,
  
  have H : y ∈ s, from
  begin
    apply @finset.mem_of_subset _ (s \ t₂),
    apply finset.sdiff_subset,
    exact y_in_st₂,
  end,
  contradiction,
  
  exact y_nin_u₁,
  exact y_nin_u₂,
end

lemma stellar_subdiv_anticomm_link_left_ad
    (X : simplicial_complex α)
    (s t : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (t_in_X : t ∈ X.simplices)
    (t_in_star_bd : t ∈ (π₁ (boundary_disjoint_link X s s_in_X)[(Lk(X, s) s_in_X) ⋆ ∂s]).simplices)
  : ∀ (u : finset α),
      (u ∈ (star_complement X s s_in_X).simplices) →
        (t ∪ u ∈ ((π₁ (barycenter_join_boundary_disjoint_link X s x s_in_X x_nin_X))[((π₁ (barycenter_disjoint_boundary X s x s_in_X x_nin_X))[(simplex {x} ⋆ ∂s)] ⋆ Lk(X, s) s_in_X)]).simplices) →
          (t ∩ u = ∅) →
            u ∈ (σ((Lk(X, t) t_in_X), s\t, x;
                  (star_boundary_diff_ne t_in_star_bd),
                  (star_boundary_mem_link t_in_star_bd),
                  (not_mem_link_vertices x_nin_X))).simplices
:= begin
  intros u u_in_star_comp tu_in_join tu_disj,
  simp only[link, stellar_subdivision, star_complement, simplicial_union] at u_in_star_comp tu_in_join ⊢,
  simp only[set.mem_union, set.mem_sep_iff] at u_in_star_comp ⊢,
  choose u_in_X s_nss_u using u_in_star_comp,

  rw [join_proj_disj_union_mem] at tu_in_join,
  choose t'₂ t'₂_in_join u'₂ u'₂_in_join t₁ t₁_in_link u₁ u₁_in_link tu_decomp using tu_in_join,
  choose t_decomp u_decomp tu_in_join tu_in_link using tu_decomp,

  simp only[set.mem_sep_iff] at t₁_in_link u₁_in_link tu_in_link,
  choose t₁_in_X st₁_in_X st₁_disj using t₁_in_link,
  choose u₁_in_X su₁_in_X su₁_disj using u₁_in_link,
  choose tu₁_in_X stu₁_in_X stu₁_disj using tu_in_link,

  rw [join_proj_mem] at t'₂_in_join u'₂_in_join,
  choose u₃ u₃_in_barycenter u₂ u₂_in_bd u'_decomp using u'₂_in_join,
  choose t₃ t₃_in_barycenter t₂ t₂_in_bd t'_decomp using t'₂_in_join,
  subst u'_decomp,
  subst t'_decomp,

  rw [simplex_boundary_mem_iff_subset] at u₂_in_bd t₂_in_bd,

  have u₃_empty : u₃ = ∅, from
  begin
    simp only [simplex, finset.mem_coe, finset.mem_powerset, finset.subset_singleton_iff] at u₃_in_barycenter,
    cases u₃_in_barycenter with u₃_empty u₃_eq_x,
    exact u₃_empty,

    have contra : x ∈ vertices X, from
    begin
      rw [vertex_iff_singleton],
      apply X.subset_closed u,
      exact u_in_X,
      
      rw [u_decomp, u₃_eq_x, finset.union_assoc],
      apply finset.subset_union_left,
    end,
    contradiction,
  end,

  have t₃_empty : t₃ = ∅, from
  begin
    simp only [simplex, finset.mem_coe, finset.mem_powerset, finset.subset_singleton_iff] at t₃_in_barycenter,
    cases t₃_in_barycenter with t₃_empty t₃_eq_x,
    exact t₃_empty,

    have contra : x ∈ vertices X, from
    begin
      rw [vertex_iff_singleton],
      apply X.subset_closed t,
      exact t_in_X,
      
      rw [t_decomp, t₃_eq_x, finset.union_assoc],
      apply finset.subset_union_left,
    end,
    contradiction,
  end,

  subst u₃,
  subst t₃,
  simp only[finset.empty_union] at u_decomp t_decomp tu_in_join,
  rw [finset.union_comm] at u_decomp t_decomp,

  left, split, split,
  exact u_in_X,
  split,

  exact stellar_subdiv_anticomm_link_left_ad_tu_in_X X s t u t₁ u₁ t₂ u₂ stu₁_in_X t₂_in_bd u₂_in_bd t_decomp u_decomp,
  exact tu_disj,
  
  rw [t_decomp, finset.sdiff_union_distrib],
  have st₁_sdiff_ident : s \ t₁ = s, from
  begin
    apply finset.sdiff_eq_self_of_disjoint,
    rw [finset.disjoint_iff_inter_eq_empty],
    exact st₁_disj,
  end,
  
  rw [st₁_sdiff_ident, finset.inter_sdiff, finset.inter_self],
  exact stellar_subdiv_anticomm_link_left_ad_st_nss_u X s t u t₁ u₁ t₂ u₂ x s_in_X x_nin_X t_in_X u_in_X tu_disj su₁_disj t₂_in_bd tu_in_join t_decomp u_decomp,
end

lemma stellar_subdiv_anticomm_link_left_bc
    (X : simplicial_complex α)
    (s t : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (t_in_X : t ∈ X.simplices)
    (t_in_star_bd : t ∈ (π₁ (boundary_disjoint_link X s s_in_X)[(Lk(X, s) s_in_X) ⋆ ∂s]).simplices)
  : ∀ (u : finset α),
      (u ∈ ((π₁ (barycenter_join_boundary_disjoint_link X s x s_in_X x_nin_X))[((π₁ (barycenter_disjoint_boundary X s x s_in_X x_nin_X))[(simplex {x} ⋆ ∂s)] ⋆ Lk(X, s) s_in_X)]).simplices) →
        (t ∪ u ∈ (star_complement X s s_in_X).simplices) →
          (t ∩ u = ∅) →
            u ∈ (σ((Lk(X, t) t_in_X), s\t, x;
                  (star_boundary_diff_ne t_in_star_bd),
                  (star_boundary_mem_link t_in_star_bd),
                  (not_mem_link_vertices x_nin_X))).simplices
:= begin
  intros u u_in_join tu_in_star_comp tu_disj,
  simp only[link, stellar_subdivision, star_complement, simplicial_union] at u_in_join tu_in_star_comp ⊢,
  simp only[set.mem_union, set.mem_sep_iff] at tu_in_star_comp ⊢,
  choose tu_in_X s_nss_tu using tu_in_star_comp,

  rw [join_proj_mem] at u_in_join,
  choose u'₂ u'₂_in_join u₁ u₁_in_link u_decomp using u_in_join,

  simp only[set.mem_sep_iff] at u₁_in_link,
  choose u₁_in_X su₁_in_X su₁_disj using u₁_in_link,

  rw [join_proj_mem] at u'₂_in_join,
  choose u₃ u₃_in_barycenter u₂ u₂_in_bd u'_decomp using u'₂_in_join,
  subst u'_decomp,

  left, split, split,
  apply X.subset_closed (t ∪ u),
  assumption,
  apply finset.subset_union_right,
  
  split; assumption,
  
  revert s_nss_tu,
  contrapose,
  simp only[not_not],
  intro st_ss_u,

  apply @finset.union_subset_left _ _ s t,
  rw [←finset.union_sdiff_self_eq_union, finset.union_sdiff_symm],
  apply finset.union_subset_union_right,
  assumption,
end

lemma stellar_subdiv_anticomm_link_left_bd_u_ss_st
    (X : simplicial_complex α)
    (s t u t₁ u₁ t₂ u₂ u₃ : finset α)
    [s_ne : nonempty ↥s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (t_in_X : t ∈ X.simplices)
    (t_in_star_bd : t ∈ (π₁ (boundary_disjoint_link X s s_in_X)[(Lk(X, s) s_in_X) ⋆ ∂s]).simplices)
    (tu_disj : t ∩ u = ∅)
    (t₂_in_bd : t₂ ⊂ s)
    (tu₂_in_bd : t₂ ∪ u₂ ⊂ s)
    (t_decomp : t = t₂ ∪ t₁)
    (u_decomp : u = u₃ ∪ u₂ ∪ u₁)
  : u₂ ⊂ s \ t₂
:= begin
  rw [finset.ssubset_iff_subset_ne] at tu₂_in_bd ⊢,
  choose tu₂_ss_s tu₂_ne_s using tu₂_in_bd,
  split,

  rw [finset.subset_sdiff],
  split,
  apply @finset.subset.trans _ _ (t₂ ∪ u₂),
  apply finset.subset_union_right,
  apply tu₂_ss_s,
  rw [finset.disjoint_iff_inter_eq_empty, ←finset.subset_empty],
  rw [←tu_disj, t_decomp, u_decomp],
  rw [finset.inter_comm],
  apply finset.inter_subset_inter,
  apply @finset.subset_union_left _ _ t₂ t₁,
  rw [finset.union_assoc, finset.union_comm, finset.union_assoc],
  apply @finset.subset_union_left _ _ u₂ (u₁ ∪ u₃),

  rw [finset.union_comm] at tu₂_ne_s,
  have H1 : s = s ∪ t₂, from
  begin
    symmetry,
    rw [finset.union_eq_left_iff_subset],
    rw [finset.ssubset_def] at t₂_in_bd,
    choose t₂_ss_s t₂_ne_s using t₂_in_bd,
    apply t₂_ss_s,
  end,
  rw [H1] at tu₂_ne_s,
  revert tu₂_ne_s,
  contrapose,
  simp only[not_ne_iff],
  rw [←@finset.sdiff_union_self_eq_union _ _ s],
  exact congr_arg (λ (a : finset α), a ∪ t₂),
end

lemma stellar_subdiv_anticomm_link_left_bd_u_mem_link
    (X : simplicial_complex α)
    (s t u t₁ u₁ t₂ u₂ u₃ : finset α) [s_ne : nonempty ↥s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (t_in_X : t ∈ X.simplices)
    (t_in_star_bd : t ∈ (π₁ (boundary_disjoint_link X s s_in_X)[(Lk(X, s) s_in_X) ⋆ ∂s]).simplices)
    (tu_disj : t ∩ u = ∅)
    (stu₁_in_X : s ∪ (t₁ ∪ u₁) ∈ X.simplices)
    (t_decomp : t = t₂ ∪ t₁)
    (u_decomp : u = u₃ ∪ u₂ ∪ u₁)
    (t₂_ss_s : t₂ ⊆ s)
  : t ∪ u₁ ∈ X.simplices ∧ t ∩ u₁ = ∅
:= begin
  split,
  rw [t_decomp],
  apply X.subset_closed (s ∪ t₁ ∪ u₁),
  rw [finset.union_assoc],
  apply stu₁_in_X,
  simp only[finset.union_assoc],
  apply finset.union_subset_union_left,
  apply t₂_ss_s,
  
  rw [←finset.subset_empty],
  apply @finset.subset.trans _ _ (t ∩ u),
  apply finset.inter_subset_inter_left,
  rw [u_decomp, finset.union_comm],
  apply finset.subset_union_left,
  rw [finset.subset_empty],
  apply tu_disj,
end

lemma stellar_subdiv_anticomm_link_left_bd_stu_mem_link
    (X : simplicial_complex α)
    (s t u t₁ u₁ t₂ u₂ u₃ : finset α) [s_ne : nonempty ↥s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (t_in_X : t ∈ X.simplices)
    (t_in_star_bd : t ∈ (π₁ (boundary_disjoint_link X s s_in_X)[(Lk(X, s) s_in_X) ⋆ ∂s]).simplices)
    (tu_disj : t ∩ u = ∅)
    (su₁_disj : s ∩ u₁ = ∅)
    (stu₁_in_X : s ∪ (t₁ ∪ u₁) ∈ X.simplices)
    (t_decomp : t = t₂ ∪ t₁)
    (u_decomp : u = u₃ ∪ u₂ ∪ u₁)
    (st₁_sdiff_ident : s \ t₁ = s)
    (t₂_ss_s : t₂ ⊆ s)
  : s \ t ∪ u₁ ∈ (Lk(X, t) t_in_X).simplices ∧ s \ t ∩ u₁ = ∅
:= begin
  split, split,
  apply X.subset_closed (s ∪ t₁ ∪ u₁),
  rw [finset.union_assoc],
  apply stu₁_in_X,
  apply @finset.subset.trans _ _ (s ∪ u₁),
  apply finset.union_subset_union_left,
  apply finset.sdiff_subset,
  rw [finset.union_assoc, finset.union_comm t₁ u₁, ←finset.union_assoc],
  apply finset.subset_union_left,
  
  split,
  apply X.subset_closed (s ∪ t₁ ∪ u₁),
  rw [finset.union_assoc],
  apply stu₁_in_X,
  rw [t_decomp, finset.sdiff_union_distrib, st₁_sdiff_ident, finset.inter_comm],
  rw [finset.inter_sdiff, finset.inter_self, ←finset.union_assoc, finset.union_assoc t₂ t₁],
  rw [finset.union_comm t₁ (s \ t₂), ←finset.union_assoc],
  rw [finset.union_assoc, finset.union_assoc s t₁],
  apply finset.union_subset_union_left,
  apply finset.subset_of_eq,
  apply finset.union_sdiff_of_subset,
  apply t₂_ss_s,
  
  rw [finset.inter_distrib_left, finset.inter_comm, finset.sdiff_inter_self, finset.empty_union],
  rw [←finset.subset_empty],
  apply @finset.subset.trans _ _ (t ∩ u),
  apply finset.inter_subset_inter_left,
  rw [u_decomp],
  apply finset.subset_union_right,
  rw [finset.subset_empty],
  apply tu_disj,
  
  rw [←finset.subset_empty],
  apply @finset.subset.trans _ _ (s ∩ u₁),
  apply finset.inter_subset_inter_right,
  apply finset.sdiff_subset,
  rw [finset.subset_empty],
  apply su₁_disj,
end

lemma stellar_subdiv_anticomm_link_left_bd
    (X : simplicial_complex α)
    (s t : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (t_in_X : t ∈ X.simplices)
    (t_in_star_bd : t ∈ (π₁ (boundary_disjoint_link X s s_in_X)[(Lk(X, s) s_in_X) ⋆ ∂s]).simplices)
  : ∀ (u : finset α),
      (u ∈ ((π₁ (barycenter_join_boundary_disjoint_link X s x s_in_X x_nin_X))[((π₁ (barycenter_disjoint_boundary X s x s_in_X x_nin_X))[(simplex {x} ⋆ ∂s)] ⋆ Lk(X, s) s_in_X)]).simplices) →
        (t ∪ u ∈ ((π₁ (barycenter_join_boundary_disjoint_link X s x s_in_X x_nin_X))[((π₁ (barycenter_disjoint_boundary X s x s_in_X x_nin_X))[(simplex {x} ⋆ ∂s)] ⋆ Lk(X, s) s_in_X)]).simplices) →
          (t ∩ u = ∅) →
            u ∈ (σ((Lk(X, t) t_in_X), s\t, x;
                  (star_boundary_diff_ne t_in_star_bd),
                  (star_boundary_mem_link t_in_star_bd),
                  (not_mem_link_vertices x_nin_X))).simplices
:= begin
  intros u u_in_join tu_in_join tu_disj,
  simp only[link, stellar_subdivision, star_complement, simplicial_union] at u_in_join tu_in_join ⊢,

  rw [join_proj_disj_union_mem] at tu_in_join,
  choose t'₂ t'₂_in_join u'₂ u'₂_in_join t₁ t₁_in_link u₁ u₁_in_link tu_decomp using tu_in_join,
  choose t_decomp u_decomp tu_in_join tu_in_link using tu_decomp,

  simp only[set.mem_sep_iff] at t₁_in_link u₁_in_link tu_in_link,
  choose t₁_in_X st₁_in_X st₁_disj using t₁_in_link,
  choose u₁_in_X su₁_in_X su₁_disj using u₁_in_link,
  choose tu₁_in_X stu₁_in_X stu₁_disj using tu_in_link,

  rw [join_proj_disj_union_mem] at tu_in_join,
  choose t₃ t₃_in_barycenter u₃ u₃_in_barycenter t₂ t₂_in_bd u₂ u₂_in_bd tu₂_decomp using tu_in_join,
  choose t₂_decomp u₂_decomp tu₃_in_barycenter tu₂_in_bd using tu₂_decomp,
  
  have t₃_empty : t₃ = ∅, from
  begin
    simp only [simplex, finset.mem_coe, finset.mem_powerset, finset.subset_singleton_iff] at t₃_in_barycenter,
    cases t₃_in_barycenter with t₃_empty t₃_eq_x,
    apply t₃_empty,

    have contra : x ∈ vertices X, from
    begin
      rw [vertex_iff_singleton],
      apply X.subset_closed t,
      apply t_in_X,
      rw [t_decomp, t₂_decomp, t₃_eq_x, finset.union_assoc],
      apply finset.subset_union_left,
    end,
    contradiction,
  end,
  subst t₃_empty,
  simp only[finset.empty_union] at t₂_decomp u₂_decomp tu₃_in_barycenter,
  rw [simplex_boundary_mem_iff_subset] at tu₂_in_bd u₂_in_bd t₂_in_bd,
  rw [t₂_decomp] at *,
  rw [u₂_decomp] at *,
  clear t₂_decomp u₂_decomp u_in_join u'₂_in_join t'₂_in_join tu₃_in_barycenter t₃_in_barycenter t'₂ u'₂,

  right,
  
  rw [join_proj_mem],
  have tu₂_disj : t₂ ∩ u₂ = ∅, from
  begin
    rw [←finset.subset_empty],
    apply @finset.subset.trans _ _ (t ∩ u),
    apply finset.inter_subset_inter,

    rw [t_decomp],
    apply @finset.subset_union_left _ _ t₂ t₁,

    rw [u_decomp, finset.union_assoc, finset.union_comm, finset.union_assoc],
    apply @finset.subset_union_left _ _ u₂ (u₁ ∪ u₃),

    rw [finset.subset_empty],
    apply tu_disj,
  end,

  have st₁_sdiff_ident : s \ t₁ = s, from
  begin
    apply finset.sdiff_eq_self_of_disjoint,
    rw [finset.disjoint_iff_inter_eq_empty],
    apply st₁_disj,
  end,

  have u₂_ss_st₂_sdiff : u₂ ⊂ s \ t₂, from
  begin
    apply stellar_subdiv_anticomm_link_left_bd_u_ss_st X s t u t₁ u₁ t₂ u₂ u₃ x s_in_X x_nin_X t_in_X t_in_star_bd tu_disj t₂_in_bd tu₂_in_bd t_decomp u_decomp,
  end,

  have u₂_ss_st : u₂ ⊂ s \ t, from
  begin
    rw [t_decomp, finset.sdiff_union_distrib, st₁_sdiff_ident, finset.inter_comm, finset.inter_sdiff, finset.inter_self],
    apply u₂_ss_st₂_sdiff,
  end,

  rw [finset.ssubset_def] at t₂_in_bd,
  choose t₂_ss_s s_nss_t₂ using t₂_in_bd,

  use (u₃ ∪ u₂), split,

  rw [join_proj_disj_union_mem],
  use u₃, split, apply u₃_in_barycenter,
  use ∅, split, apply simplicial_complex_empty_simplex,
  use ∅, split, apply simplicial_complex_empty_simplex,
  use u₂, split,
  rw [@simplex_boundary_mem_iff_subset _ _ _ _ (star_boundary_diff_ne t_in_star_bd)],
  apply u₂_ss_st,
  
  split, symmetry, apply finset.union_empty,
  split, symmetry, apply finset.empty_union,
  split, rw [finset.union_empty],
  apply u₃_in_barycenter,
  
  rw [finset.empty_union, @simplex_boundary_mem_iff_subset _ _ _ _ (star_boundary_diff_ne t_in_star_bd)],
  apply u₂_ss_st,
  
  use u₁, split, split, split,
  apply u₁_in_X,

  apply stellar_subdiv_anticomm_link_left_bd_u_mem_link X s t u t₁ u₁ t₂ u₂ u₃ x s_in_X x_nin_X t_in_X t_in_star_bd tu_disj stu₁_in_X t_decomp u_decomp t₂_ss_s,
  
  apply stellar_subdiv_anticomm_link_left_bd_stu_mem_link X s t u t₁ u₁ t₂ u₂ u₃ x s_in_X x_nin_X t_in_X t_in_star_bd tu_disj su₁_disj stu₁_in_X t_decomp u_decomp st₁_sdiff_ident t₂_ss_s,
  apply u_decomp,
end

lemma star_boundary_mem_subdiv
    {X : simplicial_complex α}
    {s t : finset α} [s_ne : nonempty s]
    {x : α}
    {s_in_X : s ∈ X.simplices}
    {x_nin_X : x ∉ vertices X}
  : t ∈ (π₁ (boundary_disjoint_link X s s_in_X)[(Lk(X, s) s_in_X) ⋆ ∂s]).simplices
      → t ∈ (σ(X, s, x; s_ne, s_in_X, x_nin_X)).simplices
:= begin
  intros t_in_star_bd,
  rw [join_proj_mem] at t_in_star_bd,
  choose t₁ t₁_in_link t₂ t₂_in_bd t_decomp using t_in_star_bd,

  simp only [stellar_subdivision, simplicial_union, set.mem_union, join_proj_mem],
  right,

  use (∅ ∪ t₂), split,
  use ∅, split, apply simplicial_complex_empty_simplex,
  use t₂, split, assumption,
  refl,

  use t₁, split, assumption,
  rw [finset.empty_union, finset.union_comm],
  assumption,
end

lemma stellar_subdiv_anticomm_link_left
    (X : simplicial_complex α)
    (s t : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (t_in_X : t ∈ X.simplices)
    (t_in_star_bd : t ∈ (π₁ (boundary_disjoint_link X s s_in_X)[(Lk(X, s) s_in_X) ⋆ ∂s]).simplices)
  : (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), t) (star_boundary_mem_subdiv t_in_star_bd)).simplices
      ⊆ (σ((Lk(X, t) t_in_X), s\t, x;
          (star_boundary_diff_ne t_in_star_bd),
          (star_boundary_mem_link t_in_star_bd),
          (not_mem_link_vertices x_nin_X))).simplices
:= begin
  simp only[stellar_subdivision, simplicial_union],
  simp only[set.subset_def],
  intros u u_in_link,
  simp only[link, set.mem_sep_iff] at u_in_link,
  choose u_in_subdiv tu_in_subdiv tu_disj using u_in_link,

  cases u_in_subdiv with u_in_star_comp u_in_join; -- Cases A, B resp.
  cases tu_in_subdiv with tu_in_star_comp tu_in_join, -- Cases C, D resp.

  apply stellar_subdiv_anticomm_link_left_ac; assumption,
  apply stellar_subdiv_anticomm_link_left_ad; assumption,
  apply stellar_subdiv_anticomm_link_left_bc; assumption,
  apply stellar_subdiv_anticomm_link_left_bd; assumption,
end

lemma stellar_subdiv_anticomm_link_right_e
    (X : simplicial_complex α)
    (s t : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (t_in_X : t ∈ X.simplices)
    (t_in_star_bd : t ∈ (π₁ (boundary_disjoint_link X s s_in_X)[(Lk(X, s) s_in_X) ⋆ ∂s]).simplices)
  : ∀ (u : finset α),
      (u ∈ (@star_complement _ _ (Lk(X, t) t_in_X) (s \ t)
          (star_boundary_diff_ne t_in_star_bd)
          (star_boundary_mem_link t_in_star_bd)).simplices)
        → (u ∈ (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), t) (star_boundary_mem_subdiv t_in_star_bd)).simplices)
:= begin
  intros u u_in_star_comp,
  simp only[link, star_complement, stellar_subdivision, simplicial_union] at u_in_star_comp ⊢,
  simp only[set.mem_union, set.mem_sep_iff] at u_in_star_comp ⊢,
  choose u_in_link st_nss_u using u_in_star_comp,
  choose u_in_X tu_in_X tu_disj using u_in_link,

  split, left, split,
  assumption,
  revert st_nss_u,
  contrapose,
  simp only[not_not],
  intro s_ss_u,
  apply @finset.subset.trans _ _ s,
  apply finset.sdiff_subset,
  assumption,
  
  split, left, split,
  assumption,
  
  simp only[finset.subset_iff, not_forall] at st_nss_u ⊢,
  choose y y_in_st y_nin_u using st_nss_u,
  simp only[finset.mem_sdiff] at y_in_st,
  choose y_in_s y_nin_t using y_in_st,
  use y, split, assumption,
  simp only[finset.mem_union, not_or_distrib],
  split; assumption,
  
  assumption,
end

lemma stellar_subdiv_anticomm_link_right_f
    (X : simplicial_complex α)
    (s t : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (t_in_X : t ∈ X.simplices)
    (t_in_star_bd : t ∈ (π₁ (boundary_disjoint_link X s s_in_X)[(Lk(X, s) s_in_X) ⋆ ∂s]).simplices)
  : ∀ (u : finset α),
      (u ∈ ((π₁ (barycenter_join_boundary_disjoint_link (Lk(X, t) t_in_X) (s \ t) x (star_boundary_mem_link t_in_star_bd) (not_mem_link_vertices x_nin_X)))[((π₁ (barycenter_disjoint_boundary X (s \ t) x (by { apply X.subset_closed s, assumption, apply finset.sdiff_subset, }) x_nin_X))[(simplex {x}) ⋆ ∂(s \ t)]) ⋆ (Lk(Lk(X, t) t_in_X, s \ t) (star_boundary_mem_link t_in_star_bd))]).simplices)
        → (u ∈ (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), t) (star_boundary_mem_subdiv t_in_star_bd)).simplices)
:= begin
  intros u u_in_join,
  simp only[link, star_complement, stellar_subdivision, simplicial_union] at u_in_join ⊢,
  simp only[set.mem_union, set.mem_sep_iff],

  rw [join_proj_mem] at u_in_join,
  choose u'₂ u'₂_in_join u₁ u₁_in_link u_decomp using u_in_join,
  rw [join_proj_mem] at u'₂_in_join,
  choose u₃ u₃_in_barycenter u₂ u₂_in_bd u'₂_decomp using u'₂_in_join,
  subst u'₂_decomp,

  let u₁_in_link := u₁_in_link,
  let u₂_in_bd' := u₂_in_bd,

  rw [@simplex_boundary_mem_iff_subset _ _ _ _ (star_boundary_diff_ne t_in_star_bd)] at u₂_in_bd,
  simp only[set.mem_sep_iff] at u₁_in_link,
  choose u₁_in_t_link stu₁_in_t_link stu₁_disj using u₁_in_link,
  choose u₁_in_X tu₁_in_X tu₁_disj using u₁_in_t_link,
  choose stu₁_in_X tstu₁_in_X tstu₁_disj using stu₁_in_t_link,

  rw [join_proj_mem] at t_in_star_bd,
  choose t₁ t₁_in_link t₂ t₂_in_bd t_decomp using t_in_star_bd,

  let t₁_in_link := t₁_in_link,
  let t₁_in_bd' := t₂_in_bd,

  simp only[link, set.mem_sep_iff] at t₁_in_link,
  choose t₁_in_X st₁_in_X st₁_disj using t₁_in_link,

  rw [simplex_boundary_mem_iff_subset] at t₂_in_bd,

  have st₁_sdiff_ident : s \ t₁ = s, from
  begin
    apply finset.sdiff_eq_self_of_disjoint,
    rw [finset.disjoint_iff_inter_eq_empty],
    assumption,
  end,

  split, right,
  rw [join_proj_mem],

  use (u₃ ∪ u₂), split,
  rw [join_proj_mem],
  use u₃, split, assumption,
  use u₂, split,
  rw [simplex_boundary_mem_iff_subset],
  apply @finset.ssubset_of_ssubset_of_subset _ _ (s \ t),
  assumption,
  apply finset.sdiff_subset,
  refl,
  
  use u₁, split,
  simp only[set.mem_sep_iff],
  split, assumption,
  split,
  apply X.subset_closed (t ∪ (s \ t ∪ u₁)),
  assumption,
  rw [←finset.union_assoc, finset.union_sdiff_self_eq_union, finset.union_assoc],
  apply finset.subset_union_right,

  rw [←finset.subset_empty],
  apply @finset.subset.trans _ _ ((t ∪ (s \ t)) ∩ u₁),
  rw [finset.union_sdiff_self_eq_union, finset.inter_distrib_right],
  apply finset.subset_union_right,
  rw [finset.subset_empty, finset.inter_distrib_right, finset.union_eq_empty_iff],
  split; assumption,

  assumption,
  
  split, right,
  rw [join_proj_disj_union_mem],

  use t₂, split,
  rw [join_proj_mem],
  use ∅, split, apply simplicial_complex_empty_simplex,
  use t₂, split,
  assumption,
  symmetry,
  apply finset.empty_union,
  
  use (u₃ ∪ u₂), split,
  rw [join_proj_mem],
  use u₃, split, assumption,
  use u₂, split,
  rw [simplex_boundary_mem_iff_subset],
  apply @finset.ssubset_of_ssubset_of_subset _ _ (s \ t),
  assumption,
  apply finset.sdiff_subset,
  refl,

  use t₁, split, assumption,

  use u₁, split,
  simp only[set.mem_sep_iff],
  split, assumption,
  split,
  apply X.subset_closed (t ∪ (s \ t ∪ u₁)),
  assumption,
  rw [←finset.union_assoc, finset.union_sdiff_self_eq_union, finset.union_assoc],
  apply finset.subset_union_right,

  rw [←finset.subset_empty],
  apply @finset.subset.trans _ _ ((t ∪ (s \ t)) ∩ u₁),
  rw [finset.union_sdiff_self_eq_union, finset.inter_distrib_right],
  apply finset.subset_union_right,
  rw [finset.subset_empty, finset.inter_distrib_right, finset.union_eq_empty_iff],
  split; assumption,

  split,
  rw [finset.union_comm],
  assumption,

  split, assumption,

  split,
  rw [join_proj_disj_union_mem],
  use ∅, split, apply simplicial_complex_empty_simplex,
  use u₃, split, assumption,
  use t₂, split,
  assumption,
  use u₂, split,
  rw [simplex_boundary_mem_iff_subset],
  apply @finset.ssubset_of_ssubset_of_subset _ _ (s \ t),
  assumption,
  apply finset.sdiff_subset,

  split,
  symmetry,
  apply finset.empty_union,

  split, refl,
  
  split,
  rw [finset.empty_union],
  assumption,

  rw [simplex_boundary_mem_iff_subset],
  rw [t_decomp, finset.sdiff_union_distrib, st₁_sdiff_ident, finset.inter_sdiff, finset.inter_self] at u₂_in_bd,
  rw [finset.ssubset_iff_subset_ne] at t₂_in_bd u₂_in_bd ⊢,
  choose t₂_ss_s t₂_ne_s using t₂_in_bd,
  choose u₂_ss_st₂ u₂_ne_st₂ using u₂_in_bd,
  split,
  apply finset.union_subset,
  assumption,
  apply @finset.subset.trans _ _ (s \ t₂),
  assumption,
  apply finset.sdiff_subset,

  have st₂u₂_ne : s \ (t₂ ∪ u₂) ≠ ∅, from
  begin
    rw [ne.def, finset.sdiff_union_distrib, ←finset.sdiff_sdiff_left', finset.sdiff_eq_empty_iff_subset],
    rw [←finset.le_iff_subset] at u₂_ss_st₂ ⊢,
    have H : u₂ < s \ t₂, from
    begin
      rw [lt_iff_le_and_ne],
      split; assumption,
    end,
    rw [finset.partial_order.lt_iff_le_not_le] at H,
    choose H1 H2 using H,
    assumption,
  end,

  rw [ne.def, finset.ext_iff, not_forall],
  rw [ne.def, finset.eq_empty_iff_forall_not_mem, not_forall] at st₂u₂_ne,
  choose y y_nin_st₂u₂ using st₂u₂_ne,
  use y,
  simp only[not_iff, finset.mem_sdiff, finset.mem_union, not_and_distrib, not_or_distrib, not_not] at y_nin_st₂u₂ ⊢,
  choose y_in_s y_nin_t₂u₂ using y_nin_st₂u₂,
  split; intros; assumption,

  simp only[set.mem_sep_iff],
  split,
  apply X.subset_closed (t ∪ u₁),
  assumption,
  rw [t_decomp, finset.union_comm t₁ t₂, finset.union_assoc],
  apply finset.subset_union_right,

  split,
  apply X.subset_closed (t ∪ (s \ t ∪ u₁)),
  assumption,
  rw [←finset.union_assoc t (s \ t), finset.union_sdiff_self_eq_union, t_decomp],
  rw [finset.union_comm (t₁ ∪ t₂) s, finset.union_comm t₁ t₂],
  rw [←finset.union_assoc s t₂, finset.union_assoc (s ∪ t₂)],
  apply finset.union_subset_union_left,
  apply finset.subset_union_left,

  rw [finset.inter_distrib_left, finset.union_eq_empty_iff],
  split, assumption,
  rw [←finset.subset_empty],
  apply @finset.subset.trans _ _ ((t ∪ (s \ t)) ∩ u₁),
  rw [finset.union_sdiff_self_eq_union, finset.inter_distrib_right],
  apply finset.subset_union_right,
  rw [finset.subset_empty, finset.inter_distrib_right, finset.union_eq_empty_iff],
  split; assumption,

  simp only[t_decomp, u_decomp, finset.inter_distrib_left, finset.inter_distrib_right, finset.union_eq_empty_iff],
  split, split, split,
  
  rw [←finset.disjoint_iff_inter_eq_empty],
  apply @disjoint_complexes_disjoint_simplices _ _ (Lk(X, s) s_in_X) (simplex {x}),
  simp only[link, set.mem_sep_iff],
  split, assumption,
  split; assumption,
  assumption,

  apply barycenter_disjoint_link X s x s_in_X x_nin_X,
  
  rw [←finset.disjoint_iff_inter_eq_empty],
  apply @disjoint_complexes_disjoint_simplices _ _ (Lk(X, s) s_in_X) (∂s),
  simp only[link, set.mem_sep_iff],
  split, assumption,
  split; assumption,
  apply @set.mem_of_subset_of_mem _ (∂(s \ t)).simplices,
  apply subsimplex_boundary_subcomplex,
  apply finset.sdiff_subset,
  assumption,
  apply boundary_disjoint_link,

  rw [←finset.subset_empty],
  apply @finset.subset.trans _ _ (t ∩ u₁),
  rw [t_decomp, finset.union_comm, finset.inter_distrib_right],
  apply finset.subset_union_right,
  rw [finset.subset_empty],
  assumption,
  
  split, split,
  rw [←finset.disjoint_iff_inter_eq_empty],
  apply @disjoint_complexes_disjoint_simplices _ _ (∂s) (simplex {x}),
  rw [simplex_boundary_mem_iff_subset],
  assumption,
  assumption,
  apply @disjoint.symm _ _ _ (vertices (simplex {x})) (vertices (∂s)),
  apply barycenter_disjoint_boundary X s x s_in_X x_nin_X,

  rw [t_decomp, finset.sdiff_union_distrib, st₁_sdiff_ident, finset.inter_sdiff, finset.inter_self, finset.ssubset_iff_subset_ne] at u₂_in_bd,
  choose u₂_ss_st₂ u₂_ne_st₂ using u₂_in_bd,
  rw [finset.subset_iff] at u₂_ss_st₂,
  rw [finset.eq_empty_iff_forall_not_mem],
  intro y,
  by_cases H : y ∈ u₂,

  specialize u₂_ss_st₂ H,
  simp only[finset.mem_sdiff] at u₂_ss_st₂,
  choose y_in_s y_nin_t₂ using u₂_ss_st₂,
  simp only[finset.mem_inter, not_and_distrib],
  left, assumption,
  
  simp only[finset.mem_inter, not_and_distrib],
  right, assumption,
  
  rw [←finset.disjoint_iff_inter_eq_empty],
  apply @disjoint_complexes_disjoint_simplices _ _ (∂s) (Lk(X, s) s_in_X),
  rw [simplex_boundary_mem_iff_subset],
  assumption,

  simp only[link, set.mem_sep_iff],
  split, assumption,
  split,
  apply X.subset_closed (t ∪ (s \ t ∪ u₁)),
  assumption,
  rw [←finset.union_assoc, finset.union_sdiff_self_eq_union, finset.union_assoc],
  apply finset.subset_union_right,

  rw [←finset.subset_empty],
  apply @finset.subset.trans _ _ ((t ∪ (s \ t)) ∩ u₁),
  rw [finset.union_sdiff_self_eq_union, finset.inter_distrib_right],
  apply finset.subset_union_right,
  rw [finset.subset_empty, finset.inter_distrib_right, finset.union_eq_empty_iff],
  split; assumption,
  
  apply @disjoint.symm _ _ _ (vertices (Lk(X, s) s_in_X)) (vertices (∂s)),
  apply boundary_disjoint_link X s s_in_X,
end

lemma stellar_subdiv_anticomm_link_right
    (X : simplicial_complex α)
    (s t : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (t_in_X : t ∈ X.simplices)
    (t_in_star_bd : t ∈ (π₁ (boundary_disjoint_link X s s_in_X)[(Lk(X, s) s_in_X) ⋆ ∂s]).simplices)
  : (σ((Lk(X, t) t_in_X), s\t, x;
        (star_boundary_diff_ne t_in_star_bd),
        (star_boundary_mem_link t_in_star_bd),
        (not_mem_link_vertices x_nin_X))).simplices
      ⊆ (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), t) (star_boundary_mem_subdiv t_in_star_bd)).simplices
:= begin
  simp only[stellar_subdivision, simplicial_union],
  simp only[set.subset_def],
  intros u u_in_subdiv,

  simp only[set.mem_union] at u_in_subdiv,
  cases u_in_subdiv with u_in_star_comp u_in_join, -- Cases E + F, resp.

  apply stellar_subdiv_anticomm_link_right_e; assumption,
  apply stellar_subdiv_anticomm_link_right_f; assumption,
end

lemma stellar_subdiv_anticomm_link
    (X : simplicial_complex α)
    (s t : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (t_in_X : t ∈ X.simplices)
    (t_in_star_bd : t ∈ (π₁ (boundary_disjoint_link X s s_in_X)[(Lk(X, s) s_in_X) ⋆ ∂s]).simplices)
  : (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), t) (star_boundary_mem_subdiv t_in_star_bd)).simplices
      = (σ((Lk(X, t) t_in_X), s\t, x;
          (star_boundary_diff_ne t_in_star_bd),
          (star_boundary_mem_link t_in_star_bd),
          (not_mem_link_vertices x_nin_X))).simplices
:= begin
  apply set.eq_of_subset_of_subset,
  apply stellar_subdiv_anticomm_link_left,
  apply stellar_subdiv_anticomm_link_right,
end