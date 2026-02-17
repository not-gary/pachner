import Pachner.Stellar.StellarSubdivision

variable {E 𝕜: Type _}
variable [DecidableEq E] [DecidableEq 𝕜]
variable [AddCommGroup E]
variable [Ring 𝕜] [Nontrivial 𝕜]

theorem star_boundary_is_join_left
    {X : AbstractSimplicialComplex E}
    {s : Finset E} [s_ne : Nonempty s]
    {x : E}
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
  : (X\St(X, s) ∩
      ((π₁[𝕜] (@disjoint_barycenter_join_boundary_link _ 𝕜 _ _ _ _ _ _ _ _ s_in_X x_nin_X)).coe
        ''ˢ (((π₁[𝕜] (disjoint_barycenter_boundary s_in_X x_nin_X)).coe
          ''ˢ (simplex {x} ⋆ ∂s)) ⋆
              Lk(X, s)))) ⊆
      ((π₁[𝕜] (disjoint_link_boundary X s)).coe ''ˢ (Lk(X, s) ⋆ ∂s)) :=
by
  intro t t_in_inter
  simp only [AbstractSimplicialComplex.instHasInter, SimplicialInter, Set.mem_inter_iff] at t_in_inter
  choose t_in_star_comp t_in_join using t_in_inter
  simp only [simplicialJoinProj_mem] at t_in_join
  choose t' t'_in_join t₁ t₁_in_link t_decomp t_ne using t_in_join

  rw [Set.mem_union, Set.mem_singleton_iff, simplicialJoinProj_mem] at t'_in_join
  cases' t'_in_join with t'_in_join t'_empty

  choose t₃ t₃_in_barycenter t₂ t₂_in_bd t'_decomp t'_ne using t'_in_join
  subst t'_decomp
  simp only [StarComplement, Set.mem_sep_iff] at t_in_star_comp
  choose t_in_X s_nss_t using t_in_star_comp
  have t₃_empty : t₃ = ∅ :=
  by
    simp only [simplex, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at t₃_in_barycenter
    cases' t₃_in_barycenter with t₃_eq_x t₃_empty
    choose t₃_eq_x t₃_ne using t₃_eq_x
    cases' t₃_eq_x with t₃_empty t₃_eq_x
    contradiction
    have contra : x ∈ X.vertices :=
    by
      rw [AbstractSimplicialComplex.mem_vertices]
      apply @X.down_closed t
      assumption
      rw [← t₃_eq_x, t_decomp, Finset.union_assoc]
      apply Finset.subset_union_left
      apply Finset.singleton_ne_empty
    contradiction
    assumption
  subst t₃_empty
  rw [Finset.empty_union] at t_decomp
  rw [simplicialJoinProj_mem]
  use t₁; constructor; assumption
  use t₂; constructor; assumption
  rw [Finset.union_comm]
  constructor <;> assumption

  subst t'_empty
  rw [Finset.empty_union] at t_decomp
  subst t_decomp
  rw [simplicialJoinProj_mem]
  use t; constructor; assumption
  use ∅; constructor
  rw [Set.mem_union]
  right; apply Set.mem_singleton
  constructor
  rw [Finset.union_empty]
  assumption

theorem star_boundary_is_join_right
    {X : AbstractSimplicialComplex E}
    {s : Finset E} [s_ne : Nonempty s]
    {x : E}
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
  : ((π₁[𝕜] (disjoint_link_boundary X s)).coe ''ˢ (Lk(X, s) ⋆ ∂s)) ⊆
      (X\St(X, s) ∩
        ((π₁[𝕜] (@disjoint_barycenter_join_boundary_link _ 𝕜 _ _ _ _ _ _ _ _ s_in_X x_nin_X)).coe
            ''ˢ ((π₁[𝕜] (disjoint_barycenter_boundary s_in_X x_nin_X)).coe
              ''ˢ (simplex {x} ⋆ ∂s) ⋆
                Lk(X, s)))) :=
by
  intro t t_in_join
  rw [simplicialJoinProj_mem] at t_in_join
  choose t₁ t₁_in_link t₂ t₂_in_bd t_decomp t_ne using t_in_join
  simp only [AbstractSimplicialComplex.instHasInter, SimplicialInter, Set.mem_inter_iff]
  constructor
  simp only [StarComplement, Set.mem_sep_iff]
  simp only [Link, Set.mem_union, Set.mem_singleton_iff, Set.mem_sep_iff] at t₁_in_link
  cases' t₁_in_link with t₁_in_link t₁_empty

  choose t₁_in_X st₁_in_X st₁_disj using t₁_in_link
  rw [Set.mem_union, Set.mem_singleton_iff, simplexBoundary_mem_iff_subset] at t₂_in_bd
  constructor
  rw [Finset.ssubset_iff_subset_ne] at t₂_in_bd
  cases' t₂_in_bd with t₂_in_bd t₂_empty

  choose t₂_ss_s t₂_ne using t₂_in_bd
  choose t₂_ss_s t₂_ne_s using t₂_ss_s
  apply @X.down_closed (s ∪ t₁)
  assumption
  rw [t_decomp, Finset.union_comm]
  apply Finset.union_subset_union_left
  assumption
  assumption

  rw [t₂_empty, Finset.union_empty] at t_decomp
  subst t_decomp
  assumption

  simp only [Finset.subset_iff, Classical.not_forall]
  rw [Finset.ssubset_iff] at t₂_in_bd
  cases' t₂_in_bd with t₂_in_bd t₂_empty

  choose t₂_in_bd t₂_ne using t₂_in_bd
  choose a a_nin_t₂ at₂_ss_s using t₂_in_bd
  rw [Finset.subset_iff] at at₂_ss_s
  specialize at₂_ss_s (Finset.mem_insert_self a t₂)
  use a; constructor
  simp only [Finset.eq_empty_iff_forall_notMem, Finset.mem_inter, not_and] at st₁_disj
  specialize st₁_disj a at₂_ss_s
  simp only [t_decomp, Finset.mem_union, not_or]
  constructor <;> assumption
  assumption

  rw [t₂_empty, Finset.union_empty] at t_decomp
  subst t_decomp
  simp only [Finset.eq_empty_iff_forall_notMem, Finset.mem_inter, not_and] at st₁_disj
  simp only [Finset.nonempty_coe_sort, Finset.nonempty_iff_ne_empty, ne_eq, Finset.eq_empty_iff_forall_notMem,
    not_forall, not_not] at s_ne
  choose a a_in_s using s_ne
  use a; use a_in_s
  specialize st₁_disj a a_in_s
  assumption

  subst t₁_empty
  rw [Finset.empty_union] at t_decomp
  subst t_decomp
  rw [Set.mem_union, Set.mem_singleton_iff] at t₂_in_bd
  cases' t₂_in_bd with t₂_in_bd t₂_empty

  simp only [simplexBoundary_mem_iff_subset] at t₂_in_bd
  choose t_sss_s t_ne using t₂_in_bd
  rw [Finset.ssubset_def] at t_sss_s
  choose t_ss_s s_nss_t using t_sss_s
  constructor
  apply @X.down_closed s
  assumption
  assumption
  assumption
  assumption
  contradiction

  simp only [simplicialJoinProj_mem, Set.mem_union, Set.mem_singleton_iff]
  use ∅ ∪ t₂; constructor
  rw [Set.mem_union, Set.mem_singleton_iff] at t₂_in_bd
  cases' t₂_in_bd with t₂_in_bd t₂_empty

  left; use ∅; constructor; right; rfl
  use t₂; constructor; left; assumption
  constructor; rfl
  rw [Finset.empty_union]
  exact face_nonempty t₂_in_bd

  right; rw [t₂_empty, Finset.empty_union]

  use t₁; constructor; assumption
  rw [Finset.empty_union, Finset.union_comm, t_decomp]
  constructor; rfl
  rw [← t_decomp]
  assumption

theorem star_boundary_is_join
    (X : AbstractSimplicialComplex E)
    (s : Finset E) [s_ne : Nonempty s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
  : (X\St(X, s) ∩
      ((π₁[𝕜] (@disjoint_barycenter_join_boundary_link _ 𝕜 _ _ _ _ _ _ _ _ s_in_X x_nin_X)).coe
        ''ˢ (((π₁[𝕜] (disjoint_barycenter_boundary s_in_X x_nin_X)).coe
          ''ˢ (simplex {x} ⋆ ∂s)) ⋆
              Lk(X, s)))) =
      ((π₁[𝕜] (disjoint_link_boundary X s)).coe ''ˢ (Lk(X, s) ⋆ ∂s)) :=
by
  rw [AbstractSimplicialComplex.ext_iff, Set.Subset.antisymm_iff]
  exact ⟨star_boundary_is_join_left s_in_X x_nin_X, star_boundary_is_join_right s_in_X x_nin_X⟩
