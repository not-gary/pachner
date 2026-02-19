import Pachner.Stellar.StellarSubdivision

variable {E 𝕜 : Type _}
  [DecidableEq E]
  [DecidableEq 𝕜] [Ring 𝕜] [Nontrivial 𝕜]
  {X : AbstractSimplicialComplex E} {s t : Finset E} {x : E}

theorem star_boundary_diff_ne
    (s_in_X : s ∈ X.faces)
  : t ∈ ((π₁[𝕜] (disjoint_link_boundary X s)).coe ''ˢ (Lk(X, s) ⋆ ∂s)).faces →
      Nonempty ↥(s \ t) :=
by
  intro t_in_star_bd
  rw [simplicialJoinProj_mem] at t_in_star_bd
  choose t₁ t₁_in_link t₂ t₂_in_bd t_decomp t_ne using t_in_star_bd
  simp only [Link, Set.mem_sep_iff, Set.mem_union, Set.mem_singleton_iff] at t₁_in_link
  cases' t₁_in_link with t₁_in_link t₁_empty

  choose t₁_in_X st₁_in_X st₁_disj using t₁_in_link
  rw [Set.mem_union, Set.mem_singleton_iff, faceBoundary_mem_iff_subset] at t₂_in_bd
  rw [Finset.nonempty_coe_sort, Finset.sdiff_nonempty]
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
  have s_ne : Nonempty { x // x ∈ s } := by
    rw [Finset.nonempty_coe_sort, Finset.nonempty_iff_ne_empty]
    exact face_nonempty s_in_X
  simp only [Finset.nonempty_coe_sort, Finset.nonempty_iff_ne_empty, ne_eq, Finset.eq_empty_iff_forall_notMem,
    not_forall, not_not] at s_ne
  choose a a_in_s using s_ne
  use a; use a_in_s
  specialize st₁_disj a a_in_s
  assumption

  rw [t₁_empty, Finset.empty_union] at t_decomp
  subst t_decomp
  rw [Set.mem_union, Set.mem_singleton_iff, faceBoundary_mem_iff_subset] at t₂_in_bd
  cases' t₂_in_bd with t_in_bd t_empty

  rw [Finset.nonempty_coe_sort, Finset.sdiff_nonempty]
  simp only [Finset.subset_iff, Classical.not_forall]
  rw [Finset.ssubset_iff] at t_in_bd
  choose t_in_bd t_ne using t_in_bd
  choose a a_nin_t at_ss_s using t_in_bd
  rw [Finset.subset_iff] at at_ss_s
  specialize at_ss_s (Finset.mem_insert_self a t)
  use a

  contradiction

theorem star_boundary_mem_subdiv
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
  : t ∈ ((π₁[𝕜] (disjoint_link_boundary X s)).coe ''ˢ (Lk(X, s) ⋆ ∂s)).faces →
      t ∈ σ(X, s, x; 𝕜, s_in_X, x_nin_X).faces :=
by
  intro t_in_star_bd
  rw [simplicialJoinProj_mem] at t_in_star_bd
  choose t₁ t₁_in_link t₂ t₂_in_bd t_decomp t_ne using t_in_star_bd
  simp only [StellarSubdivision, AbstractSimplicialComplex.instHasUnion, SimplicialUnion, Set.mem_union, simplicialJoinProj_mem]
  right
  use t₂
  cases' t₁_in_link with t₁_in_link t₁_empty
  · cases' t₂_in_bd with t₂_in_bd t₂_empty
    -- t₁ nonempty, t₂ nonempty
    · constructor
      · left
        use ∅
        constructor; right; rfl
        use t₂
        constructor; left; assumption
        rw [Finset.empty_union]
        constructor; rfl
        revert t₂_in_bd
        contrapose
        rw [ne_eq, not_not]
        intro t₂_empty
        subst t₂_empty
        apply (∂s).empty_notMem
      · use t₁
        rw [Finset.union_comm]
        exact ⟨by left; assumption, by assumption, by assumption⟩
    -- t₁ nonempty, t₂ empty
    · subst t₂_empty
      rw [Finset.union_empty] at t_decomp
      subst t_decomp
      constructor; right; rfl
      use t
      rw [Finset.empty_union]
      exact ⟨by left; assumption, by rfl, by assumption⟩
  · cases' t₂_in_bd with t₂_in_bd t₂_empty
    -- t₁ empty, t₂ nonempty
    · subst t₁_empty
      rw [Finset.empty_union] at t_decomp
      subst t_decomp
      constructor
      · left
        use ∅
        constructor; right; rfl
        use t
        rw [Finset.empty_union]
        exact ⟨by left; assumption, by rfl, by assumption⟩
      · use ∅
        rw [Finset.union_empty]
        exact ⟨by right; rfl, by rfl, by assumption⟩
    -- t₁ empty, t₂ empty
    · subst t₁_empty t₂_empty
      rw [Finset.empty_union] at t_decomp
      contradiction
