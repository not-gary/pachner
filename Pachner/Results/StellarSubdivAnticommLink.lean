import Pachner.Stellar.StellarSubdivision

variable {E 𝕜 : Type _}
variable [DecidableEq E] [DecidableEq 𝕜]
variable [AddCommGroup E]
variable [Ring 𝕜] [Nontrivial 𝕜]

theorem star_boundary_mem_link
    {X : AbstractSimplicialComplex E}
    {s t : Finset E}
    {s_in_X : s ∈ X.faces}
  : t ∈ ((π₁[𝕜] (disjoint_link_boundary X s)).coe ''ˢ (Lk(X, s) ⋆ ∂s)).faces →
      s \ t ∈ Lk(X, t).faces :=
by
  intro t_in_star_bd
  rw [simplicialJoinProj_mem] at t_in_star_bd
  choose t₁ t₁_in_link t₂ t₂_in_bd t_decomp t_ne using t_in_star_bd
  simp only [Link, Set.mem_sep_iff, Set.mem_union, Set.mem_singleton_iff] at t₁_in_link ⊢
  cases' t₁_in_link with t₁_in_link t₁_empty

  choose t₁_in_X st₁_in_X st₁_disj using t₁_in_link
  constructor
  apply @X.down_closed s
  assumption
  apply Finset.sdiff_subset
  have st₁_eq_s : s \ t₁ = s :=
  by
    rw [Finset.sdiff_eq_self_iff_disjoint, Finset.disjoint_iff_inter_eq_empty]
    assumption
  rw [t_decomp, Finset.sdiff_union_distrib, ne_eq, st₁_eq_s, ← Finset.inter_sdiff_assoc, Finset.inter_self]
  rw [Set.mem_union, Set.mem_singleton_iff, simplexBoundary_mem_iff_subset] at t₂_in_bd
  cases' t₂_in_bd with t₂_in_bd t₂_empty

  choose t₂_sss_s t₂_ne using t₂_in_bd
  rw [Finset.sdiff_eq_empty_iff_subset]
  rw [Finset.ssubset_iff] at t₂_sss_s
  choose a a_nin_t₂ at₂_ss_s using t₂_sss_s
  rw [Finset.subset_iff] at at₂_ss_s ⊢
  specialize at₂_ss_s (Finset.mem_insert_self a t₂)
  simp only [not_forall, Classical.not_imp]
  use a

  rw [t₂_empty, Finset.sdiff_empty]
  exact face_nonempty s_in_X

  constructor
  rw [Finset.union_sdiff_self_eq_union, t_decomp, Finset.union_assoc]
  simp only [SimplexBoundary, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe,
    Finset.mem_powerset] at t₂_in_bd
  cases' t₂_in_bd with t₂_in_bd t₂_empty
  choose t₂_ss_s t₂_ne_s using t₂_in_bd
  have st₂_rw : t₂ ∪ s = s := by
    rw [Finset.union_eq_right]
    assumption
  rw [st₂_rw, Finset.union_comm]
  assumption
  rw [t₂_empty, Finset.empty_union, Finset.union_comm]
  assumption
  apply Finset.inter_sdiff_self

  constructor
  apply @X.down_closed s
  assumption
  apply Finset.sdiff_subset
  have st₁_eq_s : s \ t₁ = s :=
  by
    rw [Finset.sdiff_eq_self_iff_disjoint, Finset.disjoint_iff_inter_eq_empty, t₁_empty, Finset.inter_empty]
  rw [t_decomp, Finset.sdiff_union_distrib, ne_eq, st₁_eq_s, ← Finset.inter_sdiff_assoc, Finset.inter_self]
  rw [Set.mem_union, Set.mem_singleton_iff, simplexBoundary_mem_iff_subset] at t₂_in_bd
  cases' t₂_in_bd with t₂_in_bd t₂_empty

  choose t₂_sss_s t₂_ne using t₂_in_bd
  rw [Finset.sdiff_eq_empty_iff_subset]
  rw [Finset.ssubset_iff] at t₂_sss_s
  choose a a_nin_t₂ at₂_ss_s using t₂_sss_s
  rw [Finset.subset_iff] at at₂_ss_s ⊢
  specialize at₂_ss_s (Finset.mem_insert_self a t₂)
  simp only [not_forall, Classical.not_imp]
  use a

  rw [t₂_empty, Finset.sdiff_empty]
  exact face_nonempty s_in_X

  constructor
  rw [Finset.union_sdiff_self_eq_union, t_decomp, Finset.union_assoc]
  simp only [SimplexBoundary, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe,
    Finset.mem_powerset] at t₂_in_bd
  cases' t₂_in_bd with t₂_in_bd t₂_empty
  choose t₂_ss_s t₂_ne_s using t₂_in_bd
  have st₂_rw : t₂ ∪ s = s := by
    rw [Finset.union_eq_right]
    assumption
  rw [st₂_rw, Finset.union_comm, t₁_empty, Finset.union_empty]
  assumption
  rw [t₂_empty, Finset.empty_union, t₁_empty, Finset.empty_union]
  assumption
  apply Finset.inter_sdiff_self

theorem not_mem_link_vertices
    {X : AbstractSimplicialComplex E}
    {s : Finset E}
    {x : E}
  : x ∉ X.vertices → x ∉ Lk(X, s).vertices :=
by
  contrapose
  simp only [Classical.not_not]
  apply isSubcomplex_vertices
  apply link_subcomplex

theorem stellar_subdiv_anticomm_link_left_ac
    (X : AbstractSimplicialComplex E)
    (s t : Finset E)
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (t_in_star_bd : t ∈ ((π₁[𝕜] (disjoint_link_boundary X s)).coe ''ˢ (Lk(X, s) ⋆ ∂s)).faces)
  : ∀ u : Finset E,
      u ∈ (StarComplement X s).faces →
        t ∪ u ∈ (StarComplement X s).faces →
          t ∩ u = ∅ →
            u ∈
              σ(Lk(X, t), s \ t, x; 𝕜,
                @star_boundary_mem_link _ _ _ _ _ _ _ X s t s_in_X t_in_star_bd,
                not_mem_link_vertices x_nin_X).faces :=
by
  intro u u_in_star_comp tu_in_star_comp tu_disj
  simp only [Link, StellarSubdivision, StarComplement, SimplicialUnion] at u_in_star_comp tu_in_star_comp ⊢
  simp only [Set.mem_union, Set.mem_sep_iff] at u_in_star_comp tu_in_star_comp ⊢
  choose u_in_X s_nss_u using u_in_star_comp
  choose tu_in_X s_nss_tu using tu_in_star_comp
  have st_nss_u : ¬s \ t ⊆ u := by
    revert s_nss_tu
    contrapose
    simp only [Classical.not_not]
    intro st_ss_u
    apply @Finset.union_subset_left _ _ s t
    rw [← Finset.union_sdiff_self_eq_union, Finset.union_sdiff_symm]
    apply Finset.union_subset_union_right
    assumption
  left; constructor; constructor
  assumption
  constructor <;> assumption
  assumption

theorem stellar_subdiv_anticomm_link_left_ad_tu_in_X
    (X : AbstractSimplicialComplex E)
    (s t u t₁ u₁ t₂ u₂ : Finset E)
    (stu₁_in_X : s ∪ (t₁ ∪ u₁) ∈ X.faces)
    (t₂_in_bd : t₂ ⊂ s)
    (u₂_in_bd : u₂ ⊂ s)
    (t_decomp : t = t₁ ∪ t₂)
    (u_decomp : u = u₁ ∪ u₂)
  : t ∪ u ≠ ∅ → t ∪ u ∈ X.faces :=
by
  intro tu_ne
  rw [u_decomp, t_decomp]
  by_cases t_ne : t = ∅
  by_cases u_ne : u = ∅

  rw [t_ne, u_ne, Finset.union_empty] at tu_ne
  contradiction

  apply @X.down_closed (t₁ ∪ u₁ ∪ s)
  rw [Finset.union_comm]
  exact stu₁_in_X
  have tu_ss_s : t₂ ∪ u₂ ⊆ s :=
    by
    apply Finset.union_subset <;> rw [Finset.ssubset_iff_subset_ne] at t₂_in_bd u₂_in_bd
    choose t₂_ss_s t₂_ne_s using t₂_in_bd
    exact t₂_ss_s
    choose u₂_ss_s u₂_ne_s using u₂_in_bd
    exact u₂_ss_s
  rw [Finset.union_assoc, Finset.union_comm u₁ u₂, ← Finset.union_assoc t₂,
    Finset.union_comm (t₂ ∪ u₂), ← Finset.union_assoc]
  apply Finset.union_subset_union_right
  exact tu_ss_s

  rw [ne_eq, Finset.union_eq_empty, not_and_or]
  right; rw [← u_decomp]; assumption

  apply @X.down_closed (t₁ ∪ u₁ ∪ s)
  rw [Finset.union_comm]
  exact stu₁_in_X
  have tu_ss_s : t₂ ∪ u₂ ⊆ s :=
  by
    apply Finset.union_subset <;> rw [Finset.ssubset_iff_subset_ne] at t₂_in_bd u₂_in_bd
    choose t₂_ss_s t₂_ne_s using t₂_in_bd
    exact t₂_ss_s
    choose u₂_ss_s u₂_ne_s using u₂_in_bd
    exact u₂_ss_s
  rw [Finset.union_assoc, Finset.union_comm u₁ u₂, ← Finset.union_assoc t₂,
    Finset.union_comm (t₂ ∪ u₂), ← Finset.union_assoc]
  apply Finset.union_subset_union_right
  exact tu_ss_s

  rw [ne_eq, Finset.union_eq_empty, not_and_or]
  left; rw [← t_decomp]; assumption

theorem stellar_subdiv_anticomm_link_left_ad_st_nss_u
    (X : AbstractSimplicialComplex E)
    (s t u t₁ u₁ t₂ u₂ : Finset E) [s_ne : Nonempty ↥s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (t_in_X : t ∈ X.faces)
    (u_in_X : u ∈ X.faces)
    (tu_disj : t ∩ u = ∅)
    (su₁_disj : s ∩ u₁ = ∅)
    (tu_in_join : t₂ ∪ u₂ ∈ ((π₁[𝕜] (disjoint_barycenter_boundary s_in_X x_nin_X)).coe ''ˢ (simplex {x} ⋆ ∂s)).faces ∪ {∅})
    (t_decomp : t = t₁ ∪ t₂)
    (u_decomp : u = u₁ ∪ u₂)
  : ¬s \ t₂ ⊆ u :=
by
  rw [Set.mem_union, Set.mem_singleton_iff, simplicialJoinProj_union_mem] at tu_in_join
  cases' tu_in_join with tu_in_join tu_empty
  · choose t₃ t₃_in_barycenter u₃ u₃_in_barycenter t₂ t₂_in_bd u₂ u₂_in_bd tu₂_decomp using tu_in_join
    choose t₂_decomp u₂_decomp tu₃_in_barycenter tu₂_in_bd using tu₂_decomp
    have u₃_empty : u₃ = ∅ :=
    by
      simp only [simplex, Set.mem_union, Set.mem_singleton_iff, Set.mem_diff, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at u₃_in_barycenter
      cases' u₃_in_barycenter with u₃_in_barycenter u₃_empty
      · choose u₃_eq_x u₃_ne using u₃_in_barycenter
        cases' u₃_eq_x with u₃_empty u₃_eq_x; contradiction
        have contra : x ∈ X.vertices :=
        by
          rw [AbstractSimplicialComplex.mem_vertices]
          apply X.down_closed u_in_X
          rw [u_decomp, u₂_decomp, u₃_eq_x, ← Finset.union_assoc, Finset.union_comm u₁ {x},
            Finset.union_assoc]
          apply Finset.subset_union_left
          apply Finset.singleton_ne_empty
        contradiction
      · assumption
    have t₃_empty : t₃ = ∅ :=
    by
      simp only [simplex, Set.mem_union, Set.mem_singleton_iff, Set.mem_diff, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at t₃_in_barycenter
      cases' t₃_in_barycenter with t₃_in_barycenter t₃_empty
      · choose t₃_eq_x t₃_ne using t₃_in_barycenter
        cases' t₃_eq_x with t₃_empty t₃_eq_x; contradiction
        have contra : x ∈ X.vertices :=
        by
          rw [AbstractSimplicialComplex.mem_vertices]
          apply X.down_closed t_in_X
          rw [t_decomp, t₂_decomp, t₃_eq_x, ← Finset.union_assoc, Finset.union_comm t₁ {x},
            Finset.union_assoc]
          apply Finset.subset_union_left
          apply Finset.singleton_ne_empty
        contradiction
      · assumption
    subst u₃
    subst t₃
    rw [Finset.empty_union] at t₂_decomp u₂_decomp tu₃_in_barycenter

    choose tu₂_in_bd tu₂_ne using tu₂_in_bd
    rw [← u₂_decomp, ← t₂_decomp, Set.mem_union, Set.mem_singleton_iff, simplexBoundary_mem_iff_subset] at tu₂_in_bd
    cases' tu₂_in_bd with tu₂_in_bd tu₂_empty
    · subst u₂_decomp
      subst t₂_decomp
      have u₂_ss_st₂_sdiff : u₂ ⊂ s \ t₂ :=
      by
        rw [Finset.ssubset_iff_subset_ne] at tu₂_in_bd ⊢
        choose tu₂_sss_s tu₂_ne using tu₂_in_bd
        choose tu₂_ss_s tu₂_ne_s using tu₂_sss_s
        constructor
        rw [Finset.subset_sdiff]
        constructor
        apply @Finset.Subset.trans _ _ (t₂ ∪ u₂)
        apply Finset.subset_union_right
        exact tu₂_ss_s
        rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.subset_empty]
        rw [← tu_disj, t_decomp, u_decomp]
        rw [Finset.inter_comm]
        apply Finset.inter_subset_inter <;> apply Finset.subset_union_right
        rw [Finset.union_comm] at tu₂_ne_s
        have H1 : s = s ∪ t₂ :=
        by
          symm
          rw [Finset.union_eq_left]
          apply @subset_trans _ _ _ t₂ (t₂ ∪ u₂)
          apply Finset.subset_union_left
          assumption
        rw [H1] at tu₂_ne_s
        revert tu₂_ne_s
        contrapose
        simp only [not_ne_iff]
        rw [← @Finset.sdiff_union_self_eq_union _ _ s]
        exact congr_arg fun a : Finset E => a ∪ t₂
      rw [← Finset.lt_iff_ssubset, Preorder.lt_iff_le_not_ge, Finset.le_iff_subset,
        Finset.le_iff_subset] at u₂_ss_st₂_sdiff
      choose u₂_ss_st₂ st₂_nss_u₂ using u₂_ss_st₂_sdiff
      rw [Finset.not_subset] at st₂_nss_u₂ ⊢
      choose y y_in_st₂ y_nin_u₂ using st₂_nss_u₂
      use y; use y_in_st₂
      rw [u_decomp, Finset.notMem_union]
      constructor
      rw [Finset.eq_empty_iff_forall_notMem] at su₁_disj
      specialize su₁_disj y
      simp only [Finset.mem_inter, not_and_or] at su₁_disj
      cases' su₁_disj with contra y_nin_u₁
      have H : y ∈ s := by
        apply @Finset.mem_of_subset _ (s \ t₂)
        apply Finset.sdiff_subset
        exact y_in_st₂
      contradiction
      exact y_nin_u₁
      exact y_nin_u₂
    · contradiction
  · rw [Finset.union_eq_empty] at tu_empty
    choose t₂_empty u₂_empty using tu_empty
    simp only [u_decomp, t₂_empty, u₂_empty, Finset.sdiff_empty, Finset.union_empty, Finset.subset_iff,
      not_forall]
    rw [← Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_left] at su₁_disj
    simp only [Finset.nonempty_coe_sort, Finset.nonempty_iff_ne_empty, ne_eq, Finset.eq_empty_iff_forall_notMem,
      not_forall, not_not] at s_ne
    choose x x_in_s using s_ne
    use x; use x_in_s
    specialize su₁_disj x_in_s
    assumption

theorem stellar_subdiv_anticomm_link_left_ad
    (X : AbstractSimplicialComplex E)
    (s t : Finset E)
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (t_in_X : t ∈ X.faces)
    (t_in_star_bd : t ∈ ((π₁[𝕜] (disjoint_link_boundary X s)).coe ''ˢ (Lk(X, s) ⋆ ∂s)).faces)
  : ∀ u : Finset E,
      u ∈ (StarComplement X s).faces →
        t ∪ u ∈ ((π₁[𝕜] (@disjoint_barycenter_join_boundary_link _ 𝕜 _ _ _ _ _ _ _ _ s_in_X x_nin_X)).coe
                  ''ˢ (((π₁[𝕜] (disjoint_barycenter_boundary s_in_X x_nin_X)).coe
                    ''ˢ (simplex {x} ⋆ ∂s)) ⋆
                      Lk(X, s))).faces →
          t ∩ u = ∅ →
            u ∈ σ(Lk(X, t), s \ t, x; 𝕜,
                  @star_boundary_mem_link _ _ _ _ _ _ _ X s t s_in_X t_in_star_bd,
                  not_mem_link_vertices x_nin_X).faces :=
by
  intro u u_in_star_comp tu_in_join tu_disj
  simp only [Link, StellarSubdivision, StarComplement, AbstractSimplicialComplex.instHasUnion,
    SimplicialUnion] at u_in_star_comp tu_in_join ⊢
  simp only [Set.mem_union, Set.mem_setOf] at u_in_star_comp ⊢
  choose u_in_X s_nss_u using u_in_star_comp

  rw [simplicialJoinProj_union_mem] at tu_in_join
  choose t'₂ t'₂_in_join u'₂ u'₂_in_join t₁ t₁_in_link u₁ u₁_in_link tu_decomp using tu_in_join
  choose t_decomp u_decomp tu_in_join tu_in_link using tu_decomp
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf] at t₁_in_link u₁_in_link tu_in_link
  choose tu_in_link tu_ne using tu_in_link
  simp only [simplicialJoinProj_mem, Set.mem_union, Set.mem_singleton_iff] at u'₂_in_join t'₂_in_join

  have st₁u₁_in_X : s ∪ (t₁ ∪ u₁) ∈ X.faces :=
  by
    cases' tu_in_link with tu_in_link tu_empty
    · choose tu_in_X stu_in_X stu_disj using tu_in_link
      assumption
    · rw [Finset.union_eq_empty] at tu_empty
      choose t₁_empty u₁_empty using tu_empty
      simp only [t₁_empty, u₁_empty, Finset.union_empty]
      assumption

  have t'₂_sss_s : t'₂ ⊂ s :=
  by
    cases' t'₂_in_join with t'₂_in_join t'₂_empty
    · choose t₃ t₃_in_barycenter t₂ t₂_in_bd t'_decomp t'_ne using t'₂_in_join
      have t₃_empty : t₃ = ∅ :=
      by
        cases' t₃_in_barycenter with t₃_in_barycenter t₃_empty
        · simp only [simplex, Set.mem_diff_singleton, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at t₃_in_barycenter
          choose t₃_in_barycenter t₃_ne using t₃_in_barycenter
          cases' t₃_in_barycenter with t₃_empty t₃_eq_x; contradiction
          have contra : x ∈ X.vertices :=
          by
            rw [vertices_setOf, Set.mem_setOf]
            use t; constructor; assumption
            simp only [t_decomp, t'_decomp, t₃_eq_x, Finset.mem_union]
            left; left
            apply Finset.mem_singleton_self
          contradiction
        · assumption

      subst t'_decomp t₃_empty
      rw [Finset.empty_union] at t'_ne ⊢
      rw [simplexBoundary_mem_iff_subset] at t₂_in_bd
      cases' t₂_in_bd with t₂_in_bd t₂_empty
      · choose t₂_sss_s t₂_ne using t₂_in_bd
        assumption
      · contradiction
    · rw [t'₂_empty, Finset.empty_ssubset, Finset.nonempty_iff_ne_empty]
      exact face_nonempty s_in_X

  have u'₂_sss_s : u'₂ ⊂ s :=
  by
    cases' u'₂_in_join with u'₂_in_join u'₂_empty
    · choose u₃ u₃_in_barycenter u₂ u₂_in_bd u'_decomp u'_ne using u'₂_in_join
      have u₃_empty : u₃ = ∅ :=
      by
        cases' u₃_in_barycenter with u₃_in_barycenter u₃_empty
        · simp only [simplex, Set.mem_diff_singleton, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at u₃_in_barycenter
          choose u₃_in_barycenter u₃_ne using u₃_in_barycenter
          cases' u₃_in_barycenter with u₃_empty u₃_eq_x; contradiction
          have contra : x ∈ X.vertices :=
          by
            rw [vertices_setOf, Set.mem_setOf]
            use u; constructor; assumption
            simp only [Finset.mem_union, u_decomp, u'_decomp, u₃_eq_x]
            left; left
            apply Finset.mem_singleton_self
          contradiction
        · assumption

      subst u'_decomp u₃_empty
      rw [Finset.empty_union] at u'_ne ⊢
      rw [simplexBoundary_mem_iff_subset] at u₂_in_bd
      cases' u₂_in_bd with u₂_in_bd u₂_empty
      · choose u₂_sss_s u₂_ne using u₂_in_bd
        assumption
      · contradiction
    · rw [u'₂_empty, Finset.empty_ssubset, Finset.nonempty_iff_ne_empty]
      exact face_nonempty s_in_X

  have st₁_eq_s : s \ t₁ = s :=
  by
    cases' t₁_in_link with t₁_in_link t₁_empty
    · choose t₁_in_X st₁_in_X st₁_disj using t₁_in_link
      rw [Finset.sdiff_eq_self_iff_disjoint, Finset.disjoint_iff_inter_eq_empty]
      assumption
    · rw [t₁_empty, Finset.sdiff_empty]

  cases' t'₂_in_join with t'₂_in_join t'₂_empty
  · choose t₃ t₃_in_barycenter t₂ t₂_in_bd t'_decomp t'_ne using t'₂_in_join
    have t₃_empty : t₃ = ∅ :=
    by
      cases' t₃_in_barycenter with t₃_in_barycenter t₃_empty
      · simp only [simplex, Set.mem_diff_singleton, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at t₃_in_barycenter
        choose t₃_in_barycenter t₃_ne using t₃_in_barycenter
        cases' t₃_in_barycenter with t₃_empty t₃_eq_x; contradiction
        have contra : x ∈ X.vertices :=
        by
          rw [vertices_setOf, Set.mem_setOf]
          use t; constructor; assumption
          simp only [t_decomp, t'_decomp, t₃_eq_x, Finset.mem_union]
          left; left
          apply Finset.mem_singleton_self
        contradiction
      · assumption

    cases' u'₂_in_join with u'₂_in_join u'₂_empty
    · simp only [simplicialJoinProj_mem, Set.mem_union, Set.mem_singleton_iff] at u'₂_in_join
      choose u₃ u₃_in_barycenter u₂ u₂_in_bd u'_decomp u'_ne using u'₂_in_join
      have u₃_empty : u₃ = ∅ :=
      by
        cases' u₃_in_barycenter with u₃_in_barycenter u₃_empty
        · simp only [simplex, Set.mem_diff_singleton, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at u₃_in_barycenter
          choose u₃_in_barycenter u₃_ne using u₃_in_barycenter
          cases' u₃_in_barycenter with u₃_empty u₃_eq_x; contradiction
          have contra : x ∈ X.vertices :=
          by
            rw [vertices_setOf, Set.mem_setOf]
            use u; constructor; assumption
            simp only [Finset.mem_union, u_decomp, u'_decomp, u₃_eq_x]
            left; left
            apply Finset.mem_singleton_self
          contradiction
        · assumption

      left; constructor; constructor; assumption
      constructor
      apply stellar_subdiv_anticomm_link_left_ad_tu_in_X X s t u t₁ u₁ t'₂ u'₂
        st₁u₁_in_X t'₂_sss_s u'₂_sss_s
      rw [Finset.union_comm]; assumption
      rw [Finset.union_comm]; assumption
      assumption; assumption

      have st_eq_st₂ : s \ t = s \ t'₂ :=
      by
        rw [t_decomp, Finset.sdiff_union_distrib, st₁_eq_s, Finset.sdiff_inter_right_comm, Finset.inter_self]

      rw [st_eq_st₂]
      have _ : Nonempty { x // x ∈ s } := by
        rw [Finset.nonempty_coe_sort, Finset.nonempty_iff_ne_empty]
        exact face_nonempty s_in_X
      apply @stellar_subdiv_anticomm_link_left_ad_st_nss_u _ 𝕜 _ _ _ _ _
        X s t u t₁ u₁ t'₂ u'₂ _ x s_in_X x_nin_X t_in_X u_in_X tu_disj
      cases' u₁_in_link with u₁_in_link u₁_empty
      · choose u₁_in_X su₁_in_link su₁_disj using u₁_in_link
        assumption
      · rw [u₁_empty, Finset.inter_empty]
      assumption
      rw [Finset.union_comm]
      assumption
      rw [Finset.union_comm]
      assumption
    · rw [u'₂_empty, Finset.empty_union] at u_decomp; subst u_decomp
      left; constructor; constructor; assumption

      constructor
      apply X.down_closed st₁u₁_in_X
      rw [t_decomp, Finset.union_assoc]
      apply Finset.union_subset_union_left
      rw [Finset.ssubset_iff_subset_ne] at t'₂_sss_s
      choose t'₂_ss_s t'₂_ne_s using t'₂_sss_s
      assumption
      assumption
      assumption

      have st_eq_st₂ : s \ t = s \ t'₂ :=
      by
        rw [t_decomp, Finset.sdiff_union_distrib, st₁_eq_s, Finset.sdiff_inter_right_comm, Finset.inter_self]

      rw [st_eq_st₂]
      have _ : Nonempty { x // x ∈ s } := by
        rw [Finset.nonempty_coe_sort, Finset.nonempty_iff_ne_empty]
        exact face_nonempty s_in_X
      apply @stellar_subdiv_anticomm_link_left_ad_st_nss_u _ 𝕜 _ _ _ _ _
        X s t u t₁ u t'₂ u'₂ _ x s_in_X x_nin_X t_in_X u_in_X tu_disj
      cases' u₁_in_link with u₁_in_link u₁_empty
      · choose u₁_in_X su₁_in_link su₁_disj using u₁_in_link
        assumption
      · rw [u₁_empty, Finset.inter_empty]
      assumption
      rw [Finset.union_comm]
      assumption
      rw [u'₂_empty, Finset.union_empty]
  · left; constructor; constructor; assumption

    constructor
    rw [t_decomp, t'₂_empty, Finset.empty_union]
    apply stellar_subdiv_anticomm_link_left_ad_tu_in_X X s t₁ u t₁ u ∅ ∅

    have st₁u_eq_st₁u₁ : s ∪ (t₁ ∪ u) = s ∪ (t₁ ∪ u₁) :=
    by
      rw [u_decomp, ← Finset.union_assoc t₁, Finset.union_comm t₁, Finset.union_assoc u'₂,
        ← Finset.union_assoc s]
      have su₂_eq_s : s ∪ u'₂ = s :=
      by
        rw [Finset.union_eq_left]
        cases' u'₂_in_join with u'₂_in_join u'₂_empty
        · choose u₃ u₃_in_barycenter u₂ u₂_in_bd u'_decomp u'_ne using u'₂_in_join
          have u₃_empty : u₃ = ∅ :=
          by
            cases' u₃_in_barycenter with u₃_in_barycenter u₃_empty
            · simp only [simplex, Set.mem_diff_singleton, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at u₃_in_barycenter
              choose u₃_in_barycenter u₃_ne using u₃_in_barycenter
              cases' u₃_in_barycenter with u₃_empty u₃_eq_x; contradiction
              have contra : x ∈ X.vertices :=
              by
                rw [vertices_setOf, Set.mem_setOf]
                use u; constructor; assumption
                simp only [Finset.mem_union, u_decomp, u'_decomp, u₃_eq_x]
                left; left
                apply Finset.mem_singleton_self
              contradiction
            · assumption
          rw [u'_decomp, u₃_empty, Finset.empty_union]

          cases' u₂_in_bd with u₂_in_bd u₂_empty
          · rw [simplexBoundary_mem_iff_subset, Finset.ssubset_iff_subset_ne] at u₂_in_bd
            choose u₂_sss_s u₂_ne using u₂_in_bd
            choose u₂_ss_s u₂_ne_s using u₂_sss_s
            assumption
          · rw [u₂_empty]; apply Finset.empty_subset
        · rw [u'₂_empty]; apply Finset.empty_subset
      rw [su₂_eq_s]
    rw [st₁u_eq_st₁u₁]; assumption

    rw [Finset.empty_ssubset, Finset.nonempty_iff_ne_empty]
    exact face_nonempty s_in_X
    rw [Finset.empty_ssubset, Finset.nonempty_iff_ne_empty]
    exact face_nonempty s_in_X
    rw [Finset.union_empty]
    rw [Finset.union_empty]
    rw [ne_eq, Finset.union_eq_empty, not_and_or]
    right; exact face_nonempty u_in_X
    assumption

    rw [t_decomp, t'₂_empty, Finset.empty_union, st₁_eq_s]
    assumption

theorem stellar_subdiv_anticomm_link_left_bc
    (X : AbstractSimplicialComplex E)
    (s t : Finset E)
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (t_in_X : t ∈ X.faces)
    (t_in_star_bd : t ∈ ((π₁[𝕜] (disjoint_link_boundary X s)).coe ''ˢ (Lk(X, s) ⋆ ∂s)).faces)
  : ∀ u : Finset E,
      u ∈ ((π₁[𝕜] (@disjoint_barycenter_join_boundary_link _ 𝕜 _ _ _ _ _ _ _ _ s_in_X x_nin_X)).coe
            ''ˢ (((π₁[𝕜] (disjoint_barycenter_boundary s_in_X x_nin_X)).coe
              ''ˢ (simplex {x} ⋆ ∂s)) ⋆
                Lk(X, s))).faces →
        t ∪ u ∈ (StarComplement X s).faces →
          t ∩ u = ∅ →
            u ∈ σ(Lk(X, t), s \ t, x; 𝕜,
                  @star_boundary_mem_link _ _ _ _ _ _ _ X s t s_in_X t_in_star_bd,
                  not_mem_link_vertices x_nin_X).faces :=
by
  intro u u_in_join tu_in_star_comp tu_disj
  simp only [StellarSubdivision, StarComplement, AbstractSimplicialComplex.instHasUnion, SimplicialUnion] at u_in_join tu_in_star_comp ⊢
  simp only [Set.mem_union, Set.mem_setOf] at tu_in_star_comp ⊢
  choose tu_in_X s_nss_tu using tu_in_star_comp

  rw [simplicialJoinProj_mem] at u_in_join
  choose u'₂ u'₂_in_join u₁ u₁_in_link u_decomp u_ne using u_in_join
  rw [Set.mem_union, Set.mem_singleton_iff, Link, Set.mem_setOf] at u₁_in_link
  simp only [Set.mem_union, Set.mem_singleton_iff, simplicialJoinProj_mem] at u'₂_in_join

  cases' u'₂_in_join with u'₂_in_join u'₂_empty
  · choose u₃ u₃_in_barycenter u₂ u₂_in_bd u'_decomp u'_ne using u'₂_in_join
    have u₃_empty : u₃ = ∅ :=
    by
      cases' u₃_in_barycenter with u₃_in_barycenter u₃_empty
      · simp only [simplex, Set.mem_diff_singleton, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at u₃_in_barycenter
        choose u₃_in_barycenter u₃_ne using u₃_in_barycenter
        cases' u₃_in_barycenter with u₃_empty u₃_eq_x; contradiction
        have contra : x ∈ X.vertices :=
        by
          rw [vertices_setOf, Set.mem_setOf]
          use (t ∪ u); constructor; assumption
          simp only [Finset.mem_union, u_decomp, u'_decomp, u₃_eq_x]
          right; left; left
          apply Finset.mem_singleton_self
        contradiction
      · assumption
    subst u₃_empty; rw [Finset.empty_union] at u'_decomp; subst u'_decomp
    cases' u₂_in_bd with u₂_in_bd u₂_empty
    rotate_left; contradiction

    left; constructor; constructor
    apply X.down_closed tu_in_X
    apply Finset.subset_union_right
    assumption
    constructor; assumption; assumption

    revert s_nss_tu
    contrapose
    simp only [Classical.not_not]
    intro st_ss_u
    apply @Finset.union_subset_left _ _ s t
    rw [← Finset.union_sdiff_self_eq_union, Finset.union_sdiff_symm]
    apply Finset.union_subset_union_right
    assumption
  · subst u'₂_empty; rw [Finset.empty_union] at u_decomp; subst u_decomp
    left; constructor; constructor
    apply X.down_closed tu_in_X
    apply Finset.subset_union_right
    assumption
    constructor; assumption; assumption

    revert s_nss_tu
    contrapose
    simp only [Classical.not_not]
    intro st_ss_u
    apply @Finset.union_subset_left _ _ s t
    rw [← Finset.union_sdiff_self_eq_union, Finset.union_sdiff_symm]
    apply Finset.union_subset_union_right
    assumption

theorem stellar_subdiv_anticomm_link_left_bd_u_ss_st
    (s t u t₁ u₁ t₂ u₂ u₃ : Finset E)
    (tu_disj : t ∩ u = ∅)
    (t₂_in_bd : t₂ ⊂ s)
    (tu₂_in_bd : t₂ ∪ u₂ ⊂ s)
    (t_decomp : t = t₂ ∪ t₁)
    (u_decomp : u = u₃ ∪ u₂ ∪ u₁)
  : u₂ ⊂ s \ t₂ :=
by
  rw [Finset.ssubset_iff_subset_ne] at tu₂_in_bd ⊢
  choose tu₂_ss_s tu₂_ne_s using tu₂_in_bd
  constructor
  rw [Finset.subset_sdiff]
  constructor
  apply @Finset.Subset.trans _ _ (t₂ ∪ u₂)
  apply Finset.subset_union_right
  apply tu₂_ss_s
  rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.subset_empty]
  rw [← tu_disj, t_decomp, u_decomp]
  rw [Finset.inter_comm]
  apply Finset.inter_subset_inter
  apply @Finset.subset_union_left _ _ t₂ t₁
  rw [Finset.union_assoc, Finset.union_comm, Finset.union_assoc]
  apply @Finset.subset_union_left _ _ u₂ (u₁ ∪ u₃)
  rw [Finset.union_comm] at tu₂_ne_s
  have H1 : s = s ∪ t₂ :=
  by
    symm
    rw [Finset.union_eq_left]
    rw [Finset.ssubset_def] at t₂_in_bd
    choose t₂_ss_s t₂_ne_s using t₂_in_bd
    apply t₂_ss_s
  rw [H1] at tu₂_ne_s
  revert tu₂_ne_s
  contrapose
  simp only [not_ne_iff]
  rw [← @Finset.sdiff_union_self_eq_union _ _ s]
  exact congr_arg fun a : Finset E => a ∪ t₂

theorem stellar_subdiv_anticomm_link_left_bd_u_mem_link
    (X : AbstractSimplicialComplex E)
    (s t u t₁ t₂ : Finset E)
    (t_in_X : t ∈ X.faces)
    (tu_disj : t ∩ u = ∅)
    (stu₁_in_X : s ∪ (t₁ ∪ u) ∈ X.faces)
    (t_decomp : t = t₂ ∪ t₁)
    (t₂_ss_s : t₂ ⊆ s)
  : t ∪ u ∈ X.faces ∧ t ∩ u = ∅ :=
by
  constructor
  rw [t_decomp]
  apply X.down_closed stu₁_in_X
  simp only [Finset.union_assoc]
  apply Finset.union_subset_union_left
  apply t₂_ss_s
  rw [ne_eq, Finset.union_eq_empty, not_and_or, ← t_decomp]
  left; exact face_nonempty t_in_X
  rw [← Finset.subset_empty]
  apply @Finset.Subset.trans _ _ (t ∩ u)
  apply Finset.inter_subset_inter_left
  rfl
  rw [Finset.subset_empty]
  apply tu_disj

theorem stellar_subdiv_anticomm_link_left_bd_stu_mem_link
    (X : AbstractSimplicialComplex E)
    (s t u t₁ u₁ t₂ u₂ u₃ : Finset E)
    (t_in_X : t ∈ X.faces)
    (tu_disj : t ∩ u = ∅)
    (su₁_disj : s ∩ u₁ = ∅)
    (stu₁_in_X : s ∪ (t₁ ∪ u₁) ∈ X.faces)
    (t_decomp : t = t₂ ∪ t₁)
    (u_decomp : u = u₃ ∪ u₂ ∪ u₁)
    (st₁_sdiff_ident : s \ t₁ = s)
    (t₂_ss_s : t₂ ⊂ s)
  : s \ t ∪ u₁ ∈ Lk(X, t).faces ∧ s \ t ∩ u₁ = ∅ :=
by
  constructor; constructor
  apply X.down_closed stu₁_in_X
  apply @Finset.Subset.trans _ _ (s ∪ u₁)
  apply Finset.union_subset_union_left
  apply Finset.sdiff_subset
  rw [Finset.union_comm t₁ u₁, ← Finset.union_assoc]
  apply Finset.subset_union_left

  rw [t_decomp, Finset.sdiff_union_distrib, st₁_sdiff_ident, Finset.sdiff_inter_right_comm, Finset.inter_self,
    ne_eq, Finset.union_eq_empty, not_and_or]
  left
  simp only [Finset.sdiff_eq_empty_iff_subset, Finset.subset_iff, not_forall]
  rw [Finset.ssubset_iff_of_subset] at t₂_ss_s
  choose x x_in_s x_nin_t₂ using t₂_ss_s
  use x

  rw [Finset.ssubset_iff_subset_ne] at t₂_ss_s
  choose t₂_ss_s t₂_ne_s using t₂_ss_s
  assumption

  constructor
  apply X.down_closed stu₁_in_X
  rw [t_decomp, Finset.sdiff_union_distrib, st₁_sdiff_ident, Finset.inter_comm]
  rw [← Finset.inter_sdiff_assoc, Finset.inter_self, ← Finset.union_assoc, Finset.union_assoc t₂ t₁]
  rw [Finset.union_comm t₁ (s \ t₂), ← Finset.union_assoc, Finset.union_assoc]
  apply Finset.union_subset_union_left
  apply Finset.subset_of_eq
  apply Finset.union_sdiff_of_subset
  rw [Finset.ssubset_iff_subset_ne] at t₂_ss_s
  choose t₂_ss_s t₂_ne_s using t₂_ss_s
  assumption

  rw [ne_eq, Finset.union_eq_empty, not_and_or]
  left; exact face_nonempty t_in_X

  rw [Finset.inter_union_distrib_left, Finset.inter_comm, Finset.sdiff_inter_self,
    Finset.empty_union]
  rw [← Finset.subset_empty]
  apply @Finset.Subset.trans _ _ (t ∩ u)
  apply Finset.inter_subset_inter_left
  rw [u_decomp]
  apply Finset.subset_union_right
  rw [Finset.subset_empty]
  apply tu_disj
  rw [← Finset.subset_empty]
  apply @Finset.Subset.trans _ _ (s ∩ u₁)
  apply Finset.inter_subset_inter_right
  apply Finset.sdiff_subset
  rw [Finset.subset_empty]
  apply su₁_disj

theorem stellar_subdiv_anticomm_link_left_bd
    (X : AbstractSimplicialComplex E)
    (s t : Finset E)
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (t_in_X : t ∈ X.faces)
    (t_in_star_bd : t ∈ ((π₁[𝕜] (disjoint_link_boundary X s)).coe ''ˢ (Lk(X, s) ⋆ ∂s)).faces)
  : ∀ u : Finset E,
      u ∈ ((π₁[𝕜] (@disjoint_barycenter_join_boundary_link _ 𝕜 _ _ _ _ _ _ _ _ s_in_X x_nin_X)).coe
            ''ˢ (((π₁[𝕜] (disjoint_barycenter_boundary s_in_X x_nin_X)).coe
              ''ˢ (simplex {x} ⋆ ∂s)) ⋆
                Lk(X, s))).faces →
        t ∪ u ∈ ((π₁[𝕜] (@disjoint_barycenter_join_boundary_link _ 𝕜 _ _ _ _ _ _ _ _ s_in_X x_nin_X)).coe
                  ''ˢ ((π₁[𝕜] (disjoint_barycenter_boundary s_in_X x_nin_X)).coe
                    ''ˢ (simplex {x} ⋆ ∂s) ⋆
                     Lk(X, s))).faces →
          t ∩ u = ∅ →
            u ∈ σ(Lk(X, t), s \ t, x; 𝕜,
                  @star_boundary_mem_link _ _ _ _ _ _ _ X s t s_in_X t_in_star_bd,
                  not_mem_link_vertices x_nin_X).faces :=
by
  intro u u_in_join tu_in_join tu_disj
  rw [simplicialJoinProj_union_mem] at tu_in_join
  choose t'₂ t'₂_in_join u'₂ u'₂_in_join t₁ t₁_in_link u₁ u₁_in_link tu_decomp using tu_in_join
  choose t'_decomp u_decomp tu_in_join tu_in_link tu_ne using tu_decomp
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf] at t₁_in_link u₁_in_link tu_in_link

  simp only [StellarSubdivision, StarComplement, AbstractSimplicialComplex.instHasUnion, SimplicialUnion,
    Set.mem_union, Set.mem_setOf, Set.mem_singleton_iff, simplicialJoinProj_mem]
  simp only [Link, Set.mem_setOf] at t₁_in_link u₁_in_link tu_in_link ⊢

  rw [Set.mem_union, Set.mem_singleton_iff] at t'₂_in_join u'₂_in_join tu_in_join

  have t_in_star_bd' := t_in_star_bd
  simp only [simplicialJoinProj_mem, Set.mem_union, Set.mem_singleton_iff] at t_in_star_bd
  choose t'₁ t'₁_in_link t₂ t₂_in_bd t_decomp t_ne using t_in_star_bd

  have t_ident : t₁ = t'₁ ∧ t₂ = t'₂ :=
  by
    have t'₁t'₂_disj : Disjoint t'₁ t'₂ :=
    by
      rw [Finset.disjoint_iff_inter_eq_empty, Finset.inter_comm]
      cases' t'₁_in_link with t'₁_in_link t'₁_empty
      · simp only [Link, Set.mem_setOf] at t'₁_in_link
        choose t'₁_in_X st'₁_in_X st'₁_disj using t'₁_in_link
        rw [← Finset.subset_empty] at st'₁_disj ⊢
        apply subset_trans _ st'₁_disj
        apply Finset.inter_subset_inter_right

        cases' t'₂_in_join with t'₂_in_join t'₂_empty
        · rw [simplicialJoinProj_mem] at t'₂_in_join
          choose w₃ w₃_in_barycenter w₂ w₂_in_bd t'₂_decomp t'₂_ne using t'₂_in_join
          have w₃_empty : w₃ = ∅ :=
          by
            cases' w₃_in_barycenter with w₃_in_barycenter w₃_empty
            · simp only [simplex, Set.mem_diff_singleton, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at w₃_in_barycenter
              choose w₃_in_barycenter w₃_ne using w₃_in_barycenter
              cases' w₃_in_barycenter with w₃_empty w₃_eq_x; contradiction
              have contra : x ∈ X.vertices :=
              by
                rw [vertices_setOf, Set.mem_setOf]
                use t; constructor; assumption
                simp only [t'_decomp, t'₂_decomp, w₃_eq_x, Finset.mem_union]
                left; left
                apply Finset.mem_singleton_self
              contradiction
            · assumption
          rw [w₃_empty, Finset.empty_union] at t'₂_decomp; subst t'₂_decomp

          rw [Set.mem_union, Set.mem_singleton_iff, simplexBoundary_mem_iff_subset, Finset.ssubset_iff_subset_ne] at w₂_in_bd
          cases' w₂_in_bd with t'₂_in_bd t'₂_empty
          · choose t'₂_sss_s t'₂_ne using t'₂_in_bd
            choose t'₂_ss_s t'₂_ne_s using t'₂_sss_s
            assumption
          · rw [t'₂_empty]; apply Finset.empty_subset
        · rw [t'₂_empty]; apply Finset.empty_subset
      · rw [t'₁_empty, Finset.inter_empty]

    have t₁t₂_disj : Disjoint t₁ t₂ :=
    by
      rw [Finset.disjoint_iff_inter_eq_empty, Finset.inter_comm]
      cases' t₁_in_link with t₁_in_link t₁_empty
      · choose t₁_in_X st₁_in_X st₁_disj using t₁_in_link
        rw [← Finset.subset_empty] at st₁_disj ⊢
        apply subset_trans _ st₁_disj
        apply Finset.inter_subset_inter_right

        cases' t₂_in_bd with t₂_in_bd t₂_empty
        · rw [simplexBoundary_mem_iff_subset] at t₂_in_bd
          choose t₂_sss_s t₂_ne using t₂_in_bd
          choose t₂_ss_s t₂_ne_s using t₂_sss_s
          assumption
        · rw [t₂_empty]; apply Finset.empty_subset
      · rw [t₁_empty, Finset.inter_empty]

    simp only [t'_decomp, Finset.ext_iff, Finset.mem_union] at t_decomp
    simp only [Finset.ext_iff]
    constructor

    intro a
    specialize t_decomp a
    rw [iff_def] at t_decomp
    choose t₁t'₂_ss_t'₁t₂ t'₁t₂_ss_t₁t'₂ using t_decomp
    constructor

    -- t₁ → t'₁
    intro a_in_t₁
    rw [Finset.disjoint_left] at t₁t₂_disj

    have a_in_t₁t'₂ : a ∈ t'₂ ∨ a ∈ t₁ := by right; assumption
    specialize t₁t'₂_ss_t'₁t₂ a_in_t₁t'₂
    cases' t₁t'₂_ss_t'₁t₂ with a_in_t'1 a_in_t₂
    assumption
    specialize t₁t₂_disj a_in_t₁
    contradiction

    -- t'₁ → t₁
    intro a_in_t'₁
    rw [Finset.disjoint_left] at t'₁t'₂_disj

    have a_in_t'₁t₂ : a ∈ t'₁ ∨ a ∈ t₂ := by left; assumption
    specialize t'₁t₂_ss_t₁t'₂ a_in_t'₁t₂
    cases' t'₁t₂_ss_t₁t'₂ with a_in_t'₂ a_in_t₁
    specialize t'₁t'₂_disj a_in_t'₁
    contradiction
    assumption

    intro a
    specialize t_decomp a
    rw [iff_def] at t_decomp
    choose t₁t'₂_ss_t'₁t₂ t'₁t₂_ss_t₁t'₂ using t_decomp
    constructor

    -- t₂ → t'₂
    intro a_in_t₂
    rw [Finset.disjoint_right] at t₁t₂_disj

    have a_in_t'₁t₂ : a ∈ t'₁ ∨ a ∈ t₂ := by right; assumption
    specialize t'₁t₂_ss_t₁t'₂ a_in_t'₁t₂
    cases' t'₁t₂_ss_t₁t'₂ with a_in_t'₂ a_in_t₁
    assumption
    specialize t₁t₂_disj a_in_t₂
    contradiction

    -- t'₂ → t₂
    intro a_in_t'₂
    rw [Finset.disjoint_right] at t'₁t'₂_disj

    have a_in_t₁t'₂ : a ∈ t'₂ ∨ a ∈ t₁ := by left; assumption
    specialize t₁t'₂_ss_t'₁t₂ a_in_t₁t'₂
    cases' t₁t'₂_ss_t'₁t₂ with a_in_t'1 a_in_t₂
    specialize t'₁t'₂_disj a_in_t'₂
    contradiction
    assumption
  choose t₁_ident t₂_ident using t_ident
  subst t₁_ident t₂_ident

  have st₁_eq_s : s \ t₁ = s :=
  by
    cases' t₁_in_link with t₁_in_link t₁_empty
    · choose t₁_in_X st₁_in_X st₁_disj using t₁_in_link
      rw [Finset.sdiff_eq_self_iff_disjoint, Finset.disjoint_iff_inter_eq_empty]
      assumption
    · rw [t₁_empty, Finset.sdiff_empty]

  have st₂_ne : s \ t₂ ≠ ∅ :=
  by
    cases' t₂_in_bd with t₂_in_bd t₂_empty
    · rw [simplexBoundary_mem_iff_subset] at t₂_in_bd
      choose t₂_sss_s t₂_ne using t₂_in_bd
      rw [ne_eq, Finset.sdiff_eq_empty_iff_subset, Finset.not_subset]
      apply Finset.exists_of_ssubset t₂_sss_s
    · rw [t₂_empty, Finset.sdiff_empty, ← Finset.nonempty_iff_ne_empty, Finset.nonempty_iff_ne_empty]
      exact face_nonempty s_in_X

  cases' u'₂_in_join with u'₂_in_join u'₂_empty
  · simp only [simplicialJoinProj_mem, Set.mem_union, Set.mem_singleton_iff] at u'₂_in_join
    choose u₃ u₃_in_barycenter u₂ u₂_in_bd u'_decomp u'_ne using u'₂_in_join

    right; use (u₃ ∪ u₂); constructor; left
    use u₃; constructor; assumption
    use u₂; constructor
    cases' u₂_in_bd with u₂_in_bd u₂_empty
    · have st_ne : Nonempty {x // x ∈ s \ t} :=
      by
        rw [t_decomp, Finset.nonempty_coe_sort, Finset.nonempty_iff_ne_empty, Finset.sdiff_union_distrib, st₁_eq_s,
          ← Finset.inter_sdiff_assoc, Finset.inter_self]
        assumption
      rw [simplexBoundary_mem_iff_subset, t_decomp, Finset.sdiff_union_distrib, st₁_eq_s,
        ← Finset.inter_sdiff_assoc, Finset.inter_self]
      left; constructor
      apply @stellar_subdiv_anticomm_link_left_bd_u_ss_st _ _ _
        s t u t₁ u₁ t₂ u₂ u₃ tu_disj

      cases' t₂_in_bd with t₂_in_bd t₂_empty
      · rw [simplexBoundary_mem_iff_subset] at t₂_in_bd
        choose t₂_sss_s t₂_ne_s using t₂_in_bd
        assumption
      · rw [t₂_empty, Finset.empty_ssubset, Finset.nonempty_iff_ne_empty]
        exact face_nonempty s_in_X

      cases' tu_in_join with tu_in_join tu_empty
      · rw [simplicialJoinProj_union_mem] at tu_in_join
        choose w₃ w₃_in_barycenter z₃ z₃_in_barycenter w₂ w₂_in_bd z₂ z₂_in_bd t₂_decomp u'₂_decomp wz₁_in_barycenter wz₂_in_bd tu₂_ne using tu_in_join

        have t₂_ident : t₂ = w₂ :=
        by
          have w₃_empty : w₃ = ∅ :=
          by
            cases' w₃_in_barycenter with w₃_in_barycenter w₃_empty
            · simp only [simplex, Set.mem_diff_singleton, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at w₃_in_barycenter
              choose w₃_in_barycenter w₃_ne using w₃_in_barycenter
              cases' w₃_in_barycenter with w₃_empty w₃_eq_x; contradiction
              have contra : x ∈ X.vertices :=
              by
                rw [vertices_setOf, Set.mem_setOf]
                use t; constructor; assumption
                simp only [t'_decomp, t₂_decomp, w₃_eq_x, Finset.mem_union]
                left; left
                apply Finset.mem_singleton_self
              contradiction
            · assumption
          rw [w₃_empty, Finset.empty_union] at t₂_decomp
          assumption
        subst t₂_ident

        have u₂_ident : u₂ = z₂ :=
        by
          rw [u'_decomp] at u'₂_decomp
          cases' u₃_in_barycenter with u₃_in_barycenter u₃_empty
          · simp only [simplex, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at u₃_in_barycenter
            choose u₃_in_barycenter u₃_ne using u₃_in_barycenter
            cases' u₃_in_barycenter with u₃_empty u₃_eq_x; contradiction

            subst u₃_eq_x
            cases' z₃_in_barycenter with z₃_in_barycenter z₃_empty
            · simp only [simplex, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at z₃_in_barycenter
              choose z₃_in_barycenter z₃_ne using z₃_in_barycenter
              cases' z₃_in_barycenter with z₃_empty z₃_eq_x; contradiction

              subst z₃_eq_x
              simp only [Finset.union_eq_union_iff_left, Finset.subset_iff, Finset.mem_union, Finset.mem_singleton] at u'₂_decomp
              choose u₂_ss_xz₂ z₂_ss_xu₂ using u'₂_decomp

              have x_nin_u₂ : x ∉ u₂ :=
              by
                by_contra
                have contra : x ∈ X.vertices :=
                by
                  rw [vertices_setOf]
                  use u₂; constructor
                  apply isSubcomplex_face_imp_face
                  assumption
                  apply simplexBoundary_subcomplex
                  assumption
                  assumption
                contradiction

              have x_nin_z₂ : x ∉ z₂ :=
              by
                rw [Set.mem_union, Set.mem_singleton_iff] at z₂_in_bd
                cases' z₂_in_bd with z₂_in_bd z₂_empty
                · by_contra
                  have contra : x ∈ X.vertices :=
                  by
                    rw [vertices_setOf]
                    use z₂; constructor
                    apply isSubcomplex_face_imp_face
                    assumption
                    apply simplexBoundary_subcomplex
                    assumption
                    assumption
                  contradiction
                · rw [z₂_empty]; apply Finset.notMem_empty

              rw [Finset.ext_iff]
              intro a; constructor

              intro a_in_u₂
              specialize u₂_ss_xz₂ a_in_u₂
              cases' u₂_ss_xz₂ with a_eq_x a_in_z₂
              · rw [a_eq_x] at a_in_u₂
                contradiction
              · assumption

              intro a_in_z₂
              specialize z₂_ss_xu₂ a_in_z₂
              cases' z₂_ss_xu₂ with a_eq_x a_in_u₂
              · rw [a_eq_x] at a_in_z₂
                contradiction
              · assumption

            rw [Set.mem_singleton_iff] at z₃_empty
            subst z₃_empty
            rw [Finset.empty_union] at u'₂_decomp

            cases' z₂_in_bd with z₂_in_bd z₂_empty
            · have contra : x ∈ X.vertices :=
              by
                rw [vertices_setOf, Set.mem_setOf]
                use z₂; constructor
                apply isSubcomplex_face_imp_face
                assumption
                apply simplexBoundary_subcomplex
                assumption
                rw [← u'₂_decomp, Finset.mem_union]
                left; apply Finset.mem_singleton_self
              contradiction
            · rw [Set.mem_singleton_iff] at z₂_empty
              rw [z₂_empty, Finset.union_eq_empty] at u'₂_decomp
              choose x_empty u₂_empty using u'₂_decomp
              contradiction
          · simp only [u₃_empty, Finset.empty_union] at u'₂_decomp
            have z₃_empty : z₃ = ∅ :=
            by
              cases' z₃_in_barycenter with z₃_in_barycenter z₃_empty
              · simp only [simplex, Set.mem_diff_singleton, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at z₃_in_barycenter
                choose z₃_in_barycenter z₃_ne using z₃_in_barycenter
                cases' z₃_in_barycenter with z₃_empty z₃_eq_x; contradiction
                have contra : x ∈ X.vertices :=
                by
                  rw [vertices_setOf, Set.mem_setOf]
                  use u₂; constructor
                  apply isSubcomplex_face_imp_face
                  assumption
                  apply simplexBoundary_subcomplex
                  assumption
                  rw [u'₂_decomp, Finset.mem_union, z₃_eq_x]
                  left; apply Finset.mem_singleton_self
                contradiction
              · assumption
            rw [z₃_empty, Finset.empty_union] at u'₂_decomp
            assumption
        subst u₂_ident

        have u₃_ident : u₃ = z₃ :=
        by
          rw [u'_decomp] at u'₂_decomp
          rw [Set.mem_union, Set.mem_singleton_iff] at z₃_in_barycenter
          cases' u₃_in_barycenter with u₃_in_barycenter u₃_empty <;>
          cases' z₃_in_barycenter with z₃_in_barycenter z₃_empty
          · simp only [simplex, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at z₃_in_barycenter u₃_in_barycenter

            choose z₃_in_barycenter z₃_ne using z₃_in_barycenter
            cases' z₃_in_barycenter with z₃_empty z₃_eq_x; contradiction

            choose u₃_in_barycenter u₃_ne using u₃_in_barycenter
            cases' u₃_in_barycenter with u₃_empty u₃_eq_x; contradiction

            rw [z₃_eq_x, u₃_eq_x]
          · rw [z₃_empty, Finset.empty_union] at u'₂_decomp
            simp only [simplex, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at u₃_in_barycenter
            choose u₃_in_barycenter u₃_ne using u₃_in_barycenter
            cases' u₃_in_barycenter with u₃_empty u₃_eq_x; contradiction

            have contra : x ∈ X.vertices :=
            by
              rw [vertices_setOf, Set.mem_setOf]
              use u₂; constructor
              apply isSubcomplex_face_imp_face
              assumption
              apply simplexBoundary_subcomplex
              assumption
              rw [← u'₂_decomp, Finset.mem_union, u₃_eq_x]
              left; apply Finset.mem_singleton_self
            contradiction
          · rw [u₃_empty, Finset.empty_union] at u'₂_decomp
            simp only [simplex, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at z₃_in_barycenter
            choose z₃_in_barycenter z₃_ne using z₃_in_barycenter
            cases' z₃_in_barycenter with z₃_empty z₃_eq_x; contradiction

            have contra : x ∈ X.vertices :=
            by
              rw [vertices_setOf, Set.mem_setOf]
              use u₂; constructor
              apply isSubcomplex_face_imp_face
              assumption
              apply simplexBoundary_subcomplex
              assumption
              rw [u'₂_decomp, Finset.mem_union, z₃_eq_x]
              left; apply Finset.mem_singleton_self
            contradiction
          · rw [u₃_empty, z₃_empty]
        subst u₃_ident

        rw [Set.mem_union, Set.mem_singleton_iff, simplexBoundary_mem_iff_subset] at wz₂_in_bd
        cases' wz₂_in_bd with tu₂_in_bd tu₂_empty
        · choose tu₂_sss_s tu₂_ne using tu₂_in_bd
          assumption
        · rw [tu₂_empty, Finset.empty_ssubset, Finset.nonempty_iff_ne_empty]
          exact face_nonempty s_in_X
      · rw [Finset.union_eq_empty] at tu_empty
        choose t₂_empty u'₂_empty using tu_empty
        contradiction

      rw [Finset.union_comm]; assumption
      rw [← u'_decomp]; assumption
      exact face_nonempty u₂_in_bd
    · right; assumption

    constructor; rfl
    rw [← u'_decomp]; assumption

    use u₁; constructor
    cases' u₁_in_link with u₁_in_link u₁_empty
    · choose u₁_in_X su₁_in_X su₁_disj using u₁_in_link
      cases' t₁_in_link with t₁_in_link t₁_empty
      · cases' tu_in_link with tu_in_link tu_empty
        rotate_left
        rw [Finset.union_eq_empty] at tu_empty
        choose t_empty u_empty using tu_empty
        have contra : u₁ ≠ ∅ := by exact face_nonempty u₁_in_X
        contradiction

        choose t₁_in_X st₁_in_X st₁_disj using t₁_in_link
        choose tu₁_in_X stu₁_in_X stu₁_disj using tu_in_link

        left; constructor; constructor; assumption
        apply stellar_subdiv_anticomm_link_left_bd_u_mem_link
          X s t u₁ t₁ t₂ t_in_X
        rw [← Finset.subset_empty] at tu_disj ⊢
        apply subset_trans _ tu_disj
        apply Finset.inter_subset_inter_left
        rw [u_decomp]
        apply Finset.subset_union_right
        assumption
        rw [Finset.union_comm]; assumption

        cases' t₂_in_bd with t₂_in_bd t₂_empty
        · rw [simplexBoundary_mem_iff_subset, Finset.ssubset_iff_subset_ne] at t₂_in_bd
          choose t₂_sss_s t₂_ne using t₂_in_bd
          choose t₂_ss_s t₂_ne_s using t₂_sss_s
          assumption
        · rw [t₂_empty]; apply Finset.empty_subset

        have stu₁_diff_in_link : s \ t ∪ u₁ ∈ Lk(X, t).faces ∧ s \ t ∩ u₁ = ∅ :=
        by
          apply stellar_subdiv_anticomm_link_left_bd_stu_mem_link
            X s t u t₁ u₁ t₂ u'₂ ∅ t_in_X tu_disj su₁_disj stu₁_in_X t'_decomp

          rw [Finset.empty_union]; assumption
          rw [Finset.sdiff_eq_self_iff_disjoint, Finset.disjoint_iff_inter_eq_empty]
          assumption

          cases' t₂_in_bd with t₂_in_bd t₂_empty
          · rw [simplexBoundary_mem_iff_subset] at t₂_in_bd
            choose t₂_sss_s t₂_ne using t₂_in_bd
            assumption
          · rw [t₂_empty, Finset.empty_ssubset, Finset.nonempty_iff_ne_empty]
            exact face_nonempty s_in_X

        choose stu₁_diff_in_link stu₁_diff_disj using stu₁_diff_in_link
        simp only [Link, Set.mem_setOf] at stu₁_diff_in_link
        choose stu₁_diff_in_X tstu₁_diff_in_X tstu₁_diff_disj using stu₁_diff_in_link

        constructor; constructor; assumption
        constructor <;> assumption
        assumption
      · subst t₁_empty; rw [Finset.empty_union] at t_decomp; subst t_decomp
        left; constructor; constructor; assumption

        constructor
        apply X.down_closed su₁_in_X
        apply Finset.union_subset_union_left
        cases' t₂_in_bd with t_in_bd t_empty
        · rw [simplexBoundary_mem_iff_subset] at t_in_bd
          choose t_sss_s t_ne using t_in_bd
          choose t_ss_s t_ne_s using t_sss_s
          assumption
        · rw [t_empty]; apply Finset.empty_subset

        rw [ne_eq, Finset.union_eq_empty, not_and_or]
        right; exact face_nonempty u₁_in_X

        rw [← Finset.subset_empty] at tu_disj ⊢
        apply subset_trans _ tu_disj
        apply Finset.inter_subset_inter_left
        rw [u_decomp]
        apply Finset.subset_union_right

        have stu₁_diff_in_link : s \ t ∪ u₁ ∈ Lk(X, t).faces ∧ s \ t ∩ u₁ = ∅ :=
        by
          apply stellar_subdiv_anticomm_link_left_bd_stu_mem_link
            X s t u ∅ u₁ t u'₂ ∅ t_in_X tu_disj su₁_disj

          rw [Finset.empty_union]; assumption
          rw [Finset.union_empty]
          rw [Finset.empty_union]; assumption
          rw [Finset.sdiff_empty]

          cases' t₂_in_bd with t_in_bd t_empty
          · rw [simplexBoundary_mem_iff_subset] at t_in_bd
            choose t_sss_s t_ne using t_in_bd
            assumption
          · rw [t_empty, Finset.empty_ssubset, Finset.nonempty_iff_ne_empty]
            exact face_nonempty s_in_X

        choose stu₁_diff_in_link stu₁_diff_disj using stu₁_diff_in_link
        simp only [Link, Set.mem_setOf] at stu₁_diff_in_link
        choose stu₁_diff_in_X tstu₁_diff_in_X tstu₁_diff_disj using stu₁_diff_in_link

        constructor; constructor; assumption
        constructor <;> assumption
        assumption
    · right; assumption

    constructor; rw [← u'_decomp]; assumption
    exact face_nonempty u_in_join
  · subst u'₂_empty; rw [Finset.empty_union] at *; subst u_decomp
    cases' u₁_in_link with u₁_in_link u₁_empty
    rotate_left
    have contra : u ≠ ∅ := by exact face_nonempty u_in_join
    contradiction

    cases' tu_in_link with tu_in_link tu_empty
    rotate_left
    rw [Finset.union_eq_empty] at tu_empty
    choose t₁_empty u₁_empty using tu_empty
    have contra : u ≠ ∅ := by exact face_nonempty u_in_join
    contradiction

    cases' t₁_in_link with t₁_in_link t₁_empty
    · choose u_in_X su_in_X su_disj using u₁_in_link
      choose t₁_in_X st_in_X st_disj using t₁_in_link
      choose tu_in_X stu_in_X stu_disj using tu_in_link
      left; constructor; constructor; assumption

      apply stellar_subdiv_anticomm_link_left_bd_u_mem_link
        X s t u t₁ t₂ t_in_X tu_disj stu_in_X
      rw [Finset.union_comm]; assumption

      cases' t₂_in_bd with t₂_in_bd t₂_empty
      · rw [simplexBoundary_mem_iff_subset, Finset.ssubset_iff_subset_ne] at t₂_in_bd
        choose t₂_sss_s t₂_ne using t₂_in_bd
        choose t₂_ss_s t₂_ne_s using t₂_sss_s
        assumption
      · rw [t₂_empty]
        apply Finset.empty_subset

      rw [t_decomp, Finset.sdiff_union_distrib, st₁_eq_s, ← Finset.inter_sdiff_assoc, Finset.inter_self]
      have _ : Nonempty { x // x ∈ s } := by
        rw [Finset.nonempty_coe_sort, Finset.nonempty_iff_ne_empty]
        exact face_nonempty s_in_X
      apply @stellar_subdiv_anticomm_link_left_ad_st_nss_u _ 𝕜 _ _ _ _ _
        X s t u t₁ u t₂ ∅ _ x s_in_X x_nin_X t_in_X u_in_X tu_disj su_disj

      simp only [Set.mem_union, Set.mem_singleton_iff, Finset.union_empty, simplicialJoinProj_mem]
      cases' t₂_in_bd with t₂_in_bd t₂_empty
      · left; use ∅; constructor
        right; rfl
        use t₂; constructor
        left; assumption
        constructor
        rw [Finset.empty_union]
        exact face_nonempty t₂_in_bd
      · right; assumption

      assumption
      rw [Finset.union_empty]
    · subst t₁_empty
      simp only [Finset.empty_union] at t_decomp tu_in_link
      subst t_decomp

      choose u_in_X su_in_X su_disj using tu_in_link

      cases' t₂_in_bd with t₂_in_bd t₂_empty
      · rw [simplexBoundary_mem_iff_subset, Finset.ssubset_iff_subset_ne] at t₂_in_bd
        choose t_sss_s t_ne using t₂_in_bd
        choose t_ss_s t_ne_s using t_sss_s

        left; constructor; constructor; assumption

        constructor
        apply X.down_closed su_in_X
        apply Finset.union_subset_union_left
        assumption

        assumption
        assumption

        simp only [Finset.subset_iff, not_forall, Finset.mem_sdiff]
        simp only [ne_eq, Finset.ext_iff, not_forall, not_iff] at t_ne_s
        choose a t_ne_s using t_ne_s
        use a

        by_cases a_in_t : a ∈ t
        rw [Finset.subset_iff] at t_ss_s
        specialize t_ss_s a_in_t
        rw [← t_ne_s] at t_ss_s
        contradiction

        have a_in_st : a ∈ s ∧ a ∉ t :=
        by
          rw [← t_ne_s]; constructor <;> assumption
        use a_in_st
        rw [t_ne_s] at a_in_t
        rw [← Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_left] at su_disj
        specialize su_disj a_in_t
        assumption
      · have contra : t ≠ ∅ := by exact face_nonempty t_in_X
        contradiction

theorem stellar_subdiv_anticomm_link_left
    {X : AbstractSimplicialComplex E}
    {s t : Finset E}
    {x : E}
    {s_in_X : s ∈ X.faces}
    {x_nin_X : x ∉ X.vertices}
    (t_in_X : t ∈ X.faces)
    (t_in_star_bd : t ∈ ((π₁[𝕜] (disjoint_link_boundary X s)).coe ''ˢ (Lk(X, s) ⋆ ∂s)).faces)
  : Lk(σ(X, s, x; 𝕜, s_in_X, x_nin_X), t) ⊆
      σ(Lk(X, t), s \ t, x; 𝕜,
          @star_boundary_mem_link _ _ _ _ _ _ _ X s t s_in_X t_in_star_bd,
          not_mem_link_vertices x_nin_X) :=
by
  simp only [StellarSubdivision, AbstractSimplicialComplex.instHasUnion, SimplicialUnion]
  intro u u_in_link
  simp only [Link, Set.mem_sep_iff] at u_in_link
  choose u_in_subdiv tu_in_subdiv tu_disj using u_in_link
  cases' u_in_subdiv with u_in_star_comp u_in_join <;>

  -- Cases A, B resp.
  cases' tu_in_subdiv with tu_in_star_comp tu_in_join

  -- Cases C, D resp.
  apply stellar_subdiv_anticomm_link_left_ac <;> assumption
  apply stellar_subdiv_anticomm_link_left_ad <;> assumption
  apply stellar_subdiv_anticomm_link_left_bc <;> assumption
  apply stellar_subdiv_anticomm_link_left_bd <;> assumption

theorem stellar_subdiv_anticomm_link_right_e
    (X : AbstractSimplicialComplex E)
    (s t : Finset E)
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
  : ∀ u : Finset E,
      u ∈ (StarComplement Lk(X, t) (s \ t)).faces →
        u ∈ Lk(σ(X, s, x; 𝕜, s_in_X, x_nin_X), t).faces :=
by
  intro u u_in_star_comp
  simp only [Link, StarComplement, StellarSubdivision, SimplicialUnion] at u_in_star_comp ⊢
  simp only [Set.mem_union, Set.mem_sep_iff] at u_in_star_comp ⊢
  choose u_in_link st_nss_u using u_in_star_comp
  choose u_in_X tu_in_X tu_disj using u_in_link
  constructor; left; constructor
  assumption
  revert st_nss_u
  contrapose
  simp only [Classical.not_not]
  intro s_ss_u
  apply @Finset.Subset.trans _ _ s
  apply Finset.sdiff_subset
  assumption
  constructor; left; constructor
  assumption
  simp only [Finset.subset_iff, Classical.not_forall] at st_nss_u ⊢
  choose y y_in_st y_nin_u using st_nss_u
  simp only [Finset.mem_sdiff] at y_in_st
  choose y_in_s y_nin_t using y_in_st
  use y; constructor
  simp only [Finset.mem_union, not_or]
  constructor <;> assumption
  assumption
  assumption

theorem star_boundary_mem_compl
    (X : AbstractSimplicialComplex E)
    (s t : Finset E)
    (s_in_X : s ∈ X.faces)
    (t_in_X : t ∈ X.faces)
    (t_in_star_bd : t ∈ ((π₁[𝕜] (disjoint_link_boundary X s)).coe ''ˢ (Lk(X, s) ⋆ ∂s)).faces)
  : s \ t ∈ X.faces :=
by
  apply X.down_closed s_in_X
  apply Finset.sdiff_subset
  rw [simplicialJoinProj_mem] at t_in_star_bd
  choose t₁ t₁_in_link t₂ t₂_in_bd t_decomp t_ne using t_in_star_bd
  subst t_decomp

  rw [Link, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf] at t₁_in_link
  rw [Set.mem_union, Set.mem_singleton_iff, simplexBoundary_mem_iff_subset] at t₂_in_bd

  have st₁_eq_s : s \ t₁ = s :=
  by
    cases' t₁_in_link with t₁_in_link t₁_empty
    · choose t₁_in_X st₁_in_X st₁_disj using t₁_in_link
      rw [Finset.sdiff_eq_self_iff_disjoint, Finset.disjoint_iff_inter_eq_empty]
      assumption
    · rw [t₁_empty, Finset.sdiff_empty]

  have st₂_ne : s \ t₂ ≠ ∅ :=
  by
    cases' t₂_in_bd with t₂_in_bd t₂_empty
    · choose t₂_sss_s t₂_ne using t₂_in_bd
      rw [ne_eq, Finset.sdiff_eq_empty_iff_subset, Finset.not_subset]
      apply Finset.exists_of_ssubset t₂_sss_s
    · rw [t₂_empty, Finset.sdiff_empty, ← Finset.nonempty_iff_ne_empty, Finset.nonempty_iff_ne_empty]
      exact face_nonempty s_in_X

  rw [Finset.sdiff_union_distrib, st₁_eq_s, ← Finset.inter_sdiff_assoc, Finset.inter_self]
  assumption

theorem stellar_subdiv_anticomm_link_right_f
    (X : AbstractSimplicialComplex E)
    (s t : Finset E)
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (t_in_X : t ∈ X.faces)
    (t_in_star_bd : t ∈ ((π₁[𝕜] (disjoint_link_boundary X s)).coe ''ˢ (Lk(X, s) ⋆ ∂s)).faces)
  : ∀ u : Finset E,
      u ∈ ((π₁[𝕜] (@disjoint_barycenter_join_boundary_link _ 𝕜 _ _ _ _ _ _ _ _
                    (@star_boundary_mem_link _ _ _ _ _ _ _ X s t s_in_X t_in_star_bd)
                    (not_mem_link_vertices x_nin_X))).coe
            ''ˢ (((π₁[𝕜] (disjoint_barycenter_boundary (star_boundary_mem_compl X s t s_in_X t_in_X t_in_star_bd) x_nin_X)).coe
              ''ˢ (simplex {x} ⋆ ∂(s \ t))) ⋆
                Lk(Lk(X, t), s \ t))).faces →
        u ∈ Lk(σ(X, s, x; 𝕜, s_in_X, x_nin_X), t).faces :=
by
  intro u u_in_join
  simp only [Link, StarComplement, StellarSubdivision, AbstractSimplicialComplex.instHasUnion, SimplicialUnion] at u_in_join ⊢
  simp only [Set.mem_union, Set.mem_sep_iff, Set.mem_setOf_eq]
  rw [simplicialJoinProj_mem] at u_in_join
  choose u'₂ u'₂_in_join u₁ u₁_in_link u_decomp u_ne using u_in_join
  simp only [Set.mem_union, Set.mem_singleton_iff, simplicialJoinProj_mem] at u'₂_in_join
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_sep_iff, Set.mem_setOf_eq] at u₁_in_link

  rw [simplicialJoinProj_mem] at t_in_star_bd
  choose t₁ t₁_in_link t₂ t₂_in_bd t_decomp t_ne using t_in_star_bd
  simp only [Link, Set.mem_union, Set.mem_singleton_iff, Set.mem_sep_iff] at t₁_in_link
  simp only [Set.mem_union, Set.mem_singleton_iff] at t₂_in_bd

  have st₁_eq_s : s \ t₁ = s :=
  by
    cases' t₁_in_link with t₁_in_link t₁_empty
    · choose t₁_in_X st₁_in_X st₁_disj using t₁_in_link
      rw [Finset.sdiff_eq_self_iff_disjoint, Finset.disjoint_iff_inter_eq_empty]
      assumption
    · rw [t₁_empty, Finset.sdiff_empty]

  have st₂_ne : s \ t₂ ≠ ∅ :=
  by
    cases' t₂_in_bd with t₂_in_bd t₂_empty
    · rw [simplexBoundary_mem_iff_subset] at t₂_in_bd
      choose t₂_sss_s t₂_ne using t₂_in_bd
      rw [ne_eq, Finset.sdiff_eq_empty_iff_subset, Finset.not_subset]
      apply Finset.exists_of_ssubset t₂_sss_s
    · rw [t₂_empty, Finset.sdiff_empty, ← Finset.nonempty_iff_ne_empty, Finset.nonempty_iff_ne_empty]
      exact face_nonempty s_in_X

  have s_nss_u : u₁ = ∅ ∨ u'₂ = ∅ → ¬s ⊆ u :=
  by
    intro u_empty
    cases' u_empty with u₁_empty u'₂_empty
    · subst u₁_empty; rw [Finset.union_empty] at u_decomp; subst u_decomp t_decomp
      cases' u'₂_in_join with u'₂_in_join u'₂_empty
      rotate_left; contradiction

      choose u₃ u₃_in_barycenter u₂ u₂_in_bd u_decomp u_ne using u'₂_in_join
      simp only [simplex, Set.mem_diff_singleton, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at u₃_in_barycenter
      simp only [Finset.sdiff_union_distrib, st₁_eq_s, ← Finset.inter_sdiff_assoc, Finset.inter_self,
        simplexBoundary_mem_iff_subset] at u₂_in_bd

      cases' u₂_in_bd with u₂_in_bd u₂_empty
      · choose u₂_sss_st₂ u₂_ne using u₂_in_bd
        simp only [Finset.ssubset_def] at u₂_sss_st₂
        simp only [u_decomp, Finset.subset_iff, not_forall, Classical.not_imp] at u₂_sss_st₂ ⊢
        simp only [Finset.mem_sdiff] at u₂_sss_st₂
        simp only [Finset.mem_union, not_or]

        choose u₂_ss_st₂ st₂_nss_u₂ using u₂_sss_st₂
        choose a a_in_st₂ x_nin_u₂ using st₂_nss_u₂
        choose a_in_s a_nin_t₂ using a_in_st₂
        use a; use a_in_s; constructor

        cases' u₃_in_barycenter with u₃_in_barycenter u₃_empty
        · choose u₃_in_barycenter u₃_ne using u₃_in_barycenter
          cases' u₃_in_barycenter with contra u₃_eq_x; contradiction
          rw [u₃_eq_x, Finset.mem_singleton]
          by_cases a_eq_x : a = x
          rotate_left; assumption
          rw [← a_eq_x] at x_nin_X
          have contra : a ∈ X.vertices :=
          by
            rw [vertices_setOf, Set.mem_setOf]
            use s
          contradiction
        · rw [u₃_empty]; apply Finset.notMem_empty
        assumption
      · rw [u₂_empty, Finset.union_empty] at u_decomp; subst u_decomp
        cases' u₃_in_barycenter with u₃_in_barycenter u₃_empty
        rotate_left; contradiction
        choose u₃_in_barycenter u₃_ne using u₃_in_barycenter
        cases' u₃_in_barycenter with contra u₃_eq_x; contradiction

        rw [u₃_eq_x, Finset.subset_singleton_iff, not_or]
        constructor; exact face_nonempty s_in_X
        by_cases s_eq_x : s = {x}
        rotate_left; assumption
        have contra : x ∈ X.vertices :=
        by
          rw [vertices_setOf, Set.mem_setOf]
          use s; constructor; assumption
          rw [s_eq_x]; apply Finset.mem_singleton_self
        contradiction
    · subst u'₂_empty; rw [Finset.empty_union] at u_decomp; subst u_decomp t_decomp
      cases' u₁_in_link with u₁_in_link u₁_empty
      rotate_left; contradiction

      choose u_in_link stu_in_link stu_disj using u₁_in_link
      choose u_in_X tu_in_X tu_disj using u_in_link
      choose stu_in_X tstu_in_X tstu_disj using stu_in_link

      simp only [ne_eq, Finset.sdiff_eq_empty_iff_subset, Finset.subset_iff, not_forall, Classical.not_imp] at st₂_ne
      simp only [Finset.eq_empty_iff_forall_notMem, Finset.mem_inter, not_and] at stu_disj
      choose a a_in_s a_nin_t₂ using st₂_ne
      have a_in_st₂ : a ∈ s \ t₂ :=
      by
        rw [Finset.mem_sdiff]
        constructor <;> assumption
      rw [Finset.sdiff_union_distrib, st₁_eq_s, ← Finset.inter_sdiff_assoc, Finset.inter_self] at stu_disj stu_in_X
      specialize stu_disj a a_in_st₂

      simp only [ne_eq, Finset.sdiff_eq_empty_iff_subset, Finset.subset_iff, not_forall, Classical.not_imp]
      use a

  have st₁t₂_ne : Nonempty {x // x ∈ s \ (t₁ ∪ t₂)} :=
  by
    rw [Finset.nonempty_coe_sort, Finset.nonempty_iff_ne_empty, Finset.sdiff_union_distrib, st₁_eq_s,
      ← Finset.inter_sdiff_assoc, Finset.inter_self]
    assumption

  cases' u'₂_in_join with u'₂_in_join u'₂_empty <;>
  cases' u₁_in_link with u₁_in_link u₁_empty
  -- u'₂, u₁ ≠ ∅
  · choose u_in_link stu_in_link stu_disj using u₁_in_link
    choose u_in_X tu_in_X tu_disj using u_in_link
    choose stu_in_X tstu_in_X tstu_disj using stu_in_link
    choose u₃ u₃_in_barycenter u₂ u₂_in_bd u_decomp u_ne using u'₂_in_join
    subst u_decomp t_decomp

    constructor; right
    rw [simplicialJoinProj_mem]
    use u₃ ∪ u₂; constructor; left
    rw [simplicialJoinProj_mem]
    use u₃; constructor
    rw [Set.mem_union, Set.mem_singleton_iff]
    assumption
    use u₂; constructor
    rw [Set.mem_union, Set.mem_singleton_iff]
    cases' u₂_in_bd with u₂_in_bd u₂_empty
    · left; apply isSubcomplex_face_imp_face
      assumption
      simp only [AbstractSimplicialComplex.instHasSubset, IsSubcomplex]
      apply simplexBoundary_subsimplex_subcomplex
      apply Finset.sdiff_subset
    · right; assumption

    constructor; rfl; assumption

    use u₁; constructor
    rw [Set.mem_union, Set.mem_setOf]
    left; constructor; assumption
    constructor
    rw [Finset.sdiff_union_distrib, ← Finset.union_assoc, Finset.union_inter_distrib_left] at tstu_in_X
    rw [Finset.union_comm t₁, Finset.union_assoc, Finset.union_sdiff_self_eq_union] at tstu_in_X
    rw [Finset.union_comm t₂ t₁, Finset.union_assoc, Finset.union_sdiff_self_eq_union] at tstu_in_X
    apply X.down_closed tstu_in_X
    rw [← Finset.union_assoc t₂, Finset.union_comm t₂ t₁, Finset.union_assoc t₁, Finset.inter_self, ← Finset.union_assoc,
      Finset.union_assoc]
    apply Finset.subset_union_right

    rw [ne_eq, Finset.union_eq_empty, not_and_or]
    left; exact face_nonempty s_in_X

    rw [← Finset.union_empty (s \ (t₁ ∪ t₂) ∩ u₁), ← tu_disj, ← Finset.union_inter_distrib_right, tu_disj] at stu_disj
    rw [Finset.sdiff_union_distrib, st₁_eq_s, ← Finset.inter_sdiff_assoc, Finset.inter_self] at stu_disj
    rw [Finset.union_comm t₁, ← Finset.union_assoc, Finset.sdiff_union_self_eq_union] at stu_disj
    rw [← Finset.subset_empty] at stu_disj ⊢
    apply @subset_trans _ _ _ _ ((s ∪ t₂ ∪ t₁) ∩ u₁)
    apply Finset.inter_subset_inter_right
    rw [Finset.union_assoc]
    apply Finset.subset_union_left
    assumption

    constructor; assumption
    rw [u_decomp, ne_eq, Finset.union_eq_empty, not_and_or]
    right; exact face_nonempty u_in_X

    constructor; right
    rw [simplicialJoinProj_mem]
    use (u₃ ∪ (u₂ ∪ t₂)); constructor
    rw [Set.mem_union, simplicialJoinProj_mem]
    left; use u₃; constructor
    rw [Set.mem_union, Set.mem_singleton_iff]
    assumption
    use (u₂ ∪ t₂); constructor
    rw [Set.mem_union, Set.mem_singleton_iff]
    by_cases u₂t₂_empty : u₂ ∪ t₂ = ∅
    right; assumption

    left
    rw [simplexBoundary_mem_iff_subset, Finset.ssubset_iff_subset_ne]
    constructor; constructor
    apply Finset.union_subset
    cases' u₂_in_bd with u₂_in_bd u₂_empty
    · rw [simplexBoundary_mem_iff_subset] at u₂_in_bd
      choose u₂_sss_st₁t₂ u₂_ne using u₂_in_bd
      apply @subset_trans _ _ _ _ (s \ (t₁ ∪ t₂))
      rw [Finset.ssubset_def] at u₂_sss_st₁t₂
      choose u₂_ss_st₁t₂ st₁t₂_nss_u₂ using u₂_sss_st₁t₂
      assumption
      apply Finset.sdiff_subset
    · rw [u₂_empty]; apply Finset.empty_subset
    cases' t₂_in_bd with t₂_in_bd t₂_empty
    · rw [simplexBoundary_mem_iff_subset] at t₂_in_bd
      choose t₂_sss_s t₂_ne using t₂_in_bd
      rw [Finset.ssubset_def] at t₂_sss_s
      choose t₂_ss_s s_nss_t₂ using t₂_sss_s
      assumption
    · rw [t₂_empty]; apply Finset.empty_subset

    cases' u₂_in_bd with u₂_in_bd u₂_empty
    · rw [simplexBoundary_mem_iff_subset] at u₂_in_bd
      choose u₂_sss_st₁t₂ u₂_ne using u₂_in_bd
      cases' t₂_in_bd with t₂_in_bd t₂_empty
      · rw [simplexBoundary_mem_iff_subset, Finset.ssubset_iff_of_subset] at t₂_in_bd
        choose t₂_sss_s t₂_ne using t₂_in_bd
        choose a a_in_s a_nin_t₂ using t₂_sss_s

        rw [Finset.ssubset_iff_of_subset] at u₂_sss_st₁t₂
        choose b b_in_st₁t₂ b_nin_u₂ using u₂_sss_st₁t₂
        rw [Finset.sdiff_union_distrib, st₁_eq_s, ← Finset.inter_sdiff_assoc, Finset.inter_self, Finset.mem_sdiff] at b_in_st₁t₂
        choose b_in_s b_nin_t₂ using b_in_st₁t₂

        simp only [ne_eq, Finset.ext_iff, not_forall, not_iff, Finset.mem_union, not_or]
        use b; constructor
        intro b_in_u₂t₂; assumption
        intro b_in_s; constructor <;> assumption

        rw [Finset.ssubset_iff_subset_ne] at u₂_sss_st₁t₂
        choose u₂_ss_st₁t₂ u₂_ne_st₁t₂ using u₂_sss_st₁t₂
        assumption

        rw [Finset.ssubset_iff_subset_ne] at t₂_in_bd
        choose t₂_sss_s t₂_ne using t₂_in_bd
        choose t₂_ss_s t₂_ne_s using t₂_sss_s
        assumption
      · rw [t₂_empty, Finset.union_empty]
        rw [Finset.ssubset_iff_subset_ne] at u₂_sss_st₁t₂
        choose u₂_ss_st₁t₂ u₂_ne_s using u₂_sss_st₁t₂
        rw [Finset.sdiff_union_distrib, st₁_eq_s, ← Finset.inter_sdiff_assoc, Finset.inter_self, t₂_empty, Finset.sdiff_empty] at u₂_ne_s
        assumption
    · rw [u₂_empty, Finset.empty_union]
      cases' t₂_in_bd with t₂_in_bd t₂_empty
      · rw [simplexBoundary_mem_iff_subset, Finset.ssubset_iff_subset_ne] at t₂_in_bd
        choose t₂_sss_s t₂_ne using t₂_in_bd
        choose t₂_ss_s t₂_ne_s using t₂_sss_s
        assumption
      · rw [t₂_empty]; symm
        exact face_nonempty s_in_X

    assumption

    constructor; rfl
    rw [← Finset.union_assoc, ne_eq, Finset.union_eq_empty, not_and_or]
    left; assumption

    use (u₁ ∪ t₁); constructor
    rw [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf]
    left; constructor
    apply X.down_closed tu_in_X
    rw [Finset.union_comm _ u₁, ← Finset.union_assoc]
    apply Finset.subset_union_left
    rw [ne_eq, Finset.union_eq_empty, not_and_or]
    left; exact face_nonempty u_in_X

    constructor
    rw [Finset.sdiff_union_distrib, ← Finset.union_assoc, Finset.union_inter_distrib_left] at tstu_in_X
    rw [Finset.union_comm t₁, Finset.union_assoc, Finset.union_sdiff_self_eq_union] at tstu_in_X
    rw [Finset.union_comm t₂ t₁, Finset.union_assoc, Finset.union_sdiff_self_eq_union] at tstu_in_X
    apply X.down_closed tstu_in_X
    rw [← Finset.union_assoc t₂, Finset.union_comm t₂ t₁, Finset.union_assoc t₁, Finset.inter_self,
      ← Finset.union_assoc t₁, Finset.union_assoc, Finset.union_comm (t₁ ∪ t₂), ← Finset.union_assoc (s ∪ u₁),
      Finset.union_assoc s]
    apply Finset.subset_union_left

    rw [ne_eq, Finset.union_eq_empty, not_and_or]
    left; exact face_nonempty s_in_X

    rw [Finset.inter_union_distrib_left, Finset.union_eq_empty]
    constructor

    rw [← Finset.union_empty (s \ (t₁ ∪ t₂) ∩ u₁), ← tu_disj, ← Finset.union_inter_distrib_right, tu_disj] at stu_disj
    rw [Finset.sdiff_union_distrib, st₁_eq_s, ← Finset.inter_sdiff_assoc, Finset.inter_self] at stu_disj
    rw [Finset.union_comm t₁, ← Finset.union_assoc, Finset.sdiff_union_self_eq_union] at stu_disj
    rw [← Finset.subset_empty] at stu_disj ⊢
    apply @subset_trans _ _ _ _ ((s ∪ t₂ ∪ t₁) ∩ u₁)
    apply Finset.inter_subset_inter_right
    rw [Finset.union_assoc]
    apply Finset.subset_union_left
    assumption

    cases' t₁_in_link with t₁_in_link t₁_empty
    · choose t₁_in_X st₁_in_X st₁_disj using t₁_in_link
      assumption
    · rw [t₁_empty, Finset.inter_empty]

    constructor
    rw [u_decomp, Finset.union_comm u₂, Finset.union_comm u₁, ← Finset.union_assoc u₃, Finset.union_comm u₃ t₂,
      Finset.union_assoc t₂, Finset.union_assoc t₂, Finset.union_comm (u₃ ∪ u₂) (t₁ ∪ u₁), Finset.union_assoc t₁ u₁,
      Finset.union_comm u₁, ← Finset.union_assoc t₂, Finset.union_comm t₂]

    rw [ne_eq, Finset.union_eq_empty, not_and_or]
    left; assumption

    simp only [u_decomp, Finset.inter_union_distrib_left]
    have tu₃_disj : (t₁ ∪ t₂) ∩ u₃ = ∅ :=
    by
      cases' u₃_in_barycenter with u₃_in_barycenter u₃_empty
      · simp only [simplex, Set.mem_diff_singleton, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at u₃_in_barycenter
        choose u₃_eq_x u₃_ne using u₃_in_barycenter
        cases' u₃_eq_x with u₃_empty u₃_eq_x; contradiction

        rw [u₃_eq_x, Finset.inter_singleton_of_notMem]
        revert x_nin_X; contrapose; simp only [not_not]
        intros x_in_t
        rw [vertices_setOf, Set.mem_setOf]
        use t₁ ∪ t₂
      · rw [u₃_empty, Finset.inter_empty]
    have tu₂_disj : (t₁ ∪ t₂) ∩ u₂ = ∅ :=
    by
      cases' u₂_in_bd with u₂_in_bd u₂_empty
      · rw [simplexBoundary_mem_iff_subset, Finset.ssubset_iff_subset_ne] at u₂_in_bd
        choose u₂_sss_st₁t₂ u₂_ne using u₂_in_bd
        choose u₂_ss_st₁t₂ u₂_ne_st₁t₂ using u₂_sss_st₁t₂
        rw [Finset.subset_sdiff, Finset.disjoint_iff_inter_eq_empty, Finset.inter_comm] at u₂_ss_st₁t₂
        choose u₂_ss_s tu₂_disj using u₂_ss_st₁t₂
        assumption
      · rw [u₂_empty, Finset.inter_empty]
    simp only [tu₃_disj, tu₂_disj, tu_disj, Finset.union_empty]
  -- u'₂ ≠ ∅, u₁ = ∅
  · have spec : u₁ = ∅ ∨ u'₂ = ∅ := by subst u₁_empty; left; rfl
    specialize s_nss_u spec

    subst u₁_empty; rw [Finset.union_empty] at u_decomp; subst u_decomp t_decomp
    choose u₃ u₃_in_barycenter u₂ u₂_in_bd u_decomp u_ne using u'₂_in_join
    subst u_decomp
    constructor; right

    rw [simplicialJoinProj_mem]
    use (u₃ ∪ u₂); constructor
    rw [Set.mem_union, simplicialJoinProj_mem]
    left; use u₃; constructor
    rw [Set.mem_union, Set.mem_singleton_iff]
    assumption
    use u₂; constructor
    rw [Set.mem_union, Set.mem_singleton_iff]
    cases' u₂_in_bd with u₂_in_bd u₂_empty
    · left; apply isSubcomplex_face_imp_face
      assumption
      simp only [AbstractSimplicialComplex.instHasSubset, IsSubcomplex]
      apply simplexBoundary_subsimplex_subcomplex
      apply Finset.sdiff_subset
    · right; assumption

    constructor; rfl; assumption

    use ∅; constructor
    rw [Set.mem_union]
    right; apply Set.mem_singleton

    constructor
    rw [Finset.union_empty]
    assumption

    constructor; right
    rw [simplicialJoinProj_mem]
    use (u₃ ∪ (u₂ ∪ t₂)); constructor
    rw [Set.mem_union, simplicialJoinProj_mem]
    left; use u₃; constructor
    rw [Set.mem_union, Set.mem_singleton_iff]
    assumption
    use (u₂ ∪ t₂); constructor
    rw [Set.mem_union, Set.mem_singleton_iff]
    by_cases u₂t₂_empty : u₂ ∪ t₂ = ∅
    right; assumption

    left
    rw [simplexBoundary_mem_iff_subset, Finset.ssubset_iff_subset_ne]
    constructor; constructor
    apply Finset.union_subset
    cases' u₂_in_bd with u₂_in_bd u₂_empty
    · rw [simplexBoundary_mem_iff_subset] at u₂_in_bd
      choose u₂_sss_st₁t₂ u₂_ne using u₂_in_bd
      apply @subset_trans _ _ _ _ (s \ (t₁ ∪ t₂))
      rw [Finset.ssubset_def] at u₂_sss_st₁t₂
      choose u₂_ss_st₁t₂ st₁t₂_nss_u₂ using u₂_sss_st₁t₂
      assumption
      apply Finset.sdiff_subset
    · rw [u₂_empty]; apply Finset.empty_subset
    cases' t₂_in_bd with t₂_in_bd t₂_empty
    · rw [simplexBoundary_mem_iff_subset] at t₂_in_bd
      choose t₂_sss_s t₂_ne using t₂_in_bd
      rw [Finset.ssubset_def] at t₂_sss_s
      choose t₂_ss_s s_nss_t₂ using t₂_sss_s
      assumption
    · rw [t₂_empty]; apply Finset.empty_subset

    cases' u₂_in_bd with u₂_in_bd u₂_empty
    · rw [simplexBoundary_mem_iff_subset] at u₂_in_bd
      choose u₂_sss_st₁t₂ u₂_ne using u₂_in_bd
      cases' t₂_in_bd with t₂_in_bd t₂_empty
      · rw [simplexBoundary_mem_iff_subset, Finset.ssubset_iff_of_subset] at t₂_in_bd
        choose t₂_sss_s t₂_ne using t₂_in_bd
        choose a a_in_s a_nin_t₂ using t₂_sss_s

        rw [Finset.ssubset_iff_of_subset] at u₂_sss_st₁t₂
        choose b b_in_st₁t₂ b_nin_u₂ using u₂_sss_st₁t₂
        rw [Finset.sdiff_union_distrib, st₁_eq_s, ← Finset.inter_sdiff_assoc, Finset.inter_self, Finset.mem_sdiff] at b_in_st₁t₂
        choose b_in_s b_nin_t₂ using b_in_st₁t₂

        simp only [ne_eq, Finset.ext_iff, not_forall, not_iff, Finset.mem_union, not_or]
        use b; constructor
        intro b_in_u₂t₂; assumption
        intro b_in_s; constructor <;> assumption

        rw [Finset.ssubset_iff_subset_ne] at u₂_sss_st₁t₂
        choose u₂_ss_st₁t₂ u₂_ne_st₁t₂ using u₂_sss_st₁t₂
        assumption

        rw [Finset.ssubset_iff_subset_ne] at t₂_in_bd
        choose t₂_sss_s t₂_ne using t₂_in_bd
        choose t₂_ss_s t₂_ne_s using t₂_sss_s
        assumption
      · rw [t₂_empty, Finset.union_empty]
        rw [Finset.ssubset_iff_subset_ne] at u₂_sss_st₁t₂
        choose u₂_ss_st₁t₂ u₂_ne_s using u₂_sss_st₁t₂
        rw [Finset.sdiff_union_distrib, st₁_eq_s, ← Finset.inter_sdiff_assoc, Finset.inter_self, t₂_empty, Finset.sdiff_empty] at u₂_ne_s
        assumption
    · rw [u₂_empty, Finset.empty_union]
      cases' t₂_in_bd with t₂_in_bd t₂_empty
      · rw [simplexBoundary_mem_iff_subset, Finset.ssubset_iff_subset_ne] at t₂_in_bd
        choose t₂_sss_s t₂_ne using t₂_in_bd
        choose t₂_ss_s t₂_ne_s using t₂_sss_s
        assumption
      · rw [t₂_empty]; symm
        exact face_nonempty s_in_X

    assumption

    constructor; rfl
    rw [← Finset.union_assoc, ne_eq, Finset.union_eq_empty, not_and_or]
    left; assumption

    use t₁; constructor
    rw [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf]
    assumption

    constructor
    rw [Finset.union_comm, Finset.union_comm t₁, ← Finset.union_assoc, Finset.union_assoc u₃]
    rw [ne_eq, Finset.union_eq_empty, not_and_or]
    right; assumption

    rw [Finset.inter_union_distrib_left]
    have tu₃_disj : (t₁ ∪ t₂) ∩ u₃ = ∅ :=
    by
      cases' u₃_in_barycenter with u₃_in_barycenter u₃_empty
      · simp only [simplex, Set.mem_diff_singleton, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at u₃_in_barycenter
        choose u₃_eq_x u₃_ne using u₃_in_barycenter
        cases' u₃_eq_x with u₃_empty u₃_eq_x; contradiction

        rw [u₃_eq_x, Finset.inter_singleton_of_notMem]
        revert x_nin_X; contrapose; simp only [not_not]
        intros x_in_t
        rw [vertices_setOf, Set.mem_setOf]
        use t₁ ∪ t₂
      · rw [u₃_empty, Finset.inter_empty]
    have tu₂_disj : (t₁ ∪ t₂) ∩ u₂ = ∅ :=
    by
      cases' u₂_in_bd with u₂_in_bd u₂_empty
      · rw [simplexBoundary_mem_iff_subset, Finset.ssubset_iff_subset_ne] at u₂_in_bd
        choose u₂_sss_st₁t₂ u₂_ne using u₂_in_bd
        choose u₂_ss_st₁t₂ u₂_ne_st₁t₂ using u₂_sss_st₁t₂
        rw [Finset.subset_sdiff, Finset.disjoint_iff_inter_eq_empty, Finset.inter_comm] at u₂_ss_st₁t₂
        choose u₂_ss_s tu₂_disj using u₂_ss_st₁t₂
        assumption
      · rw [u₂_empty, Finset.inter_empty]
    rw [tu₃_disj, tu₂_disj, Finset.union_empty]
  -- u'₂ = ∅, u₁ ≠ ∅
  · choose u_in_link stu_in_link stu_disj using u₁_in_link
    choose u_in_X tu_in_X tu_disj using u_in_link
    choose stu_in_X tstu_in_X tstu_disj using stu_in_link

    have spec : u₁ = ∅ ∨ u'₂ = ∅ := by rw [u'₂_empty]; right; rfl
    specialize s_nss_u spec

    subst u'₂_empty; rw [Finset.empty_union] at u_decomp; subst u_decomp t_decomp
    constructor; constructor; constructor <;> assumption

    constructor
    left; constructor; assumption
    simp only [Finset.subset_iff, not_forall, Finset.mem_union, not_or]
    simp only [← Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_left] at stu_disj
    have a_in_st₁t₂ : ∃ a : E, a ∈ s \ (t₁ ∪ t₂) :=
    by
      simp only [ne_eq, Finset.eq_empty_iff_forall_notMem, not_forall, not_not] at st₂_ne
      simp only [Finset.sdiff_union_distrib, st₁_eq_s, ← Finset.inter_sdiff_assoc, Finset.inter_self]
      assumption
    choose a a_in_st₁t₂ using a_in_st₁t₂
    specialize stu_disj a_in_st₁t₂
    rw [Finset.mem_sdiff, Finset.mem_union, not_or] at a_in_st₁t₂
    choose a_in_s a_nin_t₁t₂ using a_in_st₁t₂
    use a

    assumption
  -- u'₂, u₁ = ∅
  · rw [u'₂_empty, u₁_empty, Finset.union_empty] at u_decomp
    contradiction

theorem stellar_subdiv_anticomm_link_right
    {X : AbstractSimplicialComplex E}
    {s t : Finset E}
    {x : E}
    {s_in_X : s ∈ X.faces}
    {x_nin_X : x ∉ X.vertices}
    (t_in_X : t ∈ X.faces)
    (t_in_star_bd : t ∈ ((π₁[𝕜] (disjoint_link_boundary X s)).coe ''ˢ (Lk(X, s) ⋆ ∂s)).faces)
  : σ(Lk(X, t), s \ t, x; 𝕜,
        @star_boundary_mem_link _ _ _ _ _ _ _ X s t s_in_X t_in_star_bd,
        not_mem_link_vertices x_nin_X) ⊆
      Lk(σ(X, s, x; 𝕜, s_in_X, x_nin_X), t) :=
by
  simp only [StellarSubdivision, AbstractSimplicialComplex.instHasUnion, SimplicialUnion]
  intro u u_in_subdiv
  simp only [Set.mem_union] at u_in_subdiv
  cases' u_in_subdiv with u_in_star_comp u_in_join

  -- Cases E + F, resp.
  apply stellar_subdiv_anticomm_link_right_e <;> assumption
  apply stellar_subdiv_anticomm_link_right_f <;> assumption

theorem stellar_subdiv_anticomm_link
    (X : AbstractSimplicialComplex E)
    (s t : Finset E)
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (t_in_X : t ∈ X.faces)
    (t_in_star_bd : t ∈ ((π₁[𝕜] (disjoint_link_boundary X s)).coe ''ˢ (Lk(X, s) ⋆ ∂s)).faces)
  : Lk(σ(X, s, x; 𝕜, s_in_X, x_nin_X), t) =
      σ(Lk(X, t), s \ t, x; 𝕜,
          @star_boundary_mem_link _ _ _ _ _ _ _ X s t s_in_X t_in_star_bd,
          not_mem_link_vertices x_nin_X) :=
by
  rw [AbstractSimplicialComplex.ext_iff, Set.Subset.antisymm_iff]
  exact ⟨stellar_subdiv_anticomm_link_left t_in_X t_in_star_bd,
    stellar_subdiv_anticomm_link_right t_in_X t_in_star_bd⟩
