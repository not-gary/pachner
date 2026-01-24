import Pachner.Stellar.StellarSubdivision

variable {E 𝕜 : Type _}
variable [DecidableEq E] [DecidableEq 𝕜]
variable [AddCommGroup E]
variable [Ring 𝕜] [Nontrivial 𝕜]

theorem stellar_subdiv_link_of_starComplement_left
    {X : AbstractSimplicialComplex E}
    {s t : Finset E} [s_ne : Nonempty s]
    {x : E}
    {s_in_X : s ∈ X.faces}
    {x_nin_X : x ∉ X.vertices}
    (t_in_star_comp : t ∈ X\St(X, s).faces)
  : t ∉ ((π₁[𝕜] (boundary_disjoint_link X s)).coe
      ''ˢ (Lk(X, s) ⋆ ∂s)).faces →
        Lk(σ(X, s, x; 𝕜, s_in_X, x_nin_X), t) ⊆
          Lk(X, t) :=
by
  intro t_nin_join
  simp only [starComplement, Set.mem_sep_iff] at t_in_star_comp
  choose t_in_X s_nss_t using t_in_star_comp
  simp only [Set.subset_def, link, stellarSubdivision, simplicialUnion, starComplement,
    Set.mem_union, Set.mem_sep_iff]
  intro u u_in_link
  choose u_in_subdiv ut_in_subdiv ut_disj using u_in_link
  cases' ut_in_subdiv with ut_in_star_comp ut_in_join
  -- Cases A, B resp.
  cases' u_in_subdiv with u_in_star_comp u_in_join
  -- Cases C, D resp.
  -- Case A + C.
  · choose u_in_X s_nss_u using u_in_star_comp
    choose ut_in_X s_nss_tu using ut_in_star_comp
    constructor; assumption
    constructor <;> assumption
  -- Case A + D.
  · choose tu_in_X s_nss_tu using ut_in_star_comp
    constructor
    apply X.down_closed tu_in_X
    apply Finset.subset_union_right
    apply face_nonempty _ _ u_in_join
    constructor <;> assumption
  -- Case B + (C/D).
  · rw [join_proj_disj_union_mem] at ut_in_join
    choose t' t'_in_join u' u'_in_join t₁ t₁_in_link u₁ u₁_in_link t_decomp u_decomp tu'_in_join
      tu₁_in_link using ut_in_join
    rw [Set.mem_union, join_proj_disj_union_mem] at tu'_in_join
    cases' tu'_in_join with tu'_in_join tu'_empty

    choose t₃ t₃_in_barycenter u₃ u₃_in_barycenter t₂ t₂_in_bd u₂ u₂_in_bd t'_decomp u'_decomp
      tu₃_in_barycenter tu₂_in_bd using tu'_in_join
    subst t'_decomp
    subst u'_decomp
    simp only [simplex, Set.mem_union, Set.mem_diff, Finset.mem_coe, Finset.mem_powerset,
      Finset.subset_singleton_iff, Set.mem_singleton_iff] at t₃_in_barycenter
    cases' t₃_in_barycenter with contra t₃_empty
    choose contra t₃_ne using contra
    cases' contra with contra contra; contradiction
    have x_in_X : x ∈ X.vertices :=
    by
      subst contra
      rw [t_decomp] at t_in_X
      rw [AbstractSimplicialComplex.mem_vertices]
      apply @X.down_closed ({x} ∪ t₂ ∪ t₁)
      assumption
      rw [Finset.union_assoc]
      apply Finset.subset_union_left
      apply Finset.singleton_ne_empty
    contradiction
    subst t₃_empty
    rw [Finset.empty_union] at t_decomp
    have contra : t ∈ ((π₁[𝕜] (boundary_disjoint_link X s)).coe ''ˢ (Lk(X, s) ⋆ ∂s)).faces :=
    by
      rw [join_proj_mem]
      use t₁; constructor; assumption
      use t₂; constructor; assumption
      rw [Finset.union_comm]
      constructor
      assumption
      apply face_nonempty X t t_in_X
    contradiction

    -- tu'_empty case.
    rw [Set.mem_singleton_iff, Finset.union_eq_empty] at tu'_empty
    choose t'_empty u'_empty using tu'_empty
    subst t'_empty u'_empty
    rw [Finset.empty_union] at t_decomp u_decomp
    subst t_decomp u_decomp
    choose tu_in_link tu_ne using tu₁_in_link
    rw [Set.mem_union] at tu_in_link u₁_in_link
    cases' tu_in_link with tu_in_link tu_empty

    simp only [link, Set.mem_sep_iff] at tu_in_link
    choose tu_in_X stu_in_X stu_disj using tu_in_link
    constructor
    cases' u₁_in_link with u_in_link u_empty
    simp only [link, Set.mem_sep_iff] at u_in_link
    choose u_in_X su_in_X su_disj using u_in_link
    assumption

    rw [Set.mem_singleton_iff] at u_empty
    have u_ne : u ≠ ∅ := by apply face_nonempty _ _ u_in_subdiv
    contradiction

    constructor <;> assumption

    rw [Set.mem_singleton_iff] at tu_empty
    contradiction

theorem stellar_subdiv_link_of_starComplement_right
    {X : AbstractSimplicialComplex E}
    {s t : Finset E} [s_ne : Nonempty s]
    {x : E}
    {s_in_X : s ∈ X.faces}
    {x_nin_X : x ∉ X.vertices}
    (t_in_star_comp : t ∈ X\St(X, s).faces)
  : t ∉ ((π₁[𝕜] (boundary_disjoint_link X s)).coe
      ''ˢ (Lk(X, s) ⋆ ∂s)).faces →
        Lk(X, t) ⊆
          Lk(σ(X, s, x; 𝕜, s_in_X, x_nin_X), t) :=
by
  intro t_nin_join
  simp only [starComplement, Set.mem_sep_iff] at t_in_star_comp
  choose t_in_X s_nss_t using t_in_star_comp
  simp only [Set.subset_def, link, stellarSubdivision, simplicialUnion, starComplement,
    Set.mem_union, Set.mem_sep_iff]
  intro u u_in_link
  choose u_in_X tu_in_X tu_disj using u_in_link
  by_cases s_ss_u : s ⊆ u
  · have t_in_link : t ∈ Lk(X, s).faces :=
    by
      simp only [link, Set.mem_sep_iff]
      constructor; assumption
      constructor
      apply @X.down_closed (t ∪ u)
      assumption
      rw [Finset.union_comm]
      apply Finset.union_subset_union_right
      assumption
      rw [ne_eq, Finset.union_eq_empty, not_and_or]
      right; apply face_nonempty X t t_in_X
      rw [← Finset.subset_empty]
      apply @Finset.Subset.trans _ _ (t ∩ u)
      rw [Finset.inter_comm]
      apply Finset.inter_subset_inter_left
      assumption
      rw [Finset.subset_empty]
      assumption
    simp only [join_proj_mem, not_exists, not_and_or] at t_nin_join
    specialize t_nin_join t

    cases' t_nin_join with t_nin_link u_nin_bd
    rw [Set.mem_union, Set.mem_singleton_iff, not_or] at t_nin_link
    choose t_nin_link t_ne using t_nin_link
    contradiction

    specialize u_nin_bd ∅
    cases' u_nin_bd with u_nin_bd t_ne_t
    rw [Set.mem_union, Set.mem_singleton_iff, not_or] at u_nin_bd
    choose u_nin_bd contra using u_nin_bd
    contradiction
    cases' t_ne_t with t_ne_t t_empty
    rw [Finset.union_empty] at t_ne_t; contradiction
    rw [not_not] at t_empty
    have t_ne : t ≠ ∅ := by apply face_nonempty X t t_in_X
    contradiction
  constructor
  left; constructor <;> assumption
  constructor
  left; constructor; assumption
  revert t_nin_join
  contrapose
  simp only [Classical.not_not]
  intro s_ss_tu
  rw [join_proj_mem]
  use t \ s; constructor
  by_cases ts_ne : t \ s = ∅
  rw [Set.mem_union, ts_ne]
  right; apply Set.mem_singleton

  simp only [link, Set.mem_union, Set.mem_sep_iff]
  left; constructor
  apply @X.down_closed t
  assumption
  apply Finset.sdiff_subset
  assumption
  constructor
  rw [Finset.union_sdiff_self_eq_union]
  apply @X.down_closed (t ∪ u)
  assumption
  apply @Finset.Subset.trans _ _ (s ∪ (t ∪ u))
  rw [← Finset.union_assoc]
  apply Finset.subset_union_left
  rw [← Finset.union_eq_right] at s_ss_tu
  apply Finset.subset_of_eq
  assumption

  rw [ne_eq, Finset.union_eq_empty, not_and_or]
  left; apply face_nonempty X s s_in_X

  rw [Finset.inter_comm]
  apply Finset.sdiff_inter_self
  use t ∩ s; constructor
  rw [Set.mem_union, simplexBoundary_mem_iff_subset, Finset.ssubset_iff_subset_ne]
  by_cases ts_ne : t ∩ s = ∅
  right
  rw [ts_ne]
  apply Set.mem_singleton

  left; constructor; constructor
  apply Finset.inter_subset_right
  rw [ne_eq, Finset.inter_eq_right]
  assumption; assumption
  rw [Finset.sdiff_union_inter]
  constructor; rfl; apply face_nonempty X t t_in_X
  assumption

theorem stellar_subdiv_link_of_starComplement
    (X : AbstractSimplicialComplex E)
    (s t : Finset E) [s_ne : Nonempty s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (t_in_star_comp : t ∈ X\St(X, s).faces)
  : t ∉ ((π₁[𝕜] (boundary_disjoint_link X s)).coe
      ''ˢ (Lk(X, s) ⋆ ∂s)).faces →
        Lk(σ(X, s, x; 𝕜, s_in_X, x_nin_X), t) =
          Lk(X, t) :=
by
  intro t_nin_join
  rw [AbstractSimplicialComplex.ext_iff, Set.Subset.antisymm_iff]
  exact ⟨stellar_subdiv_link_of_starComplement_left t_in_star_comp t_nin_join,
    stellar_subdiv_link_of_starComplement_right t_in_star_comp t_nin_join⟩
