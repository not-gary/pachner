import Pachner.Subcomplex.StarComplement
import Pachner.Constructions.JoinProjections

variable {E F 𝕜 : Type _}
variable [DecidableEq E] [DecidableEq F] [DecidableEq 𝕜]
variable [AddCommGroup E] [AddCommGroup F]
variable [Ring 𝕜] [Nontrivial 𝕜]

def stellarSubdivision
    (X : AbstractSimplicialComplex E)
    (s : Finset E)
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
  : AbstractSimplicialComplex E :=
    X\St(X, s) ∪
      (π₁[𝕜] (@barycenter_join_boundary_disjoint_link _ 𝕜 _ _ _ _ _ X s x s_in_X x_nin_X)).coe ''ˢ
        (((π₁[𝕜] (barycenter_disjoint_boundary X s x s_in_X x_nin_X)).coe ''ˢ (simplex {x} ⋆ ∂s : AbstractSimplicialComplex (E × 𝕜)))
          ⋆ Lk(X, s) : AbstractSimplicialComplex (E × 𝕜))

notation "σ(" X ", " s ", " x "; " 𝕜 ", " s_in_X ", " x_nin_X ")" =>
  @stellarSubdivision _ 𝕜 _ _ _ _ _ X s x s_in_X x_nin_X

instance stellarSubdivision.fintype
    (X : AbstractSimplicialComplex E) [Fintype X.faces]
    (s : Finset E)
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
  : Fintype σ(X, s, x; 𝕜, s_in_X, x_nin_X).faces :=
by
  simp only [stellarSubdivision, simplicialUnion]
  have star_comp_fin : Fintype ↥(X\St(X, s)).faces := by apply starComplement.fintype
  have barycenter_fin : Fintype ↥(simplex {x}).faces := by apply simplex.Fintype {x}
  have bd_fin : Fintype ↥(∂s).faces := by apply simplexBoundary.fintype
  have barycenter_bd_fin : Fintype ↥(simplex {x} ⋆ ∂s : AbstractSimplicialComplex (E × 𝕜)).faces := by
    apply @simplicialJoin.fintype _ _ _ _ _ _ _ (simplex {x}) barycenter_fin (∂s) bd_fin
  have proj_bary_bd_fin :
    Fintype ((π₁[𝕜] (barycenter_disjoint_boundary X s x s_in_X x_nin_X)).coe ''ˢ (simplex {x} ⋆ ∂s : AbstractSimplicialComplex (E × 𝕜))).faces :=
    by apply @SimplicialCoe.Fintype _ _ _ _ barycenter_bd_fin
  have link_fin : Fintype ↥Lk(X, s).faces := by apply link.fintype
  have proj_link_fin :
    Fintype
      ↥((π₁[𝕜] (barycenter_disjoint_boundary X s x s_in_X x_nin_X)).coe ''ˢ (simplex {x} ⋆ ∂s : AbstractSimplicialComplex (E × 𝕜))
        ⋆ Lk(X, s) : AbstractSimplicialComplex (E × 𝕜)).faces :=
    by apply @simplicialJoin.fintype _ _ _ _ _ _ _ _ proj_bary_bd_fin _ link_fin
  have join_fin :
    Fintype
      ↥((π₁[𝕜] (@barycenter_join_boundary_disjoint_link _ 𝕜 _ _ _ _ _ X s x s_in_X x_nin_X)).coe ''ˢ
          (((π₁[𝕜] (barycenter_disjoint_boundary X s x s_in_X x_nin_X)).coe ''ˢ (simplex {x} ⋆ ∂s : AbstractSimplicialComplex (E × 𝕜)))
            ⋆ Lk(X, s) : AbstractSimplicialComplex (E × 𝕜))).faces :=
    by apply @SimplicialCoe.Fintype _ _ _ _ proj_link_fin
  apply @Set.fintypeUnion _ _ _ _ star_comp_fin join_fin

theorem stellar_subdiv_preserves_dim
    (X : AbstractSimplicialComplex E) [X_fin : Fintype X.faces]
    (s : Finset E)
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
  : X.dim = σ(X, s, x; 𝕜, s_in_X, x_nin_X).dim :=
by
  simp only [AbstractSimplicialComplex.dim, le_antisymm_iff]
  constructor
  · rw [Finset.max'_le_iff]
    intro n n_X_dim
    rw [Finset.mem_union, Finset.mem_image] at n_X_dim
    cases' n_X_dim with n_X_dim n_neg_one

    choose t t_in_X dim_t_n using n_X_dim
    rw [Set.mem_toFinset] at t_in_X
    apply Finset.le_max'
    rw [Finset.mem_union, Finset.mem_image]
    left

    by_cases s_ss_t : s ⊆ t
    · have s_nontriv : ∃ a : E, a ∈ s :=
      by
        apply Finset.Nonempty.exists_mem
        rw [Finset.nonempty_iff_ne_empty]
        apply face_nonempty X s s_in_X

      choose a a_in_s using s_nontriv
      have a_in_t : a ∈ t := by apply Finset.mem_of_subset s_ss_t a_in_s
      use t \ {a} ∪ {x}; constructor
      simp only [Set.mem_toFinset]
      unfold stellarSubdivision
      simp only [AbstractSimplicialComplex.instHasUnion, simplicialUnion, Set.mem_union]
      right
      simp only [join_proj_mem, Set.mem_union]
      use {x} ∪ s \ {a}; constructor; left
      use {x}; constructor; left
      simp only [simplex, Finset.mem_coe, Set.mem_diff]
      constructor
      apply Finset.mem_powerset_self
      rw [Set.mem_singleton_iff, ← ne_eq]
      apply Finset.singleton_ne_empty

      use s \ {a}; constructor
      by_cases sa_empty : s \ {a} = ∅
      right; rw [Set.mem_singleton_iff]; assumption

      left
      have s_ne : Nonempty {x // x ∈ s} :=
      by
        rw [Finset.nonempty_coe_sort, Finset.nonempty_iff_ne_empty]
        apply face_nonempty X s s_in_X
      rw [simplexBoundary_mem_iff_subset]
      constructor

      apply Finset.sdiff_ssubset
      rw [Finset.singleton_subset_iff]
      assumption
      apply Finset.singleton_nonempty
      assumption

      constructor; rfl
      rw [ne_eq, Finset.union_eq_empty, not_and_or]
      left; apply Finset.singleton_ne_empty

      use(t \ {a}) \ s; constructor
      simp only [link, Set.mem_sep_iff]
      by_cases tas_empty : (t \ {a}) \ s = ∅
      right; rw [Set.mem_singleton_iff]; assumption

      left; constructor
      apply X.down_closed t_in_X
      apply @Finset.Subset.trans _ _ (t \ {a}) <;> apply Finset.sdiff_subset

      assumption

      constructor
      rw [Finset.union_sdiff_self_eq_union]
      apply X.down_closed t_in_X
      apply Finset.union_subset
      assumption
      apply Finset.sdiff_subset

      rw [ne_eq, Finset.union_eq_empty, not_and_or]
      left; apply face_nonempty X s s_in_X

      apply Finset.inter_sdiff_self
      rw [Finset.union_assoc, Finset.sdiff_sdiff_left', Finset.union_inter_distrib_left]
      have sa_ta_rw : s \ {a} ∪ t \ {a} = t \ {a} :=
      by
        rw [Finset.union_eq_right]
        apply Finset.sdiff_subset_sdiff
        assumption
        rfl
      have ts_inter_ta_rw : t \ s ∩ (t \ {a}) = t \ s :=
      by
        rw [Finset.inter_eq_left]
        apply Finset.sdiff_subset_sdiff
        rfl
        rw [Finset.singleton_subset_iff]
        assumption
      have tsa_rw : (t ∩ s) \ {a} = s \ {a} :=
      by
        have ts_rw : t ∩ s = s := by
          rw [Finset.inter_eq_right]
          assumption
        rw [ts_rw]
      have ts_union_sa_rw : t \ s ∪ s \ {a} = t \ {a} :=
      by
        apply Finset.sdiff_union_sdiff_cancel
        assumption
        rw [Finset.singleton_subset_iff]
        assumption
      have sa_ts_rw : s \ {a} ∪ t \ s = t \ {a} :=
      by
        conv_rhs =>
          rw [← @Finset.sdiff_union_inter _ _ t s, Finset.union_sdiff_distrib,
            Finset.sdiff_sdiff_left', ts_inter_ta_rw, tsa_rw, ts_union_sa_rw]
        rw [Finset.union_comm]
        apply Finset.sdiff_union_sdiff_cancel
        assumption
        rw [Finset.singleton_subset_iff]
        assumption
      rw [sa_ta_rw, sa_ts_rw, Finset.inter_self, Finset.union_comm]
      constructor; rfl
      rw [ne_eq, Finset.union_eq_empty, not_and_or]
      left; apply Finset.singleton_ne_empty

      rw [face_dim] at dim_t_n
      rw [face_dim, Finset.card_union_of_disjoint, Finset.card_sdiff, Finset.card_singleton,
        Finset.card_singleton, ← dim_t_n]
      simp only [Nat.cast_add, Nat.cast_one, add_tsub_cancel_right]
      have t_nontriv : t.card > 0 :=
      by
        apply Finset.Nonempty.card_pos
        apply Finset.Nonempty.mono s_ss_t
        rw [Finset.nonempty_iff_ne_empty]
        apply face_nonempty X s s_in_X
      apply Nat.cast_pred t_nontriv
      rw [Finset.singleton_subset_iff]
      assumption
      rw [Finset.disjoint_iff_ne]
      intro b b_in_ta c c_eq_x
      rw [Finset.mem_sdiff, Finset.mem_singleton] at b_in_ta
      rw [Finset.mem_singleton] at c_eq_x
      subst c_eq_x
      revert x_nin_X
      contrapose
      simp only [Classical.not_not]
      intro b_eq_c
      subst b_eq_c
      rw [vertex_iff_in_simplex]
      use t; constructor; assumption
      choose b_in_t b_ne_a using b_in_ta
      assumption
    · use t; constructor
      rw [Set.mem_toFinset, stellarSubdivision]
      simp only [AbstractSimplicialComplex.instHasUnion, simplicialUnion, Set.mem_union]
      left
      simp only [starComplement, Set.mem_sep_iff]
      constructor <;> assumption
      assumption

    apply Finset.le_max'
    rw [Finset.mem_union]
    right; assumption
  · rw [Finset.max'_le_iff]
    intro n n_X_dim
    rw [Finset.mem_union, Finset.mem_image] at n_X_dim
    cases' n_X_dim with n_X_dim n_neg_one

    choose t t_in_subdiv dim_t_n using n_X_dim
    rw [Set.mem_toFinset] at t_in_subdiv
    apply Finset.le_max'
    rw [Finset.mem_union, Finset.mem_image]
    left
    simp only [AbstractSimplicialComplex.instHasUnion, stellarSubdivision, simplicialUnion, Set.mem_union] at t_in_subdiv
    cases' t_in_subdiv with t_in_star_comp t_in_join

    simp only [starComplement, Set.mem_sep_iff] at t_in_star_comp
    choose t_in_X s_nss_t using t_in_star_comp
    use t; constructor
    rw [Set.mem_toFinset]
    assumption
    assumption

    simp only [join_proj_mem] at t_in_join
    choose t' t'_in_join t₁ t₁_in_link t_decomp t_ne using t_in_join
    rw [Set.mem_union] at t₁_in_link

    cases' t'_in_join with t'_in_join t'_empty

    simp only [join_proj_mem] at t'_in_join
    choose t₃ t₃_in_barycenter t₂ t₂_in_bd t'_decomp t'_ne using t'_in_join
    subst t'_decomp
    simp only [simplex, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at t₃_in_barycenter
    cases' t₃_in_barycenter with t₃_eq_x t₃_empty
    · have s_ne : Nonempty {x // x ∈ s} :=
      by
        rw [Finset.nonempty_coe_sort, Finset.nonempty_iff_ne_empty]
        apply face_nonempty X s s_in_X
      have t₂_sss_s : t₂ ⊂ s :=
      by
        rw [Set.mem_union] at t₂_in_bd
        cases' t₂_in_bd with t₂_in_bd t₂_empty
        rw [simplexBoundary_mem_iff_subset s t₂] at t₂_in_bd
        choose t₂_sss_s t₂_ne using t₂_in_bd
        assumption

        rw [Set.mem_singleton_iff] at t₂_empty
        rw [t₂_empty, Finset.empty_ssubset, ← Finset.nonempty_coe_sort]
        assumption

      rw [Finset.ssubset_iff] at t₂_sss_s
      choose a a_nin_t₂ at₂_ss_s using t₂_sss_s
      use t₁ ∪ insert a t₂; constructor
      rw [Set.mem_toFinset]
      apply @X.down_closed (s ∪ t₁)
      cases' t₁_in_link with t₁_in_link t₁_empty

      simp only [link, Set.mem_sep_iff] at t₁_in_link
      choose t₁_in_X st₁_in_X st₁_disj using t₁_in_link
      assumption

      rw [Set.mem_singleton_iff] at t₁_empty
      rw [t₁_empty, Finset.union_empty]
      assumption

      rw [Finset.union_comm]
      apply Finset.union_subset_union_left
      assumption

      rw [ne_eq, Finset.union_eq_empty, not_and_or]
      right; apply Finset.insert_ne_empty

      rw [Set.mem_diff, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at t₃_eq_x
      choose t₃_eq_x t₃_ne using t₃_eq_x
      cases' t₃_eq_x with contra t₃_eq_x
      contradiction

      rw [← dim_t_n, t_decomp, t₃_eq_x]
      simp only [face_dim, Finset.union_insert, Finset.union_assoc, sub_left_inj, Nat.cast_inj]
      rw [Finset.card_insert_of_notMem, @Finset.card_union_of_disjoint _ {x},
        Finset.card_singleton, Nat.add_comm, Finset.union_comm]
      rw [Finset.disjoint_singleton_left]
      by_contra x_in_t
      have contra : x ∈ X.vertices :=
      by
        rw [vertex_iff_in_simplex]
        use s ∪ t₁; constructor
        cases' t₁_in_link with t₁_in_link t₁_empty

        simp only [link, Set.mem_sep_iff] at t₁_in_link
        choose t₁_in_X st₁_in_X st₁_disj using t₁_in_link
        assumption

        rw [Set.mem_singleton_iff] at t₁_empty
        rw [t₁_empty, Finset.union_empty]
        assumption

        apply @Finset.mem_of_subset _ (t₂ ∪ t₁)
        apply Finset.union_subset_union_left
        apply @Finset.Subset.trans _ _ (insert a t₂)
        apply Finset.subset_insert
        assumption
        assumption
      contradiction
      rw [Finset.mem_union, not_or]
      constructor
      cases' t₁_in_link with t₁_in_link t₁_empty

      simp only [link, Set.mem_sep_iff] at t₁_in_link
      choose t₁_in_X st₁_in_X st₁_disj using t₁_in_link
      simp only [Finset.eq_empty_iff_forall_notMem, Finset.mem_inter, not_and] at st₁_disj
      have a_in_s : a ∈ s :=
      by
        apply Finset.mem_of_subset at₂_ss_s
        apply Finset.mem_insert_self
      specialize st₁_disj a a_in_s
      assumption

      rw [Set.mem_singleton_iff] at t₁_empty
      rw [t₁_empty]
      apply Finset.notMem_empty

      assumption
    · use t₁ ∪ t₂; constructor
      rw [Set.mem_toFinset]
      apply @X.down_closed (s ∪ t₁)
      simp only [link, Set.mem_sep_iff] at t₁_in_link
      cases' t₁_in_link with t₁_in_link t₁_empty

      choose t₁_in_link st₁_in_link st₁_disj using t₁_in_link
      assumption
      rw [Finset.union_comm]

      rw [Set.mem_singleton_iff] at t₁_empty
      rw [t₁_empty, Finset.empty_union]
      assumption

      rw [Finset.union_comm]
      apply Finset.union_subset_union_left
      rw [Set.mem_union] at t₂_in_bd
      cases' t₂_in_bd with t₂_in_bd t₂_empty

      have s_ne : Nonempty {x // x ∈ s} :=
      by
        rw [Finset.nonempty_coe_sort, Finset.nonempty_iff_ne_empty]
        apply face_nonempty X s s_in_X

      rw [simplexBoundary_mem_iff_subset s t₂, Finset.ssubset_iff_subset_ne] at t₂_in_bd
      choose t₂_ss_s t₂_ne using t₂_in_bd
      choose t₂_ss_s t₂_ne_s using t₂_ss_s
      assumption

      rw [Set.mem_singleton_iff] at t₂_empty
      subst t₂_empty
      apply Finset.empty_subset

      rw [ne_eq, Finset.union_eq_empty, not_and_or]
      right; all_goals {
        rw [Set.mem_singleton_iff] at t₃_empty
        subst t₃_empty
        rw [Finset.empty_union] at *
        try { rw [Finset.union_comm] at t_decomp; simp only [← dim_t_n, t_decomp] }
        try assumption
      }
    rw [Set.mem_singleton_iff] at t'_empty
    subst t'_empty
    rw [Finset.empty_union] at t_decomp
    subst t_decomp

    cases' t₁_in_link with t_in_link t_empty
    use t; constructor
    rw [Set.mem_toFinset]
    apply @X.down_closed (s ∪ t)
    simp only [link, Set.mem_setOf] at t_in_link
    choose t_in_X st_in_X st_empty using t_in_link
    assumption
    apply Finset.subset_union_right
    assumption
    assumption

    rw [Set.mem_singleton_iff] at t_empty
    contradiction

    apply Finset.le_max'
    rw [Finset.mem_union]
    right; assumption

theorem stellar_subdiv_of_singleton_vertices
    (X : AbstractSimplicialComplex E)
    (x y : E)
    (y_in_X : {y} ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
  : σ(X, {y}, x; 𝕜, y_in_X, x_nin_X).vertices = X.vertices \ {y} ∪ {x} :=
by
  simp only [Set.ext_iff, stellarSubdivision, AbstractSimplicialComplex.instHasUnion, simplicialUnion, join_proj_mem, vertex_iff_in_simplex,
    Set.mem_union, Set.mem_diff, Set.mem_singleton_iff]
  intro a
  constructor
  · intro a_in_subdiv
    choose s s_in_subdiv a_in_s using a_in_subdiv
    cases' s_in_subdiv with s_in_star_comp s_in_join
    simp only [starComplement, Set.mem_sep_iff, Finset.singleton_subset_iff] at s_in_star_comp
    choose s_in_X y_nin_s using s_in_star_comp
    left; constructor

    use s
    revert y_nin_s
    contrapose
    simp only [not_not]
    intro a_eq_y
    subst a_eq_y
    assumption

    choose s' s'_in_join s₁ s₁_in_link s_decomp s_ne using s_in_join
    cases' s'_in_join with s'_in_join s'_empty

    choose s₃ s₃_in_barycenter s₂ s₂_in_bd s'_decomp s'_ne using s'_in_join
    subst s'_decomp
    have s₂_empty : s₂ = ∅ :=
    by
      simp only [simplexBoundary, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff,
        Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at s₂_in_bd
      cases' s₂_in_bd with s₂_in_bd s₂_empty
      choose s₂_ss_y s₂_ne_y using s₂_in_bd
      cases' s₂_ss_y with s₂_empty contra
      assumption
      rw [Set.mem_insert_iff, not_or, Set.mem_singleton_iff] at s₂_ne_y
      choose s₂_ne_y s₂_ne using s₂_ne_y
      contradiction
      assumption
    subst s₂_empty

    cases' s₃_in_barycenter with s₃_in_barycenter s₃_empty
    rotate_left
    subst s₃_empty
    rw [Finset.empty_union] at s'_ne
    contradiction

    cases' s₁_in_link with s₁_in_link s₁_empty
    rotate_left
    subst s'_empty s₁_empty
    rw [Finset.empty_union] at s_decomp
    contradiction

    cases' s₂_in_bd with contra taut

    have bd_contra : ∅ ∉ (∂{y}).faces := by apply (∂{y}).empty_notMem
    contradiction

    rw [Finset.union_empty] at s_decomp s'_ne
    by_cases a_eq_x : a = x
    right; assumption
    have a_nin_s₃ : a ∉ s₃ :=
    by
      simp only [simplex, Set.mem_diff, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at s₃_in_barycenter
      choose s₃_in_barycenter s₃_ne using s₃_in_barycenter
      cases' s₃_in_barycenter with contra s₃_eq_x
      contradiction
      rw [s₃_eq_x, Finset.mem_singleton]
      assumption
    have a_in_s₁ : a ∈ s₁ :=
    by
      rw [s_decomp, Finset.mem_union] at a_in_s
      cases' a_in_s with contra a_in_s₁
      contradiction
      assumption

    simp only [link, Set.mem_sep_iff] at s₁_in_link
    cases' s₁_in_link with s₁_in_link s₁_empty
    rotate_left
    have contra : s₁ ≠ ∅ :=
    by
      apply Finset.ne_empty_of_mem a_in_s₁
    contradiction

    subst s'_empty s_decomp
    rw [Finset.empty_union] at s_ne a_in_s
    choose s₁_in_X ys₁_in_X ys₁_disj using s₁_in_link
    left; constructor; use s₁

    rw [← Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_singleton_left] at ys₁_disj
    revert ys₁_disj
    contrapose
    simp only [not_not]
    intro a_eq_y
    subst a_eq_y
    assumption

    choose s₁_in_X ys₁_in_X ys₁_disj using s₁_in_link
    left; constructor; use s₁
    rw [← Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_singleton_left] at ys₁_disj
    revert ys₁_disj
    contrapose
    simp only [not_not]
    intro a_eq_y
    subst a_eq_y
    assumption
  · intro a_in_union
    cases' a_in_union with a_in_X a_eq_x
    choose a_in_s a_ne_y using a_in_X
    choose s s_in_X a_in_s using a_in_s
    use s \ {y}; constructor; left
    simp only [starComplement, Set.mem_sep_iff]
    constructor
    apply X.down_closed s_in_X
    apply Finset.sdiff_subset

    revert a_in_s
    contrapose
    rw [not_not]
    intro sy_empty
    rw [Finset.sdiff_eq_empty_iff_subset, Finset.subset_singleton_iff] at sy_empty
    cases' sy_empty with s_empty s_eq_y
    rw [s_empty]
    apply Finset.notMem_empty
    rw [s_eq_y, Finset.mem_singleton]
    assumption

    rw [Finset.singleton_subset_iff, Finset.mem_sdiff, not_and, Finset.mem_singleton,
      Classical.not_not]
    intro y_in_s
    rfl

    rw [Finset.mem_sdiff, Finset.mem_singleton]
    constructor <;> assumption
    use {x}; constructor; right
    use {x}; constructor

    left
    use {x}; constructor; left
    simp only [simplex, Set.mem_diff, Finset.mem_coe]
    constructor
    apply Finset.mem_powerset_self
    rw [Set.mem_singleton_iff]
    apply Finset.singleton_ne_empty

    use ∅; constructor
    right; rfl
    constructor
    rw [Finset.union_empty]
    apply Finset.singleton_ne_empty

    use ∅; constructor
    right; rfl
    constructor
    rw [Finset.union_empty]
    apply Finset.singleton_ne_empty

    rw [a_eq_x]
    apply Finset.mem_singleton_self

theorem stellar_subdiv_subset_vertices
    (X : AbstractSimplicialComplex E)
    (s : Finset E) [s_ne : Nonempty s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
  : σ(X, s, x; 𝕜, s_in_X, x_nin_X).vertices ⊆ X.vertices ∪ {x} :=
by
  simp only [vertices_setOf, Set.subset_def, stellarSubdivision, AbstractSimplicialComplex.instHasUnion, simplicialUnion,
    Set.mem_union, Set.mem_setOf, join_proj_mem]
  intro a a_in_subdiv
  choose t t_in_subdiv a_in_t using a_in_subdiv
  cases' t_in_subdiv with t_in_star_comp t_in_join
  left
  use t; constructor
  apply simplex_if_in_subcomplex (X\St(X, s))
  assumption

  apply starComplement_subcomplex
  assumption

  choose t' t'_in_join t₁ t₁_in_link t_decomp t_ne using t_in_join
  cases' t'_in_join with t'_in_join t'_empty

  choose t₃ t₃_in_barycenter t₂ t₂_in_bd t'_decomp t'_ne using t'_in_join
  cases' t₂_in_bd with t₂_in_bd t₂_empty <;>
  cases' t₃_in_barycenter with t₃_in_barycenter t₃_empty
  rotate_left 3
  rw [Set.mem_singleton_iff] at t₂_empty t₃_empty
  subst t₂_empty t₃_empty
  rw [Finset.union_empty] at t'_decomp
  contradiction

  left; use t₁; constructor
  cases' t₁_in_link with t₁_in_link t₁_empty
  apply @X.down_closed (s ∪ t₁)
  choose t₁_in_X st₁_in_X st₁_disj using t₁_in_link
  assumption
  apply Finset.subset_union_right
  apply face_nonempty _ _ t₁_in_link

  rw [Set.mem_singleton_iff] at t'_empty t₁_empty
  rw [t'_empty, t₁_empty, Finset.union_empty] at t_decomp
  contradiction

  rw [Set.mem_singleton_iff] at t'_empty
  rw [t'_empty, Finset.empty_union] at t_decomp
  rw [← t_decomp]
  assumption

  subst t'_decomp
  subst t_decomp
  simp only [Finset.mem_union] at a_in_t
  cases' a_in_t with a_in_t a_in_t₁
  cases' a_in_t with a_in_t₃ a_in_t₂
  right
  have a_in_x : a ∈ (simplex {x}).vertices :=
  by
    rw [vertex_iff_in_simplex]
    use t₃
  cases' t₃_in_barycenter with t₃_in_barycenter t₃_empty
  rw [simplex_vertices, Finset.mem_coe, Finset.mem_singleton] at a_in_x
  simp only [Set.mem_singleton_iff]
  assumption

  left
  use t₂; constructor
  apply simplex_if_in_subcomplex (∂s)
  assumption
  apply simplexBoundary_subcomplex
  assumption
  assumption

  left;
  use t₁; constructor
  apply simplex_if_in_subcomplex Lk(X, s)
  cases' t₁_in_link with t₁_in_link t₁_empty
  assumption

  rw [Set.mem_singleton_iff] at t₁_empty
  rw [t₁_empty] at a_in_t₁
  contradiction

  apply link_subcomplex
  assumption

  rw [Set.mem_singleton_iff] at t₃_empty
  subst t₃_empty
  rw [Finset.empty_union] at t'_decomp
  subst t'_decomp
  simp only [simplexBoundary, Set.mem_diff, Finset.mem_coe, Finset.mem_powerset,
    Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at t₂_in_bd
  choose t₂_ss_s t₂_ne_s t₂_ne using t₂_in_bd
  left; use t' ∪ t₁; constructor
  apply @X.down_closed (s ∪ t₁)
  simp only [link, Set.mem_setOf, Set.mem_singleton_iff] at t₁_in_link
  cases' t₁_in_link with t₁_in_link t₁_empty

  choose t₁_in_X st₁_in_X st₁_disj using t₁_in_link
  assumption

  rw [t₁_empty, Finset.union_empty]
  assumption

  apply Finset.union_subset_union_left
  assumption

  rw [t_decomp] at t_ne
  assumption

  rw [t_decomp] at a_in_t
  assumption

  rw [Set.mem_singleton_iff] at t₂_empty
  subst t₂_empty
  rw [Finset.union_empty] at t'_decomp
  subst t'_decomp
  simp only [simplex, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe,
    Finset.mem_powerset, Finset.subset_singleton_iff] at t₃_in_barycenter
  choose t₃_in_barycenter t₃_empty using t₃_in_barycenter
  cases' t₃_in_barycenter with t₃_empty t₃_eq_x
  contradiction

  subst t₃_eq_x
  simp only [link, Set.mem_setOf, Set.mem_singleton_iff] at t₁_in_link
  cases' t₁_in_link with t₁_in_link t₁_empty

  choose t₁_in_X st₁_in_X st₁_disj using t₁_in_link
  by_cases a_eq_x : a = x
  right; rw [a_eq_x]; apply Set.mem_singleton
  have a_in_t₁ : a ∈ t₁ :=
  by
    rw [t_decomp, Finset.mem_union, Finset.mem_singleton] at a_in_t
    cases' a_in_t with a_eq_x a_in_t₁
    contradiction
    assumption
  left; use t₁

  rw [t₁_empty, Finset.union_empty] at t_decomp
  rw [t_decomp, Finset.mem_singleton] at a_in_t
  right; rw [Set.mem_singleton_iff]; assumption

theorem stellar_subdiv_vertices
    (X : AbstractSimplicialComplex E)
    (s : Finset E) [s_ne : Nonempty s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
  : s.card > 1 → σ(X, s, x; 𝕜, s_in_X, x_nin_X).vertices = X.vertices ∪ {x} :=
by
  intro s_nontriv
  rw [Set.Subset.antisymm_iff]
  constructor

  apply stellar_subdiv_subset_vertices

  rw [Set.subset_def]
  intro a a_in_union
  rw [Set.mem_union, Set.mem_singleton_iff, vertex_iff_in_simplex] at a_in_union
  simp only [vertices_setOf, Set.subset_def, stellarSubdivision, AbstractSimplicialComplex.instHasUnion, simplicialUnion,
    Set.mem_union, Set.mem_setOf, join_proj_mem]
  cases' a_in_union with a_in_X a_eq_x

  choose t t_in_X a_in_t using a_in_X
  use {a}
  constructor

  left
  simp only [starComplement, Set.mem_sep_iff]
  constructor

  apply X.down_closed t_in_X
  rw [Finset.singleton_subset_iff]
  assumption

  apply Finset.singleton_ne_empty

  have a_le_s : ¬s.card ≤ 1 := not_le.mpr s_nontriv
  rw [← Finset.card_singleton a] at a_le_s
  revert a_le_s
  contrapose
  simp only [Classical.not_not]
  apply Finset.card_le_card
  apply Finset.mem_singleton_self

  use {x}
  constructor

  right
  use {x}
  constructor

  left
  use {x}
  constructor

  left
  simp only [simplex, Finset.mem_coe, Set.mem_diff]
  constructor
  apply Finset.mem_powerset_self
  apply Finset.singleton_ne_empty

  use ∅
  constructor
  right
  trivial

  rw [Finset.union_empty]
  constructor
  trivial
  apply Finset.singleton_ne_empty

  use ∅
  constructor
  right
  trivial

  rw [Finset.union_empty]
  constructor
  trivial
  apply Finset.singleton_ne_empty

  rw [a_eq_x]
  apply Finset.mem_singleton_self


def barycenterStar
    (X : AbstractSimplicialComplex E)
    (s : Finset E) [s_ne : Nonempty s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
  : Set (Finset E) :=
  {t ∈ σ(X, s, x; 𝕜, s_in_X, x_nin_X).faces | x ∈ t}

instance barycenterStar.fintype
    (X : AbstractSimplicialComplex E)
    (s : Finset E) [s_ne : Nonempty s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    [Fintype σ(X, s, x; 𝕜, s_in_X, x_nin_X).faces]
  : Fintype (@barycenterStar _ 𝕜 _ _ _ _ _ X s _ x s_in_X x_nin_X) :=
by
  simp only [barycenterStar]
  apply Set.fintypeSep

/- ././././Mathport/Syntax/Translate/Expr.lean:373:4: unsupported set replacement {(«expr ∪ »(s, «expr \ »(t, {x}))) | t «expr ∈ » barycenter_star[barycenter_star] X s x s_in_X x_nin_X} -/
def barycenterWeld
    (X : AbstractSimplicialComplex E)
    (s : Finset E) [s_ne : Nonempty s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
  : Set (Finset E) :=
  {(s ∪ (t \ {x})) | t ∈ @barycenterStar _ 𝕜 _ _ _ _ _ X s _ x s_in_X x_nin_X}

theorem barycenterWeld_as_union
    (X : AbstractSimplicialComplex E)
    (s : Finset E) [s_ne : Nonempty s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
  : @barycenterWeld _ 𝕜 _ _ _ _ _ X s _ x s_in_X x_nin_X =
      ⋃ t ∈ @barycenterStar _ 𝕜 _ _ _ _ _ X s _ x s_in_X x_nin_X, {s ∪ t \ {x}} :=
by
  simp only [barycenterWeld, Set.ext_iff, Set.mem_iUnion, Set.mem_setOf, Set.mem_singleton_iff]
  intro t
  constructor

  intro t_in_weld
  choose u u_in_star t_su using t_in_weld
  use u
  constructor
  symm; assumption
  assumption

  intro t_in_union
  choose u u_in_star t_su using t_in_union
  use u
  constructor
  assumption
  symm; assumption

instance barycenterWeld.fintype
    (X : AbstractSimplicialComplex E)
    (s : Finset E) [s_ne : Nonempty s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    [Fintype σ(X, s, x; 𝕜, s_in_X, x_nin_X).faces]
  : Fintype (@barycenterWeld _ 𝕜 _ _ _ _ _ X s _ x s_in_X x_nin_X) :=
by
  rw [barycenterWeld_as_union]
  apply Set.fintypeBiUnion
  intro t t_in_star
  apply Unique.fintype

theorem stellar_weld_simplices
    (X : AbstractSimplicialComplex E)
    (s : Finset E) [s_ne : Nonempty s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
  : X.faces =
      {t ∈ σ(X, s, x; 𝕜, s_in_X, x_nin_X).faces | x ∉ t} ∪
        @barycenterWeld _ 𝕜 _ _ _ _ _ X s _ x s_in_X x_nin_X :=
by
  simp only [barycenterWeld, Set.ext_iff, Set.mem_union, Set.mem_sep_iff, Set.mem_setOf]
  intro t
  constructor
  · intro t_in_X
    by_cases s_ss_t : s ⊆ t

    right
    use t \ s ∪ {x}
    constructor

    simp only [barycenterStar, Set.mem_sep_iff, stellarSubdivision, AbstractSimplicialComplex.instHasUnion, simplicialUnion, Set.mem_union,
      join_proj_mem]
    constructor

    right
    use {x} ∪ ∅
    constructor

    left
    use {x}
    constructor

    left
    simp only [simplex, Finset.mem_coe, Set.mem_diff]
    constructor
    apply Finset.mem_powerset_self
    apply Finset.singleton_ne_empty

    use ∅
    constructor

    right
    trivial

    rw [Finset.union_empty]
    constructor
    trivial
    apply Finset.singleton_ne_empty

    use t \ s
    constructor

    by_cases ts_empty : t \ s = ∅

    right
    assumption

    left
    simp only [link, Set.mem_sep_iff]
    constructor

    apply X.down_closed t_in_X
    apply Finset.sdiff_subset
    assumption

    constructor
    rw [Finset.union_sdiff_of_subset]
    assumption
    assumption

    apply Finset.inter_sdiff_self
    constructor
    rw [Finset.union_empty, Finset.union_comm]
    by_contra ts_x_empty
    rw [Finset.union_eq_empty] at ts_x_empty
    choose ts_empty x_empty using ts_x_empty
    apply Finset.singleton_ne_empty at x_empty
    assumption

    rw [Finset.mem_union]
    right
    apply Finset.mem_singleton_self

    rw [Finset.union_sdiff_distrib, Finset.sdiff_self, Finset.union_empty, Finset.sdiff_sdiff_left',
      Finset.union_inter_distrib_left]
    rw [Finset.union_sdiff_of_subset, Finset.sdiff_eq_self_of_disjoint]

    have st_rw : s ∪ t = t := by
      rw [Finset.union_eq_right]
      assumption
    rw [st_rw, Finset.inter_self]

    rw [Finset.disjoint_singleton_right]
    revert x_nin_X
    contrapose
    simp only [Classical.not_not]
    intro x_in_t
    rw [vertex_iff_in_simplex]
    use t

    assumption

    left
    constructor

    simp only [stellarSubdivision, simplicialUnion, Set.mem_union]
    left
    simp only [starComplement, Set.mem_sep_iff]
    constructor <;> assumption

    revert x_nin_X
    contrapose
    simp only [Classical.not_not]
    intro x_in_t
    rw [vertex_iff_in_simplex]
    use t
  · intro t_in_union
    cases' t_in_union with t_in_subdiv t_join_s
    choose t_in_subdiv x_nin_t using t_in_subdiv
    simp only [vertices_setOf, Set.subset_def, stellarSubdivision, AbstractSimplicialComplex.instHasUnion, simplicialUnion,
      Set.mem_union, Set.mem_setOf, join_proj_mem] at t_in_subdiv
    cases' t_in_subdiv with t_in_star_comp t_in_join
    simp only [starComplement, Set.mem_sep_iff] at t_in_star_comp
    choose t_in_X s_nss_t using t_in_star_comp
    assumption
    simp only [join_proj_mem] at t_in_join
    choose t' t'_in_join t₁ t₁_in_link t_decomp using t_in_join
    cases' t'_in_join with t'_in_join t'_empty

    choose t₃ t₃_in_barycenter t₂ t₂_in_bd t'_decomp t'_nonempty using t'_in_join
    subst t'_decomp
    have t₃_empty : t₃ = ∅ :=
      by
      simp only [simplex, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at t₃_in_barycenter
      cases' t₃_in_barycenter with t₃_eq_x t₃_empty
      have contra : x ∈ t := by
        rw [Set.mem_diff] at t₃_eq_x
        choose t₃_eq_x t₃_nonempty using t₃_eq_x
        simp only [Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at t₃_eq_x
        cases' t₃_eq_x with t₃_empty t₃_eq_x
        contradiction
        simp only [t_decomp, Finset.mem_union, t₃_eq_x]
        left; left
        apply Finset.mem_singleton_self
      contradiction
      assumption
    subst t₃_empty
    rw [Finset.empty_union] at t_decomp
    simp only [link, Set.mem_sep_iff] at t₁_in_link
    cases' t₁_in_link with t₁_in_link t₁_empty

    choose t₁_in_X st₁_in_X st₁_disj using t₁_in_link
    rw [simplexBoundary_mem_iff_subset, Finset.ssubset_iff_subset_ne] at t₂_in_bd
    cases' t₂_in_bd with t₂_in_bd t₂_empty

    choose t₂_in_bd t₂_nonempty using t₂_in_bd
    choose t₂_ss_s t₂_ne_s using t₂_in_bd
    choose t_decomp t_nonempty using t_decomp
    rw [t_decomp]
    apply X.down_closed st₁_in_X
    apply Finset.union_subset_union_left
    assumption
    by_contra t₂t₁_empty
    rw [Finset.union_eq_empty] at t₂t₁_empty
    choose t₂_empty t₁_empty using t₂t₁_empty
    contradiction

    simp only [Set.mem_singleton_iff] at t₂_empty
    simp only [Finset.empty_union] at t'_nonempty
    contradiction

    subst t₁_empty
    rw [Finset.empty_union] at t'_nonempty
    rw [Finset.union_empty] at t_decomp
    choose t_eq_t₂ t_nonempty using t_decomp
    subst t_eq_t₂
    cases' t₂_in_bd with t_in_bd t_empty

    simp only [simplexBoundary, Set.mem_diff, Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
      Finset.coe_subset, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at t_in_bd
    choose t_ss_s t_ne_s t_nonempty using t_in_bd
    apply X.down_closed s_in_X
    assumption
    assumption

    subst t_empty
    contradiction

    simp only [Set.mem_singleton_iff] at t'_empty
    subst t'_empty
    choose t_eq_t₁ t_nonempty using t_decomp
    rw [Finset.empty_union] at t_eq_t₁
    subst t_eq_t₁
    cases' t₁_in_link with t_in_link t_empty

    apply link_subcomplex_simplices X s t
    assumption

    contradiction

    choose u u_in_star su_eq_t using t_join_s
    simp only [barycenterStar, Set.mem_sep_iff] at u_in_star
    choose u_in_subdiv x_in_u using u_in_star
    simp only [stellarSubdivision, simplicialUnion, Set.mem_union] at u_in_subdiv
    cases' u_in_subdiv with u_in_star_comp u_in_join
    simp only [starComplement, Set.mem_sep_iff] at u_in_star_comp
    choose u_in_X s_nss_u using u_in_star_comp
    have contra : x ∈ X.vertices := by
      rw [vertex_iff_in_simplex]
      use u
    contradiction
    simp only [join_proj_mem] at u_in_join
    choose u' u'_in_join u₁ u₁_in_link u_decomp using u_in_join
    cases' u'_in_join with u'_in_join u'_empty

    simp only [join_proj_mem] at u'_in_join
    choose u₃ u₃_in_barycenter u₂ u₂_in_bd u'_decomp using u'_in_join
    choose u'_decomp u'_nonempty using u'_decomp
    subst u'_decomp
    simp only [link, Set.mem_sep_iff] at u₁_in_link
    cases' u₁_in_link with u₁_in_link u₁_empty

    choose u₁_in_X su₁_in_X su₁_disj using u₁_in_link
    cases' u₂_in_bd with u₂_in_bd u₂_empty

    rw [simplexBoundary_mem_iff_subset, Finset.ssubset_iff_subset_ne] at u₂_in_bd
    choose u₂_ss_s u₂_ne_s using u₂_in_bd
    have xu₁_rw : u₁ \ {x} = u₁ :=
      by
      rw [Finset.sdiff_eq_self_iff_disjoint, Finset.disjoint_singleton_right]
      by_contra
      have contra : x ∈ X.vertices := by
        rw [vertex_iff_in_simplex]
        use u₁
      contradiction
    have xu₂_rw : u₂ \ {x} = u₂ :=
      by
      rw [Finset.sdiff_eq_self_iff_disjoint, Finset.disjoint_singleton_right]
      by_contra
      have contra : x ∈ X.vertices := by
        rw [vertex_iff_in_simplex]
        use u₂; constructor
        apply X.down_closed s_in_X
        simp only [u₂_ss_s]
        assumption
        assumption
      contradiction
    choose u_decomp u_nonempty using u_decomp
    rw [← su_eq_t, u_decomp]
    simp only [Finset.union_sdiff_distrib]
    rw [xu₁_rw, xu₂_rw]
    have su₂_rw : s ∪ u₂ = s := by
      rw [Finset.union_eq_left]
      simp only [u₂_ss_s]
    simp only [simplex, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at u₃_in_barycenter
    cases' u₃_in_barycenter with u₃_in_barycenter u₃_empty

    choose u₃_eq_x u₃_nonempty using u₃_in_barycenter
    simp only [Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at u₃_eq_x
    cases' u₃_eq_x with u₃_empty u₃_eq_x

    contradiction

    subst u₃_eq_x
    rw [Finset.sdiff_self, Finset.empty_union, ← Finset.union_assoc, su₂_rw]
    assumption

    subst u₃_empty
    rw [Finset.empty_sdiff, Finset.empty_union, ← Finset.union_assoc, su₂_rw]
    assumption

    subst u₂_empty
    rw [Finset.union_empty] at *
    cases' u₃_in_barycenter with u₃_eq_x u₃_empty

    simp only [simplex, Set.mem_diff, Finset.mem_coe] at u₃_eq_x
    choose u₃_eq_x u₃_nonempty using u₃_eq_x
    simp only [Finset.mem_powerset, Finset.subset_singleton_iff] at u₃_eq_x
    cases' u₃_eq_x with u₃_empty u₃_eq_x

    contradiction

    subst u₃
    subst su_eq_t
    choose u_decomp u_nonempty using u_decomp
    subst u_decomp
    rw [Finset.union_sdiff_distrib, Finset.sdiff_self, Finset.empty_union]
    have xu₁_rw : u₁ \ {x} = u₁ :=
      by
      rw [Finset.sdiff_eq_self_iff_disjoint, Finset.disjoint_singleton_right]
      by_contra
      have contra : x ∈ X.vertices := by
        rw [vertex_iff_in_simplex]
        use u₁
      contradiction
    rw [xu₁_rw]
    assumption

    contradiction

    subst u₁_empty
    rw [Finset.union_empty] at u_decomp
    subst su_eq_t
    choose u_decomp u_nonempty using u_decomp
    subst u_decomp
    simp only [simplex, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at u₃_in_barycenter
    cases' u₃_in_barycenter with u₃_in_barycenter u₃_empty

    choose u₃_eq_x u₃_nonempty using u₃_in_barycenter
    simp only [Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at u₃_eq_x
    cases' u₃_eq_x with u₃_empty u₃_eq_x

    contradiction

    subst u₃_eq_x
    cases' u₂_in_bd with u₂_in_bd u₂_empty

    rw [simplexBoundary_mem_iff_subset, Finset.ssubset_iff_subset_ne] at u₂_in_bd
    choose u₂_ss_s u₂_nonempty using u₂_in_bd
    choose u₂_ss_s u₂_ne_s using u₂_ss_s
    rw [Finset.union_sdiff_distrib, Finset.sdiff_self, Finset.empty_union]
    have xu₂_rw : u₂ \ {x} = u₂ :=
      by
      rw [Finset.sdiff_eq_self_iff_disjoint, Finset.disjoint_singleton_right]
      by_contra
      have contra : x ∈ X.vertices := by
        rw [vertex_iff_in_simplex]
        use u₂; constructor
        apply X.down_closed s_in_X
        simp only [u₂_ss_s]
        assumption
        assumption
      contradiction
    rw [xu₂_rw]
    have su₂_rw : s ∪ u₂ = s := by
      rw [Finset.union_eq_left]
      simp only [u₂_ss_s]
    rw [su₂_rw]
    assumption

    subst u₂_empty
    rw [Finset.union_empty, Finset.sdiff_self, Finset.union_empty]
    assumption

    subst u₃_empty
    rw [Finset.empty_union] at *
    cases' u₂_in_bd with u₂_in_bd u₂_empty

    simp only [simplexBoundary, Set.mem_diff, Finset.mem_coe, Finset.mem_powerset] at u₂_in_bd
    choose u₂_ss_s u₂_ne_s_empty using u₂_in_bd
    have h : s ∪ u₂ \ {x} ⊆ s :=
      by
      have h₁ : u₂ \ {x} ⊆ u₂ :=
        by
        apply Finset.sdiff_subset
      have h₂ : s ∪ u₂ \ {x} ⊆ s ∪ u₂ :=
        by
        apply Finset.union_subset_union_right
        assumption
      trans s ∪ u₂
      assumption
      apply Finset.union_subset
      trivial
      assumption
    apply X.down_closed s_in_X
    assumption
    rw [ne_eq, Finset.union_eq_empty]
    intro s_empty_u₂_empty
    choose s_empty u₂_empty using s_empty_u₂_empty
    apply X.empty_notMem
    subst s_empty
    assumption

    subst u₂_empty
    contradiction

    subst u'_empty
    rw [Finset.empty_union] at u_decomp
    choose u_eq_u₁ u_nonempty using u_decomp
    subst u_eq_u₁

    cases' u₁_in_link with u_in_link u_empty
    simp only [link, Set.sep_and, Set.mem_inter_iff, Set.mem_setOf_eq] at u_in_link
    choose su_in_X u_in_X s_inter_u_empty using u_in_link
    choose u_in_X su_in_X using su_in_X
    subst su_eq_t
    have h : s ∪ u \ {x} ⊆ s ∪ u :=
      by
      apply Finset.union_subset_union_right
      apply Finset.sdiff_subset
    apply X.down_closed su_in_X
    assumption

    rw [ne_eq, Finset.union_eq_empty]
    intro s_empty_u_empty
    choose s_empty u_empty using s_empty_u_empty
    apply X.empty_notMem
    subst s_empty
    assumption

    contradiction

section SynthOrder
set_option synthInstance.checkSynthOrder false

instance stellarSubdivision.fintypeConverse
    (X : AbstractSimplicialComplex E)
    (s : Finset E) [s_ne : Nonempty s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    [Fintype σ(X, s, x; 𝕜, s_in_X, x_nin_X).faces]
  : Fintype X.faces :=
  by
  rw [@stellar_weld_simplices _ 𝕜 _ _ _ _ _ X s _ x s_in_X x_nin_X]
  apply Set.fintypeUnion

end SynthOrder

theorem barycenter_vertex_stellar_subdiv
    (X : AbstractSimplicialComplex E)
    (s : Finset E)
    [s_ne : Nonempty s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
  : x ∈ σ(X, s, x; 𝕜, s_in_X, x_nin_X).vertices :=
by
  rw [vertex_iff_in_simplex]
  simp only [vertices_setOf, Set.subset_def, stellarSubdivision, AbstractSimplicialComplex.instHasUnion, simplicialUnion,
      Set.mem_union, Set.mem_setOf, join_proj_mem, link]
  --simp only [stellarSubdivision, simplicialUnion, Set.mem_union, join_proj_mem]
  --right
  use {x}
  constructor

  right
  use {x}
  constructor

  left
  use {x}
  constructor

  simp only [simplex, Finset.mem_coe, Set.mem_diff, Finset.mem_powerset]
  left
  constructor
  trivial
  apply Finset.singleton_ne_empty

  use ∅
  constructor

  right
  trivial

  constructor
  trivial
  apply Finset.singleton_ne_empty

  use ∅
  constructor

  right
  trivial

  constructor
  trivial
  apply Finset.singleton_ne_empty

  apply Finset.mem_singleton_self

theorem stellar_subdiv_iso_simp
    (X : AbstractSimplicialComplex E)
    (Y : AbstractSimplicialComplex F)
    (s : Finset E) [s_ne : Nonempty s]
    (t : Finset F) [t_ne : Nonempty t]
    (x : E)
    (y : F)
    (s_in_X : s ∈ X.faces)
    (t_in_Y : t ∈ Y.faces)
    (x_nin_X : x ∉ X.vertices)
    (y_nin_Y : y ∉ Y.vertices)
    (f : SimplicialMap X Y)
    (f_iso : IsSimplicialIso f)
  : Finset.image f.map s = t →
      f.map x = y →
        IsSimplicialMap σ(X, s, x; 𝕜, s_in_X, x_nin_X) σ(Y, t, y; 𝕜, t_in_Y, y_nin_Y) f.map :=
by
  intro fs_t fx_y
  let f_iso' := f_iso
  unfold IsSimplicialIso at f_iso'
  choose g gf_inv using f_iso'
  have g_iso : IsSimplicialIso g := by apply iso_inv_is_iso f g f_iso gf_inv
  unfold IsInverseSimplicialIso at gf_inv
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply, id] at gf_inv
  choose gf_id fg_id using gf_inv
  have f_inj : Set.InjOn f.map s :=
    by
    apply @Set.LeftInvOn.injOn _ _ _ _ g.map
    simp only [Set.LeftInvOn]
    intro x x_in_s
    have x_in_vert : x ∈ X.vertices :=
      by
      rw [vertex_iff_in_simplex]
      use s; constructor; assumption
      rw [← Finset.mem_coe]
      assumption
    specialize gf_id x_in_vert
    assumption
  simp only [IsSimplicialMap]
  intro u u_in_subdiv_X
  simp only [stellarSubdivision, simplicialUnion, Set.mem_union] at u_in_subdiv_X ⊢
  cases' u_in_subdiv_X with u_in_star_comp u_in_join

  left
  simp only [starComplement, Set.mem_sep_iff] at u_in_star_comp ⊢
  choose u_in_X s_nss_u using u_in_star_comp
  constructor

  apply f.is_simplicial
  assumption

  simp only [← fs_t, Finset.image_subset_iff, Classical.not_forall, Finset.mem_image, not_exists]
  simp only [Finset.subset_iff, Classical.not_forall] at s_nss_u
  choose z z_in_s z_nin_u using s_nss_u
  use z
  use z_in_s
  intro w w_in_u
  rw [@Set.InjOn.eq_iff _ _ (X.vertices)] at w_in_u
  choose w_in_w w_eq_z using w_in_u
  subst w_eq_z
  contradiction

  apply iso_is_injective_vertices
  assumption

  rw [vertex_iff_in_simplex]
  use u
  constructor
  assumption
  choose w_in_u fw_eq_fz using w_in_u
  assumption

  rw [vertex_iff_in_simplex]
  use s

  right
  simp only [join_proj_mem, Set.mem_union] at u_in_join ⊢
  choose u' u'_in_join u₁ u₁_in_link u_decomp using u_in_join
  cases' u'_in_join with u'_in_join u'_empty

  choose u₃ u₃_in_barycenter u₂ u₂_in_bd u'_decomp using u'_in_join
  choose u'_decomp u'_nonempty using u'_decomp
  subst u'_decomp
  use Finset.image f.map (u₃ ∪ u₂)
  constructor

  left
  use Finset.image f.map u₃
  constructor

  simp only [simplex, Set.mem_diff, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at u₃_in_barycenter ⊢
  cases' u₃_in_barycenter with u₃_x u₃_empty

  left
  choose u₃_x u₃_nonempty using u₃_x
  cases' u₃_x with u₃_empty u₃_x

  contradiction

  rw [u₃_x, ← fx_y]
  constructor

  right
  apply Finset.image_singleton

  rw [Finset.image_singleton, Set.mem_singleton_iff, ← ne_eq]
  apply Finset.singleton_ne_empty

  right
  subst u₃_empty
  apply Finset.image_empty

  use Finset.image f.map u₂
  constructor

  simp only [simplexBoundary, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe,
    Finset.mem_powerset] at u₂_in_bd ⊢
  cases' u₂_in_bd with u₂_in_bd u₂_empty

  left
  choose u₂_ss_s u₂_ne_s using u₂_in_bd
  rw [Set.mem_insert_iff, not_or, ← ne_eq] at u₂_ne_s
  choose u₂_ne_s u₂_nonempty using u₂_ne_s
  simp only [← fs_t]
  constructor

  apply Finset.image_subset_image
  assumption

  rw [Set.mem_insert_iff, not_or, ← ne_eq]
  constructor

  revert u₂_ne_s
  contrapose
  simp only [Classical.not_not, Finset.ext_iff, Finset.mem_image]
  intro fu_eq_fs a
  specialize fu_eq_fs (f.map a)
  cases' fu_eq_fs with fu_ss_fs fs_ss_fu
  constructor

  intro a_in_u
  rw [Finset.subset_iff] at u₂_ss_s
  specialize u₂_ss_s a_in_u
  assumption

  intro a_in_s
  apply Set.InjOn.mem_of_mem_image f_inj u₂_ss_s
  rw [Finset.mem_coe]
  assumption

  have Hs : (∃ a_1 ∈ s, f.map a_1 = f.map a) :=
    by
    use a
  specialize fs_ss_fu Hs
  simp only [Set.mem_image]
  assumption

  rw [Set.notMem_singleton_iff, ne_eq, Finset.image_eq_empty]
  assumption

  subst u₂_empty
  rw [Finset.image_empty]
  right
  trivial

  constructor

  apply Finset.image_union

  rw [ne_eq, Finset.image_eq_empty]
  assumption

  use Finset.image f.map u₁
  constructor

  simp only [link, Set.mem_sep_iff] at u₁_in_link ⊢
  cases' u₁_in_link with u₁_in_link u₁_empty

  left
  choose u₁_in_X su₁_in_X su₁_disj using u₁_in_link
  constructor

  apply f.is_simplicial
  assumption

  constructor

  rw [← fs_t, ← Finset.image_union]
  apply f.is_simplicial
  assumption

  rw [← fs_t, ← Finset.image_inter_of_injOn, su₁_disj, Finset.image_eq_empty]
  rw [← Finset.coe_union]
  apply iso_is_injective_simplices f f_iso (s ∪ u₁)
  assumption

  right
  subst u₁_empty
  exact rfl

  choose u_decomp u_nonempty using u_decomp
  constructor

  rw [u_decomp, Finset.image_union]

  rw [ne_eq, Finset.image_eq_empty]
  assumption

  subst u'_empty
  use ∅
  constructor

  right
  trivial

  use Finset.image f.map u₁
  constructor

  left
  simp only [link, Set.mem_sep_iff] at u₁_in_link ⊢
  cases' u₁_in_link with u₁_in_link u₁_empty

  choose u₁_in_X su₁_in_X su₁_disj using u₁_in_link
  constructor

  apply f.is_simplicial
  assumption

  constructor

  rw [← fs_t, ← Finset.image_union]
  apply f.is_simplicial
  assumption

  rw [← fs_t, ← Finset.image_inter_of_injOn, su₁_disj, Finset.image_eq_empty]
  rw [← Finset.coe_union]
  apply iso_is_injective_simplices f f_iso (s ∪ u₁)
  assumption

  subst u₁_empty
  rw [Finset.empty_union] at u_decomp
  choose u_empty u_nonempty using u_decomp
  contradiction

  choose u_decomp u_nonempty using u_decomp
  constructor

  rw [Finset.empty_union] at u_decomp ⊢
  subst u_decomp
  trivial

  rw [ne_eq]
  intro fu_empty
  rw [Finset.image_eq_empty] at fu_empty
  contradiction

theorem stellar_subdiv_iso
    (X : AbstractSimplicialComplex E)
    (Y : AbstractSimplicialComplex F)
    (s : Finset E) [s_ne : Nonempty s]
    (t : Finset F) [t_ne : Nonempty t]
    (x : E)
    (y : F)
    (s_in_X : s ∈ X.faces)
    (t_in_Y : t ∈ Y.faces)
    (x_nin_X : x ∉ X.vertices)
    (y_nin_Y : y ∉ Y.vertices)
    (f : SimplicialMap X Y) (f_iso : IsSimplicialIso f)
    (g : SimplicialMap Y X) (gf_inv : IsInverseSimplicialIso f g)
  : Finset.image f.map s = t →
      f.map x = y →
        g.map y = x → σ(X, s, x; 𝕜, s_in_X, x_nin_X) ≅ σ(Y, t, y; 𝕜, t_in_Y, y_nin_Y) :=
by
  intro fs_t fx_y gy_x
  have g_iso : IsSimplicialIso g := by apply iso_inv_is_iso f g f_iso gf_inv
  unfold IsInverseSimplicialIso at gf_inv
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply, id] at gf_inv
  choose gf_id fg_id using gf_inv
  have gt_s : Finset.image g.map t = s :=
    by
    simp only [← fs_t, Finset.ext_iff, Finset.mem_image]
    intro a
    constructor
    intro a_in_img
    choose b b_in_t gb_a using a_in_img
    choose c c_in_s fc_b using b_in_t
    subst fc_b
    have c_in_X : c ∈ X.vertices := by
      rw [vertex_iff_in_simplex]
      use s
    specialize gf_id c_in_X
    rw [gf_id] at gb_a
    rw [gb_a] at c_in_s
    assumption
    intro a_in_s
    use f.map a; constructor
    use a
    have a_in_X : a ∈ X.vertices := by
      rw [vertex_iff_in_simplex]
      use s
    specialize gf_id a_in_X
    assumption
  let f_subdiv :=
    SimplicialMap.mk f.map
      (@stellar_subdiv_iso_simp _ _ 𝕜 _ _ _ _ _ _ _ X Y s _ t _ x y s_in_X t_in_Y x_nin_X y_nin_Y f f_iso fs_t fx_y)
  let g_subdiv :=
    SimplicialMap.mk g.map
      (@stellar_subdiv_iso_simp _ _ 𝕜 _ _ _ _ _ _ _ Y X t _ s _ y x t_in_Y s_in_X y_nin_Y x_nin_X g g_iso gt_s gy_x)
  unfold IsSimpliciallyIso
  use f_subdiv
  unfold IsSimplicialIso
  use g_subdiv
  unfold IsInverseSimplicialIso
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply, id]
  constructor
  · intro a a_in_X
    have a_in_union : a ∈ X.vertices ∪ {x} :=
      by
      apply @stellar_subdiv_subset_vertices _ 𝕜 _ _ _ _ _ X s
      apply a_in_X
    rw [Set.mem_union, Set.mem_singleton_iff] at a_in_union
    cases' a_in_union with a_in_X a_eq_x
    specialize gf_id a_in_X
    assumption
    subst a_eq_x
    rw [fx_y, gy_x]
  · intro a a_in_Y
    have a_in_union : a ∈ Y.vertices ∪ {y} :=
      by
      apply @stellar_subdiv_subset_vertices _ 𝕜 _ _ _ _ _ Y t
      apply a_in_Y
    rw [Set.mem_union, Set.mem_singleton_iff] at a_in_union
    cases' a_in_union with a_in_Y a_eq_y
    specialize fg_id a_in_Y
    assumption
    subst a_eq_y
    rw [gy_x, fx_y]

def stellarSubdivOfSingletonMap
    (x y : E) : E → E := fun a : E => if a = x then y else a

theorem stellar_subdiv_of_singleton_forward_simp
    (X : AbstractSimplicialComplex E)
    (x y : E)
    (y_in_X : {y} ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
  : IsSimplicialMap
      σ(X, {y}, x; 𝕜, y_in_X, x_nin_X)
      X (stellarSubdivOfSingletonMap x y) :=
by
  simp only [IsSimplicialMap, stellarSubdivision, simplicialUnion, Set.mem_union]
  intro s s_in_subdiv
  cases' s_in_subdiv with s_in_star_comp s_in_join
  -- star complement case.
  have id_s : Finset.image (stellarSubdivOfSingletonMap x y) s = s :=
    by
    simp only [stellarSubdivOfSingletonMap, Finset.ext_iff]
    intro a
    constructor
    intro a_in_img
    rw [Finset.mem_image] at a_in_img
    choose b b_in_s fb_a using a_in_img
    have b_ne_x : b ≠ x := by
      by_cases b_eq_x : b = x
      rw [b_eq_x] at b_in_s
      have contra : x ∈ X.vertices := by
        rw [vertex_iff_in_simplex]
        use s; constructor
        apply simplex_if_in_subcomplex
        apply s_in_star_comp
        apply starComplement_subcomplex
        assumption
      contradiction
      assumption
    unfold stellarSubdivOfSingletonMap at fb_a
    simp only [b_ne_x, if_false] at fb_a
    rw [fb_a] at b_in_s
    assumption
    intro a_in_s
    rw [Finset.mem_image]
    use a; constructor; assumption
    have a_ne_x : a ≠ x := by
      by_cases a_eq_x : a = x
      rw [a_eq_x] at a_in_s
      have contra : x ∈ X.vertices := by
        rw [vertex_iff_in_simplex]
        use s; constructor
        apply simplex_if_in_subcomplex
        apply s_in_star_comp
        apply starComplement_subcomplex
        assumption
      contradiction
      assumption
    unfold stellarSubdivOfSingletonMap
    simp only [a_ne_x, if_false]
  rw [id_s]
  apply simplex_if_in_subcomplex
  apply s_in_star_comp
  apply starComplement_subcomplex
  -- join case.
  simp only [Set.mem_union, join_proj_mem] at s_in_join
  choose s' s'_in_join s₁ s₁_in_link s_decomp using s_in_join
  cases' s'_in_join with s'_in_join s'_empty

  choose s₃ s₃_in_barycenter s₂ s₂_in_bd s'_decomp using s'_in_join
  choose s'_decomp s'_nonempty using s'_decomp
  subst s'_decomp
  simp only [simplexBoundary, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe,
    Finset.mem_powerset] at s₂_in_bd
  have s₂_empty : s₂ = ∅ := by
    cases' s₂_in_bd with s₂_in_bd s₂_empty
    choose s₂_ss_y s₂_ne_y using s₂_in_bd
    rw [Finset.subset_singleton_iff] at s₂_ss_y
    cases' s₂_ss_y with s₂_empty contra
    assumption
    rw [Set.mem_insert_iff, not_or] at s₂_ne_y
    choose s₂_ne_y s₂_nonempty using s₂_ne_y
    contradiction
    assumption
  subst s₂_empty
  rw [Finset.union_empty] at s_decomp
  simp only [link, Set.mem_sep_iff] at s₁_in_link
  cases' s₁_in_link with s₁_in_link s₁_empty

  choose s₁_in_X ys₁_in_X ys₁_disj using s₁_in_link
  simp only [simplex, Set.mem_diff, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at s₃_in_barycenter
  rw [and_or_right, or_comm, Set.mem_singleton_iff, ← or_assoc, or_self_iff] at s₃_in_barycenter
  choose s₃_in_barycenter _ using s₃_in_barycenter
  cases' s₃_in_barycenter with s₃_empty s₃_eq_x
  · subst s₃_empty
    rw [Finset.empty_union] at s_decomp s'_nonempty
    contradiction
  · subst s₃_eq_x
    choose s_decomp s_nonempty using s_decomp
    subst s_decomp
    have id_s : Finset.image (stellarSubdivOfSingletonMap x y) ({x} ∪ s₁) = {y} ∪ s₁ :=
      by
      simp only [stellarSubdivOfSingletonMap, Finset.ext_iff, Finset.mem_image, Finset.mem_union,
        Finset.mem_singleton]
      intro a
      constructor
      intro a_in_img
      choose b b_in_union fb_a using a_in_img
      cases' b_in_union with b_eq_x b_in_s₁
      left
      simp only [b_eq_x, eq_self_iff_true, if_true] at fb_a
      symm
      assumption
      right
      have b_ne_x : b ≠ x := by
        by_cases b_eq_x : b = x
        rw [b_eq_x] at b_in_s₁
        have contra : x ∈ X.vertices := by
          rw [vertex_iff_in_simplex]
          use s₁
        contradiction
        assumption
      simp only [b_ne_x, if_false] at fb_a
      rw [fb_a] at b_in_s₁
      assumption
      intro a_in_union
      cases' a_in_union with a_eq_y a_in_s₁
      subst a_eq_y
      use x; constructor
      left; rfl
      simp only [eq_self_iff_true, if_true]
      have a_ne_x : a ≠ x := by
        by_cases a_eq_x : a = x
        rw [a_eq_x] at a_in_s₁
        have contra : x ∈ X.vertices := by
          rw [vertex_iff_in_simplex]
          use s₁
        contradiction
        assumption
      use a; constructor
      right; assumption
      simp only [a_ne_x, if_false]
    rw [id_s]
    assumption

  subst s₁_empty
  simp only [simplex, Set.mem_diff, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at s₃_in_barycenter
  rw [and_or_right, or_comm, Set.mem_singleton_iff, ← or_assoc, or_self_iff] at s₃_in_barycenter
  choose s₃_in_barycenter _ using s₃_in_barycenter
  cases' s₃_in_barycenter with s₃_empty s₃_eq_x
  · subst s₃_empty
    rw [Finset.empty_union] at s_decomp s'_nonempty
    contradiction
  · subst s₃_eq_x
    choose s_decomp s_nonempty using s_decomp
    rw [Finset.union_empty] at *
    subst s_decomp
    have id_s : Finset.image (stellarSubdivOfSingletonMap x y) ({x}) = {y} :=
      by
      simp only [stellarSubdivOfSingletonMap, Finset.ext_iff, Finset.mem_image, Finset.mem_union,
        Finset.mem_singleton]
      intro a
      constructor
      intro a_in_img
      choose b b_in_union fb_a using a_in_img
      cases' b_in_union with b_eq_x b_in_s₁
      simp only [eq_self_iff_true, if_true] at fb_a
      symm
      assumption
      intro a_eq_y
      use x
      constructor
      trivial
      simp only [eq_self_iff_true, if_true]
      symm
      assumption
    rw [id_s]
    assumption

  subst s'_empty
  simp only [link, Set.mem_sep_iff] at s₁_in_link
  cases' s₁_in_link with s₁_in_link s₁_empty

  choose s₁_in_X ys₁_in_X ys₁_disj using s₁_in_link
  have id_s : Finset.image (stellarSubdivOfSingletonMap x y) s = s :=
    by
    simp only [stellarSubdivOfSingletonMap, Finset.ext_iff]
    intro a
    constructor
    intro a_in_img
    rw [Finset.mem_image] at a_in_img
    choose b b_in_s fb_a using a_in_img
    have b_ne_x : b ≠ x := by
      by_cases b_eq_x : b = x
      rw [b_eq_x] at b_in_s
      have contra : x ∈ X.vertices := by
        rw [vertex_iff_in_simplex]
        use s
        constructor
        rw [Finset.empty_union] at s_decomp
        choose s_eq_s₁ s_nonempty using s_decomp
        subst s_eq_s₁
        assumption
        assumption
      contradiction
      assumption
    unfold stellarSubdivOfSingletonMap at fb_a
    simp only [b_ne_x, if_false] at fb_a
    rw [fb_a] at b_in_s
    assumption
    intro a_in_s
    rw [Finset.mem_image]
    use a; constructor; assumption
    have a_ne_x : a ≠ x := by
      by_cases a_eq_x : a = x
      rw [a_eq_x] at a_in_s
      have contra : x ∈ X.vertices := by
        rw [vertex_iff_in_simplex]
        use s
        constructor
        rw [Finset.empty_union] at s_decomp
        choose s_eq_s₁ s_nonempty using s_decomp
        subst s_eq_s₁
        assumption
        assumption
      contradiction
      assumption
    unfold stellarSubdivOfSingletonMap
    simp only [a_ne_x, if_false]
  rw [id_s]
  rw [Finset.empty_union] at s_decomp
  choose s_eq_s₁ s_nonempty using s_decomp
  subst s_eq_s₁
  assumption

  subst s₁_empty
  rw [Finset.union_empty] at s_decomp
  choose s_empty s_nonempty using s_decomp
  contradiction

theorem stellar_subdiv_of_singleton_inverse_simp
    (X : AbstractSimplicialComplex E)
    (x y : E)
    (y_in_X : {y} ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
  : IsSimplicialMap X
      σ(X, {y}, x; 𝕜, y_in_X, x_nin_X)
      (stellarSubdivOfSingletonMap y x) :=
by
  simp only [IsSimplicialMap, stellarSubdivision, simplicialUnion, Set.mem_union]
  intro s s_in_X
  by_cases y_in_s : y ∈ s
  -- y ∈ s case.
  right
  simp only [Set.mem_union, join_proj_mem]
  use {x}
  constructor

  by_cases x_empty : {x} = (∅ : Finset E)

  right
  assumption

  left
  use {x}
  constructor

  simp only [simplex, Set.mem_diff, Finset.mem_coe]

  left
  constructor
  apply Finset.mem_powerset_self
  assumption

  use ∅
  constructor

  right
  trivial

  rw [Finset.union_empty]
  constructor
  rfl
  assumption

  use s \ {y}
  constructor

  by_cases smy_empty : s \ {y} = ∅

  right
  assumption

  left
  simp only [link, Set.mem_sep_iff]
  constructor

  apply X.down_closed s_in_X
  apply Finset.sdiff_subset
  assumption

  constructor

  have s_decomp : s = {y} ∪ s \ {y} :=
    by
    rw [Finset.union_sdiff_of_subset]
    rw [Finset.singleton_subset_iff]
    assumption
  rw [← s_decomp]
  assumption

  rw [Finset.inter_comm]
  apply Finset.sdiff_inter_self

  constructor

  have s_decomp : s = {y} ∪ s \ {y} :=
    by
    rw [Finset.union_sdiff_of_subset]
    rw [Finset.singleton_subset_iff]
    assumption
  unfold stellarSubdivOfSingletonMap
  rw [s_decomp, Finset.ext_iff]
  intro a
  simp only [Finset.mem_image, Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · intro a_in_img
    choose b b_in_union fb_a using a_in_img
    cases' b_in_union with b_eq_y b_ne_y
    left
    simp only [b_eq_y, eq_self_iff_true, if_true] at fb_a
    symm
    assumption
    right
    choose b_in_s b_ne_y using b_ne_y
    simp only [b_ne_y, if_false] at fb_a
    rw [fb_a] at b_ne_y b_in_s
    constructor
    right; constructor <;> assumption
    assumption
  · intro a_in_union
    cases' a_in_union with a_eq_x a_in_s
    use y; constructor
    left; rfl
    simp only [eq_self_iff_true, if_true]
    symm
    assumption
    choose a_in_s a_ne_y using a_in_s
    cases' a_in_s with contra a_in_s
    contradiction
    choose a_in_s a_ne_y using a_in_s
    use a; constructor
    right; constructor <;> assumption
    simp only [a_ne_y, if_false]

  rw [ne_eq, Finset.image_eq_empty]
  intro s_empty
  subst s_empty
  contradiction

  -- y ∉ s case.
  left
  have id_s : Finset.image (stellarSubdivOfSingletonMap y x) s = s :=
    by
    simp only [stellarSubdivOfSingletonMap, Finset.ext_iff]
    intro a
    constructor
    intro a_in_img
    rw [Finset.mem_image] at a_in_img
    choose b b_in_s fb_a using a_in_img
    have b_ne_y : b ≠ y := by
      by_cases b_eq_y : b = y
      rw [b_eq_y] at b_in_s
      contradiction
      assumption
    unfold stellarSubdivOfSingletonMap at fb_a
    simp only [b_ne_y, if_false] at fb_a
    rw [fb_a] at b_in_s
    assumption
    intro a_in_s
    rw [Finset.mem_image]
    use a; constructor; assumption
    have a_ne_y : a ≠ y := by
      by_cases a_eq_y : a = y
      rw [a_eq_y] at a_in_s
      contradiction
      assumption
    unfold stellarSubdivOfSingletonMap
    simp only [a_ne_y, if_false]
  simp only [id_s, starComplement, Set.mem_sep_iff]
  constructor
  assumption
  rw [Finset.singleton_subset_iff]
  assumption

theorem stellar_subdiv_of_singleton
    (X : AbstractSimplicialComplex E)
    (x y : E)
    (y_in_X : {y} ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
  : σ(X, {y}, x; 𝕜, y_in_X, x_nin_X) ≅ X :=
by
  let f_subdiv :
    SimplicialMap
      σ(X, {y}, x; 𝕜, y_in_X, x_nin_X)
      X :=
    SimplicialMap.mk (stellarSubdivOfSingletonMap x y)
      (stellar_subdiv_of_singleton_forward_simp X x y y_in_X x_nin_X)
  let g_subdiv :
    SimplicialMap
      X
      σ(X, {y}, x; 𝕜, y_in_X, x_nin_X) :=
    SimplicialMap.mk (stellarSubdivOfSingletonMap y x)
      (stellar_subdiv_of_singleton_inverse_simp X x y y_in_X x_nin_X)
  unfold IsSimpliciallyIso
  use f_subdiv; use g_subdiv
  unfold IsInverseSimplicialIso
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply, id]
  constructor
  · intro a a_in_subdiv
    simp only [g_subdiv, f_subdiv, stellarSubdivOfSingletonMap]
    split_ifs with a_x y_y a_y

    symm
    assumption

    contradiction

    rw [stellar_subdiv_of_singleton_vertices, Set.mem_union, Set.mem_diff_singleton,
      Set.mem_singleton_iff] at a_in_subdiv
    cases' a_in_subdiv with a_in_X_a_ne_y a_eq_y
    choose a_in_X a_ne_y using a_in_X_a_ne_y
    contradiction
    symm
    assumption

    rfl
  · intro a a_in_X
    simp only [f_subdiv, g_subdiv, stellarSubdivOfSingletonMap]
    split_ifs
    symm
    assumption
    contradiction
    subst a
    contradiction
    rfl

theorem stellar_subdiv_congr_simplices
    (X Y : AbstractSimplicialComplex E)
    (s : Finset E)
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (X_eq_Y : X.faces = Y.faces)
  : σ(X, s, x; 𝕜, s_in_X, x_nin_X).faces =
      σ(Y, s, x; 𝕜, by rw [← X_eq_Y]; assumption, by rw [← vertices_congr X Y X_eq_Y]; assumption).faces :=
by
  simp only [stellarSubdivision, simplicialUnion, starComplement, link, simplex, simplexBoundary, X_eq_Y]
  rfl
