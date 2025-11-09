import Mathlib.Tactic
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Pachner.SimplicialComplex
import Pachner.SimplicialMap
import Pachner.SimplicialSubcomplex

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
      (π₁[𝕜] (@barycenter_join_boundary_disjoint_link _ _ 𝕜 _ _ _ _ X s x s_in_X x_nin_X)).coe ''ˢ
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
      ↥((π₁[𝕜] (@barycenter_join_boundary_disjoint_link E _ 𝕜 _ _ _ _ X s x s_in_X x_nin_X)).coe ''ˢ
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

@[simp]
def StellarMove : AbstractSimplicialComplex E → AbstractSimplicialComplex E → Prop :=
  fun X Y : AbstractSimplicialComplex E =>
  (∃ (t : Finset E) (Ht : t ∈ Y.faces) (Ht_ne : Nonempty t) (y : E) (Hy : y ∉ Y.vertices),
      X ≅ @stellarSubdivision _ 𝕜 _ _ _ _ _ Y t y Ht Hy) ∨
    (∃ (s : Finset E) (Hs : s ∈ X.faces) (Hs_ne : Nonempty s) (x : E) (Hx : x ∉ X.vertices),
        Y ≅ @stellarSubdivision _ 𝕜 _ _ _ _ _ X s x Hs Hx) ∨
      X ≅ Y

noncomputable instance StellarMove.Weld.fintype
    (X Y : AbstractSimplicialComplex E) [Fintype X.faces]
    (X_weld_Y :
      ∃ (t : Finset E) (Ht : t ∈ Y.faces) (Ht_ne : Nonempty t) (y : E) (Hy : y ∉ Y.vertices),
        X ≅ @stellarSubdivision _ 𝕜 _ _ _ _ _ Y t y Ht Hy)
  : Fintype Y.faces :=
by
  choose t t_in_Y t_ne y y_nin_Y X_weld_Y using X_weld_Y
  apply
    @stellarSubdivision.fintypeConverse _ 𝕜 _ _ _ _ _ Y t _ y t_in_Y y_nin_Y
      (IsSimpliciallyIso.Fintype X σ(Y, t, y; 𝕜, t_in_Y, y_nin_Y) X_weld_Y)

noncomputable instance StellarMove.Subdiv.fintype
    (X Y : AbstractSimplicialComplex E)
    [X_fin : Fintype X.faces]
    (X_subdiv_Y :
      ∃ (s : Finset E) (Hs : s ∈ X.faces) (Hs_ne : Nonempty s) (x : E) (Hx : x ∉ X.vertices),
        Y ≅ @stellarSubdivision _ 𝕜 _ _ _ _ _ X s x Hs Hx)
  : Fintype Y.faces :=
by
  choose s s_in_X s_ne x x_nin_X X_subdiv_Y using X_subdiv_Y
  rw [simplicial_iso_symm] at X_subdiv_Y
  apply
    @IsSimpliciallyIso.Fintype _ _ _ _ σ(X, s, x; 𝕜, s_in_X, x_nin_X)
      (@stellarSubdivision.fintype _ 𝕜 _ _ _ _ _ X X_fin s x s_in_X x_nin_X) Y X_subdiv_Y

noncomputable instance StellarMove.fintype
    (X Y : AbstractSimplicialComplex E) [Fintype X.faces]
    (X_move_Y : @StellarMove _ 𝕜 _ _ _ _ _ X Y)
  : Fintype Y.faces :=
by
  simp only [StellarMove] at X_move_Y
  by_cases X_weld_Y :
    ∃ (t : Finset E) (Ht : t ∈ Y.faces) (Ht_ne : Nonempty t) (y : E) (Hy : y ∉ Y.vertices),
      X ≅ @stellarSubdivision _ 𝕜 _ _ _ _ _ Y t y Ht Hy
  apply StellarMove.Weld.fintype X Y X_weld_Y
  by_cases X_subdiv_Y :
    ∃ (s : Finset E) (Hs : s ∈ X.faces) (Hs_ne : Nonempty s) (x : E) (Hx : x ∉ X.vertices),
      Y ≅ @stellarSubdivision _ 𝕜 _ _ _ _ _ X s x Hs Hx
  apply StellarMove.Subdiv.fintype X Y X_subdiv_Y
  by_cases X_iso_Y : X ≅ Y
  apply IsSimpliciallyIso.Fintype X Y X_iso_Y
  have contra : ¬@StellarMove _ 𝕜 _ _ _ _ _ X Y :=
    by
    simp only [StellarMove, not_or]
    constructor; assumption
    constructor; assumption
    assumption
  contradiction

theorem stellarMove_preserves_dim
    (X Y : AbstractSimplicialComplex E) [X_fin : Fintype X.faces]
    [Y_fin : Fintype Y.faces]
    (X_move_Y : @StellarMove _ 𝕜 _ _ _ _ _ X Y)
  : X.dim = Y.dim :=
by
  simp only [StellarMove] at X_move_Y
  cases' X_move_Y with Y_subdiv_X X_move_Y
  choose t t_in_Y t_ne y y_nin_Y Y_subdiv_X using Y_subdiv_X
  rw [simplicial_iso_preserves_dim X σ(Y, t, y; 𝕜, t_in_Y, y_nin_Y) Y_subdiv_X]
  symm
  rw [@stellar_subdiv_preserves_dim _ 𝕜 _ _ _ _ _ Y  _ t y t_in_Y y_nin_Y]
  rotate_left
  cases' X_move_Y with X_subdiv_Y X_iso_Y
  choose s s_in_X s_ne x x_nin_X X_subdiv_Y using X_subdiv_Y
  rw [simplicial_iso_preserves_dim Y σ(X, s, x; 𝕜, s_in_X, x_nin_X) X_subdiv_Y]
  rw [@stellar_subdiv_preserves_dim _ 𝕜 _ _ _ _ _ X X_fin s x s_in_X x_nin_X]
  rotate_left
  rw [simplicial_iso_preserves_dim X Y X_iso_Y]
  all_goals
    unfold AbstractSimplicialComplex.dim
    apply le_antisymm <;>
      · apply Finset.max'_le
        intro z z_in_img
        simp only [Finset.mem_image, Set.mem_toFinset, Finset.mem_union] at z_in_img
        cases' z_in_img with z_in_img z_negative

        choose u u_in_K dim_u_z using z_in_img
        apply Finset.le_max'
        simp only [Finset.mem_image, Set.mem_toFinset, Finset.mem_union]
        left
        use u

        apply Finset.le_max'
        simp only [Finset.mem_image, Set.mem_toFinset, Finset.mem_union]
        right
        assumption

def StellarEquiv
    : AbstractSimplicialComplex E → AbstractSimplicialComplex E → Prop :=
  Relation.ReflTransGen (@StellarMove _ 𝕜 _ _ _ _ _)

notation X " ≅ₛₜ[" 𝕜 "] " Y : 50 => @StellarEquiv _ 𝕜 _ _ _ _ _ X Y

noncomputable instance StellarEquiv.fintype
    (X Y : AbstractSimplicialComplex E)
    [Fintype X.faces]
    (X_eq_Y : X ≅ₛₜ[𝕜] Y)
  : Fintype Y.faces :=
by
  apply Set.Finite.fintype
  induction' X_eq_Y with K L X_eq_K K_move_L L_dec
  rw [Set.finite_def]
  constructor
  assumption
  rw [Set.finite_def]
  have K_fin : Fintype K.faces := by
    apply Set.Finite.fintype
    assumption
  constructor
  apply @StellarMove.fintype _ 𝕜 _ _ _ _ _ K L _ K_move_L

theorem stellarEquiv_preserves_dim
    (X Y : AbstractSimplicialComplex E)
    [X_fin : Fintype X.faces]
    (X_eq_Y : X ≅ₛₜ[𝕜] Y)
  : X.dim = @AbstractSimplicialComplex.dim _ Y (@StellarEquiv.fintype _ 𝕜 _ _ _ _ _ X Y X_fin X_eq_Y) :=
by
  induction' X_eq_Y with K L X_eq_K K_move_L H_ind
  · unfold AbstractSimplicialComplex.dim
    apply le_antisymm <;>
      · rw [Finset.max'_le_iff]
        intro y y_max
        apply Finset.le_max'
        simp only [Finset.mem_image, Set.mem_toFinset, Finset.mem_union] at y_max ⊢
        cases' y_max with y_max y_neg

        left
        choose s s_in_img dim_s_y using y_max
        use s

        right
        assumption
  · let K_fin : Fintype K.faces := by
        apply @StellarEquiv.fintype _ 𝕜 _ _ _ _ _ X K _ X_eq_K
    trans K.dim
    assumption

    let K_eq_L : K ≅ₛₜ[𝕜] L := by
        unfold StellarEquiv
        apply Relation.ReflTransGen.single
        assumption
    let L_fin : Fintype L.faces := by
        apply @StellarEquiv.fintype _ 𝕜 _ _ _ _ _ K L K_fin K_eq_L
    apply @stellarMove_preserves_dim _ 𝕜 _ _ _ _ _ K L K_fin L_fin
    assumption

@[refl]
theorem stellarEquiv_refl
    (X : AbstractSimplicialComplex E)
  : X ≅ₛₜ[𝕜] X :=
by
  unfold StellarEquiv
  apply Relation.ReflTransGen.refl

@[symm]
theorem stellarEquiv_symm
    (X Y : AbstractSimplicialComplex E)
  : X ≅ₛₜ[𝕜] Y ↔ Y ≅ₛₜ[𝕜] X :=
by
  unfold StellarEquiv
  constructor <;>
    · apply Relation.ReflTransGen.symmetric
      rw [← swap_eq_iff]
      unfold StellarMove Function.swap
      apply funext; intro K
      apply funext; intro L
      simp only [eq_iff_iff]
      constructor
      · intro L_move_K
        cases' L_move_K with K_move_L L_move_K
        · right; left
          choose s Hs Hs_ne x Hx L_subdiv_K using K_move_L
          use s; use Hs; use Hs_ne; use x; use Hx
        · cases' L_move_K with L_move_K L_iso_K
          · left
            choose t Ht Ht_ne y Hy K_subdiv_L using L_move_K
            use t; use Ht; use Ht_ne; use y; use Hy
          · right; right
            rw [simplicial_iso_symm]
            assumption
      · intro K_move_L
        cases' K_move_L with L_move_K K_move_L
        · right; left
          choose s Hs Hs_ne x Hx K_subdiv_L using L_move_K
          use s; use Hs; use Hs_ne; use x; use Hx
        · cases' K_move_L with K_move_L K_iso_L
          · left
            choose t Ht Ht_ne y Hy L_subdiv_K using K_move_L
            use t; use Ht; use Ht_ne; use y; use Hy
          · right; right
            rw [simplicial_iso_symm]
            assumption

@[trans]
theorem stellarEquiv_trans
    (X Y Z : AbstractSimplicialComplex E)
  : X ≅ₛₜ[𝕜] Y → Y ≅ₛₜ[𝕜] Z → X ≅ₛₜ[𝕜] Z :=
by
  unfold StellarEquiv
  apply Relation.transitive_reflTransGen

theorem stellarEquiv_neg_trans
    (X Y Z : AbstractSimplicialComplex E)
  : X ≅ₛₜ[𝕜] Y → ¬Y ≅ₛₜ[𝕜] Z → ¬X ≅ₛₜ[𝕜] Z :=
by
  intro X_eq_Y Y_neq_Z
  revert Y_neq_Z
  contrapose
  simp only [Classical.not_not]
  intro X_eq_Z
  rw [stellarEquiv_symm] at X_eq_Y
  revert X_eq_Y X_eq_Z
  apply stellarEquiv_trans

-- TODO: maybe fix precedence for ≅ so we don't need parenthesis here
theorem stellarEquiv_preserves_iso
    (X Y : AbstractSimplicialComplex E)
  : (X ≅ Y) → X ≅ₛₜ[𝕜] Y :=
by
  intro X_iso_Y
  simp only [StellarEquiv]
  apply Relation.ReflTransGen.single
  simp only [StellarMove]
  right; right
  assumption

@[simp]
def stellarCoeMap (f : E → F) (x : E) (y : F) : E → F := fun a : E => if a = x then y else f a

theorem stellar_coe_simplex_image
    (s : Finset E)
    (x : E)
    (y : F)
    (f : E → F)
  : x ∉ s → Finset.image (stellarCoeMap f x y) s = Finset.image f s :=
by
  rw [Finset.ext_iff]
  intro x_nin_s b
  simp only [Finset.mem_image, stellarCoeMap]
  constructor
  · intro b_in_coe
    choose a a_in_s coe_a_b using b_in_coe
    revert coe_a_b
    split_ifs with a_eq_x
    rw [a_eq_x] at a_in_s
    contradiction
    intro fa_b
    use a
  · intro b_in_img
    choose a a_in_s fa_b using b_in_img
    use a; constructor; assumption
    split_ifs with a_eq_x
    rw [a_eq_x] at a_in_s
    contradiction
    assumption

theorem stellar_coe_forward_simplicial
    --[Nonempty E] TODO: keep this or not? seems redundant to [Nonempty s]
    (X : AbstractSimplicialComplex E)
    (φ : SimplicialCoe X F)
    (s : Finset E) [s_ne : Nonempty s]
    (x : E)
    (y : F)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (y_nin_coe : y ∉ (φ.coe ''ˢ X).vertices)
  : IsSimplicialMap
      σ(X, s, x; 𝕜, s_in_X, x_nin_X)
      σ(φ.coe ''ˢ X, Finset.image φ.coe s, y; 𝕜, by apply map_is_simplicial_onto_image; assumption, y_nin_coe)
      (stellarCoeMap φ.coe x y) :=
by
  simp only [IsSimplicialMap, stellarSubdivision, simplicialUnion, Set.mem_union]
  intro t t_in_subdiv
  cases' t_in_subdiv with t_in_star_comp t_in_join

  left
  rw [starComplement_coe_image X s s_in_X φ, stellar_coe_simplex_image]
  apply map_is_simplicial_onto_image
  assumption
  revert x_nin_X
  contrapose
  simp only [Classical.not_not]
  revert x
  simp only [← Finset.mem_coe, ← Set.subset_def]
  apply simplex_subset_vertices
  apply simplex_if_in_subcomplex X
  exact starComplement_subcomplex_simplices X s t t_in_star_comp
  simp only [AbstractSimplicialComplex.instHasSubset, IsSubcomplex]
  rfl

  right
  simp only [join_proj_mem, Set.mem_union] at t_in_join ⊢
  choose t' t'_in_join t₁ t₁_in_link t_decomp using t_in_join
  cases' t'_in_join with t'_in_join t'_empty

  choose t₃ t₃_in_barycenter t₂ t₂_in_bd t'_decomp using t'_in_join
  choose t'_decomp t'_nonempty using t'_decomp
  subst t'_decomp
  use Finset.image (stellarCoeMap φ.coe x y) (t₃ ∪ t₂)
  constructor

  left
  use Finset.image (stellarCoeMap φ.coe x y) t₃
  constructor

  simp only [simplex, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff, Set.mem_diff] at t₃_in_barycenter ⊢
  rw [and_or_right, or_comm, Set.mem_singleton_iff, ← or_assoc, or_self_iff] at t₃_in_barycenter
  choose t₃_in_barycenter _ using t₃_in_barycenter
  cases' t₃_in_barycenter with t₃_empty t₃_x


  subst t₃_empty
  right
  apply Finset.image_empty

  left
  constructor

  right
  rw [t₃_x, Finset.image_singleton]
  simp only [stellarCoeMap, eq_self_iff_true, if_true]

  rw [Set.mem_singleton_iff, Finset.image_eq_empty]
  subst t₃_x
  apply Finset.singleton_ne_empty

  use Finset.image (stellarCoeMap φ.coe x y) t₂
  cases' t₂_in_bd with t₂_in_bd t₂_empty

  constructor

  left
  rw [simplexBoundary_coe_image, stellar_coe_simplex_image]
  apply map_is_simplicial_onto_image
  assumption

  revert x_nin_X
  contrapose
  simp only [Classical.not_not, ← Finset.mem_coe]
  have t₂_in_X : ↑t₂ ⊆ X.vertices :=
    by
    apply simplex_subset_vertices
    apply simplex_if_in_subcomplex
    apply t₂_in_bd
    apply simplexBoundary_subcomplex
    assumption
  rw [Set.subset_def] at t₂_in_X
  specialize t₂_in_X x
  assumption

  assumption

  constructor

  apply Finset.image_union

  rw [ne_eq, Finset.image_eq_empty]
  assumption

  subst t₂_empty
  rw [Finset.image_empty]
  rw [Finset.union_empty]
  rw [Finset.union_empty] at t_decomp t'_nonempty ⊢
  constructor

  right
  rfl

  constructor

  rfl

  rw [ne_eq, Finset.image_eq_empty]
  assumption

  choose t_decomp t_nonempty using t_decomp
  use Finset.image (stellarCoeMap φ.coe x y) t₁
  rw [← Finset.image_union]

  constructor

  cases' t₁_in_link with t₁_in_link t₁_empty

  left
  rw [link_coe_image, stellar_coe_simplex_image]
  apply map_is_simplicial_onto_image
  assumption
  revert x_nin_X
  contrapose
  simp only [Classical.not_not, ← Finset.mem_coe]
  have t₁_in_X : ↑t₁ ⊆ X.vertices :=
    by
    apply simplex_subset_vertices
    apply simplex_if_in_subcomplex
    apply t₁_in_link
    apply link_subcomplex
  rw [Set.subset_def] at t₁_in_X
  specialize t₁_in_X x
  assumption
  assumption

  right
  subst t₁_empty
  apply Finset.image_empty

  constructor
  subst t_decomp
  rfl
  rw [ne_eq, Finset.image_eq_empty]
  assumption

  subst t'_empty
  rw [Finset.empty_union] at t_decomp
  choose t_eq_t₁ t_nonempty using t_decomp
  subst t_eq_t₁
  cases' t₁_in_link with t_in_link t_empty

  use ∅
  constructor

  right
  rfl

  use Finset.image (stellarCoeMap φ.coe x y) t
  constructor

  left
  rw [link_coe_image, stellar_coe_simplex_image]
  apply map_is_simplicial_onto_image
  assumption
  revert x_nin_X
  contrapose
  simp only [Classical.not_not, ← Finset.mem_coe]
  have t_in_X : ↑t ⊆ X.vertices :=
    by
    apply simplex_subset_vertices
    apply simplex_if_in_subcomplex
    apply t_in_link
    apply link_subcomplex
  rw [Set.subset_def] at t_in_X
  specialize t_in_X x
  assumption
  assumption

  constructor

  rw [Finset.empty_union]

  rw [ne_eq, Finset.image_eq_empty]
  assumption

  contradiction

theorem stellar_coe_inverse_simplicial
    (X : AbstractSimplicialComplex E)
    (φ : SimplicialCoe X F)
    (s : Finset E)
    (x : E)
    (y : F)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (y_nin_coe : y ∉ (φ.coe ''ˢ X).vertices)
  : IsSimplicialMap
      σ(φ.coe ''ˢ X, Finset.image φ.coe s, y; 𝕜, by apply map_is_simplicial_onto_image; assumption, y_nin_coe)
      σ(X, s, x; 𝕜, s_in_X, x_nin_X)
      (stellarCoeMap (φ⁻ᶜ.map) y x) :=
by
  simp only [IsSimplicialMap, stellarSubdivision, simplicialUnion, Set.mem_union]
  intro t t_in_subdiv
  cases' t_in_subdiv with t_in_star_comp t_in_join

  left
  rw [stellar_coe_simplex_image]
  rw [starComplement_coe_image, simplicialImage_is_lift_image, Set.mem_image] at t_in_star_comp
  choose u u_in_star_comp φu_t using t_in_star_comp
  simp only [simplicialMapLift] at φu_t
  rw [← φu_t]
  have inv_u : Finset.image (φ⁻ᶜ.map) (Finset.image φ.coe u) = u :=
    by
    simp only [← Finset.coe_inj, Finset.coe_image]
    apply Set.InjOn.invFunOn_image
    apply φ.Injective
    apply simplex_subset_vertices
    apply simplex_if_in_subcomplex
    apply u_in_star_comp
    apply starComplement_subcomplex
  rw [inv_u]
  assumption
  assumption
  revert y_nin_coe
  contrapose
  simp only [Classical.not_not]
  revert y
  simp only [← Finset.mem_coe, ← Set.subset_def]
  apply simplex_subset_vertices
  apply simplex_if_in_subcomplex ((φ.coe ''ˢ X)\St(φ.coe ''ˢ X, Finset.image φ.coe s))
  assumption
  apply starComplement_subcomplex

  right
  simp only [join_proj_mem, Set.mem_union] at t_in_join ⊢
  choose t' t'_in_join t₁ t₁_in_link t_decomp using t_in_join
  cases' t'_in_join with t'_in_join t'_empty

  choose t₃ t₃_in_barycenter t₂ t₂_in_bd t'_decomp using t'_in_join
  choose t'_decomp t'_nonempty using t'_decomp
  subst t'_decomp
  use Finset.image (stellarCoeMap (φ⁻ᶜ.map) y x) (t₃ ∪ t₂)
  constructor

  left
  use Finset.image (stellarCoeMap (φ⁻ᶜ.map) y x) t₃
  constructor

  simp only [simplex, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff, Set.mem_diff] at t₃_in_barycenter ⊢
  rw [and_or_right, or_comm, Set.mem_singleton_iff, ← or_assoc, or_self_iff] at t₃_in_barycenter
  choose t₃_in_barycenter _ using t₃_in_barycenter
  cases' t₃_in_barycenter with t₃_empty t₃_x

  subst t₃_empty
  rw [Finset.image_empty]
  right
  rfl

  subst t₃_x
  rw [Finset.image_singleton]
  rw [and_or_right, or_comm, Set.mem_singleton_iff, ← or_assoc, or_self_iff]
  simp only [stellarCoeMap, if_true, or_true, Finset.singleton_ne_empty, not_false_eq_true, or_false, and_true]

  use Finset.image (stellarCoeMap (φ⁻ᶜ.map) y x) t₂
  constructor

  cases' t₂_in_bd with t₂_in_bd t₂_empty

  left
  rw [stellar_coe_simplex_image]
  rw [simplexBoundary_coe_image, simplicialImage_is_lift_image, Set.mem_image] at t₂_in_bd
  choose u u_in_bd φu_t₂ using t₂_in_bd
  simp only [simplicialMapLift] at φu_t₂
  rw [← φu_t₂]
  have inv_u : Finset.image (φ⁻ᶜ.map) (Finset.image φ.coe u) = u :=
    by
    simp only [← Finset.coe_inj, Finset.coe_image]
    apply Set.InjOn.invFunOn_image
    apply φ.Injective
    apply simplex_subset_vertices
    apply simplex_if_in_subcomplex
    apply u_in_bd
    apply simplexBoundary_subcomplex
    assumption
  rw [inv_u]
  assumption
  assumption
  revert y_nin_coe
  contrapose
  simp only [Classical.not_not, ← Finset.mem_coe]
  have t₂_in_X : ↑t₂ ⊆ (φ.coe ''ˢ X).vertices :=
    by
    apply simplex_subset_vertices
    apply simplex_if_in_subcomplex
    apply t₂_in_bd
    apply simplexBoundary_subcomplex
    apply map_is_simplicial_onto_image
    assumption
  rw [Set.subset_def] at t₂_in_X
  specialize t₂_in_X y
  assumption

  right
  subst t₂_empty
  apply Finset.image_empty

  constructor

  rw [Finset.image_union]
  rw [ne_eq, Finset.image_eq_empty]
  assumption

  simp only [ne_eq, Finset.image_eq_empty, t'_nonempty, not_false_eq_true]

  use Finset.image (stellarCoeMap (φ⁻ᶜ.map) y x) t₁
  cases' t₁_in_link with t₁_in_link t₁_empty

  constructor

  rw [stellar_coe_simplex_image]
  rw [link_coe_image, simplicialImage_is_lift_image, Set.mem_image] at t₁_in_link

  left
  choose u u_in_link φu_t₁ using t₁_in_link
  simp only [simplicialMapLift] at φu_t₁
  rw [← φu_t₁]
  have inv_u : Finset.image (φ⁻ᶜ.map) (Finset.image φ.coe u) = u :=
    by
    simp only [← Finset.coe_inj, Finset.coe_image]
    apply Set.InjOn.invFunOn_image
    apply φ.Injective
    apply simplex_subset_vertices
    apply simplex_if_in_subcomplex
    apply u_in_link
    apply link_subcomplex
  rw [inv_u]
  assumption
  assumption

  revert y_nin_coe
  contrapose
  simp only [Classical.not_not, ← Finset.mem_coe]
  have t₁_in_X : ↑t₁ ⊆ (φ.coe ''ˢ X).vertices :=
    by
    apply simplex_subset_vertices
    apply simplex_if_in_subcomplex
    apply t₁_in_link
    apply link_subcomplex
  rw [Set.subset_def] at t₁_in_X
  specialize t₁_in_X y
  assumption

  choose t_decomp t_nonempty using t_decomp
  constructor

  subst t_decomp
  rw [← Finset.image_union]

  assumption

  subst t₁_empty
  rw [Finset.image_empty]
  constructor

  right
  rfl

  choose t_decomp t_nonempty using t_decomp
  constructor

  rw [Finset.union_empty] at t_decomp ⊢
  subst t_decomp
  rw [Finset.image_union]

  assumption

  subst t'_empty
  rw [Finset.empty_union] at t_decomp
  choose t_eq_t₁ t_nonempty using t_decomp
  subst t_eq_t₁
  cases' t₁_in_link with t_in_link t_empty

  use ∅

  constructor

  right
  rfl

  use Finset.image (stellarCoeMap (φ⁻ᶜ.map) y x) t
  constructor

  left
  rw [stellar_coe_simplex_image]
  rw [link_coe_image, simplicialImage_is_lift_image, Set.mem_image] at t_in_link
  choose u u_in_link φu_t using t_in_link
  simp only [simplicialMapLift] at φu_t
  rw [← φu_t]
  have inv_u : Finset.image (φ⁻ᶜ.map) (Finset.image φ.coe u) = u :=
    by
    simp only [← Finset.coe_inj, Finset.coe_image]
    apply Set.InjOn.invFunOn_image
    apply φ.Injective
    apply simplex_subset_vertices
    apply simplex_if_in_subcomplex
    apply u_in_link
    apply link_subcomplex
  rw [inv_u]
  assumption
  assumption

  revert y_nin_coe
  contrapose
  simp only [Classical.not_not, ← Finset.mem_coe]
  have t₁_in_X : ↑t ⊆ (φ.coe ''ˢ X).vertices :=
    by
    apply simplex_subset_vertices
    apply simplex_if_in_subcomplex
    apply t_in_link
    apply link_subcomplex
  rw [Set.subset_def] at t₁_in_X
  specialize t₁_in_X y
  assumption

  constructor

  rw [Finset.empty_union]

  rw [ne_eq, Finset.image_eq_empty]
  assumption

  contradiction

def stellarCoeForward
    (X : AbstractSimplicialComplex E)
    (φ : SimplicialCoe X F)
    (s : Finset E) [s_ne : Nonempty s]
    (x : E)
    (y : F)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (y_nin_coe : y ∉ (φ.coe ''ˢ X).vertices)
  : SimplicialMap
      σ(X, s, x; 𝕜, s_in_X, x_nin_X)
      σ(φ.coe ''ˢ X, Finset.image φ.coe s, y; 𝕜, by apply map_is_simplicial_onto_image; assumption, y_nin_coe) :=
  SimplicialMap.mk (stellarCoeMap φ.coe x y)
    (stellar_coe_forward_simplicial X φ s x y s_in_X x_nin_X y_nin_coe)

noncomputable def stellarCoeInverse
    (X : AbstractSimplicialComplex E)
    (φ : SimplicialCoe X F)
    (s : Finset E)
    (x : E)
    (y : F)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (y_nin_coe : y ∉ (φ.coe ''ˢ X).vertices)
  : SimplicialMap
      σ(φ.coe ''ˢ X, Finset.image φ.coe s, y; 𝕜, by apply map_is_simplicial_onto_image; assumption, y_nin_coe)
      σ(X, s, x; 𝕜, s_in_X, x_nin_X) :=
  SimplicialMap.mk (stellarCoeMap (φ⁻ᶜ.map) y x)
    (stellar_coe_inverse_simplicial X φ s x y s_in_X x_nin_X y_nin_coe)

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

theorem stellar_coe_vertices
    (X : AbstractSimplicialComplex E)
    (φ : SimplicialCoe X F)
    (s : Finset E)
    (x : E)
    (y : F)
    (x_nin_X : x ∉ X.vertices)
  : (simplicialImage (stellarCoeMap φ.coe x y) X).vertices = (φ.coe ''ˢ X).vertices :=
by
  simp only [simplicialImage_vertices, Set.ext_iff, Set.mem_image]
  intro t
  constructor <;>
    · intro t_in_img
      choose u u_in_X coe_u_t using t_in_img
      use u; constructor; assumption
      rw [← coe_u_t]
      have u_ne_x : u ≠ x := by
        by_contra u_eq_x
        rw [u_eq_x] at u_in_X
        contradiction
      simp only [stellarCoeMap, u_ne_x, if_false]

theorem stellar_coe_image
    (X : AbstractSimplicialComplex E)
    (φ : SimplicialCoe X F)
    (s : Finset E) [s_ne : Nonempty s]
    (x : E)
    (y : F)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (y_nin_coe : y ∉ (φ.coe ''ˢ X).vertices)
  : σ(simplicialImage (stellarCoeMap φ.coe x y) X, Finset.image (stellarCoeMap φ.coe x y) s,
        (stellarCoeMap φ.coe x y) x; 𝕜, by apply map_is_simplicial_onto_image; assumption,
        by
          simp only [stellarCoeMap, ↓reduceIte]
          rw [stellar_coe_vertices X φ s x y] <;> assumption)
      ≅ σ(simplicialImage φ.coe X, Finset.image φ.coe s, y; 𝕜,
          by
            apply map_is_simplicial_onto_image
            assumption,
          y_nin_coe) :=
by
  apply simplicial_iso_preserves_equiv
  have x_nin_s : x ∉ s := by
    revert x_nin_X
    contrapose
    simp only [Classical.not_not, ← Finset.mem_coe]
    have s_ss_X : ↑s ⊆ X.vertices := by
      apply simplex_subset_vertices
      assumption
    rw [Set.subset_def] at s_ss_X
    specialize s_ss_X x
    assumption
  simp only [stellar_coe_simplex_image s x y φ.coe x_nin_s]
  simp only [stellarCoeMap, eq_self_iff_true, if_true]
  apply stellar_subdiv_congr_simplices
  apply simplicialImage_congr
  simp only [Set.EqOn]
  intro z z_in_X

  simp only [stellarCoeMap, ite_eq_right_iff]
  intros h
  rw [h] at z_in_X
  contradiction

theorem stellar_coe_inv_iso
    (X : AbstractSimplicialComplex E)
    (φ : SimplicialCoe X F)
    (s : Finset E) [s_ne : Nonempty s]
    (x : E)
    (y : F)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (y_nin_coe : y ∉ (φ.coe ''ˢ X).vertices)
  : IsInverseSimplicialIso (stellarCoeForward X φ s x y s_in_X x_nin_X y_nin_coe)
      (@stellarCoeInverse _ _ 𝕜 _ _ _ _ _ _ _ X φ s x y s_in_X x_nin_X y_nin_coe) :=
by
  unfold IsInverseSimplicialIso
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply, id]
  simp only [stellarCoeInverse, stellarCoeForward]
  constructor
  · intro a a_in_subdiv
    have a_in_union : a ∈ X.vertices ∪ {x} :=
    by
      apply Set.mem_of_mem_of_subset a_in_subdiv
      apply stellar_subdiv_subset_vertices
    rw [Set.mem_union, Set.mem_singleton_iff] at a_in_union
    cases' a_in_union with a_in_X a_eq_x
    have a_ne_x : ¬a = x := by
      by_cases a_eq_x : a = x
      rw [a_eq_x] at a_in_X
      contradiction
      assumption
    have φa_ne_y : ¬φ.coe a = y := by
      by_cases φa_eq_y : φ.coe a = y
      have contra : y ∈ (φ.coe ''ˢ X).vertices :=
        by
        rw [simplicialImage_vertices, Set.mem_image]
        use a
      contradiction
      assumption
    simp only [stellarCoeMap, a_ne_x, φa_ne_y, if_false]
    apply Set.InjOn.leftInvOn_invFunOn
    apply φ.Injective
    assumption
    simp only [stellarCoeMap, a_eq_x, eq_self_iff_true, if_true]
  · intro b b_in_coe
    have b_in_union : b ∈ (φ.coe ''ˢ X).vertices ∪ {y} :=
    by
      apply Set.mem_of_mem_of_subset
      apply b_in_coe
      have φs_ne : Nonempty {x // x ∈ Finset.image φ.coe s} :=
      by
        rw [Finset.nonempty_coe_sort, Finset.image_nonempty, ← Finset.nonempty_coe_sort]
        assumption
      apply stellar_subdiv_subset_vertices
    rw [Set.mem_union, Set.mem_singleton_iff] at b_in_union
    cases' b_in_union with b_in_X b_eq_y
    have b_ne_y : ¬b = y := by
      by_cases b_eq_y : b = y
      rw [b_eq_y] at b_in_X
      contradiction
      assumption
    have φb_ne_x : ¬φ⁻ᶜ.map b = x :=
      by
      by_cases φb_eq_x : φ⁻ᶜ.map b = x
      rw [simplicialImage_vertices, Set.mem_image] at b_in_X
      choose a a_in_X φa_b using b_in_X
      rw [← φa_b] at φb_eq_x
      have inv_a : φ⁻ᶜ.map (φ.coe a) = a :=
        by
        simp only [simplicialCoeInv]
        apply Set.InjOn.leftInvOn_invFunOn
        apply φ.Injective
        assumption
      rw [inv_a] at φb_eq_x
      rw [φb_eq_x] at a_in_X
      contradiction
      assumption
    simp only [stellarCoeMap, b_ne_y, φb_ne_x, if_false]
    simp only [simplicialCoeInv]
    apply Function.invFunOn_eq
    simp only [simplicialImage_vertices, Set.mem_image] at b_in_X
    assumption
    simp only [stellarCoeMap, b_eq_y, eq_self_iff_true, if_true]

theorem stellar_coe_iso
    (X : AbstractSimplicialComplex E)
    (φ : SimplicialCoe X F)
    (s : Finset E) [s_ne : Nonempty s]
    (x : E)
    (y : F)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (y_nin_coe : y ∉ (φ.coe ''ˢ X).vertices)
  : IsSimplicialIso (@stellarCoeForward _ _ 𝕜 _ _ _ _ _ _ _ X φ s _ x y s_in_X x_nin_X y_nin_coe) :=
by
  use stellarCoeInverse X φ s x y s_in_X x_nin_X y_nin_coe
  apply stellar_coe_inv_iso

theorem stellar_weld_exists_iso
    (X Y : AbstractSimplicialComplex E)
    (Z : AbstractSimplicialComplex F)
    (t : Finset E) [t_ne : Nonempty t]
    (y : E)
    (t_in_Y : t ∈ Y.faces)
    (y_nin_Y : y ∉ Y.vertices)
  : (X ≅ Z) → X ≅ σ(Y, t, y; 𝕜, t_in_Y, y_nin_Y) → ∃ W : AbstractSimplicialComplex F, (Y ≅ W) ∧ Z ≅ₛₜ[𝕜] W :=
by
  intro X_iso_Z Y_subdiv_X
  have Z_iso_subdiv : Z ≅ σ(Y, t, y; 𝕜, t_in_Y, y_nin_Y) :=
  by
    apply simplicial_iso_trans Z X
    rw [simplicial_iso_symm]
    assumption
    assumption
  let Z_iso_subdiv' := Z_iso_subdiv
  unfold IsSimpliciallyIso at Z_iso_subdiv'
  choose f f_iso using Z_iso_subdiv'
  let f_iso' := f_iso
  unfold IsSimplicialIso at f_iso'
  choose g gf_inv using f_iso'
  let gf_inv' := gf_inv
  unfold IsInverseSimplicialIso at gf_inv'
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply,
    id] at gf_inv'
  choose gf_id fg_id using gf_inv'
  have g_iso : IsSimplicialIso g := by apply iso_inv_is_iso f g f_iso gf_inv
  by_cases t_singleton : t.card = 1
  rw [Finset.card_eq_one] at t_singleton
  choose a t_eq_a using t_singleton
  subst t_eq_a
  rw [stellar_subdiv_of_singleton_vertices] at fg_id
  use Z; constructor
  apply simplicial_iso_trans Y σ(Y, {a}, y; 𝕜, t_in_Y, y_nin_Y)
  rw [simplicial_iso_symm]
  apply stellar_subdiv_of_singleton
  rw [simplicial_iso_symm]
  assumption
  apply Relation.ReflTransGen.single
  unfold StellarMove
  right; right
  apply simplicial_iso_refl
  have t_nonsingleton : t.card > 1 :=
  by
    rw [Finset.nonempty_coe_sort, Finset.nonempty_iff_ne_empty, ne_eq, ← Finset.card_eq_zero] at t_ne
    omega
  have g_inj : Set.InjOn g.map Y.vertices :=
  by
    apply @Set.InjOn.mono _ _ Y.vertices (Y.vertices ∪ {y})
    apply Set.subset_union_left
    rw [← @stellar_subdiv_vertices _ 𝕜 _ _ _ _ _ Y t _ y t_in_Y y_nin_Y t_nonsingleton]
    apply iso_is_injective_vertices g g_iso
  let g_coe : SimplicialCoe Y F := SimplicialCoe.mk g.map g_inj
  have gy_nin_gY : g.map y ∉ (g_coe.coe ''ˢ Y).vertices :=
  by
    by_cases gy_in_Y : g.map y ∈ (g_coe.coe ''ˢ Y).vertices
    rw [simplicialImage_vertices] at gy_in_Y
    have contra : y ∈ Y.vertices :=
    by
      apply Set.InjOn.mem_of_mem_image
      apply iso_is_injective_vertices g g_iso
      rw [stellar_subdiv_vertices Y t y t_in_Y y_nin_Y t_nonsingleton]
      apply Set.subset_union_left
      apply barycenter_vertex_stellar_subdiv
      assumption
    contradiction
    assumption
  let φ := @stellarCoeForward _ _ 𝕜 _ _ _ _ _ _ _ Y g_coe t _ y (g.map y) t_in_Y y_nin_Y gy_nin_gY
  have φ_inj : Set.InjOn φ.map (Y.vertices ∪ {y}) :=
  by
    rw [← @stellar_subdiv_vertices _ 𝕜 _ _ _ _ _ Y t _ y t_in_Y y_nin_Y t_nonsingleton]
    apply
      iso_is_injective_vertices φ (stellar_coe_iso Y g_coe t y (g.map y) t_in_Y y_nin_Y gy_nin_gY)
  have φy_nin_φY : φ.map y ∉ (simplicialImage φ.map Y).vertices :=
    by
    by_cases φy_in_Y : φ.map y ∈ (simplicialImage φ.map Y).vertices
    rw [simplicialImage_vertices] at φy_in_Y
    have contra : y ∈ Y.vertices :=
    by
      apply Set.InjOn.mem_of_mem_image
      apply φ_inj
      apply Set.subset_union_left
      rw [Set.mem_union, Set.mem_singleton_iff]
      right; rfl
      assumption
    contradiction
    assumption
  use simplicialImage φ.map Y; constructor
  have φY_inj : Set.InjOn φ.map Y.vertices :=
  by
    apply @Set.InjOn.mono _ _ _ (Y.vertices ∪ {y})
    apply Set.subset_union_left
    assumption
  let φY := SimplicialCoe.mk φ.map φY_inj
  apply simplicial_iso_trans _ (φY.coe ''ˢ Y)
  apply φY.iso_onto_image
  apply simplicial_iso_preserves_equiv
  apply simplicialImage_congr

  rotate_left
  dsimp only
  apply Relation.ReflTransGen.single
  unfold StellarMove
  left
  use Finset.image φ.map t
  have φt_in_φY : Finset.image φ.map t ∈ (simplicialImage φ.map Y).faces :=
  by
    apply map_is_simplicial_onto_image Y φ.map
    assumption
  use φt_in_φY
  have φt_ne : Nonempty ↥(Finset.image φ.map t) :=
    by
    rw [Finset.nonempty_coe_sort] at t_ne ⊢
    apply Finset.Nonempty.image t_ne
  use φt_ne
  use φ.map y
  use φy_nin_φY
  apply simplicial_iso_trans Z σ(Y, t, y; 𝕜, t_in_Y, y_nin_Y)
  assumption
  apply
    simplicial_iso_trans _
      σ(simplicialImage g_coe.coe Y, Finset.image g_coe.coe t, g.map y; 𝕜, by
        apply map_is_simplicial_onto_image; assumption, gy_nin_gY)
  unfold IsSimpliciallyIso
  use φ
  apply stellar_coe_iso
  rw [simplicial_iso_symm]
  apply stellar_coe_image <;> assumption

  simp only [Set.EqOn, implies_true, φY]

theorem barycenter_injective_image
    {X : AbstractSimplicialComplex E}
    {x : E}
    {f : E → F}
  : x ∉ X.vertices → Function.Injective f → f x ∉ (simplicialImage f X).vertices :=
by
  intro x_nin_X f_inj
  by_contra fx_in_X
  rw [simplicialImage_vertices] at fx_in_X
  have contra : x ∈ X.vertices :=
  by
    apply Set.InjOn.mem_of_mem_image
    apply @Function.Injective.injOn _ _ f _ Set.univ
    assumption
    apply Set.subset_univ
    apply Set.mem_univ
    assumption
  contradiction

theorem stellar_subdiv_injective_image_simplices_left
    (X : AbstractSimplicialComplex E)
    (s : Finset E) [s_ne : Nonempty s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (f : E → F)
    (f_inj : Function.Injective f)
  : (simplicialImage f σ(X, s, x; 𝕜, s_in_X, x_nin_X)).faces ⊆
      σ(simplicialImage f X, Finset.image f s, f x; 𝕜,
        by
          apply map_is_simplicial_onto_image
          assumption,
        barycenter_injective_image x_nin_X f_inj).faces :=
by
  rw [Set.subset_def]
  intro t t_in_img
  simp only [simplicialImage, Set.mem_setOf] at t_in_img
  simp only [stellarSubdivision, simplicialUnion, Set.mem_union] at t_in_img ⊢
  choose u u_in_subdiv fu_t using t_in_img
  cases' u_in_subdiv with u_in_star_comp u_in_join
  left
  simp only [starComplement, Set.mem_sep_iff] at u_in_star_comp ⊢
  choose u_in_X s_nss_u using u_in_star_comp
  constructor
  simp only [simplicialImage, Set.mem_setOf]
  use u
  rw [← fu_t]
  revert s_nss_u
  contrapose
  simp only [Classical.not_not, Finset.subset_iff]
  intro fs_ss_fu a a_in_s
  have fa_in_fs : f a ∈ Finset.image f s := by apply Finset.mem_image_of_mem f a_in_s
  specialize fs_ss_fu fa_in_fs
  rw [Function.Injective.mem_finset_image f_inj] at fs_ss_fu
  assumption
  right
  simp only [join_proj_mem, Set.mem_union] at u_in_join ⊢
  choose u' u'_in_join u₁ u₁_in_link u_decomp u_ne using u_in_join

  cases' u'_in_join with u'_in_join u'_empty
  choose u₃ u₃_in_barycenter u₂ u₂_in_bd u'_decomp u'_ne using u'_in_join
  subst u'_decomp
  use Finset.image f (u₃ ∪ u₂); constructor

  left
  use Finset.image f u₃; constructor
  simp only [simplex, Set.mem_diff, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at u₃_in_barycenter ⊢
  cases' u₃_in_barycenter with u₃_eq_x u₃_empty

  rotate_left
  right
  rw [Set.mem_singleton_iff] at u₃_empty ⊢
  rw [u₃_empty]
  apply Finset.image_empty

  rotate_right
  choose u₃_eq_x u₃_ne using u₃_eq_x
  cases' u₃_eq_x with contra u₃_eq_x
  rw [Set.mem_singleton_iff] at u₃_ne
  contradiction

  left
  rw [u₃_eq_x]
  constructor; right
  apply Finset.image_singleton
  rw [Set.mem_singleton_iff, Finset.image_eq_empty]
  simp only [Finset.singleton_ne_empty, not_false_eq_true]

  use Finset.image f u₂; constructor
  simp only [simplexBoundary, Set.mem_union, Set.mem_insert_iff, Set.mem_diff, Finset.mem_coe, Finset.mem_powerset,
    Set.mem_singleton_iff] at u₂_in_bd ⊢
  cases' u₂_in_bd with u₂_in_bd u₂_empty
  left
  choose u₂_ss_s u₂_ne_s using u₂_in_bd
  constructor
  apply Finset.image_subset_image
  assumption
  revert u₂_ne_s
  contrapose
  simp only [Classical.not_not, Finset.ext_iff]
  intro fu₂_eq_fs

  cases' fu₂_eq_fs with fu₂_eq_fs fu₂_empty
  left
  intro a
  specialize fu₂_eq_fs (f a)
  cases' fu₂_eq_fs with fu₂_ss_fs fs_ss_fu₂
  constructor
  intro a_in_u₂
  have fa_in_fu₂ : f a ∈ Finset.image f u₂ := by apply Finset.mem_image_of_mem f a_in_u₂
  specialize fu₂_ss_fs fa_in_fu₂
  rw [Function.Injective.mem_finset_image f_inj] at fu₂_ss_fs
  assumption
  intro a_in_s
  have fa_in_fs : f a ∈ Finset.image f s := by apply Finset.mem_image_of_mem f a_in_s
  specialize fs_ss_fu₂ fa_in_fs
  rw [Function.Injective.mem_finset_image f_inj] at fs_ss_fu₂
  assumption

  right
  intro a
  specialize fu₂_empty (f a)
  cases' fu₂_empty with fu₂_ss_fs fs_ss_fu₂
  constructor
  intro a_in_u₂
  have fa_in_fu₂ : f a ∈ Finset.image f u₂ := by apply Finset.mem_image_of_mem f a_in_u₂
  specialize fu₂_ss_fs fa_in_fu₂
  contradiction
  rw [Function.Injective.mem_finset_image f_inj] at fu₂_ss_fs
  intro a_in_s
  contradiction

  right
  rw [u₂_empty]
  apply Finset.image_empty
  constructor; rw [Finset.image_union]
  rw [ne_eq, Finset.image_eq_empty]
  assumption

  rw [Finset.image_union]
  use Finset.image f u₁; constructor
  simp only [link, Set.mem_sep_iff] at u₁_in_link ⊢

  cases' u₁_in_link with u₁_in_link u₁_empty
  choose u₁_in_X su₁_in_X su₁_disj using u₁_in_link

  left; constructor
  apply map_is_simplicial_onto_image
  assumption

  constructor
  rw [← Finset.image_union]
  apply map_is_simplicial_onto_image
  assumption
  rw [← Finset.image_inter s u₁ f_inj, Finset.image_eq_empty]
  assumption

  right
  rw [Set.mem_singleton_iff] at u₁_empty ⊢
  rw [u₁_empty]
  apply Finset.image_empty

  rw [← Finset.image_union, ← fu_t, u_decomp]
  constructor
  rw [Finset.image_union]
  rw [ne_eq, Finset.image_eq_empty, Finset.union_eq_empty, not_and_or]
  left; assumption

  rw [Set.mem_singleton_iff] at u'_empty u₁_in_link
  subst u'_empty
  rw [Finset.empty_union] at u_decomp
  subst u_decomp
  use ∅; constructor
  right; apply Set.mem_singleton

  cases' u₁_in_link with u₁_in_link u₁_empty
  use Finset.image f u; constructor; left
  simp only [link, Set.mem_setOf] at u₁_in_link ⊢
  choose u_in_X su_in_X su_disj using u₁_in_link
  simp only [simplicialImage, Set.mem_setOf]

  constructor; use u
  constructor; use s ∪ u
  constructor; assumption
  rw [Finset.image_union]
  rw [← Finset.image_inter s u f_inj, Finset.image_eq_empty]
  assumption

  constructor
  rw [Finset.empty_union]
  symm; assumption
  rw [← fu_t, ne_eq, Finset.image_eq_empty]
  assumption

  contradiction

theorem stellar_subdiv_injective_image_simplices_right_ac
    (X : AbstractSimplicialComplex E)
    (s : Finset E) [s_ne : Nonempty s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (f : E → F)
    (f_inj : Function.Injective f)
  :
    ∀ t : Finset F,
      (∃ t₁ t₂ t₃ : Finset F,
          t₁ ∈ Lk(simplicialImage f X, Finset.image f s).faces ∪ {∅} ∧
            t₂ ⊆ Finset.image f s ∧ ¬t₂ = Finset.image f s ∧ ¬t₂ = ∅ ∧
            t₃ = ∅ ∧ t = t₃ ∪ t₂ ∪ t₁) →
        t ∈ (simplicialImage f σ(X, s, x; 𝕜, s_in_X, x_nin_X)).faces :=
by
  intro t t_decomp
  choose t₁ t₂ t₃ t₁_in_link t₂_ss_fs t₂_ne_fs t₂_ne t₃_empty t_decomp using t_decomp
  simp only [simplicialImage, Set.mem_setOf]
  simp only [stellarSubdivision, AbstractSimplicialComplex.instHasUnion, simplicialUnion, Set.mem_union]
  simp only [link, Set.mem_union, Set.mem_sep_iff, simplicialImage, Set.mem_setOf] at t₁_in_link

  cases' t₁_in_link with t₁_in_link t₁_empty
  choose t₁_in_fX fst₁_in_fX fst₁_disj using t₁_in_link
  choose u₁ u₁_in_X fu₁_t₁ using t₁_in_fX
  choose v v_in_X fv_fsu₁ using fst₁_in_fX
  subst fu₁_t₁
  subst t₃_empty

  set u₂ := Finset.image (Function.invFunOn f Set.univ) t₂
  have fu₂_t₂ : Finset.image f u₂ = t₂ :=
  by
    simp only [Finset.ext_iff, Finset.mem_image]
    intro a
    constructor
    intro a_in_img
    choose c c_in_inv fc_a using a_in_img

    rw [Finset.mem_image] at c_in_inv
    choose b b_in_t₂ fb_c using c_in_inv
    rw [← fb_c, @Function.invFunOn_eq _ _ Set.univ f] at fc_a
    rw [← fc_a]
    assumption
    simp only [Finset.subset_iff, Finset.mem_image] at t₂_ss_fs
    specialize t₂_ss_fs b_in_t₂
    choose d d_in_s fd_b using t₂_ss_fs
    use d; constructor; apply Set.mem_univ
    assumption
    intro a_in_t₂
    simp only [Finset.subset_iff, Finset.mem_image] at t₂_ss_fs
    specialize t₂_ss_fs a_in_t₂
    choose b b_in_s fb_a using t₂_ss_fs
    use b; constructor
    rw [Finset.mem_image]
    use a; constructor; assumption
    rw [← fb_a]
    apply Set.InjOn.leftInvOn_invFunOn
    apply Function.Injective.injOn f_inj
    apply Set.mem_univ
    assumption

  use ∅ ∪ u₂ ∪ u₁; constructor; right
  simp only [join_proj_mem]
  use ∅ ∪ u₂; constructor

  simp only [Set.mem_union, join_proj_mem]
  by_cases u₂_empty : u₂ = ∅
  right; rw [u₂_empty, Finset.union_empty]
  apply Set.mem_singleton

  left; use ∅; constructor
  right; apply Set.mem_singleton
  use u₂; constructor
  simp only [simplexBoundary, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe,
    Set.mem_insert_iff, Finset.mem_powerset, not_or]
  left; constructor
  rw [Finset.subset_iff] at t₂_ss_fs ⊢
  intro a a_in_u₂
  have fa_in_t₂ : f a ∈ t₂ :=
  by
    rw [Finset.mem_image] at a_in_u₂
    choose b b_in_t₂ fb_a using a_in_u₂
    rw [← fb_a, @Function.invFunOn_eq _ _ Set.univ f]
    assumption
    specialize t₂_ss_fs b_in_t₂
    rw [Finset.mem_image] at t₂_ss_fs
    choose c c_in_s fc_b using t₂_ss_fs
    use c; constructor; apply Set.mem_univ
    assumption
  specialize t₂_ss_fs fa_in_t₂
  rw [Function.Injective.mem_finset_image f_inj] at t₂_ss_fs
  assumption
  revert t₂_ne_fs
  contrapose
  simp only [not_and_or, Classical.not_not, Finset.ext_iff]

  intro u₂_eq_s b
  constructor
  intro b_in_t₂

  cases' u₂_eq_s with u₂_eq_s u₂_empty
  specialize u₂_eq_s ((Function.invFunOn f Set.univ) b)
  cases' u₂_eq_s with u₂_ss_s s_ss_u₂
  have fb_in_u₂ : (Function.invFunOn f Set.univ) b ∈ u₂ := by
    apply Finset.mem_image_of_mem (Function.invFunOn f Set.univ) b_in_t₂
  specialize u₂_ss_s fb_in_u₂
  rw [Finset.mem_image]
  use(Function.invFunOn f Set.univ) b; constructor
  assumption
  rw [@Function.invFunOn_eq _ _ Set.univ f]
  simp only [Finset.subset_iff, Finset.mem_image] at t₂_ss_fs
  specialize t₂_ss_fs b_in_t₂
  choose c c_in_s fc_b using t₂_ss_fs
  use c; constructor; apply Set.mem_univ
  assumption

  rw [← Finset.ext_iff] at u₂_empty
  contradiction

  intro b_in_fs
  rw [Finset.mem_image] at b_in_fs
  choose a a_in_s fa_b using b_in_fs

  cases' u₂_eq_s with u₂_eq_s u₂_empty
  specialize u₂_eq_s a
  cases' u₂_eq_s with u₂_ss_s s_ss_u₂
  specialize s_ss_u₂ a_in_s
  rw [Finset.mem_image] at s_ss_u₂
  choose c c_in_t₂ fc_a using s_ss_u₂
  rw [← fc_a] at fa_b
  rw [@Function.invFunOn_eq _ _ Set.univ f] at fa_b
  rw [← fa_b]
  assumption
  simp only [Finset.subset_iff, Finset.mem_image] at t₂_ss_fs
  specialize t₂_ss_fs c_in_t₂
  choose d d_in_s fd_c using t₂_ss_fs
  use d; constructor; apply Set.mem_univ
  assumption

  rw [← Finset.ext_iff] at u₂_empty
  contradiction

  constructor; rfl
  rw [Finset.empty_union]
  assumption

  use u₁; constructor
  simp only [link, Set.mem_sep_iff, Set.mem_union]
  left; constructor; assumption
  constructor
  have v_su₁ : v = s ∪ u₁ :=
  by
    rw [← Finset.image_union] at fv_fsu₁
    rw [Finset.ext_iff] at fv_fsu₁ ⊢
    intro a
    specialize fv_fsu₁ (f a)
    cases' fv_fsu₁ with fv_ss_fsu₁ fsu₁_ss_fv
    constructor
    intro a_in_v
    specialize fv_ss_fsu₁ (by apply Finset.mem_image_of_mem f a_in_v)
    rw [Function.Injective.mem_finset_image f_inj] at fv_ss_fsu₁
    assumption
    intro a_in_su₁
    specialize fsu₁_ss_fv (by apply Finset.mem_image_of_mem f a_in_su₁)
    rw [Function.Injective.mem_finset_image f_inj] at fsu₁_ss_fv
    assumption
  rw [v_su₁] at v_in_X
  assumption
  rw [← Finset.image_inter s u₁ f_inj, Finset.image_eq_empty] at fst₁_disj
  assumption

  constructor; rfl
  rw [Finset.empty_union, ne_eq, Finset.union_eq_empty, not_and_or]
  right; apply face_nonempty X u₁ u₁_in_X

  simp only [Finset.image_union, fu₂_t₂, Finset.image_empty]
  symm
  assumption

  set u₂ := Finset.image (Function.invFunOn f Set.univ) t₂
  have fu₂_t₂ : Finset.image f u₂ = t₂ :=
  by
    simp only [Finset.ext_iff, Finset.mem_image]
    intro a
    constructor
    intro a_in_img
    choose c c_in_inv fc_a using a_in_img

    rw [Finset.mem_image] at c_in_inv
    choose b b_in_t₂ fb_c using c_in_inv
    rw [← fb_c, @Function.invFunOn_eq _ _ Set.univ f] at fc_a
    rw [← fc_a]
    assumption
    simp only [Finset.subset_iff, Finset.mem_image] at t₂_ss_fs
    specialize t₂_ss_fs b_in_t₂
    choose d d_in_s fd_b using t₂_ss_fs
    use d; constructor; apply Set.mem_univ
    assumption
    intro a_in_t₂
    simp only [Finset.subset_iff, Finset.mem_image] at t₂_ss_fs
    specialize t₂_ss_fs a_in_t₂
    choose b b_in_s fb_a using t₂_ss_fs
    use b; constructor
    rw [Finset.mem_image]
    use a; constructor; assumption
    rw [← fb_a]
    apply Set.InjOn.leftInvOn_invFunOn
    apply Function.Injective.injOn f_inj
    apply Set.mem_univ
    assumption

  use u₂; constructor; right
  rw [join_proj_mem]
  use u₂; constructor
  simp only [Set.mem_union, join_proj_mem]
  left; use ∅; constructor
  right; apply Set.mem_singleton
  use u₂; constructor; left
  rw [simplexBoundary_mem_iff_subset, Finset.ssubset_def]
  constructor; constructor

  rw [Finset.subset_iff] at t₂_ss_fs ⊢
  intro a a_in_u₂
  have fa_in_t₂ : f a ∈ t₂ :=
  by
    rw [Finset.mem_image] at a_in_u₂
    choose b b_in_t₂ fb_a using a_in_u₂
    rw [← fb_a, @Function.invFunOn_eq _ _ Set.univ f]
    assumption
    specialize t₂_ss_fs b_in_t₂
    rw [Finset.mem_image] at t₂_ss_fs
    choose c c_in_s fc_b using t₂_ss_fs
    use c; constructor; apply Set.mem_univ
    assumption
  specialize t₂_ss_fs fa_in_t₂
  rw [Function.Injective.mem_finset_image f_inj] at t₂_ss_fs
  assumption
  revert t₂_ss_fs
  contrapose
  simp only [not_and_or, not_not]
  intro s_ss_u₂

  have fs_ss_t₂ : Finset.image f s ⊆ t₂ :=
  by
    rw [← fu₂_t₂]
    apply Finset.image_subset_image s_ss_u₂
  by_contra t₂_ss_fs
  have t₂_eq_fs : t₂ = Finset.image f s :=
  by
    rw [Finset.subset_iff] at fs_ss_t₂ t₂_ss_fs
    rw [Finset.ext_iff]
    intro b
    constructor

    intro b_in_t₂
    specialize t₂_ss_fs b_in_t₂
    assumption

    intro b_in_fs
    specialize fs_ss_t₂ b_in_fs
    assumption
  contradiction

  rw [ne_eq, Finset.image_eq_empty]
  assumption

  constructor
  rw [Finset.empty_union]
  rw [ne_eq, Finset.image_eq_empty]
  assumption

  use ∅; constructor
  rw [Set.mem_union]
  right; apply Set.mem_singleton

  constructor
  rw [Finset.union_empty]
  rw [ne_eq, Finset.image_eq_empty]
  assumption

  rw [Set.mem_singleton_iff] at t₁_empty
  subst t₁_empty t₃_empty t_decomp
  rw [Finset.empty_union, Finset.union_empty]
  assumption

theorem stellar_subdiv_injective_image_simplices_right_ad
    (X : AbstractSimplicialComplex E)
    (s : Finset E) [s_ne : Nonempty s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (f : E → F)
    (f_inj : Function.Injective f)
  : ∀ t : Finset F,
      (∃ t₁ t₂ t₃ : Finset F,
          t₁ ∈ Lk(simplicialImage f X, Finset.image f s).faces ∪ {∅} ∧
            t₂ ⊆ Finset.image f s ∧ ¬t₂ = Finset.image f s ∧ ¬t₂ = ∅ ∧
            t₃ = {f x} ∧ t = t₃ ∪ t₂ ∪ t₁) →
        t ∈ (simplicialImage f σ(X, s, x; 𝕜, s_in_X, x_nin_X)).faces :=
by
  intro t t_decomp
  choose t₁ t₂ t₃ t₁_in_link t₂_ss_fs t₂_ne_fs t₂_ne t₃_eq_fx t_decomp using t_decomp
  simp only [simplicialImage, Set.mem_setOf]
  simp only [stellarSubdivision, AbstractSimplicialComplex.instHasUnion, simplicialUnion, Set.mem_union]
  simp only [link, Set.mem_union, Set.mem_sep_iff, simplicialImage, Set.mem_setOf] at t₁_in_link
  cases' t₁_in_link with t₁_in_link t₁_empty

  choose t₁_in_fX fst₁_in_fX fst₁_disj using t₁_in_link
  choose u₁ u₁_in_X fu₁_t₁ using t₁_in_fX
  choose v v_in_X fv_fsu₁ using fst₁_in_fX
  subst fu₁_t₁
  subst t₃_eq_fx

  set u₂ := Finset.image (Function.invFunOn f Set.univ) t₂
  use {x} ∪ u₂ ∪ u₁; constructor; right
  simp only [join_proj_mem]
  use {x} ∪ u₂; constructor

  rw [Set.mem_union, join_proj_mem]
  left; use {x}; constructor
  simp only [simplex, Set.mem_union, Set.mem_diff, Finset.mem_coe]
  left; constructor
  apply Finset.mem_powerset_self
  rw [Set.mem_singleton_iff]
  apply Finset.singleton_ne_empty

  use u₂; constructor
  simp only [simplexBoundary, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe,
    Set.mem_insert_iff, not_or, Finset.mem_powerset]

  by_cases u₂_empty : u₂ = ∅
  right; assumption

  left; constructor
  rw [Finset.subset_iff] at t₂_ss_fs ⊢
  intro a a_in_u₂
  have fa_in_t₂ : f a ∈ t₂ :=
  by
    rw [Finset.mem_image] at a_in_u₂
    choose b b_in_t₂ fb_a using a_in_u₂
    rw [← fb_a, @Function.invFunOn_eq _ _ Set.univ f]
    assumption
    specialize t₂_ss_fs b_in_t₂
    rw [Finset.mem_image] at t₂_ss_fs
    choose c c_in_s fc_b using t₂_ss_fs
    use c; constructor; apply Set.mem_univ
    assumption
  specialize t₂_ss_fs fa_in_t₂
  rw [Function.Injective.mem_finset_image f_inj] at t₂_ss_fs
  assumption

  constructor
  revert t₂_ne_fs
  contrapose
  simp only [Classical.not_not, Finset.ext_iff]
  intro u₂_eq_s b
  constructor
  intro b_in_t₂
  specialize u₂_eq_s ((Function.invFunOn f Set.univ) b)
  cases' u₂_eq_s with u₂_ss_s s_ss_u₂
  have fb_in_u₂ : (Function.invFunOn f Set.univ) b ∈ u₂ := by
    apply Finset.mem_image_of_mem (Function.invFunOn f Set.univ) b_in_t₂
  specialize u₂_ss_s fb_in_u₂
  rw [Finset.mem_image]
  use(Function.invFunOn f Set.univ) b; constructor
  assumption
  rw [@Function.invFunOn_eq _ _ Set.univ f]
  simp only [Finset.subset_iff, Finset.mem_image] at t₂_ss_fs
  specialize t₂_ss_fs b_in_t₂
  choose c c_in_s fc_b using t₂_ss_fs
  use c; constructor; apply Set.mem_univ
  assumption
  intro b_in_fs
  rw [Finset.mem_image] at b_in_fs
  choose a a_in_s fa_b using b_in_fs
  specialize u₂_eq_s a
  cases' u₂_eq_s with u₂_ss_s s_ss_u₂
  specialize s_ss_u₂ a_in_s
  rw [Finset.mem_image] at s_ss_u₂
  choose c c_in_t₂ fc_a using s_ss_u₂
  rw [← fc_a] at fa_b
  rw [@Function.invFunOn_eq _ _ Set.univ f] at fa_b
  rw [← fa_b]
  assumption
  simp only [Finset.subset_iff, Finset.mem_image] at t₂_ss_fs
  specialize t₂_ss_fs c_in_t₂
  choose d d_in_s fd_c using t₂_ss_fs
  use d; constructor; apply Set.mem_univ
  assumption

  assumption

  constructor; rfl
  rw [ne_eq, Finset.union_eq_empty, not_and_or]
  left; apply Finset.singleton_ne_empty

  use u₁; constructor
  simp only [link, Set.mem_union, Set.mem_sep_iff]
  left; constructor; assumption
  constructor
  have v_su₁ : v = s ∪ u₁ :=
  by
    rw [← Finset.image_union] at fv_fsu₁
    rw [Finset.ext_iff] at fv_fsu₁ ⊢
    intro a
    specialize fv_fsu₁ (f a)
    cases' fv_fsu₁ with fv_ss_fsu₁ fsu₁_ss_fv
    constructor
    intro a_in_v
    specialize fv_ss_fsu₁ (by apply Finset.mem_image_of_mem f a_in_v)
    rw [Function.Injective.mem_finset_image f_inj] at fv_ss_fsu₁
    assumption
    intro a_in_su₁
    specialize fsu₁_ss_fv (by apply Finset.mem_image_of_mem f a_in_su₁)
    rw [Function.Injective.mem_finset_image f_inj] at fsu₁_ss_fv
    assumption
  rw [v_su₁] at v_in_X
  assumption
  rw [← Finset.image_inter s u₁ f_inj, Finset.image_eq_empty] at fst₁_disj
  assumption

  constructor; rfl
  simp only [ne_eq, Finset.union_eq_empty, not_and_or]
  left; left; apply Finset.singleton_ne_empty

  simp only [Finset.image_union]
  have fu₂_t₂ : Finset.image f u₂ = t₂ :=
  by
    simp only [Finset.ext_iff, Finset.mem_image]
    intro a
    constructor
    intro a_in_img
    choose c c_in_inv fc_a using a_in_img
    rw [Finset.mem_image] at c_in_inv
    choose b b_in_t₂ fb_c using c_in_inv
    rw [← fb_c, @Function.invFunOn_eq _ _ Set.univ f] at fc_a
    rw [← fc_a]
    assumption
    simp only [Finset.subset_iff, Finset.mem_image] at t₂_ss_fs
    specialize t₂_ss_fs b_in_t₂
    choose d d_in_s fd_b using t₂_ss_fs
    use d; constructor; apply Set.mem_univ
    assumption
    intro a_in_t₂
    simp only [Finset.subset_iff, Finset.mem_image] at t₂_ss_fs
    specialize t₂_ss_fs a_in_t₂
    choose b b_in_s fb_a using t₂_ss_fs
    use b; constructor
    rw [Finset.mem_image]
    use a; constructor; assumption
    rw [← fb_a]
    apply Set.InjOn.leftInvOn_invFunOn
    apply Function.Injective.injOn f_inj
    apply Set.mem_univ
    assumption
  rw [fu₂_t₂, Finset.image_singleton]
  symm
  assumption

  set u₂ := Finset.image (Function.invFunOn f Set.univ) t₂
  have fu₂_t₂ : Finset.image f u₂ = t₂ :=
  by
    simp only [Finset.ext_iff, Finset.mem_image]
    intro a
    constructor
    intro a_in_img
    choose c c_in_inv fc_a using a_in_img
    rw [Finset.mem_image] at c_in_inv
    choose b b_in_t₂ fb_c using c_in_inv
    rw [← fb_c, @Function.invFunOn_eq _ _ Set.univ f] at fc_a
    rw [← fc_a]
    assumption
    simp only [Finset.subset_iff, Finset.mem_image] at t₂_ss_fs
    specialize t₂_ss_fs b_in_t₂
    choose d d_in_s fd_b using t₂_ss_fs
    use d; constructor; apply Set.mem_univ
    assumption
    intro a_in_t₂
    simp only [Finset.subset_iff, Finset.mem_image] at t₂_ss_fs
    specialize t₂_ss_fs a_in_t₂
    choose b b_in_s fb_a using t₂_ss_fs
    use b; constructor
    rw [Finset.mem_image]
    use a; constructor; assumption
    rw [← fb_a]
    apply Set.InjOn.leftInvOn_invFunOn
    apply Function.Injective.injOn f_inj
    apply Set.mem_univ
    assumption

  use {x} ∪ u₂; constructor; right
  simp only [join_proj_mem, Set.mem_union]
  use {x} ∪ u₂; constructor; left
  use {x}; constructor; left
  simp only [simplex, Set.mem_diff, Finset.mem_coe]
  constructor; apply Finset.mem_powerset_self
  rw [Set.mem_singleton_iff, ← ne_eq]
  apply Finset.singleton_ne_empty

  use u₂; constructor; left
  rw [simplexBoundary_mem_iff_subset, Finset.ssubset_iff_subset_ne]
  constructor; constructor

  rw [Finset.subset_iff] at t₂_ss_fs ⊢
  intro a a_in_u₂
  have fa_in_t₂ : f a ∈ t₂ :=
  by
    rw [Finset.mem_image] at a_in_u₂
    choose b b_in_t₂ fb_a using a_in_u₂
    rw [← fb_a, @Function.invFunOn_eq _ _ Set.univ f]
    assumption
    specialize t₂_ss_fs b_in_t₂
    rw [Finset.mem_image] at t₂_ss_fs
    choose c c_in_s fc_b using t₂_ss_fs
    use c; constructor; apply Set.mem_univ
    assumption
  specialize t₂_ss_fs fa_in_t₂
  rw [Function.Injective.mem_finset_image f_inj] at t₂_ss_fs
  assumption
  revert t₂_ss_fs
  contrapose
  simp only [not_and_or, not_not]
  intro s_ss_u₂

  have fs_ss_t₂ : Finset.image f s ⊆ t₂ :=
  by
    rw [← fu₂_t₂]
    apply Finset.image_subset_image
    apply Finset.subset_of_eq
    symm; assumption
  by_contra t₂_ss_fs
  have t₂_eq_fs : t₂ = Finset.image f s :=
  by
    rw [Finset.subset_iff] at fs_ss_t₂ t₂_ss_fs
    rw [Finset.ext_iff]
    intro b
    constructor

    intro b_in_t₂
    specialize t₂_ss_fs b_in_t₂
    assumption

    intro b_in_fs
    specialize fs_ss_t₂ b_in_fs
    assumption
  contradiction

  rw [ne_eq, Finset.image_eq_empty]
  assumption

  constructor; rfl
  rw [ne_eq, Finset.union_eq_empty, not_and_or]
  left; apply Finset.singleton_ne_empty

  use ∅; constructor
  right; apply Set.mem_singleton
  constructor
  rw [Finset.union_empty]
  rw [ne_eq, Finset.union_eq_empty, not_and_or]
  left; apply Finset.singleton_ne_empty

  rw [Finset.image_union, Finset.image_singleton]
  rw [Set.mem_singleton_iff] at t₁_empty
  subst t₁_empty
  rw [Finset.union_empty] at t_decomp
  rw [← t₃_eq_fx, fu₂_t₂, t_decomp]

theorem stellar_subdiv_injective_image_simplices_right_bc
    (X : AbstractSimplicialComplex E)
    (s : Finset E) [s_ne : Nonempty s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (f : E → F)
    (f_inj : Function.Injective f)
  : ∀ t : Finset F,
      (∃ t₁ t₂ t₃ : Finset F,
          t₁ ∈ Lk(simplicialImage f X, Finset.image f s).faces ∧
            t₂ = ∅ ∧ t₃ = ∅ ∧ t = t₃ ∪ t₂ ∪ t₁) →
        t ∈ (simplicialImage f σ(X, s, x; 𝕜, s_in_X, x_nin_X)).faces :=
by
  intro t t_decomp
  choose t₁ t₂ t₃ t₁_in_link t₂_empty t₃_empty t_decomp using t_decomp
  simp only [simplicialImage, Set.mem_setOf]
  simp only [stellarSubdivision, simplicialUnion, Set.mem_union]
  simp only [link, Set.mem_union, Set.mem_sep_iff, simplicialImage, Set.mem_setOf] at t₁_in_link

  choose t₁_in_fX fst₁_in_fX fst₁_disj using t₁_in_link
  choose u₁ u₁_in_X fu₁_t₁ using t₁_in_fX
  choose v v_in_X fv_fsu₁ using fst₁_in_fX
  subst fu₁_t₁
  use ∅ ∪ ∅ ∪ u₁; constructor; right
  simp only [join_proj_mem]
  use ∅ ∪ ∅; constructor

  simp only [Set.mem_union]
  right; rw [Finset.empty_union]; apply Set.mem_singleton

  use u₁; constructor
  simp only [link, Set.mem_union, Set.mem_sep_iff]
  left; constructor; assumption
  constructor
  have v_su₁ : v = s ∪ u₁ :=
  by
    rw [← Finset.image_union] at fv_fsu₁
    rw [Finset.ext_iff] at fv_fsu₁ ⊢
    intro a
    specialize fv_fsu₁ (f a)
    cases' fv_fsu₁ with fv_ss_fsu₁ fsu₁_ss_fv
    constructor
    intro a_in_v
    specialize fv_ss_fsu₁ (by apply Finset.mem_image_of_mem f a_in_v)
    rw [Function.Injective.mem_finset_image f_inj] at fv_ss_fsu₁
    assumption
    intro a_in_su₁
    specialize fsu₁_ss_fv (by apply Finset.mem_image_of_mem f a_in_su₁)
    rw [Function.Injective.mem_finset_image f_inj] at fsu₁_ss_fv
    assumption
  rw [v_su₁] at v_in_X
  assumption
  rw [← Finset.image_inter s u₁ f_inj, Finset.image_eq_empty] at fst₁_disj
  assumption

  constructor; rfl
  simp only [Finset.empty_union]
  apply face_nonempty X u₁ u₁_in_X

  simp only [Finset.image_union, Finset.image_singleton, Finset.image_empty]
  subst t₃_empty
  subst t₂_empty
  symm
  assumption

theorem stellar_subdiv_injective_image_simplices_right_bd
    (X : AbstractSimplicialComplex E)
    (s : Finset E) [s_ne : Nonempty s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (f : E → F)
    (f_inj : Function.Injective f)
  : ∀ t : Finset F,
      (∃ t₁ t₂ t₃ : Finset F,
          t₁ ∈ Lk(simplicialImage f X, Finset.image f s).faces ∪ {∅} ∧
            t₂ = ∅ ∧ t₃ = {f x} ∧ t = t₃ ∪ t₂ ∪ t₁) →
        t ∈ (simplicialImage f σ(X, s, x; 𝕜, s_in_X, x_nin_X)).faces :=
by
  intro t t_decomp
  choose t₁ t₂ t₃ t₁_in_link t₂_empty t₃_eq_fx t_decomp using t_decomp
  simp only [simplicialImage, Set.mem_setOf]
  simp only [stellarSubdivision, AbstractSimplicialComplex.instHasUnion, simplicialUnion, Set.mem_union]
  simp only [link, Set.mem_union, Set.mem_sep_iff, simplicialImage, Set.mem_setOf] at t₁_in_link
  cases' t₁_in_link with t₁_in_link t₁_empty

  choose t₁_in_fX fst₁_in_fX fst₁_disj using t₁_in_link
  choose u₁ u₁_in_X fu₁_t₁ using t₁_in_fX
  choose v v_in_X fv_fsu₁ using fst₁_in_fX
  subst fu₁_t₁
  use {x} ∪ ∅ ∪ u₁; constructor; right
  simp only [join_proj_mem]
  use {x} ∪ ∅; constructor

  simp only [Set.mem_union, join_proj_mem]
  left; use {x}; constructor

  simp only [simplex, Set.mem_diff, Finset.mem_coe]
  left; constructor; apply Finset.mem_powerset_self
  rw [Set.mem_singleton_iff]
  apply Finset.singleton_ne_empty

  use ∅; constructor
  right; apply Set.mem_singleton

  constructor; rfl
  rw [Finset.union_empty]
  apply Finset.singleton_ne_empty

  use u₁; constructor
  simp only [link, Set.mem_union, Set.mem_sep_iff]
  left; constructor; assumption
  constructor
  have v_su₁ : v = s ∪ u₁ :=
  by
    rw [← Finset.image_union] at fv_fsu₁
    rw [Finset.ext_iff] at fv_fsu₁ ⊢
    intro a
    specialize fv_fsu₁ (f a)
    cases' fv_fsu₁ with fv_ss_fsu₁ fsu₁_ss_fv
    constructor
    intro a_in_v
    specialize fv_ss_fsu₁ (by apply Finset.mem_image_of_mem f a_in_v)
    rw [Function.Injective.mem_finset_image f_inj] at fv_ss_fsu₁
    assumption
    intro a_in_su₁
    specialize fsu₁_ss_fv (by apply Finset.mem_image_of_mem f a_in_su₁)
    rw [Function.Injective.mem_finset_image f_inj] at fsu₁_ss_fv
    assumption
  rw [v_su₁] at v_in_X
  assumption
  rw [← Finset.image_inter s u₁ f_inj, Finset.image_eq_empty] at fst₁_disj
  assumption

  constructor; rfl
  rw [Finset.union_empty, ne_eq, Finset.union_eq_empty, not_and_or]
  left; apply Finset.singleton_ne_empty

  simp only [Finset.image_union, Finset.image_singleton, Finset.image_empty, ← t₃_eq_fx, ← t₂_empty]
  symm
  assumption

  use {x}; constructor; right
  rw [join_proj_mem]
  use {x}; constructor
  rw [Set.mem_union, join_proj_mem]
  left; use {x}; constructor
  simp only [Set.mem_union, simplex, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe]
  left; constructor
  apply Finset.mem_powerset_self
  apply Finset.singleton_ne_empty

  use ∅; constructor
  rw [Set.mem_union]
  right; apply Set.mem_singleton

  constructor
  rw [Finset.union_empty]
  apply Finset.singleton_ne_empty

  use ∅; constructor
  rw [Set.mem_union]
  right; apply Set.mem_singleton

  constructor
  rw [Finset.union_empty]
  apply Finset.singleton_ne_empty

  rw [Finset.image_singleton]
  rw [Set.mem_singleton_iff] at t₁_empty
  subst t₁_empty t₂_empty t₃_eq_fx t_decomp
  simp only [Finset.union_empty]

theorem stellar_subdiv_injective_image_simplices_right
    (X : AbstractSimplicialComplex E)
    (s : Finset E) [s_ne : Nonempty s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (f : E → F)
    (f_inj : Function.Injective f)
  : σ(simplicialImage f X, Finset.image f s, f x; 𝕜,
        by
          apply map_is_simplicial_onto_image
          assumption,
        barycenter_injective_image x_nin_X f_inj).faces ⊆
      (simplicialImage f σ(X, s, x; 𝕜, s_in_X, x_nin_X)).faces :=
by
  rw [Set.subset_def]
  intro t t_in_subdiv
  simp only [stellarSubdivision, simplicialUnion, Set.mem_union] at t_in_subdiv
  cases' t_in_subdiv with t_in_star_comp t_in_join
  simp only [starComplement, Set.mem_sep_iff, simplicialImage, Set.mem_setOf] at t_in_star_comp
  choose t_in_fX fs_nss_t using t_in_star_comp
  choose u u_in_X fu_t using t_in_fX
  use u; constructor; left
  simp only [starComplement, Set.mem_sep_iff]
  constructor; assumption
  revert fs_nss_t
  contrapose
  simp only [Classical.not_not, ← fu_t]
  apply Finset.image_subset_image
  assumption
  simp only [join_proj_mem] at t_in_join ⊢
  choose t' t'_in_join t₁ t₁_in_link t_decomp t_ne using t_in_join

  rw [Set.mem_union, join_proj_mem] at t'_in_join
  cases' t'_in_join with t'_in_join t'_empty

  choose t₃ t₃_in_barycenter t₂ t₂_in_bd t'_decomp t'_ne using t'_in_join
  subst t'_decomp
  simp only [simplexBoundary, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe,
    Finset.mem_powerset] at t₂_in_bd
  simp only [simplex, Set.mem_union, Set.mem_diff, Finset.mem_coe, Finset.mem_powerset,
    Finset.subset_singleton_iff, Set.mem_singleton_iff] at t₃_in_barycenter
  cases' t₂_in_bd with t₂_in_bd t₂_empty <;>

  -- Cases A, B resp.
  cases' t₃_in_barycenter with t₃_eq_x t₃_empty
  rotate_left

  -- Cases C, D resp.
  choose t₂_ss_fs t₂_ne_fs using t₂_in_bd
  apply stellar_subdiv_injective_image_simplices_right_ac
  assumption

  use t₁; use t₂; use t₃
  rw [Set.mem_insert_iff, not_or] at t₂_ne_fs
  choose t₂_ne_fs t₂_ne using t₂_ne_fs
  constructor; assumption
  constructor; assumption
  constructor; assumption
  constructor; assumption
  constructor; assumption
  assumption

  apply stellar_subdiv_injective_image_simplices_right_bd
  assumption

  use t₁; use t₂; use t₃
  choose t₃_eq_x t₃_ne using t₃_eq_x
  cases' t₃_eq_x with contra t₃_eq_x
  contradiction
  constructor; assumption
  constructor; assumption
  constructor; assumption
  assumption

  apply stellar_subdiv_injective_image_simplices_right_bc
  assumption

  use t₁; use t₂; use t₃
  rw [Set.mem_union] at t₁_in_link
  cases' t₁_in_link with t₁_in_link t₁_empty

  constructor; assumption
  constructor; assumption
  constructor; assumption
  assumption

  rw [Set.mem_singleton_iff] at t₁_empty
  subst t₁_empty t₂_empty t₃_empty
  simp only [Finset.union_empty] at t_decomp
  contradiction

  apply stellar_subdiv_injective_image_simplices_right_bc
  assumption
  use t₁; use ∅; use ∅
  rw [Set.mem_union] at t₁_in_link
  cases' t₁_in_link with t₁_in_link t₁_empty

  constructor; assumption
  constructor; rfl
  constructor; rfl
  rw [Set.mem_singleton_iff] at t'_empty
  subst t'_empty
  simp only [Finset.empty_union] at t_decomp ⊢
  assumption

  rw [Set.mem_singleton_iff] at t'_empty t₁_empty
  subst t'_empty t₁_empty
  rw [Finset.empty_union] at t_decomp
  contradiction

  apply stellar_subdiv_injective_image_simplices_right_ad
  assumption

  use t₁; use t₂; use t₃
  choose t₂_ss_fs t₂_ne_s using t₂_in_bd
  rw [Set.mem_insert_iff, not_or] at t₂_ne_s
  choose t₂_ne_s t₂_ne using t₂_ne_s
  constructor; assumption
  constructor; assumption
  constructor; assumption
  choose t₃_eq_x t₃_ne using t₃_eq_x
  cases' t₃_eq_x with contra t₃_eq_x
  contradiction
  constructor; assumption
  constructor; assumption
  assumption

theorem stellar_subdiv_injective_image_simplices
    (X : AbstractSimplicialComplex E)
    (s : Finset E) [s_ne : Nonempty s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (f : E → F)
    (f_inj : Function.Injective f)
  : (simplicialImage f σ(X, s, x; 𝕜, s_in_X, x_nin_X)).faces =
      σ(simplicialImage f X, Finset.image f s, f x; 𝕜,
          by
            apply map_is_simplicial_onto_image
            assumption,
          barycenter_injective_image x_nin_X f_inj).faces :=
by
  rw [Set.Subset.antisymm_iff]
  constructor
  apply stellar_subdiv_injective_image_simplices_left
  assumption
  apply stellar_subdiv_injective_image_simplices_right
  assumption

theorem stellar_subdiv_injective_image
    (X : AbstractSimplicialComplex E)
    (s : Finset E) [s_ne : Nonempty s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (f : E → F)
    (f_inj : Function.Injective f)
  : simplicialImage f σ(X, s, x; 𝕜, s_in_X, x_nin_X) ≅
      σ(simplicialImage f X, Finset.image f s, f x; 𝕜,
          by
            apply map_is_simplicial_onto_image
            assumption,
          barycenter_injective_image x_nin_X f_inj) :=
by
  apply simplicial_iso_preserves_equiv
  apply stellar_subdiv_injective_image_simplices
  assumption

theorem stellar_subdiv_exists_iso
    (X Y : AbstractSimplicialComplex E)
    (Z : AbstractSimplicialComplex F)
    (s : Finset E) [s_ne : Nonempty s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (τ : E → F)
    (τ_inj : Function.Injective τ)
  : (X ≅ Z) → Y ≅ σ(X, s, x; 𝕜, s_in_X, x_nin_X) →
      ∃ W : AbstractSimplicialComplex F, (Y ≅ W) ∧ Z ≅ₛₜ[𝕜] W :=
by
  intro X_iso_Z X_subdiv_Y
  have τ_inj_subdiv : Set.InjOn τ σ(X, s, x; 𝕜, s_in_X, x_nin_X).vertices :=
  by
    apply Set.injOn_of_injective τ_inj
  let τσ := SimplicialCoe.mk τ τ_inj_subdiv
  have τ_inj_X : Set.InjOn τ X.vertices := by apply Set.injOn_of_injective τ_inj
  let τX := SimplicialCoe.mk τ τ_inj_X
  use τσ.coe ''ˢ σ(X, s, x; 𝕜, s_in_X, x_nin_X); constructor
  apply simplicial_iso_trans _ σ(X, s, x; 𝕜, s_in_X, x_nin_X)
  assumption
  apply τσ.iso_onto_image
  have τX_iso_Z : Z ≅ τX.coe ''ˢ X :=
  by
    apply simplicial_iso_trans _ X
    rw [simplicial_iso_symm]
    assumption
    apply τX.iso_onto_image
  apply @Relation.ReflTransGen.tail _ _ _ (τX.coe ''ˢ X)
  apply Relation.ReflTransGen.single
  right; right
  assumption
  right; left
  use Finset.image τX.coe s
  have τs_in_img : Finset.image τX.coe s ∈ (τX.coe ''ˢ X).faces :=
  by
    apply map_is_simplicial_onto_image X τX.coe
    assumption
  use τs_in_img
  have τs_ne : Nonempty (Finset.image τX.coe s) :=
    by
    rw [Finset.nonempty_coe_sort] at s_ne ⊢
    apply Finset.Nonempty.image s_ne
  use τs_ne
  use τX.coe x
  have τx_nin_τX : τX.coe x ∉ (τX.coe ''ˢ X).vertices :=
  by
    by_cases τx_in_X : τX.coe x ∈ (τX.coe ''ˢ X).vertices
    rw [simplicialImage_vertices] at τx_in_X
    have contra : x ∈ X.vertices :=
    by
      rw [Set.mem_image] at τx_in_X
      choose y y_in_X τy_eq_τx using τx_in_X
      rw [Function.Injective.eq_iff τ_inj] at τy_eq_τx
      rw [τy_eq_τx] at y_in_X
      assumption
    contradiction
    assumption
  use τx_nin_τX
  apply stellar_subdiv_injective_image
  assumption

theorem stellarMove_exists_iso
    (X Y : AbstractSimplicialComplex E)
    (Z : AbstractSimplicialComplex F)
    (f : E → F)
    (f_inj : Function.Injective f)
  : (X ≅ Z) → @StellarMove _ 𝕜 _ _ _ _ _ X Y →
      ∃ W : AbstractSimplicialComplex F, (Y ≅ W) ∧ Z ≅ₛₜ[𝕜] W :=
by
  intro X_iso_Z X_move_Y
  unfold StellarMove at X_move_Y
  cases' X_move_Y with Y_subdiv_X X_move_Y
  choose t t_in_Y t_ne y y_nin_Y Y_subdiv_X using Y_subdiv_X
  apply @stellar_weld_exists_iso _ _ _ _ _ _ _ _ _ _ X Y Z t t_ne y t_in_Y y_nin_Y X_iso_Z Y_subdiv_X
  cases' X_move_Y with X_subdiv_Y X_iso_Y
  choose s s_in_X s_ne x x_nin_X X_subdiv_Y using X_subdiv_Y
  apply
    @stellar_subdiv_exists_iso _ _ _ _ _ _ _ _ _ _ X Y Z s s_ne x s_in_X x_nin_X f f_inj X_iso_Z X_subdiv_Y
  use Z; constructor
  apply simplicial_iso_trans Y X
  rw [simplicial_iso_symm]
  assumption
  assumption
  rfl

theorem stellarEquiv_exists_iso
    (X Y : AbstractSimplicialComplex E)
    (Z : AbstractSimplicialComplex F)
    (f : E → F)
    (f_inj : Function.Injective f)
  : (X ≅ Z) → X ≅ₛₜ[𝕜] Y →
      ∃ W : AbstractSimplicialComplex F, (Y ≅ W) ∧ Z ≅ₛₜ[𝕜] W :=
by
  intro X_iso_Z X_eq_Y
  induction' X_eq_Y with K Y X_eq_K K_move_Y H_ind
  use Z

  choose L K_iso_L Z_eq_L using H_ind
  have Z_move_W : ∃ W : AbstractSimplicialComplex F, (Y ≅ W) ∧ L ≅ₛₜ[𝕜] W :=
  by
    apply stellarMove_exists_iso
    apply f_inj
    apply K_iso_L
    apply K_move_Y
  choose W Y_iso_W L_move_W using Z_move_W
  use W; constructor
  assumption
  apply stellarEquiv_trans Z L
  assumption
  assumption

theorem stellarMove_iso
    (X Y : AbstractSimplicialComplex E)
    (Z W : AbstractSimplicialComplex F)
    (f : E → F)
    (f_inj : Function.Injective f)
  : (X ≅ Z) → (Y ≅ W) → @StellarMove _ 𝕜 _ _ _ _ _ X Y → Z ≅ₛₜ[𝕜] W :=
by
  intro X_iso_Z Y_iso_W X_move_Y
  have Y_iso_L : ∃ L : AbstractSimplicialComplex F, (Y ≅ L) ∧ Z ≅ₛₜ[𝕜] L :=
  by
    apply stellarMove_exists_iso
    apply f_inj
    apply X_iso_Z
    apply X_move_Y
  choose L Y_iso_L Z_eq_L using Y_iso_L
  apply @Relation.ReflTransGen.tail _ _ _ L
  assumption
  right; right
  apply simplicial_iso_trans _ Y
  rw [simplicial_iso_symm]
  assumption
  assumption

theorem stellarEquiv_iso
    (X Y : AbstractSimplicialComplex E)
    (Z W : AbstractSimplicialComplex F)
    (f : E → F)
    (f_inj : Function.Injective f)
  : (X ≅ Z) → (Y ≅ W) → X ≅ₛₜ[𝕜] Y → Z ≅ₛₜ[𝕜] W :=
by
  intro X_iso_Z Y_iso_W X_eq_Y
  induction' X_eq_Y with K Y X_eq_K K_move_Y H_ind
  rw [simplicial_iso_symm] at X_iso_Z
  apply stellarEquiv_preserves_iso
  apply simplicial_iso_trans Z X <;> assumption
  have K_iso_L : ∃ L : AbstractSimplicialComplex F, (K ≅ L) ∧ Z ≅ₛₜ[𝕜] L :=
  by
    apply stellarEquiv_exists_iso
    apply f_inj
    apply X_iso_Z
    apply X_eq_K
  choose L K_iso_L Z_eq_L using K_iso_L
  apply stellarEquiv_trans Z L
  assumption
  apply stellarMove_iso K Y L W <;> assumption

/-
# Properties of Stellar Subdivision
-/
theorem barycenter_join_left
    {X Y : AbstractSimplicialComplex E}
    {x : E}
  :
    x ∉ X.vertices → (x, 0) ∉ (X ⋆ Y : AbstractSimplicialComplex (E × 𝕜)).vertices :=
by
  contrapose
  simp only [Classical.not_not, simplicialJoin_vertices_mem_left]
  exact Set.mem_of_eq_of_mem rfl

theorem stellar_join_distr_join_left
    (X Y : AbstractSimplicialComplex E)
    (s : Finset E) [s_ne : Nonempty s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
  : (((π₁[𝕜] (@barycenter_join_boundary_disjoint_link _ _ 𝕜 _ _ _ _ X s x s_in_X x_nin_X)).coe
      ''ˢ (((π₁[𝕜] (barycenter_disjoint_boundary X s x s_in_X x_nin_X)).coe
        ''ˢ (simplex {x} ⋆ ∂s)) ⋆
          Lk(X, s))) ⋆ Y).faces ⊆
      ((π₁[𝕜] (@barycenter_join_boundary_disjoint_link _ _ 𝕜 _ _ _ _ (X ⋆ Y : AbstractSimplicialComplex (E × 𝕜)) (s ⊔ₛ ∅) (x, 0)
            (by apply simplicialJoin_incl_left; assumption)
            (barycenter_join_left x_nin_X))).coe
        ''ˢ ((π₁[𝕜]
              (barycenter_disjoint_boundary (X ⋆ Y : AbstractSimplicialComplex (E × 𝕜)) (s ⊔ₛ ∅) (x, 0)
                  (by apply simplicialJoin_incl_left; assumption)
                  (barycenter_join_left x_nin_X))).coe
          ''ˢ ((simplex {((x, 0) : E × 𝕜)} ⋆ ∂(s ⊔ₛ ∅)) : AbstractSimplicialComplex ((E × 𝕜) × 𝕜)) ⋆
            (Lk(X ⋆ Y, s ⊔ₛ ∅) : AbstractSimplicialComplex (E × 𝕜)))).faces :=
by
  simp only [Set.subset_def, Set.mem_union, simplicialJoin_mem, join_proj_mem]
  intro t t_in_join
  choose u u_in_join v v_in_Y t_eq_uv using t_in_join
  cases' u_in_join with u_in_join u_empty

  choose u' u'_in_join u₁ u₁_in_link u_decomp u_ne using u_in_join
  cases' u'_in_join with u'_in_join u'_empty

  choose u₃ u₃_in_barycenter u₂ u₂_in_bd u'_decomp u'_ne using u'_in_join
  subst u'_decomp

  cases' u₂_in_bd with u₂_in_bd u₂_empty <;>
  cases' u₃_in_barycenter with u₃_in_barycenter u₃_empty
  choose u₃_in_barycenter u₃_ne using u₃_in_barycenter

  use u₃ ⊔ₛ ∅ ∪ (u₂ ⊔ₛ ∅); constructor; left
  use u₃ ⊔ₛ ∅; constructor; left
  simp only [simplex, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at u₃_in_barycenter ⊢
  constructor; right
  cases' u₃_in_barycenter with u₃_empty u₃_eq_x
  contradiction

  rw [u₃_eq_x]
  simp only [simplexDisjointUnion, Finset.product_singleton, Finset.map_singleton,
    Function.Embedding.coeFn_mk, Finset.map_empty, Finset.union_empty]

  cases' u₃_in_barycenter with u₃_empty u₃_eq_x
  rw [Set.mem_singleton_iff] at u₃_ne
  contradiction

  rw [u₃_eq_x, simplex_disjoint_empty, not_and_or]
  left; apply Finset.singleton_ne_empty

  use u₂ ⊔ₛ ∅; constructor; left
  rw [simplexBoundary_mem_iff_subset, Finset.ssubset_iff_subset_ne, and_assoc] at u₂_in_bd ⊢
  choose u₂_ss_s u₂_ne_s u₂_ne using u₂_in_bd

  simp only [ne_eq, simplex_disjoint_subset_unique, simplex_disjoint_eq_unique, not_and]
  constructor; constructor; assumption; rfl
  constructor; intro contra; contradiction

  rw [simplex_disjoint_empty, not_and_or]
  left; assumption

  constructor; rfl
  simp only [ne_eq, Finset.union_eq_empty, not_and_or, simplex_disjoint_empty]
  left; left
  rw [Set.mem_singleton_iff] at u₃_ne
  assumption

  use u₁ ⊔ₛ v; constructor
  cases' v_in_Y with v_in_Y v_empty <;>
  cases' u₁_in_link with u₁_in_link u₁_empty

  simp only [link, Set.mem_sep_iff] at u₁_in_link ⊢
  choose u₁_in_X su₁_in_X su₁_disj using u₁_in_link
  left; constructor
  rw [simplicialJoin_mem]
  use u₁; constructor
  rw [Set.mem_union]
  left; assumption

  use v; constructor
  rw [Set.mem_union]
  left; assumption

  constructor; rfl
  rw [ne_eq, simplex_disjoint_empty, not_and_or]
  left; apply face_nonempty X u₁ u₁_in_X

  constructor
  rw [simplex_disjoint_distr_union, Finset.empty_union, simplicialJoin_mem]
  use s ∪ u₁; constructor
  rw [Set.mem_union]
  left; assumption

  use v; constructor
  rw [Set.mem_union]
  left; assumption

  constructor; rfl
  rw [ne_eq, simplex_disjoint_empty, not_and_or]
  left; apply face_nonempty X (s ∪ u₁) su₁_in_X

  rw [simplex_disjoint_distr_inter, Finset.empty_inter, su₁_disj]
  simp only [simplexDisjointUnion, Finset.product_singleton, Finset.map_empty, Finset.empty_union]

  left
  rw [Set.mem_singleton_iff] at u₁_empty
  subst u₁_empty
  simp only [link, Set.mem_sep_iff]
  constructor
  apply simplicialJoin_incl_right; assumption
  constructor
  rw [simplex_disjoint_distr_union, Finset.union_empty, Finset.empty_union, simplicialJoin_mem]
  use s; constructor
  rw [Set.mem_union]
  left; assumption
  use v; constructor
  rw [Set.mem_union]
  left; assumption
  constructor; rfl
  rw [ne_eq, simplex_disjoint_empty, not_and_or]
  left; apply face_nonempty X s s_in_X

  rw [simplex_disjoint_distr_inter, Finset.inter_empty, Finset.empty_inter, simplex_disjoint_empty]
  constructor <;> rfl

  left
  simp only [link, Set.mem_sep_iff] at u₁_in_link ⊢
  rw [Set.mem_singleton_iff] at v_empty
  subst v_empty
  choose u₁_in_X su₁_in_X su₁_disj using u₁_in_link
  constructor
  apply simplicialJoin_incl_left; assumption
  constructor
  rw [simplex_disjoint_distr_union, Finset.union_empty]
  apply simplicialJoin_incl_left; assumption
  rw [simplex_disjoint_distr_inter, Finset.inter_empty, simplex_disjoint_empty]
  constructor; assumption; rfl

  right
  rw [Set.mem_singleton_iff] at v_empty u₁_empty ⊢
  subst v_empty u₁_empty
  rw [simplex_disjoint_empty]
  constructor <;> rfl

  simp only [simplex_disjoint_distr_union, Finset.empty_union, ← u_decomp]
  assumption

  use ∅ ⊔ₛ ∅ ∪ (u₂ ⊔ₛ  ∅); constructor; left
  use ∅ ⊔ₛ ∅; constructor; right
  rw [Set.mem_singleton_iff, simplex_disjoint_empty]
  constructor <;> rfl

  use u₂ ⊔ₛ ∅; constructor; left
  simp only [simplexBoundary, Set.mem_diff, Set.mem_insert_iff, Finset.mem_coe, Finset.mem_powerset, not_or, Set.mem_singleton_iff] at u₂_in_bd ⊢
  choose u₂_ss_s u₂_ne_s u₂_ne using u₂_in_bd
  constructor
  rw [simplex_disjoint_subset_unique]
  constructor; assumption; rfl
  constructor
  rw [simplex_disjoint_eq_unique, not_and_or]
  left; assumption
  rw [simplex_disjoint_empty, not_and_or]
  left; assumption

  constructor; rfl
  simp only [simplex_disjoint_distr_union, Finset.empty_union, ne_eq, simplex_disjoint_empty, not_and_or]
  left; apply face_nonempty (∂s) u₂ u₂_in_bd

  use u₁ ⊔ₛ v; constructor
  cases' u₁_in_link with u₁_in_link u₁_empty
  simp only [link, Set.mem_sep_iff] at u₁_in_link ⊢
  choose u₁_in_X su₁_in_X su₁_disj using u₁_in_link
  left; constructor

  cases' v_in_Y with v_in_Y v_empty
  rw [simplicialJoin_mem]
  use u₁; constructor
  rw [Set.mem_union]
  left; assumption
  use v; constructor
  rw [Set.mem_union]
  left; assumption
  constructor; rfl
  rw [ne_eq, simplex_disjoint_empty, not_and_or]
  left; apply face_nonempty X u₁ u₁_in_X

  rw [Set.mem_singleton_iff] at v_empty
  subst v_empty
  apply simplicialJoin_incl_left; assumption
  constructor
  rw [simplex_disjoint_distr_union, Finset.empty_union]

  cases' v_in_Y with v_in_Y v_empty
  rw [simplicialJoin_mem]
  use (s ∪ u₁); constructor
  rw [Set.mem_union]
  left; assumption
  use v; constructor
  rw [Set.mem_union]
  left; assumption
  constructor; rfl
  rw [ne_eq, simplex_disjoint_empty, not_and_or]
  left; apply face_nonempty X (s ∪ u₁) su₁_in_X

  rw [Set.mem_singleton_iff] at v_empty
  subst v_empty
  apply simplicialJoin_incl_left; assumption
  rw [simplex_disjoint_distr_inter, simplex_disjoint_empty]
  constructor; assumption; rfl

  rw [Set.mem_singleton_iff] at u₁_empty
  subst u₁_empty
  cases' v_in_Y with v_in_Y v_empty
  left
  simp only [link, Set.mem_sep_iff]
  constructor
  apply simplicialJoin_incl_right; assumption
  constructor
  rw [simplex_disjoint_distr_union, Finset.empty_union, Finset.union_empty, simplicialJoin_mem]
  use s; constructor
  rw [Set.mem_union]
  left; assumption
  use v; constructor
  rw [Set.mem_union]
  left; assumption
  constructor; rfl
  rw [ne_eq, simplex_disjoint_empty, not_and_or]
  left; apply face_nonempty X s s_in_X
  rw [simplex_disjoint_distr_inter, Finset.inter_empty, Finset.empty_inter, simplex_disjoint_empty]
  constructor <;> rfl

  right
  rw [Set.mem_singleton_iff] at v_empty ⊢
  subst v_empty
  rw [simplex_disjoint_empty]
  constructor <;> rfl

  simp only [simplex_disjoint_distr_union, Finset.empty_union]
  rw [Set.mem_singleton_iff] at u₃_empty
  rw [u₃_empty, Finset.empty_union] at u_decomp
  rw [u_decomp] at t_eq_uv
  assumption

  use u₃ ⊔ₛ ∅; constructor; left
  use u₃ ⊔ₛ ∅; constructor; left
  simp only [simplex, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at u₃_in_barycenter ⊢
  choose u₃_in_barycenter u₃_ne using u₃_in_barycenter
  cases' u₃_in_barycenter with u₃_empty u₃_in_barycenter
  contradiction
  constructor; right
  rw [Finset.eq_singleton_iff_unique_mem] at u₃_in_barycenter ⊢
  choose x_in_u₃ a_eq_x using u₃_in_barycenter
  constructor; rw [simplex_disjoint_mem_left]; assumption
  intro b b_in_u₃
  rw [simplex_disjoint_mem] at b_in_u₃
  cases' b_in_u₃ with b_in_u₃ contra
  choose b1_in_u₃ b2_zero using b_in_u₃
  specialize a_eq_x b.1 b1_in_u₃
  simp only [← a_eq_x, ← b2_zero]

  choose contra b2_one using contra
  contradiction

  rw [simplex_disjoint_empty, not_and_or]
  left; assumption

  use ∅ ⊔ₛ ∅; constructor; right
  rw [Set.mem_singleton_iff, simplex_disjoint_empty]
  constructor <;> rfl

  constructor
  simp only [simplex_disjoint_distr_union, Finset.union_empty]
  rw [ne_eq, simplex_disjoint_empty, not_and_or]
  left; apply face_nonempty (simplex {x}) u₃ u₃_in_barycenter

  use u₁ ⊔ₛ v; constructor
  simp only [link, Set.mem_sep_iff, Set.mem_singleton_iff] at u₁_in_link ⊢
  cases' u₁_in_link with u₁_in_link u₁_empty <;>
  cases' v_in_Y with v_in_Y v_empty

  left
  choose u₁_in_X su₁_in_X su₁_disj using u₁_in_link
  constructor
  rw [simplicialJoin_mem]
  use u₁; constructor
  rw [Set.mem_union]
  left; assumption
  use v; constructor
  rw [Set.mem_union]
  left; assumption
  constructor; rfl
  rw [ne_eq, simplex_disjoint_empty, not_and_or]
  left; apply face_nonempty X u₁ u₁_in_X

  constructor
  rw [simplex_disjoint_distr_union, Finset.empty_union, simplicialJoin_mem]
  use s ∪ u₁; constructor
  rw [Set.mem_union]
  left; assumption
  use v; constructor
  rw [Set.mem_union]
  left; assumption
  constructor; rfl
  rw [ne_eq, simplex_disjoint_empty, not_and_or]
  left; apply face_nonempty X (s ∪ u₁) su₁_in_X

  rw [simplex_disjoint_distr_inter, Finset.empty_inter, simplex_disjoint_empty]
  constructor; assumption; rfl

  left
  choose u₁_in_X su₁_in_X su₁_disj using u₁_in_link
  rw [Set.mem_singleton_iff] at v_empty
  subst v_empty
  constructor
  apply simplicialJoin_incl_left; assumption
  constructor
  rw [simplex_disjoint_distr_union, Finset.empty_union]
  apply simplicialJoin_incl_left; assumption
  rw [simplex_disjoint_distr_inter, Finset.empty_inter, simplex_disjoint_empty]
  constructor; assumption; rfl

  left
  subst u₁_empty
  constructor
  apply simplicialJoin_incl_right; assumption
  constructor
  rw [simplex_disjoint_distr_union, Finset.empty_union, Finset.union_empty, simplicialJoin_mem]
  use s; constructor
  rw [Set.mem_union]
  left; assumption
  use v; constructor
  rw [Set.mem_union]
  left; assumption
  constructor; rfl
  rw [ne_eq, simplex_disjoint_empty, not_and_or]
  left; apply face_nonempty X s s_in_X
  rw [simplex_disjoint_distr_inter, Finset.empty_inter, Finset.inter_empty, simplex_disjoint_empty]
  constructor <;> rfl

  right
  rw [Set.mem_singleton_iff] at v_empty
  subst u₁_empty v_empty
  rw [simplex_disjoint_empty]
  constructor <;> rfl

  rw [simplex_disjoint_distr_union, Finset.empty_union]
  rw [Set.mem_singleton_iff] at u₂_empty
  rw [u₂_empty, Finset.union_empty] at u_decomp
  rw [← u_decomp]
  assumption

  rw [Set.mem_singleton_iff] at u₂_empty u₃_empty
  rw [u₂_empty, u₃_empty] at u'_ne
  contradiction

  rw [Set.mem_singleton_iff] at u'_empty
  rw [u'_empty, Finset.empty_union] at u_decomp
  subst u_decomp
  cases' u₁_in_link with u₁_in_link u₁_empty <;>
  cases' v_in_Y with v_in_Y v_empty

  use ∅ ⊔ₛ ∅; constructor
  right
  rw [Set.mem_singleton_iff, simplex_disjoint_empty]
  constructor <;> rfl

  use u ⊔ₛ v; constructor; left
  simp only [link, Set.mem_sep_iff] at u₁_in_link ⊢
  choose u_in_X su_in_X su_disj using u₁_in_link

  constructor
  rw [simplicialJoin_mem]
  use u; constructor
  rw [Set.mem_union]
  left; assumption
  use v; constructor
  rw [Set.mem_union]
  left; assumption
  constructor; rfl
  rw [ne_eq, simplex_disjoint_empty, not_and_or]
  left; apply face_nonempty X u u_in_X

  constructor
  simp only [simplex_disjoint_distr_union, simplicialJoin_mem, Finset.empty_union]
  use s ∪ u; constructor
  rw [Set.mem_union]
  left; assumption
  use v; constructor
  rw [Set.mem_union]
  left; assumption
  constructor; rfl
  rw [ne_eq, simplex_disjoint_empty, not_and_or]
  left; apply face_nonempty X (s ∪ u) su_in_X

  rw [simplex_disjoint_distr_inter, Finset.empty_inter, simplex_disjoint_empty]
  constructor; assumption; rfl

  simp only [simplex_disjoint_distr_union, Finset.empty_union]
  assumption

  rw [Set.mem_singleton_iff] at v_empty
  subst v_empty
  use ∅ ⊔ₛ ∅; constructor; right
  rw [Set.mem_singleton_iff, simplex_disjoint_empty]
  constructor <;> rfl

  use u ⊔ₛ ∅; constructor; left
  simp only [link, Set.mem_sep_iff] at u₁_in_link ⊢
  choose u_in_X su_in_X su_disj using u₁_in_link
  constructor
  apply simplicialJoin_incl_left; assumption
  constructor
  rw [simplex_disjoint_distr_union, Finset.empty_union]
  apply simplicialJoin_incl_left; assumption
  rw [simplex_disjoint_distr_inter, Finset.empty_inter, simplex_disjoint_empty]
  constructor; assumption; rfl

  simp only [simplex_disjoint_distr_union, Finset.empty_union]
  assumption

  rw [Set.mem_singleton_iff] at u₁_empty
  subst u₁_empty
  contradiction

  rw [Set.mem_singleton_iff] at u₁_empty v_empty
  subst u₁_empty v_empty
  contradiction

  rw [Set.mem_singleton_iff] at u_empty
  subst u_empty
  cases' v_in_Y with v_in_Y v_empty
  use ∅ ⊔ₛ ∅; constructor; right
  rw [Set.mem_singleton_iff, simplex_disjoint_empty]
  constructor <;> rfl

  use ∅ ⊔ₛ v; constructor; left
  simp only [link, Set.mem_sep_iff]
  constructor
  apply simplicialJoin_incl_right; assumption
  constructor
  rw [simplex_disjoint_distr_union, Finset.union_empty, Finset.empty_union, simplicialJoin_mem]
  use s; constructor
  rw [Set.mem_union]
  left; assumption
  use v; constructor
  rw [Set.mem_union]
  left; assumption
  constructor; rfl
  rw [ne_eq, simplex_disjoint_empty, not_and_or]
  left; apply face_nonempty X s s_in_X
  rw [simplex_disjoint_distr_inter, Finset.inter_empty, Finset.empty_inter, simplex_disjoint_empty]
  constructor <;> rfl

  simp only [simplex_disjoint_distr_union, Finset.empty_union]
  assumption

  rw [Set.mem_singleton_iff] at v_empty
  choose t_empty t_ne using t_eq_uv
  subst v_empty t_empty
  rw [ne_eq, simplex_disjoint_empty, not_and_or] at t_ne
  cases t_ne <;> contradiction

theorem stellar_join_distr_join_right
    (X Y : AbstractSimplicialComplex E)
    (s : Finset E) [s_ne : Nonempty s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
  : ((π₁[𝕜] (@barycenter_join_boundary_disjoint_link _ _ 𝕜 _ _ _ _ (X ⋆ Y : AbstractSimplicialComplex (E × 𝕜)) (s ⊔ₛ ∅) (x, 0)
            (by apply simplicialJoin_incl_left; assumption)
            (barycenter_join_left x_nin_X))).coe
        ''ˢ ((π₁[𝕜]
              (barycenter_disjoint_boundary (X ⋆ Y : AbstractSimplicialComplex (E × 𝕜)) (s ⊔ₛ ∅) (x, 0)
                  (by apply simplicialJoin_incl_left; assumption)
                  (barycenter_join_left x_nin_X))).coe
          ''ˢ ((simplex {((x, 0) : E × 𝕜)} ⋆ ∂(s ⊔ₛ ∅)) : AbstractSimplicialComplex ((E × 𝕜) × 𝕜)) ⋆
            (Lk(X ⋆ Y, s ⊔ₛ ∅) : AbstractSimplicialComplex (E × 𝕜)))).faces ⊆
      (((π₁[𝕜] (@barycenter_join_boundary_disjoint_link _ _ 𝕜 _ _ _ _ X s x s_in_X x_nin_X)).coe
        ''ˢ (((π₁[𝕜] (barycenter_disjoint_boundary X s x s_in_X x_nin_X)).coe
          ''ˢ (simplex {x} ⋆ ∂s)) ⋆
            Lk(X, s))) ⋆ Y).faces :=
by
  simp only [Set.subset_def, Set.mem_union, Set.mem_singleton_iff, simplicialJoin_mem, join_proj_mem]
  intro t t_in_img
  choose t' t'_in_join t₁ t₁_in_link t_decomp using t_in_img

  have s_zero : ∀ a : E × 𝕜, a ∈ s ⊔ₛ ∅ → a.snd = 0 :=
  by
    intro a a_in_s
    rw [simplex_disjoint_mem] at a_in_s
    cases' a_in_s with a_in_s contra
    choose a_in_s a_zero using a_in_s
    assumption
    choose contra a_one using contra
    have H : a.1 ∉ (∅ : Finset E) := by apply Finset.notMem_empty
    contradiction

  cases' t'_in_join with t'_in_join t'_empty
  · choose t₃ t₃_in_barycenter t₂ t₂_in_bd t'_decomp t'_ne using t'_in_join
    subst t'_decomp

    simp only [simplex, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_powerset,
      Finset.subset_singleton_iff] at t₃_in_barycenter
    simp only [simplexBoundary_mem_iff_subset, Finset.ssubset_iff] at t₂_in_bd

    cases' t₃_in_barycenter with t₃_in_barycenter t₃_empty <;>
    cases' t₂_in_bd with t₂_in_bd t₂_empty <;>
    cases' t₁_in_link with t₁_in_link t₁_empty
    · choose t₃_in_barycenter t₃_ne using t₃_in_barycenter
      cases' t₃_in_barycenter with t₃_empty t₃_in_barycenter
      contradiction

      choose t₂_ss_s t₂_ne using t₂_in_bd
      choose a a_nin_t₂ at₂_ss_s using t₂_ss_s

      simp only [link, Set.mem_sep_iff] at t₁_in_link
      choose t₁_in_XY st₁_in_XY st₁_disj using t₁_in_link
      rw [simplicialJoin_mem] at t₁_in_XY
      choose u₁ u₁_in_X u₂ u₂_in_Y t₁_eq_u₁u₂ t₁_ne using t₁_in_XY
      subst t₁_eq_u₁u₂

      rw [simplex_disjoint_distr_union, Finset.empty_union, simplicialJoin_mem] at st₁_in_XY
      choose v₁ v₁_in_X v₂ v₂_in_Y su₁u₂_eq_v₁v₂ su₁u₂_ne using st₁_in_XY
      rw [simplex_disjoint_eq_unique] at su₁u₂_eq_v₁v₂
      choose su₁_eq_v₁ u₂_eq_v₂ using su₁u₂_eq_v₁v₂
      subst su₁_eq_v₁ u₂_eq_v₂

      rw [simplex_disjoint_distr_inter, Finset.empty_inter, simplex_disjoint_empty] at st₁_disj
      choose su₁_disj taut using st₁_disj

      use Finset.image Prod.fst (t₃ ∪ t₂) ∪ u₁; constructor; left
      use Finset.image Prod.fst (t₃ ∪ t₂); constructor; left
      use Finset.image Prod.fst t₃; constructor; left

      simp only [simplex, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_powerset,
        Finset.subset_singleton_iff]
      simp only [t₃_in_barycenter, Finset.image_singleton, Prod.fst]
      constructor; right; trivial
      apply Finset.singleton_ne_empty

      use Finset.image Prod.fst t₂; constructor; left
      rw [simplexBoundary_mem_iff_subset, Finset.ssubset_iff]
      constructor

      use Prod.fst a
      have a_zero : a.snd = 0 :=
      by
        have a_in_s : a ∈ s ⊔ₛ ∅ := by
          apply Finset.mem_of_subset at₂_ss_s
          apply Finset.mem_insert_self
        specialize s_zero a a_in_s
        assumption
      constructor
      simp only [Finset.mem_image, exists_prop, Prod.exists, exists_and_right, exists_eq_right,
        not_exists]
      intro n
      by_cases n_zero : n = 0
      rw [n_zero, ← a_zero, Prod.mk.eta]
      assumption
      have a_nin_s : (a.fst, n) ∉ s ⊔ₛ ∅ := by
        revert n_zero
        contrapose
        simp only [Classical.not_not]
        specialize s_zero (a.fst, n)
        assumption
      revert a_nin_s
      contrapose
      simp only [Classical.not_not]
      intro a_in_t₂
      apply @Finset.mem_of_subset _ t₂
      apply @Finset.Subset.trans _ _ (insert a t₂)
      apply Finset.subset_insert
      assumption
      assumption
      rw [Finset.subset_iff] at at₂_ss_s ⊢
      intro b b_in_at₂
      rw [Finset.mem_insert] at b_in_at₂
      cases' b_in_at₂ with b_eq_a b_in_t₂
      subst b_eq_a
      specialize at₂_ss_s (Finset.mem_insert_self a t₂)
      rw [← @Prod.mk.eta _ _ a, a_zero, simplex_disjoint_mem_left] at at₂_ss_s
      assumption
      rw [Finset.mem_image] at b_in_t₂
      choose c c_in_t₂ proj_c_b using b_in_t₂
      have c_in_s : c ∈ s ⊔ₛ ∅ := by
        apply Finset.mem_of_subset at₂_ss_s
        rw [Finset.mem_insert]
        right; assumption
      specialize s_zero c c_in_s
      rw [← @Prod.mk.eta _ _ c, s_zero, simplex_disjoint_mem_left, proj_c_b] at c_in_s
      assumption

      rw [ne_eq, Finset.image_eq_empty]
      assumption

      constructor
      rw [Finset.image_union]
      rw [ne_eq, Finset.image_eq_empty]
      assumption

      cases' u₁_in_X with u₁_in_X u₁_empty
      · use u₁; constructor; left
        simp only [link, Set.mem_sep_iff]
        constructor; assumption
        constructor

        rw [Set.mem_union, Set.mem_singleton_iff] at v₁_in_X
        cases' v₁_in_X with su₁_in_X su₁_empty
        · assumption
        · have s_empty : s = ∅ :=
          by
            rw [← Finset.subset_empty] at su₁_empty ⊢
            apply @subset_trans _ _ _ s (s ∪ u₁)
            apply Finset.subset_union_left
            assumption
          subst s_empty
          rw [Finset.empty_union]
          assumption
        assumption

        constructor; rfl
        rw [ne_eq, Finset.union_eq_empty, not_and_or]
        right; apply face_nonempty X u₁ u₁_in_X
      · rw [Set.mem_singleton_iff] at u₁_empty
        subst u₁_empty
        use ∅; constructor; right; rfl
        constructor; rfl
        rw [Finset.union_empty, ne_eq, Finset.image_eq_empty]
        assumption

      use u₂; constructor
      rw [Set.mem_union, Set.mem_singleton_iff] at u₂_in_Y
      assumption

      have t₂_lift : Finset.image Prod.fst t₂ ⊔ₛ ∅ = t₂ :=
      by
        simp only [Finset.ext_iff, simplex_disjoint_mem, Finset.mem_image]
        intro b
        constructor
        intro b_in_img
        cases' b_in_img with b_in_t₂ contra
        choose proj_c_b b_zero using b_in_t₂
        choose c c_in_t₂ proj_c_b using proj_c_b
        have c_in_s : c ∈ s ⊔ₛ ∅ := by
          apply Finset.mem_of_subset at₂_ss_s
          rw [Finset.mem_insert]
          right; assumption
        specialize s_zero c c_in_s
        rw [← @Prod.mk.eta _ _ c, s_zero, proj_c_b, ← b_zero, Prod.mk.eta] at c_in_t₂
        assumption
        choose contra b_one using contra
        have H : b.fst ∉ (∅ : Finset E) := by apply Finset.notMem_empty
        contradiction
        intro b_in_t₂
        left; constructor
        use b
        have b_in_s : b ∈ s ⊔ₛ ∅ := by
          apply Finset.mem_of_subset at₂_ss_s
          rw [Finset.mem_insert]
          right; assumption
        specialize s_zero b b_in_s
        assumption
      have t₃_lift : Finset.image Prod.fst t₃ ⊔ₛ ∅ = t₃ :=
      by
        simp only [simplex, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at t₃_in_barycenter
        rw [t₃_in_barycenter]
        simp only [simplexDisjointUnion, Finset.image_singleton, Finset.product_singleton,
          Finset.map_singleton, Function.Embedding.coeFn_mk, Finset.map_empty, Finset.union_empty]

      rw [← t₂_lift, ← t₃_lift] at t_decomp
      simp only [simplex_disjoint_distr_union, ← Finset.image_union, Finset.empty_union] at t_decomp
      assumption
    · subst t₁_empty
      choose t₃_in_barycenter t₃_ne using t₃_in_barycenter
      cases' t₃_in_barycenter with t₃_empty t₃_in_barycenter
      contradiction

      choose t₂_ss_s t₂_ne using t₂_in_bd
      choose a a_nin_t₂ at₂_ss_s using t₂_ss_s

      use Finset.image Prod.fst (t₃ ∪ t₂) ∪ ∅; constructor; left
      use Finset.image Prod.fst (t₃ ∪ t₂); constructor; left
      use Finset.image Prod.fst t₃; constructor; left

      simp only [simplex, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_powerset,
        Finset.subset_singleton_iff]
      simp only [t₃_in_barycenter, Finset.image_singleton, Prod.fst]
      constructor; right; trivial
      apply Finset.singleton_ne_empty

      use Finset.image Prod.fst t₂; constructor; left
      rw [simplexBoundary_mem_iff_subset, Finset.ssubset_iff]
      constructor

      use Prod.fst a
      have a_zero : a.snd = 0 :=
      by
        have a_in_s : a ∈ s ⊔ₛ ∅ := by
          apply Finset.mem_of_subset at₂_ss_s
          apply Finset.mem_insert_self
        specialize s_zero a a_in_s
        assumption
      constructor
      simp only [Finset.mem_image, exists_prop, Prod.exists, exists_and_right, exists_eq_right,
        not_exists]
      intro n
      by_cases n_zero : n = 0
      rw [n_zero, ← a_zero, Prod.mk.eta]
      assumption
      have a_nin_s : (a.fst, n) ∉ s ⊔ₛ ∅ := by
        revert n_zero
        contrapose
        simp only [Classical.not_not]
        specialize s_zero (a.fst, n)
        assumption
      revert a_nin_s
      contrapose
      simp only [Classical.not_not]
      intro a_in_t₂
      apply @Finset.mem_of_subset _ t₂
      apply @Finset.Subset.trans _ _ (insert a t₂)
      apply Finset.subset_insert
      assumption
      assumption
      rw [Finset.subset_iff] at at₂_ss_s ⊢
      intro b b_in_at₂
      rw [Finset.mem_insert] at b_in_at₂
      cases' b_in_at₂ with b_eq_a b_in_t₂
      subst b_eq_a
      specialize at₂_ss_s (Finset.mem_insert_self a t₂)
      rw [← @Prod.mk.eta _ _ a, a_zero, simplex_disjoint_mem_left] at at₂_ss_s
      assumption
      rw [Finset.mem_image] at b_in_t₂
      choose c c_in_t₂ proj_c_b using b_in_t₂
      have c_in_s : c ∈ s ⊔ₛ ∅ := by
        apply Finset.mem_of_subset at₂_ss_s
        rw [Finset.mem_insert]
        right; assumption
      specialize s_zero c c_in_s
      rw [← @Prod.mk.eta _ _ c, s_zero, simplex_disjoint_mem_left, proj_c_b] at c_in_s
      assumption

      rw [ne_eq, Finset.image_eq_empty]
      assumption

      constructor
      rw [Finset.image_union]
      rw [ne_eq, Finset.image_eq_empty]
      assumption

      use ∅; constructor; right; rfl
      constructor; rfl
      simp only [ne_eq, Finset.union_eq_empty, not_and_or, Finset.image_union, Finset.image_eq_empty]
      left; left; assumption

      use ∅; constructor; right; rfl
      have t₂_lift : Finset.image Prod.fst t₂ ⊔ₛ ∅ = t₂ :=
      by
        simp only [Finset.ext_iff, simplex_disjoint_mem, Finset.mem_image]
        intro b
        constructor
        intro b_in_img
        cases' b_in_img with b_in_t₂ contra
        choose proj_c_b b_zero using b_in_t₂
        choose c c_in_t₂ proj_c_b using proj_c_b
        have c_in_s : c ∈ s ⊔ₛ ∅ := by
          apply Finset.mem_of_subset at₂_ss_s
          rw [Finset.mem_insert]
          right; assumption
        specialize s_zero c c_in_s
        rw [← @Prod.mk.eta _ _ c, s_zero, proj_c_b, ← b_zero, Prod.mk.eta] at c_in_t₂
        assumption
        choose contra b_one using contra
        have H : b.fst ∉ (∅ : Finset E) := by apply Finset.notMem_empty
        contradiction
        intro b_in_t₂
        left; constructor
        use b
        have b_in_s : b ∈ s ⊔ₛ ∅ := by
          apply Finset.mem_of_subset at₂_ss_s
          rw [Finset.mem_insert]
          right; assumption
        specialize s_zero b b_in_s
        assumption
      have t₃_lift : Finset.image Prod.fst t₃ ⊔ₛ ∅ = t₃ :=
      by
        simp only [simplex, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at t₃_in_barycenter
        rw [t₃_in_barycenter]
        simp only [simplexDisjointUnion, Finset.image_singleton, Finset.product_singleton,
          Finset.map_singleton, Function.Embedding.coeFn_mk, Finset.map_empty, Finset.union_empty]

      rw [← t₂_lift, ← t₃_lift] at t_decomp
      simp only [simplex_disjoint_distr_union, ← Finset.image_union, Finset.union_empty] at t_decomp
      rw [Finset.union_empty]
      assumption
    · subst t₂_empty
      choose t₃_in_barycenter t₃_ne using t₃_in_barycenter
      cases' t₃_in_barycenter with t₃_empty t₃_in_barycenter
      contradiction

      simp only [link, Set.mem_sep_iff] at t₁_in_link
      choose t₁_in_XY st₁_in_XY st₁_disj using t₁_in_link
      rw [simplicialJoin_mem] at t₁_in_XY
      choose u₁ u₁_in_X u₂ u₂_in_Y t₁_eq_u₁u₂ t₁_ne using t₁_in_XY
      subst t₁_eq_u₁u₂

      rw [simplex_disjoint_distr_union, Finset.empty_union, simplicialJoin_mem] at st₁_in_XY
      choose v₁ v₁_in_X v₂ v₂_in_Y su₁u₂_eq_v₁v₂ su₁u₂_ne using st₁_in_XY
      rw [simplex_disjoint_eq_unique] at su₁u₂_eq_v₁v₂
      choose su₁_eq_v₁ u₂_eq_v₂ using su₁u₂_eq_v₁v₂
      subst su₁_eq_v₁ u₂_eq_v₂

      rw [simplex_disjoint_distr_inter, Finset.empty_inter, simplex_disjoint_empty] at st₁_disj
      choose su₁_disj taut using st₁_disj

      use Finset.image Prod.fst (t₃ ∪ ∅) ∪ u₁; constructor; left
      use Finset.image Prod.fst (t₃ ∪ ∅); constructor; left
      use Finset.image Prod.fst t₃; constructor; left

      simp only [simplex, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_powerset,
        Finset.subset_singleton_iff]
      simp only [t₃_in_barycenter, Finset.image_singleton, Prod.fst]
      constructor; right; trivial
      apply Finset.singleton_ne_empty

      use ∅; constructor; right; rfl
      constructor
      rw [Finset.image_union, Finset.image_empty]
      rw [ne_eq, Finset.image_eq_empty, Finset.union_empty]
      assumption

      cases' u₁_in_X with u₁_in_X u₁_empty
      · use u₁; constructor; left
        simp only [link, Set.mem_sep_iff]
        constructor; assumption
        constructor

        rw [Set.mem_union, Set.mem_singleton_iff] at v₁_in_X
        cases' v₁_in_X with su₁_in_X su₁_empty
        · assumption
        · have s_empty : s = ∅ :=
          by
            rw [← Finset.subset_empty] at su₁_empty ⊢
            apply @subset_trans _ _ _ s (s ∪ u₁)
            apply Finset.subset_union_left
            assumption
          subst s_empty
          rw [Finset.empty_union]
          assumption
        assumption

        constructor; rfl
        rw [ne_eq, Finset.union_eq_empty, not_and_or]
        right; apply face_nonempty X u₁ u₁_in_X
      · rw [Set.mem_singleton_iff] at u₁_empty
        subst u₁_empty
        use ∅; constructor; right; rfl
        constructor; rfl
        rw [Finset.union_empty, ne_eq, Finset.image_eq_empty]
        assumption

      use u₂; constructor
      rw [Set.mem_union, Set.mem_singleton_iff] at u₂_in_Y
      assumption

      have t₃_lift : Finset.image Prod.fst t₃ ⊔ₛ ∅ = t₃ :=
      by
        simp only [simplex, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at t₃_in_barycenter
        rw [t₃_in_barycenter]
        simp only [simplexDisjointUnion, Finset.image_singleton, Finset.product_singleton,
          Finset.map_singleton, Function.Embedding.coeFn_mk, Finset.map_empty, Finset.union_empty]

      rw [← t₃_lift] at t_decomp
      simp only [Finset.union_empty, simplex_disjoint_distr_union, Finset.empty_union] at t_decomp
      rw [Finset.image_union, Finset.image_empty, Finset.union_empty]
      assumption
    · subst t₁_empty t₂_empty
      choose t₃_in_barycenter t₃_ne using t₃_in_barycenter
      cases' t₃_in_barycenter with t₃_empty t₃_in_barycenter
      contradiction

      use Finset.image Prod.fst (t₃ ∪ ∅) ∪ ∅; constructor; left
      use Finset.image Prod.fst (t₃ ∪ ∅); constructor; left
      use Finset.image Prod.fst t₃; constructor; left

      simp only [simplex, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_powerset,
        Finset.subset_singleton_iff]
      simp only [t₃_in_barycenter, Finset.image_singleton, Prod.fst]
      constructor; right; trivial
      apply Finset.singleton_ne_empty

      use ∅; constructor; right; rfl
      constructor
      rw [Finset.image_union, Finset.image_empty]

      rw [ne_eq, Finset.image_eq_empty]
      assumption

      use ∅; constructor; right; rfl
      constructor; rfl

      simp only [Finset.union_empty, ne_eq, Finset.image_eq_empty]
      assumption

      use ∅; constructor; right; rfl

      have t₃_lift : Finset.image Prod.fst t₃ ⊔ₛ ∅ = t₃ :=
      by
        simp only [simplex, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at t₃_in_barycenter
        rw [t₃_in_barycenter]
        simp only [simplexDisjointUnion, Finset.image_singleton, Finset.product_singleton,
          Finset.map_singleton, Function.Embedding.coeFn_mk, Finset.map_empty, Finset.union_empty]

      rw [← t₃_lift] at t_decomp
      simp only [Finset.union_empty] at t_decomp ⊢
      assumption
    · subst t₃_empty
      choose t₂_ss_s t₂_ne using t₂_in_bd
      choose a a_nin_t₂ at₂_ss_s using t₂_ss_s

      simp only [link, Set.mem_sep_iff] at t₁_in_link
      choose t₁_in_XY st₁_in_XY st₁_disj using t₁_in_link
      rw [simplicialJoin_mem] at t₁_in_XY
      choose u₁ u₁_in_X u₂ u₂_in_Y t₁_eq_u₁u₂ t₁_ne using t₁_in_XY
      subst t₁_eq_u₁u₂

      rw [simplex_disjoint_distr_union, Finset.empty_union, simplicialJoin_mem] at st₁_in_XY
      choose v₁ v₁_in_X v₂ v₂_in_Y su₁u₂_eq_v₁v₂ su₁u₂_ne using st₁_in_XY
      rw [simplex_disjoint_eq_unique] at su₁u₂_eq_v₁v₂
      choose su₁_eq_v₁ u₂_eq_v₂ using su₁u₂_eq_v₁v₂
      subst su₁_eq_v₁ u₂_eq_v₂

      rw [simplex_disjoint_distr_inter, Finset.empty_inter, simplex_disjoint_empty] at st₁_disj
      choose su₁_disj taut using st₁_disj

      use Finset.image Prod.fst (∅ ∪ t₂) ∪ u₁; constructor; left
      use Finset.image Prod.fst (∅ ∪ t₂); constructor; left
      use ∅; constructor; right; rfl

      use Finset.image Prod.fst t₂; constructor; left
      rw [simplexBoundary_mem_iff_subset, Finset.ssubset_iff]
      constructor

      use Prod.fst a
      have a_zero : a.snd = 0 :=
      by
        have a_in_s : a ∈ s ⊔ₛ ∅ := by
          apply Finset.mem_of_subset at₂_ss_s
          apply Finset.mem_insert_self
        specialize s_zero a a_in_s
        assumption
      constructor
      simp only [Finset.mem_image, exists_prop, Prod.exists, exists_and_right, exists_eq_right,
        not_exists]
      intro n
      by_cases n_zero : n = 0
      rw [n_zero, ← a_zero, Prod.mk.eta]
      assumption
      have a_nin_s : (a.fst, n) ∉ s ⊔ₛ ∅ := by
        revert n_zero
        contrapose
        simp only [Classical.not_not]
        specialize s_zero (a.fst, n)
        assumption
      revert a_nin_s
      contrapose
      simp only [Classical.not_not]
      intro a_in_t₂
      apply @Finset.mem_of_subset _ t₂
      apply @Finset.Subset.trans _ _ (insert a t₂)
      apply Finset.subset_insert
      assumption
      assumption
      rw [Finset.subset_iff] at at₂_ss_s ⊢
      intro b b_in_at₂
      rw [Finset.mem_insert] at b_in_at₂
      cases' b_in_at₂ with b_eq_a b_in_t₂
      subst b_eq_a
      specialize at₂_ss_s (Finset.mem_insert_self a t₂)
      rw [← @Prod.mk.eta _ _ a, a_zero, simplex_disjoint_mem_left] at at₂_ss_s
      assumption
      rw [Finset.mem_image] at b_in_t₂
      choose c c_in_t₂ proj_c_b using b_in_t₂
      have c_in_s : c ∈ s ⊔ₛ ∅ := by
        apply Finset.mem_of_subset at₂_ss_s
        rw [Finset.mem_insert]
        right; assumption
      specialize s_zero c c_in_s
      rw [← @Prod.mk.eta _ _ c, s_zero, simplex_disjoint_mem_left, proj_c_b] at c_in_s
      assumption

      rw [ne_eq, Finset.image_eq_empty]
      assumption

      constructor
      rw [Finset.image_union, Finset.image_empty]
      rw [ne_eq, Finset.image_eq_empty]
      assumption

      cases' u₁_in_X with u₁_in_X u₁_empty
      · use u₁; constructor; left
        simp only [link, Set.mem_sep_iff]
        constructor; assumption
        constructor

        rw [Set.mem_union, Set.mem_singleton_iff] at v₁_in_X
        cases' v₁_in_X with su₁_in_X su₁_empty
        · assumption
        · have s_empty : s = ∅ :=
          by
            rw [← Finset.subset_empty] at su₁_empty ⊢
            apply @subset_trans _ _ _ s (s ∪ u₁)
            apply Finset.subset_union_left
            assumption
          subst s_empty
          rw [Finset.empty_union]
          assumption
        assumption

        constructor; rfl
        rw [ne_eq, Finset.union_eq_empty, not_and_or]
        right; apply face_nonempty X u₁ u₁_in_X
      · rw [Set.mem_singleton_iff] at u₁_empty
        subst u₁_empty
        use ∅; constructor; right; rfl
        constructor; rfl
        rw [Finset.union_empty, ne_eq, Finset.image_eq_empty]
        assumption

      use u₂; constructor
      rw [Set.mem_union, Set.mem_singleton_iff] at u₂_in_Y
      assumption

      have t₂_lift : Finset.image Prod.fst t₂ ⊔ₛ ∅ = t₂ :=
      by
        simp only [Finset.ext_iff, simplex_disjoint_mem, Finset.mem_image]
        intro b
        constructor
        intro b_in_img
        cases' b_in_img with b_in_t₂ contra
        choose proj_c_b b_zero using b_in_t₂
        choose c c_in_t₂ proj_c_b using proj_c_b
        have c_in_s : c ∈ s ⊔ₛ ∅ := by
          apply Finset.mem_of_subset at₂_ss_s
          rw [Finset.mem_insert]
          right; assumption
        specialize s_zero c c_in_s
        rw [← @Prod.mk.eta _ _ c, s_zero, proj_c_b, ← b_zero, Prod.mk.eta] at c_in_t₂
        assumption
        choose contra b_one using contra
        have H : b.fst ∉ (∅ : Finset E) := by apply Finset.notMem_empty
        contradiction
        intro b_in_t₂
        left; constructor
        use b
        have b_in_s : b ∈ s ⊔ₛ ∅ := by
          apply Finset.mem_of_subset at₂_ss_s
          rw [Finset.mem_insert]
          right; assumption
        specialize s_zero b b_in_s
        assumption

      rw [← t₂_lift] at t_decomp
      simp only [Finset.empty_union, simplex_disjoint_distr_union] at t_decomp
      rw [Finset.empty_union]
      assumption
    · subst t₁_empty t₃_empty
      choose t₂_ss_s t₂_ne using t₂_in_bd
      choose a a_nin_t₂ at₂_ss_s using t₂_ss_s

      use Finset.image Prod.fst (∅ ∪ t₂) ∪ ∅; constructor; left
      use Finset.image Prod.fst (∅ ∪ t₂); constructor; left
      use ∅; constructor; right; rfl

      use Finset.image Prod.fst t₂; constructor; left
      rw [simplexBoundary_mem_iff_subset, Finset.ssubset_iff]
      constructor

      use Prod.fst a
      have a_zero : a.snd = 0 :=
      by
        have a_in_s : a ∈ s ⊔ₛ ∅ := by
          apply Finset.mem_of_subset at₂_ss_s
          apply Finset.mem_insert_self
        specialize s_zero a a_in_s
        assumption
      constructor
      simp only [Finset.mem_image, exists_prop, Prod.exists, exists_and_right, exists_eq_right,
        not_exists]
      intro n
      by_cases n_zero : n = 0
      rw [n_zero, ← a_zero, Prod.mk.eta]
      assumption
      have a_nin_s : (a.fst, n) ∉ s ⊔ₛ ∅ := by
        revert n_zero
        contrapose
        simp only [Classical.not_not]
        specialize s_zero (a.fst, n)
        assumption
      revert a_nin_s
      contrapose
      simp only [Classical.not_not]
      intro a_in_t₂
      apply @Finset.mem_of_subset _ t₂
      apply @Finset.Subset.trans _ _ (insert a t₂)
      apply Finset.subset_insert
      assumption
      assumption
      rw [Finset.subset_iff] at at₂_ss_s ⊢
      intro b b_in_at₂
      rw [Finset.mem_insert] at b_in_at₂
      cases' b_in_at₂ with b_eq_a b_in_t₂
      subst b_eq_a
      specialize at₂_ss_s (Finset.mem_insert_self a t₂)
      rw [← @Prod.mk.eta _ _ a, a_zero, simplex_disjoint_mem_left] at at₂_ss_s
      assumption
      rw [Finset.mem_image] at b_in_t₂
      choose c c_in_t₂ proj_c_b using b_in_t₂
      have c_in_s : c ∈ s ⊔ₛ ∅ := by
        apply Finset.mem_of_subset at₂_ss_s
        rw [Finset.mem_insert]
        right; assumption
      specialize s_zero c c_in_s
      rw [← @Prod.mk.eta _ _ c, s_zero, simplex_disjoint_mem_left, proj_c_b] at c_in_s
      assumption

      rw [ne_eq, Finset.image_eq_empty]
      assumption

      constructor
      rw [Finset.image_union, Finset.image_empty]
      rw [ne_eq, Finset.image_eq_empty]
      assumption

      use ∅; constructor; right; rfl
      constructor; rfl
      rw [Finset.image_union, Finset.image_empty, Finset.empty_union, Finset.union_empty,
        ne_eq, Finset.image_eq_empty]
      assumption

      use ∅; constructor; right; rfl

      have t₂_lift : Finset.image Prod.fst t₂ ⊔ₛ ∅ = t₂ :=
      by
        simp only [Finset.ext_iff, simplex_disjoint_mem, Finset.mem_image]
        intro b
        constructor
        intro b_in_img
        cases' b_in_img with b_in_t₂ contra
        choose proj_c_b b_zero using b_in_t₂
        choose c c_in_t₂ proj_c_b using proj_c_b
        have c_in_s : c ∈ s ⊔ₛ ∅ := by
          apply Finset.mem_of_subset at₂_ss_s
          rw [Finset.mem_insert]
          right; assumption
        specialize s_zero c c_in_s
        rw [← @Prod.mk.eta _ _ c, s_zero, proj_c_b, ← b_zero, Prod.mk.eta] at c_in_t₂
        assumption
        choose contra b_one using contra
        have H : b.fst ∉ (∅ : Finset E) := by apply Finset.notMem_empty
        contradiction
        intro b_in_t₂
        left; constructor
        use b
        have b_in_s : b ∈ s ⊔ₛ ∅ := by
          apply Finset.mem_of_subset at₂_ss_s
          rw [Finset.mem_insert]
          right; assumption
        specialize s_zero b b_in_s
        assumption

      rw [← t₂_lift] at t_decomp
      rw [Finset.empty_union, Finset.union_empty] at t_decomp ⊢
      assumption
    · subst t₂_empty t₃_empty
      simp only [link, Set.mem_sep_iff] at t₁_in_link
      choose t₁_in_XY st₁_in_XY st₁_disj using t₁_in_link
      rw [simplicialJoin_mem] at t₁_in_XY
      choose u₁ u₁_in_X u₂ u₂_in_Y t₁_eq_u₁u₂ t₁_ne using t₁_in_XY
      subst t₁_eq_u₁u₂

      rw [simplex_disjoint_distr_union, Finset.empty_union, simplicialJoin_mem] at st₁_in_XY
      choose v₁ v₁_in_X v₂ v₂_in_Y su₁u₂_eq_v₁v₂ su₁u₂_ne using st₁_in_XY
      rw [simplex_disjoint_eq_unique] at su₁u₂_eq_v₁v₂
      choose su₁_eq_v₁ u₂_eq_v₂ using su₁u₂_eq_v₁v₂
      subst su₁_eq_v₁ u₂_eq_v₂

      rw [simplex_disjoint_distr_inter, Finset.empty_inter, simplex_disjoint_empty] at st₁_disj
      choose su₁_disj taut using st₁_disj

      use Finset.image Prod.fst (∅ ∪ ∅ : Finset (E × 𝕜)) ∪ u₁; constructor; left
      use Finset.image Prod.fst (∅ ∪ ∅ : Finset (E × 𝕜)); constructor; right
      rw [Finset.image_eq_empty, Finset.empty_union]

      cases' u₁_in_X with u₁_in_X u₁_empty
      · use u₁; constructor; left
        simp only [link, Set.mem_sep_iff]
        constructor; assumption
        constructor

        rw [Set.mem_union, Set.mem_singleton_iff] at v₁_in_X
        cases' v₁_in_X with su₁_in_X su₁_empty
        · assumption
        · have s_empty : s = ∅ :=
          by
            rw [← Finset.subset_empty] at su₁_empty ⊢
            apply @subset_trans _ _ _ s (s ∪ u₁)
            apply Finset.subset_union_left
            assumption
          subst s_empty
          rw [Finset.empty_union]
          assumption
        assumption

        constructor; rfl
        rw [ne_eq, Finset.union_eq_empty, not_and_or]
        right; apply face_nonempty X u₁ u₁_in_X
      · rw [Set.mem_singleton_iff] at u₁_empty
        subst u₁_empty
        use ∅; constructor; right; rfl
        constructor; rfl
        rw [Finset.union_empty, ne_eq, Finset.image_eq_empty]
        assumption

      use u₂; constructor
      rw [Set.mem_union, Set.mem_singleton_iff] at u₂_in_Y
      assumption

      simp only [Finset.empty_union] at t_decomp
      simp only [Finset.empty_union, Finset.image_empty]
      assumption
    · subst t₁_empty t₂_empty t₃_empty
      contradiction
  · subst t'_empty
    cases' t₁_in_link with t₁_in_link t₁_empty
    · simp only [link, Set.mem_sep_iff] at t₁_in_link
      choose t₁_in_XY st₁_in_XY st₁_disj using t₁_in_link
      simp only [simplicialJoin_mem, Set.mem_union, Set.mem_singleton_iff] at t₁_in_XY
      choose u₁ u₁_in_X u₂ u₂_in_Y t₁_eq_u₁u₂ t₁_ne using t₁_in_XY
      subst t₁_eq_u₁u₂
      cases' u₁_in_X with u₁_in_X u₁_empty <;>
      cases' u₂_in_Y with u₂_in_Y u₂_empty
      · use u₁; constructor; left
        use ∅; constructor; right; rfl
        use u₁; constructor; left
        simp only [link, Set.mem_sep_iff]
        constructor; assumption
        constructor

        rw [simplex_disjoint_distr_union, simplicialJoin_mem] at st₁_in_XY
        choose v₁ v₁_in_X v₂ v₂_in_Y su₁u₂_eq_v₁v₂ su₁u₂_ne using st₁_in_XY
        rw [simplex_disjoint_eq_unique] at su₁u₂_eq_v₁v₂
        choose su₁_eq_v₁ u₂_eq_v₂ using su₁u₂_eq_v₁v₂
        subst su₁_eq_v₁
        cases' v₁_in_X with su₁_in_X su₁_empty
        · assumption
        · rw [Set.mem_singleton_iff] at su₁_empty
          have s_empty : s = ∅ :=
          by
            rw [← Finset.subset_empty] at su₁_empty ⊢
            apply @subset_trans _ _ _ s (s ∪ u₁)
            apply Finset.subset_union_left
            assumption
          subst s_empty
          rw [Finset.empty_union]
          assumption
        rw [simplex_disjoint_distr_inter, simplex_disjoint_empty] at st₁_disj
        choose su₁_disj u₂_empty using st₁_disj
        assumption
        constructor
        rw [Finset.empty_union]
        apply face_nonempty X u₁ u₁_in_X

        use u₂; constructor; left; assumption
        rw [Finset.empty_union] at t_decomp
        assumption
      · subst u₂_empty
        use u₁; constructor; left
        use ∅; constructor; right; rfl
        use u₁; constructor; left
        simp only [link, Set.mem_sep_iff]
        constructor; assumption
        constructor

        rw [simplex_disjoint_distr_union, simplicialJoin_mem] at st₁_in_XY
        choose v₁ v₁_in_X v₂ v₂_in_Y su₁u₂_eq_v₁v₂ su₁u₂_ne using st₁_in_XY
        rw [simplex_disjoint_eq_unique] at su₁u₂_eq_v₁v₂
        choose su₁_eq_v₁ u₂_eq_v₂ using su₁u₂_eq_v₁v₂
        subst su₁_eq_v₁
        cases' v₁_in_X with su₁_in_X su₁_empty
        · assumption
        · rw [Set.mem_singleton_iff] at su₁_empty
          have s_empty : s = ∅ :=
          by
            rw [← Finset.subset_empty] at su₁_empty ⊢
            apply @subset_trans _ _ _ s (s ∪ u₁)
            apply Finset.subset_union_left
            assumption
          subst s_empty
          rw [Finset.empty_union]
          assumption
        rw [simplex_disjoint_distr_inter, simplex_disjoint_empty] at st₁_disj
        choose su₁_disj u₂_empty using st₁_disj
        assumption
        constructor
        rw [Finset.empty_union]
        apply face_nonempty X u₁ u₁_in_X

        use ∅; constructor; right; rfl
        rw [Finset.empty_union] at t_decomp
        assumption
      · subst u₁_empty
        use ∅; constructor; right; rfl
        use u₂; constructor; left; assumption
        rw [Finset.empty_union] at t_decomp
        assumption
      · subst u₁_empty u₂_empty
        rw [ne_eq, simplex_disjoint_empty, not_and_or] at t₁_ne
        cases t₁_ne <;> contradiction
    · subst t₁_empty
      choose t_empty t_ne using t_decomp
      rw [Finset.empty_union] at t_empty
      contradiction

theorem stellar_join_distr_join
    (X Y : AbstractSimplicialComplex E)
    (s : Finset E) [s_ne : Nonempty s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
  : (((π₁[𝕜] (@barycenter_join_boundary_disjoint_link _ _ 𝕜 _ _ _ _ X s x s_in_X x_nin_X)).coe
      ''ˢ (((π₁[𝕜] (barycenter_disjoint_boundary X s x s_in_X x_nin_X)).coe
        ''ˢ (simplex {x} ⋆ ∂s)) ⋆
          Lk(X, s))) ⋆ Y).faces =
      ((π₁[𝕜] (@barycenter_join_boundary_disjoint_link _ _ 𝕜 _ _ _ _ (X ⋆ Y : AbstractSimplicialComplex (E × 𝕜)) (s ⊔ₛ ∅) (x, 0)
            (by apply simplicialJoin_incl_left; assumption)
            (barycenter_join_left x_nin_X))).coe
        ''ˢ ((π₁[𝕜]
              (barycenter_disjoint_boundary (X ⋆ Y : AbstractSimplicialComplex (E × 𝕜)) (s ⊔ₛ ∅) (x, 0)
                  (by apply simplicialJoin_incl_left; assumption)
                  (barycenter_join_left x_nin_X))).coe
          ''ˢ ((simplex {((x, 0) : E × 𝕜)} ⋆ ∂(s ⊔ₛ ∅)) : AbstractSimplicialComplex ((E × 𝕜) × 𝕜)) ⋆
            (Lk(X ⋆ Y, s ⊔ₛ ∅) : AbstractSimplicialComplex (E × 𝕜)))).faces :=
by
  rw [Set.Subset.antisymm_iff]
  constructor
  apply stellar_join_distr_join_left <;> assumption
  apply stellar_join_distr_join_right <;> assumption

theorem stellar_subdiv_distr_join_left
    (X Y : AbstractSimplicialComplex E)
    (s : Finset E) [s_ne : Nonempty s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
  : (σ(X, s, x; 𝕜, s_in_X, x_nin_X) ⋆ Y : AbstractSimplicialComplex (E × 𝕜)) ≅
      σ(X ⋆ Y, s ⊔ₛ ∅, (x, 0); 𝕜,
        by apply @simplicialJoin_incl_left _ 𝕜; assumption,
        barycenter_join_left x_nin_X) :=
by
  apply
    @simplicial_iso_trans (E × 𝕜) (E × 𝕜) _ _ _ _ (σ(X, s, x; 𝕜, s_in_X, x_nin_X) ⋆ Y)
      (X\St(X, s) ⋆ Y ∪ (π₁[𝕜] _).coe ''ˢ ((π₁[𝕜] _).coe ''ˢ (simplex {x} ⋆ ∂s) ⋆ Lk(X, s)) ⋆ Y)
  apply simplicial_iso_preserves_equiv
  apply simplicialJoin_distr_union_right
  apply simplicial_iso_preserves_equiv
  simp only [stellarSubdivision, AbstractSimplicialComplex.instHasUnion, simplicialUnion]
  rw [join_distr_starComplement_simplices, stellar_join_distr_join]
  all_goals { assumption }

theorem barycenter_join_right
    {X Y : AbstractSimplicialComplex E}
    {x : E}
  : x ∉ Y.vertices → (x, 1) ∉ (X ⋆ Y : AbstractSimplicialComplex (E × 𝕜)).vertices :=
by
  contrapose
  simp only [Classical.not_not, simplicialJoin_vertices_mem_right]
  exact Set.mem_of_eq_of_mem rfl

theorem stellar_subdiv_distr_join_right
    (X Y : AbstractSimplicialComplex E)
    (t : Finset E) [t_ne : Nonempty t]
    (y : E)
    (t_in_Y : t ∈ Y.faces)
    (y_nin_Y : y ∉ Y.vertices)
  : (X ⋆ σ(Y, t, y; 𝕜, t_in_Y, y_nin_Y) : AbstractSimplicialComplex (E × 𝕜)) ≅
      σ(X ⋆ Y, ∅ ⊔ₛ t, (y, 1); 𝕜,
        by apply @simplicialJoin_incl_right E 𝕜; assumption,
        barycenter_join_right y_nin_Y) :=
by
  apply
    @simplicial_iso_trans (E × 𝕜) (E × 𝕜) _ _ _ _ (X ⋆ σ(Y, t, y; 𝕜, t_in_Y, y_nin_Y))
      (σ(Y, t, y; 𝕜, t_in_Y, y_nin_Y) ⋆ X)
  apply simplicialJoin_comm
  apply
    simplicial_iso_trans (σ(Y, t, y; 𝕜, t_in_Y, y_nin_Y) ⋆ X)
      σ(Y ⋆ X, t ⊔ₛ ∅, (y, 0); 𝕜,
        by apply @simplicialJoin_incl_left E 𝕜; assumption,
        barycenter_join_left y_nin_Y)
  apply stellar_subdiv_distr_join_left <;> assumption
  let f : SimplicialMap (Y ⋆ X) (X ⋆ Y) :=
    @SimplicialMap.mk (E × 𝕜) (E × 𝕜) _ _ _ simplicialJoinCommMap (simplicialJoin_comm_simplicial Y X)
  let g : SimplicialMap (X ⋆ Y) (Y ⋆ X) :=
    @SimplicialMap.mk (E × 𝕜) (E × 𝕜) _ _ _ simplicialJoinCommMap (simplicialJoin_comm_simplicial X Y)
  have gf_inv : IsInverseSimplicialIso f g :=
  by
    unfold IsInverseSimplicialIso
    constructor <;>
      · simp only [Set.restrict_eq_restrict_iff, Set.EqOn]
        intro x x_in_XY
        rw [simplicialJoin_mem_vertices] at x_in_XY
        simp only [f, g, SimplicialMap.comp, simplicialJoinCommMap, id, Function.comp_apply]
        cases' x_in_XY with x_in_X x_in_Y
        choose x_in_X x_zero using x_in_X
        simp only [x_zero, one_ne_zero, ↓reduceIte, f, g]
        simp only [← x_zero, Prod.ext_iff, Prod.fst, Prod.snd]
        choose x_in_Y x_one using x_in_Y
        simp only [x_one, one_ne_zero, ↓reduceIte, f, g]
        simp only [← x_one, Prod.ext_iff, Prod.fst, Prod.snd]
  have f_iso : IsSimplicialIso f :=
  by
    unfold IsSimplicialIso
    use g
  apply stellar_subdiv_iso
  apply f_iso
  apply gf_inv
  simp only [Finset.ext_iff, Finset.mem_image, simplex_disjoint_mem]
  intro a
  constructor
  · intro a_in_img
    choose b b_in_disj fb_a using a_in_img
    cases' b_in_disj with b_in_t contra
    choose b_in_t b_zero using b_in_t
    simp only [f, simplicialJoinCommMap, b_zero, ↓reduceIte, f, g, Prod.ext_iff] at fb_a
    choose b_eq_a a_one using fb_a
    rw [@comm _ Eq] at a_one
    rw [b_eq_a] at b_in_t
    right; constructor <;> assumption
    choose contra b_one using contra
    contradiction
  · intro a_in_disj
    cases' a_in_disj with contra a_in_t
    choose contra a_zero using contra
    contradiction
    choose a_in_t a_one using a_in_t
    use(a.fst, 0); constructor
    simp only [Prod.fst, Prod.snd]
    left; constructor
    assumption
    trivial
    simp only [f, simplicialJoinCommMap, eq_self_iff_true, if_true, ← a_one, Prod.ext_iff]
  simp only [f, simplicialJoinCommMap, eq_self_iff_true, if_true]
  simp only [g, simplicialJoinCommMap, Nat.one_ne_zero, if_false]
  simp only [one_ne_zero, ↓reduceIte, f, g]

-- Lemma 3.1, p.10
theorem simplicialJoin_stellarEquiv
    (X Y Z W : AbstractSimplicialComplex E)
  : X ≅ₛₜ[𝕜] Y → Z ≅ₛₜ[𝕜] W → (X ⋆ Z) ≅ₛₜ[𝕜] (Y ⋆ W : AbstractSimplicialComplex (E × 𝕜)) :=
by
  intro X_eq_Y Z_eq_W
  apply @Relation.ReflTransGen.trans _ _ _ (Y ⋆ Z)
  unfold StellarEquiv at *
  induction' X_eq_Y with K L X_eq_K K_move_L H_ind
  rfl
  apply @Relation.ReflTransGen.tail _ _ _ (K ⋆ Z) (L ⋆ Z)
  apply H_ind
  simp only [StellarMove] at K_move_L ⊢
  cases' K_move_L with K_move_L K_move_L
  left
  choose t Ht Ht_ne y Hy K_subdiv_L using K_move_L
  use t ⊔ₛ ∅
  have Ht_empty : (t ⊔ₛ ∅ : Finset (E × 𝕜)) ∈ (L ⋆ Z).faces :=
  by
    rw [simplicialJoin_sep]
    constructor
    rw [Set.mem_union]
    left; assumption
    constructor
    rw [Set.mem_union]
    right; apply Set.mem_singleton
    left; apply face_nonempty L t Ht
  use Ht_empty
  let Ht_empty_ne := @SimplexDisjoint.nonempty.left _ 𝕜 _ _ _ t Ht_ne
  use Ht_empty_ne
  use(y, 0)
  have Hy_0 : (y, 0) ∉ (L ⋆ Z : AbstractSimplicialComplex (E × 𝕜)).vertices :=
  by
    rw [simplicialJoin_vertices_mem_left]
    assumption
  use Hy_0
  rw [simplicial_iso_symm]
  apply
    @simplicial_iso_trans (E × 𝕜) (E × 𝕜) _ _ _ _ (@stellarSubdivision _ 𝕜 _ _ _ _ _ (L ⋆ Z) (t ⊔ₛ ∅) (y, 0) Ht_empty Hy_0)
      (@stellarSubdivision _ 𝕜 _ _ _ _ _ L t y Ht Hy ⋆ Z)
  rw [simplicial_iso_symm]
  apply @stellar_subdiv_distr_join_left _ 𝕜 <;> assumption
  apply simplicialJoin_iso_left
  rw [simplicial_iso_symm]
  assumption
  cases' K_move_L with K_move_L K_move_L
  right; left
  choose s Hs Hs_ne x Hx L_subdiv_K using K_move_L
  use s ⊔ₛ ∅
  have Hs_empty : (s ⊔ₛ ∅ : Finset (E × 𝕜)) ∈ (K ⋆ Z).faces :=
  by
    rw [simplicialJoin_sep]
    constructor
    rw [Set.mem_union]
    left; assumption
    constructor
    rw [Set.mem_union]
    right; apply Set.mem_singleton
    left; apply face_nonempty K s Hs
  use Hs_empty
  let Hs_empty_ne := @SimplexDisjoint.nonempty.left _ 𝕜 _ _ _ s Hs_ne
  use Hs_empty_ne
  use(x, 0)
  have Hx_0 : (x, 0) ∉ (K ⋆ Z : AbstractSimplicialComplex (E × 𝕜)).vertices :=
  by
    rw [simplicialJoin_vertices_mem_left]
    assumption
  use Hx_0
  rw [simplicial_iso_symm]
  apply
    @simplicial_iso_trans (E × 𝕜) (E × 𝕜) _ _ _ _ (@stellarSubdivision _ 𝕜 _ _ _ _ _ (K ⋆ Z) (s ⊔ₛ ∅) (x, 0) Hs_empty Hx_0)
      (@stellarSubdivision _ 𝕜 _ _ _ _ _ K s x Hs Hx ⋆ Z)
  rw [simplicial_iso_symm]
  apply @stellar_subdiv_distr_join_left _ 𝕜 <;> assumption
  apply simplicialJoin_iso_left
  rw [simplicial_iso_symm]
  assumption
  right; right
  apply simplicialJoin_iso_left
  assumption
  unfold StellarEquiv at *
  induction' Z_eq_W with K L Z_eq_K K_move_L H_ind
  rfl
  apply @Relation.ReflTransGen.tail _ _ _ (Y ⋆ K) (Y ⋆ L)
  apply H_ind
  simp only [StellarMove] at K_move_L ⊢
  cases' K_move_L with K_move_L K_move_L
  left
  choose t Ht Ht_ne y Hy K_subdiv_L using K_move_L
  use∅ ⊔ₛ t
  have Ht_empty : (∅ ⊔ₛ t : Finset (E × 𝕜)) ∈ (Y ⋆ L).faces :=
  by
    rw [simplicialJoin_sep]
    constructor
    rw [Set.mem_union]
    right; apply Set.mem_singleton
    constructor
    rw [Set.mem_union]
    left; assumption
    right; apply face_nonempty L t Ht
  use Ht_empty
  let Ht_empty_ne := @SimplexDisjoint.nonempty.right _ 𝕜 _ _ _ t Ht_ne
  use Ht_empty_ne
  use(y, 1)
  have Hy_1 : (y, 1) ∉ (Y ⋆ L : AbstractSimplicialComplex (E × 𝕜)).vertices :=
  by
    rw [simplicialJoin_vertices_mem_right]
    assumption
  use Hy_1
  rw [simplicial_iso_symm]
  apply
    @simplicial_iso_trans (E × 𝕜) (E × 𝕜) _ _ _ _ (@stellarSubdivision _ 𝕜 _ _ _ _ _ (Y ⋆ L) (∅ ⊔ₛ t) (y, 1) Ht_empty Hy_1)
      (Y ⋆ @stellarSubdivision _ 𝕜 _ _ _ _ _ L t y Ht Hy)
  rw [simplicial_iso_symm]
  apply @stellar_subdiv_distr_join_right _ 𝕜 <;> assumption
  apply simplicialJoin_iso_right
  rw [simplicial_iso_symm]
  assumption
  cases' K_move_L with K_move_L K_move_L
  right; left
  choose s Hs Hs_ne x Hx L_subdiv_K using K_move_L
  use∅ ⊔ₛ s
  have Hs_empty : (∅ ⊔ₛ s : Finset (E × 𝕜)) ∈ (Y ⋆ K).faces :=
  by
    rw [simplicialJoin_sep]
    constructor
    rw [Set.mem_union]
    right; apply Set.mem_singleton
    constructor
    rw [Set.mem_union]
    left; assumption
    right; apply face_nonempty K s Hs
  use Hs_empty
  let Hs_empty_ne := @SimplexDisjoint.nonempty.right _ 𝕜 _ _ _ s Hs_ne
  use Hs_empty_ne
  use(x, 1)
  have Hx_1 : (x, 1) ∉ (Y ⋆ K : AbstractSimplicialComplex (E × 𝕜)).vertices :=
  by
    rw [simplicialJoin_vertices_mem_right]
    assumption
  use Hx_1
  rw [simplicial_iso_symm]
  apply
    @simplicial_iso_trans (E × 𝕜) (E × 𝕜) _ _ _ _ (@stellarSubdivision _ 𝕜 _ _ _ _ _ (Y ⋆ K) (∅ ⊔ₛ s) (x, 1) Hs_empty Hx_1)
      (Y ⋆ @stellarSubdivision _ 𝕜 _ _ _ _ _ K s x Hs Hx)
  rw [simplicial_iso_symm]
  apply @stellar_subdiv_distr_join_right _ 𝕜 <;> assumption
  apply simplicialJoin_iso_right
  rw [simplicial_iso_symm]
  assumption
  right; right
  apply simplicialJoin_iso_right
  assumption

theorem simplicialJoin_stellarEquiv_left
    (X Y Z : AbstractSimplicialComplex E)
  : X ≅ₛₜ[𝕜] Y → (X ⋆ Z : AbstractSimplicialComplex (E × 𝕜)) ≅ₛₜ[𝕜] (Y ⋆ Z) :=
by
  intro X_eq_Y
  apply simplicialJoin_stellarEquiv X Y Z Z
  assumption
  rfl

theorem simplicialJoin_stellarEquiv_right
    (X Y Z : AbstractSimplicialComplex E)
  : X ≅ₛₜ[𝕜] Y → (Z ⋆ X : AbstractSimplicialComplex (E × 𝕜)) ≅ₛₜ[𝕜] Z ⋆ Y :=
by
  intro X_eq_Y
  apply simplicialJoin_stellarEquiv Z Z X Y
  rfl
  assumption

theorem stellar_subdiv_link_of_starComplement_left
    (X : AbstractSimplicialComplex E)
    (s t : Finset E) [s_ne : Nonempty s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (t_in_star_comp : t ∈ X\St(X, s).faces)
  : t ∉ ((π₁[𝕜] (boundary_disjoint_link X s)).coe
      ''ˢ (Lk(X, s) ⋆ ∂s)).faces →
        Lk(σ(X, s, x; 𝕜, s_in_X, x_nin_X), t).faces ⊆
          Lk(X, t).faces :=
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
    (X : AbstractSimplicialComplex E)
    (s t : Finset E) [s_ne : Nonempty s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (t_in_star_comp : t ∈ X\St(X, s).faces)
  : t ∉ ((π₁[𝕜] (boundary_disjoint_link X s)).coe
      ''ˢ (Lk(X, s) ⋆ ∂s)).faces →
        Lk(X, t).faces ⊆
          Lk(σ(X, s, x; 𝕜, s_in_X, x_nin_X), t).faces :=
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
        Lk(σ(X, s, x; 𝕜, s_in_X, x_nin_X), t).faces =
          Lk(X, t).faces :=
by
  intro t_nin_join
  rw [Set.Subset.antisymm_iff]
  constructor
  apply stellar_subdiv_link_of_starComplement_left <;>
  assumption
  apply stellar_subdiv_link_of_starComplement_right <;>
  assumption

theorem stellar_subdiv_link_of_barycenter_left
    (X : AbstractSimplicialComplex E)
    (s : Finset E) [s_ne : Nonempty s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
  : Lk(σ(X, s, x; 𝕜, s_in_X, x_nin_X), {x}).faces ⊆
      ((π₁[𝕜] (boundary_disjoint_link X s)).coe ''ˢ (Lk(X, s) ⋆ ∂s)).faces :=
by
  rw [Set.subset_def]
  intro a a_in_link
  simp only [link, Set.mem_sep_iff] at a_in_link
  choose a_in_subdiv xa_in_subdiv xa_disj using a_in_link
  simp only [stellarSubdivision, simplicialUnion, Set.mem_union] at xa_in_subdiv
  cases' xa_in_subdiv with xa_in_star_comp xa_in_join
  simp only [starComplement, Set.mem_sep_iff] at xa_in_star_comp
  choose xa_in_X s_nss_xa using xa_in_star_comp
  have contra : x ∈ X.vertices :=
  by
    rw [AbstractSimplicialComplex.mem_vertices]
    apply @X.down_closed ({x} ∪ a)
    assumption
    apply Finset.subset_union_left
    apply Finset.singleton_ne_empty
  contradiction
  rw [join_proj_disj_union_mem] at xa_in_join
  choose x' x'_in_join a' a'_in_join x₁ x₁_in_link a₁ a₁_in_link x_decomp a_decomp xa'_in_join
    xa₁_in_link using xa_in_join
  rw [Set.mem_union, Set.mem_singleton_iff, join_proj_disj_union_mem] at xa'_in_join
  cases' xa'_in_join with xa'_in_join xa'_empty

  choose x₃ x₃_in_barycenter a₃ a₃_in_barycenter x₂ x₂_in_bd a₂ a₂_in_bd x'_decomp a'_decomp
    xa₃_in_barycenter xa₂_in_bd using xa'_in_join
  subst x'_decomp
  subst a'_decomp
  have x₁_empty : x₁ = ∅ :=
  by
    have x₁_ss_x : x₁ ⊆ {x} :=
    by
      rw [x_decomp]
      apply Finset.subset_union_right
    rw [Finset.subset_singleton_iff] at x₁_ss_x
    cases' x₁_ss_x with x₁_empty x₁_eq_x
    assumption
    have contra : x ∈ X.vertices :=
    by
      simp only [x₁_eq_x, link, Set.mem_union, Set.mem_singleton_iff, Set.mem_sep_iff] at x₁_in_link
      cases' x₁_in_link with x₁_in_link x₁_empty
      choose x_in_X sx_in_X sx_disj using x₁_in_link
      rw [AbstractSimplicialComplex.mem_vertices]
      assumption
      have contra : {(x : E)} ≠ (∅ : Finset E) := by apply Finset.singleton_ne_empty
      contradiction
    contradiction
  have x₂_empty : x₂ = ∅ :=
  by
    have x₂_ss_x : x₂ ⊆ {x} :=
      by
      rw [x_decomp, Finset.union_comm, ← Finset.union_assoc]
      apply Finset.subset_union_right
    rw [Finset.subset_singleton_iff] at x₂_ss_x
    cases' x₂_ss_x with x₂_empty x₂_eq_x
    assumption
    have contra : x ∈ X.vertices :=
    by
      rw [x₂_eq_x, Set.mem_union, Set.mem_singleton_iff] at x₂_in_bd
      cases' x₂_in_bd with x₂_in_bd x₂_empty

      rw [AbstractSimplicialComplex.mem_vertices]
      apply simplex_if_in_subcomplex
      apply x₂_in_bd
      apply simplexBoundary_subcomplex
      assumption

      have contra : {(x : E)} ≠ (∅ : Finset E) := by apply Finset.singleton_ne_empty
      contradiction
    contradiction
  subst x₁_empty
  subst x₂_empty
  simp only [Finset.union_empty] at x_decomp
  subst x_decomp
  have a₃_empty : a₃ = ∅ :=
  by
    simp only [simplex, Set.mem_union, Set.mem_singleton_iff, Set.mem_diff, Finset.mem_coe, Finset.mem_powerset,
      Finset.subset_singleton_iff] at xa₃_in_barycenter
    cases' xa₃_in_barycenter with xa₃_eq_x xa₃_empty

    have xa₃_disj : {x} ∩ a₃ = ∅ :=
    by
      rw [← Finset.subset_empty]
      apply @Finset.Subset.trans _ _ ({x} ∩ a)
      rw [a_decomp, Finset.union_assoc]
      apply Finset.inter_subset_inter_left
      apply Finset.subset_union_left
      rw [Finset.subset_empty]
      assumption
    rw [singleton_inter_eq_empty_iff_not_mem] at xa₃_disj
    rw [Finset.union_eq_left, Finset.subset_singleton_iff] at xa₃_eq_x
    choose xa₃_eq_x xa₂_ne using xa₃_eq_x
    cases' xa₃_eq_x with xa₃_empty xa₃_eq_x
    contradiction
    cases' xa₃_eq_x with a₃_empty a₃_eq_x
    assumption
    have contra : x ∈ a₃ :=
    by
      rw [a₃_eq_x]
      apply Finset.mem_singleton_self
    contradiction

    rw [Finset.union_eq_empty] at xa₃_empty
    choose x_empty a₃_empty using xa₃_empty
    assumption
  subst a₃_empty
  rw [Finset.empty_union] at a_decomp
  rw [join_proj_mem]
  use a₁; constructor; assumption
  use a₂; constructor; assumption
  rw [Finset.union_comm]
  constructor; assumption
  apply face_nonempty _ _ a_in_subdiv

  -- xa'_empty case.
  rw [Finset.union_eq_empty] at xa'_empty
  choose x'_empty a'_empty using xa'_empty
  subst x'_empty a'_empty
  rw [Finset.empty_union] at a_decomp x_decomp
  subst x_decomp a_decomp
  rw [join_proj_mem]
  use a; constructor; assumption
  use ∅; constructor
  rw [Set.mem_union]
  right; apply Set.mem_singleton
  constructor
  rw [Finset.union_empty]
  apply face_nonempty _ _ a_in_subdiv

theorem stellar_subdiv_link_of_barycenter_right
    (X : AbstractSimplicialComplex E)
    (s : Finset E) [s_ne : Nonempty s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
  : ((π₁[𝕜] (boundary_disjoint_link X s)).coe ''ˢ (Lk(X, s) ⋆ ∂s)).faces ⊆
      Lk(σ(X, s, x; 𝕜, s_in_X, x_nin_X), {x}).faces :=
by
  rw [Set.subset_def]
  intro a a_in_img
  rw [join_proj_mem] at a_in_img
  choose a₁ a₁_in_link a₂ a₂_in_bd a_decomp a_ne using a_in_img
  rw [Set.mem_union, Set.mem_singleton_iff] at a₁_in_link a₂_in_bd
  simp only [link, Set.mem_sep_iff, stellarSubdivision, simplicialUnion, Set.mem_union]
  constructor; right
  simp only [join_proj_mem, Set.mem_union, Set.mem_singleton_iff]
  use ∅ ∪ a₂; constructor

  cases' a₂_in_bd with a₂_in_bd a₂_empty
  left; use ∅; constructor; right; rfl
  use a₂; constructor; left; assumption
  constructor; rfl
  rw [Finset.empty_union]
  apply face_nonempty _ _ a₂_in_bd

  right; rw [a₂_empty, Finset.union_empty]

  use a₁; constructor; assumption
  rw [Finset.empty_union, Finset.union_comm]
  constructor <;> assumption

  constructor; right
  simp only [join_proj_mem, Set.mem_union, Set.mem_singleton_iff]
  use {x} ∪ a₂; constructor; left
  use {x}; constructor; left
  simp only [simplex, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe]
  constructor
  apply Finset.mem_powerset_self
  apply Finset.singleton_ne_empty
  use a₂; constructor; assumption
  constructor; rfl
  rw [ne_eq, Finset.union_eq_empty, not_and_or]
  left; apply Finset.singleton_ne_empty

  use a₁; constructor; assumption
  rw [a_decomp, Finset.union_comm a₁ a₂, ← Finset.union_assoc]
  constructor; rfl
  rw [ne_eq, Finset.union_assoc, Finset.union_eq_empty, not_and_or]
  left; apply Finset.singleton_ne_empty
  rw [singleton_inter_eq_empty_iff_not_mem, a_decomp]
  by_contra x_in_a
  rw [Finset.mem_union] at x_in_a
  have contra : x ∈ X.vertices :=
  by
    rw [vertex_iff_in_simplex]
    cases' x_in_a with x_in_a₁ x_in_a₂
    use a₁; constructor
    apply simplex_if_in_subcomplex

    cases' a₁_in_link with a₁_in_link a₁_empty
    apply a₁_in_link

    rw [a₁_empty] at x_in_a₁
    contradiction

    apply link_subcomplex
    assumption
    use a₂; constructor
    apply simplex_if_in_subcomplex

    cases' a₂_in_bd with a₂_in_bd a₂_empty
    apply a₂_in_bd

    rw [a₂_empty] at x_in_a₂
    contradiction

    apply simplexBoundary_subcomplex
    assumption
    assumption
  contradiction

theorem stellar_subdiv_link_of_barycenter
    (X : AbstractSimplicialComplex E)
    (s : Finset E) [s_ne : Nonempty s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
  : Lk(σ(X, s, x; 𝕜, s_in_X, x_nin_X), {x}).faces =
      ((π₁[𝕜] (boundary_disjoint_link X s)).coe ''ˢ (Lk(X, s) ⋆ ∂s)).faces :=
by
  rw [Set.Subset.antisymm_iff]
  constructor
  apply stellar_subdiv_link_of_barycenter_left
  apply stellar_subdiv_link_of_barycenter_right

theorem star_boundary_is_join_left
    (X : AbstractSimplicialComplex E)
    (s : Finset E) [s_ne : Nonempty s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
  : (X\St(X, s) ∩
      ((π₁[𝕜] (@barycenter_join_boundary_disjoint_link _ _ 𝕜 _ _ _ _ X s x s_in_X x_nin_X)).coe
        ''ˢ (((π₁[𝕜] (barycenter_disjoint_boundary X s x s_in_X x_nin_X)).coe
          ''ˢ (simplex {x} ⋆ ∂s)) ⋆
              Lk(X, s)))).faces ⊆
      ((π₁[𝕜] (boundary_disjoint_link X s)).coe ''ˢ (Lk(X, s) ⋆ ∂s)).faces :=
by
  rw [Set.subset_def]
  intro t t_in_inter
  simp only [AbstractSimplicialComplex.instHasInter, simplicialInter, Set.mem_inter_iff] at t_in_inter
  choose t_in_star_comp t_in_join using t_in_inter
  simp only [join_proj_mem] at t_in_join
  choose t' t'_in_join t₁ t₁_in_link t_decomp t_ne using t_in_join

  rw [Set.mem_union, Set.mem_singleton_iff, join_proj_mem] at t'_in_join
  cases' t'_in_join with t'_in_join t'_empty

  choose t₃ t₃_in_barycenter t₂ t₂_in_bd t'_decomp t'_ne using t'_in_join
  subst t'_decomp
  simp only [starComplement, Set.mem_sep_iff] at t_in_star_comp
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
  rw [join_proj_mem]
  use t₁; constructor; assumption
  use t₂; constructor; assumption
  rw [Finset.union_comm]
  constructor <;> assumption

  subst t'_empty
  rw [Finset.empty_union] at t_decomp
  subst t_decomp
  rw [join_proj_mem]
  use t; constructor; assumption
  use ∅; constructor
  rw [Set.mem_union]
  right; apply Set.mem_singleton
  constructor
  rw [Finset.union_empty]
  assumption

theorem star_boundary_is_join_right
    (X : AbstractSimplicialComplex E)
    (s : Finset E) [s_ne : Nonempty s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
  : ((π₁[𝕜] (boundary_disjoint_link X s)).coe ''ˢ (Lk(X, s) ⋆ ∂s)).faces ⊆
      (X\St(X, s) ∩
        ((π₁[𝕜] (@barycenter_join_boundary_disjoint_link _ _ 𝕜 _ _ _ _ X s x s_in_X x_nin_X)).coe
            ''ˢ ((π₁[𝕜] (barycenter_disjoint_boundary X s x s_in_X x_nin_X)).coe
              ''ˢ (simplex {x} ⋆ ∂s) ⋆
                Lk(X, s)))).faces :=
by
  rw [Set.subset_def]
  intro t t_in_join
  rw [join_proj_mem] at t_in_join
  choose t₁ t₁_in_link t₂ t₂_in_bd t_decomp t_ne using t_in_join
  simp only [AbstractSimplicialComplex.instHasInter, simplicialInter, Set.mem_inter_iff]
  constructor
  simp only [starComplement, Set.mem_sep_iff]
  simp only [link, Set.mem_union, Set.mem_singleton_iff, Set.mem_sep_iff] at t₁_in_link
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

  simp only [join_proj_mem, Set.mem_union, Set.mem_singleton_iff]
  use ∅ ∪ t₂; constructor
  rw [Set.mem_union, Set.mem_singleton_iff] at t₂_in_bd
  cases' t₂_in_bd with t₂_in_bd t₂_empty

  left; use ∅; constructor; right; rfl
  use t₂; constructor; left; assumption
  constructor; rfl
  rw [Finset.empty_union]
  apply face_nonempty _ _ t₂_in_bd

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
      ((π₁[𝕜] (@barycenter_join_boundary_disjoint_link _ _ 𝕜 _ _ _ _ X s x s_in_X x_nin_X)).coe
        ''ˢ (((π₁[𝕜] (barycenter_disjoint_boundary X s x s_in_X x_nin_X)).coe
          ''ˢ (simplex {x} ⋆ ∂s)) ⋆
              Lk(X, s)))).faces =
      ((π₁[𝕜] (boundary_disjoint_link X s)).coe ''ˢ (Lk(X, s) ⋆ ∂s)).faces :=
by
  rw [Set.Subset.antisymm_iff]
  constructor
  apply star_boundary_is_join_left <;> assumption
  apply star_boundary_is_join_right <;> assumption

theorem star_boundary_diff_ne
    {X : AbstractSimplicialComplex E}
    {s t : Finset E} [s_ne : Nonempty s]
    {s_in_X : s ∈ X.faces}
  : t ∈ ((π₁[𝕜] (boundary_disjoint_link X s)).coe ''ˢ (Lk(X, s) ⋆ ∂s)).faces →
      Nonempty ↥(s \ t) :=
by
  intro t_in_star_bd
  rw [join_proj_mem] at t_in_star_bd
  choose t₁ t₁_in_link t₂ t₂_in_bd t_decomp t_ne using t_in_star_bd
  simp only [link, Set.mem_sep_iff, Set.mem_union, Set.mem_singleton_iff] at t₁_in_link
  cases' t₁_in_link with t₁_in_link t₁_empty

  choose t₁_in_X st₁_in_X st₁_disj using t₁_in_link
  rw [Set.mem_union, Set.mem_singleton_iff, simplexBoundary_mem_iff_subset] at t₂_in_bd
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
  simp only [Finset.nonempty_coe_sort, Finset.nonempty_iff_ne_empty, ne_eq, Finset.eq_empty_iff_forall_notMem,
    not_forall, not_not] at s_ne
  choose a a_in_s using s_ne
  use a; use a_in_s
  specialize st₁_disj a a_in_s
  assumption

  rw [t₁_empty, Finset.empty_union] at t_decomp
  subst t_decomp
  rw [Set.mem_union, Set.mem_singleton_iff, simplexBoundary_mem_iff_subset] at t₂_in_bd
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

theorem star_boundary_mem_link
    {X : AbstractSimplicialComplex E}
    {s t : Finset E} [s_ne : Nonempty s]
    {s_in_X : s ∈ X.faces}
  : t ∈ ((π₁[𝕜] (boundary_disjoint_link X s)).coe ''ˢ (Lk(X, s) ⋆ ∂s)).faces →
      s \ t ∈ Lk(X, t).faces :=
by
  intro t_in_star_bd
  rw [join_proj_mem] at t_in_star_bd
  choose t₁ t₁_in_link t₂ t₂_in_bd t_decomp t_ne using t_in_star_bd
  simp only [link, Set.mem_sep_iff, Set.mem_union, Set.mem_singleton_iff] at t₁_in_link ⊢
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
  apply face_nonempty X s s_in_X

  constructor
  rw [Finset.union_sdiff_self_eq_union, t_decomp, Finset.union_assoc]
  simp only [simplexBoundary, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe,
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
  apply face_nonempty X s s_in_X

  constructor
  rw [Finset.union_sdiff_self_eq_union, t_decomp, Finset.union_assoc]
  simp only [simplexBoundary, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe,
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
  apply is_subcomplex_vertices
  apply link_subcomplex

theorem stellar_subdiv_anticomm_link_left_ac
    (X : AbstractSimplicialComplex E)
    (s t : Finset E) [s_ne : Nonempty s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (t_in_star_bd : t ∈ ((π₁[𝕜] (boundary_disjoint_link X s)).coe ''ˢ (Lk(X, s) ⋆ ∂s)).faces)
  : ∀ u : Finset E,
      u ∈ (starComplement X s).faces →
        t ∪ u ∈ (starComplement X s).faces →
          t ∩ u = ∅ →
            u ∈
              σ(Lk(X, t), s \ t, x; 𝕜,
                @star_boundary_mem_link _ _ _ _ _ _ _ X s t s_ne s_in_X t_in_star_bd,
                not_mem_link_vertices x_nin_X).faces :=
by
  intro u u_in_star_comp tu_in_star_comp tu_disj
  simp only [link, stellarSubdivision, starComplement, simplicialUnion] at u_in_star_comp tu_in_star_comp ⊢
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
    (t₂_in_bd : t₂ ⊂ s)
    (tu_in_join :
      t₂ ∪ u₂ ∈ ((π₁[𝕜] (barycenter_disjoint_boundary X s x s_in_X x_nin_X)).coe ''ˢ (simplex {x} ⋆ ∂s)).faces)
    (t_decomp : t = t₁ ∪ t₂)
    (u_decomp : u = u₁ ∪ u₂)
  : ¬s \ t₂ ⊆ u :=
by
  rw [join_proj_disj_union_mem] at tu_in_join
  choose t₃ t₃_in_barycenter u₃ u₃_in_barycenter t₂ t₂_in_bd u₂ u₂_in_bd tu₂_decomp using tu_in_join
  choose t₂_decomp u₂_decomp tu₃_in_barycenter tu₂_in_bd using tu₂_decomp
  have u₃_empty : u₃ = ∅ :=
    by
    simp only [simplex, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at u₃_in_barycenter
    cases' u₃_in_barycenter with u₃_empty u₃_eq_x
    exact u₃_empty
    have contra : x ∈ vertices X := by
      rw [vertex_iff_singleton]
      apply X.subset_closed u
      exact u_in_X
      rw [u_decomp, u₂_decomp, u₃_eq_x, ← Finset.union_assoc, Finset.union_comm u₁ {x},
        Finset.union_assoc]
      apply Finset.subset_union_left
    contradiction
  have t₃_empty : t₃ = ∅ :=
    by
    simp only [simplex, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at
      t₃_in_barycenter
    cases' t₃_in_barycenter with t₃_empty t₃_eq_x
    exact t₃_empty
    have contra : x ∈ vertices X := by
      rw [vertex_iff_singleton]
      apply X.subset_closed t
      exact t_in_X
      rw [t_decomp, t₂_decomp, t₃_eq_x, ← Finset.union_assoc, Finset.union_comm t₁ {x},
        Finset.union_assoc]
      apply Finset.subset_union_left
    contradiction
  subst u₃
  subst t₃
  rw [Finset.empty_union] at t₂_decomp u₂_decomp tu₃_in_barycenter
  rw [← u₂_decomp, ← t₂_decomp, simplexBoundary_mem_iff_subset] at tu₂_in_bd
  subst u₂_decomp
  subst t₂_decomp
  have u₂_ss_st₂_sdiff : u₂ ⊂ s \ t₂ :=
    by
    rw [Finset.ssubset_iff_subset_ne] at tu₂_in_bd ⊢
    choose tu₂_ss_s tu₂_ne_s using tu₂_in_bd
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
    have H1 : s = s ∪ t₂ := by
      symm
      rw [Finset.union_eq_left]
      rw [Finset.ssubset_def] at t₂_in_bd
      tauto
    rw [H1] at tu₂_ne_s
    revert tu₂_ne_s
    contrapose
    simp only [not_ne_iff]
    rw [← @Finset.sdiff_union_self_eq_union _ _ s]
    exact congr_arg fun a : Finset α => a ∪ t₂
  rw [← Finset.lt_iff_ssubset, finset.partial_order.lt_iff_le_not_le, Finset.le_iff_subset,
    Finset.le_iff_subset] at u₂_ss_st₂_sdiff
  choose u₂_ss_st₂ st₂_nss_u₂ using u₂_ss_st₂_sdiff
  rw [Finset.not_subset] at st₂_nss_u₂ ⊢
  choose y y_in_st₂ y_nin_u₂ using st₂_nss_u₂
  use y; use y_in_st₂
  rw [u_decomp, Finset.not_mem_union]
  constructor
  rw [Finset.eq_empty_iff_forall_not_mem] at su₁_disj
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

theorem stellar_subdiv_anticomm_link_left_ad
    (X : AbstractSimplicialComplex E)
    (s t : Finset E) [s_ne : Nonempty s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (t_in_X : t ∈ X.faces)
    (t_in_star_bd : t ∈ ((π₁[𝕜] (boundary_disjoint_link X s)).coe ''ˢ (Lk(X, s) ⋆ ∂s)).faces)
  : ∀ u : Finset E,
      u ∈ (starComplement X s).faces →
        t ∪ u ∈ ((π₁[𝕜] (@barycenter_join_boundary_disjoint_link _ _ 𝕜 _ _ _ _ X s x s_in_X x_nin_X)).coe
                  ''ˢ (((π₁[𝕜] (barycenter_disjoint_boundary X s x s_in_X x_nin_X)).coe
                    ''ˢ (simplex {x} ⋆ ∂s)) ⋆
                      Lk(X, s))).faces →
          t ∩ u = ∅ →
            u ∈ σ(Lk(X, t), s \ t, x; 𝕜,
                  @star_boundary_mem_link _ _ _ _ _ _ _ X s t s_ne s_in_X t_in_star_bd,
                  not_mem_link_vertices x_nin_X).faces :=
by
  intro u u_in_star_comp tu_in_join tu_disj
  simp only [link, stellarSubdivision, starComplement, AbstractSimplicialComplex.instHasUnion,
    simplicialUnion] at u_in_star_comp tu_in_join ⊢
  simp only [Set.mem_union, Set.mem_setOf] at u_in_star_comp ⊢
  choose u_in_X s_nss_u using u_in_star_comp

  rw [join_proj_disj_union_mem] at tu_in_join
  choose t'₂ t'₂_in_join u'₂ u'₂_in_join t₁ t₁_in_link u₁ u₁_in_link tu_decomp using tu_in_join
  choose t_decomp u_decomp tu_in_join tu_in_link using tu_decomp
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf] at t₁_in_link u₁_in_link tu_in_link
  choose tu_in_link tu_ne using tu_in_link
  simp only [join_proj_mem, Set.mem_union, Set.mem_singleton_iff] at u'₂_in_join t'₂_in_join

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
    · rw [t'₂_empty, Finset.empty_ssubset, ← Finset.nonempty_coe_sort]
      assumption

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
    · rw [u'₂_empty, Finset.empty_ssubset, ← Finset.nonempty_coe_sort]
      assumption

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
    · simp only [join_proj_mem, Set.mem_union, Set.mem_singleton_iff] at u'₂_in_join
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

    · sorry

    sorry
  · sorry


  cases' u'₂_in_join with u'₂_in_join u'₂_empty
  · simp only [join_proj_mem, Set.mem_union, Set.mem_singleton_iff] at u'₂_in_join
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
    subst u₃_empty; rw [Finset.empty_union] at u'_decomp; subst u'_decomp

    sorry
  · sorry

  -- old
  -- intro u u_in_star_comp tu_in_join tu_disj
  -- simp only [link, stellarSubdivision, starComplement, simplicialUnion] at u_in_star_comp tu_in_join ⊢
  -- simp only [Set.mem_union, Set.mem_sep_iff] at u_in_star_comp ⊢
  -- choose u_in_X s_nss_u using u_in_star_comp
  -- rw [join_proj_disj_union_mem] at tu_in_join
  -- choose t'₂ t'₂_in_join u'₂ u'₂_in_join t₁ t₁_in_link u₁ u₁_in_link tu_decomp using tu_in_join
  -- choose t_decomp u_decomp tu_in_join tu_in_link using tu_decomp
  -- simp only [Set.mem_sep_iff] at t₁_in_link u₁_in_link tu_in_link
  -- choose t₁_in_X st₁_in_X st₁_disj using t₁_in_link
  -- choose u₁_in_X su₁_in_X su₁_disj using u₁_in_link
  -- choose tu₁_in_X stu₁_in_X stu₁_disj using tu_in_link
  -- rw [join_proj_mem] at t'₂_in_join u'₂_in_join
  -- choose u₃ u₃_in_barycenter u₂ u₂_in_bd u'_decomp using u'₂_in_join
  -- choose t₃ t₃_in_barycenter t₂ t₂_in_bd t'_decomp using t'₂_in_join
  -- subst u'_decomp
  -- subst t'_decomp
  -- rw [simplexBoundary_mem_iff_subset] at u₂_in_bd t₂_in_bd
  -- have u₃_empty : u₃ = ∅ :=
  -- by
  --   simp only [simplex, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at u₃_in_barycenter
  --   cases' u₃_in_barycenter with u₃_empty u₃_eq_x
  --   exact u₃_empty
  --   have contra : x ∈ vertices X := by
  --     rw [vertex_iff_singleton]
  --     apply X.subset_closed u
  --     exact u_in_X
  --     rw [u_decomp, u₃_eq_x, Finset.union_assoc]
  --     apply Finset.subset_union_left
  --   contradiction
  -- have t₃_empty : t₃ = ∅ :=
  -- by
  --   simp only [simplex, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at t₃_in_barycenter
  --   cases' t₃_in_barycenter with t₃_empty t₃_eq_x
  --   exact t₃_empty
  --   have contra : x ∈ vertices X :=
  --   by
  --     rw [vertex_iff_singleton]
  --     apply X.subset_closed t
  --     exact t_in_X
  --     rw [t_decomp, t₃_eq_x, Finset.union_assoc]
  --     apply Finset.subset_union_left
  --   contradiction
  -- subst u₃
  -- subst t₃
  -- simp only [Finset.empty_union] at u_decomp t_decomp tu_in_join
  -- rw [Finset.union_comm] at u_decomp t_decomp
  -- left; constructor; constructor
  -- exact u_in_X
  -- constructor
  -- exact
  --   stellar_subdiv_anticomm_link_left_ad_tu_in_X X s t u t₁ u₁ t₂ u₂ stu₁_in_X t₂_in_bd u₂_in_bd
  --     t_decomp u_decomp
  -- exact tu_disj
  -- rw [t_decomp, Finset.sdiff_union_distrib]
  -- have st₁_sdiff_ident : s \ t₁ = s :=
  -- by
  --   apply Finset.sdiff_eq_self_of_disjoint
  --   rw [Finset.disjoint_iff_inter_eq_empty]
  --   exact st₁_disj
  -- rw [st₁_sdiff_ident, Finset.inter_sdiff, Finset.inter_self]
  -- exact
  --   stellar_subdiv_anticomm_link_left_ad_st_nss_u X s t u t₁ u₁ t₂ u₂ x s_in_X x_nin_X t_in_X u_in_X
  --     tu_disj su₁_disj t₂_in_bd tu_in_join t_decomp u_decomp

theorem stellar_subdiv_anticomm_link_left_bc
    (X : AbstractSimplicialComplex E)
    (s t : Finset E) [s_ne : Nonempty s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (t_in_X : t ∈ X.faces)
    (t_in_star_bd : t ∈ ((π₁[𝕜] (boundary_disjoint_link X s)).coe ''ˢ (Lk(X, s) ⋆ ∂s)).faces)
  : ∀ u : Finset E,
      u ∈ ((π₁[𝕜] (@barycenter_join_boundary_disjoint_link _ _ 𝕜 _ _ _ _ X s x s_in_X x_nin_X)).coe
            ''ˢ (((π₁[𝕜] (barycenter_disjoint_boundary X s x s_in_X x_nin_X)).coe
              ''ˢ (simplex {x} ⋆ ∂s)) ⋆
                Lk(X, s))).faces →
        t ∪ u ∈ (starComplement X s).faces →
          t ∩ u = ∅ →
            u ∈ σ(Lk(X, t), s \ t, x; 𝕜,
                  @star_boundary_mem_link _ _ _ _ _ _ _ X s t s_ne s_in_X t_in_star_bd,
                  not_mem_link_vertices x_nin_X).faces :=
by
  intro u u_in_join tu_in_star_comp tu_disj
  simp only [stellarSubdivision, starComplement, AbstractSimplicialComplex.instHasUnion, simplicialUnion] at u_in_join tu_in_star_comp ⊢
  simp only [Set.mem_union, Set.mem_setOf] at tu_in_star_comp ⊢
  choose tu_in_X s_nss_tu using tu_in_star_comp

  rw [join_proj_mem] at u_in_join
  choose u'₂ u'₂_in_join u₁ u₁_in_link u_decomp u_ne using u_in_join
  rw [Set.mem_union, Set.mem_singleton_iff, link, Set.mem_setOf] at u₁_in_link
  simp only [Set.mem_union, Set.mem_singleton_iff, join_proj_mem] at u'₂_in_join

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
    (X : AbstractSimplicialComplex E)
    (s t u t₁ u₁ t₂ u₂ u₃ : Finset E) [s_ne : Nonempty ↥s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (t_in_X : t ∈ X.faces)
    (t_in_star_bd : t ∈ ((π₁[𝕜] (boundary_disjoint_link X s)).coe ''ˢ (Lk(X, s) ⋆ ∂s)).faces)
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
  have H1 : s = s ∪ t₂ := by
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
    (s t u t₁ u₁ t₂ u₂ u₃ : Finset E) [s_ne : Nonempty ↥s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (t_in_X : t ∈ X.faces)
    (t_in_star_bd : t ∈ ((π₁[𝕜] (boundary_disjoint_link X s)).coe ''ˢ (Lk(X, s) ⋆ ∂s)).faces)
    (tu_disj : t ∩ u = ∅)
    (stu₁_in_X : s ∪ (t₁ ∪ u₁) ∈ X.faces)
    (t_decomp : t = t₂ ∪ t₁)
    (u_decomp : u = u₃ ∪ u₂ ∪ u₁)
    (t₂_ss_s : t₂ ⊆ s)
  : t ∪ u₁ ∈ X.faces ∧ t ∩ u₁ = ∅ :=
by
  constructor
  rw [t_decomp]
  apply X.subset_closed (s ∪ t₁ ∪ u₁)
  rw [Finset.union_assoc]
  apply stu₁_in_X
  simp only [Finset.union_assoc]
  apply Finset.union_subset_union_left
  apply t₂_ss_s
  rw [← Finset.subset_empty]
  apply @Finset.Subset.trans _ _ (t ∩ u)
  apply Finset.inter_subset_inter_left
  rw [u_decomp, Finset.union_comm]
  apply Finset.subset_union_left
  rw [Finset.subset_empty]
  apply tu_disj

theorem stellar_subdiv_anticomm_link_left_bd_stu_mem_link
    (X : AbstractSimplicialComplex E)
    (s t u t₁ u₁ t₂ u₂ u₃ : Finset E) [s_ne : Nonempty ↥s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (t_in_X : t ∈ X.faces)
    (t_in_star_bd : t ∈ ((π₁[𝕜] (boundary_disjoint_link X s)).coe ''ˢ (Lk(X, s) ⋆ ∂s)).faces)
    (tu_disj : t ∩ u = ∅)
    (su₁_disj : s ∩ u₁ = ∅)
    (stu₁_in_X : s ∪ (t₁ ∪ u₁) ∈ X.faces)
    (t_decomp : t = t₂ ∪ t₁)
    (u_decomp : u = u₃ ∪ u₂ ∪ u₁)
    (st₁_sdiff_ident : s \ t₁ = s)
    (t₂_ss_s : t₂ ⊆ s)
  : s \ t ∪ u₁ ∈ Lk(X, t).faces ∧ s \ t ∩ u₁ = ∅ :=
by
  constructor; constructor
  apply X.subset_closed (s ∪ t₁ ∪ u₁)
  rw [Finset.union_assoc]
  apply stu₁_in_X
  apply @Finset.Subset.trans _ _ (s ∪ u₁)
  apply Finset.union_subset_union_left
  apply Finset.sdiff_subset
  rw [Finset.union_assoc, Finset.union_comm t₁ u₁, ← Finset.union_assoc]
  apply Finset.subset_union_left
  constructor
  apply X.subset_closed (s ∪ t₁ ∪ u₁)
  rw [Finset.union_assoc]
  apply stu₁_in_X
  rw [t_decomp, Finset.sdiff_union_distrib, st₁_sdiff_ident, Finset.inter_comm]
  rw [Finset.inter_sdiff, Finset.inter_self, ← Finset.union_assoc, Finset.union_assoc t₂ t₁]
  rw [Finset.union_comm t₁ (s \ t₂), ← Finset.union_assoc]
  rw [Finset.union_assoc, Finset.union_assoc s t₁]
  apply Finset.union_subset_union_left
  apply Finset.subset_of_eq
  apply Finset.union_sdiff_of_subset
  apply t₂_ss_s
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
    (s t : Finset E) [s_ne : Nonempty s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (t_in_X : t ∈ X.faces)
    (t_in_star_bd : t ∈ ((π₁[𝕜] (boundary_disjoint_link X s)).coe ''ˢ (Lk(X, s) ⋆ ∂s)).faces)
  : ∀ u : Finset E,
      u ∈ ((π₁[𝕜] (@barycenter_join_boundary_disjoint_link _ _ 𝕜 _ _ _ _ X s x s_in_X x_nin_X)).coe
            ''ˢ (((π₁[𝕜] (barycenter_disjoint_boundary X s x s_in_X x_nin_X)).coe
              ''ˢ (simplex {x} ⋆ ∂s)) ⋆
                Lk(X, s))).faces →
        t ∪ u ∈ ((π₁[𝕜] (@barycenter_join_boundary_disjoint_link _ _ 𝕜 _ _ _ _ X s x s_in_X x_nin_X)).coe
                  ''ˢ ((π₁[𝕜] (barycenter_disjoint_boundary X s x s_in_X x_nin_X)).coe
                    ''ˢ (simplex {x} ⋆ ∂s) ⋆
                     Lk(X, s))).faces →
          t ∩ u = ∅ →
            u ∈ σ(Lk(X, t), s \ t, x; 𝕜,
                  @star_boundary_mem_link _ _ _ _ _ _ _ X s t s_ne s_in_X t_in_star_bd,
                  not_mem_link_vertices x_nin_X).faces :=
by
  intro u u_in_join tu_in_join tu_disj
  simp only [link, stellarSubdivision, starComplement, simplicialUnion] at u_in_join tu_in_join ⊢
  rw [join_proj_disj_union_mem] at tu_in_join
  choose t'₂ t'₂_in_join u'₂ u'₂_in_join t₁ t₁_in_link u₁ u₁_in_link tu_decomp using tu_in_join
  choose t_decomp u_decomp tu_in_join tu_in_link using tu_decomp
  simp only [Set.mem_sep_iff] at t₁_in_link u₁_in_link tu_in_link
  choose t₁_in_X st₁_in_X st₁_disj using t₁_in_link
  choose u₁_in_X su₁_in_X su₁_disj using u₁_in_link
  choose tu₁_in_X stu₁_in_X stu₁_disj using tu_in_link
  rw [join_proj_disj_union_mem] at tu_in_join
  choose t₃ t₃_in_barycenter u₃ u₃_in_barycenter t₂ t₂_in_bd u₂ u₂_in_bd tu₂_decomp using tu_in_join
  choose t₂_decomp u₂_decomp tu₃_in_barycenter tu₂_in_bd using tu₂_decomp
  have t₃_empty : t₃ = ∅ :=
  by
    simp only [simplex, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at t₃_in_barycenter
    cases' t₃_in_barycenter with t₃_empty t₃_eq_x
    apply t₃_empty
    have contra : x ∈ vertices X := by
      rw [vertex_iff_singleton]
      apply X.subset_closed t
      apply t_in_X
      rw [t_decomp, t₂_decomp, t₃_eq_x, Finset.union_assoc]
      apply Finset.subset_union_left
    contradiction
  subst t₃_empty
  simp only [Finset.empty_union] at t₂_decomp u₂_decomp tu₃_in_barycenter
  rw [simplexBoundary_mem_iff_subset] at tu₂_in_bd u₂_in_bd t₂_in_bd
  rw [t₂_decomp] at *
  rw [u₂_decomp] at *
  clear t₂_decomp u₂_decomp u_in_join u'₂_in_join t'₂_in_join tu₃_in_barycenter t₃_in_barycenter t'₂ u'₂
  right
  rw [join_proj_mem]
  have tu₂_disj : t₂ ∩ u₂ = ∅ :=
  by
    rw [← Finset.subset_empty]
    apply @Finset.Subset.trans _ _ (t ∩ u)
    apply Finset.inter_subset_inter
    rw [t_decomp]
    apply @Finset.subset_union_left _ _ t₂ t₁
    rw [u_decomp, Finset.union_assoc, Finset.union_comm, Finset.union_assoc]
    apply @Finset.subset_union_left _ _ u₂ (u₁ ∪ u₃)
    rw [Finset.subset_empty]
    apply tu_disj
  have st₁_sdiff_ident : s \ t₁ = s :=
  by
    apply Finset.sdiff_eq_self_of_disjoint
    rw [Finset.disjoint_iff_inter_eq_empty]
    apply st₁_disj
  have u₂_ss_st₂_sdiff : u₂ ⊂ s \ t₂ :=
  by
    apply
      stellar_subdiv_anticomm_link_left_bd_u_ss_st X s t u t₁ u₁ t₂ u₂ u₃ x s_in_X x_nin_X t_in_X
        t_in_star_bd tu_disj t₂_in_bd tu₂_in_bd t_decomp u_decomp
  have u₂_ss_st : u₂ ⊂ s \ t :=
  by
    rw [t_decomp, Finset.sdiff_union_distrib, st₁_sdiff_ident, Finset.inter_comm,
      Finset.inter_sdiff, Finset.inter_self]
    apply u₂_ss_st₂_sdiff
  rw [Finset.ssubset_def] at t₂_in_bd
  choose t₂_ss_s s_nss_t₂ using t₂_in_bd
  use u₃ ∪ u₂; constructor
  rw [join_proj_disj_union_mem]
  use u₃; constructor; apply u₃_in_barycenter
  use∅; constructor; apply simplicialComplex_empty_simplex
  use∅; constructor; apply simplicialComplex_empty_simplex
  use u₂; constructor
  rw [@simplexBoundary_mem_iff_subset _ _ _ _ (star_boundary_diff_ne t_in_star_bd)]
  apply u₂_ss_st
  constructor; symm; apply Finset.union_empty
  constructor; symm; apply Finset.empty_union
  constructor; rw [Finset.union_empty]
  apply u₃_in_barycenter
  rw [Finset.empty_union,
    @simplexBoundary_mem_iff_subset _ _ _ _ (star_boundary_diff_ne t_in_star_bd)]
  apply u₂_ss_st
  use u₁; constructor; constructor; constructor
  apply u₁_in_X
  apply
    stellar_subdiv_anticomm_link_left_bd_u_mem_link X s t u t₁ u₁ t₂ u₂ u₃ x s_in_X x_nin_X t_in_X
      t_in_star_bd tu_disj stu₁_in_X t_decomp u_decomp t₂_ss_s
  apply
    stellar_subdiv_anticomm_link_left_bd_stu_mem_link X s t u t₁ u₁ t₂ u₂ u₃ x s_in_X x_nin_X t_in_X
      t_in_star_bd tu_disj su₁_disj stu₁_in_X t_decomp u_decomp st₁_sdiff_ident t₂_ss_s
  apply u_decomp

theorem star_boundary_mem_subdiv
    {X : AbstractSimplicialComplex E}
    {s t : Finset E} [s_ne : Nonempty s]
    {x : E}
    {s_in_X : s ∈ X.faces}
    {x_nin_X : x ∉ X.vertices}
  : t ∈ ((π₁[𝕜] (boundary_disjoint_link X s)).coe ''ˢ (Lk(X, s) ⋆ ∂s)).faces →
      t ∈ σ(X, s, x; 𝕜, s_in_X, x_nin_X).faces :=
by
  intro t_in_star_bd
  rw [join_proj_mem] at t_in_star_bd
  choose t₁ t₁_in_link t₂ t₂_in_bd t_decomp t_ne using t_in_star_bd
  simp only [stellarSubdivision, AbstractSimplicialComplex.instHasUnion, simplicialUnion, Set.mem_union, join_proj_mem]
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

theorem stellar_subdiv_anticomm_link_left
    (X : AbstractSimplicialComplex E)
    (s t : Finset E) [s_ne : Nonempty s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (t_in_X : t ∈ X.faces)
    (t_in_star_bd : t ∈ ((π₁[𝕜] (boundary_disjoint_link X s)).coe ''ˢ (Lk(X, s) ⋆ ∂s)).faces)
  : Lk(σ(X, s, x; 𝕜, s_in_X, x_nin_X), t).faces ⊆
      σ(Lk(X, t), s \ t, x; 𝕜,
          @star_boundary_mem_link _ _ _ _ _ _ _ X s t s_ne s_in_X t_in_star_bd,
          not_mem_link_vertices x_nin_X).faces :=
by
  simp only [stellarSubdivision, AbstractSimplicialComplex.instHasUnion, simplicialUnion]
  simp only [Set.subset_def]
  intro u u_in_link
  simp only [link, Set.mem_sep_iff] at u_in_link
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
      u ∈ (starComplement Lk(X, t) (s \ t)).faces →
        u ∈ Lk(σ(X, s, x; 𝕜, s_in_X, x_nin_X), t).faces :=
by
  intro u u_in_star_comp
  simp only [link, starComplement, stellarSubdivision, simplicialUnion] at u_in_star_comp ⊢
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
    (s t : Finset E) [s_ne : Nonempty s]
    (s_in_X : s ∈ X.faces)
    (t_in_X : t ∈ X.faces)
    (t_in_star_bd : t ∈ ((π₁[𝕜] (boundary_disjoint_link X s)).coe ''ˢ (Lk(X, s) ⋆ ∂s)).faces)
  : s \ t ∈ X.faces :=
by
  apply X.down_closed s_in_X
  apply Finset.sdiff_subset
  rw [join_proj_mem] at t_in_star_bd
  choose t₁ t₁_in_link t₂ t₂_in_bd t_decomp t_ne using t_in_star_bd
  subst t_decomp

  rw [link, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf] at t₁_in_link
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
    · rw [t₂_empty, Finset.sdiff_empty, ← Finset.nonempty_iff_ne_empty, ← Finset.nonempty_coe_sort]
      assumption

  rw [Finset.sdiff_union_distrib, st₁_eq_s, ← Finset.inter_sdiff_assoc, Finset.inter_self]
  assumption

theorem stellar_subdiv_anticomm_link_right_f
    (X : AbstractSimplicialComplex E)
    (s t : Finset E) [s_ne : Nonempty s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (t_in_X : t ∈ X.faces)
    (t_in_star_bd : t ∈ ((π₁[𝕜] (boundary_disjoint_link X s)).coe ''ˢ (Lk(X, s) ⋆ ∂s)).faces)
  : ∀ u : Finset E,
      u ∈ ((π₁[𝕜] (@barycenter_join_boundary_disjoint_link _ _ 𝕜 _ _ _ _ Lk(X, t) (s \ t) x
                    (@star_boundary_mem_link _ _ _ _ _ _ _ X s t s_ne s_in_X t_in_star_bd)
                    (not_mem_link_vertices x_nin_X))).coe
            ''ˢ (((π₁[𝕜] (barycenter_disjoint_boundary X (s \ t) x
                          (star_boundary_mem_compl X s t s_in_X t_in_X t_in_star_bd)
                          x_nin_X)).coe
              ''ˢ (simplex {x} ⋆ ∂(s \ t))) ⋆
                Lk(Lk(X, t), s \ t))).faces →
        u ∈ Lk(σ(X, s, x; 𝕜, s_in_X, x_nin_X), t).faces :=
by
  intro u u_in_join
  simp only [link, starComplement, stellarSubdivision, AbstractSimplicialComplex.instHasUnion, simplicialUnion] at u_in_join ⊢
  simp only [Set.mem_union, Set.mem_sep_iff, Set.mem_setOf_eq]
  rw [join_proj_mem] at u_in_join
  choose u'₂ u'₂_in_join u₁ u₁_in_link u_decomp u_ne using u_in_join
  simp only [Set.mem_union, Set.mem_singleton_iff, join_proj_mem] at u'₂_in_join
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_sep_iff, Set.mem_setOf_eq] at u₁_in_link

  rw [join_proj_mem] at t_in_star_bd
  choose t₁ t₁_in_link t₂ t₂_in_bd t_decomp t_ne using t_in_star_bd
  simp only [link, Set.mem_union, Set.mem_singleton_iff, Set.mem_sep_iff] at t₁_in_link
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
    · rw [t₂_empty, Finset.sdiff_empty, ← Finset.nonempty_iff_ne_empty, ← Finset.nonempty_coe_sort]
      assumption

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
        @simplexBoundary_mem_iff_subset _ _ (s \ t₂) u₂ (by rw [Finset.nonempty_coe_sort, Finset.nonempty_iff_ne_empty]; assumption)] at u₂_in_bd

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
        constructor; apply face_nonempty X s s_in_X
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
    rw [join_proj_mem]
    use u₃ ∪ u₂; constructor; left
    rw [join_proj_mem]
    use u₃; constructor
    rw [Set.mem_union, Set.mem_singleton_iff]
    assumption
    use u₂; constructor
    rw [Set.mem_union, Set.mem_singleton_iff]
    cases' u₂_in_bd with u₂_in_bd u₂_empty
    · left; apply simplex_if_in_subcomplex (∂(s \ (t₁ ∪ t₂)))
      assumption
      simp only [AbstractSimplicialComplex.instHasSubset, IsSubcomplex]
      apply subsimplex_boundary_subcomplex
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
    left; apply face_nonempty X s s_in_X

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
    right; apply face_nonempty X u₁ u_in_X

    constructor; right
    rw [join_proj_mem]
    use (u₃ ∪ (u₂ ∪ t₂)); constructor
    rw [Set.mem_union, join_proj_mem]
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
        apply face_nonempty X s s_in_X

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
    left; apply face_nonempty X u₁ u_in_X

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
    left; apply face_nonempty X s s_in_X

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

    rw [join_proj_mem]
    use (u₃ ∪ u₂); constructor
    rw [Set.mem_union, join_proj_mem]
    left; use u₃; constructor
    rw [Set.mem_union, Set.mem_singleton_iff]
    assumption
    use u₂; constructor
    rw [Set.mem_union, Set.mem_singleton_iff]
    cases' u₂_in_bd with u₂_in_bd u₂_empty
    · left; apply simplex_if_in_subcomplex (∂(s \ (t₁ ∪ t₂)))
      assumption
      simp only [AbstractSimplicialComplex.instHasSubset, IsSubcomplex]
      apply subsimplex_boundary_subcomplex
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
    rw [join_proj_mem]
    use (u₃ ∪ (u₂ ∪ t₂)); constructor
    rw [Set.mem_union, join_proj_mem]
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
        apply face_nonempty X s s_in_X

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
    (X : AbstractSimplicialComplex E)
    (s t : Finset E) [s_ne : Nonempty s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (t_in_X : t ∈ X.faces)
    (t_in_star_bd : t ∈ ((π₁[𝕜] (boundary_disjoint_link X s)).coe ''ˢ (Lk(X, s) ⋆ ∂s)).faces)
  : σ(Lk(X, t), s \ t, x; 𝕜,
        @star_boundary_mem_link _ _ _ _ _ _ _ X s t s_ne s_in_X t_in_star_bd,
        not_mem_link_vertices x_nin_X).faces ⊆
      Lk(σ(X, s, x; 𝕜, s_in_X, x_nin_X), t).faces :=
by
  simp only [stellarSubdivision, AbstractSimplicialComplex.instHasUnion, simplicialUnion]
  simp only [Set.subset_def]
  intro u u_in_subdiv
  simp only [Set.mem_union] at u_in_subdiv
  cases' u_in_subdiv with u_in_star_comp u_in_join

  -- Cases E + F, resp.
  apply stellar_subdiv_anticomm_link_right_e <;> assumption
  apply stellar_subdiv_anticomm_link_right_f <;> assumption

theorem stellar_subdiv_anticomm_link
    (X : AbstractSimplicialComplex E)
    (s t : Finset E) [s_ne : Nonempty s]
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (t_in_X : t ∈ X.faces)
    (t_in_star_bd : t ∈ ((π₁[𝕜] (boundary_disjoint_link X s)).coe ''ˢ (Lk(X, s) ⋆ ∂s)).faces)
  : Lk(σ(X, s, x; 𝕜, s_in_X, x_nin_X), t).faces =
      σ(Lk(X, t), s \ t, x; 𝕜,
          @star_boundary_mem_link _ _ _ _ _ _ _ X s t s_ne s_in_X t_in_star_bd,
          not_mem_link_vertices x_nin_X).faces :=
by
  apply Set.eq_of_subset_of_subset
  apply stellar_subdiv_anticomm_link_left <;> assumption
  apply stellar_subdiv_anticomm_link_right <;> assumption
