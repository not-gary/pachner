import Mathlib.Tactic
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Pachner.SimplicialComplex
import Pachner.SimplicialMap
import Pachner.SimplicialSubcomplex

variable {E F 𝕜 : Type _}
variable [DecidableEq E] [DecidableEq F] [DecidableEq 𝕜]
variable [AddCommGroup E]
variable [Ring 𝕜] [Nontrivial 𝕜]

def stellarSubdivision
    (X : AbstractSimplicialComplex E)
    (s : Finset E)
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
  : AbstractSimplicialComplex E :=
    X\St(X, s) ∪
      (π₁ (@barycenter_join_boundary_disjoint_link _ _ 𝕜 _ _ _ _ X s x s_in_X x_nin_X)).coe ''ˢ
        (((π₁ (barycenter_disjoint_boundary X s x s_in_X x_nin_X)).coe ''ˢ (simplex {x} ⋆ ∂s : AbstractSimplicialComplex (E × 𝕜)))
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
    Fintype ((π₁ (barycenter_disjoint_boundary X s x s_in_X x_nin_X)).coe ''ˢ (simplex {x} ⋆ ∂s : AbstractSimplicialComplex (E × 𝕜))).faces :=
    by apply @SimplicialCoe.Fintype _ _ _ _ barycenter_bd_fin
  have link_fin : Fintype ↥Lk(X, s).faces := by apply link.fintype
  have proj_link_fin :
    Fintype
      ↥((π₁ (barycenter_disjoint_boundary X s x s_in_X x_nin_X)).coe ''ˢ (simplex {x} ⋆ ∂s : AbstractSimplicialComplex (E × 𝕜))
        ⋆ Lk(X, s) : AbstractSimplicialComplex (E × 𝕜)).faces :=
    by apply @simplicialJoin.fintype _ _ _ _ _ _ _ _ proj_bary_bd_fin _ link_fin
  have join_fin :
    Fintype
      ↥((π₁ (@barycenter_join_boundary_disjoint_link E _ 𝕜 _ _ _ _ X s x s_in_X x_nin_X)).coe ''ˢ
          (((π₁ (barycenter_disjoint_boundary X s x s_in_X x_nin_X)).coe ''ˢ (simplex {x} ⋆ ∂s : AbstractSimplicialComplex (E × 𝕜)))
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

theorem stellar_subdiv_vertices (X : SimplicialComplex α) (s : Finset α) [s_ne : Nonempty s] (x : α)
    (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X) :
    s.card > 1 → vertices σ(X, s, x; s_ne, s_in_X, x_nin_X) = vertices X ∪ {x} :=
  by
  intro s_nontriv
  rw [Set.Subset.antisymm_iff]
  constructor
  apply stellar_subdiv_subset_vertices
  rw [Set.subset_def]
  intro a a_in_union
  rw [Set.mem_union, Set.mem_singleton_iff, vertex_iff_in_simplex] at a_in_union
  simp only [vertex_iff_in_simplex, stellarSubdivision, simplicialUnion, Set.mem_union,
    join_proj_mem]
  cases' a_in_union with a_in_X a_eq_x
  choose t t_in_X a_in_t using a_in_X
  use{a}; constructor; left
  simp only [starComplement, Set.mem_sep_iff]
  constructor
  apply X.subset_closed t
  assumption
  rw [Finset.singleton_subset_iff]
  assumption
  have a_le_s : ¬s.card ≤ 1 := not_le.mpr s_nontriv
  rw [← Finset.card_singleton a] at a_le_s
  revert a_le_s
  contrapose
  simp only [Classical.not_not]
  apply Finset.card_le_card
  apply Finset.mem_singleton_self
  use{x}; constructor; right
  use{x}; constructor
  use{x}; constructor
  simp only [simplex, Finset.mem_coe]
  apply Finset.mem_powerset_self
  use∅; constructor
  apply simplicialComplex_empty_simplex
  rw [Finset.union_empty]
  use∅; constructor
  apply simplicialComplex_empty_simplex
  rw [Finset.union_empty]
  rw [a_eq_x]
  apply Finset.mem_singleton_self

def barycenterStar (X : SimplicialComplex α) (s : Finset α) [s_ne : Nonempty s] (x : α)
    (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X) : Set (Finset α) :=
  {t ∈ σ(X, s, x; s_ne, s_in_X, x_nin_X).simplices | x ∈ t}

instance barycenterStar.fintype (X : SimplicialComplex α) (s : Finset α) [s_ne : Nonempty s] (x : α)
    (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X)
    [Fintype σ(X, s, x; s_ne, s_in_X, x_nin_X).simplices] :
    Fintype (barycenterStar X s x s_in_X x_nin_X) :=
  by
  simp only [barycenterStar]
  apply Set.fintypeSep

/- ././././Mathport/Syntax/Translate/Expr.lean:373:4: unsupported set replacement {(«expr ∪ »(s, «expr \ »(t, {x}))) | t «expr ∈ » barycenter_star[barycenter_star] X s x s_in_X x_nin_X} -/
def barycenterWeld (X : SimplicialComplex α) (s : Finset α) [s_ne : Nonempty s] (x : α)
    (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X) : Set (Finset α) :=
  "././././Mathport/Syntax/Translate/Expr.lean:373:4: unsupported set replacement {(«expr ∪ »(s, «expr \\ »(t, {x}))) | t «expr ∈ » barycenter_star[barycenter_star] X s x s_in_X x_nin_X}"

theorem barycenterWeld_as_union (X : SimplicialComplex α) (s : Finset α) [s_ne : Nonempty s] (x : α)
    (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X) :
    barycenterWeld X s x s_in_X x_nin_X =
      ⋃ t ∈ barycenterStar X s x s_in_X x_nin_X, {s ∪ t \ {x}} :=
  by
  simp only [barycenterWeld, Set.ext_iff, Set.mem_iUnion, Set.mem_setOf, Set.mem_singleton_iff]
  intro t
  constructor
  intro t_in_weld
  choose u u_in_star t_su using t_in_weld
  use u; constructor; assumption
  symm; assumption
  intro t_in_union
  choose u u_in_star t_su using t_in_union
  use u; constructor; assumption
  symm; assumption

instance barycenterWeld.fintype (X : SimplicialComplex α) (s : Finset α) [s_ne : Nonempty s] (x : α)
    (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X)
    [Fintype σ(X, s, x; s_ne, s_in_X, x_nin_X).simplices] :
    Fintype (barycenterWeld X s x s_in_X x_nin_X) :=
  by
  rw [barycenterWeld_as_union]
  apply Set.fintypeBiUnion
  intro t t_in_star
  apply Unique.fintype

theorem stellar_weld_simplices (X : SimplicialComplex α) (s : Finset α) [s_ne : Nonempty s] (x : α)
    (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X) :
    X.simplices =
      {t ∈ σ(X, s, x; s_ne, s_in_X, x_nin_X).simplices | x ∉ t} ∪
        barycenterWeld X s x s_in_X x_nin_X :=
  by
  simp only [barycenterWeld, Set.ext_iff, Set.mem_union, Set.mem_sep_iff, Set.mem_setOf]
  intro t
  constructor
  · intro t_in_X
    by_cases s_ss_t : s ⊆ t
    right
    use t \ s ∪ {x}; constructor
    simp only [barycenterStar, Set.mem_sep_iff, stellarSubdivision, simplicialUnion, Set.mem_union,
      join_proj_mem]
    constructor; right
    use{x} ∪ ∅; constructor
    use{x}; constructor
    simp only [simplex, Finset.mem_coe]
    apply Finset.mem_powerset_self
    use∅; constructor; apply simplicialComplex_empty_simplex
    rfl
    use t \ s; constructor
    simp only [link, Set.mem_sep_iff]
    constructor
    apply X.subset_closed t
    assumption
    apply Finset.sdiff_subset
    constructor
    rw [Finset.union_sdiff_of_subset]
    assumption
    assumption
    apply Finset.inter_sdiff_self
    rw [Finset.union_empty, Finset.union_comm]
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
    use t; constructor <;> assumption
    assumption
    left; constructor
    simp only [stellarSubdivision, simplicialUnion, Set.mem_union]
    left
    simp only [starComplement, Set.mem_sep_iff]
    constructor <;> assumption
    revert x_nin_X
    contrapose
    simp only [Classical.not_not]
    intro x_in_t
    rw [vertex_iff_in_simplex]
    use t; constructor <;> assumption
  · intro t_in_union
    cases' t_in_union with t_in_subdiv t_join_s
    choose t_in_subdiv x_nin_t using t_in_subdiv
    simp only [stellarSubdivision, simplicialUnion, Set.mem_union] at t_in_subdiv
    cases' t_in_subdiv with t_in_star_comp t_in_join
    simp only [starComplement, Set.mem_sep_iff] at t_in_star_comp
    choose t_in_X s_nss_t using t_in_star_comp
    assumption
    simp only [join_proj_mem] at t_in_join
    choose t' t'_in_join t₁ t₁_in_link t_decomp using t_in_join
    choose t₃ t₃_in_barycenter t₂ t₂_in_bd t'_decomp using t'_in_join
    subst t'_decomp
    have t₃_empty : t₃ = ∅ :=
      by
      simp only [simplex, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at
        t₃_in_barycenter
      cases' t₃_in_barycenter with t₃_empty t₃_eq_x
      assumption
      have contra : x ∈ t := by
        simp only [t_decomp, Finset.mem_union, t₃_eq_x]
        left; left
        apply Finset.mem_singleton_self
      contradiction
    subst t₃_empty
    rw [Finset.empty_union] at t_decomp
    simp only [link, Set.mem_sep_iff] at t₁_in_link
    choose t₁_in_X st₁_in_X st₁_disj using t₁_in_link
    rw [simplexBoundary_mem_iff_subset, Finset.ssubset_iff_subset_ne] at t₂_in_bd
    choose t₂_ss_s t₂_ne_s using t₂_in_bd
    rw [t_decomp]
    apply X.subset_closed (s ∪ t₁)
    assumption
    apply Finset.union_subset_union_left
    assumption
    choose u u_in_star su_eq_t using t_join_s
    simp only [barycenterStar, Set.mem_sep_iff] at u_in_star
    choose u_in_subdiv x_in_u using u_in_star
    simp only [stellarSubdivision, simplicialUnion, Set.mem_union] at u_in_subdiv
    cases' u_in_subdiv with u_in_star_comp u_in_join
    simp only [starComplement, Set.mem_sep_iff] at u_in_star_comp
    choose u_in_X s_nss_u using u_in_star_comp
    have contra : x ∈ vertices X := by
      rw [vertex_iff_in_simplex]
      use u; constructor <;> assumption
    contradiction
    simp only [join_proj_mem] at u_in_join
    choose u' u'_in_join u₁ u₁_in_link u_decomp using u_in_join
    choose u₃ u₃_in_barycenter u₂ u₂_in_bd u'_decomp using u'_in_join
    subst u'_decomp
    simp only [link, Set.mem_sep_iff] at u₁_in_link
    choose u₁_in_X su₁_in_X su₁_disj using u₁_in_link
    rw [simplexBoundary_mem_iff_subset, Finset.ssubset_iff_subset_ne] at u₂_in_bd
    choose u₂_ss_s u₂_ne_s using u₂_in_bd
    have xu₁_rw : u₁ \ {x} = u₁ :=
      by
      rw [Finset.sdiff_eq_self_iff_disjoint, Finset.disjoint_singleton_right]
      by_contra
      have contra : x ∈ vertices X := by
        rw [vertex_iff_in_simplex]
        use u₁; constructor <;> assumption
      contradiction
    have xu₂_rw : u₂ \ {x} = u₂ :=
      by
      rw [Finset.sdiff_eq_self_iff_disjoint, Finset.disjoint_singleton_right]
      by_contra
      have contra : x ∈ vertices X := by
        rw [vertex_iff_in_simplex]
        use u₂; constructor
        apply X.subset_closed s <;> assumption
        assumption
      contradiction
    rw [← su_eq_t, u_decomp]
    simp only [Finset.union_sdiff_distrib]
    rw [xu₁_rw, xu₂_rw]
    have su₂_rw : s ∪ u₂ = s := by
      rw [Finset.union_eq_left]
      assumption
    simp only [simplex, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at
      u₃_in_barycenter
    cases' u₃_in_barycenter with u₃_empty u₃_eq_x
    rw [u₃_empty, Finset.empty_sdiff, Finset.empty_union, ← Finset.union_assoc, su₂_rw]
    assumption
    rw [u₃_eq_x, Finset.sdiff_self, Finset.empty_union, ← Finset.union_assoc, su₂_rw]
    assumption

instance stellarSubdivision.fintypeConverse (X : SimplicialComplex α) (s : Finset α)
    [s_ne : Nonempty s] (x : α) (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X)
    [Fintype σ(X, s, x; s_ne, s_in_X, x_nin_X).simplices] : Fintype X.simplices :=
  by
  rw [stellar_weld_simplices X s x s_in_X x_nin_X]
  apply Set.fintypeUnion

theorem barycenter_vertex_stellar_subdiv (X : SimplicialComplex α) (s : Finset α)
    [s_ne : Nonempty s] (x : α) (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X) :
    x ∈ vertices σ(X, s, x; s_ne, s_in_X, x_nin_X) :=
  by
  rw [vertex_iff_singleton]
  simp only [stellarSubdivision, simplicialUnion, Set.mem_union, join_proj_mem]
  right
  use{x}; constructor
  use{x}; constructor
  simp only [simplex, Finset.mem_coe]
  apply Finset.mem_powerset_self
  use∅; constructor
  apply simplicialComplex_empty_simplex
  rw [Finset.union_empty]
  use∅; constructor
  apply simplicialComplex_empty_simplex
  rw [Finset.union_empty]

theorem stellar_subdiv_iso_simp (X : SimplicialComplex α) (Y : SimplicialComplex β) (s : Finset α)
    [s_ne : Nonempty s] (t : Finset β) [t_ne : Nonempty t] (x : α) (y : β)
    (s_in_X : s ∈ X.simplices) (t_in_Y : t ∈ Y.simplices) (x_nin_X : x ∉ vertices X)
    (y_nin_Y : y ∉ vertices Y) (f : SimplicialMap X Y) (f_iso : IsSimplicialIso f) :
    Finset.image f.map s = t →
      f.map x = y →
        IsSimplicialMap σ(X, s, x; s_ne, s_in_X, x_nin_X) σ(Y, t, y; t_ne, t_in_Y, y_nin_Y) f.map :=
  by
  intro fs_t fx_y
  let f_iso' := f_iso
  unfold IsSimplicialIso at f_iso'
  choose g gf_inv using f_iso'
  have g_iso : IsSimplicialIso g := by apply iso_inv_is_iso f g f_iso gf_inv
  unfold IsInverseSimplicialIso at gf_inv
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply,
    id.def] at gf_inv
  choose gf_id fg_id using gf_inv
  have f_inj : Set.InjOn f.map s :=
    by
    apply @Set.LeftInvOn.injOn _ _ _ _ g.map
    simp only [Set.LeftInvOn]
    intro x x_in_s
    have x_in_vert : x ∈ vertices X :=
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
  use z; constructor
  use z_in_s
  intro w w_in_u
  rw [@Set.InjOn.eq_iff _ _ (vertices X)]
  revert w_in_u z_nin_u
  contrapose
  simp only [Classical.not_forall, Classical.not_not, exists_prop, and_imp]
  intro z_nin_u w_eq_z
  rw [w_eq_z]
  assumption
  apply iso_is_injective_vertices
  assumption
  rw [vertex_iff_in_simplex]
  use u; constructor <;> assumption
  rw [vertex_iff_in_simplex]
  use s; constructor <;> assumption
  right
  simp only [join_proj_mem] at u_in_join ⊢
  choose u' u'_in_join u₁ u₁_in_link u_decomp using u_in_join
  choose u₃ u₃_in_barycenter u₂ u₂_in_bd u'_decomp using u'_in_join
  subst u'_decomp
  use Finset.image f.map (u₃ ∪ u₂); constructor
  use Finset.image f.map u₃; constructor
  simp only [simplex, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at
    u₃_in_barycenter ⊢
  cases' u₃_in_barycenter with u₃_empty u₃_x
  left
  rw [u₃_empty]
  apply Finset.image_empty
  right
  rw [u₃_x, ← fx_y]
  apply Finset.image_singleton
  use Finset.image f.map u₂; constructor
  simp only [simplexBoundary, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe,
    Finset.mem_powerset] at u₂_in_bd ⊢
  cases' u₂_in_bd with u₂_in_bd u₂_empty
  left
  choose u₂_ss_s u₂_ne_s using u₂_in_bd
  simp only [← fs_t]
  constructor
  apply Finset.image_subset_image
  assumption
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
  have Hs : ∃ (x : α) (H : x ∈ s), f.map x = f.map a :=
    by
    use a; constructor; assumption
    rfl
  specialize fs_ss_fu Hs
  simp only [Finset.mem_val, Set.mem_image, ← exists_prop]
  assumption
  simp only [u₂_empty, Finset.image_empty]
  right; rfl
  apply Finset.image_union
  use Finset.image f.map u₁; constructor
  simp only [link, Set.mem_sep_iff] at u₁_in_link ⊢
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
  rw [u_decomp, Finset.image_union]

theorem stellar_subdiv_iso (X : SimplicialComplex α) (Y : SimplicialComplex β) (s : Finset α)
    [s_ne : Nonempty s] (t : Finset β) [t_ne : Nonempty t] (x : α) (y : β)
    (s_in_X : s ∈ X.simplices) (t_in_Y : t ∈ Y.simplices) (x_nin_X : x ∉ vertices X)
    (y_nin_Y : y ∉ vertices Y) (f : SimplicialMap X Y) (f_iso : IsSimplicialIso f)
    (g : SimplicialMap Y X) (gf_inv : IsInverseSimplicialIso f g) :
    Finset.image f.map s = t →
      f.map x = y →
        g.map y = x → σ(X, s, x; s_ne, s_in_X, x_nin_X) ≅ σ(Y, t, y; t_ne, t_in_Y, y_nin_Y) :=
  by
  intro fs_t fx_y gy_x
  have g_iso : IsSimplicialIso g := by apply iso_inv_is_iso f g f_iso gf_inv
  unfold IsInverseSimplicialIso at gf_inv
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply,
    id.def] at gf_inv
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
    have c_in_X : c ∈ vertices X := by
      rw [vertex_iff_in_simplex]
      use s; constructor <;> assumption
    specialize gf_id c_in_X
    rw [gf_id] at gb_a
    rw [gb_a] at c_in_s
    assumption
    intro a_in_s
    use f.map a; constructor
    use a; constructor
    assumption
    rfl
    have a_in_X : a ∈ vertices X := by
      rw [vertex_iff_in_simplex]
      use s; constructor <;> assumption
    specialize gf_id a_in_X
    assumption
  let f_subdiv :=
    SimplicialMap.mk f.map
      (stellar_subdiv_iso_simp X Y s t x y s_in_X t_in_Y x_nin_X y_nin_Y f f_iso fs_t fx_y)
  let g_subdiv :=
    SimplicialMap.mk g.map
      (stellar_subdiv_iso_simp Y X t s y x t_in_Y s_in_X y_nin_Y x_nin_X g g_iso gt_s gy_x)
  unfold IsSimpliciallyIso
  use f_subdiv
  unfold IsSimplicialIso
  use g_subdiv
  unfold IsInverseSimplicialIso
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply,
    id.def]
  constructor
  · intro a a_in_X
    have a_in_union : a ∈ vertices X ∪ {x} :=
      by
      apply stellar_subdiv_subset_vertices X s
      apply a_in_X
    rw [Set.mem_union, Set.mem_singleton_iff] at a_in_union
    cases' a_in_union with a_in_X a_eq_x
    specialize gf_id a_in_X
    assumption
    subst a_eq_x
    rw [fx_y, gy_x]
  · intro a a_in_Y
    have a_in_union : a ∈ vertices Y ∪ {y} :=
      by
      apply stellar_subdiv_subset_vertices Y t
      apply a_in_Y
    rw [Set.mem_union, Set.mem_singleton_iff] at a_in_union
    cases' a_in_union with a_in_Y a_eq_y
    specialize fg_id a_in_Y
    assumption
    subst a_eq_y
    rw [gy_x, fx_y]

def stellarSubdivOfSingletonMap (x y : α) : α → α := fun a : α => if a = x then y else a

theorem stellar_subdiv_of_singleton_forward_simp (X : SimplicialComplex α) (x y : α)
    (y_in_X : {y} ∈ X.simplices) (x_nin_X : x ∉ vertices X) :
    IsSimplicialMap
      σ(X, {y}, x; by apply Finset.Nonempty.coe_sort; apply Finset.singleton_nonempty, y_in_X,
        x_nin_X)
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
      have contra : x ∈ vertices X := by
        rw [vertex_iff_in_simplex]
        use s; constructor
        apply simplex_if_in_subcomplex
        apply s_in_star_comp
        apply starComplement_subcomplex
        assumption
      contradiction
      assumption
    simp only [b_ne_x, if_false] at fb_a
    rw [fb_a] at b_in_s
    assumption
    intro a_in_s
    rw [Finset.mem_image]
    use a; constructor; assumption
    have a_ne_x : a ≠ x := by
      by_cases a_eq_x : a = x
      rw [a_eq_x] at a_in_s
      have contra : x ∈ vertices X := by
        rw [vertex_iff_in_simplex]
        use s; constructor
        apply simplex_if_in_subcomplex
        apply s_in_star_comp
        apply starComplement_subcomplex
        assumption
      contradiction
      assumption
    simp only [a_ne_x, if_false]
  rw [id_s]
  apply simplex_if_in_subcomplex
  apply s_in_star_comp
  apply starComplement_subcomplex
  -- join case.
  simp only [join_proj_mem] at s_in_join
  choose s' s'_in_join s₁ s₁_in_link s_decomp using s_in_join
  choose s₃ s₃_in_barycenter s₂ s₂_in_bd s'_decomp using s'_in_join
  subst s'_decomp
  simp only [simplexBoundary, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe,
    Finset.mem_powerset] at s₂_in_bd
  have s₂_empty : s₂ = ∅ := by
    cases' s₂_in_bd with s₂_in_bd s₂_empty
    choose s₂_ss_y s₂_ne_y using s₂_in_bd
    rw [Finset.subset_singleton_iff] at s₂_ss_y
    cases' s₂_ss_y with s₂_empty contra
    assumption
    contradiction
    assumption
  subst s₂_empty
  rw [Finset.union_empty] at s_decomp
  simp only [link, Set.mem_sep_iff] at s₁_in_link
  choose s₁_in_X ys₁_in_X ys₁_disj using s₁_in_link
  simp only [simplex, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at
    s₃_in_barycenter
  cases' s₃_in_barycenter with s₃_empty s₃_eq_x
  · subst s₃_empty
    rw [Finset.empty_union] at s_decomp
    subst s_decomp
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
        have contra : x ∈ vertices X := by
          rw [vertex_iff_in_simplex]
          use s; constructor <;> assumption
        contradiction
        assumption
      simp only [b_ne_x, if_false] at fb_a
      rw [fb_a] at b_in_s
      assumption
      intro a_in_s
      rw [Finset.mem_image]
      use a; constructor; assumption
      have a_ne_x : a ≠ x := by
        by_cases a_eq_x : a = x
        rw [a_eq_x] at a_in_s
        have contra : x ∈ vertices X := by
          rw [vertex_iff_in_simplex]
          use s; constructor <;> assumption
        contradiction
        assumption
      simp only [a_ne_x, if_false]
    rw [id_s]
    assumption
  · subst s₃_eq_x
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
        have contra : x ∈ vertices X := by
          rw [vertex_iff_in_simplex]
          use s₁; constructor <;> assumption
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
        have contra : x ∈ vertices X := by
          rw [vertex_iff_in_simplex]
          use s₁; constructor <;> assumption
        contradiction
        assumption
      use a; constructor
      right; assumption
      simp only [a_ne_x, if_false]
    rw [id_s]
    assumption

theorem stellar_subdiv_of_singleton_inverse_simp (X : SimplicialComplex α) (x y : α)
    (y_in_X : {y} ∈ X.simplices) (x_nin_X : x ∉ vertices X) :
    IsSimplicialMap X
      σ(X, {y}, x; by apply Finset.Nonempty.coe_sort; apply Finset.singleton_nonempty, y_in_X,
        x_nin_X)
      (stellarSubdivOfSingletonMap y x) :=
  by
  simp only [IsSimplicialMap, stellarSubdivision, simplicialUnion, Set.mem_union]
  intro s s_in_X
  by_cases y_in_s : y ∈ s
  -- y ∈ s case.
  right
  simp only [join_proj_mem]
  use{x}; constructor
  use{x}; constructor
  simp only [simplex, Finset.mem_coe]
  apply Finset.mem_powerset_self
  use∅; constructor
  apply simplicialComplex_empty_simplex
  rw [Finset.union_empty]
  use s \ {y}; constructor
  simp only [link, Set.mem_sep_iff]
  constructor
  apply X.subset_closed s
  assumption
  apply Finset.sdiff_subset
  constructor
  rw [Finset.union_sdiff_of_subset]
  assumption
  rw [Finset.singleton_subset_iff]
  assumption
  rw [Finset.inter_comm]
  apply Finset.sdiff_inter_self
  have s_decomp : s = {y} ∪ s \ {y} :=
    by
    rw [Finset.union_sdiff_of_subset]
    rw [Finset.singleton_subset_iff]
    assumption
  rw [s_decomp, stellarSubdivOfSingletonMap, Finset.ext_iff]
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
    simp only [a_ne_y, if_false]
  simp only [id_s, starComplement, Set.mem_sep_iff]
  constructor
  assumption
  rw [Finset.singleton_subset_iff]
  assumption

theorem stellar_subdiv_of_singleton (X : SimplicialComplex α) (x y : α) (y_in_X : {y} ∈ X.simplices)
    (x_nin_X : x ∉ vertices X) :
    σ(X, {y}, x; by apply Finset.Nonempty.coe_sort; apply Finset.singleton_nonempty, y_in_X,
        x_nin_X) ≅
      X :=
  by
  let f_subdiv :
    SimplicialMap
      σ(X, {y}, x; by apply Finset.Nonempty.coe_sort; apply Finset.singleton_nonempty, y_in_X,
        x_nin_X)
      X :=
    SimplicialMap.mk (stellarSubdivOfSingletonMap x y)
      (stellar_subdiv_of_singleton_forward_simp X x y y_in_X x_nin_X)
  let g_subdiv :
    SimplicialMap X
      σ(X, {y}, x; by apply Finset.Nonempty.coe_sort; apply Finset.singleton_nonempty, y_in_X,
        x_nin_X) :=
    SimplicialMap.mk (stellarSubdivOfSingletonMap y x)
      (stellar_subdiv_of_singleton_inverse_simp X x y y_in_X x_nin_X)
  unfold IsSimpliciallyIso
  use f_subdiv; use g_subdiv
  unfold IsInverseSimplicialIso
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply,
    id.def]
  constructor
  · intro a a_in_subdiv
    simp only [stellarSubdivOfSingletonMap]
    split_ifs
    symm
    assumption
    rw [stellar_subdiv_of_singleton_vertices, Set.mem_union, Set.mem_diff_singleton,
      Set.mem_singleton_iff] at a_in_subdiv
    cases' a_in_subdiv with a_in_X contra
    choose a_in_X contra using a_in_X
    contradiction
    contradiction
    rfl
  · intro a a_in_X
    simp only [stellarSubdivOfSingletonMap]
    split_ifs
    symm
    assumption
    rw [h_1] at a_in_X
    contradiction
    rfl

@[simp]
def StellarMove : SimplicialComplex α → SimplicialComplex α → Prop :=
  fun X Y : SimplicialComplex α =>
  (∃ (t : Finset α) (Ht : t ∈ Y.simplices) (Ht_ne : Nonempty t) (y : α) (Hy : y ∉ vertices Y),
      X ≅ @stellarSubdivision _ _ Y t Ht_ne y Ht Hy) ∨
    (∃ (s : Finset α) (Hs : s ∈ X.simplices) (Hs_ne : Nonempty s) (x : α) (Hx : x ∉ vertices X),
        Y ≅ @stellarSubdivision _ _ X s Hs_ne x Hs Hx) ∨
      X ≅ Y

noncomputable instance StellarMove.Weld.fintype (X Y : SimplicialComplex α) [Fintype X.simplices]
    (X_weld_Y :
      ∃ (t : Finset α) (Ht : t ∈ Y.simplices) (Ht_ne : Nonempty t) (y : α) (Hy : y ∉ vertices Y),
        X ≅ @stellarSubdivision _ _ Y t Ht_ne y Ht Hy) :
    Fintype Y.simplices :=
  by
  choose t t_in_Y t_ne y y_nin_Y X_weld_Y using X_weld_Y
  apply
    @stellarSubdivision.fintypeConverse _ _ Y t t_ne y t_in_Y y_nin_Y
      (IsSimpliciallyIso.fintype X σ(Y, t, y; t_ne, t_in_Y, y_nin_Y) X_weld_Y)

noncomputable instance StellarMove.Subdiv.fintype (X Y : SimplicialComplex α)
    [X_fin : Fintype X.simplices]
    (X_subdiv_Y :
      ∃ (s : Finset α) (Hs : s ∈ X.simplices) (Hs_ne : Nonempty s) (x : α) (Hx : x ∉ vertices X),
        Y ≅ @stellarSubdivision _ _ X s Hs_ne x Hs Hx) :
    Fintype Y.simplices :=
  by
  choose s s_in_X s_ne x x_nin_X X_subdiv_Y using X_subdiv_Y
  rw [simplicial_iso_symm] at X_subdiv_Y
  apply
    @IsSimpliciallyIso.fintype _ _ _ _ σ(X, s, x; s_ne, s_in_X, x_nin_X)
      (@stellarSubdivision.fintype _ _ X X_fin s s_ne x s_in_X x_nin_X) Y X_subdiv_Y

noncomputable instance StellarMove.fintype (X Y : SimplicialComplex α) [Fintype X.simplices]
    (X_move_Y : StellarMove X Y) : Fintype Y.simplices :=
  by
  simp only [StellarMove] at X_move_Y
  by_cases X_weld_Y :
    ∃ (t : Finset α) (Ht : t ∈ Y.simplices) (Ht_ne : Nonempty t) (y : α) (Hy : y ∉ vertices Y),
      X ≅ @stellarSubdivision _ _ Y t Ht_ne y Ht Hy
  apply StellarMove.Weld.fintype X Y X_weld_Y
  by_cases X_subdiv_Y :
    ∃ (s : Finset α) (Hs : s ∈ X.simplices) (Hs_ne : Nonempty s) (x : α) (Hx : x ∉ vertices X),
      Y ≅ @stellarSubdivision _ _ X s Hs_ne x Hs Hx
  apply StellarMove.Subdiv.fintype X Y X_subdiv_Y
  by_cases X_iso_Y : X ≅ Y
  apply IsSimpliciallyIso.fintype X Y X_iso_Y
  have contra : ¬StellarMove X Y :=
    by
    simp only [StellarMove, not_or]
    constructor; assumption
    constructor; assumption
    assumption
  contradiction

theorem stellarMove_preserves_dim (X Y : SimplicialComplex α) [X_fin : Fintype X.simplices]
    [Y_fin : Fintype Y.simplices] (X_move_Y : StellarMove X Y) : dimOfComplex X = dimOfComplex Y :=
  by
  simp only [StellarMove] at X_move_Y
  cases' X_move_Y with Y_subdiv_X X_move_Y
  choose t t_in_Y t_ne y y_nin_Y Y_subdiv_X using Y_subdiv_X
  rw [@simplicial_iso_preserves_dim α α _ _ X _ σ(Y, t, y; t_ne, t_in_Y, y_nin_Y) Y_subdiv_X]
  symm
  rw [@stellar_subdiv_preserves_dim α _ Y Y_fin t t_ne y t_in_Y y_nin_Y]
  rotate_left
  cases' X_move_Y with X_subdiv_Y X_iso_Y
  choose s s_in_X s_ne x x_nin_X X_subdiv_Y using X_subdiv_Y
  rw [@simplicial_iso_preserves_dim α α _ _ Y Y_fin σ(X, s, x; s_ne, s_in_X, x_nin_X) X_subdiv_Y]
  rw [@stellar_subdiv_preserves_dim _ _ X X_fin s s_ne x s_in_X x_nin_X]
  rotate_left
  rw [@simplicial_iso_preserves_dim α α _ _ X _ Y X_iso_Y]
  all_goals
    unfold dimOfComplex
    apply le_antisymm <;>
      · apply Finset.max'_le
        intro z z_in_img
        simp only [Finset.mem_image, Set.mem_toFinset] at z_in_img
        choose u u_in_K dim_u_z using z_in_img
        apply Finset.le_max'
        simp only [Finset.mem_image, Set.mem_toFinset]
        use u; constructor <;> assumption

def StellarEquiv (X : SimplicialComplex α) : SimplicialComplex α → Prop :=
  Relation.ReflTransGen StellarMove X

infixl:50 " ≅ₛₜ " => StellarEquiv

noncomputable instance StellarEquiv.fintype (X Y : SimplicialComplex α)
    [X_fin : Fintype X.simplices] (X_eq_Y : X ≅ₛₜ Y) : Fintype Y.simplices :=
  by
  apply Set.Finite.fintype
  induction' X_eq_Y with K L X_eq_K K_move_L L_dec
  apply Set.Finite.intro
  assumption
  apply Set.Finite.intro
  have K_fin : Fintype K.simplices := by
    apply Set.Finite.fintype
    assumption
  apply @StellarMove.fintype _ _ K L K_fin K_move_L

theorem stellarEquiv_preserves_dim (X Y : SimplicialComplex α) [X_fin : Fintype X.simplices]
    (X_eq_Y : X ≅ₛₜ Y) :
    dimOfComplex X = @dimOfComplex _ Y (@StellarEquiv.fintype α _ X Y X_fin X_eq_Y) :=
  by
  induction' X_eq_Y with K L X_eq_K K_move_L H_ind
  · unfold dimOfComplex
    apply le_antisymm <;>
      · rw [Finset.max'_le_iff]
        intro y y_max
        apply Finset.le_max'
        simp only [Finset.mem_image, Set.mem_toFinset] at y_max ⊢
        choose s s_in_img dim_s_y using y_max
        use s; constructor <;> assumption
  · trans @dimOfComplex _ K (@StellarEquiv.fintype α _ X K X_fin X_eq_K)
    assumption
    apply @stellarMove_preserves_dim _ _ K L (@StellarEquiv.fintype α _ X K X_fin X_eq_K)
    assumption

@[refl]
theorem stellarEquiv_refl (X : SimplicialComplex α) : X ≅ₛₜ X := by unfold StellarEquiv

@[symm]
theorem stellarEquiv_symm (X Y : SimplicialComplex α) : X ≅ₛₜ Y ↔ Y ≅ₛₜ X :=
  by
  unfold StellarEquiv
  constructor <;>
    · apply Relation.ReflTransGen.symmetric
      rw [← swap_eq_iff]
      simp only [StellarMove, Function.swap]
      apply funext; intro K
      apply funext; intro L
      apply propext
      constructor
      intro L_move_K
      cases L_move_K
      right; left
      choose s Hs Hs_ne x Hx L_subdiv_K using L_move_K
      use s; use Hs; use Hs_ne; use x; use Hx
      assumption
      cases L_move_K
      left
      choose t Ht Ht_ne y Hy K_subdiv_L using L_move_K
      use t; use Ht; use Ht_ne; use y; use Hy
      assumption
      right; right
      rw [simplicial_iso_symm]
      assumption
      intro K_move_L
      cases K_move_L
      right; left
      choose s Hs Hs_ne x Hx K_subdiv_L using K_move_L
      use s; use Hs; use Hs_ne; use x; use Hx
      assumption
      cases K_move_L
      left
      choose t Ht Ht_ne y Hy L_subdiv_K using K_move_L
      use t; use Ht; use Ht_ne; use y; use Hy
      assumption
      right; right
      rw [simplicial_iso_symm]
      assumption

@[trans]
theorem stellarEquiv_trans (X Y Z : SimplicialComplex α) : X ≅ₛₜ Y → Y ≅ₛₜ Z → X ≅ₛₜ Z :=
  by
  unfold StellarEquiv
  apply Relation.transitive_reflTransGen

theorem stellarEquiv_neg_trans (X Y Z : SimplicialComplex α) : X ≅ₛₜ Y → ¬Y ≅ₛₜ Z → ¬X ≅ₛₜ Z :=
  by
  intro X_eq_Y Y_neq_Z
  revert Y_neq_Z
  contrapose
  simp only [Classical.not_not]
  intro X_eq_Z
  rw [stellarEquiv_symm] at X_eq_Y
  revert X_eq_Y X_eq_Z
  apply stellarEquiv_trans

theorem stellarEquiv_preserves_iso (X Y : SimplicialComplex α) : X ≅ Y → X ≅ₛₜ Y :=
  by
  intro X_iso_Y
  simp only [StellarEquiv]
  apply Relation.ReflTransGen.single
  simp only [StellarMove]
  right; right
  assumption

@[simp]
def stellarCoeMap (f : α → β) (x : α) (y : β) : α → β := fun a : α => if a = x then y else f a

theorem stellar_coe_simplex_image (s : Finset α) (x : α) (y : β) (f : α → β) :
    x ∉ s → Finset.image (stellarCoeMap f x y) s = Finset.image f s :=
  by
  rw [Finset.ext_iff]
  intro x_nin_s b
  simp only [Finset.mem_image, stellarCoeMap]
  constructor
  · intro b_in_coe
    choose a a_in_s coe_a_b using b_in_coe
    revert coe_a_b
    split_ifs
    rw [h] at a_in_s
    contradiction
    intro fa_b
    use a; constructor <;> assumption
  · intro b_in_img
    choose a a_in_s fa_b using b_in_img
    use a; constructor; assumption
    split_ifs
    rw [h] at a_in_s
    contradiction
    assumption

theorem stellar_coe_forward_simplicial [Nonempty α] (X : SimplicialComplex α)
    (φ : SimplicialCoe X β) (s : Finset α) [s_ne : Nonempty s] (x : α) (y : β)
    (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X) (y_nin_coe : y ∉ vertices (φ[X])) :
    IsSimplicialMap σ(X, s, x; s_ne, s_in_X, x_nin_X)
      σ(φ[X], Finset.image φ.coe s, y; _, by apply map_is_simplicial_onto_image; assumption,
        y_nin_coe)
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
  apply simplex_if_in_subcomplex
  apply t_in_star_comp
  apply starComplement_subcomplex
  right
  simp only [join_proj_mem] at t_in_join ⊢
  choose t' t'_in_join t₁ t₁_in_link t_decomp using t_in_join
  choose t₃ t₃_in_barycenter t₂ t₂_in_bd t'_decomp using t'_in_join
  subst t'_decomp
  use Finset.image (stellarCoeMap φ.coe x y) (t₃ ∪ t₂); constructor
  use Finset.image (stellarCoeMap φ.coe x y) t₃; constructor
  simp only [simplex, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at
    t₃_in_barycenter ⊢
  cases' t₃_in_barycenter with t₃_empty t₃_x
  left
  rw [t₃_empty]
  apply Finset.image_empty
  right
  rw [t₃_x, Finset.image_singleton]
  simp only [stellarCoeMap, eq_self_iff_true, if_true]
  use Finset.image (stellarCoeMap φ.coe x y) t₂; constructor
  rw [simplexBoundary_coe_image, stellar_coe_simplex_image]
  apply map_is_simplicial_onto_image
  assumption
  revert x_nin_X
  contrapose
  simp only [Classical.not_not, ← Finset.mem_coe]
  have t₂_in_X : ↑t₂ ⊆ vertices X :=
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
  rw [Finset.image_union]
  use Finset.image (stellarCoeMap φ.coe x y) t₁; constructor
  rw [link_coe_image, stellar_coe_simplex_image]
  apply map_is_simplicial_onto_image
  assumption
  revert x_nin_X
  contrapose
  simp only [Classical.not_not, ← Finset.mem_coe]
  have t₁_in_X : ↑t₁ ⊆ vertices X :=
    by
    apply simplex_subset_vertices
    apply simplex_if_in_subcomplex
    apply t₁_in_link
    apply link_subcomplex
  rw [Set.subset_def] at t₁_in_X
  specialize t₁_in_X x
  assumption
  rw [t_decomp, ← Finset.image_union]

theorem stellar_coe_inverse_simplicial [Nonempty α] (X : SimplicialComplex α)
    (φ : SimplicialCoe X β) (s : Finset α) [s_ne : Nonempty s] (x : α) (y : β)
    (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X) (y_nin_coe : y ∉ vertices (φ[X])) :
    IsSimplicialMap
      σ(φ[X], Finset.image φ.coe s, y; _, by apply map_is_simplicial_onto_image; assumption,
        y_nin_coe)
      σ(X, s, x; s_ne, s_in_X, x_nin_X) (stellarCoeMap φ⁻ᶜ.map y x) :=
  by
  simp only [IsSimplicialMap, stellarSubdivision, simplicialUnion, Set.mem_union]
  intro t t_in_subdiv
  cases' t_in_subdiv with t_in_star_comp t_in_join
  left
  rw [stellar_coe_simplex_image]
  rw [starComplement_coe_image, simplicialImage_is_lift_image ((X\St(X, s)) s_in_X),
    Set.mem_image] at t_in_star_comp
  choose u u_in_star_comp φu_t using t_in_star_comp
  simp only [simplicialMapLift] at φu_t
  rw [← φu_t]
  have inv_u : Finset.image φ⁻ᶜ.map (Finset.image φ.coe u) = u :=
    by
    simp only [← Finset.coe_inj, Finset.coe_image]
    apply Set.InjOn.invFunOn_image
    apply φ.injective
    apply simplex_subset_vertices
    apply simplex_if_in_subcomplex
    apply u_in_star_comp
    apply starComplement_subcomplex
  rw [inv_u]
  assumption
  revert y_nin_coe
  contrapose
  simp only [Classical.not_not]
  revert y
  simp only [← Finset.mem_coe, ← Set.subset_def]
  apply simplex_subset_vertices
  apply simplex_if_in_subcomplex
  apply t_in_star_comp
  apply starComplement_subcomplex
  right
  simp only [join_proj_mem] at t_in_join ⊢
  choose t' t'_in_join t₁ t₁_in_link t_decomp using t_in_join
  choose t₃ t₃_in_barycenter t₂ t₂_in_bd t'_decomp using t'_in_join
  subst t'_decomp
  use Finset.image (stellarCoeMap φ⁻ᶜ.map y x) (t₃ ∪ t₂); constructor
  use Finset.image (stellarCoeMap φ⁻ᶜ.map y x) t₃; constructor
  simp only [simplex, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at
    t₃_in_barycenter ⊢
  cases' t₃_in_barycenter with t₃_empty t₃_x
  left
  rw [t₃_empty]
  apply Finset.image_empty
  right
  rw [t₃_x, Finset.image_singleton]
  simp only [stellarCoeMap, eq_self_iff_true, if_true]
  use Finset.image (stellarCoeMap φ⁻ᶜ.map y x) t₂; constructor
  rw [stellar_coe_simplex_image]
  rw [simplexBoundary_coe_image, simplicialImage_is_lift_image, Set.mem_image] at t₂_in_bd
  choose u u_in_bd φu_t₂ using t₂_in_bd
  simp only [simplicialMapLift] at φu_t₂
  rw [← φu_t₂]
  have inv_u : Finset.image φ⁻ᶜ.map (Finset.image φ.coe u) = u :=
    by
    simp only [← Finset.coe_inj, Finset.coe_image]
    apply Set.InjOn.invFunOn_image
    apply φ.injective
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
  have t₂_in_X : ↑t₂ ⊆ vertices (φ[X]) :=
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
  rw [Finset.image_union]
  use Finset.image (stellarCoeMap φ⁻ᶜ.map y x) t₁; constructor
  rw [stellar_coe_simplex_image]
  rw [link_coe_image, simplicialImage_is_lift_image (Lk(X, s) s_in_X), Set.mem_image] at t₁_in_link
  choose u u_in_link φu_t₁ using t₁_in_link
  simp only [simplicialMapLift] at φu_t₁
  rw [← φu_t₁]
  have inv_u : Finset.image φ⁻ᶜ.map (Finset.image φ.coe u) = u :=
    by
    simp only [← Finset.coe_inj, Finset.coe_image]
    apply Set.InjOn.invFunOn_image
    apply φ.injective
    apply simplex_subset_vertices
    apply simplex_if_in_subcomplex
    apply u_in_link
    apply link_subcomplex
  rw [inv_u]
  assumption
  revert y_nin_coe
  contrapose
  simp only [Classical.not_not, ← Finset.mem_coe]
  have t₁_in_X : ↑t₁ ⊆ vertices (φ[X]) :=
    by
    apply simplex_subset_vertices
    apply simplex_if_in_subcomplex
    apply t₁_in_link
    apply link_subcomplex
  rw [Set.subset_def] at t₁_in_X
  specialize t₁_in_X y
  assumption
  rw [t_decomp, ← Finset.image_union]

def stellarCoeForward [Nonempty α] (X : SimplicialComplex α) (φ : SimplicialCoe X β) (s : Finset α)
    [s_ne : Nonempty s] (x : α) (y : β) (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X)
    (y_nin_coe : y ∉ vertices (φ[X])) :
    SimplicialMap σ(X, s, x; s_ne, s_in_X, x_nin_X)
      σ(φ[X], Finset.image φ.coe s, y; _, by apply map_is_simplicial_onto_image; assumption,
        y_nin_coe) :=
  SimplicialMap.mk (stellarCoeMap φ.coe x y)
    (stellar_coe_forward_simplicial X φ s x y s_in_X x_nin_X y_nin_coe)

noncomputable def stellarCoeInverse [Nonempty α] (X : SimplicialComplex α) (φ : SimplicialCoe X β)
    (s : Finset α) [s_ne : Nonempty s] (x : α) (y : β) (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X) (y_nin_coe : y ∉ vertices (φ[X])) :
    SimplicialMap
      σ(φ[X], Finset.image φ.coe s, y; _, by apply map_is_simplicial_onto_image; assumption,
        y_nin_coe)
      σ(X, s, x; s_ne, s_in_X, x_nin_X) :=
  SimplicialMap.mk (stellarCoeMap φ⁻ᶜ.map y x)
    (stellar_coe_inverse_simplicial X φ s x y s_in_X x_nin_X y_nin_coe)

theorem stellar_subdiv_congr_simplices (X Y : SimplicialComplex α) (s : Finset α)
    [s_ne : Nonempty s] (x : α) (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X)
    (X_eq_Y : X.simplices = Y.simplices) :
    σ(X, s, x; s_ne, s_in_X, x_nin_X).simplices =
      σ(Y, s, x; s_ne, by rw [← X_eq_Y]; assumption, by rw [← vertices_congr X Y X_eq_Y];
          assumption).simplices :=
  by
  simp only [stellarSubdivision, simplicialUnion, starComplement, link, simplex, simplexBoundary,
    X_eq_Y]
  rfl

theorem stellar_coe_vertices (X : SimplicialComplex α) (φ : SimplicialCoe X β) (s : Finset α)
    [s_ne : Nonempty s] (x : α) (y : β) (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X)
    (y_nin_coe : y ∉ vertices (φ[X])) :
    vertices (simplicialImage X (stellarCoeMap φ.coe x y)) = vertices (φ[X]) :=
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

theorem stellar_coe_image (X : SimplicialComplex α) (φ : SimplicialCoe X β) (s : Finset α)
    [s_ne : Nonempty s] (x : α) (y : β) (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X)
    (y_nin_coe : y ∉ vertices (φ[X])) :
    σ(simplicialImage X (stellarCoeMap φ.coe x y), Finset.image (stellarCoeMap φ.coe x y) s,
        (stellarCoeMap φ.coe x y) x; _, by apply map_is_simplicial_onto_image; assumption,
        by
        simp only [stellarCoeMap, eq_self_iff_true, if_true]
        rw [← stellarCoeMap, stellar_coe_vertices X φ s x y] <;> assumption) ≅
      σ(simplicialImage X φ.coe, Finset.image φ.coe s, y; _, by apply map_is_simplicial_onto_image;
        assumption, y_nin_coe) :=
  by
  apply simplicial_iso_preserves_equiv
  have x_nin_s : x ∉ s := by
    revert x_nin_X
    contrapose
    simp only [Classical.not_not, ← Finset.mem_coe]
    have s_ss_X : ↑s ⊆ vertices X := by
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
  split_ifs
  rw [h] at z_in_X
  contradiction
  rfl

theorem stellar_coe_inv_iso [Nonempty α] (X : SimplicialComplex α) (φ : SimplicialCoe X β)
    (s : Finset α) [s_ne : Nonempty s] (x : α) (y : β) (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X) (y_nin_coe : y ∉ vertices (φ[X])) :
    IsInverseSimplicialIso (stellarCoeForward X φ s x y s_in_X x_nin_X y_nin_coe)
      (stellarCoeInverse X φ s x y s_in_X x_nin_X y_nin_coe) :=
  by
  unfold IsInverseSimplicialIso
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply,
    id.def]
  simp only [stellarCoeInverse, stellarCoeForward]
  constructor
  · intro a a_in_subdiv
    have a_in_union : a ∈ vertices X ∪ {x} :=
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
      have contra : y ∈ vertices (φ[X]) :=
        by
        rw [simplicialImage_vertices, Set.mem_image]
        use a; constructor <;> assumption
      contradiction
      assumption
    simp only [stellarCoeMap, a_ne_x, φa_ne_y, if_false]
    apply Set.InjOn.leftInvOn_invFunOn
    apply φ.injective
    assumption
    simp only [stellarCoeMap, a_eq_x, eq_self_iff_true, if_true]
  · intro b b_in_coe
    have b_in_union : b ∈ vertices (φ[X]) ∪ {y} :=
      by
      apply Set.mem_of_mem_of_subset
      apply b_in_coe
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
        apply φ.injective
        assumption
      rw [inv_a] at φb_eq_x
      rw [φb_eq_x] at a_in_X
      contradiction
      assumption
    simp only [stellarCoeMap, b_ne_y, φb_ne_x, if_false]
    simp only [simplicialCoeInv]
    apply Function.invFunOn_eq
    simp only [simplicialImage_vertices, Set.mem_image, ← exists_prop] at b_in_X
    assumption
    simp only [stellarCoeMap, b_eq_y, eq_self_iff_true, if_true]

theorem stellar_coe_iso [Nonempty α] (X : SimplicialComplex α) (φ : SimplicialCoe X β)
    (s : Finset α) [s_ne : Nonempty s] (x : α) (y : β) (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X) (y_nin_coe : y ∉ vertices (φ[X])) :
    IsSimplicialIso (stellarCoeForward X φ s x y s_in_X x_nin_X y_nin_coe) :=
  by
  use stellarCoeInverse X φ s x y s_in_X x_nin_X y_nin_coe
  apply stellar_coe_inv_iso

theorem stellar_weld_exists_iso [Nonempty α] (X Y : SimplicialComplex α) (Z : SimplicialComplex β)
    (t : Finset α) [t_ne : Nonempty t] (y : α) (t_in_Y : t ∈ Y.simplices)
    (y_nin_Y : y ∉ vertices Y) :
    X ≅ Z → X ≅ σ(Y, t, y; t_ne, t_in_Y, y_nin_Y) → ∃ W : SimplicialComplex β, Y ≅ W ∧ Z ≅ₛₜ W :=
  by
  intro X_iso_Z Y_subdiv_X
  have Z_iso_subdiv : Z ≅ σ(Y, t, y; t_ne, t_in_Y, y_nin_Y) :=
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
    id.def] at gf_inv'
  choose gf_id fg_id using gf_inv'
  have g_iso : IsSimplicialIso g := by apply iso_inv_is_iso f g f_iso gf_inv
  by_cases t_singleton : t.card = 1
  rw [Finset.card_eq_one] at t_singleton
  choose a t_eq_a using t_singleton
  subst t_eq_a
  rw [stellar_subdiv_of_singleton_vertices] at fg_id
  use Z; constructor
  apply simplicial_iso_trans Y σ(Y, {a}, y; t_ne, t_in_Y, y_nin_Y)
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
    rw [Finset.nonempty_coe_sort, Finset.nonempty_iff_ne_empty, Ne.def, ← Finset.card_eq_zero] at
      t_ne
    omega
  have g_inj : Set.InjOn g.map (vertices Y) :=
    by
    apply @Set.InjOn.mono _ _ (vertices Y) (vertices Y ∪ {y})
    apply Set.subset_union_left
    rw [← stellar_subdiv_vertices Y t y t_in_Y y_nin_Y t_nonsingleton]
    apply iso_is_injective_vertices g g_iso
  let g_coe : SimplicialCoe Y β := SimplicialCoe.mk g.map g_inj
  have gy_nin_gY : g.map y ∉ vertices (g_coe[Y]) :=
    by
    by_cases gy_in_Y : g.map y ∈ vertices (g_coe[Y])
    rw [simplicialImage_vertices] at gy_in_Y
    have contra : y ∈ vertices Y :=
      by
      apply Set.InjOn.mem_of_mem_image
      apply iso_is_injective_vertices g g_iso
      rw [stellar_subdiv_vertices Y t y t_in_Y y_nin_Y t_nonsingleton]
      apply Set.subset_union_left
      apply barycenter_vertex_stellar_subdiv
      assumption
    contradiction
    assumption
  let φ := stellarCoeForward Y g_coe t y (g.map y) t_in_Y y_nin_Y gy_nin_gY
  have φ_inj : Set.InjOn φ.map (vertices Y ∪ {y}) :=
    by
    rw [← stellar_subdiv_vertices Y t y t_in_Y y_nin_Y t_nonsingleton]
    apply
      iso_is_injective_vertices φ (stellar_coe_iso Y g_coe t y (g.map y) t_in_Y y_nin_Y gy_nin_gY)
  have φy_nin_φY : φ.map y ∉ vertices (simplicialImage Y φ.map) :=
    by
    by_cases φy_in_Y : φ.map y ∈ vertices (simplicialImage Y φ.map)
    rw [simplicialImage_vertices] at φy_in_Y
    have contra : y ∈ vertices Y :=
      by
      apply Set.InjOn.mem_of_mem_image
      apply φ_inj
      apply Set.subset_union_left
      rw [Set.mem_union, Set.mem_singleton_iff]
      right; rfl
      assumption
    contradiction
    assumption
  use simplicialImage Y φ.map; constructor
  have φY_inj : Set.InjOn φ.map (vertices Y) :=
    by
    apply @Set.InjOn.mono _ _ _ (vertices Y ∪ {y})
    apply Set.subset_union_left
    assumption
  let φY := SimplicialCoe.mk φ.map φY_inj
  apply simplicial_iso_trans _ (φY[Y])
  apply φY.iso_onto_image
  apply simplicial_iso_preserves_equiv
  apply simplicialImage_congr
  simp only
  apply Relation.ReflTransGen.single
  unfold StellarMove
  left
  use Finset.image φ.map t
  have φt_in_φY : Finset.image φ.map t ∈ (simplicialImage Y φ.map).simplices :=
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
  apply simplicial_iso_trans Z σ(Y, t, y; t_ne, t_in_Y, y_nin_Y)
  assumption
  apply
    simplicial_iso_trans _
      σ(simplicialImage Y g_coe.coe, Finset.image g_coe.coe t, g.map y; _, by
        apply map_is_simplicial_onto_image; assumption, gy_nin_gY)
  unfold IsSimpliciallyIso
  use φ
  apply stellar_coe_iso
  rw [simplicial_iso_symm]
  apply stellar_coe_image <;> assumption

theorem barycenter_injective_image {X : SimplicialComplex α} {x : α} {f : α → β} :
    x ∉ vertices X → Function.Injective f → f x ∉ vertices (simplicialImage X f) :=
  by
  intro x_nin_X f_inj
  by_contra fx_in_X
  rw [simplicialImage_vertices] at fx_in_X
  have contra : x ∈ vertices X := by
    apply Set.InjOn.mem_of_mem_image
    apply Function.Injective.injOn f_inj Set.univ
    apply Set.subset_univ
    apply Set.mem_univ
    assumption
  contradiction

theorem stellar_subdiv_injective_image_simplices_left (X : SimplicialComplex α) (s : Finset α)
    [s_ne : Nonempty s] (x : α) (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X) (f : α → β)
    (f_inj : Function.Injective f) :
    (simplicialImage σ(X, s, x; s_ne, s_in_X, x_nin_X) f).simplices ⊆
      σ(simplicialImage X f, Finset.image f s, f x; _, by apply map_is_simplicial_onto_image;
          assumption, barycenter_injective_image x_nin_X f_inj).simplices :=
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
  use u; constructor <;> assumption
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
  simp only [join_proj_mem] at u_in_join ⊢
  choose u' u'_in_join u₁ u₁_in_link u_decomp using u_in_join
  choose u₃ u₃_in_barycenter u₂ u₂_in_bd u'_decomp using u'_in_join
  subst u'_decomp
  use Finset.image f (u₃ ∪ u₂); constructor
  use Finset.image f u₃; constructor
  simp only [simplex, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at
    u₃_in_barycenter ⊢
  cases' u₃_in_barycenter with u₃_empty u₃_eq_x
  left
  rw [u₃_empty]
  apply Finset.image_empty
  right
  rw [u₃_eq_x]
  apply Finset.image_singleton
  use Finset.image f u₂; constructor
  simp only [simplexBoundary, Set.mem_union, Set.mem_diff, Finset.mem_coe, Finset.mem_powerset,
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
  intro fu₂_eq_fs a
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
  rw [u₂_empty]
  apply Finset.image_empty
  rw [Finset.image_union]
  use Finset.image f u₁; constructor
  simp only [link, Set.mem_sep_iff] at u₁_in_link ⊢
  choose u₁_in_X su₁_in_X su₁_disj using u₁_in_link
  constructor
  apply map_is_simplicial_onto_image
  assumption
  constructor
  rw [← Finset.image_union]
  apply map_is_simplicial_onto_image
  assumption
  rw [← Finset.image_inter s u₁ f_inj, Finset.image_eq_empty]
  assumption
  rw [← Finset.image_union, ← fu_t, u_decomp]

theorem stellar_subdiv_injective_image_simplices_right_ac [Nonempty α] (X : SimplicialComplex α)
    (s : Finset α) [s_ne : Nonempty s] (x : α) (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X)
    (f : α → β) (f_inj : Function.Injective f) :
    ∀ t : Finset β,
      (∃ t₁ t₂ t₃ : Finset β,
          t₁ ∈
              (Lk(simplicialImage X f, Finset.image f s)
                  (by apply map_is_simplicial_onto_image; assumption)).simplices ∧
            t₂ ⊆ Finset.image f s ∧ ¬t₂ = Finset.image f s ∧ t₃ = ∅ ∧ t = t₃ ∪ t₂ ∪ t₁) →
        t ∈ (simplicialImage σ(X, s, x; s_ne, s_in_X, x_nin_X) f).simplices :=
  by
  intro t t_decomp
  choose t₁ t₂ t₃ t₁_in_link t₂_ss_fs t₂_ne_fs t₃_empty t_decomp using t_decomp
  simp only [simplicialImage, Set.mem_setOf]
  simp only [stellarSubdivision, simplicialUnion, Set.mem_union]
  simp only [link, Set.mem_sep_iff, simplicialImage, Set.mem_setOf] at t₁_in_link
  choose t₁_in_fX fst₁_in_fX fst₁_disj using t₁_in_link
  choose u₁ u₁_in_X fu₁_t₁ using t₁_in_fX
  choose v v_in_X fv_fsu₁ using fst₁_in_fX
  subst fu₁_t₁
  subst t₃_empty
  set u₂ := Finset.image (Function.invFunOn f Set.univ) t₂
  use∅ ∪ u₂ ∪ u₁; constructor; right
  simp only [join_proj_mem]
  use∅ ∪ u₂; constructor
  use∅; constructor; apply simplicialComplex_empty_simplex
  use u₂; constructor
  simp only [simplexBoundary, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe,
    Finset.mem_powerset]
  left; constructor
  rw [Finset.subset_iff] at t₂_ss_fs ⊢
  intro a a_in_u₂
  have fa_in_t₂ : f a ∈ t₂ := by
    rw [Finset.mem_image] at a_in_u₂
    choose b b_in_t₂ fb_a using a_in_u₂
    rw [← fb_a, @Function.invFunOn_eq _ _ _ Set.univ f]
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
  rw [@Function.invFunOn_eq _ _ _ Set.univ f]
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
  rw [@Function.invFunOn_eq _ _ _ Set.univ f] at fa_b
  rw [← fa_b]
  assumption
  simp only [Finset.subset_iff, Finset.mem_image] at t₂_ss_fs
  specialize t₂_ss_fs c_in_t₂
  choose d d_in_s fd_c using t₂_ss_fs
  use d; constructor; apply Set.mem_univ
  assumption
  rfl
  use u₁; constructor
  simp only [link, Set.mem_sep_iff]
  constructor; assumption
  constructor
  have v_su₁ : v = s ∪ u₁ := by
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
  rfl
  simp only [Finset.image_union]
  have fu₂_t₂ : Finset.image f u₂ = t₂ :=
    by
    simp only [Finset.ext_iff, Finset.mem_image]
    intro a
    constructor
    intro a_in_img
    choose c c_in_inv fc_a using a_in_img
    choose b b_in_t₂ fb_c using c_in_inv
    rw [← fb_c, @Function.invFunOn_eq _ _ _ Set.univ f] at fc_a
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
    use a; constructor; assumption
    rw [← fb_a]
    apply Set.InjOn.leftInvOn_invFunOn
    apply Function.Injective.injOn f_inj
    apply Set.mem_univ
    assumption
  rw [fu₂_t₂, Finset.image_empty]
  symm
  assumption

theorem stellar_subdiv_injective_image_simplices_right_ad [Nonempty α] (X : SimplicialComplex α)
    (s : Finset α) [s_ne : Nonempty s] (x : α) (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X)
    (f : α → β) (f_inj : Function.Injective f) :
    ∀ t : Finset β,
      (∃ t₁ t₂ t₃ : Finset β,
          t₁ ∈
              (Lk(simplicialImage X f, Finset.image f s)
                  (by apply map_is_simplicial_onto_image; assumption)).simplices ∧
            t₂ ⊆ Finset.image f s ∧ ¬t₂ = Finset.image f s ∧ t₃ = {f x} ∧ t = t₃ ∪ t₂ ∪ t₁) →
        t ∈ (simplicialImage σ(X, s, x; s_ne, s_in_X, x_nin_X) f).simplices :=
  by
  intro t t_decomp
  choose t₁ t₂ t₃ t₁_in_link t₂_ss_fs t₂_ne_fs t₃_eq_fx t_decomp using t_decomp
  simp only [simplicialImage, Set.mem_setOf]
  simp only [stellarSubdivision, simplicialUnion, Set.mem_union]
  simp only [link, Set.mem_sep_iff, simplicialImage, Set.mem_setOf] at t₁_in_link
  choose t₁_in_fX fst₁_in_fX fst₁_disj using t₁_in_link
  choose u₁ u₁_in_X fu₁_t₁ using t₁_in_fX
  choose v v_in_X fv_fsu₁ using fst₁_in_fX
  subst fu₁_t₁
  subst t₃_eq_fx
  set u₂ := Finset.image (Function.invFunOn f Set.univ) t₂
  use{x} ∪ u₂ ∪ u₁; constructor; right
  simp only [join_proj_mem]
  use{x} ∪ u₂; constructor
  use{x}; constructor
  simp only [simplex, Finset.mem_coe]
  apply Finset.mem_powerset_self
  use u₂; constructor
  simp only [simplexBoundary, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe,
    Finset.mem_powerset]
  left; constructor
  rw [Finset.subset_iff] at t₂_ss_fs ⊢
  intro a a_in_u₂
  have fa_in_t₂ : f a ∈ t₂ := by
    rw [Finset.mem_image] at a_in_u₂
    choose b b_in_t₂ fb_a using a_in_u₂
    rw [← fb_a, @Function.invFunOn_eq _ _ _ Set.univ f]
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
  rw [@Function.invFunOn_eq _ _ _ Set.univ f]
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
  rw [@Function.invFunOn_eq _ _ _ Set.univ f] at fa_b
  rw [← fa_b]
  assumption
  simp only [Finset.subset_iff, Finset.mem_image] at t₂_ss_fs
  specialize t₂_ss_fs c_in_t₂
  choose d d_in_s fd_c using t₂_ss_fs
  use d; constructor; apply Set.mem_univ
  assumption
  rfl
  use u₁; constructor
  simp only [link, Set.mem_sep_iff]
  constructor; assumption
  constructor
  have v_su₁ : v = s ∪ u₁ := by
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
  rfl
  simp only [Finset.image_union]
  have fu₂_t₂ : Finset.image f u₂ = t₂ :=
    by
    simp only [Finset.ext_iff, Finset.mem_image]
    intro a
    constructor
    intro a_in_img
    choose c c_in_inv fc_a using a_in_img
    choose b b_in_t₂ fb_c using c_in_inv
    rw [← fb_c, @Function.invFunOn_eq _ _ _ Set.univ f] at fc_a
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
    use a; constructor; assumption
    rw [← fb_a]
    apply Set.InjOn.leftInvOn_invFunOn
    apply Function.Injective.injOn f_inj
    apply Set.mem_univ
    assumption
  rw [fu₂_t₂, Finset.image_singleton]
  symm
  assumption

theorem stellar_subdiv_injective_image_simplices_right_bc (X : SimplicialComplex α) (s : Finset α)
    [s_ne : Nonempty s] (x : α) (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X) (f : α → β)
    (f_inj : Function.Injective f) :
    ∀ t : Finset β,
      (∃ t₁ t₂ t₃ : Finset β,
          t₁ ∈
              (Lk(simplicialImage X f, Finset.image f s)
                  (by apply map_is_simplicial_onto_image; assumption)).simplices ∧
            t₂ = ∅ ∧ t₃ = ∅ ∧ t = t₃ ∪ t₂ ∪ t₁) →
        t ∈ (simplicialImage σ(X, s, x; s_ne, s_in_X, x_nin_X) f).simplices :=
  by
  intro t t_decomp
  choose t₁ t₂ t₃ t₁_in_link t₂_empty t₃_empty t_decomp using t_decomp
  simp only [simplicialImage, Set.mem_setOf]
  simp only [stellarSubdivision, simplicialUnion, Set.mem_union]
  simp only [link, Set.mem_sep_iff, simplicialImage, Set.mem_setOf] at t₁_in_link
  choose t₁_in_fX fst₁_in_fX fst₁_disj using t₁_in_link
  choose u₁ u₁_in_X fu₁_t₁ using t₁_in_fX
  choose v v_in_X fv_fsu₁ using fst₁_in_fX
  subst fu₁_t₁
  use∅ ∪ ∅ ∪ u₁; constructor; right
  simp only [join_proj_mem]
  use∅ ∪ ∅; constructor
  use∅; constructor; apply simplicialComplex_empty_simplex
  use∅; constructor; apply simplicialComplex_empty_simplex
  rfl
  use u₁; constructor
  simp only [link, Set.mem_sep_iff]
  constructor; assumption
  constructor
  have v_su₁ : v = s ∪ u₁ := by
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
  rfl
  simp only [Finset.image_union, Finset.image_singleton, Finset.image_empty]
  subst t₃_empty
  subst t₂_empty
  symm
  assumption

theorem stellar_subdiv_injective_image_simplices_right_bd (X : SimplicialComplex α) (s : Finset α)
    [s_ne : Nonempty s] (x : α) (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X) (f : α → β)
    (f_inj : Function.Injective f) :
    ∀ t : Finset β,
      (∃ t₁ t₂ t₃ : Finset β,
          t₁ ∈
              (Lk(simplicialImage X f, Finset.image f s)
                  (by apply map_is_simplicial_onto_image; assumption)).simplices ∧
            t₂ = ∅ ∧ t₃ = {f x} ∧ t = t₃ ∪ t₂ ∪ t₁) →
        t ∈ (simplicialImage σ(X, s, x; s_ne, s_in_X, x_nin_X) f).simplices :=
  by
  intro t t_decomp
  choose t₁ t₂ t₃ t₁_in_link t₂_empty t₃_eq_fx t_decomp using t_decomp
  simp only [simplicialImage, Set.mem_setOf]
  simp only [stellarSubdivision, simplicialUnion, Set.mem_union]
  simp only [link, Set.mem_sep_iff, simplicialImage, Set.mem_setOf] at t₁_in_link
  choose t₁_in_fX fst₁_in_fX fst₁_disj using t₁_in_link
  choose u₁ u₁_in_X fu₁_t₁ using t₁_in_fX
  choose v v_in_X fv_fsu₁ using fst₁_in_fX
  subst fu₁_t₁
  use{x} ∪ ∅ ∪ u₁; constructor; right
  simp only [join_proj_mem]
  use{x} ∪ ∅; constructor
  use{x}; constructor
  simp only [simplex, Finset.mem_coe]
  apply Finset.mem_powerset_self
  use∅; constructor; apply simplicialComplex_empty_simplex
  rfl
  use u₁; constructor
  simp only [link, Set.mem_sep_iff]
  constructor; assumption
  constructor
  have v_su₁ : v = s ∪ u₁ := by
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
  rfl
  simp only [Finset.image_union, Finset.image_singleton, Finset.image_empty, ← t₃_eq_fx, ← t₂_empty]
  symm
  assumption

theorem stellar_subdiv_injective_image_simplices_right [Nonempty α] (X : SimplicialComplex α)
    (s : Finset α) [s_ne : Nonempty s] (x : α) (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X)
    (f : α → β) (f_inj : Function.Injective f) :
    σ(simplicialImage X f, Finset.image f s, f x; _, by apply map_is_simplicial_onto_image;
          assumption, barycenter_injective_image x_nin_X f_inj).simplices ⊆
      (simplicialImage σ(X, s, x; s_ne, s_in_X, x_nin_X) f).simplices :=
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
  choose t' t'_in_join t₁ t₁_in_link t_decomp using t_in_join
  choose t₃ t₃_in_barycenter t₂ t₂_in_bd t'_decomp using t'_in_join
  subst t'_decomp
  simp only [simplexBoundary, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe,
    Finset.mem_powerset] at t₂_in_bd
  simp only [simplex, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at
    t₃_in_barycenter
  cases' t₂_in_bd with t₂_in_bd t₂_empty <;>-- Cases A, B resp.
    cases' t₃_in_barycenter with t₃_empty t₃_eq_x
  -- Cases C, D resp.
  choose t₂_ss_fs t₂_ne_fs using t₂_in_bd
  apply stellar_subdiv_injective_image_simplices_right_ac
  assumption
  use t₁; use t₂; use t₃
  repeat' constructor; assumption
  assumption
  choose t₂_ss_fs t₂_ne_fs using t₂_in_bd
  apply stellar_subdiv_injective_image_simplices_right_ad
  assumption
  use t₁; use t₂; use t₃
  repeat' constructor; assumption
  assumption
  apply stellar_subdiv_injective_image_simplices_right_bc
  assumption
  use t₁; use t₂; use t₃
  repeat' constructor; assumption
  assumption
  apply stellar_subdiv_injective_image_simplices_right_bd
  assumption
  use t₁; use t₂; use t₃
  repeat' constructor; assumption
  assumption

theorem stellar_subdiv_injective_image_simplices [Nonempty α] (X : SimplicialComplex α)
    (s : Finset α) [s_ne : Nonempty s] (x : α) (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X)
    (f : α → β) (f_inj : Function.Injective f) :
    (simplicialImage σ(X, s, x; s_ne, s_in_X, x_nin_X) f).simplices =
      σ(simplicialImage X f, Finset.image f s, f x; _, by apply map_is_simplicial_onto_image;
          assumption, barycenter_injective_image x_nin_X f_inj).simplices :=
  by
  rw [Set.Subset.antisymm_iff]
  constructor
  apply stellar_subdiv_injective_image_simplices_left
  apply stellar_subdiv_injective_image_simplices_right

theorem stellar_subdiv_injective_image [Nonempty α] (X : SimplicialComplex α) (s : Finset α)
    [s_ne : Nonempty s] (x : α) (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X) (f : α → β)
    (f_inj : Function.Injective f) :
    simplicialImage σ(X, s, x; s_ne, s_in_X, x_nin_X) f ≅
      σ(simplicialImage X f, Finset.image f s, f x; _, by apply map_is_simplicial_onto_image;
        assumption, barycenter_injective_image x_nin_X f_inj) :=
  by
  apply simplicial_iso_preserves_equiv
  apply stellar_subdiv_injective_image_simplices

theorem stellar_subdiv_exists_iso [Nonempty α] (X Y : SimplicialComplex α) (Z : SimplicialComplex β)
    (s : Finset α) [s_ne : Nonempty s] (x : α) (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X)
    (τ : α → β) (τ_inj : Function.Injective τ) :
    X ≅ Z → Y ≅ σ(X, s, x; s_ne, s_in_X, x_nin_X) → ∃ W : SimplicialComplex β, Y ≅ W ∧ Z ≅ₛₜ W :=
  by
  intro X_iso_Z X_subdiv_Y
  have τ_inj_subdiv : Set.InjOn τ (vertices σ(X, s, x; s_ne, s_in_X, x_nin_X)) := by
    apply Set.injOn_of_injective τ_inj
  let τσ := SimplicialCoe.mk τ τ_inj_subdiv
  have τ_inj_X : Set.InjOn τ (vertices X) := by apply Set.injOn_of_injective τ_inj
  let τX := SimplicialCoe.mk τ τ_inj_X
  use τσ[σ(X, s, x; s_ne, s_in_X, x_nin_X)]; constructor
  apply simplicial_iso_trans _ σ(X, s, x; s_ne, s_in_X, x_nin_X)
  assumption
  apply τσ.iso_onto_image
  have τX_iso_Z : Z ≅ τX[X] := by
    apply simplicial_iso_trans _ X
    rw [simplicial_iso_symm]
    assumption
    apply τX.iso_onto_image
  apply @Relation.ReflTransGen.tail _ _ _ (τX[X])
  apply Relation.ReflTransGen.single
  right; right
  assumption
  right; left
  use Finset.image τX.coe s
  have τs_in_img : Finset.image τX.coe s ∈ τX[X].simplices :=
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
  have τx_nin_τX : τX.coe x ∉ vertices (τX[X]) :=
    by
    by_cases τx_in_X : τX.coe x ∈ vertices (τX[X])
    rw [simplicialImage_vertices] at τx_in_X
    have contra : x ∈ vertices X := by
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

theorem stellarMove_exists_iso [Nonempty α] (X Y : SimplicialComplex α) (Z : SimplicialComplex β)
    (f : α → β) (f_inj : Function.Injective f) :
    X ≅ Z → StellarMove X Y → ∃ W : SimplicialComplex β, Y ≅ W ∧ Z ≅ₛₜ W :=
  by
  intro X_iso_Z X_move_Y
  unfold StellarMove at X_move_Y
  cases' X_move_Y with Y_subdiv_X X_move_Y
  choose t t_in_Y t_ne y y_nin_Y Y_subdiv_X using Y_subdiv_X
  apply @stellar_weld_exists_iso _ _ _ _ _ X Y Z t t_ne y t_in_Y y_nin_Y X_iso_Z Y_subdiv_X
  cases' X_move_Y with X_subdiv_Y X_iso_Y
  choose s s_in_X s_ne x x_nin_X X_subdiv_Y using X_subdiv_Y
  apply
    @stellar_subdiv_exists_iso _ _ _ _ _ X Y Z s s_ne x s_in_X x_nin_X f f_inj X_iso_Z X_subdiv_Y
  use Z; constructor
  apply simplicial_iso_trans Y X
  rw [simplicial_iso_symm]
  assumption
  assumption
  rfl

theorem stellarEquiv_exists_iso [Nonempty α] (X Y : SimplicialComplex α) (Z : SimplicialComplex β)
    (f : α → β) (f_inj : Function.Injective f) :
    X ≅ Z → X ≅ₛₜ Y → ∃ W : SimplicialComplex β, Y ≅ W ∧ Z ≅ₛₜ W :=
  by
  intro X_iso_Z X_eq_Y
  induction' X_eq_Y with K Y X_eq_K K_move_Y H_ind
  use Z; constructor
  assumption
  apply stellarEquiv_refl
  choose L K_iso_L Z_eq_L using H_ind
  have Z_move_W : ∃ W : SimplicialComplex β, Y ≅ W ∧ L ≅ₛₜ W :=
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

theorem stellarMove_iso [Nonempty α] (X Y : SimplicialComplex α) (Z W : SimplicialComplex β)
    (f : α → β) (f_inj : Function.Injective f) : X ≅ Z → Y ≅ W → StellarMove X Y → Z ≅ₛₜ W :=
  by
  intro X_iso_Z Y_iso_W X_move_Y
  have Y_iso_L : ∃ L : SimplicialComplex β, Y ≅ L ∧ Z ≅ₛₜ L :=
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

theorem stellarEquiv_iso [Nonempty α] (X Y : SimplicialComplex α) (Z W : SimplicialComplex β)
    (f : α → β) (f_inj : Function.Injective f) : X ≅ Z → Y ≅ W → X ≅ₛₜ Y → Z ≅ₛₜ W :=
  by
  intro X_iso_Z Y_iso_W X_eq_Y
  induction' X_eq_Y with K Y X_eq_K K_move_Y H_ind
  rw [simplicial_iso_symm] at X_iso_Z
  apply stellarEquiv_preserves_iso
  apply simplicial_iso_trans Z X <;> assumption
  have K_iso_L : ∃ L : SimplicialComplex β, K ≅ L ∧ Z ≅ₛₜ L :=
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
theorem barycenter_join_left {X Y : SimplicialComplex α} {x : α} :
    x ∉ vertices X → (x, 0) ∉ vertices (X ⋆ Y) :=
  by
  contrapose
  simp only [Classical.not_not, simplicialJoin_vertices_mem_left]
  exact Set.mem_of_eq_of_mem rfl

theorem stellar_join_distr_join_left (X Y : SimplicialComplex α) (s : Finset α) [s_ne : Nonempty s]
    (x : α) (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X) :
    (π₁
              (barycenter_join_boundary_disjoint_link X s x s_in_X
                x_nin_X)[π₁ (barycenter_disjoint_boundary X s x s_in_X x_nin_X)[simplex {x} ⋆ ∂s] ⋆
              Lk(X, s) s_in_X] ⋆
          Y).simplices ⊆
      π₁
            (barycenter_join_boundary_disjoint_link (X ⋆ Y) (s ⊔ₛ ∅) (x, 0)
              (by apply simplicialJoin_incl_left; assumption)
              (barycenter_join_left
                x_nin_X))[π₁
                (barycenter_disjoint_boundary (X ⋆ Y) (s ⊔ₛ ∅) (x, 0)
                  (by apply simplicialJoin_incl_left; assumption)
                  (barycenter_join_left x_nin_X))[simplex {(x, 0)} ⋆ ∂(s ⊔ₛ ∅)] ⋆
            Lk(X ⋆ Y, s ⊔ₛ ∅) (by apply simplicialJoin_incl_left; assumption)].simplices :=
  by
  simp only [Set.subset_def, simplicialJoin_mem, join_proj_mem]
  intro t t_in_join
  choose u u_in_join v v_in_Y t_eq_uv using t_in_join
  choose u' u'_in_join u₁ u₁_in_link u_decomp using u_in_join
  choose u₃ u₃_in_barycenter u₂ u₂_in_bd u'_decomp using u'_in_join
  subst u'_decomp
  use u₃ ⊔ₛ ∅ ∪ (u₂ ⊔ₛ ∅); constructor
  use u₃ ⊔ₛ ∅; constructor
  simp only [simplex, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at
    u₃_in_barycenter ⊢
  cases' u₃_in_barycenter with u₃_empty u₃_eq_x
  left
  rw [u₃_empty]
  simp only [simplexDisjointUnion, Finset.product_singleton, Finset.map_empty, Finset.empty_union]
  right
  rw [u₃_eq_x]
  simp only [simplexDisjointUnion, Finset.product_singleton, Finset.map_singleton,
    Function.Embedding.coeFn_mk, Finset.map_empty, Finset.union_empty]
  use u₂ ⊔ₛ ∅; constructor
  rw [simplexBoundary_mem_iff_subset, Finset.ssubset_iff_subset_ne] at u₂_in_bd ⊢
  choose u₂_ss_s u₂_ne_s using u₂_in_bd
  simp only [Ne.def, simplex_disjoint_subset_unique, simplex_disjoint_eq_unique, not_and]
  constructor; constructor; assumption; rfl
  intro contra; contradiction
  rfl
  use u₁ ⊔ₛ v; constructor
  simp only [link, Set.mem_sep_iff] at u₁_in_link ⊢
  choose u₁_in_X su₁_in_X su₁_disj using u₁_in_link
  constructor
  rw [simplicialJoin_mem]
  use u₁; constructor; assumption
  use v; constructor; assumption
  rfl
  constructor
  rw [simplex_disjoint_distr_union, Finset.empty_union, simplicialJoin_mem]
  use s ∪ u₁; constructor; assumption
  use v; constructor; assumption
  rfl
  rw [simplex_disjoint_distr_inter, Finset.empty_inter, su₁_disj]
  simp only [simplexDisjointUnion, Finset.product_singleton, Finset.map_empty, Finset.empty_union]
  simp only [simplex_disjoint_distr_union, Finset.empty_union, ← u_decomp]
  assumption

theorem stellar_join_distr_join_right (X Y : SimplicialComplex α) (s : Finset α) [s_ne : Nonempty s]
    (x : α) (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X) :
    π₁
            (barycenter_join_boundary_disjoint_link (X ⋆ Y) (s ⊔ₛ ∅) (x, 0)
              (by apply simplicialJoin_incl_left; assumption)
              (barycenter_join_left
                x_nin_X))[π₁
                (barycenter_disjoint_boundary (X ⋆ Y) (s ⊔ₛ ∅) (x, 0)
                  (by apply simplicialJoin_incl_left; assumption)
                  (barycenter_join_left x_nin_X))[simplex {(x, 0)} ⋆ ∂(s ⊔ₛ ∅)] ⋆
            Lk(X ⋆ Y, s ⊔ₛ ∅) (by apply simplicialJoin_incl_left; assumption)].simplices ⊆
      (π₁
              (barycenter_join_boundary_disjoint_link X s x s_in_X
                x_nin_X)[π₁ (barycenter_disjoint_boundary X s x s_in_X x_nin_X)[simplex {x} ⋆ ∂s] ⋆
              Lk(X, s) s_in_X] ⋆
          Y).simplices :=
  by
  simp only [Set.subset_def, simplicialJoin_mem, join_proj_mem]
  intro t t_in_img
  choose t' t'_in_join t₁ t₁_in_link t_decomp using t_in_img
  choose t₃ t₃_in_barycenter t₂ t₂_in_bd t'_decomp using t'_in_join
  subst t'_decomp
  simp only [link, Set.mem_sep_iff] at t₁_in_link
  choose t₁_in_XY st₁_in_XY st₁_disj using t₁_in_link
  rw [simplicialJoin_mem] at t₁_in_XY
  choose u₁ u₁_in_X v₁ v₁_in_Y t₁_eq_uv₁ using t₁_in_XY
  subst t₁_eq_uv₁
  have s_zero : ∀ a : α × ℕ, a ∈ s ⊔ₛ ∅ → a.snd = 0 :=
    by
    intro a a_in_s
    rw [simplex_disjoint_mem] at a_in_s
    cases' a_in_s with a_in_s contra
    choose a_in_s a_zero using a_in_s
    assumption
    choose contra a_one using contra
    have H : a.fst ∉ ∅ := by apply Finset.not_mem_empty
    contradiction
  rw [simplexBoundary_mem_iff_subset, Finset.ssubset_iff] at t₂_in_bd
  choose a a_nin_t₂ at₂_ss_s using t₂_in_bd
  use Finset.image Prod.fst (t₃ ∪ t₂) ∪ u₁; constructor
  use Finset.image Prod.fst (t₃ ∪ t₂); constructor
  use Finset.image Prod.fst t₃; constructor
  simp only [simplex, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at
    t₃_in_barycenter ⊢
  cases' t₃_in_barycenter with t₃_empty t₃_eq_x
  left
  rw [t₃_empty]
  apply Finset.image_empty
  right
  simp only [t₃_eq_x, Finset.image_singleton, Prod.fst]
  use Finset.image Prod.fst t₂; constructor
  rw [simplexBoundary_mem_iff_subset, Finset.ssubset_iff]
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
  rw [Finset.image_union]
  use u₁; constructor
  simp only [link, Set.mem_sep_iff]
  constructor; assumption
  constructor
  rw [simplex_disjoint_distr_union, simplicialJoin_sep] at st₁_in_XY
  choose su₁_in_X sv₁_in_Y using st₁_in_XY
  assumption
  rw [simplex_disjoint_distr_inter, simplex_disjoint_empty] at st₁_disj
  choose su₁_disj sv₁_disj using st₁_disj
  assumption
  rfl
  use v₁; constructor; assumption
  rw [← Finset.empty_union v₁, ← Finset.empty_union ∅, ← simplex_disjoint_distr_union,
    Finset.image_union, ← simplex_disjoint_distr_union]
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
    have H : b.fst ∉ ∅ := by apply Finset.not_mem_empty
    contradiction
    intro b_in_t₂
    left
    use b; constructor; assumption
    rfl
    have b_in_s : b ∈ s ⊔ₛ ∅ := by
      apply Finset.mem_of_subset at₂_ss_s
      rw [Finset.mem_insert]
      right; assumption
    specialize s_zero b b_in_s
    assumption
  have t₃_lift : Finset.image Prod.fst t₃ ⊔ₛ ∅ = t₃ :=
    by
    simp only [simplex, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at
      t₃_in_barycenter
    cases' t₃_in_barycenter with t₃_empty t₃_eq_x
    rw [t₃_empty, Finset.image_empty, simplex_disjoint_empty]
    constructor <;> rfl
    rw [t₃_eq_x]
    simp only [simplexDisjointUnion, Finset.image_singleton, Finset.product_singleton,
      Finset.map_singleton, Function.Embedding.coeFn_mk, Finset.map_empty, Finset.union_empty]
  rw [t₂_lift, t₃_lift]
  assumption

theorem stellar_join_distr_join (X Y : SimplicialComplex α) (s : Finset α) [s_ne : Nonempty s]
    (x : α) (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X) :
    (π₁
              (barycenter_join_boundary_disjoint_link X s x s_in_X
                x_nin_X)[π₁ (barycenter_disjoint_boundary X s x s_in_X x_nin_X)[simplex {x} ⋆ ∂s] ⋆
              Lk(X, s) s_in_X] ⋆
          Y).simplices =
      π₁
            (barycenter_join_boundary_disjoint_link (X ⋆ Y) (s ⊔ₛ ∅) (x, 0)
              (by apply simplicialJoin_incl_left; assumption)
              (barycenter_join_left
                x_nin_X))[π₁
                (barycenter_disjoint_boundary (X ⋆ Y) (s ⊔ₛ ∅) (x, 0)
                  (by apply simplicialJoin_incl_left; assumption)
                  (barycenter_join_left x_nin_X))[simplex {(x, 0)} ⋆ ∂(s ⊔ₛ ∅)] ⋆
            Lk(X ⋆ Y, s ⊔ₛ ∅) (by apply simplicialJoin_incl_left; assumption)].simplices :=
  by
  rw [Set.Subset.antisymm_iff]
  constructor
  apply stellar_join_distr_join_left
  apply stellar_join_distr_join_right

theorem stellar_subdiv_distr_join_left (X Y : SimplicialComplex α) (s : Finset α)
    [s_ne : Nonempty s] (x : α) (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X) :
    σ(X, s, x; s_ne, s_in_X, x_nin_X) ⋆ Y ≅
      σ(X ⋆ Y, s ⊔ₛ ∅, (x, 0); _, by apply simplicialJoin_incl_left; assumption,
        barycenter_join_left x_nin_X) :=
  by
  apply
    simplicial_iso_trans (σ(X, s, x; s_ne, s_in_X, x_nin_X) ⋆ Y)
      ((X\St(X, s)) s_in_X ⋆ Y ∪ π₁ _[π₁ _[simplex {x} ⋆ ∂s] ⋆ Lk(X, s) _] ⋆ Y)
  apply simplicial_iso_preserves_equiv
  apply simplicialJoin_distr_union_right
  apply simplicial_iso_preserves_equiv
  simp only [stellarSubdivision, simplicialUnion]
  rw [join_distr_starComplement_simplices, stellar_join_distr_join]

theorem barycenter_join_right {X Y : SimplicialComplex α} {x : α} :
    x ∉ vertices Y → (x, 1) ∉ vertices (X ⋆ Y) :=
  by
  contrapose
  simp only [Classical.not_not, simplicialJoin_vertices_mem_right]
  exact Set.mem_of_eq_of_mem rfl

theorem stellar_subdiv_distr_join_right (X Y : SimplicialComplex α) (t : Finset α)
    [t_ne : Nonempty t] (y : α) (t_in_Y : t ∈ Y.simplices) (y_nin_Y : y ∉ vertices Y) :
    X ⋆ σ(Y, t, y; t_ne, t_in_Y, y_nin_Y) ≅
      σ(X ⋆ Y, ∅ ⊔ₛ t, (y, 1); _, by apply simplicialJoin_incl_right; assumption,
        barycenter_join_right y_nin_Y) :=
  by
  apply
    simplicial_iso_trans (X ⋆ σ(Y, t, y; t_ne, t_in_Y, y_nin_Y))
      (σ(Y, t, y; t_ne, t_in_Y, y_nin_Y) ⋆ X)
  apply simplicialJoin_comm
  apply
    simplicial_iso_trans (σ(Y, t, y; t_ne, t_in_Y, y_nin_Y) ⋆ X)
      σ(Y ⋆ X, t ⊔ₛ ∅, (y, 0); _, by apply simplicialJoin_incl_left; assumption,
        barycenter_join_left y_nin_Y)
  apply stellar_subdiv_distr_join_left <;> assumption
  let f : SimplicialMap (Y ⋆ X) (X ⋆ Y) :=
    SimplicialMap.mk simplicialJoinCommMap (simplicialJoin_comm_simplicial Y X)
  let g : SimplicialMap (X ⋆ Y) (Y ⋆ X) :=
    SimplicialMap.mk simplicialJoinCommMap (simplicialJoin_comm_simplicial X Y)
  have gf_inv : IsInverseSimplicialIso f g :=
    by
    unfold IsInverseSimplicialIso
    constructor <;>
      · simp only [Set.restrict_eq_restrict_iff, Set.EqOn]
        intro x x_in_XY
        rw [simplicialJoin_mem_vertices] at x_in_XY
        simp only [f, g, SimplicialMap.comp, simplicialJoinCommMap, id.def, Function.comp_apply]
        cases' x_in_XY with x_in_X x_in_Y
        choose x_in_X x_zero using x_in_X
        simp only [x_zero, eq_self_iff_true, if_true, Nat.one_ne_zero, if_false]
        simp only [← x_zero, Prod.ext_iff, Prod.fst, Prod.snd]
        constructor <;> rfl
        choose x_in_Y x_one using x_in_Y
        simp only [x_one, eq_self_iff_true, if_true, Nat.one_ne_zero, if_false]
        simp only [← x_one, Prod.ext_iff, Prod.fst, Prod.snd]
        constructor <;> rfl
  have f_iso : IsSimplicialIso f := by
    unfold IsSimplicialIso
    use g
    apply gf_inv
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
    simp only [simplicialJoinCommMap, b_zero, eq_self_iff_true, if_true, Prod.ext_iff] at fb_a
    choose b_eq_a a_one using fb_a
    rw [@comm _ Eq] at a_one
    rw [b_eq_a] at b_in_t
    right; constructor <;> assumption
    choose contra b_one using contra
    have H : b.fst ∉ ∅ := by apply Finset.not_mem_empty
    contradiction
  · intro a_in_disj
    cases' a_in_disj with contra a_in_t
    choose contra a_zero using contra
    have H : a.fst ∉ ∅ := by apply Finset.not_mem_empty
    contradiction
    choose a_in_t a_one using a_in_t
    use(a.fst, 0); constructor
    simp only [Prod.fst, Prod.snd]
    left; constructor
    assumption
    rfl
    simp only [simplicialJoinCommMap, eq_self_iff_true, if_true, ← a_one, Prod.ext_iff,
      true_and_iff]
  simp only [simplicialJoinCommMap, eq_self_iff_true, if_true]
  simp only [simplicialJoinCommMap, Nat.one_ne_zero, if_false]

-- Lemma 3.1, p.10
theorem simplicialJoin_stellarEquiv (X Y Z W : SimplicialComplex α) :
    X ≅ₛₜ Y → Z ≅ₛₜ W → X ⋆ Z ≅ₛₜ Y ⋆ W :=
  by
  intro X_eq_Y Z_eq_W
  trans Y ⋆ Z
  unfold StellarEquiv at *
  induction' X_eq_Y with K L X_eq_K K_move_L H_ind
  rfl
  apply @Relation.ReflTransGen.tail _ _ _ (K ⋆ Z) (L ⋆ Z)
  apply H_ind
  simp only [StellarMove] at K_move_L ⊢
  cases K_move_L
  left
  choose t Ht Ht_ne y Hy K_subdiv_L using K_move_L
  use t ⊔ₛ ∅
  have Ht_empty : t ⊔ₛ ∅ ∈ (L ⋆ Z).simplices :=
    by
    rw [simplicialJoin_sep]
    constructor
    assumption
    apply simplicialComplex_empty_simplex
  use Ht_empty
  let Ht_empty_ne := @SimplexDisjoint.nonempty.left _ _ t Ht_ne
  use Ht_empty_ne
  use(y, 0)
  have Hy_0 : (y, 0) ∉ vertices (L ⋆ Z) :=
    by
    rw [simplicialJoin_vertices_mem_left]
    assumption
  use Hy_0
  rw [simplicial_iso_symm]
  apply
    simplicial_iso_trans (@stellarSubdivision _ _ (L ⋆ Z) (t ⊔ₛ ∅) Ht_empty_ne (y, 0) Ht_empty Hy_0)
      (@stellarSubdivision _ _ L t Ht_ne y Ht Hy ⋆ Z)
  rw [simplicial_iso_symm]
  apply @stellar_subdiv_distr_join_left _ _ _ _ _ Ht_ne <;> assumption
  apply simplicialJoin_iso_left
  rw [simplicial_iso_symm]
  assumption
  cases K_move_L
  right; left
  choose s Hs Hs_ne x Hx L_subdiv_K using K_move_L
  use s ⊔ₛ ∅
  have Hs_empty : s ⊔ₛ ∅ ∈ (K ⋆ Z).simplices :=
    by
    rw [simplicialJoin_sep]
    constructor
    assumption
    apply simplicialComplex_empty_simplex
  use Hs_empty
  let Hs_empty_ne := @SimplexDisjoint.nonempty.left _ _ s Hs_ne
  use Hs_empty_ne
  use(x, 0)
  have Hx_0 : (x, 0) ∉ vertices (K ⋆ Z) :=
    by
    rw [simplicialJoin_vertices_mem_left]
    assumption
  use Hx_0
  rw [simplicial_iso_symm]
  apply
    simplicial_iso_trans (@stellarSubdivision _ _ (K ⋆ Z) (s ⊔ₛ ∅) Hs_empty_ne (x, 0) Hs_empty Hx_0)
      (@stellarSubdivision _ _ K s Hs_ne x Hs Hx ⋆ Z)
  rw [simplicial_iso_symm]
  apply @stellar_subdiv_distr_join_left _ _ _ _ _ Hs_ne <;> assumption
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
  cases K_move_L
  left
  choose t Ht Ht_ne y Hy K_subdiv_L using K_move_L
  use∅ ⊔ₛ t
  have Ht_empty : ∅ ⊔ₛ t ∈ (Y ⋆ L).simplices :=
    by
    rw [simplicialJoin_sep]
    constructor
    apply simplicialComplex_empty_simplex
    assumption
  use Ht_empty
  let Ht_empty_ne := @SimplexDisjoint.nonempty.right _ _ t Ht_ne
  use Ht_empty_ne
  use(y, 1)
  have Hy_1 : (y, 1) ∉ vertices (Y ⋆ L) :=
    by
    rw [simplicialJoin_vertices_mem_right]
    assumption
  use Hy_1
  rw [simplicial_iso_symm]
  apply
    simplicial_iso_trans (@stellarSubdivision _ _ (Y ⋆ L) (∅ ⊔ₛ t) Ht_empty_ne (y, 1) Ht_empty Hy_1)
      (Y ⋆ @stellarSubdivision _ _ L t Ht_ne y Ht Hy)
  rw [simplicial_iso_symm]
  apply @stellar_subdiv_distr_join_right _ _ _ _ _ Ht_ne <;> assumption
  apply simplicialJoin_iso_right
  rw [simplicial_iso_symm]
  assumption
  cases K_move_L
  right; left
  choose s Hs Hs_ne x Hx L_subdiv_K using K_move_L
  use∅ ⊔ₛ s
  have Hs_empty : ∅ ⊔ₛ s ∈ (Y ⋆ K).simplices :=
    by
    rw [simplicialJoin_sep]
    constructor
    apply simplicialComplex_empty_simplex
    assumption
  use Hs_empty
  let Hs_empty_ne := @SimplexDisjoint.nonempty.right _ _ s Hs_ne
  use Hs_empty_ne
  use(x, 1)
  have Hx_1 : (x, 1) ∉ vertices (Y ⋆ K) :=
    by
    rw [simplicialJoin_vertices_mem_right]
    assumption
  use Hx_1
  rw [simplicial_iso_symm]
  apply
    simplicial_iso_trans (@stellarSubdivision _ _ (Y ⋆ K) (∅ ⊔ₛ s) Hs_empty_ne (x, 1) Hs_empty Hx_1)
      (Y ⋆ @stellarSubdivision _ _ K s Hs_ne x Hs Hx)
  rw [simplicial_iso_symm]
  apply @stellar_subdiv_distr_join_right _ _ _ _ _ Hs_ne <;> assumption
  apply simplicialJoin_iso_right
  rw [simplicial_iso_symm]
  assumption
  right; right
  apply simplicialJoin_iso_right
  assumption

theorem simplicialJoin_stellarEquiv_left (X Y Z : SimplicialComplex α) :
    X ≅ₛₜ Y → X ⋆ Z ≅ₛₜ Y ⋆ Z := by
  intro X_eq_Y
  apply simplicialJoin_stellarEquiv X Y Z Z
  assumption
  rfl

theorem simplicialJoin_stellarEquiv_right (X Y Z : SimplicialComplex α) :
    X ≅ₛₜ Y → Z ⋆ X ≅ₛₜ Z ⋆ Y := by
  intro X_eq_Y
  apply simplicialJoin_stellarEquiv Z Z X Y
  rfl
  assumption

theorem stellar_subdiv_link_of_starComplement_left (X : SimplicialComplex α) (s t : Finset α)
    [s_ne : Nonempty s] (x : α) (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X)
    (t_in_star_comp : t ∈ ((X\St(X, s)) s_in_X).simplices) :
    t ∉ π₁ (boundary_disjoint_link X s s_in_X)[Lk(X, s) s_in_X ⋆ ∂s].simplices →
      (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), t)
            (by simp only [stellarSubdivision, simplicialUnion, Set.mem_union]; left;
              assumption)).simplices ⊆
        (Lk(X, t)
            (by simp only [starComplement, Set.mem_sep_iff] at t_in_star_comp;
              choose t_in_X H using t_in_star_comp; assumption)).simplices :=
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
    apply X.subset_closed (t ∪ u)
    assumption
    apply Finset.subset_union_right
    constructor <;> assumption
  -- Case B + (C/D).
  · rw [join_proj_disj_union_mem] at ut_in_join
    choose t' t'_in_join u' u'_in_join t₁ t₁_in_link u₁ u₁_in_link t_decomp u_decomp tu'_in_join
      tu₁_in_link using ut_in_join
    rw [join_proj_disj_union_mem] at tu'_in_join
    choose t₃ t₃_in_barycenter u₃ u₃_in_barycenter t₂ t₂_in_bd u₂ u₂_in_bd t'_decomp u'_decomp
      tu₃_in_barycenter tu₂_in_bd using tu'_in_join
    subst t'_decomp
    subst u'_decomp
    simp only [simplex, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at
      t₃_in_barycenter
    cases' t₃_in_barycenter with t₃_empty contra
    rotate_left
    have x_in_X : x ∈ vertices X := by
      subst contra
      rw [t_decomp] at t_in_X
      rw [vertex_iff_singleton]
      apply X.subset_closed ({x} ∪ t₂ ∪ t₁)
      assumption
      rw [Finset.union_assoc]
      apply Finset.subset_union_left
    contradiction
    subst t₃_empty
    rw [Finset.empty_union] at t_decomp
    have contra : t ∈ π₁ (boundary_disjoint_link X s s_in_X)[Lk(X, s) s_in_X ⋆ ∂s].simplices :=
      by
      rw [join_proj_mem]
      use t₁; constructor; assumption
      use t₂; constructor; assumption
      rw [Finset.union_comm]
      assumption
    contradiction

theorem stellar_subdiv_link_of_starComplement_right (X : SimplicialComplex α) (s t : Finset α)
    [s_ne : Nonempty s] (x : α) (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X)
    (t_in_star_comp : t ∈ ((X\St(X, s)) s_in_X).simplices) :
    t ∉ π₁ (boundary_disjoint_link X s s_in_X)[Lk(X, s) s_in_X ⋆ ∂s].simplices →
      (Lk(X, t)
            (by simp only [starComplement, Set.mem_sep_iff] at t_in_star_comp;
              choose t_in_X H using t_in_star_comp; assumption)).simplices ⊆
        (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), t)
            (by simp only [stellarSubdivision, simplicialUnion, Set.mem_union]; left;
              assumption)).simplices :=
  by
  intro t_nin_join
  simp only [starComplement, Set.mem_sep_iff] at t_in_star_comp
  choose t_in_X s_nss_t using t_in_star_comp
  simp only [Set.subset_def, link, stellarSubdivision, simplicialUnion, starComplement,
    Set.mem_union, Set.mem_sep_iff]
  intro u u_in_link
  choose u_in_X tu_in_X tu_disj using u_in_link
  by_cases s_ss_u : s ⊆ u
  · have t_in_link : t ∈ (Lk(X, s) s_in_X).simplices :=
      by
      simp only [link, Set.mem_sep_iff]
      constructor; assumption
      constructor
      apply X.subset_closed (t ∪ u)
      assumption
      rw [Finset.union_comm]
      apply Finset.union_subset_union_right
      assumption
      rw [← Finset.subset_empty]
      apply @Finset.Subset.trans _ _ (t ∩ u)
      rw [Finset.inter_comm]
      apply Finset.inter_subset_inter_left
      assumption
      rw [Finset.subset_empty]
      assumption
    simp only [join_proj_mem, not_exists] at t_nin_join
    specialize t_nin_join t t_in_link
    specialize t_nin_join ∅ (simplicialComplex_empty_simplex (∂s))
    rw [Finset.union_empty] at t_nin_join
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
  simp only [link, Set.mem_sep_iff]
  constructor
  apply X.subset_closed t
  assumption
  apply Finset.sdiff_subset
  constructor
  rw [Finset.union_sdiff_self_eq_union]
  apply X.subset_closed (t ∪ u)
  assumption
  apply @Finset.Subset.trans _ _ (s ∪ (t ∪ u))
  rw [← Finset.union_assoc]
  apply Finset.subset_union_left
  rw [← Finset.union_eq_right] at s_ss_tu
  apply Finset.subset_of_eq
  assumption
  rw [Finset.inter_comm]
  apply Finset.sdiff_inter_self
  use t ∩ s; constructor
  rw [simplexBoundary_mem_iff_subset, Finset.ssubset_iff_subset_ne]
  constructor
  apply Finset.inter_subset_right
  rw [Ne.def, Finset.inter_eq_right]
  assumption
  rw [Finset.sdiff_union_inter]
  assumption

theorem stellar_subdiv_link_of_starComplement (X : SimplicialComplex α) (s t : Finset α)
    [s_ne : Nonempty s] (x : α) (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X)
    (t_in_star_comp : t ∈ ((X\St(X, s)) s_in_X).simplices) :
    t ∉ π₁ (boundary_disjoint_link X s s_in_X)[Lk(X, s) s_in_X ⋆ ∂s].simplices →
      (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), t)
            (by simp only [stellarSubdivision, simplicialUnion, Set.mem_union]; left;
              assumption)).simplices =
        (Lk(X, t)
            (by simp only [starComplement, Set.mem_sep_iff] at t_in_star_comp;
              choose t_in_X H using t_in_star_comp; assumption)).simplices :=
  by
  intro t_nin_join
  rw [Set.Subset.antisymm_iff]
  constructor
  apply stellar_subdiv_link_of_starComplement_left
  assumption
  apply stellar_subdiv_link_of_starComplement_right
  assumption

theorem stellar_subdiv_link_of_barycenter_left (X : SimplicialComplex α) (s : Finset α)
    [s_ne : Nonempty s] (x : α) (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X) :
    (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), {x})
          (by rw [← vertex_iff_singleton]; apply barycenter_vertex_stellar_subdiv)).simplices ⊆
      π₁ (boundary_disjoint_link X s s_in_X)[Lk(X, s) s_in_X ⋆ ∂s].simplices :=
  by
  rw [Set.subset_def]
  intro a a_in_link
  simp only [link, Set.mem_sep_iff] at a_in_link
  choose a_in_subdiv xa_in_subdiv xa_disj using a_in_link
  simp only [stellarSubdivision, simplicialUnion, Set.mem_union] at xa_in_subdiv
  cases' xa_in_subdiv with xa_in_star_comp xa_in_join
  simp only [starComplement, Set.mem_sep_iff] at xa_in_star_comp
  choose xa_in_X s_nss_xa using xa_in_star_comp
  have contra : x ∈ vertices X := by
    rw [vertex_iff_singleton]
    apply X.subset_closed ({x} ∪ a)
    assumption
    apply Finset.subset_union_left
  contradiction
  rw [join_proj_disj_union_mem] at xa_in_join
  choose x' x'_in_join a' a'_in_join x₁ x₁_in_link a₁ a₁_in_link x_decomp a_decomp xa'_in_join
    xa₁_in_link using xa_in_join
  rw [join_proj_disj_union_mem] at xa'_in_join
  choose x₃ x₃_in_barycenter a₃ a₃_in_barycenter x₂ x₂_in_bd a₂ a₂_in_bd x'_decomp a'_decomp
    xa₃_in_barycenter xa₂_in_bd using xa'_in_join
  subst x'_decomp
  subst a'_decomp
  have x₁_empty : x₁ = ∅ :=
    by
    have x₁_ss_x : x₁ ⊆ {x} := by
      rw [x_decomp]
      apply Finset.subset_union_right
    rw [Finset.subset_singleton_iff] at x₁_ss_x
    cases' x₁_ss_x with x₁_empty x₁_eq_x
    assumption
    have contra : x ∈ vertices X :=
      by
      simp only [x₁_eq_x, link, Set.mem_sep_iff] at x₁_in_link
      choose x_in_X sx_in_X sx_disj using x₁_in_link
      rw [vertex_iff_singleton]
      assumption
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
    have contra : x ∈ vertices X := by
      rw [x₂_eq_x] at x₂_in_bd
      rw [vertex_iff_singleton]
      apply simplex_if_in_subcomplex
      apply x₂_in_bd
      apply simplexBoundary_subcomplex
      assumption
    contradiction
  subst x₁_empty
  subst x₂_empty
  simp only [Finset.union_empty] at x_decomp
  subst x_decomp
  have a₃_empty : a₃ = ∅ :=
    by
    simp only [simplex, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at
      xa₃_in_barycenter
    cases' xa₃_in_barycenter with xa₃_empty xa₃_eq_x
    rw [Finset.union_eq_empty] at xa₃_empty
    choose x_empty a₃_empty using xa₃_empty
    have contra : {(x : α)} ≠ (∅ : Finset α) := Finset.singleton_ne_empty x
    contradiction
    have xa₃_disj : {x} ∩ a₃ = ∅ := by
      rw [← Finset.subset_empty]
      apply @Finset.Subset.trans _ _ ({x} ∩ a)
      rw [a_decomp, Finset.union_assoc]
      apply Finset.inter_subset_inter_left
      apply Finset.subset_union_left
      rw [Finset.subset_empty]
      assumption
    rw [singleton_inter_eq_empty_iff_not_mem] at xa₃_disj
    rw [Finset.union_eq_left, Finset.subset_singleton_iff] at xa₃_eq_x
    cases' xa₃_eq_x with a₃_empty a₃_eq_x
    assumption
    have contra : x ∈ a₃ := by
      rw [a₃_eq_x]
      apply Finset.mem_singleton_self
    contradiction
  subst a₃_empty
  rw [Finset.empty_union] at a_decomp
  rw [join_proj_mem]
  use a₁; constructor; assumption
  use a₂; constructor; assumption
  rw [Finset.union_comm]
  assumption

theorem stellar_subdiv_link_of_barycenter_right (X : SimplicialComplex α) (s : Finset α)
    [s_ne : Nonempty s] (x : α) (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X) :
    π₁ (boundary_disjoint_link X s s_in_X)[Lk(X, s) s_in_X ⋆ ∂s].simplices ⊆
      (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), {x})
          (by rw [← vertex_iff_singleton]; apply barycenter_vertex_stellar_subdiv)).simplices :=
  by
  rw [Set.subset_def]
  intro a a_in_img
  rw [join_proj_mem] at a_in_img
  choose a₁ a₁_in_link a₂ a₂_in_bd a_decomp using a_in_img
  simp only [link, Set.mem_sep_iff, stellarSubdivision, simplicialUnion, Set.mem_union]
  constructor; right
  simp only [join_proj_mem]
  use∅ ∪ a₂; constructor
  use∅; constructor; apply simplicialComplex_empty_simplex
  use a₂; constructor; assumption
  rfl
  use a₁; constructor; assumption
  rw [Finset.empty_union, Finset.union_comm]
  assumption
  constructor; right
  simp only [join_proj_mem]
  use{x} ∪ a₂; constructor
  use{x}; constructor
  simp only [simplex, Finset.mem_coe]
  apply Finset.mem_powerset_self
  use a₂; constructor; assumption
  rfl
  use a₁; constructor; assumption
  rw [a_decomp, Finset.union_comm a₁ a₂, ← Finset.union_assoc]
  rw [singleton_inter_eq_empty_iff_not_mem, a_decomp]
  by_contra x_in_a
  rw [Finset.mem_union] at x_in_a
  have contra : x ∈ vertices X := by
    rw [vertex_iff_in_simplex]
    cases' x_in_a with x_in_a₁ x_in_a₂
    use a₁; constructor
    apply simplex_if_in_subcomplex
    apply a₁_in_link
    apply link_subcomplex
    assumption
    use a₂; constructor
    apply simplex_if_in_subcomplex
    apply a₂_in_bd
    apply simplexBoundary_subcomplex
    assumption
    assumption
  contradiction

theorem stellar_subdiv_link_of_barycenter (X : SimplicialComplex α) (s : Finset α)
    [s_ne : Nonempty s] (x : α) (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X) :
    (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), {x})
          (by rw [← vertex_iff_singleton]; apply barycenter_vertex_stellar_subdiv)).simplices =
      π₁ (boundary_disjoint_link X s s_in_X)[Lk(X, s) s_in_X ⋆ ∂s].simplices :=
  by
  rw [Set.Subset.antisymm_iff]
  constructor
  apply stellar_subdiv_link_of_barycenter_left
  apply stellar_subdiv_link_of_barycenter_right

theorem star_boundary_is_join_left (X : SimplicialComplex α) (s : Finset α) [s_ne : Nonempty s]
    (x : α) (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X) :
    ((X\St(X, s)) s_in_X ∩
          π₁
              (barycenter_join_boundary_disjoint_link X s x s_in_X
                x_nin_X)[π₁ (barycenter_disjoint_boundary X s x s_in_X x_nin_X)[simplex {x} ⋆ ∂s] ⋆
              Lk(X, s) s_in_X]).simplices ⊆
      π₁ (boundary_disjoint_link X s s_in_X)[Lk(X, s) s_in_X ⋆ ∂s].simplices :=
  by
  rw [Set.subset_def]
  intro t t_in_inter
  simp only [simplicialInter, Set.mem_inter_iff] at t_in_inter
  choose t_in_star_comp t_in_join using t_in_inter
  simp only [join_proj_mem] at t_in_join
  choose t' t'_in_join t₁ t₁_in_link t_decomp using t_in_join
  choose t₃ t₃_in_barycenter t₂ t₂_in_bd t'_decomp using t'_in_join
  subst t'_decomp
  simp only [starComplement, Set.mem_sep_iff] at t_in_star_comp
  choose t_in_X s_nss_t using t_in_star_comp
  have t₃_empty : t₃ = ∅ :=
    by
    simp only [simplex, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at
      t₃_in_barycenter
    cases' t₃_in_barycenter with t₃_empty t₃_eq_x
    assumption
    have contra : x ∈ vertices X := by
      rw [vertex_iff_singleton]
      apply X.subset_closed t
      assumption
      rw [← t₃_eq_x, t_decomp, Finset.union_assoc]
      apply Finset.subset_union_left
    contradiction
  subst t₃_empty
  rw [Finset.empty_union] at t_decomp
  rw [join_proj_mem]
  use t₁; constructor; assumption
  use t₂; constructor; assumption
  rw [Finset.union_comm]
  assumption

theorem star_boundary_is_join_right (X : SimplicialComplex α) (s : Finset α) [s_ne : Nonempty s]
    (x : α) (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X) :
    π₁ (boundary_disjoint_link X s s_in_X)[Lk(X, s) s_in_X ⋆ ∂s].simplices ⊆
      ((X\St(X, s)) s_in_X ∩
          π₁
              (barycenter_join_boundary_disjoint_link X s x s_in_X
                x_nin_X)[π₁ (barycenter_disjoint_boundary X s x s_in_X x_nin_X)[simplex {x} ⋆ ∂s] ⋆
              Lk(X, s) s_in_X]).simplices :=
  by
  rw [Set.subset_def]
  intro t t_in_join
  rw [join_proj_mem] at t_in_join
  choose t₁ t₁_in_link t₂ t₂_in_bd t_decomp using t_in_join
  simp only [simplicialInter, Set.mem_inter_iff]
  constructor
  simp only [starComplement, Set.mem_sep_iff]
  simp only [link, Set.mem_sep_iff] at t₁_in_link
  choose t₁_in_X st₁_in_X st₁_disj using t₁_in_link
  rw [simplexBoundary_mem_iff_subset] at t₂_in_bd
  constructor
  rw [Finset.ssubset_iff_subset_ne] at t₂_in_bd
  choose t₂_ss_s t₂_ne_s using t₂_in_bd
  apply X.subset_closed (s ∪ t₁)
  assumption
  rw [t_decomp, Finset.union_comm]
  apply Finset.union_subset_union_left
  assumption
  simp only [Finset.subset_iff, Classical.not_forall, not_imp]
  rw [Finset.ssubset_iff] at t₂_in_bd
  choose a a_nin_t₂ at₂_ss_s using t₂_in_bd
  rw [Finset.subset_iff] at at₂_ss_s
  specialize at₂_ss_s (Finset.mem_insert_self a t₂)
  use a; constructor; assumption
  simp only [Finset.eq_empty_iff_forall_not_mem, Finset.mem_inter, not_and] at st₁_disj
  specialize st₁_disj a at₂_ss_s
  simp only [t_decomp, Finset.mem_union, not_or]
  constructor <;> assumption
  simp only [join_proj_mem]
  use∅ ∪ t₂; constructor
  use∅; constructor; apply simplicialComplex_empty_simplex
  use t₂; constructor; assumption
  rfl
  use t₁; constructor; assumption
  rw [Finset.empty_union, Finset.union_comm, t_decomp]

theorem star_boundary_is_join (X : SimplicialComplex α) (s : Finset α) [s_ne : Nonempty s] (x : α)
    (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X) :
    ((X\St(X, s)) s_in_X ∩
          π₁
              (barycenter_join_boundary_disjoint_link X s x s_in_X
                x_nin_X)[π₁ (barycenter_disjoint_boundary X s x s_in_X x_nin_X)[simplex {x} ⋆ ∂s] ⋆
              Lk(X, s) s_in_X]).simplices =
      π₁ (boundary_disjoint_link X s s_in_X)[Lk(X, s) s_in_X ⋆ ∂s].simplices :=
  by
  rw [Set.Subset.antisymm_iff]
  constructor
  apply star_boundary_is_join_left
  apply star_boundary_is_join_right

theorem star_boundary_diff_ne {X : SimplicialComplex α} {s t : Finset α} [s_ne : Nonempty s]
    {s_in_X : s ∈ X.simplices} :
    t ∈ π₁ (boundary_disjoint_link X s s_in_X)[Lk(X, s) s_in_X ⋆ ∂s].simplices →
      Nonempty ↥(s \ t) :=
  by
  intro t_in_star_bd
  rw [join_proj_mem] at t_in_star_bd
  choose t₁ t₁_in_link t₂ t₂_in_bd t_decomp using t_in_star_bd
  simp only [link, Set.mem_sep_iff] at t₁_in_link
  choose t₁_in_X st₁_in_X st₁_disj using t₁_in_link
  rw [simplexBoundary_mem_iff_subset] at t₂_in_bd
  rw [Finset.nonempty_coe_sort, Finset.sdiff_nonempty]
  simp only [Finset.subset_iff, Classical.not_forall, not_imp]
  rw [Finset.ssubset_iff] at t₂_in_bd
  choose a a_nin_t₂ at₂_ss_s using t₂_in_bd
  rw [Finset.subset_iff] at at₂_ss_s
  specialize at₂_ss_s (Finset.mem_insert_self a t₂)
  use a; constructor; assumption
  simp only [Finset.eq_empty_iff_forall_not_mem, Finset.mem_inter, not_and] at st₁_disj
  specialize st₁_disj a at₂_ss_s
  simp only [t_decomp, Finset.mem_union, not_or]
  constructor <;> assumption

theorem star_boundary_mem_link {X : SimplicialComplex α} {s t : Finset α} {s_in_X : s ∈ X.simplices}
    {t_in_X : t ∈ X.simplices} :
    t ∈ π₁ (boundary_disjoint_link X s s_in_X)[Lk(X, s) s_in_X ⋆ ∂s].simplices →
      s \ t ∈ (Lk(X, t) t_in_X).simplices :=
  by
  intro t_in_star_bd
  rw [join_proj_mem] at t_in_star_bd
  choose t₁ t₁_in_link t₂ t₂_in_bd t_decomp using t_in_star_bd
  simp only [link, Set.mem_sep_iff] at t₁_in_link ⊢
  choose t₁_in_X st₁_in_X st₁_disj using t₁_in_link
  constructor
  apply X.subset_closed s
  assumption
  apply Finset.sdiff_subset
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

theorem not_mem_link_vertices {X : SimplicialComplex α} {s : Finset α} {x : α}
    {s_in_X : s ∈ X.simplices} : x ∉ vertices X → x ∉ vertices (Lk(X, s) s_in_X) :=
  by
  contrapose
  simp only [Classical.not_not]
  apply is_subcomplex_vertices
  apply link_subcomplex

theorem stellar_subdiv_anticomm_link_left_ac (X : SimplicialComplex α) (s t : Finset α)
    [s_ne : Nonempty s] (x : α) (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X)
    (t_in_X : t ∈ X.simplices)
    (t_in_star_bd : t ∈ π₁ (boundary_disjoint_link X s s_in_X)[Lk(X, s) s_in_X ⋆ ∂s].simplices) :
    ∀ u : Finset α,
      u ∈ (starComplement X s s_in_X).simplices →
        t ∪ u ∈ (starComplement X s s_in_X).simplices →
          t ∩ u = ∅ →
            u ∈
              σ(Lk(X, t) t_in_X, s \ t, x; star_boundary_diff_ne t_in_star_bd,
                  star_boundary_mem_link t_in_star_bd, not_mem_link_vertices x_nin_X).simplices :=
  by
  intro u u_in_star_comp tu_in_star_comp tu_disj
  simp only [link, stellarSubdivision, starComplement, simplicialUnion] at u_in_star_comp
    tu_in_star_comp ⊢
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

theorem stellar_subdiv_anticomm_link_left_ad_tu_in_X (X : SimplicialComplex α)
    (s t u t₁ u₁ t₂ u₂ : Finset α) [s_ne : Nonempty ↥s] (stu₁_in_X : s ∪ (t₁ ∪ u₁) ∈ X.simplices)
    (t₂_in_bd : t₂ ⊂ s) (u₂_in_bd : u₂ ⊂ s) (t_decomp : t = t₁ ∪ t₂) (u_decomp : u = u₁ ∪ u₂) :
    t ∪ u ∈ X.simplices := by
  rw [u_decomp, t_decomp]
  apply X.subset_closed (t₁ ∪ u₁ ∪ s)
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

theorem stellar_subdiv_anticomm_link_left_ad_st_nss_u (X : SimplicialComplex α)
    (s t u t₁ u₁ t₂ u₂ : Finset α) [s_ne : Nonempty ↥s] (x : α) (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X) (t_in_X : t ∈ X.simplices) (u_in_X : u ∈ X.simplices)
    (tu_disj : t ∩ u = ∅) (su₁_disj : s ∩ u₁ = ∅) (t₂_in_bd : t₂ ⊂ s)
    (tu_in_join :
      t₂ ∪ u₂ ∈ π₁ (barycenter_disjoint_boundary X s x s_in_X x_nin_X)[simplex {x} ⋆ ∂s].simplices)
    (t_decomp : t = t₁ ∪ t₂) (u_decomp : u = u₁ ∪ u₂) : ¬s \ t₂ ⊆ u :=
  by
  rw [join_proj_disj_union_mem] at tu_in_join
  choose t₃ t₃_in_barycenter u₃ u₃_in_barycenter t₂ t₂_in_bd u₂ u₂_in_bd tu₂_decomp using tu_in_join
  choose t₂_decomp u₂_decomp tu₃_in_barycenter tu₂_in_bd using tu₂_decomp
  have u₃_empty : u₃ = ∅ :=
    by
    simp only [simplex, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at
      u₃_in_barycenter
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

theorem stellar_subdiv_anticomm_link_left_ad (X : SimplicialComplex α) (s t : Finset α)
    [s_ne : Nonempty s] (x : α) (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X)
    (t_in_X : t ∈ X.simplices)
    (t_in_star_bd : t ∈ π₁ (boundary_disjoint_link X s s_in_X)[Lk(X, s) s_in_X ⋆ ∂s].simplices) :
    ∀ u : Finset α,
      u ∈ (starComplement X s s_in_X).simplices →
        t ∪ u ∈
            π₁
                  (barycenter_join_boundary_disjoint_link X s x s_in_X
                    x_nin_X)[π₁
                      (barycenter_disjoint_boundary X s x s_in_X x_nin_X)[simplex {x} ⋆ ∂s] ⋆
                  Lk(X, s) s_in_X].simplices →
          t ∩ u = ∅ →
            u ∈
              σ(Lk(X, t) t_in_X, s \ t, x; star_boundary_diff_ne t_in_star_bd,
                  star_boundary_mem_link t_in_star_bd, not_mem_link_vertices x_nin_X).simplices :=
  by
  intro u u_in_star_comp tu_in_join tu_disj
  simp only [link, stellarSubdivision, starComplement, simplicialUnion] at u_in_star_comp tu_in_join
    ⊢
  simp only [Set.mem_union, Set.mem_sep_iff] at u_in_star_comp ⊢
  choose u_in_X s_nss_u using u_in_star_comp
  rw [join_proj_disj_union_mem] at tu_in_join
  choose t'₂ t'₂_in_join u'₂ u'₂_in_join t₁ t₁_in_link u₁ u₁_in_link tu_decomp using tu_in_join
  choose t_decomp u_decomp tu_in_join tu_in_link using tu_decomp
  simp only [Set.mem_sep_iff] at t₁_in_link u₁_in_link tu_in_link
  choose t₁_in_X st₁_in_X st₁_disj using t₁_in_link
  choose u₁_in_X su₁_in_X su₁_disj using u₁_in_link
  choose tu₁_in_X stu₁_in_X stu₁_disj using tu_in_link
  rw [join_proj_mem] at t'₂_in_join u'₂_in_join
  choose u₃ u₃_in_barycenter u₂ u₂_in_bd u'_decomp using u'₂_in_join
  choose t₃ t₃_in_barycenter t₂ t₂_in_bd t'_decomp using t'₂_in_join
  subst u'_decomp
  subst t'_decomp
  rw [simplexBoundary_mem_iff_subset] at u₂_in_bd t₂_in_bd
  have u₃_empty : u₃ = ∅ :=
    by
    simp only [simplex, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at
      u₃_in_barycenter
    cases' u₃_in_barycenter with u₃_empty u₃_eq_x
    exact u₃_empty
    have contra : x ∈ vertices X := by
      rw [vertex_iff_singleton]
      apply X.subset_closed u
      exact u_in_X
      rw [u_decomp, u₃_eq_x, Finset.union_assoc]
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
      rw [t_decomp, t₃_eq_x, Finset.union_assoc]
      apply Finset.subset_union_left
    contradiction
  subst u₃
  subst t₃
  simp only [Finset.empty_union] at u_decomp t_decomp tu_in_join
  rw [Finset.union_comm] at u_decomp t_decomp
  left; constructor; constructor
  exact u_in_X
  constructor
  exact
    stellar_subdiv_anticomm_link_left_ad_tu_in_X X s t u t₁ u₁ t₂ u₂ stu₁_in_X t₂_in_bd u₂_in_bd
      t_decomp u_decomp
  exact tu_disj
  rw [t_decomp, Finset.sdiff_union_distrib]
  have st₁_sdiff_ident : s \ t₁ = s :=
    by
    apply Finset.sdiff_eq_self_of_disjoint
    rw [Finset.disjoint_iff_inter_eq_empty]
    exact st₁_disj
  rw [st₁_sdiff_ident, Finset.inter_sdiff, Finset.inter_self]
  exact
    stellar_subdiv_anticomm_link_left_ad_st_nss_u X s t u t₁ u₁ t₂ u₂ x s_in_X x_nin_X t_in_X u_in_X
      tu_disj su₁_disj t₂_in_bd tu_in_join t_decomp u_decomp

theorem stellar_subdiv_anticomm_link_left_bc (X : SimplicialComplex α) (s t : Finset α)
    [s_ne : Nonempty s] (x : α) (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X)
    (t_in_X : t ∈ X.simplices)
    (t_in_star_bd : t ∈ π₁ (boundary_disjoint_link X s s_in_X)[Lk(X, s) s_in_X ⋆ ∂s].simplices) :
    ∀ u : Finset α,
      u ∈
          π₁
                (barycenter_join_boundary_disjoint_link X s x s_in_X
                  x_nin_X)[π₁
                    (barycenter_disjoint_boundary X s x s_in_X x_nin_X)[simplex {x} ⋆ ∂s] ⋆
                Lk(X, s) s_in_X].simplices →
        t ∪ u ∈ (starComplement X s s_in_X).simplices →
          t ∩ u = ∅ →
            u ∈
              σ(Lk(X, t) t_in_X, s \ t, x; star_boundary_diff_ne t_in_star_bd,
                  star_boundary_mem_link t_in_star_bd, not_mem_link_vertices x_nin_X).simplices :=
  by
  intro u u_in_join tu_in_star_comp tu_disj
  simp only [link, stellarSubdivision, starComplement, simplicialUnion] at u_in_join tu_in_star_comp
    ⊢
  simp only [Set.mem_union, Set.mem_sep_iff] at tu_in_star_comp ⊢
  choose tu_in_X s_nss_tu using tu_in_star_comp
  rw [join_proj_mem] at u_in_join
  choose u'₂ u'₂_in_join u₁ u₁_in_link u_decomp using u_in_join
  simp only [Set.mem_sep_iff] at u₁_in_link
  choose u₁_in_X su₁_in_X su₁_disj using u₁_in_link
  rw [join_proj_mem] at u'₂_in_join
  choose u₃ u₃_in_barycenter u₂ u₂_in_bd u'_decomp using u'₂_in_join
  subst u'_decomp
  left; constructor; constructor
  apply X.subset_closed (t ∪ u)
  assumption
  apply Finset.subset_union_right
  constructor <;> assumption
  revert s_nss_tu
  contrapose
  simp only [Classical.not_not]
  intro st_ss_u
  apply @Finset.union_subset_left _ _ s t
  rw [← Finset.union_sdiff_self_eq_union, Finset.union_sdiff_symm]
  apply Finset.union_subset_union_right
  assumption

theorem stellar_subdiv_anticomm_link_left_bd_u_ss_st (X : SimplicialComplex α)
    (s t u t₁ u₁ t₂ u₂ u₃ : Finset α) [s_ne : Nonempty ↥s] (x : α) (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X) (t_in_X : t ∈ X.simplices)
    (t_in_star_bd : t ∈ π₁ (boundary_disjoint_link X s s_in_X)[Lk(X, s) s_in_X ⋆ ∂s].simplices)
    (tu_disj : t ∩ u = ∅) (t₂_in_bd : t₂ ⊂ s) (tu₂_in_bd : t₂ ∪ u₂ ⊂ s) (t_decomp : t = t₂ ∪ t₁)
    (u_decomp : u = u₃ ∪ u₂ ∪ u₁) : u₂ ⊂ s \ t₂ :=
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
  exact congr_arg fun a : Finset α => a ∪ t₂

theorem stellar_subdiv_anticomm_link_left_bd_u_mem_link (X : SimplicialComplex α)
    (s t u t₁ u₁ t₂ u₂ u₃ : Finset α) [s_ne : Nonempty ↥s] (x : α) (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X) (t_in_X : t ∈ X.simplices)
    (t_in_star_bd : t ∈ π₁ (boundary_disjoint_link X s s_in_X)[Lk(X, s) s_in_X ⋆ ∂s].simplices)
    (tu_disj : t ∩ u = ∅) (stu₁_in_X : s ∪ (t₁ ∪ u₁) ∈ X.simplices) (t_decomp : t = t₂ ∪ t₁)
    (u_decomp : u = u₃ ∪ u₂ ∪ u₁) (t₂_ss_s : t₂ ⊆ s) : t ∪ u₁ ∈ X.simplices ∧ t ∩ u₁ = ∅ :=
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

theorem stellar_subdiv_anticomm_link_left_bd_stu_mem_link (X : SimplicialComplex α)
    (s t u t₁ u₁ t₂ u₂ u₃ : Finset α) [s_ne : Nonempty ↥s] (x : α) (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X) (t_in_X : t ∈ X.simplices)
    (t_in_star_bd : t ∈ π₁ (boundary_disjoint_link X s s_in_X)[Lk(X, s) s_in_X ⋆ ∂s].simplices)
    (tu_disj : t ∩ u = ∅) (su₁_disj : s ∩ u₁ = ∅) (stu₁_in_X : s ∪ (t₁ ∪ u₁) ∈ X.simplices)
    (t_decomp : t = t₂ ∪ t₁) (u_decomp : u = u₃ ∪ u₂ ∪ u₁) (st₁_sdiff_ident : s \ t₁ = s)
    (t₂_ss_s : t₂ ⊆ s) : s \ t ∪ u₁ ∈ (Lk(X, t) t_in_X).simplices ∧ s \ t ∩ u₁ = ∅ :=
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

theorem stellar_subdiv_anticomm_link_left_bd (X : SimplicialComplex α) (s t : Finset α)
    [s_ne : Nonempty s] (x : α) (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X)
    (t_in_X : t ∈ X.simplices)
    (t_in_star_bd : t ∈ π₁ (boundary_disjoint_link X s s_in_X)[Lk(X, s) s_in_X ⋆ ∂s].simplices) :
    ∀ u : Finset α,
      u ∈
          π₁
                (barycenter_join_boundary_disjoint_link X s x s_in_X
                  x_nin_X)[π₁
                    (barycenter_disjoint_boundary X s x s_in_X x_nin_X)[simplex {x} ⋆ ∂s] ⋆
                Lk(X, s) s_in_X].simplices →
        t ∪ u ∈
            π₁
                  (barycenter_join_boundary_disjoint_link X s x s_in_X
                    x_nin_X)[π₁
                      (barycenter_disjoint_boundary X s x s_in_X x_nin_X)[simplex {x} ⋆ ∂s] ⋆
                  Lk(X, s) s_in_X].simplices →
          t ∩ u = ∅ →
            u ∈
              σ(Lk(X, t) t_in_X, s \ t, x; star_boundary_diff_ne t_in_star_bd,
                  star_boundary_mem_link t_in_star_bd, not_mem_link_vertices x_nin_X).simplices :=
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
    simp only [simplex, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at
      t₃_in_barycenter
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
  clear t₂_decomp u₂_decomp u_in_join u'₂_in_join t'₂_in_join tu₃_in_barycenter t₃_in_barycenter t'₂
    u'₂
  right
  rw [join_proj_mem]
  have tu₂_disj : t₂ ∩ u₂ = ∅ := by
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
  have u₂_ss_st₂_sdiff : u₂ ⊂ s \ t₂ := by
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

theorem star_boundary_mem_subdiv {X : SimplicialComplex α} {s t : Finset α} [s_ne : Nonempty s]
    {x : α} {s_in_X : s ∈ X.simplices} {x_nin_X : x ∉ vertices X} :
    t ∈ π₁ (boundary_disjoint_link X s s_in_X)[Lk(X, s) s_in_X ⋆ ∂s].simplices →
      t ∈ σ(X, s, x; s_ne, s_in_X, x_nin_X).simplices :=
  by
  intro t_in_star_bd
  rw [join_proj_mem] at t_in_star_bd
  choose t₁ t₁_in_link t₂ t₂_in_bd t_decomp using t_in_star_bd
  simp only [stellarSubdivision, simplicialUnion, Set.mem_union, join_proj_mem]
  right
  use∅ ∪ t₂; constructor
  use∅; constructor; apply simplicialComplex_empty_simplex
  use t₂; constructor; assumption
  rfl
  use t₁; constructor; assumption
  rw [Finset.empty_union, Finset.union_comm]
  assumption

theorem stellar_subdiv_anticomm_link_left (X : SimplicialComplex α) (s t : Finset α)
    [s_ne : Nonempty s] (x : α) (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X)
    (t_in_X : t ∈ X.simplices)
    (t_in_star_bd : t ∈ π₁ (boundary_disjoint_link X s s_in_X)[Lk(X, s) s_in_X ⋆ ∂s].simplices) :
    (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), t) (star_boundary_mem_subdiv t_in_star_bd)).simplices ⊆
      σ(Lk(X, t) t_in_X, s \ t, x; star_boundary_diff_ne t_in_star_bd,
          star_boundary_mem_link t_in_star_bd, not_mem_link_vertices x_nin_X).simplices :=
  by
  simp only [stellarSubdivision, simplicialUnion]
  simp only [Set.subset_def]
  intro u u_in_link
  simp only [link, Set.mem_sep_iff] at u_in_link
  choose u_in_subdiv tu_in_subdiv tu_disj using u_in_link
  cases' u_in_subdiv with u_in_star_comp u_in_join <;>-- Cases A, B resp.
    cases' tu_in_subdiv with tu_in_star_comp tu_in_join
  -- Cases C, D resp.
    apply stellar_subdiv_anticomm_link_left_ac <;>
    assumption
  apply stellar_subdiv_anticomm_link_left_ad <;> assumption
  apply stellar_subdiv_anticomm_link_left_bc <;> assumption
  apply stellar_subdiv_anticomm_link_left_bd <;> assumption

theorem stellar_subdiv_anticomm_link_right_e (X : SimplicialComplex α) (s t : Finset α)
    [s_ne : Nonempty s] (x : α) (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X)
    (t_in_X : t ∈ X.simplices)
    (t_in_star_bd : t ∈ π₁ (boundary_disjoint_link X s s_in_X)[Lk(X, s) s_in_X ⋆ ∂s].simplices) :
    ∀ u : Finset α,
      u ∈
          (@starComplement _ _ (Lk(X, t) t_in_X) (s \ t) (star_boundary_diff_ne t_in_star_bd)
              (star_boundary_mem_link t_in_star_bd)).simplices →
        u ∈
          (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), t)
              (star_boundary_mem_subdiv t_in_star_bd)).simplices :=
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
  use y; constructor; assumption
  simp only [Finset.mem_union, not_or]
  constructor <;> assumption
  assumption

theorem stellar_subdiv_anticomm_link_right_f (X : SimplicialComplex α) (s t : Finset α)
    [s_ne : Nonempty s] (x : α) (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X)
    (t_in_X : t ∈ X.simplices)
    (t_in_star_bd : t ∈ π₁ (boundary_disjoint_link X s s_in_X)[Lk(X, s) s_in_X ⋆ ∂s].simplices) :
    ∀ u : Finset α,
      u ∈
          π₁
                (barycenter_join_boundary_disjoint_link (Lk(X, t) t_in_X) (s \ t) x
                  (star_boundary_mem_link t_in_star_bd)
                  (not_mem_link_vertices
                    x_nin_X))[π₁
                    (barycenter_disjoint_boundary X (s \ t) x
                      (by apply X.subset_closed s; assumption; apply Finset.sdiff_subset)
                      x_nin_X)[simplex {x} ⋆ ∂(s \ t)] ⋆
                Lk(Lk(X, t) t_in_X, s \ t) (star_boundary_mem_link t_in_star_bd)].simplices →
        u ∈
          (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), t)
              (star_boundary_mem_subdiv t_in_star_bd)).simplices :=
  by
  intro u u_in_join
  simp only [link, starComplement, stellarSubdivision, simplicialUnion] at u_in_join ⊢
  simp only [Set.mem_union, Set.mem_sep_iff]
  rw [join_proj_mem] at u_in_join
  choose u'₂ u'₂_in_join u₁ u₁_in_link u_decomp using u_in_join
  rw [join_proj_mem] at u'₂_in_join
  choose u₃ u₃_in_barycenter u₂ u₂_in_bd u'₂_decomp using u'₂_in_join
  subst u'₂_decomp
  let u₁_in_link := u₁_in_link
  let u₂_in_bd' := u₂_in_bd
  rw [@simplexBoundary_mem_iff_subset _ _ _ _ (star_boundary_diff_ne t_in_star_bd)] at u₂_in_bd
  simp only [Set.mem_sep_iff] at u₁_in_link
  choose u₁_in_t_link stu₁_in_t_link stu₁_disj using u₁_in_link
  choose u₁_in_X tu₁_in_X tu₁_disj using u₁_in_t_link
  choose stu₁_in_X tstu₁_in_X tstu₁_disj using stu₁_in_t_link
  rw [join_proj_mem] at t_in_star_bd
  choose t₁ t₁_in_link t₂ t₂_in_bd t_decomp using t_in_star_bd
  let t₁_in_link := t₁_in_link
  let t₁_in_bd' := t₂_in_bd
  simp only [link, Set.mem_sep_iff] at t₁_in_link
  choose t₁_in_X st₁_in_X st₁_disj using t₁_in_link
  rw [simplexBoundary_mem_iff_subset] at t₂_in_bd
  have st₁_sdiff_ident : s \ t₁ = s :=
    by
    apply Finset.sdiff_eq_self_of_disjoint
    rw [Finset.disjoint_iff_inter_eq_empty]
    assumption
  constructor; right
  rw [join_proj_mem]
  use u₃ ∪ u₂; constructor
  rw [join_proj_mem]
  use u₃; constructor; assumption
  use u₂; constructor
  rw [simplexBoundary_mem_iff_subset]
  apply @Finset.ssubset_of_ssubset_of_subset _ _ (s \ t)
  assumption
  apply Finset.sdiff_subset
  rfl
  use u₁; constructor
  simp only [Set.mem_sep_iff]
  constructor; assumption
  constructor
  apply X.subset_closed (t ∪ (s \ t ∪ u₁))
  assumption
  rw [← Finset.union_assoc, Finset.union_sdiff_self_eq_union, Finset.union_assoc]
  apply Finset.subset_union_right
  rw [← Finset.subset_empty]
  apply @Finset.Subset.trans _ _ ((t ∪ s \ t) ∩ u₁)
  rw [Finset.union_sdiff_self_eq_union, Finset.union_inter_distrib_right]
  apply Finset.subset_union_right
  rw [Finset.subset_empty, Finset.union_inter_distrib_right, Finset.union_eq_empty]
  constructor <;> assumption
  assumption
  constructor; right
  rw [join_proj_disj_union_mem]
  use t₂; constructor
  rw [join_proj_mem]
  use∅; constructor; apply simplicialComplex_empty_simplex
  use t₂; constructor
  assumption
  symm
  apply Finset.empty_union
  use u₃ ∪ u₂; constructor
  rw [join_proj_mem]
  use u₃; constructor; assumption
  use u₂; constructor
  rw [simplexBoundary_mem_iff_subset]
  apply @Finset.ssubset_of_ssubset_of_subset _ _ (s \ t)
  assumption
  apply Finset.sdiff_subset
  rfl
  use t₁; constructor; assumption
  use u₁; constructor
  simp only [Set.mem_sep_iff]
  constructor; assumption
  constructor
  apply X.subset_closed (t ∪ (s \ t ∪ u₁))
  assumption
  rw [← Finset.union_assoc, Finset.union_sdiff_self_eq_union, Finset.union_assoc]
  apply Finset.subset_union_right
  rw [← Finset.subset_empty]
  apply @Finset.Subset.trans _ _ ((t ∪ s \ t) ∩ u₁)
  rw [Finset.union_sdiff_self_eq_union, Finset.union_inter_distrib_right]
  apply Finset.subset_union_right
  rw [Finset.subset_empty, Finset.union_inter_distrib_right, Finset.union_eq_empty]
  constructor <;> assumption
  constructor
  rw [Finset.union_comm]
  assumption
  constructor; assumption
  constructor
  rw [join_proj_disj_union_mem]
  use∅; constructor; apply simplicialComplex_empty_simplex
  use u₃; constructor; assumption
  use t₂; constructor
  assumption
  use u₂; constructor
  rw [simplexBoundary_mem_iff_subset]
  apply @Finset.ssubset_of_ssubset_of_subset _ _ (s \ t)
  assumption
  apply Finset.sdiff_subset
  constructor
  symm
  apply Finset.empty_union
  constructor; rfl
  constructor
  rw [Finset.empty_union]
  assumption
  rw [simplexBoundary_mem_iff_subset]
  rw [t_decomp, Finset.sdiff_union_distrib, st₁_sdiff_ident, Finset.inter_sdiff,
    Finset.inter_self] at u₂_in_bd
  rw [Finset.ssubset_iff_subset_ne] at t₂_in_bd u₂_in_bd ⊢
  choose t₂_ss_s t₂_ne_s using t₂_in_bd
  choose u₂_ss_st₂ u₂_ne_st₂ using u₂_in_bd
  constructor
  apply Finset.union_subset
  assumption
  apply @Finset.Subset.trans _ _ (s \ t₂)
  assumption
  apply Finset.sdiff_subset
  have st₂u₂_ne : s \ (t₂ ∪ u₂) ≠ ∅ :=
    by
    rw [Ne.def, Finset.sdiff_union_distrib, ← Finset.sdiff_sdiff_left',
      Finset.sdiff_eq_empty_iff_subset]
    rw [← Finset.le_iff_subset] at u₂_ss_st₂ ⊢
    have H : u₂ < s \ t₂ := by
      rw [lt_iff_le_and_ne]
      constructor <;> assumption
    rw [finset.partial_order.lt_iff_le_not_le] at H
    choose H1 H2 using H
    assumption
  rw [Ne.def, Finset.ext_iff, Classical.not_forall]
  rw [Ne.def, Finset.eq_empty_iff_forall_not_mem, Classical.not_forall] at st₂u₂_ne
  choose y y_nin_st₂u₂ using st₂u₂_ne
  use y
  simp only [not_iff, Finset.mem_sdiff, Finset.mem_union, not_and_or, not_or, Classical.not_not] at
    y_nin_st₂u₂ ⊢
  choose y_in_s y_nin_t₂u₂ using y_nin_st₂u₂
  constructor <;> intros <;> assumption
  simp only [Set.mem_sep_iff]
  constructor
  apply X.subset_closed (t ∪ u₁)
  assumption
  rw [t_decomp, Finset.union_comm t₁ t₂, Finset.union_assoc]
  apply Finset.subset_union_right
  constructor
  apply X.subset_closed (t ∪ (s \ t ∪ u₁))
  assumption
  rw [← Finset.union_assoc t (s \ t), Finset.union_sdiff_self_eq_union, t_decomp]
  rw [Finset.union_comm (t₁ ∪ t₂) s, Finset.union_comm t₁ t₂]
  rw [← Finset.union_assoc s t₂, Finset.union_assoc (s ∪ t₂)]
  apply Finset.union_subset_union_left
  apply Finset.subset_union_left
  rw [Finset.inter_union_distrib_left, Finset.union_eq_empty]
  constructor; assumption
  rw [← Finset.subset_empty]
  apply @Finset.Subset.trans _ _ ((t ∪ s \ t) ∩ u₁)
  rw [Finset.union_sdiff_self_eq_union, Finset.union_inter_distrib_right]
  apply Finset.subset_union_right
  rw [Finset.subset_empty, Finset.union_inter_distrib_right, Finset.union_eq_empty]
  constructor <;> assumption
  simp only [t_decomp, u_decomp, Finset.inter_union_distrib_left, Finset.union_inter_distrib_right,
    Finset.union_eq_empty]
  constructor; constructor; constructor
  rw [← Finset.disjoint_iff_inter_eq_empty]
  apply @disjoint_complexes_disjoint_simplices _ _ (Lk(X, s) s_in_X) (simplex {x})
  simp only [link, Set.mem_sep_iff]
  constructor; assumption
  constructor <;> assumption
  assumption
  apply barycenter_disjoint_link X s x s_in_X x_nin_X
  rw [← Finset.disjoint_iff_inter_eq_empty]
  apply @disjoint_complexes_disjoint_simplices _ _ (Lk(X, s) s_in_X) (∂s)
  simp only [link, Set.mem_sep_iff]
  constructor; assumption
  constructor <;> assumption
  apply @Set.mem_of_subset_of_mem _ (∂(s \ t)).simplices
  apply subsimplex_boundary_subcomplex
  apply Finset.sdiff_subset
  assumption
  apply boundary_disjoint_link
  rw [← Finset.subset_empty]
  apply @Finset.Subset.trans _ _ (t ∩ u₁)
  rw [t_decomp, Finset.union_comm, Finset.union_inter_distrib_right]
  apply Finset.subset_union_right
  rw [Finset.subset_empty]
  assumption
  constructor; constructor
  rw [← Finset.disjoint_iff_inter_eq_empty]
  apply @disjoint_complexes_disjoint_simplices _ _ (∂s) (simplex {x})
  rw [simplexBoundary_mem_iff_subset]
  assumption
  assumption
  apply @Disjoint.symm _ _ _ (vertices (simplex {x})) (vertices (∂s))
  apply barycenter_disjoint_boundary X s x s_in_X x_nin_X
  rw [t_decomp, Finset.sdiff_union_distrib, st₁_sdiff_ident, Finset.inter_sdiff, Finset.inter_self,
    Finset.ssubset_iff_subset_ne] at u₂_in_bd
  choose u₂_ss_st₂ u₂_ne_st₂ using u₂_in_bd
  rw [Finset.subset_iff] at u₂_ss_st₂
  rw [Finset.eq_empty_iff_forall_not_mem]
  intro y
  by_cases H : y ∈ u₂
  specialize u₂_ss_st₂ H
  simp only [Finset.mem_sdiff] at u₂_ss_st₂
  choose y_in_s y_nin_t₂ using u₂_ss_st₂
  simp only [Finset.mem_inter, not_and_or]
  left; assumption
  simp only [Finset.mem_inter, not_and_or]
  right; assumption
  rw [← Finset.disjoint_iff_inter_eq_empty]
  apply @disjoint_complexes_disjoint_simplices _ _ (∂s) (Lk(X, s) s_in_X)
  rw [simplexBoundary_mem_iff_subset]
  assumption
  simp only [link, Set.mem_sep_iff]
  constructor; assumption
  constructor
  apply X.subset_closed (t ∪ (s \ t ∪ u₁))
  assumption
  rw [← Finset.union_assoc, Finset.union_sdiff_self_eq_union, Finset.union_assoc]
  apply Finset.subset_union_right
  rw [← Finset.subset_empty]
  apply @Finset.Subset.trans _ _ ((t ∪ s \ t) ∩ u₁)
  rw [Finset.union_sdiff_self_eq_union, Finset.union_inter_distrib_right]
  apply Finset.subset_union_right
  rw [Finset.subset_empty, Finset.union_inter_distrib_right, Finset.union_eq_empty]
  constructor <;> assumption
  apply @Disjoint.symm _ _ _ (vertices (Lk(X, s) s_in_X)) (vertices (∂s))
  apply boundary_disjoint_link X s s_in_X

theorem stellar_subdiv_anticomm_link_right (X : SimplicialComplex α) (s t : Finset α)
    [s_ne : Nonempty s] (x : α) (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X)
    (t_in_X : t ∈ X.simplices)
    (t_in_star_bd : t ∈ π₁ (boundary_disjoint_link X s s_in_X)[Lk(X, s) s_in_X ⋆ ∂s].simplices) :
    σ(Lk(X, t) t_in_X, s \ t, x; star_boundary_diff_ne t_in_star_bd,
          star_boundary_mem_link t_in_star_bd, not_mem_link_vertices x_nin_X).simplices ⊆
      (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), t)
          (star_boundary_mem_subdiv t_in_star_bd)).simplices :=
  by
  simp only [stellarSubdivision, simplicialUnion]
  simp only [Set.subset_def]
  intro u u_in_subdiv
  simp only [Set.mem_union] at u_in_subdiv
  cases' u_in_subdiv with u_in_star_comp u_in_join
  -- Cases E + F, resp.
    apply stellar_subdiv_anticomm_link_right_e <;>
    assumption
  apply stellar_subdiv_anticomm_link_right_f <;> assumption

theorem stellar_subdiv_anticomm_link (X : SimplicialComplex α) (s t : Finset α) [s_ne : Nonempty s]
    (x : α) (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X) (t_in_X : t ∈ X.simplices)
    (t_in_star_bd : t ∈ π₁ (boundary_disjoint_link X s s_in_X)[Lk(X, s) s_in_X ⋆ ∂s].simplices) :
    (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), t) (star_boundary_mem_subdiv t_in_star_bd)).simplices =
      σ(Lk(X, t) t_in_X, s \ t, x; star_boundary_diff_ne t_in_star_bd,
          star_boundary_mem_link t_in_star_bd, not_mem_link_vertices x_nin_X).simplices :=
  by
  apply Set.eq_of_subset_of_subset
  apply stellar_subdiv_anticomm_link_left
  apply stellar_subdiv_anticomm_link_right
