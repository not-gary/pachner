import Pachner.Constructions.Join
import Pachner.Subcomplex.SimplexBoundary
import Pachner.Subcomplex.Link

variable {E F 𝕜 : Type _}
variable [DecidableEq E] [DecidableEq F] [DecidableEq 𝕜]
variable [AddCommGroup E] [AddCommGroup F]
variable [Ring 𝕜] [Nontrivial 𝕜]
variable {X Y : AbstractSimplicialComplex E} {s t : Finset E} {x : E}

-- Show that, for disjoint complexes, projection to the first coordinate is a coercion.
theorem simplicialJoinProj_injective
  : Disjoint X.vertices Y.vertices → Set.InjOn Prod.fst (X ⋆ Y : AbstractSimplicialComplex (E × 𝕜)).vertices :=
by
  intro X_disj_Y
  simp only [Set.InjOn, vertices_setOf, SimplicialJoin, Set.mem_diff, Set.mem_union, Set.mem_setOf]
  simp only [vertices_setOf, Set.disjoint_iff_forall_ne, Set.mem_setOf] at X_disj_Y
  intro x₁ x₁_in_lhs x₂ x₂_in_rhs
  choose s₁ s₁_in_join x₁_in_s₁ using x₁_in_lhs
  choose s₁_in_join s₁_ne using s₁_in_join
  choose u₁ u₁_in_X v₁ v₁_in_Y uv₁_eq_s₁ using s₁_in_join
  rw [← uv₁_eq_s₁, simplexDisjoint_mem_iff] at x₁_in_s₁
  choose s₂ s₂_in_join x₂_in_s₂ using x₂_in_rhs
  choose s₂_in_join s₂_ne using s₂_in_join
  choose u₂ u₂_in_X v₂ v₂_in_Y uv₂_eq_s₂ using s₂_in_join
  rw [← uv₂_eq_s₂, simplexDisjoint_mem_iff] at x₂_in_s₂
  cases' x₁_in_s₁ with x₁_in_X x₁_in_Y <;> cases' x₂_in_s₂ with x₂_in_X x₂_in_Y

  -- x₁, x₂ ∈ X case.
  intro x₁_eq_x₂
  choose x₁_in_u₁ x₁_zero using x₁_in_X
  choose x₂_in_u₂ x₂_zero using x₂_in_X
  rw [← x₂_zero] at x₁_zero
  rw [Prod.ext_iff]
  constructor <;> assumption

  -- x₁ ∈ X, x₂ ∈ Y case.
  contrapose
  intro x₁_neq_x₂
  choose x₁_in_u₁ x₁_zero using x₁_in_X
  choose x₂_in_v₂ x₂_one using x₂_in_Y

  cases' u₁_in_X with u₁_in_X u₁_empty
  cases' v₂_in_Y with v₂_in_Y v₂_empty

  have H₁ : ∃ s ∈ X.faces, x₁.fst ∈ s :=
  by
    use u₁
  specialize X_disj_Y H₁
  have H₂ : ∃ s ∈ Y.faces, x₂.fst ∈ s :=
  by
    use v₂
  specialize X_disj_Y H₂
  assumption

  -- v₂ = ∅ case.
  rw [Set.mem_singleton_iff] at v₂_empty
  rw [v₂_empty] at x₂_in_v₂
  contradiction
  -- u₁ = ∅ case.
  rw [Set.mem_singleton_iff] at u₁_empty
  rw [u₁_empty] at x₁_in_u₁
  contradiction

  -- x₁ ∈ Y, x₂ ∈ X case.
  contrapose
  intro x₁_neq_x₂
  choose x₁_in_v₁ x₁_one using x₁_in_Y
  choose x₂_in_u₂ x₂_zero using x₂_in_X

  cases' u₂_in_X with u₂_in_X u₂_empty
  cases' v₁_in_Y with v₁_in_Y v₁_empty

  have H₂ : ∃ s ∈ X.faces, x₂.fst ∈ s :=
  by
    use u₂
  specialize X_disj_Y H₂
  have H₁ : ∃ s ∈ Y.faces, x₁.fst ∈ s :=
  by
    use v₁
  specialize X_disj_Y H₁
  rw [← ne_eq, ne_comm]
  assumption

  -- v₁ = ∅ case.
  rw [Set.mem_singleton_iff] at v₁_empty
  rw [v₁_empty] at x₁_in_v₁
  contradiction
  -- u₂ = ∅ case.
  rw [Set.mem_singleton_iff] at u₂_empty
  rw [u₂_empty] at x₂_in_u₂
  contradiction

  -- x₁, x₂ ∈ Y case.
  intro x₁_eq_x₂
  choose x₁_in_v₁ x₁_one using x₁_in_Y
  choose x₂_in_v₂ x₂_one using x₂_in_Y
  rw [← x₂_one] at x₁_one
  rw [Prod.ext_iff]
  constructor <;> assumption

def SimplicialJoinProj {X Y : AbstractSimplicialComplex E} (H : Disjoint X.vertices Y.vertices)
  : SimplicialCoe (X ⋆ Y : AbstractSimplicialComplex (E × 𝕜)) E :=
      SimplicialCoe.mk Prod.fst (simplicialJoinProj_injective H)

notation "π₁[" 𝕜 "]" => @SimplicialJoinProj _ 𝕜 _ _ _ _ _ _ _

theorem simplicialJoinProj_mem_vertices
    (H : Disjoint X.vertices Y.vertices)
  : x ∈ ((π₁[𝕜] H).coe ''ˢ (X ⋆ Y : AbstractSimplicialComplex (E × 𝕜))).vertices ↔ x ∈ X.vertices ∨ x ∈ Y.vertices :=
by
  simp only [vertices_setOf, SimplicialImage, SimplicialJoin, Set.mem_diff, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf, SimplicialJoinProj]
  constructor
  -- x ∈ X ⋆ Y case.
  intro x_in_join
  choose u u_in_img x_in_u using x_in_join
  choose v v_in_join proj_v_u using u_in_img
  choose v_in_join v_ne using v_in_join
  choose s s_in_X t t_in_Y st_eq_v using v_in_join
  rw [← proj_v_u, Finset.mem_image] at x_in_u
  choose y y_in_v proj_y_x using x_in_u
  rw [← st_eq_v, simplexDisjoint_mem_iff] at y_in_v
  cases' y_in_v with y_in_X y_in_Y
  left
  choose y_in_s y_zero using y_in_X
  cases' s_in_X with s_in_X contra
  subst proj_y_x
  use s

  rw [contra] at y_in_s
  contradiction

  right
  choose y_in_t y_one using y_in_Y
  cases' t_in_Y with t_in_Y contra
  subst proj_y_x
  use t

  rw [contra] at y_in_t
  contradiction

  -- x ∈ X ∪ Y case.
  intro x_in_union
  cases' x_in_union with x_in_X x_in_Y

  -- x ∈ X subcase.
  choose s s_in_X x_in_s using x_in_X
  use s; constructor
  use s ⊔ₛ ∅; constructor
  constructor
  use s; constructor; left; assumption
  use ∅; constructor; right; rfl
  rfl
  rw [Set.notMem_singleton_iff, ne_eq, simplexDisjoint_empty, not_and_or]
  left; apply Finset.ne_empty_of_mem x_in_s

  simp only [SimplexDisjointUnion, Finset.image_union, Finset.empty_product, Finset.image_empty,
    Finset.union_empty]
  simp only [Finset.ext_iff, Finset.mem_image]
  intro a
  constructor
  intro a_in_img
  choose b b_in_prod proj_b_a using a_in_img
  simp only [Finset.mem_product] at b_in_prod
  choose b_in_s b_zero using b_in_prod
  subst proj_b_a
  assumption
  intro a_in_s
  use (a, 0); constructor
  simp only [Finset.mem_product, Prod.fst, Prod.snd, Finset.mem_singleton]
  constructor; assumption; trivial
  simp only [Prod.fst]
  assumption

  -- x ∈ Y subcase.
  choose t t_in_Y x_in_t using x_in_Y
  use t; constructor
  use ∅ ⊔ₛ t; constructor
  constructor
  use ∅; constructor; right; rfl
  use t; constructor; left; assumption
  rfl
  rw [Set.notMem_singleton_iff, ne_eq, simplexDisjoint_empty, not_and_or]
  right; apply Finset.ne_empty_of_mem x_in_t

  simp only [SimplexDisjointUnion, Finset.image_union, Finset.empty_product, Finset.image_empty,
    Finset.empty_union]
  simp only [Finset.ext_iff, Finset.mem_image]
  intro a
  constructor
  intro a_in_img
  choose b b_in_prod proj_b_a using a_in_img
  simp only [Finset.mem_product] at b_in_prod
  choose b_in_s b_one using b_in_prod
  subst proj_b_a
  assumption
  intro a_in_s
  use(a, 1); constructor
  simp only [Finset.mem_product, Prod.fst, Prod.snd, Finset.mem_singleton]
  constructor; assumption; trivial
  simp only [Prod.fst]
  assumption

theorem simplexDisjointUnion_simplicialJoinProj : Finset.image Prod.fst (s ⊔ₛ t : Finset (E × 𝕜)) = s ∪ t :=
by
  simp only [SimplexDisjointUnion, Finset.image_union, Finset.ext_iff, Finset.mem_image,
    Finset.mem_union]
  intro x
  constructor
  intro x_in_img
  cases' x_in_img with x_in_s x_in_t
  left
  choose y y_in_prod proj_y_x using x_in_s
  simp only [Finset.mem_product] at y_in_prod
  choose y_in_s y_zero using y_in_prod
  subst proj_y_x
  assumption
  right
  choose y y_in_prod proj_y_x using x_in_t
  simp only [Finset.mem_product] at y_in_prod
  choose y_in_t y_one using y_in_prod
  subst proj_y_x
  assumption
  intro x_in_st
  cases' x_in_st with x_in_s x_in_t
  left
  use(x, 0); constructor
  simp only [Finset.mem_product]
  constructor
  assumption
  apply Finset.mem_singleton_self
  simp only [Prod.fst]
  right
  use(x, 1); constructor
  simp only [Finset.mem_product]
  constructor
  assumption
  apply Finset.mem_singleton_self
  simp only [Prod.fst]

theorem simplicialJoinProj_mem
    (H : Disjoint X.vertices Y.vertices)
  : s ∈ ((π₁[𝕜] H).coe ''ˢ (X ⋆ Y)).faces ↔ ∃ t ∈ X.faces ∪ {∅}, ∃ u ∈ Y.faces ∪ {∅}, s = t ∪ u ∧ s ≠ ∅ :=
by
  simp only [SimplicialImage, SimplicialJoin, SimplicialJoinProj, Set.mem_diff, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf]
  constructor

  -- s ∈ X ⋆ Y case.
  intro s_in_join
  choose v v_in_join proj_v_s using s_in_join
  choose v_in_join v_ne using v_in_join
  choose t t_in_X u u_in_Y tu_eq_v using v_in_join
  simp only at proj_v_s
  rw [← tu_eq_v, simplexDisjointUnion_simplicialJoinProj] at proj_v_s
  use t; constructor; assumption
  use u; constructor; assumption
  constructor
  symm; assumption

  subst proj_v_s
  rw [ne_eq, Finset.union_eq_empty, not_and_or]
  cases' t_in_X with t_in_X t_empty
  left
  revert t_in_X
  contrapose
  rw [not_not]
  intro t_empty
  rw [t_empty]
  apply X.empty_notMem

  cases' u_in_Y with u_in_Y u_empty
  right
  revert u_in_Y
  contrapose
  rw [not_not]
  intro u_empty
  rw [u_empty]
  apply Y.empty_notMem

  subst t_empty u_empty tu_eq_v
  rw [Set.notMem_singleton_iff, ne_eq, simplexDisjoint_empty, not_and_or] at v_ne
  cases v_ne <;> contradiction

  -- s X ∪ Y case.
  intro x_decomp
  choose t t_in_X u u_in_Y s_eq_tu s_ne using x_decomp
  rw [← @simplexDisjointUnion_simplicialJoinProj E 𝕜] at s_eq_tu
  use t ⊔ₛ u; constructor; constructor
  use t; constructor; assumption
  use u

  rw [Set.notMem_singleton_iff, ne_eq, simplexDisjoint_empty, not_and_or]
  cases' t_in_X with t_in_X t_empty
  left
  revert t_in_X
  contrapose
  rw [not_not]
  intro t_empty
  rw [t_empty]
  apply X.empty_notMem

  cases' u_in_Y with u_in_Y u_empty
  right
  revert u_in_Y
  contrapose
  rw [not_not]
  intro t_empty
  rw [t_empty]
  apply Y.empty_notMem

  subst t_empty u_empty s_eq_tu
  rw [ne_eq, Finset.image_eq_empty, simplexDisjoint_empty, not_and_or] at s_ne
  cases s_ne <;> contradiction

  symm; assumption

theorem simplicialJoinProj_union_mem
    (H : Disjoint X.vertices Y.vertices)
  : s ∪ t ∈ ((π₁[𝕜] H).coe ''ˢ (X ⋆ Y)).faces ↔
      ∃ (s₁ : _) (_ : s₁ ∈ X.faces ∪ {∅}) (t₁ : _) (_ : t₁ ∈ X.faces ∪ {∅})
        (s₂ : _) (_ : s₂ ∈ Y.faces ∪ {∅}) (t₂ : _) (_ : t₂ ∈ Y.faces ∪ {∅}),
          s = s₁ ∪ s₂ ∧ t = t₁ ∪ t₂ ∧ s₁ ∪ t₁ ∈ X.faces ∪ {∅} ∧ s₂ ∪ t₂ ∈ Y.faces ∪ {∅} ∧ s ∪ t ≠ ∅ :=
by
  rw [simplicialJoinProj_mem]
  constructor

  -- s ∪ t ∈ X ⋆ Y case.
  intro st_in_join
  choose u u_in_X v v_in_X st_eq_uv st_ne using st_in_join
  use s ∩ u; constructor
  use t ∩ u; constructor
  use s ∩ v; constructor
  use t ∩ v; constructor
  constructor

  rw [← Finset.inter_union_distrib_left, ← st_eq_uv, Finset.union_comm, Finset.inter_union_self]
  constructor
  rw [← Finset.inter_union_distrib_left, ← st_eq_uv, Finset.inter_union_self]
  constructor
  rw [← Finset.union_inter_distrib_right, st_eq_uv, Finset.inter_comm, Finset.union_comm,
    Finset.inter_union_self]
  assumption

  rw [Set.mem_union, Set.mem_singleton_iff] at ⊢ v_in_X
  constructor
  cases' v_in_X with v_in_Y v_empty
  left
  apply Y.down_closed
  assumption

  rw [← Finset.union_inter_distrib_right]
  apply Finset.inter_subset_right
  rw [← Finset.union_inter_distrib_right, st_eq_uv, Finset.inter_comm,
    Finset.inter_union_self]
  revert v_in_Y
  contrapose
  rw [not_not]
  intro v_empty
  rw [v_empty]
  apply Y.empty_notMem

  right
  subst v_empty
  simp only [Finset.inter_empty, Finset.union_idempotent]
  assumption

  cases' v_in_X with v_in_Y v_empty
  by_cases tv_empty : t ∩ v = ∅
  right; rw [Set.mem_singleton_iff]; assumption
  left
  apply Y.down_closed
  assumption
  apply Finset.inter_subset_right
  assumption

  right
  rw [Set.mem_singleton_iff] at ⊢ v_empty
  subst v_empty
  rw [Finset.inter_empty]

  cases' v_in_X with v_in_Y v_empty
  by_cases sv_empty : s ∩ v = ∅
  right; rw [Set.mem_singleton_iff]; assumption
  left
  apply Y.down_closed
  assumption
  apply Finset.inter_subset_right
  assumption

  right
  rw [Set.mem_singleton_iff] at ⊢ v_empty
  subst v_empty
  rw [Finset.inter_empty]

  cases' u_in_X with u_in_X u_empty
  by_cases tu_empty : t ∩ u = ∅
  right; rw [Set.mem_singleton_iff]; assumption
  left
  apply X.down_closed
  assumption
  apply Finset.inter_subset_right
  assumption

  right
  rw [Set.mem_singleton_iff] at ⊢ u_empty
  subst u_empty
  rw [Finset.inter_empty]

  cases' u_in_X with u_in_X u_empty
  by_cases su_empty : s ∩ u = ∅
  right; rw [Set.mem_singleton_iff]; assumption
  left
  apply X.down_closed
  assumption
  apply Finset.inter_subset_right
  assumption

  right
  rw [Set.mem_singleton_iff] at ⊢ u_empty
  subst u_empty
  rw [Finset.inter_empty]

  -- s ∪ t decomp case.
  intro st_decomp
  choose s₁ s₁_in_X t₁ t₁_in_X s₂ s₂_in_Y t₂ t₂_in_Y st_decomp using st_decomp
  choose s_decomp t_decomp st₁_in_X st₂_in_Y st_ne using st_decomp
  use s₁ ∪ t₁; constructor; assumption
  use s₂ ∪ t₂; constructor; assumption
  rw [Finset.union_comm s₂, Finset.union_assoc, ← Finset.union_assoc t₁,
    Finset.union_comm (t₁ ∪ t₂), ← Finset.union_assoc]
  rw [← s_decomp, ← t_decomp]
  constructor; rfl
  assumption

-- TODO: General result on existence of coercion for complexes over ℤ.
-- Useful for combinatorial mfds.
-- cf. Lean 3 unported code for former def'n using ℕ.

theorem disjoint_barycenter_boundary
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
  : Disjoint ((simplex {x}).vertices) ((∂s).vertices) :=
by
  rw [Set.disjoint_left]
  intro y y_in_barycenter
  apply Set.notMem_subset
  rw [Set.subset_def]
  intro z
  apply simplexBoundary_subcomplex_vertices s_in_X
  simp only [AbstractSimplicialComplex.vertices, simplex] at y_in_barycenter
  simp only [Finset.coe_powerset, Finset.coe_singleton, Set.mem_diff, Set.mem_preimage,
    Set.mem_powerset_iff, Set.subset_singleton_iff, Set.mem_singleton_iff, forall_eq,
    Finset.singleton_ne_empty, not_false_eq_true, and_true,
    Set.setOf_eq_eq_singleton] at y_in_barycenter
  subst y_in_barycenter
  assumption

theorem disjoint_barycenter_join_boundary_link
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
  : Disjoint (((π₁[𝕜] (disjoint_barycenter_boundary s_in_X x_nin_X)).coe ''ˢ ((simplex {x}) ⋆ ∂s : AbstractSimplicialComplex (E × 𝕜))).vertices)
       (Lk(X, s).vertices) :=
by
  rw [Set.disjoint_left]
  intro y y_in_join
  rw [simplicialJoinProj_mem_vertices] at y_in_join
  simp only [AbstractSimplicialComplex.vertices_eq, Link, Set.mem_iUnion, not_exists]
  intro u u_in_link
  simp only [Set.mem_sep_iff] at u_in_link
  rcases u_in_link with ⟨u_in_X, su_in_X, su_empty⟩
  cases' y_in_join with y_in_barycenter y_in_bd

  -- y ∈ {x}
  simp only [AbstractSimplicialComplex.vertices_eq, simplex, Set.mem_iUnion] at y_in_barycenter
  choose t Ht y_in_t using y_in_barycenter
  rw [Set.mem_diff, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at Ht
  choose Ht t_ne using Ht

  cases' Ht with t_empty t_ne
  rw [Set.mem_singleton_iff] at t_ne
  contradiction

  rw [Finset.mem_coe, t_ne, Finset.mem_singleton] at y_in_t
  simp only [AbstractSimplicialComplex.vertices_eq, Set.mem_iUnion, not_exists] at x_nin_X
  specialize x_nin_X u
  specialize x_nin_X u_in_X
  rw [y_in_t]
  apply x_nin_X

  -- y ∈ ∂s
  simp only [AbstractSimplicialComplex.vertices_eq, SimplexBoundary, Set.mem_iUnion] at y_in_bd
  choose t Ht y_in_t using y_in_bd
  rw [Set.mem_diff, Finset.mem_coe, Finset.mem_powerset, Finset.subset_iff] at Ht
  choose t_sset_s t_ne using Ht
  rw [Set.mem_insert_iff, not_or] at t_ne
  choose t_ne_s t_ne using t_ne

  rw [Finset.mem_coe] at y_in_t
  specialize t_sset_s y_in_t
  rw [← Finset.coe_eq_empty, Set.eq_empty_iff_forall_notMem] at su_empty
  specialize su_empty y
  rw [Finset.mem_coe, Finset.mem_inter, not_and_or] at su_empty
  cases' su_empty with contra y_nin_u
  contradiction
  rw [Finset.mem_coe]
  apply y_nin_u

theorem disjoint_link_boundary
    (X : AbstractSimplicialComplex E)
    (s : Finset E)
   : Disjoint (Lk(X, s).vertices) ((∂s).vertices) := by
  rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
  intro x
  simp only [Set.mem_inter_iff, not_and, vertex_iff_in_simplex, not_exists]
  intro t_in_link u u_in_bd
  simp only [Link, Set.mem_sep_iff] at t_in_link
  choose t t_in_link x_in_t using t_in_link
  choose t_in_X st_in_X st_disj using t_in_link
  simp only [SimplexBoundary, Set.mem_union, Set.mem_diff, Finset.mem_coe, Finset.mem_powerset] at u_in_bd
  cases' u_in_bd with u_ss_s u_empty
  simp at u_empty
  choose u_ne_s u_nonempty using u_empty
  have ut_disj : u ∩ t = ∅ := by
    rw [← Finset.subset_empty]
    apply @Finset.Subset.trans _ _ (s ∩ t)
    apply Finset.inter_subset_inter_right u_ss_s
    rw [Finset.subset_empty]
    assumption
  rw [Finset.eq_empty_iff_forall_notMem] at ut_disj
  specialize ut_disj x
  rw [Finset.mem_inter, not_and] at ut_disj
  by_cases x_in_u : x ∈ u
  specialize ut_disj x_in_u
  contradiction
  assumption

theorem disjoint_link_barycenter
    (x_nin_X : x ∉ X.vertices)
  : Disjoint (Lk(X, s).vertices) ((simplex {x}).vertices) :=
by
  rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
  intro y
  simp only [Set.mem_inter_iff, not_and, vertex_iff_in_simplex, not_exists]
  intro t_in_link u u_in_barycenter
  simp only [Link, Set.mem_sep_iff] at t_in_link
  choose t t_in_link y_in_t using t_in_link
  choose t_in_X st_in_X st_disj using t_in_link
  simp only [simplex, Set.mem_diff, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at u_in_barycenter
  cases' u_in_barycenter with u_eq_x u_nonempty
  rw [Set.mem_singleton_iff] at u_nonempty
  cases' u_eq_x with u_empty u_eq_x
  contradiction
  have ut_disj : u ∩ t = ∅ :=
    by
    rw [← Finset.coe_inj, Finset.coe_empty, ← Set.subset_empty_iff, Finset.coe_inter]
    apply @Set.Subset.trans _ _ ({x} ∩ X.vertices)
    apply Set.inter_subset_inter
    simp only [u_eq_x, Finset.coe_singleton]
    rfl
    apply simplex_subset_vertices
    assumption
    rw [Set.subset_empty_iff, Set.eq_empty_iff_forall_notMem]
    intro y
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, not_and]
    intro y_eq_x
    subst y_eq_x
    assumption
  simp only [Finset.eq_empty_iff_forall_notMem, Finset.mem_inter, not_and] at ut_disj
  specialize ut_disj y
  by_cases y_in_u : y ∈ u
  specialize ut_disj y_in_u
  contradiction
  assumption
