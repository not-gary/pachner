import Pachner.Stellar.StellarEquivalence
import Pachner.Constructions.JoinProperties

variable
  {E 𝕜 : Type _}
  [DecidableEq E]
  [DecidableEq 𝕜] [Ring 𝕜] [Nontrivial 𝕜]
  {X Y Z W : AbstractSimplicialComplex E} {s t : Finset E} {x y : E}

theorem simplicialJoin_stellarSubdivision_faces_left
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
  : ((π₁[𝕜] (@disjoint_barycenter_join_boundary_link _ 𝕜 _ _ _ _ _ _ _ s_in_X x_nin_X)).coe
      ''ˢ (((π₁[𝕜] (disjoint_barycenter_boundary s_in_X x_nin_X)).coe
        ''ˢ (Simplex {x} ⋆ ∂s)) ⋆ Lk(X, s))) ⋆ Y ⊆
      (π₁[𝕜] (@disjoint_barycenter_join_boundary_link _ 𝕜 _ _ _ _ (X ⋆ Y) _ _
            (simplicialJoin_incl_left s_in_X) (simplicialJoin_notMem_vertices_left x_nin_X))).coe
        ''ˢ ((π₁[𝕜]
              (@disjoint_barycenter_boundary _ _ (X ⋆ Y) _ _ (simplicialJoin_incl_left s_in_X) (simplicialJoin_notMem_vertices_left x_nin_X))).coe
          ''ˢ (Simplex {((x, 0) : E × 𝕜)} ⋆ ∂(s ⊔ₛ ∅)) ⋆ Lk(X ⋆ Y, s ⊔ₛ ∅)) :=
by
  simp only [AbstractSimplicialComplex.instHasSubset, IsSubcomplex, Set.subset_def,
    Set.mem_union, simplicialJoin_mem, simplicialJoinProj_mem]
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
  simp only [Simplex, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at u₃_in_barycenter ⊢
  constructor; right
  cases' u₃_in_barycenter with u₃_empty u₃_eq_x
  contradiction

  rw [u₃_eq_x]
  simp only [FaceDisjointUnion, Finset.product_singleton, Finset.map_singleton,
    Function.Embedding.coeFn_mk, Finset.map_empty, Finset.union_empty]

  cases' u₃_in_barycenter with u₃_empty u₃_eq_x
  rw [Set.mem_singleton_iff] at u₃_ne
  contradiction

  rw [u₃_eq_x, faceDisjoint_empty, not_and_or]
  left; apply Finset.singleton_ne_empty

  use u₂ ⊔ₛ ∅; constructor; left
  rw [faceBoundary_mem_iff_subset, Finset.ssubset_iff_subset_ne, and_assoc] at u₂_in_bd ⊢
  choose u₂_ss_s u₂_ne_s u₂_ne using u₂_in_bd

  simp only [ne_eq, faceDisjoint_subset_unique, faceDisjoint_eq_unique, not_and]
  constructor; constructor; assumption; rfl
  constructor; intro contra; contradiction

  rw [faceDisjoint_empty, not_and_or]
  left; assumption

  constructor; rfl
  simp only [ne_eq, Finset.union_eq_empty, not_and_or, faceDisjoint_empty]
  left; left
  rw [Set.mem_singleton_iff] at u₃_ne
  assumption

  use u₁ ⊔ₛ v; constructor
  cases' v_in_Y with v_in_Y v_empty <;>
  cases' u₁_in_link with u₁_in_link u₁_empty

  simp only [Link, Set.mem_sep_iff] at u₁_in_link ⊢
  choose u₁_in_X su₁_in_X su₁_disj using u₁_in_link
  left; constructor
  exact simplicialJoin_mem_left u₁_in_X (Set.mem_union_left {∅} v_in_Y)

  constructor
  rw [faceDisjoint_distr_union, Finset.empty_union]
  exact simplicialJoin_mem_left su₁_in_X (Set.mem_union_left {∅} v_in_Y)

  rw [faceDisjoint_distr_inter, Finset.empty_inter, su₁_disj]
  simp only [FaceDisjointUnion, Finset.product_singleton, Finset.map_empty, Finset.empty_union]

  left
  subst u₁_empty
  rw [← simplicialJoin_link_left s_in_X]
  exact simplicialJoin_incl_right v_in_Y

  left
  subst v_empty
  rw [← simplicialJoin_link_left s_in_X]
  exact simplicialJoin_incl_left u₁_in_link

  right
  subst v_empty u₁_empty
  rw [Set.mem_singleton_iff, faceDisjoint_empty, and_self]

  simp only [faceDisjoint_distr_union, Finset.empty_union, ← u_decomp]
  assumption

  use ∅ ⊔ₛ ∅ ∪ (u₂ ⊔ₛ  ∅); constructor; left
  use ∅ ⊔ₛ ∅; constructor; right
  rw [Set.mem_singleton_iff, faceDisjoint_empty]
  constructor <;> rfl

  use u₂ ⊔ₛ ∅; constructor; left
  simp only [FaceBoundary, Set.mem_diff, Set.mem_insert_iff, Finset.mem_coe, Finset.mem_powerset, not_or, Set.mem_singleton_iff] at u₂_in_bd ⊢
  choose u₂_ss_s u₂_ne_s u₂_ne using u₂_in_bd
  constructor
  rw [faceDisjoint_subset_unique]
  constructor; assumption; rfl
  constructor
  rw [faceDisjoint_eq_unique, not_and_or]
  left; assumption
  rw [faceDisjoint_empty, not_and_or]
  left; assumption

  constructor; rfl
  simp only [faceDisjoint_distr_union, Finset.empty_union, ne_eq, faceDisjoint_empty, not_and_or]
  left; exact face_nonempty u₂_in_bd

  use u₁ ⊔ₛ v; constructor
  cases' u₁_in_link with u₁_in_link u₁_empty
  simp only [Link, Set.mem_sep_iff] at u₁_in_link ⊢
  choose u₁_in_X su₁_in_X su₁_disj using u₁_in_link
  left; constructor

  exact simplicialJoin_mem_left u₁_in_X v_in_Y
  constructor
  rw [faceDisjoint_distr_union, Finset.empty_union]

  exact simplicialJoin_mem_left su₁_in_X v_in_Y
  rw [faceDisjoint_distr_inter, faceDisjoint_empty]
  constructor; assumption; rfl

  subst u₁_empty
  cases' v_in_Y with v_in_Y v_empty
  left
  rw [← simplicialJoin_link_left s_in_X]
  exact simplicialJoin_incl_right v_in_Y

  right
  subst v_empty
  rw [Set.mem_singleton_iff, faceDisjoint_empty, and_self]

  simp only [faceDisjoint_distr_union, Finset.empty_union]
  rw [Set.mem_singleton_iff] at u₃_empty
  rw [u₃_empty, Finset.empty_union] at u_decomp
  rw [u_decomp] at t_eq_uv
  assumption

  use u₃ ⊔ₛ ∅; constructor; left
  use u₃ ⊔ₛ ∅; constructor; left
  simp only [Simplex, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at u₃_in_barycenter ⊢
  choose u₃_in_barycenter u₃_ne using u₃_in_barycenter
  cases' u₃_in_barycenter with u₃_empty u₃_in_barycenter
  contradiction
  constructor; right
  rw [Finset.eq_singleton_iff_unique_mem] at u₃_in_barycenter ⊢
  choose x_in_u₃ a_eq_x using u₃_in_barycenter
  constructor; rw [faceDisjoint_mem_iff_left]; assumption
  intro b b_in_u₃
  rw [faceDisjoint_mem_iff] at b_in_u₃
  cases' b_in_u₃ with b_in_u₃ contra
  choose b1_in_u₃ b2_zero using b_in_u₃
  specialize a_eq_x b.1 b1_in_u₃
  simp only [← a_eq_x, ← b2_zero]

  choose contra b2_one using contra
  contradiction

  rw [faceDisjoint_empty, not_and_or]
  left; assumption

  use ∅ ⊔ₛ ∅; constructor; right
  rw [Set.mem_singleton_iff, faceDisjoint_empty]
  constructor <;> rfl

  constructor
  simp only [faceDisjoint_distr_union, Finset.union_empty]
  rw [ne_eq, faceDisjoint_empty, not_and_or]
  left; exact face_nonempty u₃_in_barycenter

  use u₁ ⊔ₛ v; constructor
  simp only [Link, Set.mem_sep_iff, Set.mem_singleton_iff] at u₁_in_link ⊢
  cases' u₁_in_link with u₁_in_link u₁_empty <;>
  cases' v_in_Y with v_in_Y v_empty

  left
  choose u₁_in_X su₁_in_X su₁_disj using u₁_in_link
  constructor
  exact simplicialJoin_mem_left u₁_in_X (Set.mem_union_left {∅} v_in_Y)

  constructor
  rw [faceDisjoint_distr_union, Finset.empty_union]
  exact simplicialJoin_mem_left su₁_in_X (Set.mem_union_left {∅} v_in_Y)

  rw [faceDisjoint_distr_inter, Finset.empty_inter, faceDisjoint_empty]
  constructor; assumption; rfl

  left
  choose u₁_in_X su₁_in_X su₁_disj using u₁_in_link
  rw [Set.mem_singleton_iff] at v_empty
  subst v_empty
  constructor
  exact simplicialJoin_incl_left u₁_in_X
  constructor
  rw [faceDisjoint_distr_union, Finset.empty_union]
  exact simplicialJoin_incl_left su₁_in_X
  rw [faceDisjoint_distr_inter, Finset.empty_inter, faceDisjoint_empty]
  constructor; assumption; rfl

  left
  subst u₁_empty
  constructor
  exact simplicialJoin_incl_right v_in_Y
  constructor
  rw [faceDisjoint_distr_union, Finset.empty_union, Finset.union_empty]
  exact simplicialJoin_mem_left s_in_X (Set.mem_union_left {∅} v_in_Y)

  rw [faceDisjoint_distr_inter, Finset.empty_inter, Finset.inter_empty, faceDisjoint_empty]
  constructor <;> rfl

  right
  rw [Set.mem_singleton_iff] at v_empty
  subst u₁_empty v_empty
  rw [faceDisjoint_empty]
  constructor <;> rfl

  rw [faceDisjoint_distr_union, Finset.empty_union]
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
  rw [Set.mem_singleton_iff, faceDisjoint_empty]
  constructor <;> rfl

  use u ⊔ₛ v; constructor; left
  simp only [Link, Set.mem_sep_iff] at u₁_in_link ⊢
  choose u_in_X su_in_X su_disj using u₁_in_link

  constructor
  exact simplicialJoin_mem_left u_in_X (Set.mem_union_left {∅} v_in_Y)

  constructor
  simp only [faceDisjoint_distr_union, Finset.empty_union]
  exact simplicialJoin_mem_left su_in_X (Set.mem_union_left {∅} v_in_Y)

  rw [faceDisjoint_distr_inter, Finset.empty_inter, faceDisjoint_empty]
  constructor; assumption; rfl

  simp only [faceDisjoint_distr_union, Finset.empty_union]
  assumption

  rw [Set.mem_singleton_iff] at v_empty
  subst v_empty
  use ∅ ⊔ₛ ∅; constructor; right
  rw [Set.mem_singleton_iff, faceDisjoint_empty]
  constructor <;> rfl

  use u ⊔ₛ ∅; constructor; left
  simp only [Link, Set.mem_sep_iff] at u₁_in_link ⊢
  choose u_in_X su_in_X su_disj using u₁_in_link
  constructor
  exact simplicialJoin_incl_left u_in_X
  constructor
  rw [faceDisjoint_distr_union, Finset.empty_union]
  exact simplicialJoin_incl_left su_in_X
  rw [faceDisjoint_distr_inter, Finset.empty_inter, faceDisjoint_empty]
  constructor; assumption; rfl

  simp only [faceDisjoint_distr_union, Finset.empty_union]
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
  rw [Set.mem_singleton_iff, faceDisjoint_empty]
  constructor <;> rfl

  use ∅ ⊔ₛ v; constructor; left
  simp only [Link, Set.mem_sep_iff]
  constructor
  exact simplicialJoin_incl_right v_in_Y
  constructor
  rw [faceDisjoint_distr_union, Finset.union_empty, Finset.empty_union]
  exact simplicialJoin_mem_left s_in_X (Set.mem_union_left {∅} v_in_Y)
  rw [faceDisjoint_distr_inter, Finset.inter_empty, Finset.empty_inter, faceDisjoint_empty]
  constructor <;> rfl

  simp only [faceDisjoint_distr_union, Finset.empty_union]
  assumption

  rw [Set.mem_singleton_iff] at v_empty
  choose t_empty t_ne using t_eq_uv
  subst v_empty t_empty
  rw [ne_eq, faceDisjoint_empty, not_and_or] at t_ne
  cases t_ne <;> contradiction

theorem simplicialJoin_stellarSubdivision_faces_right
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
  : (π₁[𝕜] (@disjoint_barycenter_join_boundary_link _ 𝕜 _ _ _ _ (X ⋆ Y) _ _
            (simplicialJoin_incl_left s_in_X) (simplicialJoin_notMem_vertices_left x_nin_X))).coe
        ''ˢ ((π₁[𝕜] (@disjoint_barycenter_boundary _ _ (X ⋆ Y) _ _
                (simplicialJoin_incl_left s_in_X) (simplicialJoin_notMem_vertices_left x_nin_X))).coe
          ''ˢ (Simplex {((x, 0) : E × 𝕜)} ⋆ ∂(s ⊔ₛ ∅)) ⋆ Lk(X ⋆ Y, s ⊔ₛ ∅)) ⊆
      ((π₁[𝕜] (@disjoint_barycenter_join_boundary_link _ 𝕜 _ _ _ _ _ _ _ s_in_X x_nin_X)).coe
        ''ˢ (((π₁[𝕜] (disjoint_barycenter_boundary s_in_X x_nin_X)).coe
          ''ˢ (Simplex {x} ⋆ ∂s)) ⋆ Lk(X, s))) ⋆ Y :=
by
  simp only [AbstractSimplicialComplex.instHasSubset, IsSubcomplex, Set.subset_def,
    Set.mem_union, Set.mem_singleton_iff, simplicialJoin_mem, simplicialJoinProj_mem]
  intro t t_in_img
  choose t' t'_in_join t₁ t₁_in_link t_decomp using t_in_img

  have s_zero : ∀ a : E × 𝕜, a ∈ s ⊔ₛ ∅ → a.snd = 0 :=
  by
    intro a a_in_s
    rw [faceDisjoint_mem_iff] at a_in_s
    cases' a_in_s with a_in_s contra
    choose a_in_s a_zero using a_in_s
    assumption
    choose contra a_one using contra
    have H : a.1 ∉ (∅ : Finset E) := by apply Finset.notMem_empty
    contradiction

  cases' t'_in_join with t'_in_join t'_empty
  · choose t₃ t₃_in_barycenter t₂ t₂_in_bd t'_decomp t'_ne using t'_in_join
    subst t'_decomp

    simp only [Simplex, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_powerset,
      Finset.subset_singleton_iff] at t₃_in_barycenter
    simp only [faceBoundary_mem_iff_subset, Finset.ssubset_iff] at t₂_in_bd

    cases' t₃_in_barycenter with t₃_in_barycenter t₃_empty <;>
    cases' t₂_in_bd with t₂_in_bd t₂_empty <;>
    cases' t₁_in_link with t₁_in_link t₁_empty
    · choose t₃_in_barycenter t₃_ne using t₃_in_barycenter
      cases' t₃_in_barycenter with t₃_empty t₃_in_barycenter
      contradiction

      choose t₂_ss_s t₂_ne using t₂_in_bd
      choose a a_nin_t₂ at₂_ss_s using t₂_ss_s

      simp only [Link, Set.mem_sep_iff] at t₁_in_link
      choose t₁_in_XY st₁_in_XY st₁_disj using t₁_in_link
      rw [simplicialJoin_mem] at t₁_in_XY
      choose u₁ u₁_in_X u₂ u₂_in_Y t₁_eq_u₁u₂ t₁_ne using t₁_in_XY
      subst t₁_eq_u₁u₂

      rw [faceDisjoint_distr_union, Finset.empty_union, simplicialJoin_mem] at st₁_in_XY
      choose v₁ v₁_in_X v₂ v₂_in_Y su₁u₂_eq_v₁v₂ su₁u₂_ne using st₁_in_XY
      rw [faceDisjoint_eq_unique] at su₁u₂_eq_v₁v₂
      choose su₁_eq_v₁ u₂_eq_v₂ using su₁u₂_eq_v₁v₂
      subst su₁_eq_v₁ u₂_eq_v₂

      rw [faceDisjoint_distr_inter, Finset.empty_inter, faceDisjoint_empty] at st₁_disj
      choose su₁_disj taut using st₁_disj

      use Finset.image Prod.fst (t₃ ∪ t₂) ∪ u₁; constructor; left
      use Finset.image Prod.fst (t₃ ∪ t₂); constructor; left
      use Finset.image Prod.fst t₃; constructor; left

      simp only [Simplex, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_powerset,
        Finset.subset_singleton_iff]
      simp only [t₃_in_barycenter, Finset.image_singleton, Prod.fst]
      constructor; right; trivial
      apply Finset.singleton_ne_empty

      use Finset.image Prod.fst t₂; constructor; left
      rw [faceBoundary_mem_iff_subset, Finset.ssubset_iff]
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
      rw [← @Prod.mk.eta _ _ a, a_zero, faceDisjoint_mem_iff_left] at at₂_ss_s
      assumption
      rw [Finset.mem_image] at b_in_t₂
      choose c c_in_t₂ proj_c_b using b_in_t₂
      have c_in_s : c ∈ s ⊔ₛ ∅ := by
        apply Finset.mem_of_subset at₂_ss_s
        rw [Finset.mem_insert]
        right; assumption
      specialize s_zero c c_in_s
      rw [← @Prod.mk.eta _ _ c, s_zero, faceDisjoint_mem_iff_left, proj_c_b] at c_in_s
      assumption

      rw [ne_eq, Finset.image_eq_empty]
      assumption

      constructor
      rw [Finset.image_union]
      rw [ne_eq, Finset.image_eq_empty]
      assumption

      cases' u₁_in_X with u₁_in_X u₁_empty
      · use u₁; constructor; left
        simp only [Link, Set.mem_sep_iff]
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
        right; exact face_nonempty u₁_in_X
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
        simp only [Finset.ext_iff, faceDisjoint_mem_iff, Finset.mem_image]
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
        simp only [Simplex, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at t₃_in_barycenter
        rw [t₃_in_barycenter]
        simp only [FaceDisjointUnion, Finset.image_singleton, Finset.product_singleton,
          Finset.map_singleton, Function.Embedding.coeFn_mk, Finset.map_empty, Finset.union_empty]

      rw [← t₂_lift, ← t₃_lift] at t_decomp
      simp only [faceDisjoint_distr_union, ← Finset.image_union, Finset.empty_union] at t_decomp
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

      simp only [Simplex, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_powerset,
        Finset.subset_singleton_iff]
      simp only [t₃_in_barycenter, Finset.image_singleton, Prod.fst]
      constructor; right; trivial
      apply Finset.singleton_ne_empty

      use Finset.image Prod.fst t₂; constructor; left
      rw [faceBoundary_mem_iff_subset, Finset.ssubset_iff]
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
      rw [← @Prod.mk.eta _ _ a, a_zero, faceDisjoint_mem_iff_left] at at₂_ss_s
      assumption
      rw [Finset.mem_image] at b_in_t₂
      choose c c_in_t₂ proj_c_b using b_in_t₂
      have c_in_s : c ∈ s ⊔ₛ ∅ := by
        apply Finset.mem_of_subset at₂_ss_s
        rw [Finset.mem_insert]
        right; assumption
      specialize s_zero c c_in_s
      rw [← @Prod.mk.eta _ _ c, s_zero, faceDisjoint_mem_iff_left, proj_c_b] at c_in_s
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
        simp only [Finset.ext_iff, faceDisjoint_mem_iff, Finset.mem_image]
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
        simp only [Simplex, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at t₃_in_barycenter
        rw [t₃_in_barycenter]
        simp only [FaceDisjointUnion, Finset.image_singleton, Finset.product_singleton,
          Finset.map_singleton, Function.Embedding.coeFn_mk, Finset.map_empty, Finset.union_empty]

      rw [← t₂_lift, ← t₃_lift] at t_decomp
      simp only [faceDisjoint_distr_union, ← Finset.image_union, Finset.union_empty] at t_decomp
      rw [Finset.union_empty]
      assumption
    · subst t₂_empty
      choose t₃_in_barycenter t₃_ne using t₃_in_barycenter
      cases' t₃_in_barycenter with t₃_empty t₃_in_barycenter
      contradiction

      simp only [Link, Set.mem_sep_iff] at t₁_in_link
      choose t₁_in_XY st₁_in_XY st₁_disj using t₁_in_link
      rw [simplicialJoin_mem] at t₁_in_XY
      choose u₁ u₁_in_X u₂ u₂_in_Y t₁_eq_u₁u₂ t₁_ne using t₁_in_XY
      subst t₁_eq_u₁u₂

      rw [faceDisjoint_distr_union, Finset.empty_union, simplicialJoin_mem] at st₁_in_XY
      choose v₁ v₁_in_X v₂ v₂_in_Y su₁u₂_eq_v₁v₂ su₁u₂_ne using st₁_in_XY
      rw [faceDisjoint_eq_unique] at su₁u₂_eq_v₁v₂
      choose su₁_eq_v₁ u₂_eq_v₂ using su₁u₂_eq_v₁v₂
      subst su₁_eq_v₁ u₂_eq_v₂

      rw [faceDisjoint_distr_inter, Finset.empty_inter, faceDisjoint_empty] at st₁_disj
      choose su₁_disj taut using st₁_disj

      use Finset.image Prod.fst (t₃ ∪ ∅) ∪ u₁; constructor; left
      use Finset.image Prod.fst (t₃ ∪ ∅); constructor; left
      use Finset.image Prod.fst t₃; constructor; left

      simp only [Simplex, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_powerset,
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
        simp only [Link, Set.mem_sep_iff]
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
        right; exact face_nonempty u₁_in_X
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
        simp only [Simplex, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at t₃_in_barycenter
        rw [t₃_in_barycenter]
        simp only [FaceDisjointUnion, Finset.image_singleton, Finset.product_singleton,
          Finset.map_singleton, Function.Embedding.coeFn_mk, Finset.map_empty, Finset.union_empty]

      rw [← t₃_lift] at t_decomp
      simp only [Finset.union_empty, faceDisjoint_distr_union, Finset.empty_union] at t_decomp
      rw [Finset.image_union, Finset.image_empty, Finset.union_empty]
      assumption
    · subst t₁_empty t₂_empty
      choose t₃_in_barycenter t₃_ne using t₃_in_barycenter
      cases' t₃_in_barycenter with t₃_empty t₃_in_barycenter
      contradiction

      use Finset.image Prod.fst (t₃ ∪ ∅) ∪ ∅; constructor; left
      use Finset.image Prod.fst (t₃ ∪ ∅); constructor; left
      use Finset.image Prod.fst t₃; constructor; left

      simp only [Simplex, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_powerset,
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
        simp only [Simplex, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at t₃_in_barycenter
        rw [t₃_in_barycenter]
        simp only [FaceDisjointUnion, Finset.image_singleton, Finset.product_singleton,
          Finset.map_singleton, Function.Embedding.coeFn_mk, Finset.map_empty, Finset.union_empty]

      rw [← t₃_lift] at t_decomp
      simp only [Finset.union_empty] at t_decomp ⊢
      assumption
    · subst t₃_empty
      choose t₂_ss_s t₂_ne using t₂_in_bd
      choose a a_nin_t₂ at₂_ss_s using t₂_ss_s

      simp only [Link, Set.mem_sep_iff] at t₁_in_link
      choose t₁_in_XY st₁_in_XY st₁_disj using t₁_in_link
      rw [simplicialJoin_mem] at t₁_in_XY
      choose u₁ u₁_in_X u₂ u₂_in_Y t₁_eq_u₁u₂ t₁_ne using t₁_in_XY
      subst t₁_eq_u₁u₂

      rw [faceDisjoint_distr_union, Finset.empty_union, simplicialJoin_mem] at st₁_in_XY
      choose v₁ v₁_in_X v₂ v₂_in_Y su₁u₂_eq_v₁v₂ su₁u₂_ne using st₁_in_XY
      rw [faceDisjoint_eq_unique] at su₁u₂_eq_v₁v₂
      choose su₁_eq_v₁ u₂_eq_v₂ using su₁u₂_eq_v₁v₂
      subst su₁_eq_v₁ u₂_eq_v₂

      rw [faceDisjoint_distr_inter, Finset.empty_inter, faceDisjoint_empty] at st₁_disj
      choose su₁_disj taut using st₁_disj

      use Finset.image Prod.fst (∅ ∪ t₂) ∪ u₁; constructor; left
      use Finset.image Prod.fst (∅ ∪ t₂); constructor; left
      use ∅; constructor; right; rfl

      use Finset.image Prod.fst t₂; constructor; left
      rw [faceBoundary_mem_iff_subset, Finset.ssubset_iff]
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
      rw [← @Prod.mk.eta _ _ a, a_zero, faceDisjoint_mem_iff_left] at at₂_ss_s
      assumption
      rw [Finset.mem_image] at b_in_t₂
      choose c c_in_t₂ proj_c_b using b_in_t₂
      have c_in_s : c ∈ s ⊔ₛ ∅ := by
        apply Finset.mem_of_subset at₂_ss_s
        rw [Finset.mem_insert]
        right; assumption
      specialize s_zero c c_in_s
      rw [← @Prod.mk.eta _ _ c, s_zero, faceDisjoint_mem_iff_left, proj_c_b] at c_in_s
      assumption

      rw [ne_eq, Finset.image_eq_empty]
      assumption

      constructor
      rw [Finset.image_union, Finset.image_empty]
      rw [ne_eq, Finset.image_eq_empty]
      assumption

      cases' u₁_in_X with u₁_in_X u₁_empty
      · use u₁; constructor; left
        simp only [Link, Set.mem_sep_iff]
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
        right; exact face_nonempty u₁_in_X
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
        simp only [Finset.ext_iff, faceDisjoint_mem_iff, Finset.mem_image]
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
      simp only [Finset.empty_union, faceDisjoint_distr_union] at t_decomp
      rw [Finset.empty_union]
      assumption
    · subst t₁_empty t₃_empty
      choose t₂_ss_s t₂_ne using t₂_in_bd
      choose a a_nin_t₂ at₂_ss_s using t₂_ss_s

      use Finset.image Prod.fst (∅ ∪ t₂) ∪ ∅; constructor; left
      use Finset.image Prod.fst (∅ ∪ t₂); constructor; left
      use ∅; constructor; right; rfl

      use Finset.image Prod.fst t₂; constructor; left
      rw [faceBoundary_mem_iff_subset, Finset.ssubset_iff]
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
      rw [← @Prod.mk.eta _ _ a, a_zero, faceDisjoint_mem_iff_left] at at₂_ss_s
      assumption
      rw [Finset.mem_image] at b_in_t₂
      choose c c_in_t₂ proj_c_b using b_in_t₂
      have c_in_s : c ∈ s ⊔ₛ ∅ := by
        apply Finset.mem_of_subset at₂_ss_s
        rw [Finset.mem_insert]
        right; assumption
      specialize s_zero c c_in_s
      rw [← @Prod.mk.eta _ _ c, s_zero, faceDisjoint_mem_iff_left, proj_c_b] at c_in_s
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
        simp only [Finset.ext_iff, faceDisjoint_mem_iff, Finset.mem_image]
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
      simp only [Link, Set.mem_sep_iff] at t₁_in_link
      choose t₁_in_XY st₁_in_XY st₁_disj using t₁_in_link
      rw [simplicialJoin_mem] at t₁_in_XY
      choose u₁ u₁_in_X u₂ u₂_in_Y t₁_eq_u₁u₂ t₁_ne using t₁_in_XY
      subst t₁_eq_u₁u₂

      rw [faceDisjoint_distr_union, Finset.empty_union, simplicialJoin_mem] at st₁_in_XY
      choose v₁ v₁_in_X v₂ v₂_in_Y su₁u₂_eq_v₁v₂ su₁u₂_ne using st₁_in_XY
      rw [faceDisjoint_eq_unique] at su₁u₂_eq_v₁v₂
      choose su₁_eq_v₁ u₂_eq_v₂ using su₁u₂_eq_v₁v₂
      subst su₁_eq_v₁ u₂_eq_v₂

      rw [faceDisjoint_distr_inter, Finset.empty_inter, faceDisjoint_empty] at st₁_disj
      choose su₁_disj taut using st₁_disj

      use Finset.image Prod.fst (∅ ∪ ∅ : Finset (E × 𝕜)) ∪ u₁; constructor; left
      use Finset.image Prod.fst (∅ ∪ ∅ : Finset (E × 𝕜)); constructor; right
      rw [Finset.image_eq_empty, Finset.empty_union]

      cases' u₁_in_X with u₁_in_X u₁_empty
      · use u₁; constructor; left
        simp only [Link, Set.mem_sep_iff]
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
        right; exact face_nonempty u₁_in_X
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
    · simp only [Link, Set.mem_sep_iff] at t₁_in_link
      choose t₁_in_XY st₁_in_XY st₁_disj using t₁_in_link
      simp only [simplicialJoin_mem, Set.mem_union, Set.mem_singleton_iff] at t₁_in_XY
      choose u₁ u₁_in_X u₂ u₂_in_Y t₁_eq_u₁u₂ t₁_ne using t₁_in_XY
      subst t₁_eq_u₁u₂
      cases' u₁_in_X with u₁_in_X u₁_empty <;>
      cases' u₂_in_Y with u₂_in_Y u₂_empty
      · use u₁; constructor; left
        use ∅; constructor; right; rfl
        use u₁; constructor; left
        simp only [Link, Set.mem_sep_iff]
        constructor; assumption
        constructor

        rw [faceDisjoint_distr_union, simplicialJoin_mem] at st₁_in_XY
        choose v₁ v₁_in_X v₂ v₂_in_Y su₁u₂_eq_v₁v₂ su₁u₂_ne using st₁_in_XY
        rw [faceDisjoint_eq_unique] at su₁u₂_eq_v₁v₂
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
        rw [faceDisjoint_distr_inter, faceDisjoint_empty] at st₁_disj
        choose su₁_disj u₂_empty using st₁_disj
        assumption
        constructor
        rw [Finset.empty_union]
        exact face_nonempty u₁_in_X

        use u₂; constructor; left; assumption
        rw [Finset.empty_union] at t_decomp
        assumption
      · subst u₂_empty
        use u₁; constructor; left
        use ∅; constructor; right; rfl
        use u₁; constructor; left
        simp only [Link, Set.mem_sep_iff]
        constructor; assumption
        constructor

        rw [faceDisjoint_distr_union, simplicialJoin_mem] at st₁_in_XY
        choose v₁ v₁_in_X v₂ v₂_in_Y su₁u₂_eq_v₁v₂ su₁u₂_ne using st₁_in_XY
        rw [faceDisjoint_eq_unique] at su₁u₂_eq_v₁v₂
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
        rw [faceDisjoint_distr_inter, faceDisjoint_empty] at st₁_disj
        choose su₁_disj u₂_empty using st₁_disj
        assumption
        constructor
        rw [Finset.empty_union]
        exact face_nonempty u₁_in_X

        use ∅; constructor; right; rfl
        rw [Finset.empty_union] at t_decomp
        assumption
      · subst u₁_empty
        use ∅; constructor; right; rfl
        use u₂; constructor; left; assumption
        rw [Finset.empty_union] at t_decomp
        assumption
      · subst u₁_empty u₂_empty
        rw [ne_eq, faceDisjoint_empty, not_and_or] at t₁_ne
        cases t₁_ne <;> contradiction
    · subst t₁_empty
      choose t_empty t_ne using t_decomp
      rw [Finset.empty_union] at t_empty
      contradiction

theorem simplicialJoin_stellarSubdivision_faces
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
  : ((π₁[𝕜] (@disjoint_barycenter_join_boundary_link _ 𝕜 _ _ _ _ _ _ _ s_in_X x_nin_X)).coe
      ''ˢ (((π₁[𝕜] (disjoint_barycenter_boundary s_in_X x_nin_X)).coe
        ''ˢ (Simplex {x} ⋆ ∂s)) ⋆ Lk(X, s))) ⋆ Y =
      (π₁[𝕜] (@disjoint_barycenter_join_boundary_link _ 𝕜 _ _ _ _ (X ⋆ Y) _ _
            (simplicialJoin_incl_left s_in_X) (simplicialJoin_notMem_vertices_left x_nin_X))).coe
        ''ˢ ((π₁[𝕜] (@disjoint_barycenter_boundary _ _ (X ⋆ Y) _ _
                (simplicialJoin_incl_left s_in_X) (simplicialJoin_notMem_vertices_left x_nin_X))).coe
          ''ˢ ((Simplex {((x, 0) : E × 𝕜)} ⋆ ∂(s ⊔ₛ ∅))) ⋆ Lk(X ⋆ Y, s ⊔ₛ ∅)) :=
by
  rw [AbstractSimplicialComplex.ext_iff, Set.Subset.antisymm_iff]
  exact ⟨simplicialJoin_stellarSubdivision_faces_left s_in_X x_nin_X, simplicialJoin_stellarSubdivision_faces_right s_in_X x_nin_X⟩

theorem simplicialJoin_stellarSubdivision_left
    {s_in_X : s ∈ X.faces}
    {x_nin_X : x ∉ X.vertices}
  : (σ(X, s, x; 𝕜, s_in_X, x_nin_X) ⋆ Y : AbstractSimplicialComplex (E × 𝕜)) =
    (σ(X ⋆ Y, s ⊔ₛ ∅, (x, 0); 𝕜, simplicialJoin_incl_left s_in_X, simplicialJoin_notMem_vertices_left x_nin_X)) :=
by
  simp only [StellarSubdivision, AbstractSimplicialComplex.ext_iff,
    simplicialJoin_simplicialUnion_right, simplicialJoin_starComplement_left s_in_X,
    StellarSubdivision, simplicialJoin_stellarSubdivision_faces s_in_X x_nin_X]

-- TODO: could be = instead of ≅ but requires some work
theorem simplicialJoin_stellarSubdivision_right
    {t_in_Y : t ∈ Y.faces}
    {y_nin_Y : y ∉ Y.vertices}
  : (X ⋆ σ(Y, t, y; 𝕜, t_in_Y, y_nin_Y) : AbstractSimplicialComplex (E × 𝕜)) ≅
      (σ(X ⋆ Y, ∅ ⊔ₛ t, (y, 1); 𝕜,
        simplicialJoin_incl_right t_in_Y,
        simplicialJoin_notMem_vertices_right y_nin_Y) : AbstractSimplicialComplex (E × 𝕜)) :=
by
  apply
    @simplicialIso_trans (E × 𝕜) (E × 𝕜) _ _ _ _ (X ⋆ σ(Y, t, y; 𝕜, t_in_Y, y_nin_Y)) _
      (σ(Y, t, y; 𝕜, t_in_Y, y_nin_Y) ⋆ X)
  apply simplicialJoin_comm
  apply
    simplicialIso_trans (σ(Y ⋆ X, t ⊔ₛ ∅, (y, 0); 𝕜, simplicialJoin_incl_left t_in_Y,
        simplicialJoin_notMem_vertices_left y_nin_Y) : AbstractSimplicialComplex (E × 𝕜))
  rw [simplicialJoin_stellarSubdivision_left]
  let f : SimplicialMap (Y ⋆ X) (X ⋆ Y) :=
    @SimplicialMap.mk (E × 𝕜) (E × 𝕜) _ _ _ SimplicialJoinCommMap simplicialJoin_comm_simplicial
  let g : SimplicialMap (X ⋆ Y) (Y ⋆ X) :=
    @SimplicialMap.mk (E × 𝕜) (E × 𝕜) _ _ _ SimplicialJoinCommMap simplicialJoin_comm_simplicial
  have gf_inv : IsInverseSimplicialIso f g :=
  by
    unfold IsInverseSimplicialIso
    constructor <;>
      · simp only [Set.restrict_eq_restrict_iff, Set.EqOn]
        intro x x_in_XY
        rw [simplicialJoin_mem_vertices] at x_in_XY
        simp only [f, g, SimplicialMap.comp, SimplicialJoinCommMap, id, Function.comp_apply]
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
  apply stellarSubdivision_simplicialIso
  apply f_iso
  apply gf_inv
  simp only [Finset.ext_iff, Finset.mem_image, faceDisjoint_mem_iff]
  intro a
  constructor
  · intro a_in_img
    choose b b_in_disj fb_a using a_in_img
    cases' b_in_disj with b_in_t contra
    choose b_in_t b_zero using b_in_t
    simp only [f, SimplicialJoinCommMap, b_zero, ↓reduceIte, f, g, Prod.ext_iff] at fb_a
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
    simp only [f, SimplicialJoinCommMap, eq_self_iff_true, if_true, ← a_one, Prod.ext_iff]
  simp only [f, SimplicialJoinCommMap, eq_self_iff_true, if_true]
  simp only [g, SimplicialJoinCommMap, Nat.one_ne_zero, if_false]
  simp only [one_ne_zero, ↓reduceIte, f, g]

lemma simplicialJoin_stellarSubdivision_iso
    (H : ∃ (t : Finset E) (t_in_Y : t ∈ Y)
      (y : E) (y_nin_Y : y ∉ Y.vertices),
      (X ≅ σ(Y, t, y; 𝕜, t_in_Y, y_nin_Y)))
  : ∃ (t' : Finset (E × 𝕜)) (t'_in_YZ : t' ∈ Y ⋆ Z)
      (y' : E × 𝕜) (y'_nin_YZ : y' ∉ ((Y ⋆ Z) : AbstractSimplicialComplex (E × 𝕜)).vertices),
    ((X ⋆ Z) : AbstractSimplicialComplex (E × 𝕜)) ≅
      σ(Y ⋆ Z, t', y'; 𝕜, t'_in_YZ, y'_nin_YZ) :=
by
  choose t t_in_Y y y_nin_Y X_iso_Ysubdiv using H
  use t ⊔ₛ ∅, simplicialJoin_incl_left t_in_Y, (y, 0),
    simplicialJoin_notMem_vertices_left y_nin_Y
  calc (X ⋆ Z: AbstractSimplicialComplex (E × 𝕜))
      _ ≅ σ(Y, t, y; 𝕜, t_in_Y, y_nin_Y) ⋆ Z := simplicialJoin_simplicialIso_left X_iso_Ysubdiv
      _ = σ(Y ⋆ Z, t ⊔ₛ ∅, (y, 0); 𝕜, simplicialJoin_incl_left t_in_Y, simplicialJoin_notMem_vertices_left y_nin_Y) :=
          simplicialJoin_stellarSubdivision_left

theorem simplicialJoin_stellarMove
  : (X ≅ₛₜₘ[𝕜] Y) → ((X ⋆ Z) ≅ₛₜₘ[𝕜] ((Y ⋆ Z) : AbstractSimplicialComplex (E × 𝕜))) :=
by
  intro X_move_Y
  cases' X_move_Y with X_move_Ysubdiv h
  · left
    exact simplicialJoin_stellarSubdivision_iso X_move_Ysubdiv
  cases' h with Ksubdiv_move_L K_iso_L
  · right; left
    exact simplicialJoin_stellarSubdivision_iso Ksubdiv_move_L
  · right; right
    exact simplicialJoin_simplicialIso_left K_iso_L

theorem simplicialJoin_stellarEquiv_left
  : X ≅ₛₜ[𝕜] Y → (X ⋆ Z) ≅ₛₜ[𝕜] (Y ⋆ Z : AbstractSimplicialComplex (E × 𝕜)) :=
by
  intro X_eq_Y
  induction' X_eq_Y with K L X_eq_K K_move_L XZ_eq_KZ
  · rfl
  · calc (X ⋆ Z : AbstractSimplicialComplex (E × 𝕜))
      _ ≅ₛₜ[𝕜]  K ⋆ Z := XZ_eq_KZ
      _ ≅ₛₜₘ[𝕜] L ⋆ Z := simplicialJoin_stellarMove K_move_L

theorem simplicialJoin_stellarEquiv_right
  : X ≅ₛₜ[𝕜] Y → (Z ⋆ X) ≅ₛₜ[𝕜] (Z ⋆ Y : AbstractSimplicialComplex (E × 𝕜)) :=
by
  intro X_eq_Y
  calc (Z ⋆ X : AbstractSimplicialComplex (E × 𝕜))
    _ ≅     X ⋆ Z := simplicialJoin_comm
    _ ≅ₛₜ[𝕜] Y ⋆ Z := simplicialJoin_stellarEquiv_left X_eq_Y
    _ ≅     Z ⋆ Y := simplicialJoin_comm

-- Lemma 3.1, p.10
theorem simplicialJoin_stellarEquiv
  : X ≅ₛₜ[𝕜] Y → Z ≅ₛₜ[𝕜] W → (X ⋆ Z) ≅ₛₜ[𝕜] (Y ⋆ W : AbstractSimplicialComplex (E × 𝕜)) :=
by
  intro X_eq_Y Z_eq_W
  calc (X ⋆ Z : AbstractSimplicialComplex (E × 𝕜))
    _ ≅ₛₜ[𝕜] Y ⋆ Z := simplicialJoin_stellarEquiv_left X_eq_Y
    _ ≅ₛₜ[𝕜] Y ⋆ W := simplicialJoin_stellarEquiv_right Z_eq_W
