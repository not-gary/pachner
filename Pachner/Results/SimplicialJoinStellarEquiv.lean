/-
Copyright (c) 2025 Garett Cunningham, Daniel Zach, Stefan Friedl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Garett Cunningham, Daniel Zach, Stefan Friedl
-/

import Pachner.Stellar.StellarEquivalence
import Pachner.Constructions.JoinProperties

variable
  {E 𝕜 : Type _}
  [DecidableEq E]
  [DecidableEq 𝕜] [Ring 𝕜] [Nontrivial 𝕜]
  {X Y Z W : AbstractSimplicialComplex E} {s t : Finset E} {x y : E}

theorem simplicialJoin_stellarSubdivision_faces_left (s_in_X : s ∈ X.faces) (x_nin_X : x ∉ X.vertices) :
  ((π₁[𝕜] (@disjoint_barycenter_join_boundary_link _ 𝕜 _ _ _ _ _ _ _ s_in_X x_nin_X)).coe
    ''ˢ (((π₁[𝕜] (disjoint_barycenter_boundary s_in_X x_nin_X)).coe
      ''ˢ (Simplex {x} ⋆ ∂s)) ⋆ Lk(X, s))) ⋆ Y ⊆
  (π₁[𝕜] (@disjoint_barycenter_join_boundary_link _ 𝕜 _ _ _ _ (X ⋆ Y) _ _
      (simplicialJoin_incl_left s_in_X) (simplicialJoin_notMem_vertices_left x_nin_X))).coe
    ''ˢ ((π₁[𝕜] (@disjoint_barycenter_boundary _ _ (X ⋆ Y) _ _
        (simplicialJoin_incl_left s_in_X) (simplicialJoin_notMem_vertices_left x_nin_X))).coe
      ''ˢ ((Simplex {((x, 0) : E × 𝕜)} ⋆ ∂(s ⊔ₛ ∅))) ⋆ Lk(X ⋆ Y, s ⊔ₛ ∅)) :=
by
  simp only [AbstractSimplicialComplex.instHasSubset, IsSubcomplex, Set.subset_def,
    Set.mem_union, simplicialJoin_mem, simplicialJoinProj_mem]
  intro t t_in_join
  have not_or_self {h : Prop} : ¬h ∨ h := by
    by_cases h' : h
    · exact Or.inr h'
    · exact Or.inl h'
  rcases t_in_join with ⟨u, ⟨u', ⟨u₃, u₃_in_barycenter, u₂, u₂_in_bd, u'_decomp, u'_ne⟩ | u'_empty,
      u₁, u₁_in_link, u_decomp, u_ne⟩ | u_empty, v, v_in_Y, t_eq_uv⟩
  · subst u_decomp u'_decomp
    refine ⟨u₃ ⊔ₛ ∅ ∪ (u₂ ⊔ₛ ∅), ⟨Or.inl ⟨u₃ ⊔ₛ ∅, ?_⟩, ⟨u₁ ⊔ₛ v, ⟨?_, ?_⟩⟩⟩⟩
    · simp only [Simplex, Set.mem_diff, Finset.mem_coe, Finset.mem_powerset, and_or_right] at u₃_in_barycenter ⊢
      have u₃_in_barycenter : u₃ ⊆ {x} := by
        rcases u₃_in_barycenter.left with u₃_in_barycenter | u₃_empty
        · exact u₃_in_barycenter
        · subst u₃_empty
          exact Finset.empty_subset {x}
      refine ⟨⟨Or.inl ?_, ?_⟩, ⟨u₂ ⊔ₛ ∅, ?_⟩⟩
      · rw [Finset.subset_singleton_iff] at u₃_in_barycenter ⊢
        rw [faceDisjoint_empty, eq_self, and_true]
        rcases u₃_in_barycenter with u₃_empty | u₃_eq_x <;> subst u₃
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rw [Set.mem_singleton_iff, faceDisjoint_empty, eq_self, and_true]
        exact not_or_self
      · simp only [eq_self, true_and, faceDisjoint_distr_union, Finset.union_empty, ne_eq, faceDisjoint_empty, eq_self,
          and_true, u'_ne, not_false_eq_true, Set.mem_singleton_iff]
        simp only [faceBoundary_mem_iff_subset, Finset.ssubset_iff_subset_ne, ne_eq] at u₂_in_bd ⊢
        simp only [faceDisjoint_subset_unique, Finset.subset_empty, faceDisjoint_eq_unique, and_true, faceDisjoint_empty]
        exact u₂_in_bd
    · rw [← simplicialJoin_link_left s_in_X, simplicialJoin_sep, and_or_right, and_or_right]
      refine ⟨Or.inl u₁_in_link, ⟨Or.inl v_in_Y, ?_⟩⟩
      rw [ne_eq, ne_eq, ← not_and_or, Set.mem_singleton_iff, faceDisjoint_empty]
      exact not_or_self
    · rw [faceDisjoint_distr_union, faceDisjoint_distr_union, Finset.empty_union, Finset.empty_union]
      exact t_eq_uv
  · subst u_decomp u'_empty
    refine ⟨∅ ⊔ₛ ∅, ⟨Or.inr rfl, ⟨u₁ ⊔ₛ v, ⟨?_, ?_⟩⟩⟩⟩
    · rw [← simplicialJoin_link_left s_in_X, simplicialJoin_sep, and_or_right, and_or_right]
      refine ⟨Or.inl u₁_in_link, ⟨Or.inl v_in_Y, ?_⟩⟩
      rw [ne_eq, ne_eq, ← not_and_or, Set.mem_singleton_iff, faceDisjoint_empty]
      exact not_or_self
    · rw [faceDisjoint_distr_union, Finset.empty_union v]
      exact t_eq_uv
  · subst u_empty
    refine ⟨∅ ⊔ₛ ∅, ⟨Or.inr rfl, ⟨∅ ⊔ₛ v, ⟨?_, ?_⟩⟩⟩⟩
    · rw [← simplicialJoin_link_left s_in_X, simplicialJoin_sep, and_or_right, and_or_right]
      refine ⟨Or.inl ?_, ⟨Or.inl v_in_Y, ?_⟩⟩
      · apply Set.mem_union_right
        exact Set.mem_singleton _
      · rw [ne_eq, ne_eq, ← not_and_or, Set.mem_singleton_iff, faceDisjoint_empty, eq_self, true_and]
        exact not_or_self
    · rw [faceDisjoint_distr_union, Finset.empty_union, Finset.empty_union]
      exact t_eq_uv

theorem simplicialJoin_stellarSubdivision_faces_right (s_in_X : s ∈ X.faces) (x_nin_X : x ∉ X.vertices) :
  (π₁[𝕜] (@disjoint_barycenter_join_boundary_link _ 𝕜 _ _ _ _ (X ⋆ Y) _ _
      (simplicialJoin_incl_left s_in_X) (simplicialJoin_notMem_vertices_left x_nin_X))).coe
    ''ˢ ((π₁[𝕜] (@disjoint_barycenter_boundary _ _ (X ⋆ Y) _ _
        (simplicialJoin_incl_left s_in_X) (simplicialJoin_notMem_vertices_left x_nin_X))).coe
      ''ˢ ((Simplex {((x, 0) : E × 𝕜)} ⋆ ∂(s ⊔ₛ ∅))) ⋆ Lk(X ⋆ Y, s ⊔ₛ ∅)) ⊆
  ((π₁[𝕜] (@disjoint_barycenter_join_boundary_link _ 𝕜 _ _ _ _ _ _ _ s_in_X x_nin_X)).coe
    ''ˢ (((π₁[𝕜] (disjoint_barycenter_boundary s_in_X x_nin_X)).coe
      ''ˢ (Simplex {x} ⋆ ∂s)) ⋆ Lk(X, s))) ⋆ Y :=
by
  simp only [AbstractSimplicialComplex.instHasSubset, IsSubcomplex, Set.subset_def, Set.mem_union, simplicialJoin_mem, simplicialJoinProj_mem]
  intro t t_in_img
  rcases t_in_img with ⟨t', t'_in_join, t₁, t₁_in_link, t_decomp⟩
  simp only [Link, Set.mem_sep_iff, simplicialJoin_mem, Set.mem_union, Set.mem_singleton_iff] at t₁_in_link ⊢
  rcases t'_in_join with ⟨t₃, t₃_in_barycenter, t₂, t₂_in_bd, t'_decomp, t'_ne⟩ | t'_empty
  · subst t'_decomp
    simp only [Simplex, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_powerset,
      Finset.subset_singleton_iff] at t₃_in_barycenter ⊢
    simp only [faceBoundary_mem_iff_subset, Finset.ssubset_iff] at t₂_in_bd ⊢

    have s_zero : ∀ a : E × 𝕜, a ∈ s ⊔ₛ ∅ → a.snd = 0 := by
      intro a a_in_s
      rw [faceDisjoint_mem_iff] at a_in_s
      rcases a_in_s with ⟨_, a_zero⟩ | ⟨contra, _⟩
      · exact a_zero
      · contradiction

    have duplicate_section (u₁ : Finset E) :
      (∃ t,
        ((t = ∅ ∨ t = {x}) ∧ ¬t = ∅ ∨ t = ∅) ∧
          ∃ u,
            ((∃ a ∉ u, insert a u ⊆ s) ∧ u ≠ ∅ ∨ u = ∅) ∧
              Finset.image Prod.fst (t₃ ∪ t₂) = t ∪ u ∧ Finset.image Prod.fst (t₃ ∪ t₂) ≠ ∅) ∨
      Finset.image Prod.fst (t₃ ∪ t₂) = ∅ := by
      · refine Or.inl ⟨Finset.image Prod.fst t₃, ⟨?_, ⟨Finset.image Prod.fst t₂, ⟨?_, ⟨Finset.image_union _ _, ?_⟩⟩⟩⟩⟩
        · rw [and_or_right, or_comm, ← or_assoc, or_self] at t₃_in_barycenter ⊢
          constructor
          · rcases t₃_in_barycenter.left with t₃_empty | t₃_in_barycenter <;> subst t₃
            · exact Or.inl rfl
            · exact Or.inr rfl
          · by_cases h : Finset.image Prod.fst t₃ = ∅
            · exact Or.inr h
            · exact Or.inl h
        · rcases t₂_in_bd with ⟨⟨a, a_nin_t₂, at₂_ss_s⟩, t₂_ne⟩ | t₂_empty
          · have a_zero : a.snd = 0 := s_zero a (Finset.mem_of_subset at₂_ss_s (Finset.mem_insert_self _ _))
            refine Or.inl ⟨⟨Prod.fst a, ⟨?_, ?_⟩⟩, ?_⟩
            · simp only [Finset.mem_image, exists_prop, Prod.exists, exists_and_right, exists_eq_right, not_exists]
              intro n
              by_cases n_zero : n = 0
              · rw [n_zero, ← a_zero, Prod.mk.eta]
                exact a_nin_t₂
              · have a_nin_s : (a.fst, n) ∉ s ⊔ₛ ∅ := by
                  revert n_zero
                  contrapose
                  simp only [Classical.not_not]
                  exact s_zero (a.fst, n)
                revert a_nin_s
                contrapose
                simp only [Classical.not_not]
                exact Finset.mem_of_subset (Finset.Subset.trans (Finset.subset_insert _ _) at₂_ss_s)
            · rw [Finset.subset_iff] at at₂_ss_s ⊢
              intro b b_in_at₂
              rw [Finset.mem_insert] at b_in_at₂
              rcases b_in_at₂ with b_eq_a | b_in_t₂
              · subst b_eq_a
                specialize at₂_ss_s (Finset.mem_insert_self a t₂)
                rw [← @Prod.mk.eta _ _ a, a_zero, faceDisjoint_mem_iff_left] at at₂_ss_s
                exact at₂_ss_s
              · rw [Finset.mem_image] at b_in_t₂
                rcases b_in_t₂ with ⟨c, c_in_t₂, proj_c_b⟩
                have c_in_s : c ∈ s ⊔ₛ ∅ := by
                  apply Finset.mem_of_subset at₂_ss_s
                  rw [Finset.mem_insert]
                  right
                  exact c_in_t₂
                specialize s_zero c c_in_s
                rw [← @Prod.mk.eta _ _ c, s_zero, faceDisjoint_mem_iff_left, proj_c_b] at c_in_s
                exact c_in_s
            · rw [ne_eq, Finset.image_eq_empty]
              exact t₂_ne
          · subst t₂_empty
            exact Or.inr rfl
        · simp only [ne_eq, Finset.image_eq_empty, t'_ne, not_false_eq_true]

    have t₂_lift : Finset.image Prod.fst t₂ ⊔ₛ ∅ = t₂ := by
      simp only [Finset.ext_iff, faceDisjoint_mem_iff, Finset.mem_image]
      intro b
      constructor
      · intro b_in_img
        rcases b_in_img with ⟨⟨c, c_in_t₂, proj_c_b⟩, b_zero⟩ | ⟨contra, _⟩
        · have c_in_s : c ∈ s ⊔ₛ ∅ := by
            rcases t₂_in_bd with ⟨⟨a, a_nin_t₂, at₂_ss_s⟩, t₂_ne⟩ | t₂_empty
            · apply Finset.mem_of_subset at₂_ss_s
              rw [Finset.mem_insert]
              exact Or.inr c_in_t₂
            · subst t₂_empty
              simp only [Finset.notMem_empty] at c_in_t₂
          specialize s_zero c c_in_s
          have b_eq_c : b = c := by simp only [Prod.ext_iff, b_zero, s_zero, proj_c_b, eq_self, and_true]
          rw [b_eq_c]
          exact c_in_t₂
        · simp only [Finset.notMem_empty] at contra
      · intro b_in_t₂
        have b_in_s : b ∈ s ⊔ₛ ∅ := by
          rcases t₂_in_bd with ⟨⟨a, a_nin_t₂, at₂_ss_s⟩, t₂_ne⟩ | t₂_empty
          · apply Finset.mem_of_subset at₂_ss_s
            rw [Finset.mem_insert]
            exact Or.inr b_in_t₂
          · subst t₂_empty
            simp only [Finset.notMem_empty] at b_in_t₂
        exact Or.inl (And.intro ⟨b, b_in_t₂, rfl⟩ (s_zero b b_in_s))

    have t₃_lift : Finset.image Prod.fst t₃ ⊔ₛ ∅ = t₃ := by
      rcases t₃_in_barycenter with ⟨t₃_empty | t₃_in_barycenter, t₃_ne⟩ | t₃_empty
      · contradiction
      · simp only [t₃_in_barycenter, FaceDisjointUnion, Finset.image_singleton, Finset.product_singleton,
          Finset.map_singleton, Function.Embedding.coeFn_mk, Finset.map_empty, Finset.union_empty]
      · subst t₃_empty
        rfl

    rw [← t₂_lift, ← t₃_lift] at t_decomp
    rw [faceDisjoint_distr_union, ← Finset.image_union, Finset.empty_union] at t_decomp
    rcases t₁_in_link with ⟨⟨u₁, u₁_in_X, u₂, u₂_in_Y, t₁_eq_u₁u₂, t₁_ne⟩, st₁_in_XY, st₁_disj⟩ | t₁_empty
    · subst t₁_eq_u₁u₂
      rw [faceDisjoint_distr_union, Finset.empty_union] at st₁_in_XY
      rcases st₁_in_XY with ⟨v₁, v₁_in_X, v₂, v₂_in_Y, su₁u₂_eq_v₁v₂, su₁u₂_ne⟩
      rw [faceDisjoint_eq_unique] at su₁u₂_eq_v₁v₂
      rcases su₁u₂_eq_v₁v₂ with ⟨su₁_eq_v₁, u₂_eq_v₂⟩
      subst su₁_eq_v₁ u₂_eq_v₂
      rw [faceDisjoint_distr_inter, Finset.empty_inter, faceDisjoint_empty] at st₁_disj
      refine ⟨Finset.image Prod.fst (t₃ ∪ t₂) ∪ u₁, ⟨
        Or.inl ⟨Finset.image Prod.fst (t₃ ∪ t₂), ⟨duplicate_section u₁, ⟨u₁, ⟨?_, ⟨rfl, ?_⟩⟩⟩⟩⟩,
        ⟨u₂, ⟨u₂_in_Y, ?_⟩⟩⟩⟩
      · rcases u₁_in_X with u₁_in_X | u₁_empty
        · refine Or.inl ⟨u₁_in_X, ⟨?_, st₁_disj.left⟩⟩
          rcases v₁_in_X with su₁_in_X | su₁_empty
          · exact su₁_in_X
          · have s_empty : s = ∅ := by
              rw [← Finset.subset_empty] at su₁_empty ⊢
              calc s
                _ ⊆ s ∪ u₁ := Finset.subset_union_left
                _ ⊆ ∅ := su₁_empty
            subst s_empty
            rw [Finset.empty_union]
            exact u₁_in_X
        · exact Or.inr u₁_empty
      · rw [ne_eq, Finset.union_eq_empty, not_and_or, Finset.image_eq_empty, ← ne_eq]
        exact Or.inl t'_ne
      · rw [faceDisjoint_distr_union, Finset.empty_union] at t_decomp
        exact t_decomp
    · refine ⟨Finset.image Prod.fst (t₃ ∪ t₂) ∪ ∅, ⟨
        Or.inl ⟨Finset.image Prod.fst (t₃ ∪ t₂), ⟨duplicate_section ∅, ⟨∅, ⟨Or.inr rfl, ⟨rfl, ?_⟩⟩⟩⟩⟩,
        ⟨∅, ⟨Or.inr rfl, ?_⟩⟩⟩⟩
      · rw [ne_eq, Finset.union_eq_empty, not_and_or, Finset.image_eq_empty, ← ne_eq]
        exact Or.inl t'_ne
      · subst t₁_empty
        rw [Finset.union_empty] at t_decomp ⊢
        exact t_decomp
  · subst t'_empty
    rcases t₁_in_link with ⟨⟨u₁, u₁_in_X, u₂, u₂_in_Y, t₁_eq_u₁u₂, t₁_ne⟩, st₁_in_XY, st₁_disj⟩ | t₁_empty
    · subst t₁_eq_u₁u₂
      rw [faceDisjoint_distr_union, Finset.empty_union] at st₁_in_XY
      rcases st₁_in_XY with ⟨v₁, v₁_in_X, v₂, v₂_in_Y, su₁u₂_eq_v₁v₂, su₁u₂_ne⟩
      rw [faceDisjoint_eq_unique] at su₁u₂_eq_v₁v₂
      rcases su₁u₂_eq_v₁v₂ with ⟨su₁_eq_v₁, u₂_eq_v₂⟩
      subst su₁_eq_v₁ u₂_eq_v₂
      rw [faceDisjoint_distr_inter, Finset.empty_inter, faceDisjoint_empty] at st₁_disj
      refine ⟨u₁, ⟨?_, ⟨u₂, ⟨u₂_in_Y, ?_⟩⟩⟩⟩
      · rcases u₁_in_X with u₁_in_X | u₁_empty
        · refine Or.inl ⟨∅, ⟨Or.inr rfl, ⟨u₁, ⟨
            Or.inl ⟨u₁_in_X, ⟨?_, st₁_disj.left⟩⟩,
            ⟨(Finset.empty_union u₁).symm, face_nonempty u₁_in_X⟩⟩⟩⟩⟩
          rcases v₁_in_X with su₁_in_X | su₁_empty
          · exact su₁_in_X
          · have s_empty : s = ∅ := by
              rw [← Finset.subset_empty] at su₁_empty ⊢
              calc s
                _ ⊆ s ∪ u₁ := Finset.subset_union_left
                _ ⊆ ∅ := su₁_empty
            subst s_empty
            rw [Finset.empty_union]
            exact u₁_in_X
        · exact Or.inr u₁_empty
      · rw [Finset.empty_union] at t_decomp
        exact t_decomp
    · simp only [t₁_empty, Finset.empty_union, ne_eq, and_not_self] at t_decomp

theorem simplicialJoin_stellarSubdivision_faces (s_in_X : s ∈ X.faces) (x_nin_X : x ∉ X.vertices) :
  ((π₁[𝕜] (@disjoint_barycenter_join_boundary_link _ 𝕜 _ _ _ _ _ _ _ s_in_X x_nin_X)).coe
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

theorem simplicialJoin_stellarSubdivision_left {s_in_X : s ∈ X.faces} {x_nin_X : x ∉ X.vertices} :
  (σ(X, s, x; 𝕜, s_in_X, x_nin_X) ⋆ Y : AbstractSimplicialComplex (E × 𝕜)) =
    (σ(X ⋆ Y, s ⊔ₛ ∅, (x, 0); 𝕜, simplicialJoin_incl_left s_in_X, simplicialJoin_notMem_vertices_left x_nin_X)) :=
by
  simp only [StellarSubdivision, AbstractSimplicialComplex.ext_iff,
    simplicialJoin_simplicialUnion_right, simplicialJoin_starComplement_left s_in_X,
    StellarSubdivision, simplicialJoin_stellarSubdivision_faces s_in_X x_nin_X]

-- TODO: could be = instead of ≅ but requires some work
theorem simplicialJoin_stellarSubdivision_right {t_in_Y : t ∈ Y.faces} {y_nin_Y : y ∉ Y.vertices} :
  (X ⋆ σ(Y, t, y; 𝕜, t_in_Y, y_nin_Y) : AbstractSimplicialComplex (E × 𝕜)) ≅
    (σ(X ⋆ Y, ∅ ⊔ₛ t, (y, 1); 𝕜, simplicialJoin_incl_right t_in_Y,
        simplicialJoin_notMem_vertices_right y_nin_Y) : AbstractSimplicialComplex (E × 𝕜)) :=
by
  calc (X ⋆ StellarSubdivision Y t y t_in_Y y_nin_Y : AbstractSimplicialComplex (E × 𝕜))
    _ ≅ (σ(Y, t, y; 𝕜, t_in_Y, y_nin_Y) ⋆ X) := simplicialJoin_comm
    _ = σ(Y ⋆ X, t ⊔ₛ ∅, (y, 0); 𝕜, simplicialJoin_incl_left t_in_Y, simplicialJoin_notMem_vertices_left y_nin_Y) := simplicialJoin_stellarSubdivision_left

  let f : SimplicialMap (Y ⋆ X) (X ⋆ Y) := @SimplicialMap.mk (E × 𝕜) (E × 𝕜) _ _ _ SimplicialJoinCommMap simplicialJoin_comm_simplicial
  let g : SimplicialMap (X ⋆ Y) (Y ⋆ X) := @SimplicialMap.mk (E × 𝕜) (E × 𝕜) _ _ _ SimplicialJoinCommMap simplicialJoin_comm_simplicial
  have gf_inv : IsInverseSimplicialIso f g := by
    constructor <;>
    · simp only [Set.restrict_eq_restrict_iff, Set.EqOn]
      intro x x_in_XY
      rw [simplicialJoin_mem_vertices] at x_in_XY
      simp only [f, g, SimplicialMap.comp, SimplicialJoinCommMap, id, Function.comp_apply]
      rcases x_in_XY with ⟨_, x_index⟩ | ⟨_, x_index⟩ <;>
      · simp only [x_index, one_ne_zero, ↓reduceIte, f, g]
        simp only [← x_index, Prod.ext_iff, Prod.fst, Prod.snd]
  have f_iso : IsSimplicialIso f := by use g
  apply stellarSubdivision_simplicialIso _ _ _ _ _ f_iso _ gf_inv
  simp only [Finset.ext_iff, Finset.mem_image, faceDisjoint_mem_iff]
  intro a
  constructor
  · intro a_in_img
    rcases a_in_img with ⟨b, ⟨b_in_t, b_zero⟩ | ⟨contra, _⟩, fb_a⟩
    · simp only [f, SimplicialJoinCommMap, b_zero, ↓reduceIte, f, g, Prod.ext_iff] at fb_a
      rcases fb_a with ⟨b_eq_a, a_one⟩
      rw [b_eq_a] at b_in_t
      exact Or.inr ⟨b_in_t, a_one.symm⟩
    · contradiction
  · intro a_in_disj
    rcases a_in_disj with ⟨contra, _⟩ | ⟨a_in_t, a_one⟩
    · contradiction
    · refine ⟨(a.fst, 0), ⟨?_, ?_⟩⟩
      · simp only [Prod.fst, Prod.snd, and_true]
        exact Or.inl a_in_t
      · simp only [f, SimplicialJoinCommMap, eq_self_iff_true, if_true, ← a_one, Prod.ext_iff]
  simp only [f, SimplicialJoinCommMap, eq_self_iff_true, if_true]
  simp only [g, SimplicialJoinCommMap, one_ne_zero, ↓reduceIte]

lemma simplicialJoin_stellarSubdivision_iso
    (H : ∃ (t : Finset E) (t_in_Y : t ∈ Y) (y : E) (y_nin_Y : y ∉ Y.vertices), (X ≅ σ(Y, t, y; 𝕜, t_in_Y, y_nin_Y)))
  : ∃ (t' : Finset (E × 𝕜)) (t'_in_YZ : t' ∈ Y ⋆ Z) (y' : E × 𝕜) (y'_nin_YZ : y' ∉ (Y ⋆ Z).vertices),
    ((X ⋆ Z) : AbstractSimplicialComplex (E × 𝕜)) ≅ σ(Y ⋆ Z, t', y'; 𝕜, t'_in_YZ, y'_nin_YZ) :=
by
  rcases H with ⟨t, t_in_Y, y, y_nin_Y, X_iso_Ysubdiv⟩
  refine ⟨t ⊔ₛ ∅, simplicialJoin_incl_left t_in_Y, (y, 0), simplicialJoin_notMem_vertices_left y_nin_Y, ?_⟩
  calc (X ⋆ Z: AbstractSimplicialComplex (E × 𝕜))
    _ ≅ σ(Y, t, y; 𝕜, t_in_Y, y_nin_Y) ⋆ Z := simplicialJoin_simplicialIso_left X_iso_Ysubdiv
    _ = σ(Y ⋆ Z, t ⊔ₛ ∅, (y, 0); 𝕜, simplicialJoin_incl_left t_in_Y, simplicialJoin_notMem_vertices_left y_nin_Y) := simplicialJoin_stellarSubdivision_left

theorem simplicialJoin_stellarMove (X_move_Y : X ≅ₛₜₘ[𝕜] Y) : ((X ⋆ Z) ≅ₛₜₘ[𝕜] ((Y ⋆ Z) : AbstractSimplicialComplex (E × 𝕜))) := by
  rcases X_move_Y with X_move_Ysubdiv | Ksubdiv_move_L | K_iso_L
  · exact Or.inl (simplicialJoin_stellarSubdivision_iso X_move_Ysubdiv)
  · exact Or.inr (Or.inl (simplicialJoin_stellarSubdivision_iso Ksubdiv_move_L))
  · exact Or.inr (Or.inr (simplicialJoin_simplicialIso_left K_iso_L))

theorem simplicialJoin_stellarEquiv_left (X_eq_Y : X ≅ₛₜ[𝕜] Y) : (X ⋆ Z) ≅ₛₜ[𝕜] (Y ⋆ Z : AbstractSimplicialComplex (E × 𝕜)) := by
  induction' X_eq_Y with K L X_eq_K K_move_L XZ_eq_KZ
  · rfl
  · calc (X ⋆ Z : AbstractSimplicialComplex (E × 𝕜))
      _ ≅ₛₜ[𝕜]  K ⋆ Z := XZ_eq_KZ
      _ ≅ₛₜₘ[𝕜] L ⋆ Z := simplicialJoin_stellarMove K_move_L

theorem simplicialJoin_stellarEquiv_right (X_eq_Y : X ≅ₛₜ[𝕜] Y) : (Z ⋆ X) ≅ₛₜ[𝕜] (Z ⋆ Y : AbstractSimplicialComplex (E × 𝕜)) :=
  calc (Z ⋆ X : AbstractSimplicialComplex (E × 𝕜))
    _ ≅     X ⋆ Z := simplicialJoin_comm
    _ ≅ₛₜ[𝕜] Y ⋆ Z := simplicialJoin_stellarEquiv_left X_eq_Y
    _ ≅     Z ⋆ Y := simplicialJoin_comm

-- Lemma 3.1, p.10
theorem simplicialJoin_stellarEquiv (X_eq_Y : X ≅ₛₜ[𝕜] Y) (Z_eq_W : Z ≅ₛₜ[𝕜] W) : (X ⋆ Z) ≅ₛₜ[𝕜] (Y ⋆ W : AbstractSimplicialComplex (E × 𝕜)) :=
  calc (X ⋆ Z : AbstractSimplicialComplex (E × 𝕜))
    _ ≅ₛₜ[𝕜] Y ⋆ Z := simplicialJoin_stellarEquiv_left X_eq_Y
    _ ≅ₛₜ[𝕜] Y ⋆ W := simplicialJoin_stellarEquiv_right Z_eq_W
