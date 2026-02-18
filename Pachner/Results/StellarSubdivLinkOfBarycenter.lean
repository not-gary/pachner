import Pachner.Stellar.StellarSubdivision

variable {E : Type _} [DecidableEq E] [AddCommGroup E]
variable {𝕜 : Type _} [DecidableEq 𝕜] [Ring 𝕜] [Nontrivial 𝕜]
variable {X : AbstractSimplicialComplex E} {s t : Finset E} {x : E}

theorem stellarSubdivision_link_of_barycenter_left
    {s_in_X : s ∈ X.faces}
    {x_nin_X : x ∉ X.vertices}
  : Lk(σ(X, s, x; 𝕜, s_in_X, x_nin_X), {x}) ⊆
      ((π₁[𝕜] (disjoint_link_boundary X s)).coe ''ˢ (Lk(X, s) ⋆ ∂s)) :=
by
  intro a a_in_link
  simp only [Link, Set.mem_sep_iff] at a_in_link
  choose a_in_subdiv xa_in_subdiv xa_disj using a_in_link
  simp only [StellarSubdivision, SimplicialUnion, Set.mem_union] at xa_in_subdiv
  cases' xa_in_subdiv with xa_in_star_comp xa_in_join
  simp only [StarComplement, Set.mem_sep_iff] at xa_in_star_comp
  choose xa_in_X s_nss_xa using xa_in_star_comp
  have contra : x ∈ X.vertices :=
  by
    rw [AbstractSimplicialComplex.mem_vertices]
    apply @X.down_closed ({x} ∪ a)
    assumption
    apply Finset.subset_union_left
    apply Finset.singleton_ne_empty
  contradiction
  rw [simplicialJoinProj_union_mem] at xa_in_join
  choose x' x'_in_join a' a'_in_join x₁ x₁_in_link a₁ a₁_in_link x_decomp a_decomp xa'_in_join
    xa₁_in_link using xa_in_join
  rw [Set.mem_union, Set.mem_singleton_iff, simplicialJoinProj_union_mem] at xa'_in_join
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
      simp only [x₁_eq_x, Link, Set.mem_union, Set.mem_singleton_iff, Set.mem_sep_iff] at x₁_in_link
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
      apply isSubcomplex_face_imp_face
      apply x₂_in_bd
      apply faceBoundary_subcomplex
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
  rw [simplicialJoinProj_mem]
  use a₁; constructor; assumption
  use a₂; constructor; assumption
  rw [Finset.union_comm]
  constructor; assumption
  exact face_nonempty a_in_subdiv

  -- xa'_empty case.
  rw [Finset.union_eq_empty] at xa'_empty
  choose x'_empty a'_empty using xa'_empty
  subst x'_empty a'_empty
  rw [Finset.empty_union] at a_decomp x_decomp
  subst x_decomp a_decomp
  rw [simplicialJoinProj_mem]
  use a; constructor; assumption
  use ∅; constructor
  rw [Set.mem_union]
  right; apply Set.mem_singleton
  constructor
  rw [Finset.union_empty]
  exact face_nonempty a_in_subdiv

theorem stellarSubdivision_link_of_barycenter_right
    {s_in_X : s ∈ X.faces}
    {x_nin_X : x ∉ X.vertices}
  : ((π₁[𝕜] (disjoint_link_boundary X s)).coe ''ˢ (Lk(X, s) ⋆ ∂s)) ⊆
      Lk(σ(X, s, x; 𝕜, s_in_X, x_nin_X), {x}) :=
by
  intro a a_in_img
  rw [simplicialJoinProj_mem] at a_in_img
  choose a₁ a₁_in_link a₂ a₂_in_bd a_decomp a_ne using a_in_img
  rw [Set.mem_union, Set.mem_singleton_iff] at a₁_in_link a₂_in_bd
  simp only [Link, Set.mem_sep_iff, StellarSubdivision, SimplicialUnion, Set.mem_union]
  constructor; right
  simp only [simplicialJoinProj_mem, Set.mem_union, Set.mem_singleton_iff]
  use ∅ ∪ a₂; constructor

  cases' a₂_in_bd with a₂_in_bd a₂_empty
  left; use ∅; constructor; right; rfl
  use a₂; constructor; left; assumption
  constructor; rfl
  rw [Finset.empty_union]
  exact face_nonempty a₂_in_bd

  right; rw [a₂_empty, Finset.union_empty]

  use a₁; constructor; assumption
  rw [Finset.empty_union, Finset.union_comm]
  constructor <;> assumption

  constructor; right
  simp only [simplicialJoinProj_mem, Set.mem_union, Set.mem_singleton_iff]
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
    rw [vertex_iff_in_face]
    cases' x_in_a with x_in_a₁ x_in_a₂
    use a₁; constructor
    apply isSubcomplex_face_imp_face

    cases' a₁_in_link with a₁_in_link a₁_empty
    apply a₁_in_link

    rw [a₁_empty] at x_in_a₁
    contradiction

    apply link_subcomplex
    assumption
    use a₂; constructor
    apply isSubcomplex_face_imp_face

    cases' a₂_in_bd with a₂_in_bd a₂_empty
    apply a₂_in_bd

    rw [a₂_empty] at x_in_a₂
    contradiction

    apply faceBoundary_subcomplex
    assumption
    assumption
  contradiction

theorem stellarSubdivision_link_of_barycenter
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
  : Lk(σ(X, s, x; 𝕜, s_in_X, x_nin_X), {x}) =
      ((π₁[𝕜] (disjoint_link_boundary X s)).coe ''ˢ (Lk(X, s) ⋆ ∂s)) :=
by
  rw [AbstractSimplicialComplex.ext_iff, Set.Subset.antisymm_iff]
  exact ⟨stellarSubdivision_link_of_barycenter_left, stellarSubdivision_link_of_barycenter_right⟩
