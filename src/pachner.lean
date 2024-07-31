import tactic          -- standard proof tactics
import data.set        -- basics on sets
import data.set.finite -- basics on finite sets
import data.finset     -- type-level finite sets
import .simplicial_complex
import .simplicial_subcomplex
import .combinatorical_manifold
import .stellar
import .bistellar

variables {α β : Type*}
variables [decidable_eq α] [decidable_eq β]

theorem pachner
    (X : closed_combinatorical_manifold α)
    (Y : closed_combinatorical_manifold β)
  : is_bistellar_equivalent X.manifold Y.manifold ↔
      is_stellar_equivalent X.manifold.complex Y.manifold.complex
:=
begin
  unfold is_bistellar_equivalent,
  unfold is_stellar_equivalent,
  split, intros,

  -- bistellar => stellar
  sorry,
  -- stellar => bistellar
  sorry,
end

-- Containment for later reference.
lemma stellar_subdiv_link_of_star_mem
    {X : simplicial_complex α}
    {s t : finset α} [s_ne : nonempty s]
    {x : α}
    {s_in_X : s ∈ X.simplices}
    {x_nin_X : x ∉ vertices X}
    (t_in_join : (∃ (t₁ t₂ t₃ : finset α),
                    nonempty t₁ ∧ t₁ ∈ (Lk(X, s) s_in_X).simplices ∧
                    nonempty t₂ ∧ t₂ ∈ (∂s).simplices ∧
                    nonempty t₃ ∧ t₃ ∈ (@simplex α {x}).simplices ∧
                    t = t₁ ∪ t₂ ∪ t₃))
  : t ∈ (σ(X, s, x; s_ne, s_in_X, x_nin_X)).simplices
:= sorry

lemma stellar_subdiv_link_of_star_left
    (X : simplicial_complex α)
    (s t : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (t_in_join : (∃ (t₁ t₂ t₃ : finset α),
                    nonempty t₁ ∧ t₁ ∈ (Lk(X, s) s_in_X).simplices ∧
                    nonempty t₂ ∧ t₂ ∈ (∂s).simplices ∧
                    nonempty t₃ ∧ t₃ ∈ (@simplex α {x}).simplices ∧
                    t = t₁ ∪ t₂ ∪ t₃))
  : (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), t) (stellar_subdiv_link_of_star_mem t_in_join)).simplices
      ⊆ {∅}
:= begin
  simp only [set.subset_def, link, stellar_subdivision, simplicial_union, set.mem_union, set.mem_sep_iff, set.mem_singleton_iff],
  intros u u_in_link,
  choose u_in_subdiv tu_in_subdiv tu_disj using u_in_link,

  choose t₁ t₂ t₃ t₁_ne t₁_in_link t₂_ne t₂_in_bd t₃_ne t₃_in_barycenter t_decomp using t_in_join,
  simp only [simplex, finset.mem_coe, finset.mem_powerset, finset.subset_singleton_iff] at t₃_in_barycenter,
  cases t₃_in_barycenter with t₃_empty t₃_eq_x,
  rw [finset.nonempty_coe_sort, finset.nonempty_iff_ne_empty] at t₃_ne,
  contradiction,
  subst t₃_eq_x,

  cases tu_in_subdiv with tu_in_star_comp tu_in_join, -- Cases A, B resp.

  -- Case A + (C/D).
  { simp only [star_complement, set.mem_sep_iff] at tu_in_star_comp,
    choose tu_in_X s_nss_tu using tu_in_star_comp,
    
    have contra : x ∈ vertices X, from
    begin
      rw [vertex_iff_singleton],
      apply X.subset_closed (t ∪ u),
      assumption,

      apply @finset.subset.trans _ _ t,
      rw [t_decomp],
      apply finset.subset_union_right,
      apply finset.subset_union_left,
    end,
    
    contradiction, },

  cases u_in_subdiv with u_in_star_comp u_in_join, -- Cases C, D resp.

  -- Case B + C.
  {  },
end

-- TODO: Not true. Only works if max dim, we need not be the case.
--       What's the correct RHS, then?
lemma stellar_subdiv_link_of_star
    (X : simplicial_complex α)
    (s t : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : (∃ (t₁ t₂ t₃ : finset α),
        nonempty t₁ ∧ t₁ ∈ (Lk(X, s) s_in_X).simplices ∧
        nonempty t₂ ∧ t₂ ∈ (∂s).simplices ∧
        nonempty t₃ ∧ t₃ ∈ (@simplex α {x}).simplices ∧
        t = t₁ ∪ t₂ ∪ t₃) →
      (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), t) sorry).simplices = {∅}
:= sorry

lemma stellar_subdiv_link_of_link_barycenter_mem
    {X : simplicial_complex α}
    {s t : finset α} [s_ne : nonempty s]
    {x : α}
    {s_in_X : s ∈ X.simplices}
    {x_nin_X : x ∉ vertices X}
    (t_in_join : ∃ (t₁ t₂ : finset α),
                    nonempty t₁ ∧ t₁ ∈ (Lk(X, s) s_in_X).simplices ∧
                    nonempty t₂ ∧ t₂ ∈ (@simplex α {x}).simplices ∧
                    t = t₁ ∪ t₂)
  : t ∈ (σ(X, s, x; s_ne, s_in_X, x_nin_X)).simplices
:= sorry

lemma stellar_subdiv_link_of_link_barycenter_left
    (X : simplicial_complex α)
    (s t : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (t_in_join : ∃ (t₁ t₂ : finset α),
                    nonempty t₁ ∧ t₁ ∈ (Lk(X, s) s_in_X).simplices ∧
                    nonempty t₂ ∧ t₂ ∈ (@simplex α {x}).simplices ∧
                    t = t₁ ∪ t₂)
  : (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), t) (stellar_subdiv_link_of_link_barycenter_mem t_in_join)).simplices
      ⊆ (∂s).simplices
:= begin
  simp only [set.subset_def, link, stellar_subdivision, simplicial_union, set.mem_union, set.mem_sep_iff],
  intros u u_in_link,
  choose u_in_subdiv tu_in_subdiv tu_disj using u_in_link,

  choose t₁ t₂ t₁_ne t₁_in_link t₂_ne t₂_in_barycenter t_decomp using t_in_join,
  simp only [simplex, finset.mem_coe, finset.mem_powerset, finset.subset_singleton_iff] at t₂_in_barycenter,
  cases t₂_in_barycenter with t₂_empty t₂_eq_x,
  rw [finset.nonempty_coe_sort, finset.nonempty_iff_ne_empty] at t₂_ne,
  contradiction,
  subst t₂_eq_x,

  rw [simplex_boundary_mem_iff_subset, finset.ssubset_iff_subset_ne],
  cases tu_in_subdiv with tu_in_star_comp tu_in_join, -- Cases A, B resp.

  -- Case A + (C/D).
  { simp only [star_complement, set.mem_sep_iff] at tu_in_star_comp,
    choose tu_in_X s_nss_tu using tu_in_star_comp,
    
    have contra : x ∈ vertices X, from
    begin
      rw [vertex_iff_singleton],
      apply X.subset_closed (t ∪ u),
      assumption,

      apply @finset.subset.trans _ _ t,
      rw [t_decomp],
      apply finset.subset_union_right,
      apply finset.subset_union_left,
    end,
    
    contradiction, },

  cases u_in_subdiv with u_in_star_comp u_in_join, -- Cases C, D resp.

  -- Case B + C.
  { simp only [star_complement, set.mem_sep_iff] at u_in_star_comp,
    choose u_in_X s_nss_u using u_in_star_comp,
    
    rw [join_proj_disj_union_mem] at tu_in_join,
    choose v' v'_in_join u' u'_in_join v₁ v₁_in_link u₁ u₁_in_link t_decomp u_decomp vu'_in_join vu₁_in_link using tu_in_join,
    rw [join_proj_disj_union_mem] at vu'_in_join,
    choose v₃ v₃_in_barycenter u₃ u₃_in_barycenter v₂ v₂_in_bd u₂ u₂_in_bd v'_decomp u'_decomp vu₃_in_barycenter vu₂_in_bd using vu'_in_join,
    subst v'_decomp,
    subst u'_decomp,
    
    simp only [simplex, finset.mem_coe, finset.mem_powerset, finset.subset_singleton_iff] at v₃_in_barycenter,
    cases v₃_in_barycenter with v₃_empty v₃_eq_x,
     },
end

lemma stellar_subdiv_link_of_link_barycenter
    (X : simplicial_complex α)
    (s t : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (t_in_join : ∃ (t₁ t₂ : finset α),
                    nonempty t₁ ∧ t₁ ∈ (Lk(X, s) s_in_X).simplices ∧
                    nonempty t₂ ∧ t₂ ∈ (@simplex α {x}).simplices ∧
                    t = t₁ ∪ t₂)
  : (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), t) (stellar_subdiv_link_of_link_barycenter_mem t_in_join)).simplices
      = (∂s).simplices
:= sorry

lemma stellar_subdiv_link_of_boundary_barycenter
    (X : simplicial_complex α)
    (s t : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : (∃ (t₁ t₂ : finset α),
        nonempty t₁ ∧ t₁ ∈ (@simplex α {x}).simplices ∧
        nonempty t₂ ∧ t₂ ∈ (∂s).simplices ∧
        t = t₁ ∪ t₂) →
      (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), t) sorry).simplices = (Lk(X, s) s_in_X).simplices
:= sorry