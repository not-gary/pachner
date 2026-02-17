import Pachner.Constructions.Join
import Pachner.Subcomplex.Intersection
import Pachner.Subcomplex.Star
import Pachner.Subcomplex.StarComplement
import Pachner.Subcomplex.Link

variable {E : Type _}
variable [DecidableEq E] [AddCommGroup E]
variable {𝕜 : Type _}
variable [DecidableEq 𝕜] [Ring 𝕜] [Nontrivial 𝕜]
variable {X Y Z : AbstractSimplicialComplex E} {s t : Finset E}

-- Distributive properties of join over union
section Union

-- Lemma 2.4 (1), p.8
theorem simplicialJoin_simplicialUnion_left : (X ⋆ (Y ∪ Z)) = (X ⋆ Y ∪ X ⋆ Z : AbstractSimplicialComplex (E × 𝕜)) := by
  simp only [AbstractSimplicialComplex.ext_iff, SimplicialJoin, SimplicialUnion,
    AbstractSimplicialComplex.instHasUnion, Set.ext_iff]
  intro x
  constructor
  · intro H
    rw [Set.mem_diff] at H
    cases' H with H x_empty
    rcases H with ⟨s, Hs, t, Ht, Hx⟩
    rw [Set.mem_union, Set.mem_diff, Set.mem_diff]
    iterate 2 rw [Set.mem_setOf]
    iterate 2 rw [Set.mem_union] at Ht
    cases' Ht with Ht t_empty
    cases' Ht with t_in_y t_in_Z
    left
    constructor
    use s; constructor; tauto
    use t; tauto
    assumption
    right
    constructor
    use s; constructor; tauto
    use t; tauto
    assumption
    right
    constructor
    use s; constructor; tauto
    use t; tauto
    assumption
  · intro H
    rw [Set.mem_union, Set.mem_diff, Set.mem_diff] at H
    cases' H with Hy Hz
    cases' Hy with Hy x_nonempty
    rcases Hy with ⟨s, Hs, t, Ht, Hx⟩
    rw [Set.mem_diff]
    constructor
    use s; constructor; tauto
    use t
    rw [Set.mem_union, Set.mem_union]
    rw [Set.mem_union] at Ht
    tauto
    assumption
    cases' Hz with Hz x_nonempty
    rcases Hz with ⟨s, Hs, t, Ht, Hx⟩
    rw [Set.mem_diff]
    constructor
    use s; constructor; tauto
    use t
    rw [Set.mem_union, Set.mem_union]
    constructor
    rw [Set.mem_union] at Ht
    tauto
    assumption
    assumption

theorem simplicialJoin_simplicialUnion_right : ((Y ∪ Z) ⋆ X) = (Y ⋆ X ∪ (Z ⋆ X : AbstractSimplicialComplex (E × 𝕜))) := by
  simp only [AbstractSimplicialComplex.ext_iff, SimplicialJoin,
    AbstractSimplicialComplex.instHasUnion, SimplicialUnion, Set.ext_iff, Set.mem_union,
    Set.mem_diff, Set.mem_setOf]
  intro u
  constructor
  · intro u_in_join
    choose u_in_join u_ne using u_in_join
    choose s s_in_YZ t t_in_X st_eq_u using u_in_join
    rw [or_or_distrib_right] at s_in_YZ
    cases' s_in_YZ with s_in_Y s_in_Z
    left; constructor
    use s; constructor; assumption
    use t
    assumption

    right; constructor
    use s; constructor; assumption
    use t
    assumption
  · intro u_in_union
    cases' u_in_union with u_in_XY u_in_XZ
    choose u_in_XY u_ne using u_in_XY
    choose s s_in_X t t_in_Y st_eq_u using u_in_XY
    constructor
    use s; constructor
    rw [or_or_distrib_right]
    left; assumption
    use t
    assumption

    choose u_in_XZ u_ne using u_in_XZ
    choose s s_in_X t t_in_Z st_eq_u using u_in_XZ
    constructor
    use s; constructor
    rw [or_or_distrib_right]
    right; assumption
    use t
    assumption

end Union


-- Distributive properties of join over intersection
section Intersection

-- TODO: simplicialJoin_simplicialInter_left

-- Lemma 2.4 (2), p.8
theorem simplicialJoin_simplicialInter_right : (X ⋆ (Y ∩ Z)) = (X ⋆ Y ∩ (X ⋆ Z) : AbstractSimplicialComplex (E × 𝕜)) := by
  simp only [AbstractSimplicialComplex.ext_iff, SimplicialJoin, SimplicialInter,
    AbstractSimplicialComplex.instHasInter, Set.ext_iff]
  intro x
  constructor
  · intro H
    rw [Set.mem_diff] at H
    cases' H with H x_empty
    rcases H with ⟨s, Hs, t, Ht, Hx⟩
    rw [Set.mem_inter_iff, Set.mem_diff, Set.mem_diff]
    iterate 2 rw [Set.mem_setOf]
    rw [Set.mem_union] at Ht
    rw [Set.mem_inter_iff] at Ht
    cases' Ht with Ht t_empty
    cases' Ht with Hy Hz
    constructor
    constructor
    use s; constructor; tauto
    use t; tauto
    assumption
    constructor
    use s; constructor; tauto
    use t; tauto
    assumption
    constructor
    constructor
    use s; constructor; tauto
    use t; tauto
    assumption
    constructor
    use s; constructor; tauto
    use t; tauto
    assumption
  · intro H
    rw [Set.mem_inter_iff, Set.mem_diff, Set.mem_diff] at H
    cases' H with Hy Hz
    cases' Hy with Hy x_nonempty
    cases' Hz with Hz x_nonempty
    rcases Hy with ⟨sy, Hsy, ty, Hty, Hxy⟩
    rcases Hz with ⟨sz, Hsz, tz, Htz, Hxz⟩
    subst Hxy
    rw [simplexDisjoint_eq_unique] at Hxz
    cases' Hxz with Hsz Htz
    subst Hsz; subst Htz
    rw [Set.mem_diff]
    constructor
    use sz; constructor; tauto
    use tz
    rw [Set.mem_union, Set.mem_inter_iff]
    constructor
    cases' Htz with Htz t_empty
    cases' Hty with Hty t_empty
    iterate 5 tauto

end Intersection

-- Distributive properties of join over star
section Star

-- TODO: simplicialJoin_star_right

-- Lemma 2.2 (2), p.7
theorem simplicialJoin_star_left
    (s_in_X : s ∈ X.faces)
  : St(X, s) ⋆ Y = (St(X ⋆ Y, s ⊔ₛ ∅) : AbstractSimplicialComplex (E × 𝕜)) :=
by
  simp only [SimplicialJoin, StarNeighborhood, AbstractSimplicialComplex.ext_iff, Set.ext_iff]
  intro x
  repeat' rw [Set.mem_setOf, Set.mem_diff, Set.mem_singleton_iff]
  constructor
  · intro H
    choose H x_nonempty using H
    rcases H with ⟨t, Ht, u, Hu, Hx⟩
    rw [Set.mem_union] at Ht
    cases' Ht with Ht t_empty
    rw [Set.mem_sep_iff] at Ht
    cases' Ht with Ht Hst
    constructor
    constructor
    use t; constructor; tauto
    use u; tauto
    subst Hx
    constructor
    use s ∪ t; constructor; tauto
    use u
    constructor <;> try rw [simplexDisjoint_distr_union]; simp
    assumption
    simp
    intro s_empty
    intro t_empty
    subst t_empty
    simp at x_nonempty
    assumption
    rw [Set.mem_singleton_iff] at t_empty
    subst t_empty
    constructor
    constructor
    use ∅
    constructor
    tauto
    use u
    assumption
    subst Hx
    constructor
    use s
    constructor
    tauto
    use u
    constructor
    assumption
    rw [simplexDisjoint_distr_union, simplexDisjoint_eq_unique]
    constructor
    rw [Finset.union_empty]
    rw [Finset.empty_union]
    simp
    intro
    simp at x_nonempty
    assumption
  · intro H
    cases' H with Hx Hx_union
    choose Hx x_nonempty using Hx
    rcases Hx with ⟨t, Ht, u, Hu, Hx⟩
    choose Hx_union x_union_nonempty using Hx_union
    rcases Hx_union with ⟨t', Ht', u', Hu', Hx_union⟩
    subst Hx
    rw [simplexDisjoint_distr_union, simplexDisjoint_eq_unique] at Hx_union
    cases' Hx_union with Ht' Hu'
    simp at Hu'
    subst Ht'; subst Hu'
    cases' Ht with t_in_X t_empty
    · constructor
      use t
      constructor
      rw [Set.mem_union, Set.mem_sep_iff]
      left
      constructor; assumption
      cases' Ht' with st_in_X st_empty
      · assumption
      · simp at st_empty
        choose s_empty t_empty using st_empty
        subst s_empty t_empty
        revert s_in_X
        contrapose
        intro empty_in_X
        simp at empty_in_X
        assumption
      use u'
      assumption
    · constructor
      use ∅
      constructor; tauto
      use u'
      constructor; assumption
      rw [Set.mem_singleton_iff] at t_empty
      subst t_empty
      trivial
      assumption

end Star


-- Distributive properties of join over star complement
section StarComplement

theorem simplicialJoin_starComplement_left
    (s_in_X : s ∈ X.faces)
  : X\St(X, s) ⋆ Y =
      ((X ⋆ Y)\St(X ⋆ Y, s ⊔ₛ ∅) : AbstractSimplicialComplex (E × 𝕜)) :=
by
  simp only [SimplicialJoin, StarComplement, AbstractSimplicialComplex.ext_iff, Set.ext_iff]
  intro x
  repeat' rw [Set.mem_setOf, Set.mem_diff, Set.mem_singleton_iff]
  constructor
  · intro H
    choose H x_nonempty using H
    rcases H with ⟨t, Ht, u, Hu, Hx⟩
    rw [Set.mem_union] at Ht
    rw [Set.mem_sep_iff] at Ht
    cases' Ht with Ht t_empty
    cases' Ht with Ht Hs_not_sset_t
    constructor
    constructor
    use t; constructor; tauto
    use u; tauto
    subst Hx
    rw [simplexDisjoint_subset_unique]
    simp; tauto
    rw [Set.mem_singleton_iff] at t_empty
    subst t_empty
    constructor
    constructor
    use ∅
    constructor; tauto
    use u; tauto
    subst Hx
    rw [simplexDisjoint_subset_unique]
    simp
    revert s_in_X
    contrapose
    rw [Classical.not_not]
    intro s_empty
    subst s_empty
    apply X.empty_notMem
  · intro H
    cases' H with Hx Hs_not_sset_x
    cases' Hx with Hx x_nonempty
    rcases Hx with ⟨t, Ht, u, Hu, Hx⟩
    subst Hx
    rw [simplexDisjoint_subset_unique] at Hs_not_sset_x
    simp at Hs_not_sset_x
    cases' Ht with Ht t_empty
    · constructor
      use t; constructor
      rw [Set.mem_union, Set.mem_sep_iff]
      left
      constructor <;> assumption
      use u; assumption
    · constructor
      use ∅
      constructor
      tauto
      use u
      constructor
      assumption
      rw [t_empty]
      assumption

-- Lemma 2.2 (3), p.7
-- TODO: could be = instead of ≅ but requires some work
theorem simplicialJoin_starComplement_right
    (s_in_X : s ∈ X.faces)
  : (Y ⋆ (X\St(X, s)) : AbstractSimplicialComplex (E × 𝕜)) ≅
      ((X ⋆ Y)\St(X ⋆ Y, s ⊔ₛ ∅) : AbstractSimplicialComplex (E × 𝕜)) :=
by
  calc Y ⋆ (StarComplement X s)
    _ ≅ (StarComplement X s) ⋆ Y := simplicialJoin_comm
    _ = StarComplement (X ⋆ Y) (s ⊔ₛ ∅) := simplicialJoin_starComplement_left s_in_X

end StarComplement


-- Distributive properties of join over Link
section Link


-- Lemma 2.3, p.8
theorem simplicialJoin_link
    (s_in_X : s ∈ X.faces ∨ s = ∅)
    (t_in_Y : t ∈ Y.faces ∨ t = ∅)
  : Lk(X ⋆ Y, s ⊔ₛ t) = (Lk(X, s) ⋆ Lk(Y, t) : AbstractSimplicialComplex (E × 𝕜)) :=
by
  simp only [Link, SimplicialJoin, AbstractSimplicialComplex.ext_iff, Set.ext_iff]
  intro x
  repeat' rw [Set.mem_setOf, Set.mem_diff, Set.mem_singleton_iff]
  constructor
  · intro H
    cases' H with H_left H_right
    cases' H_left with H_left x_nonempty
    rcases H_left with ⟨s', Hs', t', Ht', Hx⟩
    cases' H_right with H_left H_inter
    cases' H_left with H_left st_x_nonempty
    rcases H_left with ⟨s'', Hs'', t'', Ht'', H_union⟩
    subst Hx
    rw [simplexDisjoint_distr_inter, simplexDisjoint_empty] at H_inter
    rw [simplexDisjoint_distr_union, simplexDisjoint_eq_unique] at H_union
    cases' H_union with H_s_union H_t_union
    subst H_s_union; subst H_t_union
    constructor
    cases' Hs' with Hs' s_empty
    use s'; constructor
    rw [Set.mem_union, Set.mem_sep_iff]
    left
    constructor; assumption
    constructor
    cases' Hs'' with Hs'' s''_empty
    assumption
    simp at s''_empty
    choose s_empty s'_empty using s''_empty
    subst s_empty s'_empty
    simp
    assumption
    tauto
    use t'
    constructor
    rw [Set.mem_union, Set.mem_sep_iff]
    cases' Ht' with Ht' t_empty
    left
    constructor; assumption
    constructor
    cases' Ht'' with Ht'' t''_empty
    assumption
    simp at t''_empty
    choose t_empty t'_empty using t''_empty
    subst t_empty t'_empty
    iterate 4 tauto
    use s'
    constructor; tauto
    use t'
    constructor
    cases' Ht' with Ht' t_empty
    rw [Set.mem_union, Set.mem_sep_iff]
    left
    constructor; assumption
    constructor
    cases' Ht'' with Ht'' t''_empty
    assumption
    simp at t''_empty
    choose t_empty t'_empty using t''_empty
    subst t_empty t'_empty
    iterate 5 tauto
  · intro H
    cases' H with H x_nonempty
    rcases H with ⟨s', Hs', t', Ht', Hx⟩
    constructor
    · constructor
      use s'
      constructor
      cases' Hs' with Hs' s_empty
      rw [Set.mem_sep_iff] at Hs'
      tauto
      tauto
      use t'
      constructor
      cases' Ht' with Ht' t_empty
      rw [Set.mem_sep_iff] at Ht'
      tauto
      tauto
      assumption
      assumption
    · constructor
      constructor
      use s ∪ s'
      constructor
      cases' Hs' with Hs' s_empty
      rw [Set.mem_sep_iff] at Hs'
      tauto
      rw[ Set.mem_singleton_iff] at s_empty
      subst s_empty
      simp; tauto
      use t ∪ t'
      constructor
      cases' Ht' with Ht' t_empty
      rw [Set.mem_sep_iff] at Ht'
      tauto
      rw [Set.mem_singleton_iff] at t_empty
      subst t_empty
      simp; tauto
      subst Hx
      rw [simplexDisjoint_distr_union]
      subst Hx
      simp
      intro s_empty t_empty s'_empty
      subst s_empty t_empty s'_empty
      simp at x_nonempty
      assumption
      subst Hx
      rw [simplexDisjoint_distr_inter, simplexDisjoint_empty]
      cases' Hs' with Hs' s_empty
      rw [Set.mem_sep_iff] at Hs'
      constructor; tauto
      cases' Ht' with Ht' t_empty
      rw [Set.mem_sep_iff] at Ht'
      tauto
      rw [Set.mem_singleton_iff] at t_empty
      subst t_empty
      simp
      constructor
      rw [Set.mem_singleton_iff] at s_empty
      subst s_empty
      simp
      cases' Ht' with Ht' t_empty
      rw [Set.mem_sep_iff] at Ht'
      tauto
      rw [Set.mem_singleton_iff] at t_empty
      subst t_empty
      simp

-- Lemma 2.2 (1), p.7
theorem simplicialJoin_link_left
    (s_in_X : s ∈ X.faces)
  : Lk(X, s) ⋆ Y = (Lk(X ⋆ Y, s ⊔ₛ ∅) : AbstractSimplicialComplex (E × 𝕜)) :=
by
  rw [simplicialJoin_link (Set.mem_union_left {∅} s_in_X) (by right; rfl), link_empty_eq_self]

theorem simplicialJoin_link_right
    (t_in_Y : t ∈ Y.faces)
  : X ⋆ Lk(Y, t) = (Lk(X ⋆ Y, ∅ ⊔ₛ t) : AbstractSimplicialComplex (E × 𝕜)) :=
by
  rw [simplicialJoin_link (by right; rfl) (Set.mem_union_left {∅} t_in_Y), link_empty_eq_self]

end Link
