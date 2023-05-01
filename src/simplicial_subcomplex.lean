import tactic          -- standard proof tactics
import data.set        -- basics on sets
import data.set.finite -- basics on finite sets
import data.finset     -- type-level finite sets
import .simplicial_complex
import .fin_simplicial_complex
import .simplicial_map

variables {α β : Type*}
variables [decidable_eq α] [decidable_eq β]

-- Boundary of a single simplex.
def simplex_boundary
    (s : finset α)
  : simplicial_complex α
:= simplicial_complex.mk
    (((finset.powerset s) \ {s}) ∪ {∅})
    (begin
      rw [set.nonempty_coe_sort, set.nonempty_def],

      use ∅,
      rw [set.mem_union],
      right,
      tauto,
    end)
    (begin
      simp,
      split,

      intros t t_sset_empty,
      left,
      rw [←finset.subset_empty],
      assumption,

      intros s_1 _ _ t _,

      have : s_1 ⊆ t -> t ⊆ s_1 -> s_1 = t, from
      begin
        exact subset_antisymm,
      end,

      have : t ⊆ s_1 -> s_1 ⊆ s -> t ⊆ s, from
      begin
        exact subset_trans,
      end,
      finish,
    end)
prefix `∂`:75 := simplex_boundary

instance simplex_boundary.fintype
    (s : finset α)
  : fintype (∂s).simplices
:= begin
  unfold simplex_boundary,
  dsimp only[simplicial_complex.simplices],
  apply set.fintype_union,
end

lemma simplex_boundary_iso
    (s : finset α) [nonempty s]
    (t : finset β) [nonempty t]
  : simplex s ≅ simplex t → ∂s ≅ ∂t
:= sorry

-- Star of a complex wrt a simplex.
@[simp]
def star
    (X : simplicial_complex α)
    (s : finset α)
    (s_in_X : s ∈ X.simplices)
  : simplicial_complex α
:= simplicial_complex.mk
    ({t ∈ X.simplices | (s ∪ t) ∈ X.simplices})
    (begin
      rw [set.nonempty_coe_sort, set.nonempty_def],
      use ∅,
      rw [set.mem_sep_iff],
      split,

      apply simplicial_complex_empty_simplex,

      rw [finset.union_empty],
      assumption,
    end)
    (begin
      simp,
      intros s_1 _ _ t _,

      have : t ⊆ s_1 -> t ∈ X.simplices, from
      begin
        apply X.subset_closed, assumption
      end,

      have : s ⊆ s -> t ⊆ s_1 -> s ∪ t ⊆ s ∪ s_1, from
      begin
        exact finset.union_subset_union,
      end,

      have : s ∪ t ⊆ s ∪ s_1 -> s ∪ t ∈ X.simplices, from
      begin
        apply X.subset_closed, assumption,
      end,
      finish,
    end)
notation `St(` X `, ` s `)` := star X s

instance star.fintype
    (X : simplicial_complex α) [fintype X.simplices]
    (s : finset α)
    (s_in_X : s ∈ X.simplices)
  : fintype (star X s s_in_X).simplices
:= begin
  unfold star,
  dsimp only[simplicial_complex.simplices],

  have H_dec : decidable_pred (λ a : finset α, s ∪ a ∈ X.simplices), from
  begin
    unfold decidable_pred,
    intros a,
    apply set.decidable_mem_of_fintype,
  end,

  apply @set.fintype_sep _ _ _ _ H_dec,
  assumption,
end

-- TODO: Potential problem with statement. Correctly, if f : X -> Y
--       is iso'sm, then we want f(s) = t. But, maybe this is fine?
--       Problem reflects in other constructions below.
lemma star_iso
    (X : simplicial_complex α)
    (Y : simplicial_complex β)
    (s : finset α)
    (t : finset β)
    (f : simplicial_map X Y)
    (s_in_X : s ∈ X.simplices)
    (t_in_Y : t ∈ Y.simplices)
    (f_iso : is_simplicial_iso f)
  : finset.image f.map s = t → St(X, s) s_in_X ≅ St(Y, t) t_in_Y
:= sorry

-- Link of a complex wrt a simplex.
@[simp]
def link
    (X : simplicial_complex α)
    (s : finset α)
    (s_in_X : s ∈ X.simplices)
  : simplicial_complex α
:= simplicial_complex.mk
    ({t ∈ X.simplices | (s ∪ t) ∈ X.simplices ∧ (s ∩ t) = ∅})
    (begin
      rw [set.nonempty_coe_sort, set.nonempty_def],
      use ∅,
      rw [set.mem_sep_iff],
      split,

      apply simplicial_complex_empty_simplex,

      split,

      rw [finset.union_empty],
      assumption,

      rw [finset.inter_empty],
    end)
    (begin
      simp,
      intros s_1 _ _ _ Hss1_inter t Ht_sset,

      split; split; try
      { revert Ht_sset,
        apply X.subset_closed,
        assumption, },
      
      { suffices : s ∪ t ⊆ s ∪ s_1,
        revert this,
        apply X.subset_closed,
        assumption,
        
        apply finset.union_subset_union; tauto, },

      { rw [←finset.disjoint_iff_inter_eq_empty],
        apply finset.disjoint_of_subset_right Ht_sset,
        rw [finset.disjoint_iff_inter_eq_empty],
        assumption, },
    end)
notation `Lk(` X `, ` s `)` := link X s

instance link.fintype
    (X : simplicial_complex α) [fintype X.simplices]
    (s : finset α)
    (s_in_X : s ∈ X.simplices)
  : fintype (link X s s_in_X).simplices
:= begin
  simp only[link, simplicial_complex.simplices],
  rw [set.sep_and],

  have dec_left : decidable_pred (λ x : finset α, s ∪ x ∈ X.simplices), from
  begin
    unfold decidable_pred,
    intro x,
    apply set.decidable_mem_of_fintype,
  end,

  have fin_left : fintype ↥{x ∈ X.simplices | s ∪ x ∈ X.simplices}, from
  begin
    apply @set.fintype_sep _ _ _ _ dec_left,
    assumption,
  end,

  have dec_right : decidable_pred (λ x : finset α, s ∩ x = ∅), from
  begin
    unfold decidable_pred,
    intro x,
    apply set.decidable_mem_of_fintype,
  end,

  have fin_right : fintype ↥{x ∈ X.simplices | s ∩ x = ∅}, from
  begin
    apply @set.fintype_sep _ _ _ _ dec_right,
    assumption,
  end,

  apply @set.fintype_inter _ _ _ _ fin_left fin_right,
end

lemma link_iso
    (X : simplicial_complex α)
    (Y : simplicial_complex β)
    (s : finset α)
    (t : finset β)
    (f : simplicial_map X Y)
    (s_in_X : s ∈ X.simplices)
    (t_in_Y : t ∈ Y.simplices)
    (f_iso : is_simplicial_iso f)
  : finset.image f.map s = t → Lk(X, s) s_in_X ≅ Lk(Y, t) t_in_Y
:= sorry

-- Complement of the star of a complex wrt a simplex.
@[simp]
def star_complement
    (X : simplicial_complex α)
    (s : finset α) [nonempty s]
    (s_in_X : s ∈ X.simplices)
  : simplicial_complex α
:= simplicial_complex.mk
    ({t ∈ X.simplices | ¬(s ⊆ t)})
    (begin
      rw [set.nonempty_coe_sort, set.nonempty_def],
      use ∅,
      rw [set.mem_sep_iff],
      split,

      apply simplicial_complex_empty_simplex,

      rw [finset.subset_empty],
      apply finset.nonempty.ne_empty,
      rw [←finset.nonempty_coe_sort],
      assumption,
    end)
    (begin
      simp,
      intros s_1 s1_in_X s_nsset_s1 t t_sset_s,
      split,

      apply X.subset_closed s_1;
      assumption,

      rw [finset.not_subset] at *,
      choose x Hx x_nin_s1 using s_nsset_s1,
      use x, split, assumption,
      revert x_nin_s1,
      contrapose,
      simp,
      apply finset.mem_of_subset,
      assumption,
    end)
notation X `\St(` X `, ` s `)` := star_complement X s

instance star_complement.fintype
    (X : simplicial_complex α) [fintype X.simplices]
    (s : finset α) [nonempty s]
    (s_in_X : s ∈ X.simplices)
  : fintype (star_complement X s s_in_X).simplices
:= begin
  simp only[star_complement, simplicial_complex.simplices],

  have H_dec : decidable_pred (λ t : finset α, ¬s ⊆ t), from
  begin
    unfold decidable_pred,
    intro t,
    sorry,
  end,

  apply @set.fintype_sep _ _ _ _ H_dec,
  assumption,
end

lemma star_complement_iso
    (X : simplicial_complex α)
    (Y : simplicial_complex β)
    (s : finset α) [nonempty s]
    (t : finset β) [nonempty t]
    (f : simplicial_map X Y)
    (s_in_X : s ∈ X.simplices)
    (t_in_Y : t ∈ Y.simplices)
    (f_iso : is_simplicial_iso f)
  : finset.image f.map s = t → (X\St(X, s) s_in_X) ≅ (Y\St(Y, t) t_in_Y)
:= sorry

@[simp]
def is_neg_one_sphere
    {X : simplicial_complex α}
    {s : finset α}
    {s_in_X : s ∈ X.simplices}
    (Y : simplicial_complex α)
    (Y_link_X : Y = Lk(X, s) s_in_X)
  : Prop
:= Y = empty_sc

@[simp]
def neg_one_ball
    {X : simplicial_complex α}
    (x : α)
    (x_nin_X : x ∉ vertices X)
  : simplicial_complex α
:= simplicial_complex.mk
    ({{x}, ∅})
    (begin
      rw [set.nonempty_coe_sort, set.nonempty_def],
      use ∅,
      simp,
    end)
    (begin
      simp,
      intros t t_sset_empty,
      rw [finset.subset_empty] at t_sset_empty,
      tauto,
    end)

def is_m_sphere
    (Y : simplicial_complex α) [fintype Y.simplices]
    (m : ℕ)
  : Prop
:= ∃ (X : simplicial_complex α) (s : finset α) (s_in_X : s ∈ X.simplices),
    (Y = Lk(X, s) s_in_X) →
      (finset.card (vertices Y).to_finset = m + 2) ∧
        (Y.simplices = (finset.powerset (vertices Y).to_finset) \ {(vertices Y).to_finset}) ∧
        ¬((vertices Y).to_finset ∈ X.simplices)

lemma m_sphere_iso
    (X Y : simplicial_complex α) [fintype X.simplices]
    (Z W : simplicial_complex β) [fintype Y.simplices]
    (s ∈ X.simplices)
    (t ∈ X.simplices)
    (m : ℕ)
  : is_m_sphere X m → X ≅ Y → is_m_sphere Y m
:= sorry

-- The ball around a simplex.
def m_ball
    (X : simplicial_complex α) [fintype X.simplices]
    (s : finset α)
    (s_in_X : s ∈ X.simplices)
  : simplicial_complex α
:= simplicial_complex.mk
    (finset.powerset (vertices (Lk(X, s) s_in_X)).to_finset)
    (begin
      rw [set.nonempty_coe_sort, set.nonempty_def],
      existsi ∅,
      apply finset.empty_mem_powerset,
    end)
    (begin
      sorry,
    end)
notation `B(` X `, ` s `)` := m_ball X s

instance ball.fintype
    (X : simplicial_complex α) [fintype X.simplices]
    (s : finset α)
    (s_in_X : s ∈ X.simplices)
  : fintype (m_ball X s s_in_X).simplices
:= begin
  simp only[m_ball, simplicial_complex.simplices],
  apply finset_coe.fintype,
end

lemma m_ball_iso
    (X : simplicial_complex α) [fintype X.simplices]
    (Y : simplicial_complex β) [fintype Y.simplices]
    (s : finset α)
    (t : finset β)
    (f : simplicial_map X Y)
    (s_in_X : s ∈ X.simplices)
    (t_in_Y : t ∈ Y.simplices)
    (f_iso : is_simplicial_iso f)
  : finset.image f.map s = t → B(X, s) s_in_X ≅ B(Y, t) t_in_Y
:= sorry

-- The cone of a complex.
@[simp]
def cone
    (X : simplicial_complex α)
    (x : α)
    (x_nin_X : x ∉ vertices X)
  : simplicial_complex (α × ℕ)
:= (neg_one_ball x x_nin_X) ⋆ X
notation `Cone(` X `, ` x `)` := cone X x

instance cone.fintype
    (X : simplicial_complex α) [fintype X.simplices]
    (x : α)
    (x_nin_X : x ∉ vertices X)
  : fintype (Cone(X, x) x_nin_X).simplices
:= begin
  dsimp only[cone, neg_one_ball, simplicial_join, simplicial_complex.simplices],
  sorry,
end

lemma cone_iso
    (X : simplicial_complex α)
    (Y : simplicial_complex β)
    (x : α)
    (y : β)
    (x_nin_X : x ∉ vertices X)
    (y_nin_Y : y ∉ vertices Y)
  : X ≅ Y → Cone(X, x) x_nin_X ≅ Cone(Y, y) y_nin_Y
:= sorry

lemma dim_of_cone
    (X : simplicial_complex α) [fintype X.simplices]
    (x : α)
    (x_nin_X : x ∉ vertices X)
  : dim_of_complex (cone X x x_nin_X) = dim_of_complex X + 1
:= sorry

/-
# Subcomplexes Under Simplicial Join
-/

-- Distributive properties of join over certain subcomplexes.

-- Lemma 2.2 (1), p.7
lemma join_distl_link
    (X Y : simplicial_complex α)
    (s : finset α)
    (s_in_X : s ∈ X.simplices)
  : Y ⋆ (Lk(X, s) s_in_X) ≅ Lk((X ⋆ Y), (s ⊔ₛ ∅)) (by { apply simplicial_join_incl_left, assumption, })
:= begin
  apply simplicial_iso_trans (Y ⋆ (Lk(X, s) s_in_X)) ((Lk(X, s) s_in_X) ⋆ Y),
  apply simplicial_join_comm,

  apply simplicial_iso_preserves_equiv,
  dsimp only[simplicial_join, link, simplicial_complex.simplices],

  rw [set.ext_iff],
  intro x,
  repeat { rw [set.mem_set_of] },

  split,
  { intro H,
    rcases H with ⟨t, Ht, u, Hu, Hx⟩,
    rw [set.mem_sep_iff] at Ht,
    rcases Ht with ⟨Ht, Hst, Hst_empty⟩,
    
    split,
    use t, split, tauto,
    use u, tauto,
    
    split,
    subst Hx,
    rw [simplex_disjoint_distr_union],
    use (s ∪ t), split, tauto,
    use u, split, tauto,
    simp,
    
    subst Hx,
    rw [simplex_disjoint_distr_inter],
    simp, tauto, },
  { intro H,
    rcases H with ⟨Hx, Hx_union, Hsx_empty⟩,
    rcases Hx with ⟨t, Ht, u, Hu, Hx⟩,
    rcases Hx_union with ⟨t', Ht', u', Hu', Hx_union⟩,
    
    subst Hx,
    rw [simplex_disjoint_distr_union, simplex_disjoint_eq_unique] at Hx_union,
    cases Hx_union with Ht' Hu',
    simp at Hu', subst Hu',

    rw [simplex_disjoint_distr_inter, simplex_disjoint_empty] at Hsx_empty,
    cases Hsx_empty with Hst_empty Hu'_trivial,
    
    use t, split,
    rw [set.mem_sep_iff],
    split; try { subst Ht' }; tauto,
    
    use u', tauto, }
end

-- Lemma 2.2 (2), p.7
lemma join_distl_star
    {a : Type*} [decidable_eq a]
    (X Y : simplicial_complex a)
    (s : finset a)
    (s_in_X : s ∈ X.simplices)
  : (Y ⋆ (St(X, s) s_in_X)) ≅ (St((X ⋆ Y), (s ⊔ₛ ∅)) (by { apply simplicial_join_incl_left, assumption }))
:= begin
  apply simplicial_iso_trans (Y ⋆ (St(X, s) s_in_X)) ((St(X, s) s_in_X) ⋆ Y),
  apply simplicial_join_comm,

  apply simplicial_iso_preserves_equiv,
  dsimp only[simplicial_join, star, simplicial_complex.simplices],

  rw [set.ext_iff],
  intro x,
  repeat { rw [set.mem_set_of] },

  split,
  { intro H,
    rcases H with ⟨t, Ht, u, Hu, Hx⟩,
    rw [set.mem_sep_iff] at Ht,
    cases Ht with Ht Hst,
    
    split,
    use t, split, tauto,
    use u, tauto,
    
    subst Hx,
    use (s ∪ t), split, tauto,
    use u,
    split; try { rw [simplex_disjoint_distr_union], simp, }; tauto, },
  { intro H,
    cases H with Hx Hx_union,
    rcases Hx with ⟨t, Ht, u, Hu, Hx⟩,
    rcases Hx_union with ⟨t', Ht', u', Hu', Hx_union⟩,
    
    subst Hx,
    rw [simplex_disjoint_distr_union, simplex_disjoint_eq_unique] at Hx_union,
    cases Hx_union with Ht' Hu',
    simp at Hu',
    subst Ht', subst Hu',
    
    use t, split,
    rw [set.mem_sep_iff]; try { simp }; tauto,
    use u', split; tauto, }
end

-- Lemma 2.2 (3), p.7
lemma join_distl_star_complement
    (X Y : simplicial_complex α)
    (s : finset α) [nonempty s]
    (s_in_X : s ∈ X.simplices)
  : Y ⋆ (star_complement X s s_in_X) ≅ star_complement (X ⋆ Y) (s ⊔ₛ ∅) (by { apply simplicial_join_incl_left, assumption })
:= begin
  apply simplicial_iso_trans (Y ⋆ (star_complement X s s_in_X)) ((star_complement X s s_in_X) ⋆ Y),
  apply simplicial_join_comm,

  apply simplicial_iso_preserves_equiv,
  dsimp only[simplicial_join, star_complement, simplicial_complex.simplices],

  rw [set.ext_iff],
  intro x,
  repeat { rw [set.mem_set_of] },

  split,
  { intro H,
    rcases H with ⟨t, Ht, u, Hu, Hx⟩,
    rw [set.mem_sep_iff] at Ht,
    cases Ht with Ht Hs_not_sset_t,
    
    split,
    use t, split, tauto,
    use u, tauto,
    
    subst Hx,
    rw [simplex_disjoint_subset_unique],
    simp, tauto, },
  { intro H,
    cases H with Hx Hs_not_sset_x,
    rcases Hx with ⟨t, Ht, u, Hu, Hx⟩,
    
    subst Hx,
    rw [simplex_disjoint_subset_unique] at Hs_not_sset_x,
    simp at Hs_not_sset_x,
    
    use t, split,
    rw [set.mem_sep_iff], tauto,
    use u, split; tauto, }
end

-- Lemma 2.3, p.8
lemma join_fact_link
    (X Y : simplicial_complex α)
    (s t : finset α)
    (s_in_X : s ∈ X.simplices)
    (t_in_Y : t ∈ Y.simplices)
  : Lk(X ⋆ Y, s ⊔ₛ t) (by { rw [simplicial_join_sep], tauto }) ≅ Lk(X, s) s_in_X ⋆ Lk(Y, t) t_in_Y
:= begin
  apply simplicial_iso_preserves_equiv,
  dsimp only[link, simplicial_join, simplicial_complex.simplices],

  rw [set.ext_iff],
  intro x,
  repeat { rw [set.mem_set_of] },
  
  split,
  { intros H,
    cases H,
    rcases H_left with ⟨s', Hs', t', Ht', Hx⟩,
    cases H_right with H_left H_inter,
    rcases H_left with ⟨s'', Hs'', t'', Ht'', H_union⟩,
    
    subst Hx,
    rw [simplex_disjoint_distr_inter, simplex_disjoint_empty] at H_inter,
    rw [simplex_disjoint_distr_union, simplex_disjoint_eq_unique] at H_union,
    cases H_union with H_s_union H_t_union,
    subst H_s_union, subst H_t_union,
    
    use s', split,
    rw [set.mem_sep_iff],
    split; tauto,
    
    use t',
    rw [set.mem_sep_iff],
    split; tauto, },
  { intros H,
    rcases H with ⟨s', Hs', t', Ht', Hx⟩,
    rw [set.mem_sep_iff] at Hs' Ht',

    split,
    { use s', split, tauto,
      use t', tauto, },
    { use (s ∪ s'), split, tauto,
      use (t ∪ t'), split, tauto,
      
      subst Hx,
      rw [simplex_disjoint_distr_union],
      
      subst Hx,
      rw [simplex_disjoint_distr_inter, simplex_disjoint_empty],
      tauto, } },
end

-- Lemma 2.4 (1), p.8
lemma join_distr_union_left
    (X Y Z : simplicial_complex α)
  : X ⋆ (Y ∪ Z) ≅ (X ⋆ Y) ∪ (X ⋆ Z)
:= begin
  apply simplicial_iso_preserves_equiv,
  dsimp only[simplicial_join, simplicial_union, simplicial_complex.simplices],

  rw [set.ext_iff],
  intro x,
  repeat { rw [set.mem_set_of] },

  split,
  { intro H,
    rcases H with ⟨s, Hs, t, Ht, Hx⟩,
    
    rw [←set.set_of_or, set.mem_set_of],
    rw [set.mem_union] at Ht,
    
    destruct Ht,
    
    intro Hy,
    left,
    use s, split, tauto,
    use t, tauto,
    
    intro Hz,
    right,
    use s, split, tauto,
    use t, tauto, },
  { intro H,
    rw [←set.set_of_or, set.mem_set_of] at H,
    destruct H,
    
    intro Hy,
    rcases Hy with ⟨s, Hs, t, Ht, Hx⟩,
    use s, split, tauto,
    use t, rw [set.mem_union], tauto,
    
    intro Hz,
    rcases Hz with ⟨s, Hs, t, Ht, Hx⟩,
    use s, split, tauto,
    use t, rw [set.mem_union], tauto, }
end

-- Lemma 2.4 (2), p.8
lemma join_distr_inter_left
    (X Y Z : simplicial_complex α)
  : X ⋆ (Y ∩ Z) ≅ (X ⋆ Y) ∩ (X ⋆ Z)
:= begin
  apply simplicial_iso_preserves_equiv,
  dsimp only[simplicial_join, simplicial_inter, simplicial_complex.simplices],

  rw [set.ext_iff],
  intro x,
  repeat { rw [set.mem_set_of] },

  split,
  { intro H,
    rcases H with ⟨s, Hs, t, Ht, Hx⟩,
    
    rw [←set.set_of_and, set.mem_set_of],
    rw [set.mem_inter_iff] at Ht,
    cases Ht with Hy Hz,
    
    split,
    
    use s, split, tauto,
    use t, tauto,
    
    use s, split, tauto,
    use t, tauto, },
  { intro H,
    rw [←set.set_of_and, set.mem_set_of] at H,
    cases H with Hy Hz,
    
    rcases Hy with ⟨sy, Hsy, ty, Hty, Hxy⟩,
    rcases Hz with ⟨sz, Hsz, tz, Htz, Hxz⟩,
    subst Hxy,
    rw [simplex_disjoint_eq_unique] at Hxz,
    cases Hxz with Hsz Htz,
    subst Hsz, subst Htz,
    
    use sz, split, tauto,
    use tz, rw [set.mem_inter_iff], tauto, }
end

/-
# Properties of Links
-/

-- Lemma 3.5, p.14
lemma link_of_face_complement
    (X : simplicial_complex α)
    (s t : finset α)
    (s_in_X : s ∈ X.simplices)
    (t_sset_s : t ⊆ s)
  : Lk(X, s) s_in_X ≅ Lk(Lk(X, t) (by { apply X.subset_closed s; assumption }), s \ t) (by { sorry })
:= sorry