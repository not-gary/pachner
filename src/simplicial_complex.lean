/-
Copyright (c) 2022 Clara Löh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.txt.
Author: Clara Löh.
-/

import tactic          -- standard proof tactics
import data.set.basic        -- basics on sets
import data.set.finite -- basics on finite sets
import data.finset.basic     -- type-level finite sets

open_locale big_operators

variables {α : Type*}

/- 
# Simplicial complexes
-/

/- A simplicial complex is a set of finite sets 
   that is closed under taking subsets;
   we use finsets to model these finite sets
-/   

@[simp]
def is_subset_closed
    (S : set (finset α))
:= ∀ s ∈ S, ∀ t, t ⊆ s → t ∈ S    

structure simplicial_complex (α : Type*)
:= mk :: (simplices : set (finset α))
         (nonempty : nonempty simplices)
         (subset_closed : is_subset_closed simplices)

lemma eq_simplices_subset_closed
    (S T : set (finset α))
  : S = T → is_subset_closed S → is_subset_closed T
:=
begin
  intros S_eq_T subset_closed_S,
  subst S_eq_T,
  exact subset_closed_S,
end

lemma simplicial_complex_empty_simplex
    (X : simplicial_complex α)
  : ∅ ∈ X.simplices
:= begin
  have H : nonempty X.simplices, by apply X.nonempty,
  rw [set.nonempty_coe_sort, set.nonempty_def] at H,
  choose s Hs using H,
  apply X.subset_closed s; tauto,
end

-- The empty simplicial complex
def empty_sc 
    {a : Type*}
  : simplicial_complex a
:= simplicial_complex.mk  
     ({∅} : set (finset a))
     (by { rw [set.nonempty_coe_sort, set.nonempty_def], use ∅, simp, })
     (begin
        unfold is_subset_closed,
        intros s H_empty t t_sset_s,
        rw [set.mem_singleton_iff] at H_empty,
        rw [H_empty, finset.subset_empty] at t_sset_s,
        tauto,
      end)

lemma empty_type_implies_empty_complex
    {α : Type*} [is_empty α]
  : ∀ (X : simplicial_complex α), X.simplices = {∅}
:= begin
  intro X,
  rw [set.eq_singleton_iff_unique_mem],
  split,

  apply simplicial_complex_empty_simplex,

  intros s s_in_X,
  apply finset.eq_empty_of_is_empty,
end

instance simplex_image.nonempty
    {β : Type*} [decidable_eq β]
    (s : finset α) [nonempty s]
    (f : α → β)
  : nonempty ↥(finset.image f s)
:= begin
  apply finset.nonempty.coe_sort,
  apply finset.nonempty.image,
  apply finset.nonempty_coe_sort.mp,
  assumption,
end

/- The set of vertices of a simplicial complex is 
   the set of all elements 
   that occur in at least one of the simplices.
-/
def vertices 
    (X : simplicial_complex α)
  : set α
:= ⋃ (s : finset α) (H : s ∈ X.simplices), s

lemma vertices_set_of
    (X : simplicial_complex α)
  : vertices X = { x : α | ∃ s ∈ X.simplices, x ∈ s }
:= begin
  simp only [vertices, set.ext_iff, set.mem_Union, set.mem_set_of],
  intro x,
  refl,
end

instance vertices.fintype
    [decidable_eq α]
    (X : simplicial_complex α) [fintype X.simplices]
  : fintype (vertices X)
:= begin
  unfold vertices,
  apply set.fintype_bUnion,
  intros s s_in_X,
  apply finset_coe.fintype,
end

lemma simplex_subset_vertices
    (X : simplicial_complex α)
    (s : finset α)
  : s ∈ X.simplices → ↑s ⊆ vertices X
:= begin
  intro s_in_X,
  rw [vertices_set_of, set.subset_def],
  intros x x_in_s,
  rw [set.mem_set_of],

  use s, split; assumption,
end

instance vertices.fintype_converse
    [decidable_eq α]
    (X : simplicial_complex α)
    [X_dec : decidable_pred (λ s, s ∈ X.simplices)]
  : fintype (vertices X) → fintype X.simplices
:= begin
  intro fin_vert_X,
  apply set.fintype_subset ↑(finset.powerset (@set.to_finset _ (vertices X) fin_vert_X)),

  rw [set.subset_def],
  intros s s_in_X,
  rw [finset.mem_coe, finset.mem_powerset, set.subset_to_finset],
  apply simplex_subset_vertices,
  assumption,

  apply finset.fintype_coe_sort,
  assumption,
end

lemma vertex_iff_singleton
    (X : simplicial_complex α)
    (x : α)
  : x ∈ vertices X ↔ {x} ∈ X.simplices
:= begin
  split,

  intro x_vert,
  simp only[vertices, set.mem_Union] at x_vert,
  choose s Hs x_in_s using x_vert,
  apply X.subset_closed s,
  assumption,
  rw [finset.subset_iff],
  intros y y_eq_x,
  rw [finset.mem_singleton] at y_eq_x,
  rw [y_eq_x] at *,
  tauto,

  intro x_simpl,
  simp only[vertices, set.mem_Union],
  use {x},
  split,
  assumption,
  rw [finset.mem_coe, finset.mem_singleton],
end

lemma simplex_mem_is_vertex
    (X : simplicial_complex α)
    (s : finset α)
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_in_s : x ∈ s)
  : x ∈ vertices X
:= begin
  rw [vertices_set_of, set.mem_set_of],
  use s, split; assumption,
end

lemma vertex_iff_in_simplex
    (X : simplicial_complex α)
    (x : α)
  : x ∈ vertices X ↔ ∃ (s ∈ X.simplices), x ∈ s
:= begin
  rw [vertices_set_of, set.mem_set_of],
end

lemma empty_sc_vertices
  : vertices (@empty_sc α) = ∅
:= begin
  rw [vertices_set_of, set.eq_empty_iff_forall_not_mem],
  intro x,
  simp only [set.mem_set_of, not_exists, empty_sc, set.mem_singleton_iff],
  intros s s_empty,
  rw [s_empty],
  apply set.not_mem_empty x,
end

lemma vertices_congr
    (X Y : simplicial_complex α)
  : X.simplices = Y.simplices → vertices X = vertices Y
:= begin
  intros X_eq_Y,
  simp only [vertices_set_of, X_eq_Y],
end

-- The simplex generated by a finset
@[simp]
def simplex
    (V : finset α)
  : simplicial_complex α
:= simplicial_complex.mk 
    (finset.powerset V)
    (begin
      rw [set.nonempty_coe_sort],
      apply finset.powerset_nonempty,
    end)
    (by { simp, tauto })

instance simplex.fintype
    (s : finset α)
  : fintype (simplex s).simplices
:= begin
  simp only [simplex, simplicial_complex.simplices],
  apply finset_coe.fintype,
end

instance simplex.finite
    (s : finset α)
  : finite (simplex s).simplices
:= begin
  simp only [simplex, simplicial_complex.simplices],
  rw [set.finite_coe_iff],
  apply set.finite.intro,
  apply finset_coe.fintype,
end

lemma simplex_vertices
    (s : finset α)
  : vertices (@simplex α s) = s
:= begin
  rw [vertices_set_of],
  simp only [set.ext_iff, set.mem_set_of, simplex, set.mem_singleton_iff],
  intro y,
  split,

  intro y_in_union,
  choose t t_in_simplex y_in_t using y_in_union,
  simp only [finset.mem_coe, finset.mem_powerset, finset.subset_iff] at t_in_simplex,
  specialize t_in_simplex y_in_t,
  rw [finset.mem_coe],
  assumption,

  intro y_in_s,
  use s, split,
  rw [finset.mem_coe],
  apply finset.mem_powerset_self,
  rw [finset.mem_coe] at y_in_s,
  assumption,
end

-- The standard n-simplex is generated by {0,...,n}
@[simp]
def std_simplex
    (n : ℕ)
  : simplicial_complex ℕ
:= simplex (finset.range (n + 1))

/-
# Dimension of simplices and simplicial complexes
-/

-- The dimension of a simplex is just its cardinality - 1. 
@[simp]
def dim
    (s : finset α)
  : ℤ
:= finset.card s - 1

@[simp]
def is_k_simplex
    (s : finset α)
    (k : ℕ)
:= dim s = k

#eval dim (finset.range 5) -- 4
#eval dim (finset.range 0) -- -1

-- A simplicial complex has dimension n 
-- if n is the maximal dimension of all simplices. 
@[simp]
def has_dimension_leq
    (X : simplicial_complex α)
    (n : ℕ)
:= ∀ s ∈ X.simplices, dim s ≤ n    

@[simp]
def has_dimension_geq
    (X : simplicial_complex α)
    (n : ℕ)
:= ∃ s ∈ X.simplices, dim s ≥ n    

@[simp]
def has_dimension
    (X : simplicial_complex α)
    (n : ℕ)
:= has_dimension_leq X n ∧ has_dimension_geq X n    

-- The standard n-simplex has dimension n
lemma dim_std_simplex
    (n : ℕ)
  : has_dimension (std_simplex n) n
:= begin
  let Dn := std_simplex n,

  -- dim ≤ n
  have dim_leq_n : has_dimension_leq Dn n, from
  begin
    assume s : finset nat,
    assume s_in_Dn : s ∈ Dn.simplices,

    -- By definition, s ⊆ {0,...,n}.
    have s_sub_n : s ⊆ finset.range (n+1), 
         by exact finset.mem_powerset.mp s_in_Dn,
    
    -- Thus, s has cardinality at most n + 1.
    have card_s_leq_n1 : finset.card s ≤ n + 1, from
    begin
      calc finset.card s ≤ finset.card (finset.range (n+1)) 
                         : by exact finset.card_le_of_subset s_sub_n
                     ... ≤ n + 1 
                         : by finish,
    end,

    -- Whence, s has dimension at most n
    show dim s ≤ n, from
    begin      
      calc dim s = finset.card s - 1 : by simp only [dim]
             ... ≤ n + 1 - 1         : by linarith 
             ... ≤ n                 : by linarith,
    end,
  end,

  -- dim ≥ n
  have dim_geq_n : has_dimension_geq Dn n, from
  begin
    -- We use {0,...,n} as a witness
    let s := finset.range (n+1),
    use s,

    have s_in_Dn : s ∈ (std_simplex n).simplices, 
         by simp,

    have dim_s : dim s ≥ n, 
         by finish,

    show _, by exact ⟨s_in_Dn, dim_s⟩, -- alternatively: and.intro ...
  end,

  show _, by exact ⟨dim_leq_n, dim_geq_n⟩,
end

lemma dim_geq_zero_iff_nonempty
    (s : finset α)
  : 0 ≤ dim s ↔ s ≠ ∅
:= begin
  unfold dim,
  rw [ne.def, ←finset.card_eq_zero],
  split,
  

  contrapose,
  simp only[not_not],
  intro s_card_zero,
  rw [s_card_zero],
  omega,

  intro s_card_ne_zero,
  have s_card_pos : s.card > 0, by omega,
  linarith,
end

lemma dim_neg_one_iff_empty
    (s : finset α)
  : dim s = -1 ↔ s = ∅
:= begin
  unfold dim,
  rw [←finset.card_eq_zero],
  split,

  intro s_card_neg_one,
  simp only [sub_eq_neg_self, nat.cast_eq_zero] at s_card_neg_one,
  assumption,

  intro s_card_zero,
  rw [s_card_zero],
  simp,
end

lemma dim_zero_iff_vertex
    (s : finset α)
  : dim s = 0 ↔ ∃ x : α, s = {x}
:= begin
  unfold dim,
  split,

  intro s_card_minus_one,
  have s_card_one : s.card = 1, by linarith,
  rw [←finset.card_eq_one],
  assumption,

  intro exists_x,
  rw [←finset.card_eq_one] at exists_x,
  rw [exists_x],
  simp,
end

-- TODO: Do we want a nonempty result on t as well?
lemma simplex_decomp [decidable_eq α]
    (s : finset α)
  : 0 < dim s → ∃ (x ∈ s) (t : finset α), t = s \ {x}
:= begin
  unfold dim,
  intro s_card_pos,

  have s_card_gt_one : 1 < s.card, by linarith,
  rw [finset.one_lt_card] at s_card_gt_one,
  choose a a_in_s b b_in_s a_ne_b using s_card_gt_one,

  use a, split, assumption,
  use (s \ {a}),
end

lemma simplex_decomp_dim [decidable_eq α]
    (s : finset α)
    (x : α)
    (x_in_s : x ∈ s)
  : 0 < dim s → 0 ≤ dim (s \ {x})
:= begin
  unfold dim,
  intro s_card_pos,

  have s_card_gt_one : 1 < s.card, by linarith,
  rw [finset.card_sdiff, finset.card_singleton],
  apply int.sub_nonneg_of_le,
  rw [int.coe_nat_sub, int.coe_nat_one, int.le_sub_one_iff],

  rw [nat.one_lt_cast],
  assumption,

  apply le_of_lt,
  assumption,

  rw [finset.singleton_subset_iff],
  assumption,
end

lemma simplex_decomp_dim_eq [decidable_eq α]
    (s : finset α)
    (x : α)
    (x_in_s : x ∈ s)
  : 0 < dim s → dim (s \ {x}) = dim s - 1
:= begin
  unfold dim,
  intro s_card_pos,
  rw [finset.card_sdiff, finset.card_singleton],
  rw [sub_left_inj, int.coe_nat_sub, int.coe_nat_one],

  linarith,

  rw [finset.singleton_subset_iff],
  assumption,
end

-- The dimension of a finite complex is the maximum
-- dimension of its simplices.

-- TODO: Remove or make a lemma for equivalence to below.
@[simp]
def dim_of_complex'
    (X : simplicial_complex α) [fintype X.simplices]
  : int
:= match finset.max (finset.bUnion X.simplices.to_finset (λ s, {dim s})) with
    | option.none := -1   -- degenerate ∅ case
    | option.some z := z
  end

instance dim_set.fintype
    (X : simplicial_complex α) [fintype X.simplices]
  : fintype (finset.image dim X.simplices.to_finset)
:= begin
  apply set.fintype_mem_finset,
end

lemma dim_set_nonempty
    (X : simplicial_complex α) [fintype X.simplices]
  : (finset.image dim X.simplices.to_finset).nonempty
:= begin
  apply finset.nonempty.image,
  unfold finset.nonempty,
  use ∅,
  rw [←finset.mem_coe, set.coe_to_finset],
  apply simplicial_complex_empty_simplex,
end

@[simp]
def dim_of_complex
    (X : simplicial_complex α) [fintype X.simplices]
  : ℤ
:= finset.max' (finset.image dim X.simplices.to_finset) (dim_set_nonempty X)

/-
# Disjointness of simplicial complexes.
-/
section disjoint

variable [decidable_eq α]

-- Define when two simplicial complexes are disjoint via disjointness of vertices.
def disjoint_complexes
    (X Y : simplicial_complex α)
  : Prop
:= disjoint (vertices X) (vertices Y)

-- Indeed, this implies simplices are disjoint, too.
lemma disjoint_simplices_iff_disj_vertices
    (X Y : simplicial_complex α)
    (s t : finset α)
    (s_in_X : s ∈ X.simplices)
    (t_in_Y : t ∈ Y.simplices)
  : disjoint_complexes X Y → disjoint s t
:= begin
  simp only[disjoint_complexes, vertices],
  intro XY_disj,

  rw [set.disjoint_iff_inter_eq_empty, ←set.subset_empty_iff] at XY_disj,
  rw [finset.disjoint_iff_inter_eq_empty, ←finset.subset_empty, ←finset.coe_subset, finset.coe_empty, finset.coe_inter],

  apply @set.subset.trans _ _
    ((⋃ (s : finset α) (H : s ∈ X.simplices), ↑s) ∩ ⋃ (s : finset α) (H : s ∈ Y.simplices), ↑ s),

  apply set.inter_subset_inter;
  apply set.subset_bUnion_of_mem; assumption,
  assumption,
end

-- Disjoint singletons are also disjoint.
lemma disjoint_singleton
    (X : simplicial_complex α)
    (x : α)
  : x ∉ vertices X → disjoint_complexes X (simplex {x})
:= begin
  simp only [disjoint_complexes, simplex_vertices {x}],
  intro x_nin_X,
  
  rw [set.disjoint_iff_inter_eq_empty, finset.coe_singleton, set.inter_singleton_eq_empty],
  assumption,
end

end disjoint

/-
# Operators on simplicial complexes.
-/

section operators

variables [decidable_eq α]

@[simp]
def simplicial_union
    (X Y : simplicial_complex α)
  : simplicial_complex α
:= simplicial_complex.mk
    (X.simplices ∪ Y.simplices)
    (begin
      rw [set.nonempty_coe_sort],
      rw [set.union_nonempty],
      left,
      rw [←set.nonempty_coe_sort],
      apply X.nonempty,
    end)
    (begin
      unfold is_subset_closed,
      intros s s_in_XY t t_sset_s,
      rw [set.mem_union] at *,
      cases s_in_XY with s_in_X s_in_Y,

      left,
      apply X.subset_closed s;
      assumption,

      right,
      apply Y.subset_closed s;
      assumption,
    end)

@[reducible]
instance : has_union (simplicial_complex α) := ⟨simplicial_union⟩

instance simplicial_union.fintype
    (X Y : simplicial_complex α) [fintype X.simplices] [fintype Y.simplices]
  : fintype (X ∪ Y).simplices
:= begin
  simp only [simplicial_union],
  apply set.fintype_union,
end

lemma simplicial_union_assoc
    (X Y Z : simplicial_complex α)
  : (X ∪ Y) ∪ Z = X ∪ (Y ∪ Z)
:= begin
  simp,
  rw [set.union_assoc],
end

lemma simplicial_union_comm
    (X Y : simplicial_complex α)
  : X ∪ Y = Y ∪ X
:= begin
  simp,
  rw [set.union_comm],
end

lemma simplicial_union_simplices
    (X Y : simplicial_complex α)
  : (X ∪ Y).simplices = X.simplices ∪ Y.simplices
:= begin
  simp only[simplicial_union],
end

lemma simplicial_union_dim
    (X Y : simplicial_complex α) [fintype X.simplices] [fintype Y.simplices]
  : dim_of_complex (X ∪ Y) = max (dim_of_complex X) (dim_of_complex Y)
:= begin
  unfold dim_of_complex,
  apply le_antisymm,

  { apply finset.max'_le,
    intros y y_in_img,
    simp only [finset.mem_image, simplicial_union, set.mem_union, set.mem_to_finset] at y_in_img,
    choose s s_in_union dim_s_y using y_in_img,
    rw [le_max_iff],
    cases s_in_union with s_in_X s_in_Y,
    
    left,
    apply finset.le_max',
    rw [finset.mem_image],
    use s, split,
    rw [set.mem_to_finset],
    assumption,
    assumption,
    
    right,
    apply finset.le_max',
    rw [finset.mem_image],
    use s, split,
    rw [set.mem_to_finset],
    assumption,
    assumption, },

  { rw [max_le_iff],
    split,
    
    rw [finset.max'_le_iff],
    intros y y_in_img,
    simp only [finset.mem_image, set.mem_to_finset] at y_in_img,
    choose s s_in_X dim_s_y using y_in_img,
    apply finset.le_max',
    simp only [finset.mem_image, simplicial_union, set.mem_union, set.mem_to_finset],
    use s, split,
    left, assumption,
    assumption,
    
    rw [finset.max'_le_iff],
    intros y y_in_img,
    simp only [finset.mem_image, set.mem_to_finset] at y_in_img,
    choose s s_in_Y dim_s_y using y_in_img,
    apply finset.le_max',
    simp only [finset.mem_image, simplicial_union, set.mem_union, set.mem_to_finset],
    use s, split,
    right, assumption,
    assumption, },
end

@[simp]
def simplicial_inter
    (X Y : simplicial_complex α)
  : simplicial_complex α
:= simplicial_complex.mk
    (X.simplices ∩ Y.simplices)
    (begin
      rw [set.nonempty_coe_sort],
      rw [set.inter_nonempty],
      use ∅,
      split;
      apply simplicial_complex_empty_simplex,
    end)
    (begin
      unfold is_subset_closed,
      intros s s_in_XY t t_sset_s,
      rw [set.mem_inter_iff] at *,
      cases s_in_XY with s_in_X s_in_Y,
      split,

      apply X.subset_closed s;
      assumption,

      apply Y.subset_closed s;
      assumption,
    end)
    
@[reducible]
instance : has_inter (simplicial_complex α) := ⟨simplicial_inter⟩

lemma simplicial_inter_assoc
    (X Y Z : simplicial_complex α)
  : (X ∩ Y) ∩ Z = X ∩ (Y ∩ Z)
:= begin
  simp,
  rw [set.inter_assoc],
end

lemma simplicial_inter_comm
    (X Y : simplicial_complex α)
  : X ∩ Y = Y ∩ X
:= begin
  simp,
  rw [set.inter_comm],
end

end operators

/-
# Subcomplexes
-/

-- Define a subcomplex in the usual way:
-- i.e., simplices are contained in the other.
def is_subcomplex
    (X Y : simplicial_complex α)
  : Prop
:= X.simplices ⊆ Y.simplices

@[reducible]
instance : has_subset (simplicial_complex α) := ⟨is_subcomplex⟩

lemma is_subcomplex_vertex
    (X Y : simplicial_complex α)
    (Y_subcomp_X : Y ⊆ X)
  : ∀ x : α, x ∈ vertices Y → x ∈ vertices X
:= begin
  simp only [vertices],
  simp only [simplicial_complex.has_subset, is_subcomplex, set.subset_def] at Y_subcomp_X,

  intros y y_in_vert_Y,
  simp only [set.mem_Union] at y_in_vert_Y ⊢,
  choose s Hs y_in_s using y_in_vert_Y,
  specialize Y_subcomp_X s Hs,

  use s, split, apply Y_subcomp_X,
  apply y_in_s,
end

lemma is_subcomplex_vertices
    (X Y : simplicial_complex α)
    (Y_subcomp_X : Y ⊆ X)
  : vertices Y ⊆ vertices X
:= begin
  simp only [set.subset_def],
  apply is_subcomplex_vertex X Y Y_subcomp_X,
end

-- Equivalent, useful definition of a simplex as a subcomplex of the original.
def is_simplex
    (s : finset α)
    (X : simplicial_complex α)
  : Prop
:= (simplex s) ⊆ X

@[reducible]
instance : has_mem (finset α) (simplicial_complex α) := ⟨is_simplex⟩

lemma simplex_iff_subcomplex_mem
    (X : simplicial_complex α)
    (s : finset α)
  : s ∈ X.simplices ↔ (simplex s) ⊆ X
:= begin
  split,

  intro s_in_X_simpl,
  simp only[is_subcomplex, simplex],
  rw [set.subset_def],
  intros x x_in_s_power,
  apply X.subset_closed s,
  assumption,
  rw [finset.mem_coe, finset.mem_powerset] at x_in_s_power,
  assumption,

  intro s_simpl_X,
  simp only[is_subcomplex, simplex] at s_simpl_X,
  rw [set.subset_def] at s_simpl_X,
  specialize s_simpl_X s,
  rw [finset.mem_coe] at s_simpl_X,
  specialize s_simpl_X (finset.mem_powerset_self s),
  assumption,
end

-- This is, in fact, equivalent to our definition.
lemma simplex_iff_subcomplex
    (X : simplicial_complex α)
    (s : finset α)
  : s ∈ X.simplices ↔ s ∈ X
:= begin
  simp only [is_simplex],
  apply simplex_iff_subcomplex_mem,
end

lemma simplicial_union_eq_left_iff_subcomplex
    (X Y : simplicial_complex α) [decidable_eq α]
  : (X ∪ Y).simplices = X.simplices ↔ Y ⊆ X
:= begin
  simp only [simplicial_union, is_subcomplex],
  apply set.union_eq_left_iff_subset,
end

lemma simplicial_union_eq_right_iff_subcomplex
    (X Y : simplicial_complex α) [decidable_eq α]
  : (X ∪ Y).simplices = Y.simplices ↔ X ⊆ Y
:= begin
  simp only [simplicial_union, is_subcomplex],
  apply set.union_eq_right_iff_subset,
end

lemma subcomplex_simplicial_union_left_simplices
    [decidable_eq α]
    (X Y : simplicial_complex α)
  : ∀ s : finset α, s ∈ X.simplices → s ∈ (X ∪ Y).simplices
:= begin
  apply set.subset_union_left,
end

lemma subcomplex_simplicial_union_left
    [decidable_eq α]
    (X Y : simplicial_complex α)
  : X ⊆ X ∪ Y
:= begin
  simp only [is_subcomplex, simplicial_union],
  apply set.subset_union_left,
end

lemma subcomplex_simplicial_union_right_simplices
    [decidable_eq α]
    (X Y : simplicial_complex α)
  : ∀ s : finset α, s ∈ Y.simplices → s ∈ (X ∪ Y).simplices
:= begin
  apply set.subset_union_right,
end

lemma subcomplex_simplicial_union_right
    (X Y : simplicial_complex α) [decidable_eq α]
  : Y ⊆ X ∪ Y
:= begin
  simp only [is_subcomplex, simplicial_union],
  apply set.subset_union_right,
end

lemma simplex_if_in_subcomplex
    (X Y : simplicial_complex α)
    (s : finset α)
  : s ∈ X.simplices → X ⊆ Y → s ∈ Y.simplices
:= begin
  intros s_in_X X_sub_Y,
  simp only [is_subcomplex, set.subset_def] at X_sub_Y,
  specialize X_sub_Y s s_in_X,
  assumption,
end

lemma subcomplex_simplicial_inter_left_simplices
    [decidable_eq α]
    (X Y : simplicial_complex α)
  : ∀ s : finset α, s ∈ (X ∩ Y).simplices → s ∈ X.simplices
:= begin
  apply set.inter_subset_left,
end

lemma subcomplex_simplicial_inter_left
    [decidable_eq α]
    (X Y : simplicial_complex α)
  : X ∩ Y ⊆ X
:= begin
  simp only [is_subcomplex, simplicial_inter],
  apply set.inter_subset_left,
end

lemma subcomplex_simplicial_inter_right_simplices
    [decidable_eq α]
    (X Y : simplicial_complex α)
  : ∀ s : finset α, s ∈ (X ∩ Y).simplices → s ∈ Y.simplices
:= begin
  apply set.inter_subset_right,
end

lemma subcomplex_simplicial_inter_right
    [decidable_eq α]
    (X Y : simplicial_complex α)
  : X ∩ Y ⊆ Y
:= begin
  simp only [is_subcomplex, simplicial_inter],
  apply set.inter_subset_right,
end

lemma singleton_inter_eq_empty_iff_not_mem
    [decidable_eq α]
    {s : finset α} {a : α}
  : {a} ∩ s = ∅ ↔ a ∉ s
:= begin
  simp only [finset.eq_empty_iff_forall_not_mem, finset.mem_inter, not_and],
  split,

  intros as_disj,
  specialize as_disj a (by { apply finset.mem_singleton_self, }),
  assumption,

  intros a_nin_s x x_in_a,
  rw [finset.mem_singleton] at x_in_a,
  rw [x_in_a],
  assumption,
end