/-
Copyright (c) 2022 Clara Löh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.txt.
Author: Clara Löh.
-/

import tactic          -- standard proof tactics
import data.set.basic        -- basics on sets
import data.set.finite -- basics on finite sets
import data.finset.basic     -- type-level finite sets
import .simplicial_complex -- basics on simplicial complexes

variables {α β γ : Type*}

/-
# Simplicial maps
-/

section simplicial_map

variable [decidable_eq β]

/- Simplicial maps are maps between the underlying base types 
   that map simplices to simplices.
-/   
@[simp]
def is_simplicial_map
    (X : simplicial_complex α)
    (Y : simplicial_complex β)
    (f : α → β)
:= ∀ s, s ∈ X.simplices → finset.image f s ∈ Y.simplices    

structure simplicial_map
   (X : simplicial_complex α) 
   (Y : simplicial_complex β)
:= mk :: (map : α → β)
         (is_simplicial : is_simplicial_map X Y map)

lemma simplicial_map_restrict_is_simplicial
    (X Y : simplicial_complex α)
    (Z : simplicial_complex β)
    (f : simplicial_map X Z)
  : Y ⊆ X → is_simplicial_map Y Z f.map
:= begin
  simp only [is_simplicial_map, is_subcomplex],
  intros Y_sub_X s s_in_Y,
  simp only [set.subset_def] at Y_sub_X,
  specialize Y_sub_X s s_in_Y,
  apply f.is_simplicial,
  assumption,
end

def simplicial_map.restrict
    {X Y : simplicial_complex α}
    {Z : simplicial_complex β}
    (f : simplicial_map X Z)
    (Y_sub_X : Y ⊆ X)
  : simplicial_map Y Z
:= simplicial_map.mk f.map (simplicial_map_restrict_is_simplicial X Y Z f Y_sub_X)

def simplicial_map_lift
    {X : simplicial_complex α}
    {Y : simplicial_complex β}
    (f : simplicial_map X Y)
  : finset α → finset β
:= λ s : finset α, finset.image f.map s

def simplicial_image
    (X : simplicial_complex α)
    (f : α → β)
  : simplicial_complex β
:= simplicial_complex.mk
    ({(finset.image f s) | s ∈ X.simplices})
    (begin
      rw [set.nonempty_coe_sort, set.nonempty_def],
      use ∅,
      rw [set.mem_set_of],
      use ∅,
      split,
      apply simplicial_complex_empty_simplex,
      apply finset.image_empty,
    end)
    (begin
      simp only[is_subset_closed],
      intros s s_in_img t t_sset_s,
      rw [set.mem_set_of] at *,
      choose u Hu u_img using s_in_img,

      rw [←u_img, ←finset.coe_subset, finset.coe_image, finset.subset_image_iff] at t_sset_s,
      choose v v_sset_u v_img using t_sset_s,

      use v, split,
      apply X.subset_closed u,
      assumption,

      rw [←finset.coe_subset],
      assumption,
      assumption,
    end)

lemma map_is_simplicial_onto_image
    (X : simplicial_complex α)
    (f : α → β)
  : is_simplicial_map X (simplicial_image X f) f
:= begin
  unfold is_simplicial_map,
  intros s s_in_X,
  simp only[simplicial_image, set.mem_set_of],
  use s, split; tauto,
end

def simplicial_map.onto_image
    {X : simplicial_complex α}
    {Z : simplicial_complex β}
    (f : simplicial_map X Z)
  : simplicial_map X (simplicial_image X f.map)
:= simplicial_map.mk f.map (map_is_simplicial_onto_image X f.map)

lemma simplicial_image_vertices
    (X : simplicial_complex α)
    (f : α → β)
  : vertices (simplicial_image X f) = f '' (vertices X)
:= begin
  simp only [vertices_set_of, simplicial_image, set.image, set.ext_iff, set.mem_set_of],
  intro y,
  split,

  intro y_in_vert_img,
  choose t t_in_img y_in_t using y_in_vert_img,
  choose s s_in_X fs_eq_t using t_in_img,
  rw [←fs_eq_t, finset.mem_image] at y_in_t,
  choose x x_in_s fx_eq_y using y_in_t,
  use x, split,
  use s, split; assumption,
  assumption,

  intro y_in_img_vert,
  choose x x_in_X fx_eq_y using y_in_img_vert,
  choose s s_in_X x_in_s using x_in_X,
  use (finset.image f s), split,
  use s, split,
  assumption,
  refl,
  rw [←fx_eq_y],
  apply finset.mem_image_of_mem,
  assumption,
end

notation `⟨`f `, ` X `⟩` := @simplicial_map.mk _ _ _ X (simplicial_image X f) f (map_is_simplicial_onto_image X f)

lemma simplicial_image_is_lift_image
    (X : simplicial_complex α)
    (f : α → β)
  : (simplicial_image X f).simplices = (simplicial_map_lift ⟨f, X⟩) '' X.simplices
:= begin
  simp only [simplicial_image, simplicial_map_lift, set.ext_iff],
  intro s,
  split,

  intro s_in_img,
  simp only [set.mem_set_of] at s_in_img,
  choose t t_in_X ft_eq_s using s_in_img,
  simp only [set.mem_image],
  use t, split; assumption,

  intro s_in_lift,
  simp only [set.mem_image] at s_in_lift,
  choose t t_in_X ft_eq_s using s_in_lift,
  simp only [set.mem_set_of],
  use t, split; assumption,
end

lemma simplicial_image_union
    (X Y : simplicial_complex α) [decidable_eq α]
    (f : α → β)
  : (simplicial_image (X ∪ Y) f).simplices = (simplicial_image X f).simplices ∪ (simplicial_image Y f).simplices
:= begin
  simp only [simplicial_image_is_lift_image, simplicial_map_lift, simplicial_union, set.image, set.ext_iff, set.mem_union, set.mem_set_of],
  intro t,
  split,

  intro t_in_img_union,
  choose s s_in_XY fs_eq_t using t_in_img_union,
  cases s_in_XY with s_in_X s_in_Y,

  left, use s, split; assumption,
  right, use s, split; assumption,

  intro t_in_union_img,
  cases t_in_union_img with t_in_left t_in_right,

  choose s s_in_X fs_eq_t using t_in_left,
  use s, split,
  left, assumption,
  assumption,

  choose s s_in_Y fs_eq_t using t_in_right,
  use s, split,
  right, assumption,
  assumption,
end

end simplicial_map

/-
# Simplicial maps on vertices
-/

section vertices

variables [decidable_eq α] [decidable_eq β]

/- In order to prove that simplicial maps 
   map vertices to vertices, we first show: 
   One can go back and forth between vertices 
   and singletons that are simplices.
-/
lemma vertex_to_singleton
    (X : simplicial_complex α)
    (x : α)
    (x_in_X : x ∈ vertices X)
  : {x} ∈ X.simplices
:= begin
  simp only[vertices] at x_in_X,
  rw [set.mem_Union] at x_in_X,
  choose s x_in_X using x_in_X,
  rw [set.mem_Union] at x_in_X,
  choose Hs x_in_s using x_in_X,

  -- As x is a vertex, x is contained in a simplex s of X.
  -- Therefore, {x} ⊆ s.
  have x_sub_s : {x} ⊆ s,
       by finish,

  -- As the set of simplices of X is closed under subsets, 
  -- also {x} is a simplex of X.
  apply X.subset_closed s;
  assumption,
end     

lemma singleton_to_vertex
    (X : simplicial_complex α)
    (x : α)
    (x_in_SX : {x} ∈ X.simplices)
  : x ∈ vertices X
:= begin
  -- {x} witnesses that x is contained in a simplex 
  -- and thus is a vertex
  simp only[vertices, set.mem_Union],
  use {x},
  finish,
end  

-- Simplicial maps map vertices to vertices.
lemma simplicial_map_on_vertices
    (X : simplicial_complex α)
    (Y : simplicial_complex β)
    (f : simplicial_map X Y)
    (x : α)
    (x_in_X : x ∈ vertices X)
  : f.map x ∈ vertices Y
:= begin
  simp only[vertices, set.mem_Union],
  use (finset.image f.map {x}),
  split,
  apply f.is_simplicial,
  rw [←vertex_iff_singleton],
  assumption,
  rw [finset.mem_coe],
  apply finset.mem_image_of_mem,
  rw [finset.mem_singleton],
end

lemma simplicial_lift_bij_implies_vertices_bij
    (X : simplicial_complex α)
    (Y : simplicial_complex β)
    (f : simplicial_map X Y)
  : set.bij_on (simplicial_map_lift f) X.simplices Y.simplices → set.bij_on f.map (vertices X) (vertices Y)
:= begin
  simp only [set.bij_on, set.maps_to, set.inj_on, set.surj_on, simplicial_map_lift, vertices_set_of],
  intro lift_bij,
  choose lift_range lift_inj lift_surj using lift_bij,
  split,

  intros x x_in_X,
  simp only [set.mem_set_of] at x_in_X ⊢,
  choose s s_in_X x_in_s using x_in_X,
  specialize lift_range s_in_X,
  use (finset.image f.map s),
  split, assumption,
  apply finset.mem_image_of_mem,
  assumption,
  
  split,
  intros x₁ x₁_in_X x₂ x₂_in_X fx₁_eq_fx₂,
  simp only [set.mem_set_of] at x₁_in_X x₂_in_X,
  rw [←vertex_iff_in_simplex, vertex_iff_singleton] at x₁_in_X x₂_in_X,
  specialize lift_inj x₁_in_X x₂_in_X,
  rw [←finset.singleton_inj, ←finset.image_singleton, ←finset.image_singleton] at fx₁_eq_fx₂,
  specialize lift_inj fx₁_eq_fx₂,
  rw [finset.singleton_inj] at lift_inj,
  assumption,
  
  simp only [set.subset_def] at lift_surj ⊢,
  intros y y_in_Y,
  simp only [set.mem_set_of] at y_in_Y,
  choose t t_in_Y y_in_t using y_in_Y,
  specialize lift_surj t t_in_Y,
  
  simp only [set.mem_image] at lift_surj ⊢,
  choose s s_in_X fs_eq_t using lift_surj,
  rw [←fs_eq_t, finset.mem_image] at y_in_t,
  choose x x_in_s fx_eq_y using y_in_t,
  
  use x, split,
  simp only [set.mem_set_of],
  use s, split; assumption,
  assumption,
end

lemma vertices_bij_implies_simplicial_lift_maps_to
    (X : simplicial_complex α)
    (Y : simplicial_complex β)
    (f : simplicial_map X Y)
  : set.bij_on f.map (vertices X) (vertices Y) → set.maps_to (simplicial_map_lift f) X.simplices Y.simplices
:= begin
  simp only [set.bij_on, set.maps_to, set.inj_on, set.surj_on, simplicial_map_lift, vertices_set_of],
  intro img_bij,
  choose img_range img_inj img_surj using img_bij,
  
  intros s s_in_X,
  by_cases s_ne : s = ∅,
  
  subst s_ne,
  rw [finset.image_empty],
  apply simplicial_complex_empty_simplex,
  
  simp only [finset.eq_empty_iff_forall_not_mem, not_forall, not_not] at s_ne,
  choose x x_in_s using s_ne,
  have x_in_X : x ∈ vertices X, from
  begin
    rw [vertices_set_of, set.mem_set_of],
    use s, split; assumption,
  end,
  rw [vertices_set_of] at x_in_X,
  specialize img_range x_in_X,
  
  simp only [set.mem_set_of] at img_range,
  choose t t_in_Y fx_in_t using img_range,
  apply f.is_simplicial,
  assumption,
end

lemma vertices_bij_implies_simplicial_lift_inj
    (X : simplicial_complex α)
    (Y : simplicial_complex β)
    (f : simplicial_map X Y)
  : set.bij_on f.map (vertices X) (vertices Y) → set.inj_on (simplicial_map_lift f) X.simplices
:= begin
  simp only [set.bij_on, set.maps_to, set.inj_on, set.surj_on, simplicial_map_lift, vertices_set_of],
  intro img_bij,
  choose img_range img_inj img_surj using img_bij,
  
  intros s₁ s₁_in_X s₂ s₂_in_X fs₁_eq_fs₂,
  simp only [finset.ext_iff] at fs₁_eq_fs₂ ⊢,

  have s₁_ss_vert : ↑s₁ ⊆ vertices X, by { apply simplex_subset_vertices X s₁ s₁_in_X, },
  have s₂_ss_vert : ↑s₂ ⊆ vertices X, by { apply simplex_subset_vertices X s₂ s₂_in_X, },

  intro a,
  specialize fs₁_eq_fs₂ (f.map a),
  cases fs₁_eq_fs₂ with fs₁_ss_fs₂ fs₂_ss_fs₁,
  split,

  intro a_in_s₁,
  have fa_in_fs₁ : f.map a ∈ finset.image f.map s₁, from
  begin
    apply finset.mem_image_of_mem f.map a_in_s₁,
  end,
  specialize fs₁_ss_fs₂ fa_in_fs₁,
  rw [←finset.mem_coe, finset.coe_image, @set.inj_on.mem_image_iff _ _ (vertices X), finset.mem_coe] at fs₁_ss_fs₂,
  assumption,
  simp only [vertices_set_of, exists_prop],
  assumption,
  assumption,

  apply set.mem_of_subset_of_mem s₁_ss_vert,
  rw [finset.mem_coe],
  assumption,

  intro a_in_s₂,
  have fa_in_fs₂ : f.map a ∈ finset.image f.map s₂, from
  begin
    apply finset.mem_image_of_mem f.map a_in_s₂,
  end,
  specialize fs₂_ss_fs₁ fa_in_fs₂,
  rw [←finset.mem_coe, finset.coe_image, @set.inj_on.mem_image_iff _ _ (vertices X), finset.mem_coe] at fs₂_ss_fs₁,
  assumption,
  simp only [vertices_set_of, exists_prop],
  assumption,
  assumption,

  apply set.mem_of_subset_of_mem s₂_ss_vert,
  rw [finset.mem_coe],
  assumption,
end

end vertices

/-
# Dimension monotonicity
-/

section dimension

variable [decidable_eq β]

-- The dimension of simplices does not increase 
-- under simplicial maps.
lemma simplicial_map_dim_mono
    (X : simplicial_complex α)
    (Y : simplicial_complex β)
    (f : simplicial_map X Y)
    (s : finset α)
    (s_in_SX : s ∈ X.simplices)
  : dim (finset.image f.map s) ≤ dim s
:= begin
  calc dim (finset.image f.map s) 
         = finset.card (finset.image f.map s) - 1 
         : by unfold dim
     ... ≤ finset.card s - 1
         : by simp[finset.card_image_le]
     ... ≤ dim s 
         : by unfold dim,
end

end dimension

/-
# Examples
-/

-- The identity map is simplicial.
lemma id_is_simplicial_map [decidable_eq α]
    (X : simplicial_complex α)
  : is_simplicial_map X X id
:= begin
  simp,
end

def id_simplicial_map [decidable_eq α]
    (X : simplicial_complex α)
  : simplicial_map X X 
:= simplicial_map.mk 
     (id)
     (id_is_simplicial_map X)    

-- Constant maps are simplicial
lemma const_is_simplicial [decidable_eq β]
      (X : simplicial_complex α)
      (Y : simplicial_complex β)
      (y_0 : β)
      (y0_vertex : y_0 ∈ vertices Y)
    : is_simplicial_map X Y (λ x : α, y_0)
:= begin
  -- As y_0 is a vertex of Y, the set {y_0} is a simplex of Y  
  have y0_in_SY : {y_0} ∈ Y.simplices, 
       by exact vertex_to_singleton Y y_0 y0_vertex,

  -- Setup for the main argument
  assume s : finset α,
  assume s_in_SX : s ∈ X.simplices,
  
  let f  := λ x : α, y_0,
  let fs := finset.image f s,

  -- We have f(s) ⊆ {y_0}
  have fs_sub_y0 : fs ⊆ {y_0}, from
  begin
    assume y,
    assume y_in_fs : y ∈ fs,
    show y ∈ {y_0}, by finish,
  end,

  -- and thus f(s) is a simplex of Y.
  show fs ∈ Y.simplices, 
       by exact Y.subset_closed {y_0} y0_in_SY fs fs_sub_y0,
end  

def const_simplicial_map [decidable_eq β]
    (X : simplicial_complex α)
    (Y : simplicial_complex β)
    (y_0 : β)
    (y0_vertex : y_0 ∈ vertices Y)
  : simplicial_map X Y
:= simplicial_map.mk 
     (λ x : α, y_0)
     (const_is_simplicial X Y y_0 y0_vertex)  

-- Compositions of simplicial maps are simplicial
lemma is_simplicial_comp [decidable_eq β] [decidable_eq γ]
    {X : simplicial_complex α}
    {Y : simplicial_complex β}
    {Z : simplicial_complex γ}
    (f : α → β)
    (f_simpl : is_simplicial_map X Y f)
    (g : β → γ)
    (g_simpl : is_simplicial_map Y Z g)
  : is_simplicial_map X Z (g ∘ f)
:= begin
  assume s : finset α,
  assume s_in_SX : s ∈ X.simplices,

  let t : finset β := finset.image f s,

  have t_in_SY : t ∈ Y.simplices,
       by {apply (f_simpl s), apply s_in_SX}, -- or just: tauto},

  have gfs_in_SZ : finset.image g t ∈ Z.simplices,
       by {apply (g_simpl t), apply t_in_SY},

  show finset.image (g ∘ f) s ∈ Z.simplices, 
    by calc finset.image (g ∘ f) s 
          = finset.image g (finset.image f s) 
          : by exact finset.image_image.symm
      ... = finset.image g t
          : by refl
      ... ∈ Z.simplices
          : by exact gfs_in_SZ,     
end

def simplicial_map.comp [decidable_eq β] [decidable_eq γ]
    {X : simplicial_complex α}
    {Y : simplicial_complex β}
    {Z : simplicial_complex γ}
    (f : simplicial_map X Y)
    (g : simplicial_map Y Z)
  : simplicial_map X Z
:= simplicial_map.mk 
     (g.map ∘ f.map)
     (is_simplicial_comp f.map f.is_simplicial g.map g.is_simplicial)

/-
# Simplicial isomorphisms
-/

section isomorphism

variables [decidable_eq α] [decidable_eq β] [decidable_eq γ]

-- A simplicial map is a simplicial isomorphism
-- if it admits an inverse simplicial map.
@[simp]
def is_inverse_simplicial_iso
    {X : simplicial_complex α}
    {Y : simplicial_complex β}
    (f : simplicial_map X Y)
    (g : simplicial_map Y X)
  : Prop
:= (vertices X).restrict (simplicial_map.comp f g).map = (vertices X).restrict id
 ∧ (vertices Y).restrict (simplicial_map.comp g f).map = (vertices Y).restrict id

lemma is_inverse_simplicial_iso_symm
    {X : simplicial_complex α}
    {Y : simplicial_complex β}
    (f : simplicial_map X Y)
    (g : simplicial_map Y X)
  : is_inverse_simplicial_iso f g ↔ is_inverse_simplicial_iso g f
:= begin
  split; unfold is_inverse_simplicial_iso,
  { intro f_inv_g,
    cases f_inv_g with fg_id gf_id,
    
    split; assumption, },
  { intro g_inv_f,
    cases g_inv_f with gf_id fg_id,
    
    split; assumption, }
end

@[simp]
def is_simplicial_iso 
    {X : simplicial_complex α}
    {Y : simplicial_complex β}
    (f : simplicial_map X Y)
  : Prop
:= ∃ g : simplicial_map Y X, is_inverse_simplicial_iso f g
--:= set.bij_on (simplicial_map_lift f) X.simplices Y.simplices

-- For example, the identity map is a simplicial isomorphism
-- because it is its own inverse

lemma id_is_simplicial_iso
    (X : simplicial_complex α)
  : is_simplicial_iso (id_simplicial_map X)
:=
begin
  use id_simplicial_map X,
  show is_inverse_simplicial_iso (id_simplicial_map X) (id_simplicial_map X), 
       by finish,
end

lemma iso_inv_is_iso
    {X : simplicial_complex α}
    {Y : simplicial_complex β}
    (f : simplicial_map X Y)
    (g : simplicial_map Y X)
  : is_simplicial_iso f → is_inverse_simplicial_iso f g → is_simplicial_iso g
:= begin
  intros f_iso g_inv_f,
  unfold is_simplicial_iso,
  use f,
  rw [is_inverse_simplicial_iso] at g_inv_f ⊢,
  rw [and_comm],
  assumption,
end

-- The composition of two isomorphisms gives an isomorphism.
lemma iso_comp_is_iso
    {X : simplicial_complex α}
    {Y : simplicial_complex β}
    {Z : simplicial_complex γ}
    (f : simplicial_map X Y)
    (g : simplicial_map Y Z)
  : is_simplicial_iso f → is_simplicial_iso g → is_simplicial_iso (simplicial_map.comp f g)
:= begin
  unfold is_simplicial_iso,
  intros f_iso g_iso,
  choose f_inv f_iso using f_iso,
  choose g_inv g_iso using g_iso,
  use (g_inv.comp f_inv),
  simp only[is_inverse_simplicial_iso, simplicial_map.comp, id_simplicial_map] at *,
  cases f_iso with f_inv_left f_inv_right,
  cases g_iso with g_inv_left g_inv_right,
  simp at *,
  unfold set.eq_on at *,
  split,

  intros x x_vert,
  specialize f_inv_left x_vert,
  specialize g_inv_left (simplicial_map_on_vertices X Y f x x_vert),
  rw [function.comp.assoc, ←function.comp.assoc g_inv.map, function.comp_app, g_inv_left],
  simp,
  assumption,

  intros z z_vert,
  specialize g_inv_right z_vert,
  specialize f_inv_right (simplicial_map_on_vertices Z Y g_inv z z_vert),
  rw [function.comp.assoc, ←function.comp.assoc f.map, function.comp_app, f_inv_right],
  simp,
  assumption,
end

lemma iso_is_injective_vertices
    {X : simplicial_complex α}
    {Y : simplicial_complex β}
    (f : simplicial_map X Y)
    (f_iso : is_simplicial_iso f)
  : set.inj_on f.map (vertices X)
:= begin
  unfold is_simplicial_iso at f_iso,
  choose g g_inv_f using f_iso,
  unfold is_inverse_simplicial_iso at g_inv_f,
  choose fg_id gf_id using g_inv_f,

  simp only [function.funext_iff, set.restrict_eq_restrict_iff, set.eq_on] at fg_id,
  unfold set.inj_on,
  intros x₁ x₁_in_X x₂ x₂_in_X fx₁_eq_fx₂,

  have fgx₁_eq_x₁ : (f.comp g).map x₁ = id x₁, from
  begin
    specialize fg_id x₁_in_X,
    assumption,
  end,

  have fgx₂_eq_x₂ : (f.comp g).map x₂ = id x₂, from
  begin
    specialize fg_id x₂_in_X,
    assumption,
  end,

  simp only [simplicial_map.comp, function.comp_apply] at fgx₁_eq_x₁ fgx₂_eq_x₂,
  simp only [fx₁_eq_fx₂, fgx₂_eq_x₂, id.def] at fgx₁_eq_x₁,
  symmetry,
  assumption,
end

lemma iso_is_injective_simplices
    {X : simplicial_complex α}
    {Y : simplicial_complex β}
    (f : simplicial_map X Y)
    (f_iso : is_simplicial_iso f)
  : ∀ s ∈ X.simplices, set.inj_on f.map ↑s
:= begin
  intros s s_in_X,
  simp only [set.inj_on],
  intros x₁ x₁_in_s x₂ x₂_in_s fx₁_eq_fx₂,

  unfold is_simplicial_iso at f_iso,
  choose g gf_inv using f_iso,
  unfold is_inverse_simplicial_iso at gf_inv,
  choose gf_id fg_id using gf_inv,

  simp only [set.restrict_eq_restrict_iff, set.eq_on, simplicial_map.comp, function.comp_apply] at gf_id,
  have x₁_in_X : x₁ ∈ vertices X, from
  begin
    rw [vertex_iff_in_simplex],
    use s, split; assumption,
  end,

  have x₂_in_X : x₂ ∈ vertices X, from
  begin
    rw [vertex_iff_in_simplex],
    use s, split; assumption,
  end,

  have gfx₁_eq_x₁ : g.map (f.map x₁) = x₁, from
  begin
    specialize gf_id x₁_in_X,
    rw [id.def] at gf_id,
    assumption,
  end,

  have gfx₂_eq_x₂ : g.map (f.map x₂) = x₂, from
  begin
    specialize gf_id x₂_in_X,
    rw [id.def] at gf_id,
    assumption,
  end,

  have gfx₁_eq_gfx₂ : g.map (f.map x₁) = g.map (f.map x₂), from
  begin
    apply congr_arg g.map,
    assumption,
  end,

  rw [gfx₁_eq_x₁, gfx₂_eq_x₂] at gfx₁_eq_gfx₂,
  assumption,
end

lemma iso_is_surjective_vertices
    {X : simplicial_complex α}
    {Y : simplicial_complex β}
    (f : simplicial_map X Y)
    (f_iso : is_simplicial_iso f)
  : set.surj_on f.map (vertices X) (vertices Y)
:= begin
  unfold is_simplicial_iso at f_iso,
  choose g g_inv_f using f_iso,
  unfold is_inverse_simplicial_iso at g_inv_f,
  choose fg_id gf_id using g_inv_f,

  simp only [function.funext_iff, set.restrict_eq_restrict_iff, set.eq_on] at gf_id,
  simp only [set.surj_on, set.subset_def, set.mem_image],
  intros x x_in_Y,

  specialize gf_id x_in_Y,
  simp only [simplicial_map.comp, function.comp_apply] at gf_id,
  use (g.map x), split,

  rw [vertex_iff_in_simplex] at x_in_Y ⊢,
  choose s s_in_Y x_in_s using x_in_Y,

  use (finset.image g.map s), split,
  apply g.is_simplicial,
  assumption,
  apply finset.mem_image_of_mem,

  assumption,

  rw [id.def] at gf_id,
  assumption,
end

-- Defining isomorphy between simplicial complexes.
@[simp]
def is_simplicially_iso
    (X : simplicial_complex α)
    (Y : simplicial_complex β)
  : Prop
:= ∃ (f : simplicial_map X Y), is_simplicial_iso f
infixr ` ≅ `:50 := is_simplicially_iso

lemma simplicial_iso_implies_lift_bij
    (X : simplicial_complex α)
    (Y : simplicial_complex β)
    (f : simplicial_map X Y)
  : is_simplicial_iso f → Y.simplices = (simplicial_map_lift f) '' X.simplices
:= begin
  intro f_iso,
  unfold is_simplicial_iso at f_iso,
  choose g g_inv_f using f_iso,
  unfold is_inverse_simplicial_iso at g_inv_f,
  choose fg_id gf_id using g_inv_f,

  rw [set.ext_iff],
  intro t,
  split,

  intro t_in_Y,
  simp only [simplicial_map_lift, set.mem_image],
  use (finset.image g.map t),
  split,
  apply g.is_simplicial,
  assumption,

  simp only [←finset.coe_inj, finset.coe_image],
  rw [←set.image_comp],
  conv_rhs {
    rw [←set.image_id ↑t],
  },
  apply set.eq_on.image_eq,
  simp only [function.funext_iff, set.restrict_eq_restrict_iff, simplicial_map.comp] at gf_id,
  have t_in_vert : ↑t ⊆ vertices Y, by { apply simplex_subset_vertices Y t t_in_Y, },
  apply set.eq_on.mono t_in_vert,
  assumption,

  intro t_in_lift,
  simp only [simplicial_map_lift, set.mem_image] at t_in_lift,
  choose s s_in_X fs_eq_t using t_in_lift,
  subst fs_eq_t,
  apply f.is_simplicial,
  assumption,
end

lemma simplicial_iso_vertices
    (X : simplicial_complex α)
    (Y : simplicial_complex β)
    (f : simplicial_map X Y)
  : is_simplicial_iso f → vertices Y = f.map '' vertices X
:= begin
  intro f_iso,
  unfold is_simplicial_iso at f_iso,
  choose g gf_inv using f_iso,
  unfold is_inverse_simplicial_iso at gf_inv,
  simp only [set.restrict_eq_restrict_iff, set.eq_on, simplicial_map.comp, function.comp_app, id.def] at gf_inv,
  choose gf_id fg_id using gf_inv,

  rw [set.ext_iff],
  intro x,
  split,

  intro x_in_Y,
  specialize fg_id x_in_Y,
  rw [set.mem_image],
  use (g.map x), split,

  rw [vertex_iff_singleton] at x_in_Y ⊢,
  rw [←finset.image_singleton],
  apply g.is_simplicial,
  assumption,

  assumption,

  intro x_in_img,
  rw [set.mem_image] at x_in_img,
  choose y y_in_X fy_eq_x using x_in_img,
  rw [vertex_iff_singleton] at y_in_X ⊢,
  rw [←fy_eq_x, ←finset.image_singleton],
  apply f.is_simplicial,
  assumption,
end

noncomputable
instance is_simplicially_iso.fintype
    (X : simplicial_complex α) [fintype X.simplices]
    (Y : simplicial_complex β)
    (X_iso_Y : X ≅ Y)
  : fintype Y.simplices
:= begin
  unfold is_simplicially_iso at X_iso_Y,
  choose f f_iso using X_iso_Y,
  rw [simplicial_iso_implies_lift_bij X Y f f_iso],

  apply set.fintype_image,
end

lemma simplicial_iso_preserves_simplex_dim
    {X : simplicial_complex α}
    {Y : simplicial_complex β}
    (f : simplicial_map X Y)
    (f_iso : is_simplicial_iso f)
  : ∀ s ∈ X.simplices, dim s = dim (finset.image f.map s)
:= begin
  intros s s_in_X,
  unfold dim,
  apply congr_arg (λ (z : ℤ), z - 1),
  symmetry,
  rw [nat.cast_inj, finset.card_image_iff],
  apply iso_is_injective_simplices f f_iso s s_in_X,
end

lemma simplicial_iso_preserves_dim
    (X : simplicial_complex α) [X_fin : fintype X.simplices]
    (Y : simplicial_complex β)
    (X_iso_Y : X ≅ Y)
  : @dim_of_complex α X X_fin = @dim_of_complex β Y (@is_simplicially_iso.fintype α β _ _ X X_fin Y X_iso_Y)
:= begin
  unfold is_simplicially_iso at X_iso_Y,
  choose f f_iso using X_iso_Y,
  simp only [dim_of_complex],
  
  rw [le_antisymm_iff],
  split,

  -- dim X ≤ dim Y case.
  rw [finset.max'_le_iff],
  intros n n_X_dim,
  rw [finset.mem_image] at n_X_dim,
  choose s s_in_X s_dim_n using n_X_dim,
  rw [set.mem_to_finset] at s_in_X,
  rw [←s_dim_n],

  apply finset.le_max',
  rw [simplicial_iso_preserves_simplex_dim f f_iso s s_in_X, finset.mem_image],
  use (finset.image f.map s),
  split,

  rw [set.mem_to_finset],
  apply f.is_simplicial,
  assumption,

  refl,

  -- dim Y ≤ dim X case.
  rw [finset.max'_le_iff],
  intros m m_Y_dim,
  rw [finset.mem_image] at m_Y_dim,
  choose t t_in_Y t_dim_m using m_Y_dim,
  rw [set.mem_to_finset] at t_in_Y,
  rw [←t_dim_m],

  let f_iso' := f_iso,
  unfold is_simplicial_iso at f_iso',
  choose g gf_inv using f_iso',
  have g_iso : is_simplicial_iso g, from
  begin
    apply iso_inv_is_iso f g f_iso gf_inv,
  end,

  apply finset.le_max',
  rw [simplicial_iso_preserves_simplex_dim g g_iso t t_in_Y, finset.mem_image],
  use (finset.image g.map t),
  split,

  rw [set.mem_to_finset],
  apply g.is_simplicial,
  assumption,

  refl,
end

-- Being simplicially isomorphic is an equivalence relation.
@[refl]
lemma simplicial_iso_refl
    (X : simplicial_complex α)
  : X ≅ X
:= begin
  unfold is_simplicially_iso,
  use id_simplicial_map X,
  apply id_is_simplicial_iso,
end

@[symm]
lemma simplicial_iso_symm
    (X : simplicial_complex α)
    (Y : simplicial_complex β)
  : X ≅ Y ↔ Y ≅ X
:= begin
  unfold is_simplicially_iso,
  split; unfold is_simplicial_iso,
  { intro X_iso_Y,
    choose f g f_inv_g using X_iso_Y,
    
    use g, use f,
    rw [is_inverse_simplicial_iso_symm],
    assumption, },
  { intro Y_iso_X,
    choose f g f_inv_g using Y_iso_X,
    
    use g, use f,
    rw [is_inverse_simplicial_iso_symm],
    assumption, }
end

@[trans]
lemma simplicial_iso_trans
    (X : simplicial_complex α)
    (Y : simplicial_complex β)
    (Z : simplicial_complex γ)
  : X ≅ Y → Y ≅ Z → X ≅ Z
:= begin
  intros X_iso_Y Y_iso_Z,
  unfold is_simplicially_iso at *,
  choose f f_iso using X_iso_Y,
  choose g g_iso using Y_iso_Z,
  use (f.comp g),
  apply iso_comp_is_iso;
  assumption,
end

lemma simplicial_iso_preserves_equiv
    (X Y : simplicial_complex α)
  : X.simplices = Y.simplices → X ≅ Y
:= begin
  intro H,
  unfold is_simplicially_iso,

  have id_simplicial_X : is_simplicial_map X Y id, from
  begin
    unfold is_simplicial_map,
    intros s Hs,
    rw [finset.image_id, ←H],
    assumption,
  end,

  have id_simplicial_Y : is_simplicial_map Y X id, from
  begin
    unfold is_simplicial_map,
    intros s Hs,
    rw [finset.image_id, H],
    assumption,
  end,

  set id_X := simplicial_map.mk id id_simplicial_X,
  use id_X,
  unfold is_simplicial_iso,

  set id_Y := simplicial_map.mk id id_simplicial_Y,
  use id_Y,

  unfold is_inverse_simplicial_iso,
  split; simp only[simplicial_map.comp];
  rw [function.comp.left_id];
  simp only[id_simplicial_map],
end

lemma simplicial_iso_preserves_subcomplex_image
    (X Y Z : simplicial_complex α)
    (f : simplicial_map Y Z)
    (f_iso : is_simplicial_iso f)
  : X ⊆ Y → simplicial_image X f.map ⊆ Z
:= begin
  intro X_sub_Y,
  simp only [is_subcomplex] at X_sub_Y ⊢,

  rw [simplicial_iso_implies_lift_bij Y Z f f_iso],
  simp only [simplicial_map_lift, set.image],
  simp only [set.subset_def] at X_sub_Y ⊢,

  intros t t_in_fX,
  simp only [set.mem_set_of] at t_in_fX ⊢,
  choose s s_in_X fs_eq_t using t_in_fX,
  specialize X_sub_Y s s_in_X,

  use s, split; assumption,
end

end isomorphism

/-
# Simplicial Coercions
-/

section coercion

variables [decidable_eq α] [decidable_eq β] [decidable_eq γ]

-- Define as coercion on types that lifts to simplicial map.
structure simplicial_coe
    (X : simplicial_complex α)
    (β : Type*)
:= mk :: (coe : α → β)
         (injective : set.inj_on coe (vertices X))
notation φ `[` X `]` := simplicial_image X φ.coe

def simplicial_coe.simplicial_map
    {X : simplicial_complex α}
    (φ : simplicial_coe X β)
  : simplicial_map X (φ[X])
:= simplicial_map.mk φ.coe (map_is_simplicial_onto_image X φ.coe)

instance simplicial_coe.fintype
    (X : simplicial_complex α) [fintype X.simplices]
    (φ : simplicial_coe X β)
  : fintype (φ[X]).simplices
:= begin
  rw [simplicial_image_is_lift_image],
  apply set.fintype_image,
end

lemma simplicial_coe_inv_is_simplicial
    [nonempty α]
    {X : simplicial_complex α}
    (φ : simplicial_coe X β)
  : is_simplicial_map (φ[X]) X (function.inv_fun_on φ.coe (vertices X))
:= begin
  simp only [is_simplicial_map, simplicial_image],
  intros t t_in_coe,
  simp only [set.mem_set_of] at t_in_coe,
  choose s s_in_X coe_s_t using t_in_coe,

  rw [←coe_s_t],
  have inv_id : finset.image (function.inv_fun_on φ.coe (vertices X)) (finset.image φ.coe s) = s, from
  begin
    simp only [←finset.coe_inj, finset.coe_image],
    apply set.inj_on.inv_fun_on_image,
    apply φ.injective,
    apply simplex_subset_vertices,
    assumption,
  end,
  rw [inv_id],
  assumption,
end

noncomputable
def simplicial_coe_inv
    [nonempty α]
    {X : simplicial_complex α}
    (φ : simplicial_coe X β)
  : simplicial_map (φ[X]) X
:= simplicial_map.mk (function.inv_fun_on φ.coe (vertices X)) (simplicial_coe_inv_is_simplicial φ)
notation φ`⁻ᶜ` := simplicial_coe_inv φ

lemma coe_inv_is_inverse_simplicial_iso
    [nonempty α]
    {X : simplicial_complex α}
    (φ : simplicial_coe X β)
  : is_inverse_simplicial_iso (simplicial_map.mk φ.coe (map_is_simplicial_onto_image X φ.coe)) (φ⁻ᶜ)
:= begin
  simp only [is_inverse_simplicial_iso, simplicial_map.comp, set.restrict_eq_restrict_iff],
  split,

  apply set.inj_on.left_inv_on_inv_fun_on,
  apply φ.injective,
  
  simp only [set.eq_on, id.def],
  intros y y_in_coe,
  apply function.inv_fun_on_eq,
  rw [simplicial_image_vertices, set.mem_image] at y_in_coe,
  choose x x_in_X coe_x_y using y_in_coe,
  use x, split; assumption,
end

lemma coe_is_iso
    [nonempty α]
    (X : simplicial_complex α)
    (φ : simplicial_coe X β)
  : is_simplicial_iso (@simplicial_map.mk α β _ X (φ[X]) φ.coe (by { apply map_is_simplicial_onto_image, }))
:= begin
  unfold is_simplicial_iso,
  use (@simplicial_coe_inv _ _ _ _ _ X φ),
  apply coe_inv_is_inverse_simplicial_iso,
end

lemma simplicial_coe.iso_onto_image
    [nonempty α]
    {X : simplicial_complex α}
    (φ : simplicial_coe X β)
  : X ≅ φ[X]
:= begin
  unfold is_simplicially_iso,
  use φ.coe,
  apply map_is_simplicial_onto_image,
  apply coe_is_iso,  
end

lemma coe_preserves_iso
    [nonempty α]
    (X Y : simplicial_complex α)
    (φ : simplicial_coe X β)
    (ψ : simplicial_coe Y β)
  : X ≅ Y → φ[X] ≅ ψ[Y]
:= begin
  intros X_iso_Y,
  apply simplicial_iso_trans (φ[X]) X,
  rw [simplicial_iso_symm],
  apply φ.iso_onto_image,

  rw [simplicial_iso_symm],
  apply simplicial_iso_trans (ψ[Y]) Y,
  rw [simplicial_iso_symm],
  apply ψ.iso_onto_image,

  rw [simplicial_iso_symm],
  assumption,
end

lemma coe_comp_is_injective
    {X : simplicial_complex α}
    (φ : simplicial_coe X β)
    (ψ : simplicial_coe (φ[X]) γ)
  : set.inj_on (ψ.coe ∘ φ.coe) (vertices X)
:= begin
  apply set.inj_on.comp ψ.injective φ.injective,
  simp only [set.maps_to],
  intros x x_vert,
  dsimp only [simplicial_image, vertices, simplicial_complex.simplices],
  simp only [set.mem_Union],

  use ({φ.coe x}),
  split,

  simp only [set.mem_set_of],
  use ({x}),
  split,
  rw [←vertex_iff_singleton],
  apply x_vert,
  rw [finset.image_singleton],

  rw [finset.mem_coe, finset.mem_singleton],
end

lemma coe_comp_image
    (X : simplicial_complex α)
    (φ : simplicial_coe X β)
    (ψ : simplicial_coe (φ[X]) γ)
  : (simplicial_image X (ψ.coe ∘ φ.coe)).simplices = (simplicial_image (φ[X]) ψ.coe).simplices
:= begin
  dsimp only [simplicial_image, simplicial_complex.simplices],
  rw [set.ext_iff],
  intro s,
  split,

  { intro s_in_comp,
    rw [set.mem_set_of] at *,
    choose t Ht img_eq_s using s_in_comp,
    
    set u : finset β := finset.image φ.coe t,
    use u,
    split,
    
    rw [set.mem_set_of],
    use t, split, assumption,
    refl,
    
    rw [←finset.image_image] at img_eq_s,
    assumption, },

  { intro s_in_coe,
    rw [set.mem_set_of] at *,
    choose t Ht img_eq_s using s_in_coe,
    rw [set.mem_set_of] at Ht,
    choose u u_in_X img_u_eq_t using Ht,
    
    use u, split, assumption,
    rw [←finset.image_image, img_u_eq_t],
    assumption, },
end

@[simp]
def simplicial_coe.comp
    {X : simplicial_complex α}
    (φ : simplicial_coe X β)
    (ψ : simplicial_coe (φ[X]) γ)
  : simplicial_coe X γ
:= simplicial_coe.mk (ψ.coe ∘ φ.coe) (coe_comp_is_injective φ ψ)

-- Restriction of coe is coe.
lemma coe_restrict_is_injective
    (X Y : simplicial_complex α)
    (φ : simplicial_coe X β)
    (Y_subcomp_X : vertices Y ⊆ vertices X)
  : set.inj_on φ.coe (vertices Y)
:= begin
  apply set.inj_on.mono Y_subcomp_X,
  apply φ.injective,
end

@[simp]
def simplicial_coe.restrict
    {X : simplicial_complex α}
    (φ : simplicial_coe X β)
    (Y : simplicial_complex α)
    (Y_subcomp_X : vertices Y ⊆ vertices X)
  : simplicial_coe Y β
:= simplicial_coe.mk φ.coe (coe_restrict_is_injective X Y φ Y_subcomp_X)
notation φ `[` Y `; ` H `]` := simplicial_image Y (simplicial_coe.restrict φ Y H).coe

def simplicial_coe.restrict_coe
    {X Y : simplicial_complex α}
    {Y_subcomp_X : vertices Y ⊆ vertices X}
  : has_coe (simplicial_coe X β) (simplicial_coe Y β)
:= has_coe.mk (λ φ : simplicial_coe X β, φ.restrict Y Y_subcomp_X)

-- Convert isomorphisms into coercions.
def simplicial_map.coe
    {X : simplicial_complex α}
    {Y : simplicial_complex β}
    (f : simplicial_map X Y)
    (f_iso : is_simplicial_iso f)
  : simplicial_coe X β
:= simplicial_coe.mk f.map (iso_is_injective_vertices f f_iso)

-- Coercion on images.
--  g[Y] = X → φ[X]
--  ↑     ↗ φ ∘ g
--  Y
def simplicial_coe_on_image
    {X : simplicial_complex α}
    {Y : simplicial_complex β}
    (f : simplicial_map X Y)
    (f_iso : is_simplicial_iso f)
    (Y_img_X : Y.simplices = simplicial_map_lift f '' X.simplices)
    (φ : simplicial_coe Y γ)
  : simplicial_coe X γ
:= simplicial_coe.mk
    (φ.coe ∘ f.map)
    (begin
      apply set.inj_on.comp φ.injective,
      apply (f.coe f_iso).injective,

      unfold set.maps_to,
      intros x x_in_X,
      simp only [vertex_iff_singleton, Y_img_X, simplicial_map_lift, set.image, set.mem_set_of],
      use {x}, split,

      rw [←vertex_iff_singleton],
      assumption,

      apply finset.image_singleton,
    end)


lemma simplicial_coe_union_simplices
    (X Y : simplicial_complex α)
    (φ : simplicial_coe (X ∪ Y) β)
  : φ[X ∪ Y].simplices =
      (φ[X; by { apply is_subcomplex_vertices, apply subcomplex_simplicial_union_left, }]
        ∪ φ[Y; by { apply is_subcomplex_vertices, apply subcomplex_simplicial_union_right, }]).simplices
:= begin
  apply simplicial_image_union,
end

lemma simplicial_coe_union
    (X Y : simplicial_complex α)
    (φ : simplicial_coe (X ∪ Y) β)
  : φ[X ∪ Y] ≅
      (φ[X; by { apply is_subcomplex_vertices, apply subcomplex_simplicial_union_left, }]
        ∪ φ[Y; by { apply is_subcomplex_vertices, apply subcomplex_simplicial_union_right, }])
:= begin
  apply simplicial_iso_preserves_equiv,
  apply simplicial_coe_union_simplices,
end

end coercion

/-
# Simplicial joins
-/

section join

variables [decidable_eq α] [decidable_eq β]

-- Start with some formalization of disjoint unions.
@[simp]
def simplex_disjoint_union
    (s t : finset α)
  : finset (α × ℕ)
:= (finset.product s {0}) ∪ (finset.product t {1})
infixl ` ⊔ₛ `:65 := simplex_disjoint_union

instance simplex_disjoint.nonempty
    (s t : finset α) [H : nonempty s ∨ nonempty t]
  : nonempty (s ⊔ₛ t)
:= begin
  iterate 2 { rw [finset.nonempty_coe_sort, ←finset.coe_nonempty] at * },
  unfold simplex_disjoint_union,
  rw [finset.coe_union, set.union_nonempty],
  cases H with Hs Ht,

  left,
  rw [finset.coe_nonempty] at *,
  rw [finset.nonempty_product],
  split,
  assumption,
  simp,

  right,
  rw [finset.coe_nonempty] at *,
  rw [finset.nonempty_product],
  split,
  assumption,
  simp,
end

instance simplex_disjoint.nonempty.left
    (s : finset α) [nonempty s]
  : nonempty (s ⊔ₛ ∅)
:= begin
  have : nonempty ↥s ∨ nonempty ↥(∅ : finset α), from
  begin
    left, assumption,
  end,

  apply @simplex_disjoint.nonempty _ _ s (∅ : finset α) this,
end

instance simplex_disjoint.nonempty.right
    (t : finset α) [nonempty t]
  : nonempty (∅ ⊔ₛ t)
:= begin
  have : nonempty ↥(∅ : finset α) ∨ nonempty ↥t, from
  begin
    right, assumption,
  end,

  apply @simplex_disjoint.nonempty _ _ (∅ : finset α) t this,
end

instance simplex_disjoint.partial_order
  : partial_order (finset (α × ℕ))
:= finset.partial_order

lemma simplex_disjoint_disjoint
    (s t : finset α)
  : @disjoint _ simplex_disjoint.partial_order _ (finset.product s {(0 : ℕ)}) (finset.product t {(1 : ℕ)})
:= begin
  rw [finset.disjoint_left],
  intros x x_in_s0,
  rw [finset.mem_product] at *,
  cases x_in_s0 with x_in_s x0,
  rw [not_and_distrib],
  right,
  rw [finset.mem_singleton] at *,
  rw [x0],
  simp,
end

lemma simplex_disjoint_mem
    (s t : finset α)
    (x : α × ℕ)
  : x ∈ s ⊔ₛ t ↔ x.fst ∈ s ∧ x.snd = 0 ∨ x.fst ∈ t ∧ x.snd = 1
:= begin
  simp only[simplex_disjoint_union],
  rw [←finset.disj_union_eq_union, finset.mem_disj_union],
  split,

  intro x_in_prod,
  cases x_in_prod with x_in_s0 x_in_t1,

  rw [finset.mem_product] at x_in_s0,
  cases x_in_s0 with x_in_s x0,
  left, split,
  assumption,
  rw [finset.mem_singleton] at x0,
  assumption,

  rw [finset.mem_product] at x_in_t1,
  cases x_in_t1 with x_in_t x1,
  right, split,
  assumption,
  rw [finset.mem_singleton] at x1,
  assumption,

  intro x_in_st,
  iterate 2 { rw [finset.mem_product, finset.mem_singleton] },
  assumption,

  apply simplex_disjoint_disjoint,
end

lemma simplex_disjoint_mem_left
    (s t : finset α)
    (x : α)
  : (x, 0) ∈ (s ⊔ₛ t) ↔ x ∈ s
:= begin
  unfold simplex_disjoint_union,
  split,
  { intro x0_in_st,
    rw [finset.mem_union] at x0_in_st,
    cases x0_in_st with x0_in_s0 x0_in_t1,
    
    rw [finset.mem_product] at x0_in_s0,
    cases x0_in_s0 with x_in_s zero,
    simp at x_in_s,
    assumption,
    
    rw [finset.mem_product] at x0_in_t1,
    cases x0_in_t1 with x_in_t contra,
    simp at contra,
    contradiction, },
  { intro x_in_s,
    rw [finset.mem_union],
    left,
    rw [finset.mem_product],
    split,
    simp, assumption,
    simp, }
end

lemma simplex_disjoint_mem_right
    (s t : finset α)
    (x : α)
  : (x, 1) ∈ (s ⊔ₛ t) ↔ x ∈ t
:= begin
  unfold simplex_disjoint_union,
  split,
  { intro x1_in_st,
    rw [finset.mem_union] at x1_in_st,
    cases x1_in_st with x1_in_s0 x1_in_t1,
    
    rw [finset.mem_product] at x1_in_s0,
    cases x1_in_s0 with x_in_s contra,
    simp at contra,
    contradiction,
    
    rw [finset.mem_product] at x1_in_t1,
    cases x1_in_t1 with x_in_t one,
    simp at x_in_t,
    assumption, },
  { intro x_in_t,
    rw [finset.mem_union],
    right,
    rw [finset.mem_product],
    split,
    simp, assumption,
    simp, }
end

lemma simplex_disjoint_subset_unique
    (s t u w : finset α)
  : (s ⊔ₛ t) ⊆ (u ⊔ₛ w) ↔ s ⊆ u ∧ t ⊆ w
:= begin
  split,

  intro disj_sset,
  rw [finset.subset_iff] at disj_sset,
  split;
  rw [finset.subset_iff];
  intros x x_in_s,

  have Hs_0 : (x, 0) ∈ s ⊔ₛ t, from
  begin
    rw [simplex_disjoint_mem_left],
    assumption,
  end,
  specialize disj_sset Hs_0,
  rw [simplex_disjoint_mem_left] at disj_sset,
  assumption,

  have Ht_1 : (x, 1) ∈ s ⊔ₛ t, from
  begin
    rw [simplex_disjoint_mem_right],
    assumption,
  end,
  specialize disj_sset Ht_1,
  rw [simplex_disjoint_mem_right] at disj_sset,
  assumption,

  intro sset,
  cases sset with s_sset_u t_sset_w,
  rw [finset.subset_iff] at *,
  intros x x_in_st,
  simp only[simplex_disjoint_union, finset.mem_union, finset.mem_product] at *,
  cases x_in_st,

  left,
  cases x_in_st with x_in_s x0,
  split,
  specialize s_sset_u x_in_s,
  assumption,
  assumption,

  right,
  cases x_in_st with x_in_t x1,
  split,
  specialize t_sset_w x_in_t,
  assumption,
  assumption,
end

lemma simplex_disjoint_subset_sep
    (s : finset (α × ℕ))
    (t u : finset α)
  : s ⊆ (t ⊔ₛ u) ↔ ∃ (z w : finset α), s = z ⊔ₛ w ∧ z ⊆ t ∧ w ⊆ u
:= begin
  split,

  intro s_sset_tu,

  let z_prod : finset (α × ℕ) := finset.filter (λ x : α × ℕ, x.snd = 0) s,
  let z : finset α := finset.bUnion z_prod (λ x, {x.fst}),

  let w_prod : finset (α × ℕ) := finset.filter (λ x : α × ℕ, x.snd = 1) s,
  let w : finset α := finset.bUnion w_prod (λ x, {x.fst}),

  use z, use w,
  
  have s_eq_zw : s = z ⊔ₛ w, from
  begin
    rw [finset.ext_iff],
    intro x,
    split,

    rw [finset.subset_iff] at s_sset_tu,
    simp_rw [simplex_disjoint_mem] at s_sset_tu,

    intro x_in_s,
    specialize s_sset_tu x_in_s,
    rw [simplex_disjoint_mem],
    simp only[z, z_prod, w, w_prod],
    iterate 2 { rw [finset.mem_bUnion] },
    cases s_sset_tu,

    left,
    cases s_sset_tu with x_in_t x0,

    use x,
    rw [finset.mem_filter],
    split, split, assumption,
    assumption,
    rw [finset.mem_singleton],

    assumption,

    right,
    cases s_sset_tu with x_in_u x1,
    split,

    use x,
    rw [finset.mem_filter],
    split, split, assumption,
    assumption,
    rw [finset.mem_singleton],

    assumption,

    intro x_in_zw,
    rw [simplex_disjoint_mem] at x_in_zw,
    cases x_in_zw;

    { cases x_in_zw with x_in_filter xn,
      simp only[z, z_prod, w, w_prod] at x_in_filter,
      rw [finset.mem_bUnion] at x_in_filter,
      choose y y_in_prod x_eq_y using x_in_filter,
      rw [finset.mem_filter] at y_in_prod,
      cases y_in_prod with y_in_s yn,
      rw [finset.mem_singleton] at x_eq_y,
      have : x = y, from
      begin
        rw [prod.eq_iff_fst_eq_snd_eq],
        split,
        assumption,
        rw [xn, yn],
      end,
      rw [this],
      assumption, },
  end,

  split,
  apply s_eq_zw,

  rw [←simplex_disjoint_subset_unique, ←s_eq_zw],
  assumption,

  intro s_eq_zw,
  choose z w s_eq_zw using s_eq_zw,
  choose s_eq_zw z_sset_t w_sset_u using s_eq_zw,
  rw [finset.subset_iff],
  intros x x_in_s,
  rw [s_eq_zw] at x_in_s,
  rw [simplex_disjoint_mem] at *,
  cases x_in_s,

  left,
  cases x_in_s with x_in_t x0,
  split,
  rw [finset.subset_iff] at z_sset_t,
  specialize z_sset_t x_in_t,
  assumption,
  assumption,

  right,
  cases x_in_s with x_in_u x1,
  split,
  rw [finset.subset_iff] at w_sset_u,
  specialize w_sset_u x_in_u,
  assumption,
  assumption,
end

lemma simplex_disjoint_eq_unique
    (s t u w : finset α)
  : (s ⊔ₛ t) = (u ⊔ₛ w) ↔ s = u ∧ t = w
:= begin
  split,
  { intro H,
    repeat { rw [finset.subset.antisymm_iff] at * },
    cases H with st_sset_uw uw_sset_st,
    rw [simplex_disjoint_subset_unique] at *,
    tauto, },
  { intro H,
    repeat { rw [finset.subset.antisymm_iff] at * },
    repeat { rw [simplex_disjoint_subset_unique] },
    tauto, }
end

lemma simplex_disjoint_empty
    (s t : finset α)
  : (s ⊔ₛ t) = ∅ ↔ s = ∅ ∧ t = ∅
:= begin
  have H : (∅ : finset (α × ℕ)) = ((∅ : finset α) ⊔ₛ (∅ : finset α)), from
  begin
    simp,
    repeat { rw [finset.map_empty] },
  end,

  rw H,
  apply simplex_disjoint_eq_unique,
end

lemma simplex_disjoint_distr_union
    (s t u w : finset α)
  : (s ⊔ₛ t) ∪ (u ⊔ₛ w) = ((s ∪ u) ⊔ₛ (t ∪ w))
:= begin
  unfold simplex_disjoint_union,
  rw [←finset.union_assoc],
  rw [finset.union_assoc _ (finset.product t {1}) (finset.product u {0})],
  rw [finset.union_comm (finset.product t {1}) (finset.product u {0})],
  rw [←finset.union_assoc],
  rw [finset.union_assoc _ (finset.product t {1}) (finset.product w {1})],
  repeat { rw [finset.union_product] },
end

lemma simplex_disjoint_distr_inter
    (s t u w : finset α)
  : (s ⊔ₛ t) ∩ (u ⊔ₛ w) = ((s ∩ u) ⊔ₛ (t ∩ w))
:= begin
  unfold simplex_disjoint_union,
  repeat { rw [finset.inter_distrib_left] },
  repeat { rw [finset.inter_distrib_right] },

  have H_tu_empty : (finset.product t {1} : finset (α × ℕ)) ∩ (finset.product u {0} : finset (α × ℕ)) = ∅, from
  begin
    rw [←finset.disjoint_iff_inter_eq_empty],
    rw [finset.disjoint_product],
    right,
    rw [finset.disjoint_iff_inter_eq_empty],
    tauto,
  end,

  have H_sw_empty : (finset.product s {0} : finset (α × ℕ)) ∩ (finset.product w {1} : finset (α × ℕ)) = ∅, from
  begin
    rw [←finset.disjoint_iff_inter_eq_empty],
    rw [finset.disjoint_product],
    right,
    rw [finset.disjoint_iff_inter_eq_empty],
    tauto,
  end,

  rw [H_tu_empty, H_sw_empty],
  repeat { rw [finset.union_empty, finset.empty_union] },
  repeat { rw [finset.inter_product] },
end

lemma simplex_disjoint_card
    (s t : finset α)
  : (s ⊔ₛ t).card = s.card + t.card
:= begin
  simp only [simplex_disjoint_union],
  set s₀ : finset (α × ℕ) := s ×ˢ {0},
  set t₁ : finset (α × ℕ) := t ×ˢ {1},

  have card_disj : (s₀ ∪ t₁).card = s₀.card + t₁.card, from
  begin
    apply finset.card_union_eq,
    simp only [s₀, t₁, finset.disjoint_product, finset.disjoint_singleton],
    right,
    apply nat.zero_ne_one,
  end,
  simp only [card_disj, s₀, t₁, finset.card_product, finset.card_singleton, mul_one],
end

-- Define simplicial join.
@[simp]
def simplicial_join
    (X Y : simplicial_complex α)
  : simplicial_complex (α × ℕ) 
:= simplicial_complex.mk
    ({(s ⊔ₛ t) | (s ∈ X.simplices) (t ∈ Y.simplices)})
    (begin
      rw [set.nonempty_coe_sort, set.nonempty_def],
      use ∅,
      rw [set.mem_set_of],
      use ∅, split, apply simplicial_complex_empty_simplex,
      use ∅, split, apply simplicial_complex_empty_simplex,
      tauto,
    end)
    (begin
      unfold is_subset_closed,
      intros s s_in_XY t t_sset_s,
      rw [set.mem_set_of] at *,
      choose u Hu v Hv uv_eq_s using s_in_XY,
      rw [←uv_eq_s, simplex_disjoint_subset_sep] at t_sset_s,
      choose z w t_eq_zw using t_sset_s,
      choose t_eq_zw z_sset_u w_sset_v using t_eq_zw,

      use z, split,
      apply X.subset_closed u;
      assumption,

      use w, split,
      apply Y.subset_closed v;
      assumption,

      symmetry, assumption,
    end)
infixl ` ⋆ `:70 := simplicial_join

lemma simplicial_join_as_union
    (X Y : simplicial_complex α)
  : (X ⋆ Y).simplices = ⋃ (s ∈ X.simplices), ⋃ (t ∈ Y.simplices), {s ⊔ₛ t}
:= begin
  simp only [simplicial_join, set.ext_iff, set.mem_Union, set.mem_set_of, set.mem_singleton_iff],
  intro x,
  split,

  intro x_in_join,
  choose s s_in_X t t_in_Y st_eq_x using x_in_join,
  use s, split, assumption,
  use t, split, assumption,
  symmetry, assumption,

  intro x_in_union,
  choose s s_in_X t t_in_Y st_eq_x using x_in_union,
  use s, split, assumption,
  use t, split, assumption,
  symmetry, assumption,
end

-- Establish basic algebraic properties about joins.
instance simplicial_join.fintype
    (X : simplicial_complex α) [fintype X.simplices]
    (Y : simplicial_complex α) [fintype Y.simplices]
  : fintype (X ⋆ Y).simplices
:= begin
  rw [simplicial_join_as_union],
  apply set.fintype_bUnion,
  intros s s_in_X,

  apply set.fintype_bUnion,
  intros t t_in_Y,

  apply unique.fintype,
end

lemma simplicial_join_sep
    (X Y : simplicial_complex α)
    (s t : finset α)
  : (s ⊔ₛ t) ∈ (X ⋆ Y).simplices ↔ s ∈ X.simplices ∧ t ∈ Y.simplices
:= begin
  unfold simplicial_join,
  simp only[simplicial_complex.simplices],
  rw [set.mem_set_of],

  split,
  { intro st_in_XY,
    choose u Hu w Hw uw_eq_st using st_in_XY,
    rw [simplex_disjoint_eq_unique] at uw_eq_st,
    cases uw_eq_st with u_eq_s w_eq_t,
    split,
    rw [u_eq_s] at Hu,
    assumption,
    rw [w_eq_t] at Hw,
    assumption, },
  { intro st_in_XY,
    cases st_in_XY with s_in_X t_in_Y,
    use s, split, assumption,
    use t, split, assumption,
    refl, }
end

lemma simplicial_join_mem
    (X Y : simplicial_complex α)
    (s : finset (α × ℕ))
  : s ∈ (X ⋆ Y).simplices ↔ ∃ (t ∈ X.simplices) (u ∈ Y.simplices), s = (t ⊔ₛ u)
:= begin
  unfold simplicial_join,
  simp only[simplicial_complex.simplices],
  rw [set.mem_set_of],

  split,
  { intro s_in_XY,
    choose t Ht u Hu s_eq_tu using s_in_XY,
    use t, split, assumption,
    use u, split, assumption,
    symmetry,
    assumption, },
  { intro s_eq_tu,
    choose t Ht u Hu s_eq_tu using s_eq_tu,
    use t, split, assumption,
    use u, split, assumption,
    symmetry,
    assumption, }
end

lemma simplicial_join_incl_left
    (X Y : simplicial_complex α)
    (s : finset α)
  : s ∈ X.simplices → (s ⊔ₛ ∅) ∈ (X ⋆ Y).simplices
:= begin
  intro s_in_X,
  unfold simplicial_join,
  simp only[simplicial_complex.simplices],
  rw [set.mem_set_of],
  use s, split, assumption,
  use ∅, split, apply simplicial_complex_empty_simplex,
  refl,
end

lemma simplicial_join_incl_right
    (X Y : simplicial_complex α)
    (t : finset α)
  : t ∈ Y.simplices → (∅ ⊔ₛ t) ∈ (X ⋆ Y).simplices
:= begin
  intro t_in_Y,
  unfold simplicial_join,
  simp only[simplicial_complex.simplices],
  rw [set.mem_set_of],
  use ∅, split, apply simplicial_complex_empty_simplex,
  use t, split, assumption,
  refl,
end

lemma simplicial_join_vertices_mem_left
    (X Y : simplicial_complex α)
    (x : α)
  : (x, 0) ∈ vertices (X ⋆ Y) ↔ x ∈ vertices X
:= begin
  dsimp only[vertices, simplicial_join, simplicial_complex.simplices],
  repeat { rw [set.mem_Union] },
  
  split,
  { intro x0_in_XY,
    choose s s_lift Hs x0_in_s using x0_in_XY,
    rw [set.mem_set_of, set.mem_range] at Hs,
    choose Hs s_lifts using Hs,
    choose t Ht u Hu tu_eq_s using Hs,
    
    use t,
    rw [set.mem_Union],
    use Ht,
    have Hx_0 : (x, 0) ∈ s, from
    begin
      rw [←finset.mem_coe, s_lifts],
      assumption,
    end,
    rw [finset.mem_coe],
    rw [←tu_eq_s, simplex_disjoint_mem_left] at Hx_0,
    assumption, },
  { intro x_in_s,
    choose s s_lift Hs x_in_s using x_in_s,
    rw [set.mem_range] at Hs,
    choose Hs s_lifts using Hs,
    
    use (s ⊔ₛ ∅),
    rw [set.mem_set_of, set.mem_Union],
    have H_ex : ∃ (z : finset α) (Hz : z ∈ X.simplices)
                  (w : finset α) (Hw : w ∈ Y.simplices),
                 z ⊔ₛ w = s ⊔ₛ ∅, from
    begin
      use s, split, assumption,
      use ∅, split, apply simplicial_complex_empty_simplex,
      refl,
    end,
    use H_ex,
    rw [finset.mem_coe, simplex_disjoint_mem_left],
    have Hx : x ∈ s, from
    begin
      rw [←finset.mem_coe, s_lifts],
      assumption,
    end,
    assumption, }
end

lemma simplicial_join_vertices_mem_right
    (X Y : simplicial_complex α)
    (x : α)
  : (x, 1) ∈ vertices (X ⋆ Y) ↔ x ∈ vertices Y
:= begin
  dsimp only[vertices, simplicial_join, simplicial_complex.simplices],
  repeat { rw [set.mem_Union] },
  
  split,
  { intro x1_in_XY,
    choose s s_lift Hs x1_in_s using x1_in_XY,
    rw [set.mem_set_of, set.mem_range] at Hs,
    choose Hs s_lifts using Hs,
    choose t Ht u Hu tu_eq_s using Hs,
    
    use u,
    rw [set.mem_Union],
    use Hu,
    have Hx_1 : (x, 1) ∈ s, from
    begin
      rw [←finset.mem_coe, s_lifts],
      assumption,
    end,
    rw [finset.mem_coe],
    rw [←tu_eq_s, simplex_disjoint_mem_right] at Hx_1,
    assumption, },
  { intro x_in_s,
    choose s s_lift Hs x_in_s using x_in_s,
    rw [set.mem_range] at Hs,
    choose Hs s_lifts using Hs,
    
    use (∅ ⊔ₛ s),
    rw [set.mem_set_of, set.mem_Union],
    have H_ex : ∃ (z : finset α) (Hz : z ∈ X.simplices)
                  (w : finset α) (Hw : w ∈ Y.simplices),
                 z ⊔ₛ w = ∅ ⊔ₛ s, from
    begin
      use ∅, split, apply simplicial_complex_empty_simplex,
      use s, split, assumption,
      refl,
    end,
    use H_ex,
    rw [finset.mem_coe, simplex_disjoint_mem_right],
    have Hx : x ∈ s, from
    begin
      rw [←finset.mem_coe, s_lifts],
      assumption,
    end,
    assumption, }
end

lemma simplicial_join_mem_vertices
    (X Y : simplicial_complex α)
    (x : α × ℕ)
  : x ∈ vertices (X ⋆ Y) ↔ (x.fst ∈ vertices X ∧ x.snd = 0) ∨ (x.fst ∈ vertices Y ∧ x.snd = 1)
:= begin
  split,
  { intro x_in_XY,
    simp only[vertices, simplicial_join] at x_in_XY,
    rw [set.mem_Union] at x_in_XY,
    choose y x_in_XY using x_in_XY,
    rw [set.mem_Union] at x_in_XY,
    choose Hy x_in_y using x_in_XY,
    rw [set.mem_set_of] at Hy,
    choose s Hy using Hy,
    cases Hy with Hs Hy,
    choose t Hy using Hy,
    cases Hy with Ht st_eq_y,
    rw [finset.ext_iff] at st_eq_y,
    specialize st_eq_y x,
    cases st_eq_y with st_imp_y y_imp_st,
    rw [finset.mem_coe] at x_in_y,
    specialize y_imp_st x_in_y,
    rw [simplex_disjoint_mem] at y_imp_st,
    cases y_imp_st with x_in_s x_in_t,
    
    left,
    cases x_in_s with x_in_s x0,
    split,
    
    simp only[vertices],
    rw [set.mem_Union],
    use s,
    rw [set.mem_Union],
    use Hs,
    rw [finset.mem_coe],
    assumption,
    
    assumption,
    
    right,
    cases x_in_t with x_in_t x1,
    split,
    
    simp only[vertices],
    rw [set.mem_Union],
    use t,
    rw [set.mem_Union],
    use Ht,
    rw [finset.mem_coe],
    assumption,
    
    assumption, },
  { intro x_in_X_or_Y,
    cases x_in_X_or_Y with x_in_X x_in_Y,
    
    cases x_in_X with x_in_X x0,
    simp only[vertices] at *,
    rw [set.mem_Union] at *,
    choose s x_in_X using x_in_X,
    use (s ⊔ₛ ∅),
    rw [set.mem_Union] at *,
    choose Hs x_in_s using x_in_X,
    have Hs_incl : s ⊔ₛ ∅ ∈ (X ⋆ Y).simplices, from
    begin
      apply simplicial_join_incl_left,
      assumption,
    end,
    use Hs_incl,
    rw [finset.mem_coe, simplex_disjoint_mem],
    left,
    rw [finset.mem_coe] at x_in_s,
    split; assumption,
    
    cases x_in_Y with x_in_Y x1,
    simp only[vertices] at *,
    rw [set.mem_Union] at *,
    choose t x_in_Y using x_in_Y,
    use (∅ ⊔ₛ t),
    rw [set.mem_Union] at *,
    choose Ht x_in_t using x_in_Y,
    have Ht_incl : ∅ ⊔ₛ t ∈ (X ⋆ Y).simplices, from
    begin
      apply simplicial_join_incl_right,
      assumption,
    end,
    use Ht_incl,
    rw [finset.mem_coe, simplex_disjoint_mem],
    right,
    rw [finset.mem_coe] at x_in_t,
    split; assumption, }
end

def simplicial_join_iso_map
    (f g : α → β)
  : α × ℕ → β × ℕ
:= λ x : α × ℕ, if (x.snd = 0) then (f x.fst, x.snd) else (g x.fst, x.snd)

lemma simplicial_join_iso_simplicial
    (X Y : simplicial_complex α)
    (Z W : simplicial_complex β)
    (f : simplicial_map X Z)
    (g : simplicial_map Y W)
  : is_simplicial_map (X ⋆ Y) (Z ⋆ W) (simplicial_join_iso_map f.map g.map)
:= begin
  unfold is_simplicial_map,
  intros s s_in_XY,

  rw [simplicial_join_mem] at *,
  choose t Ht u Hu s_eq_tu using s_in_XY,

  use (finset.image f.map t), split,
  apply f.is_simplicial,
  assumption,

  use (finset.image g.map u), split,
  apply g.is_simplicial,
  assumption,

  rw [s_eq_tu],
  simp only[simplex_disjoint_union],
  rw [finset.image_union],

  rw [finset.ext_iff],
  intro x,
  split,
  { intro x_in_f,
    rw [finset.mem_union] at *,
    cases x_in_f,
    
    left,
    rw [finset.mem_product],
    rw [finset.mem_image] at *,
    choose y y_in_t0 using x_in_f,
    cases y_in_t0 with y_in_t0 fy_x,

    use y.fst,
    rw [finset.mem_product] at y_in_t0,
    cases y_in_t0 with y_in_t0 y_0,
    split,
    assumption,

    simp only [simplicial_join_iso_map] at fy_x,
    revert fy_x,
    split_ifs,
    
    intro y0_x,
    rw [←y0_x],
    
    rw [finset.mem_singleton] at y_0,
    contradiction,
    
    simp only [simplicial_join_iso_map] at fy_x,
    revert fy_x,
    split_ifs,
    
    intro y0_x,
    rw [finset.mem_singleton, ←y0_x],
    
    rw [finset.mem_product] at y_in_t0,
    cases y_in_t0 with y_in_t0 y_0,
    rw [finset.mem_singleton] at y_0,
    assumption,
    
    intro fy_x,
    rw [prod.eq_iff_fst_eq_snd_eq] at fy_x,
    cases fy_x with fy_x_fst fy_x_snd,
    simp at fy_x_snd,
    rw [finset.mem_singleton, ←fy_x_snd],
    finish,
    
    simp only [finset.mem_image, simplicial_join_iso_map] at x_in_f,
    choose y y_in_u fy_eq_x using x_in_f,
    revert fy_eq_x,
    split_ifs,
    
    rw [finset.mem_product, finset.mem_singleton] at y_in_u,
    choose y_in_u y_one using y_in_u,
    have contra : y.snd ≠ 0, by omega,
    contradiction,
    
    intro gy_eq_x,
    simp only [prod.ext_iff, prod.fst, prod.snd] at gy_eq_x,
    choose gy_eq_x x_one using gy_eq_x,
    rw [finset.mem_product, finset.mem_singleton] at y_in_u,
    choose y_in_u y_one using y_in_u,
    right,
    rw [finset.mem_product, finset.mem_image],
    split,
    use y.fst, split,
    assumption,
    assumption,
    rw [finset.mem_singleton, ←x_one],
    assumption, },

  { intro x_in_f_prod,
    rw [finset.mem_union] at *,
    cases x_in_f_prod,
    
    left,
    rw [finset.mem_product] at x_in_f_prod,
    cases x_in_f_prod with x_in_fxz x0,
    rw [finset.mem_image] at *,
    choose y y_in_t fxz_y using x_in_fxz,
    
    use (y, 0),
    split,

    rw [finset.mem_product],
    simp,
    assumption,
    
    simp only [simplicial_join_iso_map],
    split_ifs,
    
    rw [prod.eq_iff_fst_eq_snd_eq],
    split,
    assumption,
    rw [finset.mem_singleton] at x0,
    rw [x0],
    
    rw [prod.eq_iff_fst_eq_snd_eq],
    split,
    assumption,
    rw [finset.mem_singleton] at x0,
    rw [x0],
    
    right,
    rw [finset.mem_product] at x_in_f_prod,
    cases x_in_f_prod with x_in_fyw x1,
    rw [finset.mem_singleton] at x1,
    rw [finset.mem_image] at *,
    choose y y_in_u fyw_y using x_in_fyw,
    
    use (y, 1),
    split,
    
    rw [finset.mem_product],
    split,
    assumption,
    simp,
    
    simp only [simplicial_join_iso_map],
    split_ifs,
    
    finish,
    
    rw [prod.eq_iff_fst_eq_snd_eq],
    split,
    assumption,
    rw [x1], }
end

def simplicial_join_iso_inverse_map
    (f g : β → α)
  : β × ℕ → α × ℕ
:= λ x : β × ℕ, if (x.snd = 0) then (f x.fst, x.snd) else (g x.fst, x.snd)

-- TODO: Fix the proofs that f, g are simplicial.
--       Perhaps, move the function def's outside + proofs.
lemma simplicial_join_iso
    (X Y : simplicial_complex α)
    (Z W : simplicial_complex β)
  : X ≅ Z → Y ≅ W → X ⋆ Y ≅ Z ⋆ W
:= begin
  unfold is_simplicially_iso,
  unfold is_simplicial_iso,
  unfold is_inverse_simplicial_iso,
  simp only[simplicial_map.comp, simplicial_map.map],

  intros X_iso_Z Y_iso_W,
  choose f_xz g_zx fxz_inv_gzx using X_iso_Z,
  choose f_yw g_wy fyw_inv_gwy using Y_iso_W,

  cases fxz_inv_gzx with gzx_fxz_id fxz_gzx_id,
  cases fyw_inv_gwy with gwy_fyw_id fyw_gwy_id,

  let fs : simplicial_map (X ⋆ Y) (Z ⋆ W) :=
    simplicial_map.mk
      (simplicial_join_iso_map f_xz.map f_yw.map)
      (simplicial_join_iso_simplicial X Y Z W f_xz f_yw),

  let gs : simplicial_map (Z ⋆ W) (X ⋆ Y) :=
    simplicial_map.mk
      (simplicial_join_iso_map g_zx.map g_wy.map)
      (simplicial_join_iso_simplicial Z W X Y g_zx g_wy),

  use fs,
  use gs,
  simp only[simplicial_map.map],

  split; rw [function.funext_iff],
  { intro x,
    simp only[id, function.comp, simplicial_join_iso_map],
    simp at *,
    split_ifs;
    rw [prod.eq_iff_fst_eq_snd_eq],

    split,
    simp,
    rw [←function.comp_apply g_zx.map f_xz.map, gzx_fxz_id],
    simp,

    rw [←simplicial_join_vertices_mem_left _ Y],
    have x_in_XY : ↑x ∈ vertices (X ⋆ Y), from
    begin
      apply subtype.coe_prop,
    end,
    rw [←h],
    simp only[prod.mk.eta],
    assumption,
    
    split,
    simp,

    rw [←function.comp_apply g_wy.map f_yw.map, gwy_fyw_id],
    simp,
    
    rw [←simplicial_join_vertices_mem_right X],
    have x_in_XY : ↑x ∈ vertices (X ⋆ Y), from
    begin
      apply subtype.coe_prop,
    end,
    rw [simplicial_join_mem_vertices] at x_in_XY,
    cases x_in_XY,
    
    cases x_in_XY with x_in_X x0,
    contradiction,
    
    cases x_in_XY with x_in_Y x1,
    rw [←x1],
    simp only[prod.mk.eta],
    rw [simplicial_join_mem_vertices],
    right,
    split; assumption, },
  { intro x,
    simp only[id, function.comp, simplicial_join_iso_map],
    simp at *,
    split_ifs;
    rw [prod.eq_iff_fst_eq_snd_eq],

    split,
    simp,
    rw [←function.comp_apply f_xz.map g_zx.map, fxz_gzx_id],
    simp,

    rw [←simplicial_join_vertices_mem_left _ W],
    have x_in_XY : ↑x ∈ vertices (Z ⋆ W), from
    begin
      apply subtype.coe_prop,
    end,
    rw [←h],
    simp only[prod.mk.eta],
    assumption,
    
    split,
    simp,

    rw [←function.comp_apply f_yw.map g_wy.map, fyw_gwy_id],
    simp,
    
    rw [←simplicial_join_vertices_mem_right Z],
    have x_in_XY : ↑x ∈ vertices (Z ⋆ W), from
    begin
      apply subtype.coe_prop,
    end,
    rw [simplicial_join_mem_vertices] at x_in_XY,
    cases x_in_XY,
    
    cases x_in_XY with x_in_X x0,
    contradiction,
    
    cases x_in_XY with x_in_Y x1,
    rw [←x1],
    simp only[prod.mk.eta],
    rw [simplicial_join_mem_vertices],
    right,
    split; assumption, },
end

lemma simplicial_join_iso_left
    (X Y Z : simplicial_complex α)
  : X ≅ Y → X ⋆ Z ≅ Y ⋆ Z
:= begin
  intro X_iso_Y,
  apply simplicial_join_iso,
  assumption,
  refl,
end

lemma simplicial_join_iso_right
    (X Y Z : simplicial_complex α)
  : X ≅ Y → Z ⋆ X ≅ Z ⋆ Y
:= begin
  intro X_iso_Y,
  apply simplicial_join_iso,
  refl,
  assumption,
end

def simplicial_join_assoc_forward_aux
    (X Y Z : simplicial_complex α)
    (ψ : simplicial_coe (Y ⋆ Z) α)
  : α × ℕ → α × ℕ
:= λ x : α × ℕ, if (x.snd = 0) then x else (ψ.coe (x.fst, 0), x.snd)

def simplicial_join_assoc_forward_map
    (X Y Z : simplicial_complex α)
    (φ : simplicial_coe (X ⋆ Y) α)
    (ψ : simplicial_coe (Y ⋆ Z) α)
    (f : simplicial_map (φ[X ⋆ Y]) (X ⋆ Y))
  : α × ℕ → α × ℕ
:= λ x : α × ℕ, if (x.snd = 0)
    then ((simplicial_join_assoc_forward_aux X Y Z ψ) (f.map x.fst))
    else (ψ.coe x, x.snd)

-- set_option profiler true

lemma simplicial_join_assoc_forward_simplicial_left
    (X Y Z : simplicial_complex α)
    (φ : simplicial_coe (X ⋆ Y) α)
    (ψ : simplicial_coe (Y ⋆ Z) α)
    (f : simplicial_map (φ[X ⋆ Y]) (X ⋆ Y))
    (f_inv : is_inverse_simplicial_iso φ.simplicial_map f)
    (a b t : finset α)
    (a_in_X : a ∈ X.simplices)
    (b_in_Y : b ∈ Y.simplices)
    (t_in_Z : t ∈ Z.simplices)
  : finset.image
      (simplicial_join_assoc_forward_map X Y Z φ ψ f)
      (finset.image φ.coe (a ⊔ₛ b) ⊔ₛ t)
    ⊆ a ⊔ₛ finset.image ψ.coe (b ⊔ₛ t)
:= begin
  simp only [simplicial_join_assoc_forward_map, finset.subset_iff],
  intros x x_in_img,
  rw [finset.mem_image] at x_in_img,
  choose y y_in_u img_y_x using x_in_img,

  unfold is_inverse_simplicial_iso at f_inv,
  simp only [set.restrict_eq_restrict_iff, set.eq_on, simplicial_map.comp, function.comp_app, id.def] at f_inv,
  choose fφ_id φf_id using f_inv,
  
  simp only [simplex_disjoint_union, finset.mem_union, finset.mem_image, finset.mem_product, finset.mem_singleton],
  revert img_y_x,
  split_ifs,
  
  simp only [simplicial_join_assoc_forward_aux],
  have y_rw : y = (y.fst, 0), from
  begin
    simp only [prod.ext_iff],
    split, refl, assumption,
  end,
  rw [y_rw, simplex_disjoint_mem_left, finset.mem_image] at y_in_u,
  choose z z_in_ab coe_z_y using y_in_u,

  have z_in_join : z ∈ vertices (X ⋆ Y), from
  begin
    rw [vertex_iff_in_simplex],
    use (a ⊔ₛ b), split,
    rw [simplicial_join_mem],
    use a, split, assumption,
    use b, split, assumption,
    refl,
    assumption,
  end,
  specialize fφ_id z_in_join,
  have coe_rw : φ.simplicial_map.map = φ.coe, by refl,
  rw [coe_rw] at fφ_id,

  split_ifs,
  
  intro fy_x,
  left,
  rw [←coe_z_y, fφ_id] at fy_x h_1,
  subst fy_x,
  
  rw [simplex_disjoint_mem] at z_in_ab,
  cases z_in_ab with z_in_a contra,
  assumption,
  choose z_in_b contra using contra,
  have H : z.snd ≠ 0, by omega,
  contradiction,
  
  intro ψfy_x,
  right,
  rw [←coe_z_y, fφ_id] at ψfy_x h_1,
  subst ψfy_x,
  simp only [prod.fst, prod.snd],
  
  rw [simplex_disjoint_mem] at z_in_ab,
  cases z_in_ab with contra z_in_b,
  choose z_in_a contra using contra,
  contradiction,

  choose z_in_b z_one using z_in_b,
  split,
  
  use (z.fst, 0), split, left,
  simp only [prod.fst, prod.snd],
  split, assumption, refl,
  
  apply congr_arg, refl,
  assumption,
  
  intro ψy_x,
  right,
  rw [simplex_disjoint_mem] at y_in_u,
  cases y_in_u with contra y_in_t,
  choose y_in_a contra using contra,
  contradiction,
  
  choose y_in_t y_one using y_in_t,
  simp only [prod.ext_iff] at ψy_x,
  choose ψy_x x_one using ψy_x,
  rw [y_one, @comm _ eq] at x_one,
  split,
  
  use y, split,
  right, split; assumption,
  assumption,
  assumption,
end

lemma simplicial_join_assoc_forward_simplicial_right
    (X Y Z : simplicial_complex α)
    (φ : simplicial_coe (X ⋆ Y) α)
    (ψ : simplicial_coe (Y ⋆ Z) α)
    (f : simplicial_map (φ[X ⋆ Y]) (X ⋆ Y))
    (f_inv : is_inverse_simplicial_iso φ.simplicial_map f)
    (a b t : finset α)
    (a_in_X : a ∈ X.simplices)
    (b_in_Y : b ∈ Y.simplices)
    (t_in_Z : t ∈ Z.simplices)
  : a ⊔ₛ finset.image ψ.coe (b ⊔ₛ t)
    ⊆ finset.image
        (simplicial_join_assoc_forward_map X Y Z φ ψ f)
        (finset.image φ.coe (a ⊔ₛ b) ⊔ₛ t)
:= begin
  simp only [simplicial_join_assoc_forward_map, finset.subset_iff],
  intros x x_in_join,

  unfold is_inverse_simplicial_iso at f_inv,
  simp only [set.restrict_eq_restrict_iff, set.eq_on, simplicial_map.comp, function.comp_app, id.def] at f_inv,
  choose fφ_id φf_id using f_inv,
  
  simp only [simplex_disjoint_mem, finset.mem_image] at x_in_join,
  simp only [finset.mem_image, simplicial_join_assoc_forward_aux],
  cases x_in_join with x_in_a x_in_ψ,
  
  have x_in_XY : x ∈ vertices (X ⋆ Y), from
  begin
    rw [vertex_iff_in_simplex],
    use (a ⊔ₛ b), split,
    rw [simplicial_join_mem],
    use a, split, assumption,
    use b, split, assumption,
    refl,
    rw [simplex_disjoint_mem],
    left, assumption,
  end,
  specialize fφ_id x_in_XY,
  have coe_rw : φ.simplicial_map.map = φ.coe, by refl,
  rw [coe_rw] at fφ_id,

  use (φ.coe x, 0), split,
  rw [simplex_disjoint_mem_left],
  apply finset.mem_image_of_mem,
  rw [simplex_disjoint_mem],
  left, assumption,
  
  choose x_in_a x_zero using x_in_a,
  simp only [fφ_id, x_zero, eq_self_iff_true, if_true],
  
  choose x_in_ψ x_one using x_in_ψ,
  choose y y_in_bt ψy_x using x_in_ψ,
  cases y_in_bt with y_in_b y_in_t,
  
  choose y_in_b y_zero using y_in_b,
  use (φ.coe (y.fst, 1), 0), split,
  rw [simplex_disjoint_mem_left],
  apply finset.mem_image_of_mem,
  rw [simplex_disjoint_mem],
  right,
  simp only [prod.fst, prod.snd],
  split, assumption, refl,
  
  have y_in_XY : (y.fst, 1) ∈ vertices (X ⋆ Y), from
  begin
    rw [vertex_iff_in_simplex],
    use (a ⊔ₛ b), split,
    rw [simplicial_join_mem],
    use a, split, assumption,
    use b, split, assumption,
    refl,
    rw [simplex_disjoint_mem],
    simp only [prod.fst, prod.snd],
    right,
    split, assumption, refl,
  end,
  specialize fφ_id y_in_XY,
  have coe_rw : φ.simplicial_map.map = φ.coe, by refl,
  rw [coe_rw] at fφ_id,
  
  simp only [fφ_id, y_zero, eq_self_iff_true, if_true, nat.one_ne_zero, if_false],
  have y_rw : y = (y.fst, y.snd), from
  begin
    simp only [prod.ext_iff],
    split; refl,
  end,
  rw [y_rw] at ψy_x,
  rw [←y_zero, ←x_one, ψy_x],
  simp only [prod.ext_iff],
  split; refl,
  
  use y, split,
  rw [simplex_disjoint_mem],
  right, assumption,
  
  choose y_in_t y_one using y_in_t,
  simp only [y_one, nat.one_ne_zero, if_false, prod.ext_iff],
  rw [@comm _ eq] at x_one,
  split, assumption, assumption,
end

lemma simplicial_join_assoc_forward_simplicial
    (X Y Z : simplicial_complex α)
    (φ : simplicial_coe (X ⋆ Y) α)
    (ψ : simplicial_coe (Y ⋆ Z) α)
    (f : simplicial_map (φ[X ⋆ Y]) (X ⋆ Y))
    (f_inv : is_inverse_simplicial_iso φ.simplicial_map f)
  : is_simplicial_map (φ[X ⋆ Y] ⋆ Z) (X ⋆ ψ[Y ⋆ Z]) (simplicial_join_assoc_forward_map X Y Z φ ψ f)
:= begin
  simp only [is_simplicial_map],
  intros u u_in_join,
  rw [simplicial_join_mem] at u_in_join ⊢,
  choose s s_in_coe t t_in_z u_eq_st using u_in_join,
  simp only [simplicial_image, simplicial_join, set.mem_set_of] at s_in_coe,
  choose v v_in_join coe_v_s using s_in_coe,
  choose a a_in_X b b_in_Y ab_eq_v using v_in_join,
  subst ab_eq_v,
  subst coe_v_s,
  subst u_eq_st,
  
  use a, split, assumption,
  use (finset.image ψ.coe (b ⊔ₛ t)), split,
  simp only [simplicial_image, set.mem_set_of, simplicial_join_mem],
  use (b ⊔ₛ t), split,
  use b, split, assumption,
  use t, split, assumption,
  refl, refl,

  simp only [simplicial_join_assoc_forward_map, finset.ext_iff],
  intro x,
  split,

  apply simplicial_join_assoc_forward_simplicial_left;
  assumption,

  apply simplicial_join_assoc_forward_simplicial_right;
  assumption,
end

def simplicial_join_assoc_inv_aux
    (X Y Z : simplicial_complex α)
    (φ : simplicial_coe (X ⋆ Y) α)
  : α × ℕ → α × ℕ
:= λ x : α × ℕ, if (x.snd = 0) then (φ.coe (x.fst, 1), 0) else x

def simplicial_join_assoc_inv_map
    (X Y Z : simplicial_complex α)
    (φ : simplicial_coe (X ⋆ Y) α)
    (ψ : simplicial_coe (Y ⋆ Z) α)
    (g : simplicial_map (ψ[Y ⋆ Z]) (Y ⋆ Z))
  : α × ℕ → α × ℕ
:= λ x : α × ℕ, if (x.snd = 0)
    then (φ.coe x, 0)
    else ((simplicial_join_assoc_inv_aux X Y Z φ) (g.map x.fst))

lemma simplicial_join_assoc_inv_simplicial_left
    (X Y Z : simplicial_complex α)
    (φ : simplicial_coe (X ⋆ Y) α)
    (ψ : simplicial_coe (Y ⋆ Z) α)
    (g : simplicial_map (ψ[Y ⋆ Z]) (Y ⋆ Z))
    (g_inv : is_inverse_simplicial_iso ψ.simplicial_map g)
    (s a b : finset α)
    (s_in_X : s ∈ X.simplices)
    (a_in_Y : a ∈ Y.simplices)
    (b_in_Z : b ∈ Z.simplices)
  : finset.image
      (simplicial_join_assoc_inv_map X Y Z φ ψ g)
      (s ⊔ₛ finset.image ψ.coe (a ⊔ₛ b))
    ⊆ finset.image φ.coe (s ⊔ₛ a) ⊔ₛ b
:= begin
  simp only [simplicial_join_assoc_inv_map, finset.subset_iff],
  intros x x_in_img,

  unfold is_inverse_simplicial_iso at g_inv,
  simp only [set.restrict_eq_restrict_iff, set.eq_on, simplicial_map.comp, function.comp_app, id.def] at g_inv,
  choose gψ_id ψg_id using g_inv,

  simp only [finset.mem_image, simplex_disjoint_mem, simplicial_join_assoc_inv_map] at x_in_img,
  choose y y_in_join img_y_x using x_in_img,
  
  simp only [simplex_disjoint_union, finset.mem_union, finset.mem_image, finset.mem_product, finset.mem_singleton],
  revert img_y_x,
  split_ifs,
  
  cases y_in_join with y_in_s contra,
  intro φy_x,
  
  left,
  simp only [prod.ext_iff] at φy_x,
  choose φy_x x_zero using φy_x,
  rw [@comm _ eq] at x_zero,
  use y, split,
  left, assumption,
  assumption,
  assumption,
  
  choose y_in_coe contra using contra,
  have H : y.snd ≠ 0, by omega,
  contradiction,
  
  cases y_in_join with contra y_in_coe,
  choose y_in_s contra using contra,
  contradiction,
  
  choose y_in_coe y_one using y_in_coe,
  choose z z_in_join ψz_y using y_in_coe,
  simp only [simplicial_join_assoc_inv_aux],
  intro img_y_x,
  
  have z_in_YZ : z ∈ vertices (Y ⋆ Z), from
  begin
    rw [vertex_iff_in_simplex],
    use (a ⊔ₛ b), split,  
    rw [simplicial_join_mem],
    use a, split, assumption,
    use b, split, assumption,
    refl,
    rw [simplex_disjoint_mem],
    assumption,  
  end,
  specialize gψ_id z_in_YZ,
  have coe_rw : ψ.simplicial_map.map = ψ.coe, by refl,
  rw [coe_rw] at gψ_id,
  
  cases z_in_join with z_in_a z_in_b,
  
  left,
  choose z_in_a z_zero using z_in_a,
  simp only [←ψz_y, gψ_id, prod.ext_iff, z_zero, eq_self_iff_true, if_true] at img_y_x,
  choose φz_x x_zero using img_y_x,
  rw [@comm _ eq] at x_zero,
  split,
  use (z.fst, 1), split, right,
  simp only [prod.fst, prod.snd],
  split, assumption, refl,
  assumption,
  assumption,
  
  right,
  choose z_in_b z_one using z_in_b,
  simp only [←ψz_y, gψ_id, prod.ext_iff, z_one, nat.one_ne_zero, if_false] at img_y_x,
  choose z_eq_x x_one using img_y_x,
  rw [z_eq_x] at z_in_b,
  rw [@comm _ eq] at x_one,
  split; assumption,
end

lemma simplicial_join_assoc_inv_simplicial_right
    (X Y Z : simplicial_complex α)
    (φ : simplicial_coe (X ⋆ Y) α)
    (ψ : simplicial_coe (Y ⋆ Z) α)
    (g : simplicial_map (ψ[Y ⋆ Z]) (Y ⋆ Z))
    (g_inv : is_inverse_simplicial_iso ψ.simplicial_map g)
    (s a b : finset α)
    (s_in_X : s ∈ X.simplices)
    (a_in_Y : a ∈ Y.simplices)
    (b_in_Z : b ∈ Z.simplices)
  : finset.image φ.coe (s ⊔ₛ a) ⊔ₛ b
    ⊆ finset.image
        (simplicial_join_assoc_inv_map X Y Z φ ψ g)
        (s ⊔ₛ finset.image ψ.coe (a ⊔ₛ b))
:= begin
  simp only [simplicial_join_assoc_inv_map, finset.subset_iff],
  intros x x_in_join,

  unfold is_inverse_simplicial_iso at g_inv,
  simp only [set.restrict_eq_restrict_iff, set.eq_on, simplicial_map.comp, function.comp_app, id.def] at g_inv,
  choose gψ_id ψg_id using g_inv,

  simp only [simplex_disjoint_mem, finset.mem_image] at x_in_join,
  simp only [finset.mem_image, simplicial_join_assoc_inv_map],
  cases x_in_join with x_in_coe x_in_b,
  
  choose x_in_coe x_zero using x_in_coe,
  choose y y_in_join φy_x using x_in_coe,
  simp only [simplicial_join_assoc_inv_aux],
  cases y_in_join with y_in_s y_in_a,
  
  use y, split,
  rw [simplex_disjoint_mem],
  left, assumption,
  
  choose y_in_s y_zero using y_in_s,
  rw [@comm _ eq] at x_zero,
  simp only [y_zero, eq_self_iff_true, if_true, prod.ext_iff],
  split; assumption,
  
  choose y_in_a y_one using y_in_a,
  use (ψ.coe (y.fst, 0), 1), split,
  rw [simplex_disjoint_mem_right],
  apply finset.mem_image_of_mem,
  rw [simplex_disjoint_mem_left],
  assumption,

  have y_in_YZ : (y.fst, 0) ∈ vertices (Y ⋆ Z), from
  begin
    rw [vertex_iff_in_simplex],
    use (a ⊔ₛ b), split,
    rw [simplicial_join_mem],
    use a, split, assumption,
    use b, split, assumption,
    refl,
    rw [simplex_disjoint_mem_left],
    assumption,
  end,
  specialize gψ_id y_in_YZ,
  have coe_rw : ψ.simplicial_map.map = ψ.coe, by refl,
  rw [coe_rw] at gψ_id,
  
  simp only [y_one, gψ_id, nat.one_ne_zero, if_false, eq_self_iff_true, if_true],
  have y_rw : y = (y.fst, y.snd), from
  begin
    simp only [prod.ext_iff],
    split; refl,
  end,
  rw [y_rw] at φy_x,
  rw [←y_one, ←x_zero, φy_x],
  simp only [prod.ext_iff],
  split; refl,
  
  use (ψ.coe x, 1), split,
  rw [simplex_disjoint_mem_right],
  apply finset.mem_image_of_mem,
  rw [simplex_disjoint_mem],
  right, assumption,
  
  have x_in_YZ : x ∈ vertices (Y ⋆ Z), from
  begin
    rw [vertex_iff_in_simplex],
    use (a ⊔ₛ b), split,
    rw [simplicial_join_mem],
    use a, split, assumption,
    use b, split, assumption,
    refl,
    rw [simplex_disjoint_mem],
    right, assumption,
  end,
  specialize gψ_id x_in_YZ,
  have coe_rw : ψ.simplicial_map.map = ψ.coe, by refl,
  rw [coe_rw] at gψ_id,
  
  choose x_in_b x_one using x_in_b,
  simp only [simplicial_join_assoc_inv_aux],
  simp only [prod.snd, x_one, gψ_id, nat.one_ne_zero, if_false],
end

lemma simplicial_join_assoc_inv_simplicial
    (X Y Z : simplicial_complex α)
    (φ : simplicial_coe (X ⋆ Y) α)
    (ψ : simplicial_coe (Y ⋆ Z) α)
    (g : simplicial_map (ψ[Y ⋆ Z]) (Y ⋆ Z))
    (g_inv : is_inverse_simplicial_iso ψ.simplicial_map g)
  : is_simplicial_map (X ⋆ ψ[Y ⋆ Z]) (φ[X ⋆ Y] ⋆ Z) (simplicial_join_assoc_inv_map X Y Z φ ψ g)
:= begin
  simp only [is_simplicial_map],
  intros u u_in_join,
  rw [simplicial_join_mem] at u_in_join ⊢,
  choose s s_in_X t t_in_coe u_eq_st using u_in_join,
  simp only [simplicial_image, simplicial_join, set.mem_set_of] at t_in_coe,
  choose v v_in_join coe_v_s using t_in_coe,
  choose a a_in_Y b b_in_Z ab_eq_v using v_in_join,
  subst ab_eq_v,
  subst coe_v_s,
  subst u_eq_st,
  
  use (finset.image φ.coe (s ⊔ₛ a)), split,
  simp only [simplicial_image, set.mem_set_of, simplicial_join_mem],
  use (s ⊔ₛ a), split,
  use s, split, assumption,
  use a, split, assumption,
  refl, refl,
  use b, split, assumption,

  simp only [simplicial_join_assoc_forward_map, finset.ext_iff],
  intro x,
  split,

  apply simplicial_join_assoc_inv_simplicial_left;
  assumption,

  apply simplicial_join_assoc_inv_simplicial_right;
  assumption,
end

lemma simplicial_join_assoc
    [nonempty α]
    (X Y Z : simplicial_complex α)
    (φ : simplicial_coe (X ⋆ Y) α)
    (ψ : simplicial_coe (Y ⋆ Z) α)
  : φ[(X ⋆ Y)] ⋆ Z ≅ X ⋆ ψ[(Y ⋆ Z)]
:= begin
  have φ_iso : is_simplicial_iso φ.simplicial_map, by apply coe_is_iso,
  have ψ_iso : is_simplicial_iso ψ.simplicial_map, by apply coe_is_iso,

  unfold is_simplicial_iso at φ_iso ψ_iso,
  choose gXY gφ_inv using φ_iso,
  choose gYZ gψ_inv using ψ_iso,

  let f_assoc : simplicial_map (φ[X ⋆ Y] ⋆ Z) (X ⋆ ψ[Y ⋆ Z]) :=
    simplicial_map.mk
      (simplicial_join_assoc_forward_map X Y Z φ ψ gXY)
      (simplicial_join_assoc_forward_simplicial X Y Z φ ψ gXY gφ_inv),

  let g_assoc : simplicial_map (X ⋆ ψ[Y ⋆ Z]) (φ[X ⋆ Y] ⋆ Z) :=
    simplicial_map.mk
      (simplicial_join_assoc_inv_map X Y Z φ ψ gYZ)
      (simplicial_join_assoc_inv_simplicial X Y Z φ ψ gYZ gψ_inv),

  unfold is_inverse_simplicial_iso at gφ_inv gψ_inv,
  simp only [set.restrict_eq_restrict_iff, set.eq_on, simplicial_map.comp, function.comp_app, id.def] at gφ_inv gψ_inv,
  
  have φ_rw : φ.simplicial_map.map = φ.coe, by refl,
  have ψ_rw : ψ.simplicial_map.map = ψ.coe, by refl,
  simp only [φ_rw] at gφ_inv,
  simp only [ψ_rw] at gψ_inv,

  choose gφ_id φg_id using gφ_inv,
  choose gψ_id ψg_id using gψ_inv,

  unfold is_simplicially_iso,
  use f_assoc,

  unfold is_simplicial_iso,
  use g_assoc,

  unfold is_inverse_simplicial_iso,
  simp only [set.restrict_eq_restrict_iff, set.eq_on, simplicial_map.comp, function.comp_app, id.def],
  simp only [simplicial_join_assoc_forward_map, simplicial_join_assoc_inv_map],
  split,

  { intros x x_in_join,
    rw [vertex_iff_in_simplex] at x_in_join,
    choose u u_in_join x_in_u using x_in_join,
    simp only [simplicial_join_mem, simplicial_image, set.mem_set_of] at u_in_join,
    choose s s_in_coe t t_in_Z u_eq_st using u_in_join,
    choose v v_in_join coe_v_s using s_in_coe,
    choose a a_in_X b b_in_Y v_eq_ab using v_in_join,
    subst v_eq_ab,
    subst coe_v_s,
    subst u_eq_st,
    
    simp only [finset.mem_image, simplex_disjoint_mem] at x_in_u,
    cases x_in_u with x_in_coe x_in_t,
    
    choose x_in_coe x_zero using x_in_coe,
    choose y y_in_join φy_x using x_in_coe,
    simp only [←φy_x, x_zero, eq_self_iff_true, if_true],
    simp only [simplicial_join_assoc_forward_aux, simplicial_join_assoc_inv_aux],

    have y_in_XY : y ∈ vertices (X ⋆ Y), from
    begin
      rw [vertex_iff_in_simplex],
      use (a ⊔ₛ b), split,
      rw [simplicial_join_mem],
      use a, split, assumption,
      use b, split, assumption,
      refl,
      rw [simplex_disjoint_mem],
      assumption,
    end,
    specialize gφ_id y_in_XY,
    simp only [gφ_id],
    cases y_in_join with y_in_a y_in_b,
    
    choose y_in_a y_zero using y_in_a,
    simp only [y_zero, eq_self_iff_true, if_true, prod.snd, prod.ext_iff],
    rw [@comm _ eq] at x_zero,
    split; assumption,
    
    choose y_in_b y_one using y_in_b,
    have y_in_YZ : (y.fst, 0) ∈ vertices (Y ⋆ Z), from
    begin
      rw [simplicial_join_vertices_mem_left, vertex_iff_in_simplex],
      use b, split; assumption,
    end,
    specialize gψ_id y_in_YZ,
    simp only [gψ_id, y_one, eq_self_iff_true, if_true, nat.one_ne_zero, if_false, prod.snd, prod.ext_iff],
    have y_rw : y = (y.fst, y.snd), from
    begin
      simp only [prod.ext_iff],
      split; refl,
    end,
    rw [@comm _ eq] at x_zero,
    rw [←y_one, ←y_rw],
    split; assumption,
    
    have x_in_YZ : x ∈ vertices (Y ⋆ Z), from
    begin
      rw [vertex_iff_in_simplex],
      use (b ⊔ₛ t), split,
      rw [simplicial_join_mem],
      use b, split, assumption,
      use t, split, assumption,
      refl,
      rw [simplex_disjoint_mem],
      right, assumption,
    end,
    choose x_in_t x_one using x_in_t,
    specialize gψ_id x_in_YZ,
    simp only [simplicial_join_assoc_inv_aux],
    simp only [gψ_id, x_one, nat.one_ne_zero, if_false], },

  { intros x x_in_join,
    rw [vertex_iff_in_simplex] at x_in_join,
    choose u u_in_join x_in_u using x_in_join,
    simp only [simplicial_join_mem, simplicial_image, set.mem_set_of] at u_in_join,
    choose s s_in_X t t_in_coe u_eq_st using u_in_join,
    choose v v_in_join coe_v_t using t_in_coe,
    choose a a_in_X b b_in_Y v_eq_ab using v_in_join,
    subst v_eq_ab,
    subst coe_v_t,
    subst u_eq_st,
    
    simp only [finset.mem_image, simplex_disjoint_mem] at x_in_u,
    cases x_in_u with x_in_s x_in_coe,
    
    have x_in_XY : x ∈ vertices (X ⋆ Y), from
    begin
      rw [vertex_iff_in_simplex],
      use (s ⊔ₛ a), split,
      rw [simplicial_join_mem],
      use s, split, assumption,
      use a, split, assumption,
      refl,
      rw [simplex_disjoint_mem],
      left, assumption,
    end,
    choose x_in_s x_one using x_in_s,
    specialize gφ_id x_in_XY,
    simp only [simplicial_join_assoc_forward_aux],
    simp only [gφ_id, x_one, eq_self_iff_true, if_true],
    
    choose x_in_coe x_one using x_in_coe,
    choose y y_in_join ψy_x using x_in_coe,
    cases y_in_join with y_in_a y_in_b,
    
    have y_in_YZ : y ∈ vertices (Y ⋆ Z), from
    begin
      rw [vertex_iff_in_simplex],
      use (a ⊔ₛ b), split,
      rw [simplicial_join_mem],
      use a, split, assumption,
      use b, split, assumption,
      refl,
      rw [simplex_disjoint_mem],
      left, assumption,
    end,
    choose y_in_a y_zero using y_in_a,
    specialize gψ_id y_in_YZ,

    have y_in_XY : (y.fst, 1) ∈ vertices (X ⋆ Y), from
    begin
      rw [simplicial_join_vertices_mem_right, vertex_iff_in_simplex],
      use a, split; assumption,
    end,
    specialize gφ_id y_in_XY,

    simp only [simplicial_join_assoc_forward_aux, simplicial_join_assoc_inv_aux],
    simp only [←ψy_x, gψ_id, gφ_id, y_zero, x_one, eq_self_iff_true, if_true, nat.one_ne_zero, if_false, prod.snd],
    have y_rw : y = (y.fst, y.snd), from
    begin
      simp only [prod.ext_iff],
      split; refl,
    end,
    rw [←y_zero, ←y_rw],
    rw [@comm _ eq] at x_one,
    simp only [prod.ext_iff],
    split; assumption,
    
    have y_in_YZ : y ∈ vertices (Y ⋆ Z), from
    begin
      rw [vertex_iff_in_simplex],
      use (a ⊔ₛ b), split,
      rw [simplicial_join_mem],
      use a, split, assumption,
      use b, split, assumption,
      refl,
      rw [simplex_disjoint_mem],
      right, assumption,
    end,
    choose y_in_b y_one using y_in_b,
    specialize gψ_id y_in_YZ,
    
    simp only [simplicial_join_assoc_forward_aux, simplicial_join_assoc_inv_aux],
    simp only [←ψy_x, gψ_id, y_one, x_one, nat.one_ne_zero, if_false, prod.ext_iff],
    split; refl, },
end

def simplicial_join_comm_map
  : α × ℕ → α × ℕ
:= λ x : α × ℕ, if (x.snd = 0) then (x.fst, 1) else (x.fst, 0)

lemma simplicial_join_comm_simplicial
    (X Y : simplicial_complex α)
  : is_simplicial_map (X ⋆ Y) (Y ⋆ X) (simplicial_join_comm_map)
:= begin
  simp only [is_simplicial_map, simplicial_join, set.mem_set_of],
  intros u u_in_XY,
  choose s s_in_X t t_in_Y st_eq_u using u_in_XY,

  use t, split, assumption,
  use s, split, assumption,

  simp only [simplicial_join_comm_map, finset.ext_iff],
  intro x, split,

  { intro x_in_ts,
    rw [simplex_disjoint_mem] at x_in_ts,
    rw [finset.mem_image],
    cases x_in_ts with x_in_t x_in_s,
    
    choose x_in_t x_zero using x_in_t,
    use (x.fst, 1), split,
    rw [←st_eq_u, simplex_disjoint_mem_right],
    assumption,
    
    simp only [nat.one_ne_zero, if_false],
    simp only [←x_zero, prod.ext_iff],
    split; refl,
    
    choose x_in_s x_one using x_in_s,
    use (x.fst, 0), split,
    rw [←st_eq_u, simplex_disjoint_mem_left],
    assumption,
    
    simp only [eq_self_iff_true, if_true],
    simp only [←x_one, prod.ext_iff],
    split; refl, },

  { intro x_in_img,
    rw [finset.mem_image] at x_in_img,
    rw [simplex_disjoint_mem],
    choose y y_in_u fy_eq_x using x_in_img,
    revert fy_eq_x,
    split_ifs,
    
    intro y_one_x,
    simp only [prod.ext_iff, prod.fst, prod.snd] at y_one_x,
    choose y_eq_x x_one using y_one_x,
    rw [@comm _ eq] at x_one,
    rw [←st_eq_u, simplex_disjoint_mem] at y_in_u,
    cases y_in_u with y_in_s contra,
    
    choose y_in_s y_zero using y_in_s,
    rw [y_eq_x] at y_in_s,
    right, split; assumption,
    
    choose y_in_t contra using contra,
    have H : y.snd ≠ 0, by omega,
    contradiction,
    
    intro y_zero_x,
    simp only [prod.ext_iff, prod.fst, prod.snd] at y_zero_x,
    choose y_eq_x x_zero using y_zero_x,
    rw [@comm _ eq] at x_zero,
    rw [←st_eq_u, simplex_disjoint_mem] at y_in_u,
    cases y_in_u with contra y_in_t,
    
    choose y_in_s contra using contra,
    contradiction,
    
    choose y_in_t y_one using y_in_t,
    rw [y_eq_x] at y_in_t,
    left, split; assumption, },
end

lemma simplicial_join_comm
    (X Y : simplicial_complex α)
  : X ⋆ Y ≅ Y ⋆ X
:= begin
  let f : simplicial_map (X ⋆ Y) (Y ⋆ X) :=
    simplicial_map.mk
      (simplicial_join_comm_map)
      (simplicial_join_comm_simplicial X Y),

  let g : simplicial_map (Y ⋆ X) (X ⋆ Y) :=
    simplicial_map.mk
      (simplicial_join_comm_map)
      (simplicial_join_comm_simplicial Y X),

  unfold is_simplicially_iso,
  use f,
  
  unfold is_simplicial_iso,
  use g,

  unfold is_inverse_simplicial_iso,
  split;

  { simp only [set.restrict_eq_restrict_iff, set.eq_on],
    intros x x_in_XY,
    rw [simplicial_join_mem_vertices] at x_in_XY,
    simp only [f, g, simplicial_map.comp, simplicial_join_comm_map, id.def, function.comp_app],
    cases x_in_XY with x_in_X x_in_Y,
    
    choose x_in_X x_zero using x_in_X,
    simp only [x_zero, eq_self_iff_true, if_true, nat.one_ne_zero, if_false],
    simp only [←x_zero, prod.ext_iff, prod.fst, prod.snd],
    split; refl,
    
    choose x_in_Y x_one using x_in_Y,
    simp only [x_one, eq_self_iff_true, if_true, nat.one_ne_zero, if_false],
    simp only [←x_one, prod.ext_iff, prod.fst, prod.snd],
    split; refl, },
end

-- Make sense of natural projections, inclusions, etc.
def simplicial_join_id_forward_map
  : α × ℕ → α
:= λ x : α × ℕ, x.fst

lemma simplicial_join_id_left_forward_simplicial
    (X : simplicial_complex α)
  : is_simplicial_map (X ⋆ empty_sc) X simplicial_join_id_forward_map
:= begin
  simp only [is_simplicial_map, simplicial_join_id_forward_map, empty_sc],
  intros u u_in_X_empty,
  rw [simplicial_join_mem] at u_in_X_empty,
  choose s s_in_X t t_in_empty st_eq_u using u_in_X_empty,

  rw [set.mem_singleton_iff] at t_in_empty,
  simp only [t_in_empty, simplex_disjoint_union, finset.empty_product, finset.union_empty] at st_eq_u,
  simp only [st_eq_u],
  
  have s_img : finset.image prod.fst (s ×ˢ {0}) = s, from
  begin
    simp only [finset.ext_iff, finset.mem_image],
    intro x,
    split,

    intro x_in_img,
    choose y y_in_prod proj_y_x using x_in_img,
    rw [finset.mem_product] at y_in_prod,
    choose y_in_s y_zero using y_in_prod,
    rw [←proj_y_x],
    assumption,

    intro x_in_s,
    use (x, 0), split,
    simp only [finset.mem_product, prod.fst, prod.snd],
    split,
    assumption,
    apply finset.mem_singleton_self,

    simp only [prod.fst],
  end,

  rw [s_img],
  assumption,
end

def simplicial_join_id_left_inverse_map
  : α → α × ℕ
:= λ x : α, (x, 0)

lemma simplicial_join_id_left_inverse_simplicial
    (X : simplicial_complex α)
  : is_simplicial_map X (X ⋆ empty_sc) (simplicial_join_id_left_inverse_map)
:= begin
  simp only [is_simplicial_map],
  intros u u_in_X,
  simp only [simplicial_join, empty_sc, set.mem_set_of],

  use u, split, assumption,
  use ∅, split, apply simplicial_complex_empty_simplex,

  have u_img : finset.image simplicial_join_id_left_inverse_map u = u ×ˢ {0}, from
  begin
    simp only [simplicial_join_id_left_inverse_map, finset.ext_iff, finset.mem_image, finset.mem_product],
    intro x,
    split,

    intro x_in_img,
    choose y y_in_u inj_y_x using x_in_img,
    simp only [prod.ext_iff, prod.fst, prod.snd] at inj_y_x,
    choose y_eq_x x_zero using inj_y_x,
    rw [@comm _ eq, ←finset.mem_singleton] at x_zero,
    rw [y_eq_x] at y_in_u,
    split; assumption,

    intro x_in_prod,
    choose x_in_u x_zero using x_in_prod,
    rw [finset.mem_singleton, @comm _ eq] at x_zero,
    use x.fst, split, assumption,
    simp only [prod.ext_iff, prod.fst, prod.snd],
    split, refl, assumption,
  end,

  simp only [u_img, simplex_disjoint_union, finset.empty_product, finset.union_empty],
end

lemma simplicial_join_id_left
    (X : simplicial_complex α)
  : X ⋆ empty_sc ≅ X
:= begin
  let f : simplicial_map (X ⋆ empty_sc) X :=
    simplicial_map.mk
      (simplicial_join_id_forward_map)
      (simplicial_join_id_left_forward_simplicial X),

  let g : simplicial_map X (X ⋆ empty_sc) :=
    simplicial_map.mk
      (simplicial_join_id_left_inverse_map)
      (simplicial_join_id_left_inverse_simplicial X),

  unfold is_simplicially_iso,
  use f,

  unfold is_simplicial_iso,
  use g,

  unfold is_inverse_simplicial_iso,
  split,

  { simp only [set.restrict_eq_restrict_iff, set.eq_on],
    intros x x_in_X_empty,
    rw [simplicial_join_mem_vertices] at x_in_X_empty,
    simp only [f, g, simplicial_join_id_forward_map, simplicial_join_id_left_inverse_map],
    simp only [simplicial_map.comp, function.comp_app, id.def, prod.ext_iff, prod.fst, prod.snd],
    cases x_in_X_empty with x_in_X contra,
    
    choose x_in_X x_zero using x_in_X,
    rw [@comm _ eq] at x_zero,
    split,
    refl,
    assumption,
    
    choose contra x_one using contra,
    rw [empty_sc_vertices] at contra,
    have H : x.fst ∉ ∅, by apply set.not_mem_empty x.fst,
    contradiction, },

  { simp only [set.restrict_eq_restrict_iff, set.eq_on],
    intros x x_in_X,
    simp only [f, g, simplicial_join_id_forward_map, simplicial_join_id_left_inverse_map],
    simp only [simplicial_map.comp, function.comp_app, id.def], },
end

lemma simplicial_join_id_right_forward_simplicial
    (X : simplicial_complex α)
  : is_simplicial_map (empty_sc ⋆ X) X simplicial_join_id_forward_map
:= begin
  simp only [is_simplicial_map, simplicial_join_id_forward_map, empty_sc],
  intros u u_in_empty_X,
  rw [simplicial_join_mem] at u_in_empty_X,
  choose s s_in_empty t t_in_X st_eq_u using u_in_empty_X,

  rw [set.mem_singleton_iff] at s_in_empty,
  simp only [s_in_empty, simplex_disjoint_union, finset.empty_product, finset.empty_union] at st_eq_u,
  simp only [st_eq_u],
  
  have t_img : finset.image prod.fst (t ×ˢ {1}) = t, from
  begin
    simp only [finset.ext_iff, finset.mem_image],
    intro x,
    split,

    intro x_in_img,
    choose y y_in_prod proj_y_x using x_in_img,
    rw [finset.mem_product] at y_in_prod,
    choose y_in_s y_zero using y_in_prod,
    rw [←proj_y_x],
    assumption,

    intro x_in_t,
    use (x, 1), split,
    simp only [finset.mem_product, prod.fst, prod.snd],
    split,
    assumption,
    apply finset.mem_singleton_self,

    simp only [prod.fst],
  end,

  rw [t_img],
  assumption,
end

def simplicial_join_id_right_inverse_map
  : α → α × ℕ
:= λ x : α, (x, 1)

lemma simplicial_join_id_right_inverse_simplicial
    (X : simplicial_complex α)
  : is_simplicial_map X (empty_sc ⋆ X) simplicial_join_id_right_inverse_map
:= begin
  simp only [is_simplicial_map],
  intros u u_in_X,
  simp only [simplicial_join, empty_sc, set.mem_set_of],

  use ∅, split, apply simplicial_complex_empty_simplex,
  use u, split, assumption,

  have u_img : finset.image simplicial_join_id_right_inverse_map u = u ×ˢ {1}, from
  begin
    simp only [simplicial_join_id_right_inverse_map, finset.ext_iff, finset.mem_image, finset.mem_product],
    intro x,
    split,

    intro x_in_img,
    choose y y_in_u inj_y_x using x_in_img,
    simp only [prod.ext_iff, prod.fst, prod.snd] at inj_y_x,
    choose y_eq_x x_zero using inj_y_x,
    rw [@comm _ eq, ←finset.mem_singleton] at x_zero,
    rw [y_eq_x] at y_in_u,
    split; assumption,

    intro x_in_prod,
    choose x_in_u x_zero using x_in_prod,
    rw [finset.mem_singleton, @comm _ eq] at x_zero,
    use x.fst, split, assumption,
    simp only [prod.ext_iff, prod.fst, prod.snd],
    split, refl, assumption,
  end,

  simp only [u_img, simplex_disjoint_union, finset.empty_product, finset.empty_union],
end

lemma simplicial_join_id_right
    (X : simplicial_complex α)
  : empty_sc ⋆ X ≅ X
:= begin
  let f : simplicial_map (empty_sc ⋆ X) X :=
    simplicial_map.mk
      (simplicial_join_id_forward_map)
      (simplicial_join_id_right_forward_simplicial X),

  let g : simplicial_map X (empty_sc ⋆ X) :=
    simplicial_map.mk
      (simplicial_join_id_right_inverse_map)
      (simplicial_join_id_right_inverse_simplicial X),

  unfold is_simplicially_iso,
  use f,

  unfold is_simplicial_iso,
  use g,

  unfold is_inverse_simplicial_iso,
  split,

  { simp only [set.restrict_eq_restrict_iff, set.eq_on],
    intros x x_in_empty_X,
    rw [simplicial_join_mem_vertices] at x_in_empty_X,
    simp only [f, g, simplicial_join_id_forward_map, simplicial_join_id_right_inverse_map],
    simp only [simplicial_map.comp, function.comp_app, id.def, prod.ext_iff, prod.fst, prod.snd],
    cases x_in_empty_X with contra x_in_X,

    choose contra x_one using contra,
    rw [empty_sc_vertices] at contra,
    have H : x.fst ∉ ∅, by apply set.not_mem_empty x.fst,
    contradiction,
    
    choose x_in_X x_zero using x_in_X,
    rw [@comm _ eq] at x_zero,
    split,
    refl,
    assumption, },

  { simp only [set.restrict_eq_restrict_iff, set.eq_on],
    intros x x_in_X,
    simp only [f, g, simplicial_join_id_forward_map, simplicial_join_id_right_inverse_map],
    simp only [simplicial_map.comp, function.comp_app, id.def], },
end

lemma simplicial_join_natural_incl_left
    (X Y : simplicial_complex α)
    (t : finset α)
  : t ∈ Y.simplices ↔ X ⋆ simplex t ⊆ X ⋆ Y
:= begin
  simp only [simplicial_join, is_subcomplex, set.subset_def, set.mem_set_of],
  split,

  -- t ∈ Y case.
  intros t_in_Y u u_in_join,
  choose s s_in_X v v_in_Y sv_eq_u using u_in_join,

  use s, split, assumption,
  use v, split,
  apply simplex_if_in_subcomplex (simplex t),
  assumption,
  rw [←simplex_iff_subcomplex_mem],
  assumption,
  assumption,

  -- X ⋆ t ⊆ X ⋆ Y case.
  intros X_sub_Y,
  specialize X_sub_Y (∅ ⊔ₛ t),

  have X_mem : ∃ (s : finset α) (H : s ∈ X.simplices) (v : finset α) (H : v ∈ (simplex t).simplices),
      s ⊔ₛ v = ∅ ⊔ₛ t, from
  begin
    use ∅, split, apply simplicial_complex_empty_simplex,
    use t, split,
    simp only [simplex, finset.mem_coe],
    apply finset.mem_powerset_self,
    refl,
  end,
  specialize X_sub_Y X_mem,

  choose s s_in_X v v_in_Y sv_eq_t using X_sub_Y,
  rw [simplex_disjoint_eq_unique] at sv_eq_t,
  choose s_empty v_eq_t using sv_eq_t,
  subst v_eq_t,
  assumption,
end

lemma simplicial_join_natural_incl_right
    (X Y : simplicial_complex α)
    (s : finset α)
  : s ∈ X.simplices ↔ simplex s ⋆ Y ⊆ X ⋆ Y
:= begin
  simp only [simplicial_join, is_subcomplex, set.subset_def, set.mem_set_of],
  split,

  -- s ∈ X case.
  intros s_in_X u u_in_join,
  choose t t_in_X v v_in_Y tv_eq_u using u_in_join,

  use t, split,
  apply simplex_if_in_subcomplex (simplex s),
  assumption,
  rw [←simplex_iff_subcomplex_mem],
  assumption,
  use v, split,
  assumption,
  assumption,

  -- X ⋆ t ⊆ X ⋆ Y case.
  intros X_sub_Y,
  specialize X_sub_Y (s ⊔ₛ ∅),

  have Y_mem : ∃ (t : finset α) (H : t ∈ (simplex s).simplices) (v : finset α) (H : v ∈ Y.simplices),
      t ⊔ₛ v = s ⊔ₛ ∅, from
  begin
    use s, split,
    simp only [simplex, finset.mem_coe],
    apply finset.mem_powerset_self,

    use ∅, split, apply simplicial_complex_empty_simplex,

    refl,
  end,
  specialize X_sub_Y Y_mem,

  choose t t_in_X v v_in_Y tv_eq_s using X_sub_Y,
  rw [simplex_disjoint_eq_unique] at tv_eq_s,
  choose s_eq_t v_empty using tv_eq_s,
  subst s_eq_t,
  assumption,
end

lemma simplicial_join_subcomplex
    (X Y Z W : simplicial_complex α)
    (X_subcomp_Z : X ⊆ Z)
    (Y_subcomp_W : Y ⊆ W)
  : X ⋆ Y ⊆ Z ⋆ W
:= begin
  simp only [simplicial_complex.has_subset, is_subcomplex] at *,
  simp only [simplicial_join, simplicial_complex.simplices],
  simp only [set.subset_def] at *,

  intros s s_in_XY,
  simp only [set.mem_set_of] at *,
  choose t Ht u Hu tu_eq_s using s_in_XY,
  specialize X_subcomp_Z t Ht,
  specialize Y_subcomp_W u Hu,

  use t, split, apply X_subcomp_Z,
  use u, split, apply Y_subcomp_W,
  apply tu_eq_s,
end

lemma simplicial_join_distr_union_left
    (X Y Z : simplicial_complex α)
  : (X ⋆ (Y ∪ Z)).simplices = ((X ⋆ Y) ∪ (X ⋆ Z)).simplices
:= begin
  simp only [simplicial_join, simplicial_union, set.ext_iff, set.mem_union, set.mem_set_of],
  intro u,
  split,

  { intro u_in_join,
    choose s s_in_X t t_in_YZ st_eq_u using u_in_join,
    cases t_in_YZ with t_in_Y t_in_Z,
    
    left,
    use s, split, assumption,
    use t, split, assumption,
    assumption,
    
    right,
    use s, split, assumption,
    use t, split, assumption,
    assumption, },

  { intro u_in_union,
    cases u_in_union with u_in_XY u_in_XZ,
    
    choose s s_in_X t t_in_Y st_eq_u using u_in_XY,
    use s, split, assumption,
    use t, split,
    left, assumption,
    assumption,
    
    choose s s_in_X t t_in_Z st_eq_u using u_in_XZ,
    use s, split, assumption,
    use t, split,
    right, assumption,
    assumption, },
end

lemma simplicial_join_distr_union_left_iso
    (X Y Z : simplicial_complex α)
  : X ⋆ (Y ∪ Z) ≅ (X ⋆ Y) ∪ (X ⋆ Z)
:= begin
  apply simplicial_iso_preserves_equiv,
  apply simplicial_join_distr_union_left,
end

lemma simplicial_join_distr_union_right
    (X Y Z : simplicial_complex α)
  : ((Y ∪ Z) ⋆ X).simplices = ((Y ⋆ X) ∪ (Z ⋆ X)).simplices
:= begin
  simp only [simplicial_join, simplicial_union, set.ext_iff, set.mem_union, set.mem_set_of],
  intro u,
  split,

  { intro u_in_join,
    choose s s_in_YZ t t_in_X st_eq_u using u_in_join,
    cases s_in_YZ with s_in_Y s_in_Z,
    
    left,
    use s, split, assumption,
    use t, split, assumption,
    assumption,
    
    right,
    use s, split, assumption,
    use t, split, assumption,
    assumption, },

  { intro u_in_union,
    cases u_in_union with u_in_XY u_in_XZ,
    
    choose s s_in_X t t_in_Y st_eq_u using u_in_XY,
    use s, split,
    left, assumption,
    use t, split, assumption,
    assumption,
    
    choose s s_in_X t t_in_Z st_eq_u using u_in_XZ,
    use s, split,
    right, assumption,
    use t, split, assumption,
    assumption, },
end

lemma simplicial_join_distr_union_right_iso
    (X Y Z : simplicial_complex α)
  : (Y ∪ Z) ⋆ X ≅ (Y ⋆ X) ∪ (Z ⋆ X)
:= begin
  apply simplicial_iso_preserves_equiv,
  apply simplicial_join_distr_union_right,
end

-- Lemma 2.1, p.5
lemma dim_of_join
    (X Y : simplicial_complex α) [fintype X.simplices] [fintype Y.simplices]
  : dim_of_complex (X ⋆ Y) = (dim_of_complex X) + (dim_of_complex Y) + 1
:= begin
  intros,
  set k := dim_of_complex (X ⋆ Y),
  set n := dim_of_complex X,
  set m := dim_of_complex Y,

  rw [le_antisymm_iff],
  split,

  { have k_dim : k ∈ finset.image dim (X ⋆ Y).simplices.to_finset, by apply finset.max'_mem,
    simp only [finset.mem_image, set.mem_to_finset] at k_dim,
    choose u u_in_XY dim_u_k using k_dim,
    rw [simplicial_join_mem] at u_in_XY,
    choose s s_in_X t t_in_Y u_eq_st using u_in_XY,
    
    rw [←dim_u_k, dim, u_eq_st, simplex_disjoint_card],
    have st_dim : ↑(s.card + t.card) - 1 = dim s + dim t + 1, by {simp, linarith, },
    rw [st_dim],
    
    have s_le_dim : dim s ≤ dim_of_complex X, from
    begin
      apply finset.le_max',
      simp only [finset.mem_image, set.mem_to_finset],
      use s, split, assumption,
      refl,
    end,
    
    have t_le_dim : dim t ≤ dim_of_complex Y, from
    begin
      apply finset.le_max',
      simp only [finset.mem_image, set.mem_to_finset],
      use t, split, assumption,
      refl,
    end,
    
    linarith, },

  { have n_dim : n ∈ finset.image dim X.simplices.to_finset, by apply finset.max'_mem,
    have m_dim : m ∈ finset.image dim Y.simplices.to_finset, by apply finset.max'_mem,
    simp only [finset.mem_image, set.mem_to_finset] at n_dim m_dim,
    
    choose s s_in_X dim_s_n using n_dim,
    choose t t_in_Y dim_t_m using m_dim,
    have st_dim : ↑(s.card + t.card) - 1 = dim s + dim t + 1, by {simp, linarith, },
    simp only [←dim_s_n, ←dim_t_m, ←st_dim, ←simplex_disjoint_card],
    
    apply finset.le_max',
    simp only [finset.mem_image, set.mem_to_finset],
    use (s ⊔ₛ t), split,
    
    rw [simplicial_join_mem],
    use s, split, assumption,
    use t, split, assumption,
    refl,
    
    unfold dim, },
end

-- Show that, for disjoint complexes, projection to the first coordinate is a coercion.

lemma join_fst_proj_is_coe
    (X Y : simplicial_complex α)
  : disjoint (vertices X) (vertices Y) → set.inj_on (prod.fst) (vertices (X ⋆ Y))
:= begin
  intro X_disj_Y,
  simp only [set.inj_on, vertices_set_of, simplicial_join, set.mem_set_of],
  simp only [vertices_set_of, set.disjoint_iff_forall_ne, set.mem_set_of] at X_disj_Y,

  intros x₁ x₁_in_lhs x₂ x₂_in_rhs,

  choose s₁ s₁_in_join x₁_in_s₁ using x₁_in_lhs,
  choose u₁ u₁_in_X v₁ v₁_in_Y uv₁_eq_s₁ using s₁_in_join,
  rw [←uv₁_eq_s₁, simplex_disjoint_mem] at x₁_in_s₁,

  choose s₂ s₂_in_join x₂_in_s₂ using x₂_in_rhs,
  choose u₂ u₂_in_X v₂ v₂_in_Y uv₂_eq_s₂ using s₂_in_join,
  rw [←uv₂_eq_s₂, simplex_disjoint_mem] at x₂_in_s₂,

  cases x₁_in_s₁ with x₁_in_X x₁_in_Y;
  cases x₂_in_s₂ with x₂_in_X x₂_in_Y,

  -- x₁, x₂ ∈ X case.
  intros x₁_eq_x₂,

  choose x₁_in_u₁ x₁_zero using x₁_in_X,
  choose x₂_in_u₂ x₂_zero using x₂_in_X,
  rw [←x₂_zero] at x₁_zero,
  rw [prod.ext_iff],
  split; assumption,

  -- x₁ ∈ X, x₂ ∈ Y case.
  contrapose,
  intros x₁_neq_x₂,

  choose x₁_in_u₁ x₁_zero using x₁_in_X,
  choose x₂_in_v₂ x₂_one using x₂_in_Y,

  have H₁ : ∃ (s : finset α) (H : s ∈ X.simplices), x₁.fst ∈ s, from
  begin
    use u₁, split; assumption,
  end, 
  specialize X_disj_Y x₁.fst H₁,

  have H₂ : ∃ (s : finset α) (H : s ∈ Y.simplices), x₂.fst ∈ s, from
  begin
    use v₂, split; assumption,
  end,
  specialize X_disj_Y x₂.fst H₂,

  assumption,

  -- x₁ ∈ Y, x₂ ∈ X case.
  contrapose,
  intros x₁_neq_x₂,

  choose x₁_in_v₁ x₁_one using x₁_in_Y,
  choose x₂_in_u₂ x₂_zero using x₂_in_X,

  have H₂ : ∃ (s : finset α) (H : s ∈ X.simplices), x₂.fst ∈ s, from
  begin
    use u₂, split; assumption,
  end,
  specialize X_disj_Y x₂.fst H₂,

  have H₁ : ∃ (s : finset α) (H : s ∈ Y.simplices), x₁.fst ∈ s, from
  begin
    use v₁, split; assumption,
  end, 
  specialize X_disj_Y x₁.fst H₁,

  rw [←ne.def, ne_comm],
  assumption,

  -- x₁, x₂ ∈ Y case.
  intros x₁_eq_x₂,

  choose x₁_in_v₁ x₁_one using x₁_in_Y,
  choose x₂_in_v₂ x₂_one using x₂_in_Y,
  rw [←x₂_one] at x₁_one,
  rw [prod.ext_iff],
  split; assumption,
end

def join_fst
    {X Y : simplicial_complex α}
    (H : disjoint (vertices X) (vertices Y))
  : simplicial_coe (X ⋆ Y) α
:= simplicial_coe.mk (prod.fst) (join_fst_proj_is_coe X Y H)
notation `π₁` := join_fst

lemma join_proj_vertices_mem
    (X Y : simplicial_complex α)
    (x : α)
    (H : disjoint (vertices X) (vertices Y))
  : x ∈ vertices ((π₁ H)[(X ⋆ Y)]) ↔ x ∈ vertices X ∨ x ∈ vertices Y
:= begin
  simp only [vertices_set_of, simplicial_image, simplicial_join, set.mem_set_of, join_fst],
  split,

  -- x ∈ X ⋆ Y case.
  intros x_in_join,
  choose u u_in_img x_in_u using x_in_join,
  choose v v_in_join proj_v_u using u_in_img,
  choose s s_in_X t t_in_Y st_eq_v using v_in_join,

  rw [←proj_v_u, finset.mem_image] at x_in_u,
  choose y y_in_v proj_y_x using x_in_u,
  rw [←st_eq_v, simplex_disjoint_mem] at y_in_v,
  cases y_in_v with y_in_X y_in_Y,

  left,
  choose y_in_s y_zero using y_in_X,
  subst proj_y_x,
  use s, split; assumption,

  right,
  choose y_in_t y_one using y_in_Y,
  subst proj_y_x,
  use t, split; assumption,

  -- x ∈ X ∪ Y case.
  intros x_in_union,
  cases x_in_union with x_in_X x_in_Y,

  -- x ∈ X subcase.
  choose s s_in_X x_in_s using x_in_X,
  use s, split,
  use (s ⊔ₛ ∅), split,

  use s, split, assumption,
  use ∅, split, apply simplicial_complex_empty_simplex,
  refl,

  simp only [simplex_disjoint_union, finset.image_union, finset.empty_product, finset.image_empty, finset.union_empty],
  simp only [finset.ext_iff, finset.mem_image],
  intros a,
  split,

  intros a_in_img,
  choose b b_in_prod proj_b_a using a_in_img,
  simp only [finset.mem_product] at b_in_prod,
  choose b_in_s b_zero using b_in_prod,
  subst proj_b_a,
  assumption,

  intros a_in_s,
  use (a, 0), split,
  simp only [finset.mem_product, prod.fst, prod.snd, finset.mem_singleton],
  split, assumption, refl,
  simp only [prod.fst],
  assumption,

  -- x ∈ Y subcase.
  choose t t_in_Y x_in_t using x_in_Y,
  use t, split,
  use (∅ ⊔ₛ t), split,

  use ∅, split, apply simplicial_complex_empty_simplex,
  use t, split, assumption,
  refl,

  simp only [simplex_disjoint_union, finset.image_union, finset.empty_product, finset.image_empty, finset.empty_union],
  simp only [finset.ext_iff, finset.mem_image],
  intros a,
  split,

  intros a_in_img,
  choose b b_in_prod proj_b_a using a_in_img,
  simp only [finset.mem_product] at b_in_prod,
  choose b_in_s b_one using b_in_prod,
  subst proj_b_a,
  assumption,

  intros a_in_s,
  use (a, 1), split,
  simp only [finset.mem_product, prod.fst, prod.snd, finset.mem_singleton],
  split, assumption, refl,
  simp only [prod.fst],
  assumption,
end

lemma simplex_disjoint_union_prod_fst
    (s t : finset α)
  : finset.image prod.fst (s ⊔ₛ t) = s ∪ t
:= begin
  simp only [simplex_disjoint_union, finset.image_union, finset.ext_iff, finset.mem_image, finset.mem_union],
  intro x,
  split,

  intro x_in_img,
  cases x_in_img with x_in_s x_in_t,

  left,
  choose y y_in_prod proj_y_x using x_in_s,
  simp only [finset.mem_product] at y_in_prod,
  choose y_in_s y_zero using y_in_prod,
  subst proj_y_x,
  assumption,

  right,
  choose y y_in_prod proj_y_x using x_in_t,
  simp only [finset.mem_product] at y_in_prod,
  choose y_in_t y_one using y_in_prod,
  subst proj_y_x,
  assumption,

  intro x_in_st,
  cases x_in_st with x_in_s x_in_t,

  left,
  use (x, 0), split,
  simp only [finset.mem_product],
  split,
  assumption,
  apply finset.mem_singleton_self,
  simp only [prod.fst],

  right,
  use (x, 1), split,
  simp only [finset.mem_product],
  split,
  assumption,
  apply finset.mem_singleton_self,
  simp only [prod.fst],
end

lemma join_proj_mem
    (X Y : simplicial_complex α)
    (s : finset α)
    (H : disjoint (vertices X) (vertices Y))
  : s ∈ ((π₁ H)[(X ⋆ Y)]).simplices ↔ ∃ (t ∈ X.simplices) (u ∈ Y.simplices), s = t ∪ u
:= begin
  simp only [simplicial_image, simplicial_join, join_fst, set.mem_set_of],
  split,

  -- s ∈ X ⋆ Y case.
  intros s_in_join,
  choose v v_in_join proj_v_s using s_in_join,
  choose t t_in_X u u_in_Y tu_eq_v using v_in_join,

  rw [←tu_eq_v, simplex_disjoint_union_prod_fst] at proj_v_s,
  use t, split, assumption,
  use u, split, assumption,
  symmetry,
  assumption,

  -- s X ∪ Y case.
  intro x_decomp,
  choose t t_in_X u u_in_Y s_eq_tu using x_decomp,
  rw [←simplex_disjoint_union_prod_fst] at s_eq_tu,

  use (t ⊔ₛ u), split,
  use t, split, assumption,
  use u, split, assumption,
  refl,

  symmetry,
  assumption,
end

lemma join_proj_disj_union_mem
    (X Y : simplicial_complex α)
    (s t : finset α)
    (H : disjoint (vertices X) (vertices Y))
  : s ∪ t ∈ ((π₁ H)[(X ⋆ Y)]).simplices ↔
      ∃ (s₁ t₁ ∈ X.simplices) (s₂ t₂ ∈ Y.simplices),
        s = s₁ ∪ s₂ ∧ t = t₁ ∪ t₂ ∧ (s₁ ∪ t₁ ∈ X.simplices) ∧ (s₂ ∪ t₂ ∈ Y.simplices)
:= begin
  rw [join_proj_mem],
  split,

  -- s ∪ t ∈ X ⋆ Y case.
  intro st_in_join,
  choose u u_in_X v v_in_X st_eq_uv using st_in_join,

  use (s ∩ u), split,
  apply X.subset_closed u,
  assumption,
  apply finset.inter_subset_right,

  use (t ∩ u), split,
  apply X.subset_closed u,
  assumption,
  apply finset.inter_subset_right,

  use (s ∩ v), split,
  apply Y.subset_closed v,
  assumption,
  apply finset.inter_subset_right,

  use (t ∩ v), split,
  apply Y.subset_closed v,
  assumption,
  apply finset.inter_subset_right,

  split,
  rw [←finset.inter_distrib_left, ←st_eq_uv, finset.union_comm, finset.inter_union_self],
  
  split,
  rw [←finset.inter_distrib_left, ←st_eq_uv, finset.inter_union_self],

  split,
  rw [←finset.inter_distrib_right, st_eq_uv, finset.inter_comm, finset.union_comm, finset.inter_union_self],
  assumption,

  rw [←finset.inter_distrib_right, st_eq_uv, finset.inter_comm, finset.inter_union_self],
  assumption,

  -- s ∪ t decomp case.
  intro st_decomp,
  choose s₁ s₁_in_X t₁ t₁_in_X s₂ s₂_in_Y t₂ t₂_in_Y st_decomp using st_decomp,
  choose s_decomp t_decomp st₁_in_X st₂_in_Y using st_decomp,

  use (s₁ ∪ t₁), split, assumption,
  use (s₂ ∪ t₂), split, assumption,

  rw [finset.union_comm s₂, finset.union_assoc, ←finset.union_assoc t₁, finset.union_comm (t₁ ∪ t₂), ←finset.union_assoc],
  rw [←s_decomp, ←t_decomp],
end

-- General result on existence of coercion for complexes over ℕ
@[simp]
def finite_nat_complex_bound
    (X : simplicial_complex ℕ) [fintype X.simplices]
  : ℕ
:= ((vertices X) ∪ {(0 : ℕ)}).to_finset.max'
    (begin
      rw [set.to_finset_nonempty, set.union_nonempty],
      right,
      apply set.singleton_nonempty,
    end)

lemma finite_nat_complex_bound_ne
    (X : simplicial_complex ℕ) [fintype X.simplices]
    [X_ne : (vertices X).to_finset.nonempty]
  : finite_nat_complex_bound X = (vertices X).to_finset.max' X_ne
:= begin
  simp only [finite_nat_complex_bound, le_antisymm_iff],
  split,

  rw [finset.max'_le_iff],
  intros y y_in_X,
  rw [set.mem_to_finset, set.mem_union, set.mem_singleton_iff, ←set.mem_to_finset] at y_in_X,
  cases y_in_X with y_in_X y_zero,

  apply finset.le_max',
  assumption,

  rw [y_zero],
  apply zero_le,

  rw [finset.max'_le_iff],
  intros y y_in_X,
  apply finset.le_max',
  rw [set.mem_to_finset, set.mem_union, set.mem_singleton_iff, ←set.mem_to_finset],
  left, assumption,
end

def join_nat_proj_map
    (X Y : simplicial_complex ℕ) [fintype X.simplices]
  : ℕ × ℕ → ℕ
:= λ x : ℕ × ℕ, if (x.snd = 0) then x.fst else (x.fst + (finite_nat_complex_bound X) + 1)

lemma join_nat_proj_is_coe
    (X Y : simplicial_complex ℕ) [fintype X.simplices]
  : set.inj_on (join_nat_proj_map X Y) (vertices (X ⋆ Y))
:= begin
  simp only [set.inj_on, simplicial_join_mem_vertices, join_nat_proj_map],
  simp only [set.mem_set_of, simplicial_join_mem, ite_eq_iff],
  intros x₁ x₁_in_join x₂ x₂_in_join x₁_eq_x₂,

  cases x₁_in_join with x₁_in_X x₁_in_Y;
  cases x₂_in_join with x₂_in_X x₂_in_Y,

  -- x₁, x₂ ∈ X case.
  choose x₁_in_X x₁_zero using x₁_in_X,
  choose x₂_in_X x₂_zero using x₂_in_X,

  cases x₁_eq_x₂ with x₁_eq_x₂ contra,
  choose x₁_zero x₁_eq_x₂ using x₁_eq_x₂,
  rw [@comm _ eq, ite_eq_iff] at x₁_eq_x₂,

  cases x₁_eq_x₂ with x₁_eq_x₂ contra,
  choose x₂_zero x₁_eq_x₂ using x₁_eq_x₂,
  rw [prod.ext_iff],
  split,
  symmetry,
  assumption,
  rw [←x₂_zero] at x₁_zero,
  assumption,

  choose contra H using contra,
  contradiction,

  choose contra H using contra,
  contradiction,

  -- x₁ ∈ X, x₂ ∈ Y case.
  choose x₁_in_X x₁_zero using x₁_in_X,
  choose x₂_in_Y x₂_one using x₂_in_Y,

  cases x₁_eq_x₂ with x₁_eq_x₂ contra,
  choose x₁_zero x₁_eq_x₂ using x₁_eq_x₂,
  rw [@comm _ eq, ite_eq_iff] at x₁_eq_x₂,

  cases x₁_eq_x₂ with contra x₁_eq_x₂,
  choose contra H using contra,
  have x₂_nonzero : x₂.snd ≠ 0, by omega,
  contradiction,

  choose x₂_nonzero x₁_eq_x₂ using x₁_eq_x₂,
  have x₁_le_bound : x₁.fst ≤ finite_nat_complex_bound X, from
  begin
    by_cases X_ne : vertices X = ∅,
    rw [X_ne] at x₁_in_X,
    have contra : x₁.fst ∉ ∅, from
    begin
      apply set.not_mem_empty,
    end,
    contradiction,

    rw [←ne.def, ←set.nonempty_iff_ne_empty, ←set.to_finset_nonempty] at X_ne,
    rw [@finite_nat_complex_bound_ne X _ X_ne],

    apply finset.le_max',
    rw [set.mem_to_finset],
    assumption,
  end,

  have x₁_lt_x₂_bound : x₁.fst < x₂.fst + finite_nat_complex_bound X + 1, by omega,
  have contra : x₂.fst + finite_nat_complex_bound X + 1 ≠ x₁.fst, by exact ne_of_gt x₁_lt_x₂_bound,
  contradiction,

  choose contra H using contra,
  contradiction,

  -- x₁ ∈ Y, x₂ ∈ X case.
  choose x₁_in_Y x₁_one using x₁_in_Y,
  choose x₂_in_X x₂_zero using x₂_in_X,

  cases x₁_eq_x₂ with contra x₁_eq_x₂,
  choose contra H using contra,
  have x₁_nonzero : x₁.snd ≠ 0, by omega,
  contradiction,

  choose x₁_zero x₁_eq_x₂ using x₁_eq_x₂,
  rw [@comm _ eq, ite_eq_iff] at x₁_eq_x₂,
  cases x₁_eq_x₂ with x₁_eq_x₂ contra,

  choose x₂_nonzero x₁_eq_x₂ using x₁_eq_x₂,
  have x₂_le_bound : x₂.fst ≤ finite_nat_complex_bound X, from
  begin
    simp only [finite_nat_complex_bound],
    apply finset.le_max',
    rw [set.mem_to_finset, set.mem_union],
    left, assumption,
  end,

  have x₂_lt_x₁_bound : x₂.fst < x₁.fst + finite_nat_complex_bound X + 1, by omega,
  have contra : x₂.fst ≠ x₁.fst + finite_nat_complex_bound X + 1, by exact ne_of_lt x₂_lt_x₁_bound,
  contradiction,

  choose contra H using contra,
  have x₂_nonzero : x₂.snd ≠ 0, by omega,
  contradiction,

  -- x₁, x₂ ∈ Y case.
  choose x₁_in_Y x₁_one using x₁_in_Y,
  choose x₂_in_Y x₂_one using x₂_in_Y,

  cases x₁_eq_x₂ with contra x₁_eq_x₂,
  choose contra H using contra,
  have x₁_nonzero : x₁.snd ≠ 0, by omega,
  contradiction,

  choose x₁_nonzero x₁_eq_x₂ using x₁_eq_x₂,
  rw [@comm _ eq, ite_eq_iff] at x₁_eq_x₂,
  cases x₁_eq_x₂ with contra x₁_eq_x₂,

  choose contra H using contra,
  have x₂_nonzero : x₂.snd ≠ 0, by omega,
  contradiction,

  choose x₂_nonzero x₁_eq_x₂ using x₁_eq_x₂,
  have x₁_fst_eq_x₂_fst : x₁.fst = x₂.fst, from
  begin
    rw [nat.add_assoc, nat.add_assoc] at x₁_eq_x₂,
    symmetry,
    apply nat.add_right_cancel x₁_eq_x₂,
  end,
  rw [←x₂_one] at x₁_one,
  rw [prod.ext_iff],
  split; assumption,
end

def join_nat_proj
    (X Y : simplicial_complex ℕ) [fintype X.simplices]
  : simplicial_coe (X ⋆ Y) ℕ
:= simplicial_coe.mk (join_nat_proj_map X Y) (join_nat_proj_is_coe X Y)
notation `ν⟨` X `, ` Y `⟩` := join_nat_proj X Y

end join