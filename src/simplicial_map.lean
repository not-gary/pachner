/-
Copyright (c) 2022 Clara Löh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.txt.
Author: Clara Löh.
-/

import tactic          -- standard proof tactics
import data.set        -- basics on sets
import data.set.finite -- basics on finite sets
import data.finset     -- type-level finite sets
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

def simplicial_map_lift
    {X : simplicial_complex α}
    {Y : simplicial_complex β}
    (f : simplicial_map X Y)
  : finset α → finset β
:= λ s : finset α, finset.image f.map s

def simplicial_image
    (X : simplicial_complex α)
    (f : α → β)
    (f_inj : function.injective f)
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

      have Hf : set.inj_on f (f⁻¹' ↑t), from
      begin
        apply function.injective.inj_on,
        assumption,
      end,
      use (finset.preimage t f Hf),
      split,

      apply X.subset_closed u,
      assumption,
      rw [finset.subset_iff] at *,
      intros x x_in_preimg,
      rw [finset.mem_preimage] at x_in_preimg,
      specialize t_sset_s x_in_preimg,
      rw [finset.ext_iff] at u_img,
      specialize u_img (f x),
      cases u_img,
      specialize u_img_mpr t_sset_s,
      rw [function.injective.mem_finset_image] at u_img_mpr,
      assumption,

      assumption,

      rw [finset.ext_iff],
      intro x,
      rw [finset.mem_image],
      split,

      intro y_in_preimg,
      choose y Hy y_in_preimg using y_in_preimg,
      rw [finset.mem_preimage, y_in_preimg] at Hy,
      assumption,

      intro x_in_t,
      rw [finset.ext_iff] at u_img,
      specialize u_img x,
      cases u_img,
      rw [finset.subset_iff] at t_sset_s,
      specialize t_sset_s x_in_t,
      specialize u_img_mpr t_sset_s,
      rw [finset.mem_image] at u_img_mpr,
      choose y Hy y_img using u_img_mpr,
      rw [←y_img, ←finset.mem_preimage] at x_in_t,
      use y, split; assumption,
    end)

lemma map_is_simplicial_onto_image
    (X : simplicial_complex α)
    (f : α → β)
    (f_inj : function.injective f)
  : is_simplicial_map X (simplicial_image X f f_inj) f
:= begin
  unfold is_simplicial_map,
  intros s s_in_X,
  simp only[simplicial_image, set.mem_set_of],
  use s, split; tauto,
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
:= (simplicial_map.comp f g).map = (id_simplicial_map X).map
 ∧ (simplicial_map.comp g f).map = (id_simplicial_map Y).map

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
  split,

  rw [function.comp.assoc, ←function.comp.assoc g_inv.map, g_inv_left],
  simp,
  assumption,

  rw [function.comp.assoc, ←function.comp.assoc f.map, f_inv_right],
  simp,
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

-- Being simplicially isomorphic is an equivalence relation.
@[refl]
lemma simplicial_iso_refl
    (X : simplicial_complex α)
  : X ≅ X
:=
begin
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

  use ⟨id, id_simplicial_X⟩,
  unfold is_simplicial_iso,
  use ⟨id, id_simplicial_Y⟩,

  unfold is_inverse_simplicial_iso,
  split; simp only[simplicial_map.comp];
  rw [function.comp.left_id];
  simp only[id_simplicial_map],
end

end isomorphism

/-
# Simplicial Coercions
-/

section coercion

variables [decidable_eq α] [decidable_eq β]

-- Define as map on simplicial complexes that's iso'ic onto image.
structure simplicial_coe'
    (α : Type*) [decidable_eq α]
    (β : Type*) [decidable_eq β]
:= mk :: (coe : simplicial_complex α → simplicial_complex β)
         (iso_onto_image : ∀ X : simplicial_complex α, X ≅ coe X)

-- Define as coercion on types that lifts to simplicial map.
structure simplicial_coe
    (α : Type*) [decidable_eq α]
    (β : Type*) [decidable_eq β]
:= mk :: (coe : α → β)
         (injective : coe.injective) -- necessary?
         (iso_onto_image : ∀ X : simplicial_complex α, X ≅ simplicial_image X coe injective)

notation φ `[` X `]` := simplicial_image X φ.coe φ.injective

lemma coe_preserves_iso
    (X Y : simplicial_complex α)
    (φ : simplicial_coe α β)
  : X ≅ Y → φ[X] ≅ φ[Y]
:= begin
  intros X_iso_Y,
  apply simplicial_iso_trans (φ[X]) X,
  rw [simplicial_iso_symm],
  apply φ.iso_onto_image,

  rw [simplicial_iso_symm],
  apply simplicial_iso_trans (φ[Y]) Y,
  rw [simplicial_iso_symm],
  apply φ.iso_onto_image,

  rw [simplicial_iso_symm],
  assumption,
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

-- Define simplicial join.
@[simp]
def simplicial_join'
    (X Y : simplicial_complex α)
  : simplicial_complex (α × ℕ) 
:= simplicial_complex.mk
    (⋃ (s ∈ X.simplices), ⋃ (t ∈ Y.simplices), {s ⊔ₛ t})
    (begin
      rw [set.nonempty_coe_sort, set.nonempty_def],
      use (∅ : finset (α × ℕ)),
      rw [set.mem_Union],
      use (∅ : finset α),
      rw [set.mem_Union],
      use simplicial_complex_empty_simplex X,
      rw [set.mem_Union],
      use (∅ : finset α),
      rw [set.mem_Union],
      use simplicial_complex_empty_simplex Y,
      have H_empty : (∅ : finset (α × ℕ)) = (∅ : finset α) ⊔ₛ (∅ : finset α), from
      begin
        symmetry,
        rw [simplex_disjoint_empty],
        split; refl,
      end,
      rw [←H_empty],
      sorry,
    end)
    (begin
      simp only[is_subset_closed],
      intros s s_in_XY t t_sset_s,
      rw [set.mem_Union] at *,

      choose z s_in_XY using s_in_XY,
      rw [set.mem_Union] at s_in_XY,
      choose Hz s_in_XY using s_in_XY,
      rw [set.mem_Union] at s_in_XY,
      choose w s_in_XY using s_in_XY,
      rw [set.mem_Union] at s_in_XY,
      choose Hw s_eq_zw using s_in_XY,
      rw [set.mem_singleton_iff] at s_eq_zw,
      rw [s_eq_zw, simplex_disjoint_subset_sep] at t_sset_s,
      choose zt wt t_eq_zw using t_sset_s,
      choose t_eq_zw zt_sset_z wt_sset_w using t_eq_zw,

      use zt,
      rw [set.mem_Union],
      have Hzt : zt ∈ X.simplices, from
      begin
        apply X.subset_closed z; assumption,
      end,
      use Hzt,
      rw [set.mem_Union],
      use wt,
      rw [set.mem_Union],
      have Hwt : wt ∈ Y.simplices, from
      begin
        apply Y.subset_closed w; assumption,
      end,
      use Hwt,
      rw [set.mem_singleton_iff],
      assumption,
    end)

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

-- Establish basic algebraic properties about joins.
instance simplicial_join.fintype
    (X : simplicial_complex α) [fintype X.simplices]
    (Y : simplicial_complex α) [fintype Y.simplices]
  : fintype (X ⋆ Y).simplices
:= begin
  simp only[simplicial_join, simplicial_complex.simplices, simplex_disjoint_union],
  sorry, -- TODO: set.finite.dependent,
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

-- TODO: Fix the proofs that f, g are simplicial.
lemma simplicial_join_iso
    (X Y : simplicial_complex α)
    (Z W : simplicial_complex β)
  : X ≅ Z → Y ≅ W → X ⋆ Y ≅ Z ⋆ W
:= begin
  unfold is_simplicially_iso,
  unfold is_simplicial_iso,
  unfold is_inverse_simplicial_iso,
  unfold id_simplicial_map,
  simp only[simplicial_map.comp, simplicial_map.map],

  intros X_iso_Z Y_iso_W,
  choose f_xz g_zx fxz_inv_gzx using X_iso_Z,
  choose f_yw g_wy fyw_inv_gwy using Y_iso_W,

  cases fxz_inv_gzx with gzx_fxz_id fxz_gzx_id,
  cases fyw_inv_gwy with gwy_fyw_id fyw_gwy_id,

  let f : α × ℕ → β × ℕ :=
    λ x : α × ℕ, if (x.snd = 0) then (f_xz.map x.fst, x.snd) else (f_yw.map x.fst, x.snd),

  have f_simplicial : is_simplicial_map (X ⋆ Y) (Z ⋆ W) f, by sorry,--from
  -- begin
  --   unfold is_simplicial_map,
  --   intros s s_in_XY,

  --   rw [simplicial_join_mem] at *,
  --   choose t Ht u Hu s_eq_tu using s_in_XY,

  --   use (finset.image f_xz.map t), split,
  --   apply f_xz.is_simplicial,
  --   assumption,

  --   use (finset.image f_yw.map u), split,
  --   apply f_yw.is_simplicial,
  --   assumption,

  --   rw [s_eq_tu],
  --   simp only[simplex_disjoint_union],
  --   rw [finset.image_union],

  --   rw [finset.ext_iff],
  --   intro x,
  --   split,
  --   { intro x_in_f,
  --     rw [finset.mem_union] at *,
  --     cases x_in_f,
      
  --     left,
  --     rw [finset.mem_product],
  --     rw [finset.mem_image] at *,
  --     choose y y_in_t0 using x_in_f,
  --     cases y_in_t0 with y_in_t0 fy_x,

  --     use y.fst,
  --     rw [finset.mem_product] at y_in_t0,
  --     cases y_in_t0 with y_in_t0 y_0,
  --     split,
  --     assumption,

  --     simp only[f] at fy_x,
  --     revert fy_x,
  --     split_ifs,
      
  --     intro y0_x,
  --     rw [←y0_x],
      
  --     rw [finset.mem_singleton] at y_0,
  --     contradiction,
      
  --     simp only[f] at fy_x,
  --     revert fy_x,
  --     split_ifs,
      
  --     intro y0_x,
  --     rw [finset.mem_singleton, ←y0_x],
      
  --     rw [finset.mem_product] at y_in_t0,
  --     cases y_in_t0 with y_in_t0 y_0,
  --     rw [finset.mem_singleton] at y_0,
  --     assumption,
      
  --     intro fy_x,
  --     rw [prod.eq_iff_fst_eq_snd_eq] at fy_x,
  --     cases fy_x with fy_x_fst fy_x_snd,
  --     simp at fy_x_snd,
  --     rw [finset.mem_singleton, ←fy_x_snd],
  --     finish,
      
  --     sorry, },
  --   { intro x_in_f_prod,
  --     rw [finset.mem_union] at *,
  --     cases x_in_f_prod,
      
  --     left,
  --     rw [finset.mem_product] at x_in_f_prod,
  --     cases x_in_f_prod with x_in_fxz x0,
  --     rw [finset.mem_image] at *,
  --     choose y y_in_t fxz_y using x_in_fxz,
      
  --     use (y, 0),
  --     split,

  --     rw [finset.mem_product],
  --     simp,
  --     assumption,
      
  --     simp only[f],
  --     split_ifs,
      
  --     rw [prod.eq_iff_fst_eq_snd_eq],
  --     split,
  --     assumption,
  --     rw [finset.mem_singleton] at x0,
  --     rw [x0],
      
  --     rw [prod.eq_iff_fst_eq_snd_eq],
  --     split,
  --     assumption,
  --     rw [finset.mem_singleton] at x0,
  --     rw [x0],
      
  --     right,
  --     rw [finset.mem_product] at x_in_f_prod,
  --     cases x_in_f_prod with x_in_fyw x1,
  --     rw [finset.mem_singleton] at x1,
  --     rw [finset.mem_image] at *,
  --     choose y y_in_u fyw_y using x_in_fyw,
      
  --     use (y, 1),
  --     split,
      
  --     rw [finset.mem_product],
  --     split,
  --     assumption,
  --     simp,
      
  --     simp only[f],
  --     split_ifs,
      
  --     finish,
      
  --     rw [prod.eq_iff_fst_eq_snd_eq],
  --     split,
  --     assumption,
  --     rw [x1], }
  -- end,

  let fs : simplicial_map (X ⋆ Y) (Z ⋆ W) :=
    simplicial_map.mk f f_simplicial,

  let g : β × ℕ → α × ℕ :=
    λ x : β × ℕ, if (x.snd = 0) then (g_zx.map x.fst, x.snd) else (g_wy.map x.fst, x.snd),

  have g_simplicial : is_simplicial_map (Z ⋆ W) (X ⋆ Y) g, by sorry,--from
  -- begin
  --   unfold is_simplicial_map,
  --   intros s s_in_ZW,
  --   rw [simplicial_join_mem] at *,
  --   simp only[simplex_disjoint_union] at *,

  --   choose t t_in_Z u u_in_W s_eq_tu using s_in_ZW,
  --   rw [s_eq_tu],
  --   use (finset.image g_zx.map t),
  --   split,
  --   apply g_zx.is_simplicial,
  --   assumption,

  --   use (finset.image g_wy.map u),
  --   split,
  --   apply g_wy.is_simplicial,
  --   assumption,

  --   rw [finset.ext_iff],
  --   intro x,
  --   split,
  --   { intro x_in_g,
  --     rw [finset.image_union, finset.mem_union, finset.mem_image, finset.mem_image] at x_in_g,
  --     rw [finset.mem_union],
  --     cases x_in_g,
      
  --     left,
  --     choose y y_in_t0 using x_in_g,
  --     cases y_in_t0 with y_in_t0 gy_x,
  --     rw [finset.mem_product] at y_in_t0,
  --     cases y_in_t0 with y_in_t y0,
  --     rw [finset.mem_product, finset.mem_image],
  --     split,
      
  --     use y.fst,
  --     split,
  --     assumption,
      
  --     simp only[g] at gy_x,
  --     revert gy_x,
  --     split_ifs,
      
  --     intro gy_x,
  --     rw [prod.eq_iff_fst_eq_snd_eq] at gy_x,
  --     cases gy_x with gy_x_fst gy_x_snd,
  --     assumption,
      
  --     rw [finset.mem_singleton] at y0,
  --     contradiction,
      
  --     simp only[g] at gy_x,
  --     revert gy_x,
  --     split_ifs,
      
  --     intro gy_x,
  --     rw [prod.eq_iff_fst_eq_snd_eq] at gy_x,
  --     cases gy_x with gy_x_fst gy_x_snd,
  --     rw [finset.mem_singleton, ←gy_x_snd],
      
  --     rw [finset.mem_singleton] at y0,
  --     contradiction,
      
  --     right,
  --     choose y y_in_u1 using x_in_g,
  --     cases y_in_u1 with y_in_u1 gy_x,
  --     rw [finset.mem_product] at y_in_u1,
  --     cases y_in_u1 with y_in_u y1,
  --     rw [finset.mem_product, finset.mem_image],
  --     split,
      
  --     use y.fst,
  --     split,
  --     assumption,
      
  --     simp only[g] at gy_x,
  --     revert gy_x,
  --     split_ifs,
      
  --     rw [finset.mem_singleton] at y1,
  --     finish,
      
  --     intro gy_x,
  --     rw [prod.eq_iff_fst_eq_snd_eq] at gy_x,
  --     cases gy_x with gy_x_fst gy_x_snd,
  --     assumption,
      
  --     simp only[g] at gy_x,
  --     revert gy_x,
  --     split_ifs,
      
  --     rw [finset.mem_singleton] at y1,
  --     finish,
      
  --     intro gy_x,
  --     rw [prod.eq_iff_fst_eq_snd_eq] at gy_x,
  --     cases gy_x with gy_x_fst gy_x_snd,
  --     rw [finset.mem_singleton, ←gy_x_snd], },
  --   { intro x_in_g_prod,
  --     rw [finset.mem_union, finset.mem_product, finset.mem_product, finset.mem_image, finset.mem_image] at x_in_g_prod,
  --     rw [finset.mem_image],
  --     cases x_in_g_prod,
      
  --     cases x_in_g_prod with gzx_x x0,
  --     choose y y_in_t gzx_x using gzx_x,
  --     rw [finset.mem_singleton] at x0,
      
  --     use (y, 0),
  --     split,

  --     rw [finset.mem_union],
  --     left,
  --     rw [finset.mem_product],
  --     split,
  --     assumption,
  --     simp,
      
  --     simp only[g],
  --     split_ifs,
      
  --     rw [prod.eq_iff_fst_eq_snd_eq],
  --     split,
  --     assumption,
  --     rw [x0],
      
  --     rw [prod.eq_iff_fst_eq_snd_eq],
  --     split,
  --     assumption,
  --     rw [x0],
      
  --     cases x_in_g_prod with gzx_x x1,
  --     choose y y_in_u gzx_x using gzx_x,
  --     rw [finset.mem_singleton] at x1,
      
  --     use (y, 1),
  --     split,
      
  --     rw [finset.mem_union],
  --     right,
  --     rw [finset.mem_product],
  --     split,
  --     assumption,
  --     simp,
      
  --     simp only[g],
  --     split_ifs,
      
  --     finish,
      
  --     rw [prod.eq_iff_fst_eq_snd_eq],
  --     split,
  --     assumption,
  --     rw [x1], }
  -- end,

  let gs : simplicial_map (Z ⋆ W) (X ⋆ Y) :=
    simplicial_map.mk g g_simplicial,

  use fs,
  use gs,
  simp only[simplicial_map.map],

  split; rw [function.funext_iff],
  { intro x,
    simp only[id, function.comp, f, g],
    split_ifs;
    rw [prod.eq_iff_fst_eq_snd_eq],

    split,
    simp,
    rw [←function.comp_apply g_zx.map f_xz.map, gzx_fxz_id],
    simp,
    
    split,
    simp,
    rw [←function.comp_apply g_wy.map f_yw.map, gwy_fyw_id],
    simp, },
  { intro x,
    simp only[id, function.comp, f, g],
    split_ifs;
    rw [prod.eq_iff_fst_eq_snd_eq],
    
    split,
    simp,
    rw [←function.comp_apply f_xz.map g_zx.map, fxz_gzx_id],
    simp,
    
    split,
    simp,
    rw [←function.comp_apply f_yw.map g_wy.map, fyw_gwy_id],
    simp, }
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

lemma simplicial_join_assoc
    (X Y Z : simplicial_complex α)
    (φ : simplicial_coe (α × ℕ) α)
  : φ[(X ⋆ Y)] ⋆ Z ≅ X ⋆ φ[(Y ⋆ Z)]
:= sorry

lemma simplicial_join_comm
    (X Y : simplicial_complex α)
  : X ⋆ Y ≅ Y ⋆ X
:= sorry

-- Make sense of natural projections, inclusions, etc.
lemma simplicial_join_id
    (X : simplicial_complex α)
  : X ⋆ empty_sc ≅ X
:= sorry

lemma simplicial_join_natural_incl_left
    (X Y : simplicial_complex α)
    (t : finset α)
  : t ∈ Y.simplices ↔ X ⋆ simplex t ⊆ X ⋆ Y
:= sorry

lemma simplicial_join_natural_incl_right
    (X Y : simplicial_complex α)
    (s : finset α)
  : s ∈ X.simplices ↔ simplex s ⋆ Y ⊆ X ⋆ Y
:= sorry

lemma simplicial_join_distr_union_left
    (X Y Z : simplicial_complex α)
  : X ⋆ (Y ∪ Z) ≅ (X ⋆ Y) ∪ (X ⋆ Z)
:= sorry

lemma simplicial_join_distr_union_right
    (X Y Z : simplicial_complex α)
  : (Y ∪ Z) ⋆ X ≅ (Y ⋆ X) ∪ (Z ⋆ X)
:= sorry

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

-- Lemma 2.1, p.5
lemma dim_of_join
    {a : Type*} [decidable_eq a]
    (X Y : simplicial_complex a) [fintype X.simplices] [fintype Y.simplices]
  : dim_of_complex (X ⋆ Y) = (dim_of_complex X) + (dim_of_complex Y) + 1
:= begin
  intros,
  set n := dim_of_complex X,
  set m := dim_of_complex Y,
  unfold dim_of_complex,
  sorry,
end

end join