/-
Copyright (c) 2022 Clara Löh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.txt.
Author: Clara Löh.
-/

import tactic          -- standard proof tactics
import .simplicial_complex      -- basics on simplicial complexes
import .simplicial_map          -- simplicial maps
import .gen_simplicial_complex  -- generation of finite simplicial complexes (including examples)
import .comb_simplicial_complex -- union/intersection of two simplicial complexes (and zigzag)
import .euler_characteristic    -- Euler characteristic of finite simplicial complexes
import algebra.big_operators.basic
import algebra.big_operators.order
import topology.metric_space.basic 
open_locale big_operators -- to enable ∑ notation

open classical  -- we work in classical logic

/-
# Exercise [a small simplicial complex]
-/

-- the set of simplices of our "small" simplicial complex
@[simp]
def small_sc_S 
  : set (finset ℕ)
:= {{0}, {1}, ∅}

-- Preparation: 
-- subsets of the empty finset are empty
lemma finset_sub_empty 
    {a : Type*}
    (t : finset a)
    (t_sub_empty : t ⊆ ∅)
  : t = ∅
:=
begin
  exact finset.subset_empty.mp t_sub_empty,    
end

-- Preparation:
-- {{0}, {1}, ∅} is closed under taking subsets
lemma small_sc_subset_closed 
    : is_subset_closed small_sc_S -- ({{0}, {1}, ∅} : set (finset ℕ))
:= 
begin
  let S : set (finset ℕ) := {{0}, {1}, ∅},
  assume s, 
  assume s_in_S : s ∈ S,

  assume t,
  assume t_sub_s : t ⊆ s,

  show t ∈ S, from 
  begin
    simp only[small_sc_S] at *,
    -- we consider the three cases for s separately:
    cases s_in_S,
      -- s = {0}
      finish,
    cases s_in_S,
      -- s = {1}
      finish,
      -- s = ∅ 
      {have t_empty: t = ∅, 
            by {rw[set.mem_singleton_iff.mp s_in_S] at t_sub_s, 
                exact finset_sub_empty t t_sub_s}, 
      finish},
  end,
end    


-- definition of our "small" simplicial complex
@[simp]
def small_sc 
  : simplicial_complex ℕ 
:= simplicial_complex.mk 
     (small_sc_S) --{ {0}, {1}, ∅} : set (finset ℕ))
     (small_sc_subset_closed)

-- How many non-empty simplices does small_sc have?

-- Preparation: to use finset.card, we need that 
-- small_sc.simplices indeed is finite
instance : fintype small_sc.simplices 
:= 
begin
  dsimp[small_sc],
  exact set.fintype_insert {0} {{1}, ∅},
end

-- our "small" simplicial complex 
-- has exactly two non-empty simplices
lemma small_sc_has_two_nonempty_simplices 
    : finset.card ((set.to_finset small_sc.simplices) \ {∅}) 
    = 2
:=
begin 
  refl, -- can be directly evaluated
end    


-- Alternatively:
-- More explicitly, without using card:
-- our small simplicial complex
-- has at least two non-empty simplices
lemma small_sc_has_geq_two_simplices
    : ∃ s t, s ∈ small_sc.simplices 
           ∧ t ∈ small_sc.simplices
           ∧ s ≠ ∅ 
           ∧ t ≠ ∅ 
:=
begin
  use {0},
  use {1},

  /-
  -- Alternatively: quick but implicit
  split, simp,
  split, simp, 
  split, simp, 
  simp,
  -/

  have s0_in_S : {0} ∈ small_sc.simplices, by simp,
  have s1_in_S : {1} ∈ small_sc.simplices, by simp,
  have s0_neq_empty : {0} ≠ ∅, by simp,
  have s1_neq_empty : {1} ≠ ∅, by exact finset.singleton_ne_empty 1, 

  exact ⟨ s0_in_S, ⟨ s1_in_S,
        ⟨ s0_neq_empty, s1_neq_empty ⟩⟩⟩,
end    

-- and similarly, one would have to show 
-- that small_sc has at most two non-empty simplices ...


/-
# Exercise [subcomplexes]
-/

def is_subcomplex_of 
    {a : Type*}
    (Y : simplicial_complex a)
    (X : simplicial_complex a)
  : Prop 
:= Y.simplices ⊆ X.simplices

lemma incl_is_simplicial 
    {a : Type*} [decidable_eq a]
    {Y : simplicial_complex a}
    {X : simplicial_complex a}
    (Y_sub_X : is_subcomplex_of Y X)
  : is_simplicial_map Y X id  
:= 
begin
  assume s,
  assume s_in_SY : s ∈ Y.simplices,

  calc finset.image id s = s           : by simp    
                   ...   ∈ X.simplices : by tauto,
end

def inclusion_of_subcomplex
    {a : Type*} [decidable_eq a]
    (Y : simplicial_complex a)
    (X : simplicial_complex a)
    (Y_sub_X : is_subcomplex_of Y X)
  : simplicial_map Y X
:= simplicial_map.mk 
     id
     (incl_is_simplicial Y_sub_X)

/-
# Exercise [nerves]
-/

/- we take the liberty of interpreting "a set X" by a type;
   alternatively, one could always take a setup of the form:
     {a : Type*}
     (X : set a)
     (U : set (set a))
     (U_subs_X : ∀ u, u ∈ U → u ⊆ X)
-/

@[simp]
def is_nerve_member 
    {X : Type*}
    (U : set (set X))
    (V : finset (set X))
  : Prop
:= V = ∅ 
 ∨ ( ↑V ⊆ U 
   ∧ ∃ x : X, ∀ u ∈ V, x ∈ u )
-- finset.bInter does not yet exist in mathlib ...

@[simp]
def nerve_simplices
    {X : Type*}
    (U : set (set X))
  : set (finset (set X))
:= { V : finset (set X)
   | is_nerve_member U V
   }

lemma nerve_simplices_subset_closed 
    {X : Type*}
    (U : set (set X))
  : is_subset_closed (nerve_simplices U)  
:= 
begin
  have empty_in_SN : ∅ ∈ nerve_simplices U,
       by simp,

  assume s,
  assume s_in_SN : s ∈ nerve_simplices U,
  assume t,
  assume t_sub_s : t ⊆ s,

  show t ∈ nerve_simplices U, from 
  begin 
    dsimp only[nerve_simplices] at s_in_SN,
    cases s_in_SN,
      -- s = ∅ 
      {rw[s_in_SN] at t_sub_s, 
       have t_empty : t = ∅, 
            by rw[finset_sub_empty t t_sub_s], 
       simp[t_empty]},

      -- s ⊆ U ∧ ∃ x, ∀ u, u ∈ s → x ∈ u
      {rcases s_in_SN.2 with ⟨ x, x_in_inter_s⟩,
       show is_nerve_member U t, from 
       begin 
         apply or.intro_right,
         have t_sub_U : ↑t ⊆ U , 
              by tauto,
         have inter_t_nonempty : ∃ x, ∀ u, u ∈ t → x ∈ u, from  
              begin 
                 use x,
                 assume u : set X,
                 assume u_in_t : u ∈ t, 
                 show x ∈ u, from 
                      begin 
                        have u_in_s : u ∈ s, 
                             by tauto,
                        show x ∈ u, 
                             by exact x_in_inter_s u u_in_s, 
                      end,
              end,
         exact ⟨ t_sub_U, inter_t_nonempty ⟩,
       end}, 
  end
end

def nerve 
    {X : Type*}
    (U : set (set X))
  : simplicial_complex (set X)
:= simplicial_complex.mk 
     (nerve_simplices U)
     (nerve_simplices_subset_closed U)  

/-
# Exercise [Rips complexes]
-/

@[simp]
def rips_simplices
    (X : Type*) [metric_space X]
    (r : ℝ)
  : set (finset X)
:= { s : finset X 
   | ∀ x y, x ∈ s → y ∈ s → dist x y ≤ r }

lemma rips_subset_closed 
    (X : Type*) [metric_space X]
    (r : ℝ)
  : is_subset_closed (rips_simplices X r)
:= 
begin
  assume s,
  assume s_in_RS : s ∈ rips_simplices X r,
  assume t,
  assume t_sub_s : t ⊆ s,

  show t ∈ rips_simplices X r, from 
  begin
    assume x y,
    assume x_in_t : x ∈ t,
    assume y_in_t : y ∈ t,

    have x_in_s : x ∈ s, by tauto,
    have y_in_s : y ∈ s, by tauto,

    show dist x y ≤ r, 
         by exact s_in_RS x y x_in_s y_in_s,
  end 
end  

@[simp]
def rips_complex 
    (X : Type*) [metric_space X]
    (r : ℝ)
  : simplicial_complex X
:= simplicial_complex.mk 
     (rips_simplices X r) 
     (rips_subset_closed X r)

lemma rips_complex_mono
    (X : Type*) [metric_space X]
    (r : ℝ)
    (R : ℝ)
    (r_leq_R : r ≤ R)
  : is_subcomplex_of (rips_complex X r) (rips_complex X R)  
:=
begin
  unfold is_subcomplex_of,
  change ∀ (a : finset X), 
          (∀ (x y : X), x ∈ a → y ∈ a → dist x y ≤ r) 
         → ∀ (x y : X), x ∈ a → y ∈ a → dist x y ≤ R,
  assume s : finset X,
  assume s_in_RS_r : s ∈ (rips_complex X r).simplices,

  show s ∈ (rips_complex X R).simplices, from 
  begin 
    assume x : X,
    assume y : X,
    assume x_in_s : x ∈ s,
    assume y_in_s : y ∈ s,

    calc dist x y ≤ r : by exact s_in_RS_r x y x_in_s y_in_s
              ... ≤ R : by exact r_leq_R,
  end,  
end  


-- similarly [but not equivalently!], 
-- one could define the Cech complexes 
-- through the nerve construction
@[simp]
def cech_complex
    (X : Type*) [metric_space X]
    (r : ℝ)
  : simplicial_complex (set X)
:=
nerve { (metric.closed_ball x r) | x : X } 

/-
# Exercise [the line]
-/

@[simp]
def line_edges 
  : set (finset int)
:= { ({n,n+1} : finset int) | n : int }  

@[simp]
def line_vertices
  : set (finset int)
:= { ({n} : finset int) | n : int }

@[simp]
def line_simplices 
:= line_edges ∪ line_vertices ∪ {∅}

-- to define the real line via the set line_simplices,
-- we need to establish that line_simplices is subsets-closed

-- Preparation:
-- each simplex lies in an edge
lemma line_simplices_lie_in_edges
    (s : finset int) 
    (s_in_L : s ∈ line_simplices)
  : ∃ n : int, s ⊆ {n,n+1}
:= 
begin 
  change ∃ (n : ℤ), s ⊆ {n, n + 1},
  have s_explicit : s = ∅ 
                  ∨ (∃ (n : ℤ), {n, n + 1} = s) 
                  ∨  ∃ (n : ℤ), {n} = s, 
       by finish,
  -- this is a straightforward case distinction
  cases s_explicit,
    -- s = ∅ 
    finish,
  cases s_explicit,
    -- ∃ n, {n,n+1} = s 
    {rcases s_explicit with ⟨ n, nn1_is_s ⟩,
     use n,
     finish,}, 
    -- ∃ n, {n} = s 
    {rcases s_explicit with ⟨n, n_is_s⟩,
     use n,
     rw[n_is_s.symm],
     simp,} 
end  

-- Preparation:
-- subsets of an edge can be described explicitly
lemma subsets_of_edge 
    {a : Type*} [decidable_eq a]
    (x y : a)
    (t : finset a)
    (t_sub_xy : t ⊆ {x,y})
  : t = ∅ ∨ t = {x} ∨ t = {y} ∨ t = {x,y}
:= 
begin 
  -- we compute the powerset of {x,y} in explicit terms
  let p := finset.powerset ({x,y} : finset a),
  have p_explicit: p = {∅, {y}, {x}, {x,y}}, from 
  begin 
    calc p = finset.powerset (insert x {y})
           : by refl
       ... = finset.powerset {y} ∪ finset.image (insert x) (finset.powerset {y})
           : by  exact finset.powerset_insert {y} x
       ... = {∅, {y}} ∪ finset.image (insert x) {∅, {y}} 
           : by congr
       ... = {∅, {y}} ∪ {{x}, {x,y}}
           : by simp    
       ... = {∅, {y}, {x}, {x,y} }
           : by refl,
  end,

  -- ... and then conclude
  have t_in_p : t ∈ p, 
       by exact finset.mem_powerset.mpr t_sub_xy,

  show _, by {rw[p_explicit] at t_in_p,
              finish},
end   


lemma line_subset_closed 
    : is_subset_closed line_simplices
:=
begin
  change ∀ (s : finset ℤ), 
           ((∃ (n : ℤ), {n, n + 1} = s) ∨ ∃ (n : ℤ), {n} = s) ∨ s ∈ {∅} 
         → ∀ (t : finset ℤ), t ⊆ s 
             → ((∃ (n : ℤ), {n, n + 1} = t) ∨ ∃ (n : ℤ), {n} = t) ∨ t ∈ {∅},
  assume s,
  assume s_in_S : s ∈ line_simplices,
  assume t,
  assume t_sub_s : t ⊆ s,

  -- we show that s (whence t) is contained in an edge 
  -- and then use our explicit description of subsets of edges
  rcases line_simplices_lie_in_edges s s_in_S 
         with ⟨ n, s_sub_nn1 : s ⊆ {n,n+1} ⟩,

  have t_sub_nn1 : t ⊆ {n,n+1}, 
       by exact finset.subset.trans t_sub_s s_sub_nn1,

  have t_cases : t = ∅ ∨ t = {n} ∨ t = {n+1} ∨ t = {n,n+1}
       := subsets_of_edge n (n+1) t t_sub_nn1, 

  -- each of these cases for t is clear
  show t ∈ line_simplices, by finish,
end    

-- therefore, we can construct a simplicial complex 
-- with line_simplices as set of simplices
def line_sc : simplicial_complex int
:= simplicial_complex.mk 
    (line_simplices)
    (line_subset_closed) 

-- this line has dimension 1:
lemma dim_line 
    : has_dimension line_sc 1
:= 
begin
  let L := line_sc, 

  have dim_leq_1 : has_dimension_leq L 1, from
  begin
    assume s : finset int,
    assume s_in_S : s ∈ L.simplices,

    -- each simplex lies in an edge ...
    rcases line_simplices_lie_in_edges s s_in_S 
         with ⟨ n, s_sub_nn1 : s ⊆ {n,n+1} ⟩,

    -- ... and thus has dimension at most 1
    calc dim s = finset.card s - 1 
               : by simp
           ... ≤ finset.card {n,n+1} - 1 
               : by {simp, exact finset.card_le_of_subset s_sub_nn1}
           ... ≤ 1 
               : by simp,
  end,

  have dim_geq_1 : has_dimension_geq L 1, from
  begin
    -- we use {0,1} as a witness
    let s : finset int := {0,1},
    use {0,1},

    have s_in_L : s ∈ L.simplices, from
    begin
      have s_in_edges: s ∈ line_edges, 
           by {simp only[line_edges], use 0, ring_nf},
      show _, by exact or.inl (or.inl s_in_edges), 
    end,

    have dim_s_geq_1 : dim s ≥ 1, by simp,

    show _, by exact ⟨ s_in_L, dim_s_geq_1 ⟩,
  end,

  show _, by exact ⟨ dim_leq_1, dim_geq_1 ⟩,
end    


-- alternatively, one could introduce a way to generate 
-- simplicial complexes (similarly to the finite case 
-- in fingen_simplicial_complex) 
-- and then to proceed as in the exercise on the 
-- dimension of finite generated simplicial complexes.


/-
# Exercise [the category of simplicial complexes]
-/

-- categories consist of a category_struct together with 
-- the usual axioms for morphisms;
-- * a category_struct consists of a quiver together with
--   "identity" morphisms and "compositions";
-- * a quiver associates to any two objects of the base type 
--   a "type of morphisms";

-- thus, categories are structures with the following fields:
--
--  hom      : for each two objects, the type of morphisms between them
--  id       : for each objects, the designated identity morphism
--  comp     : for each three objects and all morphisms between them, 
--             their composition
--
--  id_comp' : composition with id from the left is neutral 
--  comp_id' : composition with id from the right is neuetral
--  assoc'   : composition is associative
-- 
-- the fields id_comp', comp_id', assoc' will be filled in automatically, 
-- provided that the corresponding statements can be automatically derived 
-- or are proved in the context

-- Preparation: 
-- extensionality for simplicial maps
lemma sc_map_ext 
    {a : Type*} {b : Type*} [decidable_eq b]
    {X : simplicial_complex a}
    {Y : simplicial_complex b}
    (f : simplicial_map X Y)
    (g : simplicial_map X Y)
    (f_is_g : f.map = g.map)
  : f = g 
:= 
begin
  rcases f with ⟨ f_map, f_is_simplicial ⟩,
  rcases g with ⟨ g_map, g_is_simplicial ⟩,
  simp only[f_is_g],
  show f_map = g_map, by exact f_is_g,
end    

-- Preparation: 
-- composition with the identity is left/right neutral
@[simp]
lemma sc_map_id_comp 
    {a : Type*} {b : Type*} [decidable_eq a] [decidable_eq b] 
    {X : simplicial_complex a}
    {Y : simplicial_complex b}
    (f : simplicial_map X Y)
  : simplicial_map.comp (id_simplicial_map X) f = f
:=
begin
  let g := simplicial_map.comp (id_simplicial_map X) f,
  have eq_on_map_level : g.map = f.map, 
       by refl, 
  show g = f, by exact sc_map_ext g f eq_on_map_level,
end  

@[simp]
lemma id_map_sc_comp 
    {a : Type*} {b : Type*} [decidable_eq a] [decidable_eq b] 
    {X : simplicial_complex a}
    {Y : simplicial_complex b}
    (f : simplicial_map X Y)
  : simplicial_map.comp f (id_simplicial_map Y) = f
:=
begin
  let g := simplicial_map.comp f (id_simplicial_map Y),
  have eq_on_map_level : g.map = f.map, 
       by refl, 
  show g = f, by exact sc_map_ext g f eq_on_map_level,
end  


-- the actual category instance for simplicial complexes
instance {a : Type*} [decidable_eq a]
: category_theory.category (simplicial_complex a)
:= { hom := λ X Y, simplicial_map X Y, 
     id  := λ X, id_simplicial_map X, 
     comp := λ X Y Z, λ f, λ g, simplicial_map.comp f g,
   }


-- alternatively, one could also make use of the fun_like setup

-- now one could go on to compare the category theoretic notion 
-- of isomorphisms with is_simplicial_iso etc. ...


/-
# Exercise [the cube]
-/

-- two triangles generating a square with given vertices
def square
    {a : Type*} [decidable_eq a]
    (w x y z: a) 
  : finset (finset a)
:= { {w,x,y}, {w,y,z} }

-- the surface of a cube,
-- built from generating sets of its six square faces
def cube
  : fin_simplicial_complex nat
:= fingen_simplicial_complex 
     ( ({ square 0 1 2 3  
        , square 0 1 5 4
        , square 0 3 7 4
        , square 1 5 6 2
        , square 2 6 7 3
        , square 4 5 6 7 } : finset (finset (finset nat)))
     .bUnion (λ x,x) )  

#eval χ cube -- 2

/-
# Exercise [dimension of generated simplicial complexes]
-/

def gen_set_has_dimension
    {a : Type*} -- [decidable_eq a]
    (S : finset (finset a))
    (n : nat) 
:= (∀ s ∈ S, dim s ≤ n)
 ∧ (∃ s ∈ S, dim s ≥ n)

def gen_set_members
    {a : Type*} [decidable_eq a]
    (S : finset (finset a))
    (s : finset a)
  : s ∈ fingen_simplices S ↔ ∃ t ∈ S, s ⊆ t
:=
begin
  simp,
end  

lemma has_dim_fingen_simplicial_complex
    {a : Type*} [decidable_eq a]
    (S : finset (finset a))
    (n : nat)
    (dim_S_n : gen_set_has_dimension S n)
  : has_dimension (↑(fingen_simplicial_complex S) : simplicial_complex a) n 
:=
begin
  let X := fingen_simplicial_complex S,

  have dim_leq_n : has_dimension_leq ↑X n, from
  begin
    unfold_coes,
    assume s : finset a,
    assume s_in_SX : s ∈ X.simplices,

    have ex_t : ∃ t ∈ S, s ⊆ t,
         by exact (gen_set_members S s).mp s_in_SX,
    rcases ex_t with ⟨ t : finset a, ⟨ t_in_S, s_sub_t⟩⟩,

    have dim_t_leq_n : dim t ≤ n, 
      by exact dim_S_n.1 t t_in_S,

    show dim s ≤ n, by
      calc dim s = finset.card s - 1 
                 : by refl
             ... ≤ finset.card t - 1 
                 : by {simp, exact finset.card_le_of_subset s_sub_t}
             ... ≤ dim t  
                 : by refl
             ... ≤ n 
                 : by exact dim_t_leq_n,
  end,

  have dim_geq_n : has_dimension_geq ↑X n, from
  begin
    rcases dim_S_n.2 with ⟨ t : finset a, ⟨t_in_S, dim_t_geq_n ⟩⟩,
    use t,

    have t_in_SX : t ∈ X.simplices, from
    begin
      simp only[has_dimension_leq, dim] at *,
      apply (gen_set_members S t).mpr
            (by {use t, exact ⟨ t_in_S, by tauto ⟩}),
    end,

    show _, by {unfold_coes, exact ⟨t_in_SX, dim_t_geq_n⟩},
  end,

  show _, by exact ⟨ dim_leq_n, dim_geq_n ⟩,
end

lemma dimension_torus
    : has_dimension (↑torus : simplicial_complex nat) 2
:=
begin
  -- we only need to check this on the defining generating set
  apply has_dim_fingen_simplicial_complex,
  split,
  -- leq 2
    finish,
  -- geq 2
    use {0,1,4},
    finish,
end

/-
# Exercise [simplicial maps via generators]
-/
 
lemma simplicial_map_via_gen
    {a : Type*} [decidable_eq a]
    {b : Type*} [decidable_eq b]
    (S : finset (finset a))
    {Y : fin_simplicial_complex b}
    (f : a → b)
    (f_simplicial_on_S : ∀ s ∈ S, finset.image f s ∈ Y.simplices)
  : is_simplicial_map (↑(fingen_simplicial_complex S) : simplicial_complex a) 
                      (↑Y : simplicial_complex b)
                      f
:=
begin
  let X := fingen_simplicial_complex S,
  assume s, 
  assume s_in_SX: s ∈ X.simplices,

  have s_in_genS : s ∈ fingen_simplices S, 
       by tauto,
  simp only[fingen_simplices, finset.mem_bUnion, finset.mem_powerset] at s_in_genS,
  rcases s_in_genS with ⟨ t, ⟨ t_in_S, t_sub_s⟩⟩,

  show finset.image f s ∈ Y.simplices, from 
  begin 
    have ft_in_SY : finset.image f t ∈ Y.simplices, 
         by exact f_simplicial_on_S t t_in_S,
    have fs_sub_ft : finset.image f s ⊆ finset.image f t,
         by exact finset.image_subset_image t_sub_s, 
    show _, 
         by exact Y.subset_closed _ ft_in_SY (finset.image f s) fs_sub_ft,
  end,
end


/-
# Exercise [an estimate for the Euler characteristic]
-/

/- The absolute value of the Euler characteristic 
   of a finite simplicial complex is bounded 
   in absolute value 
   from above by the number of simplices. 
-/

-- Preparation:
-- the absolute value of the parity is at most 1
lemma parity_abs_leq_1 
    (x : int)
  : |parity x| ≤  1
:=
begin
  unfold parity,

  -- basic case analysis on the if-then-else branches
  split_ifs,

  -- all branches are trivial:
  -- if x < 0
  finish,
  -- if x ≥ 0 and x.mod 2 = 0
  finish,
  -- if x ≥ 0 and x.mod 2 ≠ 0
  finish,
end

-- Preparation:
-- the corresponding estimate 
-- for the parity of the dimension of simplices
lemma simplices_par_abs_leq_1
    {a : Type*}
    (X : fin_simplicial_complex a)
  : ∀ s : finset a, s ∈ X.simplices → |parity (dim s)| ≤ 1
:=
begin
  assume s,
  assume s_in_SX : s ∈ X.simplices,

  exact parity_abs_leq_1 (dim s),
end  

-- Preparation: 
-- Similar to nat_abs_sum: inductive triangle inequality
lemma abs_sum_le 
    {a : Type*} 
    (s : finset a) 
    (f : a → ℤ) 
  : |∑ i in s, f i| ≤ ∑ i in s, |f i|
:=
begin
  classical,
  -- By induction over the underlying finset
  apply finset.induction_on s,
  -- Base case: the empty sum
  { calc |∑ (i : a) in ∅, f i| = 0 
                               : by simp[finset.sum_empty]
                           ... ≤ ∑ (i : a) in ∅, |f i|
                               : by exact abs_nonpos_iff.mpr rfl,  
  },
  -- Induction step: summing over one more element,
  -- using the triangle inequality abs_add for abs   
  { assume j : a, 
    assume s : finset a,
    assume j_not_in_s : j ∉ s, 
    assume ind_hyp, 
    calc |∑ (i : a) in insert j s, f i| 
             = |f j + ∑ (i : a) in s, f i|
             : by {congr, simp[finset.sum_insert j_not_in_s]}
         ... ≤ |f j| + |∑ (i : a) in s, f i|
             : by exact abs_add _ _
         ... ≤ |f j| + ∑ (i : a) in s, |f i|
             : by simp[ind_hyp]        
         ... ≤ ∑ (i : a) in insert j s, |f i| 
             : by simp[finset.sum_insert j_not_in_s],
  },
end

-- The claimed estimate follows by combining 
-- the inductive triangle inequality with the parity estimate
lemma euler_leq_simplices
    {a : Type*} 
    (X : fin_simplicial_complex a)
  : abs (euler_char X) ≤ finset.card X.simplices
:=
begin
  calc abs (euler_char X) 
       = abs (∑ (s : finset a) in X.simplices, parity (dim s))
       : by unfold euler_char
   ... ≤ ∑ (s : finset a) in X.simplices, abs (parity (dim s)) 
       : by exact abs_sum_le X.simplices (λ x, parity (dim x))
   ... ≤ ∑ (s : finset a) in X.simplices, 1
       : by exact finset.sum_le_sum (simplices_par_abs_leq_1 X)
   ... ≤ finset.card X.simplices 
       : by finish,
end

/-
# Exercise [Euler characteristic and isomorphisms]
-/

-- Preparation:
-- inverse simplicial isomorphisms lead to inverse bijections 
-- between the sets of simplices
lemma iso_simplices_inv 
    {a : Type*} [decidable_eq a]
    {b : Type*} [decidable_eq b]
    {X : fin_simplicial_complex a}
    {Y : fin_simplicial_complex b}
    (f : simplicial_map (↑X : simplicial_complex a) (↑Y : simplicial_complex b))
    (g : simplicial_map (↑Y : simplicial_complex b) (↑X : simplicial_complex a))
    (f_inv_g : is_inverse_simplicial_iso f g)
  : ∀ (s : finset a), s ∈ X.simplices 
    → finset.image g.map (finset.image f.map s) = s
:=     
begin
  simp only[is_inverse_simplicial_iso] at f_inv_g,
  assume s : finset a,
  assume s_in_SX : s ∈ X.simplices,


  have f_inv_g_maps : g.map ∘ f.map  = id, from 
  begin
    have gf_id : simplicial_map.comp f g = id_simplicial_map ↑X, 
         by tauto,
    calc g.map ∘ f.map = (id_simplicial_map ↑X).map 
                       : by {rw[gf_id.symm], simp[simplicial_map.comp]} 
                   ... = id : by refl,
  end,

  calc finset.image g.map (finset.image f.map s) 
           = s : by simp[finset.image_image,f_inv_g_maps],
end   

lemma iso_simplices_inv' 
    {a : Type*} [decidable_eq a]
    {b : Type*} [decidable_eq b]
    {X : fin_simplicial_complex a}
    {Y : fin_simplicial_complex b}
    (f : simplicial_map (↑X : simplicial_complex a) (↑Y : simplicial_complex b))
    (g : simplicial_map (↑Y : simplicial_complex b) (↑X : simplicial_complex a))
    (f_inv_g : is_inverse_simplicial_iso f g)
  : ∀ (s : finset b), s ∈ Y.simplices 
    → finset.image f.map (finset.image g.map s) = s
:=     
begin
  have g_inv_f : is_inverse_simplicial_iso g f, 
       by exact ⟨f_inv_g.2, f_inv_g.1⟩,
  exact iso_simplices_inv g f g_inv_f,
end


-- Preparation:
-- simplicial isomorphisms preserve the dimensions of simplices
lemma iso_dim_preserving
    {a : Type*} [decidable_eq a]
    {b : Type*} [decidable_eq b]
    {X : fin_simplicial_complex a}
    {Y : fin_simplicial_complex b}
    (f : simplicial_map (↑X : simplicial_complex a) (↑Y : simplicial_complex b))
    (f_iso : is_simplicial_iso f)
  : ∀ s : finset a, s ∈ X.simplices
    → dim (finset.image f.map s) = dim s
:=
begin
  rcases f_iso with ⟨ g, f_inv_g : is_inverse_simplicial_iso f g⟩,
  assume s : finset a,
  assume s_in_SX : s ∈ X.simplices,

  have dim_leq : dim (finset.image f.map s) ≤ dim s, 
       by exact simplicial_map_dim_mono X Y f s s_in_SX,

  have dim_geq : dim (finset.image f.map s) ≥ dim s, from 
  begin
    let t := finset.image f.map s,

    have s_is_gt : finset.image g.map t = s,
         by {dsimp only[t], 
             rw[iso_simplices_inv f g f_inv_g s s_in_SX]},
    
    calc dim (finset.image f.map s) 
             = dim (finset.image f.map (finset.image g.map t))
             : by simp[s_is_gt]
         ... = dim t
             : by {congr, simp only[iso_simplices_inv' f g f_inv_g t _], 
                   exact s_is_gt}
         ... ≥ dim (finset.image g.map t)
             : by {simp, exact finset.card_image_le}
         ... = dim s 
             : by exact congr_arg dim s_is_gt,
  end,

  show _, by exact le_antisymm dim_leq dim_geq,
end   

-- Preparation:
-- and as a consequence: the same result for parity ∘ dim
lemma iso_pdim_preserving
    {a : Type*} [decidable_eq a]
    {b : Type*} [decidable_eq b]
    {X : fin_simplicial_complex a}
    {Y : fin_simplicial_complex b}
    (f : simplicial_map (↑X : simplicial_complex a) (↑Y : simplicial_complex b))
    (f_iso : is_simplicial_iso f)
  : ∀ s : finset a, s ∈ X.simplices
    → parity (dim (finset.image f.map s)) = parity (dim s)
:=
begin
  assume s, 
  assume s_in_SX : s ∈ X.simplices,
  show parity (dim (finset.image f.map s)) = parity (dim s), 
       by {congr, exact iso_dim_preserving f f_iso s s_in_SX},
end

-- the actual result: 
-- the Euler characteristic is invariant under simplicial isomorphisms
lemma iso_euler_char
    {a : Type*} [decidable_eq a]
    {b : Type*} [decidable_eq b]
    {X : fin_simplicial_complex a}
    {Y : fin_simplicial_complex b}
    (f : simplicial_map (↑X : simplicial_complex a) (↑Y : simplicial_complex b))
    (f_iso : is_simplicial_iso f)
  : χ X = χ Y 
:=
begin
  -- we convert the sums via finset.sum_bij', 
  -- using the bijections i and j between the sets of simplices, 
  -- given by f and its inverse, respectively
  -- preparations: 
  let i : Π (s : finset a), s ∈ X.simplices → finset b 
      := λ (s : finset a) (s_in_SX : s ∈ X.simplices), 
           finset.image f.map s,
  have i_welldef : Π (s : finset a) (s_in_SX : s ∈ X.simplices), 
                      i s s_in_SX ∈ Y.simplices 
       := f.is_simplicial,         

  have pdim_i : ∀ (s : finset a) (s_in_SX : s ∈ X.simplices), 
           (parity ∘ dim) s = (parity ∘ dim) (i s s_in_SX)
       := λ s s_in_SX, (iso_pdim_preserving f f_iso s s_in_SX).symm,   

  -- let g be the inverse of f:
  rcases f_iso with ⟨ g, f_inv_g : is_inverse_simplicial_iso f g⟩,

  let j : Π (s : finset b), s ∈ Y.simplices → finset a 
      := λ (s : finset b) (s_in_SY : s ∈ Y.simplices),
           finset.image g.map s,
  have j_welldef : Π (s : finset b) (s_in_SY : s ∈ Y.simplices), 
                     j s s_in_SY ∈ X.simplices
       := g.is_simplicial,

  -- i and j are inverses of each other
  have ji_is_id : ∀ (s : finset a) (s_in_SX : s ∈ X.simplices), 
       j (i s s_in_SX) (i_welldef s s_in_SX) = s, from 
  begin
    assume s,
    assume s_in_SX,
    calc j (i s s_in_SX) _ 
             = (finset.image g.map (finset.image f.map s)) 
             : by {refine rfl, exact i_welldef s s_in_SX}    
         ... = s     
             : by {apply iso_simplices_inv f g f_inv_g s _, 
                   exact s_in_SX},   
  end,

  have ij_is_id : ∀ (s : finset b) (s_in_SY : s ∈ Y.simplices), 
       i (j s s_in_SY) (j_welldef s s_in_SY) = s, from 
  begin  
    assume s,
    assume s_in_SY,
    calc i (j s s_in_SY) _ 
             = (finset.image f.map (finset.image g.map s)) 
             : by {refine rfl, exact j_welldef s s_in_SY}    
         ... = s     
             : by {apply iso_simplices_inv' f g f_inv_g s _, exact s_in_SY},
  end,

  -- finally, we can put everything together:
  calc χ X = ∑ (s : finset a) in X.simplices, parity (dim s) 
           : by refl    
       ... = ∑ (t : finset b) in Y.simplices, parity (dim t)
           : by exact finset.sum_bij' i i_welldef pdim_i 
                                      j j_welldef 
                                      ji_is_id ij_is_id   
       ... = χ Y 
           : by refl,
end  


/-
# Exercise [the Euler characteristic of zig]
-/

-- we compute the Euler characteristic of zig n 
-- by showing that zig n is isomorphic to zig 0;
-- to this end, we use the translation maps by ±n
-- and then use isomorphism invariance of χ
@[simp]
def f (n : int) : ℤ × ℤ → ℤ × ℤ 
:= λ x, (n + x.1, x.2)  

@[simp]
def g (n : int) : ℤ × ℤ → ℤ × ℤ 
:= λ x, (-n + x.1, x.2)  

-- To show that f and g are mutually inverse simplicial isos 
-- between zig 0 and zig n, we first introduce: 
-- a more flexible version of zig (allowing int parameter)
@[simp]
def zig_gen' 
    (k : int)
  : finset (finset (ℤ × ℤ))  
:= {{(k, 0), (k + 1, 0)}, 
    {(k, 0), (k, 1)}, 
    {(k, 1), (k + 1, 0)}}

@[simp]
def zig'
    (n : int)
  : fin_simplicial_complex (int × int)
:= fingen_simplicial_complex (zig_gen' n) 

-- Preparation: 
-- f and g are simplicial
lemma f_zig_gen'
    (k : int)
    (n : int)
  : ∀ s, s ∈ zig_gen' k → finset.image (f n) s ∈ (zig' (n+k)).simplices
:= 
begin
  assume s,
  assume s_in_zig_gen : s ∈ zig_gen' k,
  simp at s_in_zig_gen,

  -- zig_gen has only three elements; we check all of them individually:
  have f_00_10: finset.image (f n) {(k,0), (k+1,0)} ∈ (zig' (n+k)).simplices, from 
  begin 
    calc finset.image (f n) {(k,0), (k+1,0)} 
          = {(n+k,0), (n+k+1, 0)} 
          : by {simp, ring_nf} 
      ... ∈ (zig' (n+k)).simplices
          : by simp[zig',fingen_simplicial_complex],
    -- or just, very briefly:
    -- simp [zig'], ring_nf, unfold fingen_simplicial_complex, simp,      
  end,

  have f_00_01: finset.image (f n) {(k,0), (k,1)} ∈ (zig' (n+k)).simplices, 
       by simp[zig',fingen_simplicial_complex],

  have f_01_10: finset.image (f n) {(k,1), (k+1,0)} ∈ (zig' (n+k)).simplices, 
       by {simp[zig',fingen_simplicial_complex], ring_nf, simp},

  show _, 
       by exact or.elim3 s_in_zig_gen 
                (by {assume s, rw[s], exact f_00_10})
                (by {assume s, rw[s], exact f_00_01})
                (by {assume s, rw[s], exact f_01_10}),
end

-- and the simplicial property for zig' 0 → zig' n 
-- instead of zig' 0 → zig' (n+0)
-- (which is almost the same, but not quite the same)
lemma f_zig_gen_0
    (n : int)
  : ∀ s, s ∈ zig_gen' 0 → finset.image (f n) s ∈ (zig' n).simplices
:= 
begin
  assume s, 
  assume s_in_zig_gen: s ∈ zig_gen' 0,
  
  have unreduced_version : finset.image (f n) s ∈ (zig' (n+0)).simplices, 
        by exact f_zig_gen' 0 n s s_in_zig_gen,
  
  show _, by {ring_nf at unreduced_version, exact unreduced_version},
end

-- the simplicial map induced by f
@[simp]
def fzig
    (n : int)
  : @simplicial_map (ℤ × ℤ) (ℤ × ℤ) _ (zig' 0) (zig' n)
:= simplicial_map.mk 
     (f n)
     (simplicial_map_via_gen (zig_gen' 0) (f n) (f_zig_gen_0 n))

lemma g_zig_gen_0
    (n : int)
  : ∀ s, s ∈ zig_gen' n → finset.image (g n) s ∈ (zig' 0).simplices
:=
begin
  assume s, 
  assume s_in_zig_gen: s ∈ zig_gen' n,
  
  have unreduced_version : finset.image (g n) s ∈ (zig' (-n+n)).simplices, 
        by exact f_zig_gen' n (-n) s s_in_zig_gen,
  
  show _, by {ring_nf at unreduced_version, exact unreduced_version},
end

-- the simplicial map induced by g
@[simp]
def gzig 
    (n : int)
  : @simplicial_map (ℤ × ℤ) (ℤ × ℤ) _ (zig' n) (zig' 0)
:= simplicial_map.mk 
     (f (-n))
     (simplicial_map_via_gen (zig_gen' n) (g n) (g_zig_gen_0 n))

-- Preparation: 
-- fzig is a simplicial iso (with inverse gzig)
lemma fzig_is_iso 
      (n : int)
    : is_simplicial_iso (fzig n)
:= 
begin
  unfold is_simplicial_iso,
  use (gzig n),

  show is_inverse_simplicial_iso (fzig n) (gzig n), from 
  begin 
    unfold is_inverse_simplicial_iso,
    let gf := simplicial_map.comp (gzig n) (fzig n),
    let fg := simplicial_map.comp (fzig n) (gzig n),

    have gf_id : simplicial_map.comp (gzig n) (fzig n) 
               = id_simplicial_map (zig' n), from
    begin 
      have gf_map_id : gf.map = id, 
           by {dsimp only[gf], simp only[simplicial_map.comp, fzig, gzig, f], 
               ext, ring_nf, simp},

      show _, by exact sc_map_ext _ _ gf_map_id,
    end,       

    have fg_id : simplicial_map.comp (fzig n) (gzig n) 
               = id_simplicial_map (zig' 0), from
    begin 
      have fg_map_id : fg.map = id, 
           by {dsimp only[fg], simp only[simplicial_map.comp, fzig, gzig, f], 
               ext, ring_nf, simp},

      show _, by exact sc_map_ext _ _ fg_map_id,
    end,       

    show _, by exact ⟨fg_id, gf_id⟩, 
  end,
end      

-- Thus, we can compute the Euler characteristic of zig n, 
-- as outlined above
lemma euler_char_zig'
    (n : nat)
  : χ (zig n) = 0 
:= 
begin 
  calc χ (zig n) = χ (zig' n)
                 : by refl
             ... = χ (zig' 0) 
                 : by exact (iso_euler_char (fzig n) (fzig_is_iso n)).symm    
             ... = 0 
                 : by refl,
end    

/-
# Exercise [the Euler characteristic of zigzags]
-/

-- To complete the computation of the Euler characteristic 
-- of zigzags, it remains to compute the Euler characteristic 
-- of the intersection of zigzag n and zig n.

-- Preparation: 
-- more on the vertices of zig and zigzag

@[simp]
def fin_vertices 
    {a : Type*} [decidable_eq a]
    (X : fin_simplicial_complex a)
  : finset a
:= X.simplices.bUnion (λ s, s)

lemma fin_is_subset_closed 
    {a : Type*} [decidable_eq a]
    (X : fin_simplicial_complex a)
    (s : finset a)
    (s_in_SX : s ∈ X.simplices)
    (t : finset a)
    (t_sub_s : t ⊆ s)
  : t ∈ X.simplices  
:=
begin
  exact X.subset_closed s (by tauto) t t_sub_s,
end  

lemma single_vertex_sc 
    {a: Type*} [decidable_eq a]
    (X : fin_simplicial_complex a)
    (x : a)
    (x_is_VX : fin_vertices X = {x})
  : X.simplices = {{x}, ∅ }
:=
begin
  have SX_sub_x : X.simplices ⊆ {{x},∅}, from 
  begin 
    assume s, 
    assume s_in_SX : s ∈ X.simplices,

    have s_sub_x : s ⊆ {x}, from 
    begin 
      assume y,
      assume y_in_s : y ∈ s,

      have y_in_VX : y ∈ fin_vertices X, from 
      begin 
        dsimp only[fin_vertices] at *,
        apply finset.mem_bUnion.mpr,
        use s,

        exact ⟨s_in_SX, y_in_s⟩,
      end,

      show _, by {rw[x_is_VX] at y_in_VX, exact y_in_VX},
    end,

    show _, by finish,
  end,

  have x_sub_SX : {{x},∅} ⊆ X.simplices, from 
  begin 
    have x_in_SX : {x} ∈ X.simplices, from 
    begin 
      dsimp only[fin_vertices] at x_is_VX,

      have ex_s : ∃ s (s_in_SX : s ∈ X.simplices), x ∈ s, from 
      begin 
        apply finset.mem_bUnion.mp,
        rw[x_is_VX],
        exact finset.mem_singleton.mpr rfl,
      end,
      rcases ex_s with ⟨s, ⟨ s_in_SX, x_in_s ⟩⟩,
      have x_sub_s : {x} ⊆ s, 
           by exact finset.singleton_subset_iff.mpr x_in_s,

      show _, by exact fin_is_subset_closed X s s_in_SX {x} x_sub_s,
    end,

    have empty_in_SX : ∅ ∈ X.simplices, 
         by exact fin_is_subset_closed X {x} x_in_SX ∅ (by tauto),
  
    show _, 
         by {assume s,
             assume s_in_xempty : s ∈ {{x},∅},
             finish},
  end,

  show _, 
       by {apply finset.coe_inj.mp, 
           exact set.eq_of_subset_of_subset SX_sub_x x_sub_SX},
end    

lemma union_vertices 
    {a : Type*} [decidable_eq a]
    (X : fin_simplicial_complex a)
    (Y : fin_simplicial_complex a)
  : fin_vertices (union_sc X Y) = fin_vertices X ∪ fin_vertices Y
:=
begin
  -- this is only elementary logic
  ext x,
  simp only[fin_vertices, union_sc, finset.mem_bUnion],
  -- both implications are simple:
  split, 
    finish, 
    finish,
end    

lemma inter_vertices 
    {a : Type*} [decidable_eq a]
    (X : fin_simplicial_complex a)
    (Y : fin_simplicial_complex a)
  : fin_vertices (inter_sc X Y) = fin_vertices X ∩ fin_vertices Y
:=
begin
  -- we simplify down to basic Boolean expressions
  ext x,
  simp [fin_vertices, inter_sc, finset.mem_bUnion, finset.mem_inter],

  -- the first implication is basic logic
  have left_to_right : (∃ s, (s ∈ X.simplices ∧ s ∈ Y.simplices) ∧ x ∈ s)
                     → (∃ s, s ∈ X.simplices ∧ x ∈ s) ∧ ∃ s, s ∈ Y.simplices ∧ x ∈ s,
  by tauto,

  -- the converse implication uses the properties of simplicial complexes
  have right_to_left : ((∃ s, s ∈ X.simplices ∧ x ∈ s) ∧ ∃ s, s ∈ Y.simplices ∧ x ∈ s)
                     → (∃ s, (s ∈ X.simplices ∧ s ∈ Y.simplices) ∧ x ∈ s), from 
  begin 
    assume ex_s_X_t_Y,
    rcases ex_s_X_t_Y with ⟨ ⟨ s, ⟨ s_in_SX, x_in_s⟩⟩ 
                           , ⟨ t, ⟨ t_in_SY, x_in_t⟩⟩⟩,
    let u := s ∩ t,
    use u,

    have u_in_SX : u ∈ X.simplices, 
         by exact fin_is_subset_closed X s s_in_SX u (finset.inter_subset_left s t),                       

    have u_in_SY : u ∈ Y.simplices, 
         by exact fin_is_subset_closed Y t t_in_SY u (finset.inter_subset_right s t),                       

    have x_in_u : x ∈ u, 
         by exact finset.mem_inter_of_mem x_in_s x_in_t,

    show _, by exact ⟨ ⟨u_in_SX, u_in_SY⟩, x_in_u⟩,
  end,
  
  show _, by exact ⟨ left_to_right, right_to_left ⟩,
end    


-- Preparation:
-- the vertices of a generated simplicial complex
-- can be described in terms of the generating set
lemma fingen_vertices 
    {a : Type*} [decidable_eq a]
    (S : finset (finset a))
  : fin_vertices (fingen_simplicial_complex S)  
  = S.bUnion (λ s, s)
:=
begin 
  -- this is a straightforward reformulation
  -- that can be performed almost automatically
  ext, -- or: ext x (for better readability of the auto-named variables)
  simp [fin_vertices, finset.mem_bUnion, fingen_simplicial_complex],
  tauto,
end

lemma zig_vertices 
    (n : nat)
  : fin_vertices (zig n)
  = { (n,0), (n,1), (n+1,0) }    
:=
begin
  -- we first simplify the expression to a simple equivalence 
  ext x,
  simp[zig, fingen_vertices, finset.mem_bUnion], 
  -- ... which can be checked automatically
  tauto,
end

lemma zig_zig_inter_succ 
    (n : nat)
  : fin_vertices (zig n) ∩ fin_vertices (zig (n + 1))
  = {(n+1,0)}
:= 
begin
  -- we first simplify the expression to a simple equivalence 
  simp only[zig_vertices],
  ext x,
  simp only[finset.mem_inter],
  simp,
  ring_nf,
  -- we show both implications separately, 
  -- which can be performed almost automatically
  split,
    -- left → right
    {assume x_in_inter,
    finish},
    -- right → left
    tauto,
end

lemma zig_vertices_leq 
    (n : nat)
    (x : ℤ × ℤ)
    (x_in_zig : x ∈ fin_vertices (zig n))
  : x.1 ≤ n+1
:= 
begin 
  -- we use the explicit description of the vertices of zig n
  simp[zig_vertices] at x_in_zig,
  -- ... then go through the cases
  cases x_in_zig,
    -- x = (n,0)
    {calc x.1 = n   : by simp[x_in_zig]
          ... ≤ n+1 : by linarith,},
    cases x_in_zig,
    -- x = (n,1)
    {calc x.1 = n   : by simp[x_in_zig]
          ... ≤ n+1 : by linarith},
    -- x = (n+1,0)        
    {calc x.1 = n+1 : by simp[x_in_zig]
          ... ≤ n+1 : by linarith},
end      

lemma zig_vertices_geq 
    (n : nat)
    (x : ℤ × ℤ)
    (x_in_zig : x ∈ fin_vertices (zig n))
  : ↑n ≤ x.1
:= 
begin 
  -- we use the explicit description of the vertices of zig n
  simp [zig_vertices] at x_in_zig,
  -- ... and then go through the cases
  cases x_in_zig,
    -- x = (n,0)
    {calc x.1 = n : by simp[x_in_zig]
          ... ≥ n : by linarith,},
    cases x_in_zig,
    -- x = (n,1)
    {calc x.1 = n : by simp[x_in_zig]
          ... ≥ n : by linarith},
    -- x = (n+1,0)        
    {calc x.1 = n+1 : by simp[x_in_zig]
          ... ≥ n   : by linarith},
end      

lemma zig_zig_inter_nonsucc 
    (k : nat)
    (n : nat)
    (k1_leq_n : k + 1 ≤ n)
  : fin_vertices (inter_sc (zig k) (zig (n + 1)))
  = ∅ 
:= 
begin
   apply finset.eq_empty_of_forall_not_mem,
   assume x : ℤ × ℤ,
   assume x_in_inter : x ∈ fin_vertices (inter_sc (zig k) (zig (n+1))),
   simp only[inter_vertices] at x_in_inter,
   have x_in_zig_k : x ∈ fin_vertices (zig k), 
        by exact finset.mem_of_mem_inter_left x_in_inter,
   have x_in_zig_n1 : x ∈ fin_vertices (zig (n+1)),
        by exact finset.mem_of_mem_inter_right x_in_inter,

   have contradiction : x.1 < x.1, by 
   calc x.1 ≤ ↑k+1 : by exact zig_vertices_leq k x x_in_zig_k
        ... < ↑n+1 : by {norm_cast, linarith[k1_leq_n],} 
        ... ≤ x.1  : by exact zig_vertices_geq (n+1) x x_in_zig_n1, 
   show false, by exact x.fst.lt_irrefl contradiction,
end

lemma zigzag_vertices_leq 
    (n : nat)
    (x : ℤ × ℤ)
    (x_in_zigzag : x ∈ fin_vertices (zigzag n))
  : x.1 ≤ n
:= 
begin
  induction n with m ind_hyp,

  case nat.zero : 
  begin 
    have zz0_vertices : fin_vertices (zigzag 0) = {(0,0)}, 
         by refl,
    calc x.1 = (0,0).1 : by {rw[zz0_vertices] at x_in_zigzag, simp[finset.mem_insert] at x_in_zigzag, rw[x_in_zigzag]}
         ... ≤ 0       : by exact rfl.ge,
  end,

  case nat.succ : 
  begin 
    have zz_vertices : fin_vertices (zigzag (m+1))
                     = fin_vertices (zigzag m)
                     ∪ fin_vertices (zig m), 
    by exact union_vertices _ _,
    simp only [zz_vertices,finset.mem_union] at x_in_zigzag,
    cases x_in_zigzag,
      -- x is a vertex of zigzag m  
      {calc x.1 ≤ m   : by exact ind_hyp x_in_zigzag
            ... ≤ m+1 : by linarith},
      -- x is a vertex of zig m
      {exact zig_vertices_leq m x x_in_zigzag},
  end,
end    

lemma zigzag_inter_non_succ_vertices 
    (k : nat)
    (n : nat)
    (k1_leq_n : k + 1 ≤ n)
  : fin_vertices (zigzag k) ∩ fin_vertices (zig n)
  = ∅ 
:= 
begin 
   apply finset.eq_empty_of_forall_not_mem,
   assume x : ℤ × ℤ,
   assume x_in_inter : x ∈ fin_vertices (zigzag k) ∩ fin_vertices (zig n),
   have x_in_zigzag_k : x ∈ fin_vertices (zigzag k), 
        by exact finset.mem_of_mem_inter_left x_in_inter,
   have x_in_zig_n : x ∈ fin_vertices (zig n),
        by exact finset.mem_of_mem_inter_right x_in_inter,

   have contradiction : x.1 < x.1, by 
   calc x.1 ≤ ↑k   : by exact zigzag_vertices_leq k x x_in_zigzag_k 
        ... < ↑k+1 : by linarith
        ... ≤ ↑n   : by {norm_cast, exact k1_leq_n}
        ... ≤ x.1  : by exact zig_vertices_geq n x x_in_zig_n, 

   show false, 
        by exact x.fst.lt_irrefl contradiction,
end

lemma zigzag_inter_vertices 
    (n : nat)
  : fin_vertices (inter_sc (zigzag n) (zig n))
  = {(n,0)}
:= 
begin 
  induction n with m ind_hyp,

  case nat.zero : {refl},

  case nat.succ :
  begin
    calc fin_vertices (inter_sc (zigzag (m+1)) (zig (m+1))) 
             = fin_vertices (zigzag (m+1))
             ∩ fin_vertices (zig (m+1))
             : by exact inter_vertices _ _
         ... = fin_vertices (union_sc (zigzag m) (zig m)) 
             ∩ fin_vertices (zig (m+1))
             : by simp[zigzag]
         ... = ( fin_vertices (zigzag m) ∪ fin_vertices (zig m) ) 
             ∩ ( fin_vertices (zig (m+1)) )
             : by {congr, exact union_vertices _ _} 
         ... = ( fin_vertices (zigzag m) ∩ fin_vertices (zig (m+1)) )
             ∪ ( fin_vertices (zig m) ∩ fin_vertices (zig (m+1)) )
             : by exact finset.inter_distrib_right _ _ _
         ... = ∅ 
             ∪ {(m+1,0)}
             : by {congr, exact zigzag_inter_non_succ_vertices m (m+1) (by linarith),
                   exact zig_zig_inter_succ m}             
         ... = {(m+1,0)} 
             : by simp,
  end,
end

-- Preparation:
-- we compute the set of simplices of this intersection
lemma zigzag_inter 
    (n : nat)
  : (inter_sc (zigzag n) (zig n)).simplices 
  = { {(n,0)}, ∅ }  
:= 
begin 
  have inter_has_single_vertex 
     : fin_vertices (inter_sc (zigzag n) (zig n)) = {(n,0)},
       by exact zigzag_inter_vertices n,
  show _, by exact single_vertex_sc _ _ inter_has_single_vertex,
end

lemma euler_char_zigzag_inter'
    (n : nat)
  : χ (inter_sc (zigzag n) (zig n)) = 1
:=
begin
  -- with the explicit description of the intersection, 
  -- this is just a computation
  simp only[euler_char, zigzag_inter n], 
  refl,
end      

lemma euler_char_zigzag'
      (n : nat)
    : χ (zigzag n) = 1 - n  
:=
begin
  induction n with m ind_hyp,

  -- base case: 0
  case nat.zero : {refl},

  -- induction step: m -> m + 1
  case nat.succ : 
  begin
    calc χ (zigzag (m+1))
         = χ (zigzag m) 
         + χ (zig m) 
         - χ (inter_sc (zigzag m) (zig m)) 
         : by exact euler_char_union (zigzag m) (zig m)
     ... = 1 - m + 0 - 1
         : by simp[ind_hyp, euler_char_zig', euler_char_zigzag_inter']
     ... = 1 - (m+1) 
         : by ring,
  end
end

/-
# Exercise [wedges of simplicial complexes]
-/

-- We define the wedge via quotients:
-- the quotient relation identifies the two basepoints in the disjoint union;
-- (we model disjoint unions on the type level by sum types);
-- This leads to a setoid 
-- (i.e., a pair of a type and an equivalence relation on this type), 
-- whence to a quotient.
-- Because we want to define the simplices of the wedge 
-- by applying the canonical inclusion maps to the simplices of the two summands, 
-- we should keep track of decidability of equality.

open sum -- to simplify notation for sum types

-- the wedge relation, identifying the two basepoints
@[simp]
def wedge_rel 
    {a b : Type*}
    (x0 : a)
    (y0 : b)
  : sum a b → sum a b → Prop 
:= λ x y, x = y 
       ∨ (x = inl x0 ∧ y = inr y0)
       ∨ (x = inr y0 ∧ y = inl x0)

-- Preparation:
-- the wedge relation is an equivalence relation

-- for efficiency reasons, we prove transitivity separately
lemma wedge_rel_is_transitive 
    {a b : Type*}
    (x0 : a)
    (y0 : b)
  : transitive (wedge_rel x0 y0)
:=
begin
  let r := wedge_rel x0 y0,
  assume x y z,
  assume r_xy : r x y,
  assume r_yz : r y z,

  -- we only need to go through the cases of r_xy (and r_yz)
  have case_x_is_y : x = y → r x z, 
       by {assume x_is_y, 
           subst x_is_y, exact r_yz},

  have case_xx0_yy0 : x = inl x0 ∧ y = inr y0 → r x z, 
       by {assume xx0_yy0,
           dsimp only[r], finish},

  have case_xy0_yx0 : x = inr y0 ∧ y = inl x0 → r x z, 
       by {assume xy0_yx0,
           dsimp only[r], finish},

  show r x z, 
       by exact or.elim3 r_xy 
                         case_x_is_y case_xx0_yy0 case_xy0_yx0,
end

lemma wedge_rel_is_equivrel 
    {a b : Type*}
    (x0 : a)
    (y0 : b)
  : equivalence (wedge_rel x0 y0)
:=
begin
  let r := wedge_rel x0 y0,

  have r_is_reflexive: reflexive r, from 
  begin 
    assume x, 
    show r x x, by {dsimp[r], exact or.inl rfl} ,
  end,

  have r_is_symmetric: symmetric r, from 
  begin 
    assume x y,
    assume r_xy : r x y,
    show r y x, by {dsimp[r] at r_xy, finish}
  end,

  have r_is_transitive: transitive r, 
       by exact wedge_rel_is_transitive x0 y0,

  show equivalence r, 
       by exact ⟨r_is_reflexive, 
                ⟨r_is_symmetric, 
                 r_is_transitive⟩⟩,
end    

-- Preparation: 
-- moreover, the wedge relation is clearly decidable
instance wedge_rel_decidable_eq 
    (a b : Type*) [decidable_eq a] [decidable_eq b]
    (x0 : a)
    (y0 : b)
  : Π (x y : sum a b), decidable (wedge_rel x0 y0 x y) 
:= 
λ x y,
  if x_eq_y : x = y 
     then is_true (or.inl x_eq_y) 
          else if bp_eq : x = inl x0 ∧ y = inr y0 
                  then is_true (or.inr (or.inl bp_eq))
                  else if bp_eq_flip : x = inr y0 ∧ y = inl x0 
                          then is_true (or.inr (or.inr bp_eq_flip))
                          else is_false (by finish)

-- the wedge setoid, consisting of the wedge relation on the sum type
def wedge_setoid 
    (a b : Type*)
    (x0 : a)
    (y0 : b)
  : setoid (sum a b)  
:= {r     := wedge_rel x0 y0, 
    iseqv := wedge_rel_is_equivrel x0 y0}  

-- Preparation:
-- the wedge type is the corresponding quotient type
@[simp]
def wedge_type 
    {a b : Type*} [decidable_eq a] [decidable_eq b]
    (x0 : a)
    (y0 : b)
:= quotient (wedge_setoid a b x0 y0)

instance decidable_eq_wedge 
    (a b : Type*) [decidable_eq a] [decidable_eq b]
    (x0 : a)
    (y0 : b)
  : decidable_eq (wedge_type x0 y0)
:= @quotient.decidable_eq (sum a b) (wedge_setoid a b x0 y0) 
                          (wedge_rel_decidable_eq a b x0 y0)

-- the maps into the wedge
def wedge_inl 
    {a b : Type*} [decidable_eq a] [decidable_eq b]
    (x0 : a)
    (y0 : b)
  : a → wedge_type x0 y0 
:= λ x, quot.mk _ (inl x)

def wedge_inr
    {a b : Type*} [decidable_eq a] [decidable_eq b]
    (x0 : a)
    (y0 : b)
  : b → wedge_type x0 y0
:= λ y, quot.mk _ (inr y)

def wedge_simplices_inl 
    {a b : Type*} [decidable_eq a] [decidable_eq b]
    (X : fin_simplicial_complex a)
    (x0 : a)
    (Y : fin_simplicial_complex b)
    (y0 : b)
  : finset (finset (wedge_type x0 y0))
:= finset.image (λ s, finset.image (wedge_inl x0 y0) s) X.simplices

def wedge_simplices_inr 
    {a b : Type*} [decidable_eq a] [decidable_eq b]
    (X : fin_simplicial_complex a)
    (x0 : a)
    (Y : fin_simplicial_complex b)
    (y0 : b)
  : finset (finset (wedge_type x0 y0))
:= finset.image (λ s, finset.image (wedge_inr x0 y0) s) Y.simplices


def wedge_inl_sc 
    {a b : Type*} [decidable_eq a] [decidable_eq b]
    (X : fin_simplicial_complex a)
    (x0 : a)
    -- (x0_in_X : x0 ∈ vertices X)
    (Y : fin_simplicial_complex b)
    (y0 : b)
    -- (y0_in_Y : y0 ∈ vertices Y)
  : fin_simplicial_complex (wedge_type x0 y0)
:= fingen_simplicial_complex (wedge_simplices_inl X x0 Y y0)

def wedge_inr_sc 
    {a b : Type*} [decidable_eq a] [decidable_eq b]
    (X : fin_simplicial_complex a)
    (x0 : a)
    -- (x0_in_X : x0 ∈ vertices X)
    (Y : fin_simplicial_complex b)
    (y0 : b)
    -- (y0_in_Y : y0 ∈ vertices Y)
  : fin_simplicial_complex (wedge_type x0 y0)
:= fingen_simplicial_complex (wedge_simplices_inr X x0 Y y0)


-- One could prove directly that wedge_simplices_inl is indeed subset closed
-- (it is not entirely obvious, though);
-- instead, we take the simplicial complexes generated by wedge_simplices_inl/inr
-- and then take their union;

-- The wedge is the union of wedge_inl_sc and wedge_inr_sc;
-- we provide 
-- * a raw version (without the condition that the points are actual vertices)
-- * and the usual genuine wedge of pointed (finite) simplicial complexes 
-- if one of the points is not a vertex of the corresponding complex,
-- then the raw wedge in fact models the disjoint union

-- The raw version:
def raw_wedge_sc 
    {a b : Type*} [decidable_eq a] [decidable_eq b]
    (X : fin_simplicial_complex a)
    (x0 : a)
    (Y : fin_simplicial_complex b)
    (y0 : b)
  : fin_simplicial_complex (wedge_type x0 y0)
:= union_sc (wedge_inl_sc X x0 Y y0) 
            (wedge_inr_sc X x0 Y y0)

-- some examples
#eval χ (raw_wedge_sc torus 0 torus 0)
#eval χ (raw_wedge_sc projective_plane 0 torus 0)
#eval χ (raw_wedge_sc moebius 0 moebius 0)
#eval χ (raw_wedge_sc (zig 0) (0,0) (zig 0) (0,0))


-- For the genuine version:
-- Preparation: pointed finite simplicial complexes 
-- are finite simplicial complexes together with a vertex
structure ptd_simplicial_complex 
    (a : Type*) [decidable_eq a]
:= mk :: (complex   : fin_simplicial_complex a)
         (basepoint : a)
         (bpt_is_vertex : basepoint ∈ fin_vertices complex)

-- Preparation:
-- the basepoint as vertex of the wedge
lemma simplex_from_vertex 
    {a : Type*} [decidable_eq a]
    (X : fin_simplicial_complex a)
    (x : a)
    (x_in_VX : x ∈ fin_vertices X)
  : ∃ s (s_in_SX : s ∈ X.simplices), x ∈ s
:=
begin
  exact finset.mem_bUnion.mp x_in_VX,
end    

lemma vertex_from_simplex
    {a : Type*} [decidable_eq a]
    (X : fin_simplicial_complex a)
    (x : a)
    (s : finset a)
    (s_in_SX : s ∈ X.simplices)
    (x_in_s : x ∈ s)
  : x ∈ fin_vertices X
:=
begin
  simp only[fin_vertices, finset.mem_bUnion],
  use s,
  show _, by exact ⟨ s_in_SX, x_in_s⟩,
end  

lemma wedge_basepoint_is_vertex
    {a b : Type*} [decidable_eq a] [decidable_eq b]
    (X : ptd_simplicial_complex a)
    (Y : ptd_simplicial_complex b)
  : wedge_inl X.basepoint Y.basepoint X.basepoint 
  ∈ fin_vertices (raw_wedge_sc X.complex X.basepoint Y.complex Y.basepoint)
:=
begin
  rcases X with ⟨ X', x0, x0_in_VX ⟩,
  rcases Y with ⟨ Y', y0, y0_in_VY ⟩,

  let W  := raw_wedge_sc X' x0 Y' y0,
  let w0 := wedge_inl x0 y0 x0,

  show w0 ∈ fin_vertices W, from 
  begin 
    -- because x0 is a vertex of X, it lies in a simplex of X
    have x0_in_SX : ∃ s ∈ X'.simplices, x0 ∈ s, 
         by exact simplex_from_vertex X' x0 x0_in_VX,
    rcases x0_in_SX with ⟨ s, ⟨ s_in_SX, x0_in_s ⟩⟩,

    -- we can push this simplex s to the wedge
    let sr := finset.image (wedge_inl x0 y0) s,
    have sr_in_SX_inl : sr ∈ (wedge_inl_sc X' x0 Y' y0).simplices,
         by {simp only[wedge_inl_sc,fingen_simplicial_complex,fingen_simplices,finset.mem_bUnion], 
             use sr,
             simp only[wedge_simplices_inl,finset.mem_powerset,finset.mem_image],
             split, 
               {use s, exact ⟨ s_in_SX, by tauto⟩}, 
               {refl}},              
    have sr_in_SW : sr ∈ W.simplices, 
         by {dsimp only[W], simp only[raw_wedge_sc,union_sc,finset.mem_union], 
             apply or.intro_left, exact sr_in_SX_inl},
    -- by construction, w0 lies in this push-forward simplex ...          
    have w0_in_sr : w0 ∈ sr, 
         by {dsimp only[sr,w0], apply finset.mem_image_of_mem, exact x0_in_s},

    -- ... and thus we conclude that w0 indeed is a vertex of the wedge
    show _, by exact vertex_from_simplex W w0 sr sr_in_SW w0_in_sr,
  end,
end  


def wedge_sc 
    {a b : Type*} [decidable_eq a] [decidable_eq b]
    (X : ptd_simplicial_complex a)
    (Y : ptd_simplicial_complex b)
  : ptd_simplicial_complex (wedge_type X.basepoint Y.basepoint)  
:= ptd_simplicial_complex.mk 
     (raw_wedge_sc X.complex X.basepoint Y.complex Y.basepoint)
     (wedge_inl X.basepoint Y.basepoint X.basepoint)
     (wedge_basepoint_is_vertex X Y)

-- A simple example:
-- self-wedges of zig 0 (with the basepoint (0,0))
def ptd_zig 
  : ptd_simplicial_complex (ℤ × ℤ)
:= ptd_simplicial_complex.mk 
     (zig 0)
     (0,0)
     (begin 
        simp only[fin_vertices, finset.mem_bUnion], 
        use {(0,0), (1,0)}, 
        simp[zig, fingen_simplicial_complex],
      end)  

def ptd_double_zig 
:= wedge_sc ptd_zig ptd_zig

def ptd_triple_zig 
:= wedge_sc ptd_double_zig ptd_zig

def ptd_sixfold_zig
:= wedge_sc ptd_triple_zig ptd_triple_zig

#eval χ ptd_double_zig.complex
#eval χ ptd_triple_zig.complex
#eval χ ptd_sixfold_zig.complex


-- Now, one could go on 
-- * to establish that inl and inr define simplicial maps; 
-- * to prove the universal property of wedges of pointed simplicial complexes;
-- * to prove a formula for the Euler characteristic of wedges of pointed complexes; 
-- * to model zigzags via iterated wedges of zig 0;
-- * ... 

/-
# Exercise [Roses]
-/

-- Formalising roses as iterated wedges is tricky: 
-- The canonical type of roses is an involved dependent type: 
-- The type of each wedge step depends on the basepoints,
-- which in turn depend on the previous steps of the construction. 

-- The most straightforward way to implement this would be to give 
-- a mutually recursive definition of the types and basepoints. 
-- However Lean does not support such induction-recursion. 

-- We trick around this by bundling simplicial complexes and 
-- their types into a new structure rose_t. 
-- Moreover, we also need to keep track of instances of decdiable_eq.

structure rose_t
:= mk :: (type : Type)
         (dec_eq_type : decidable_eq type)
         (sc : @ptd_simplicial_complex type dec_eq_type)

-- We need a _global_ instance,
-- otherwise the implicitly triggered type class inference 
-- for decidable_eq on wedge_type etc will not succeed.

instance (r : rose_t) 
: decidable_eq r.type 
:= r.dec_eq_type

-- The inductive construction of roses:
def rose
  : nat → rose_t
| 0     := rose_t.mk (ℤ × ℤ) (by apply_instance) (ptd_zig)
| (n+1) := 
begin
  let t := wedge_type (rose n).sc.basepoint ptd_zig.basepoint,
  let dec_eq_t := @decidable_eq_wedge (rose n).type (ℤ × ℤ) 
                                      (rose n).dec_eq_type (by apply_instance)
                                      (rose n).sc.basepoint ptd_zig.basepoint,                    
  -- we take the wedge of rose n and ptd_zig:
  let X := wedge_sc (rose n).sc ptd_zig,
  let r := rose_t.mk t dec_eq_t X,
 
  exact r,
end          

-- plausibility check:
#eval finset.card (simplices_of_dim (rose 2).sc.complex 0) -- 7
#eval finset.card (simplices_of_dim (rose 2).sc.complex 1) -- 9

#eval χ (rose 0).sc.complex --  0
#eval χ (rose 1).sc.complex -- -1
#eval χ (rose 2).sc.complex -- -2
-- #eval χ (rose 3).sc.complex -- deterministic timeout :)