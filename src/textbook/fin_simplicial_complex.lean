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

open classical  -- we work in classical logic


/-
# Finiteness of simplicial complexes
-/

-- A simplicial complex is finite if its set of simplices is finite
def is_finite_simplicial_complex 
    {a : Type*}
    (X : simplicial_complex a)
:= set.finite (X.simplices)    

-- Finiteness of the set of simplices 
-- is equivalent to 
-- finiteness of the set of vertices

lemma fin_simplices_fin_vertices
    {a : Type*}
    (X : simplicial_complex a)
    (X_fin_S : is_finite_simplicial_complex X)
  : set.finite (vertices X)  
:=
begin
  let S := X.simplices,
  let V := vertices X,

  -- Because S is finite, 
  -- also V (as finite union of finsets) is finite
  let S' := { (↑s : set a) | s ∈ S },
  let U  := set.sUnion S',

  have U_finite : set.finite U, from 
  begin 
    -- finite unions of finite sets are finite
    apply set.finite.sUnion,

    -- the set S' is finite because S is finite
    show set.finite S', 
         by {simp only[S', bex_def],
             apply set.finite.image (λs, ↑s) (by assumption)},

    -- all elements of S' are finite sets
    show ∀ (t : set a), t ∈ S' → t.finite, from 
    begin
      assume t : set a,
      assume t_in_S' : t ∈ S',
      dsimp only[S'] at t_in_S',
      rcases t_in_S' with ⟨s, ⟨s_in_S, t_is_s : ↑s = t⟩⟩,
      have s_finite : set.finite ↑s, 
           by exact finset.finite_to_set s, 
      show t.finite, 
           by {induction t_is_s, exact s_finite},
    end,  
  end,

  have V_sub_U : V ⊆ U, from 
  begin 
    assume x,
    assume x_in_V : x ∈ V,
    dsimp only[V, vertices] at x_in_V,
    finish,
  end,

  show set.finite V, 
       by exact set.finite.subset U_finite V_sub_U,
end

lemma fin_vertices_fin_simplices
    {a : Type*}
    (X : simplicial_complex a)
    (X_fin_V : set.finite (vertices X))
  : is_finite_simplicial_complex X 
:=
begin
  -- S is finite,
  -- because S is a subset of the powerset of vertices X,
  -- which is finite (as powerset of a finite set)
  let S : set (finset a) := X.simplices,

  let PV := finset.powerset (set.finite.to_finset X_fin_V),

  have S_sub_PV : S ⊆ PV, from 
  begin
    assume s,
    assume s_in_S : s ∈ S,

    show s ∈ PV, from 
    begin
      simp only[finset.mem_powerset],
      assume x,
      assume x_in_s : x ∈ s,

      show x ∈ X_fin_V.to_finset,
           by {apply set.mem_to_finset.mpr, unfold vertices, 
               use s, exact ⟨ s_in_S, x_in_s ⟩},
    end,       
  end,

  have PV_finite : set.finite ↑PV, 
       by exact finset.finite_to_set PV,

  show set.finite S, 
       by exact set.finite.subset PV_finite S_sub_PV,
end   


/-
# Finite simplicial complexes
-/

/- We provide a separate structure for simplicial complexes 
   with a priori finiteness guarantee (for better computability).
-/
structure fin_simplicial_complex (a : Type*)
:= mk :: (simplices : finset (finset a))
         (subset_closed : is_subset_closed (simplices : set (finset a)))

-- Converting a fin_simplicial_complex to a simplicial_complex
def to_sc 
    {a : Type*}
    (X : fin_simplicial_complex a)
  : simplicial_complex a
:= simplicial_complex.mk 
     (↑X.simplices)
     (X.subset_closed)

instance {a : Type*}
: has_coe (fin_simplicial_complex a) (simplicial_complex a)
:= { coe := to_sc }

-- Finite simplicial complexes are indeed finite
lemma fin_sc_is_finite
    {a : Type*}
    (X : fin_simplicial_complex a)
  : is_finite_simplicial_complex (↑X : simplicial_complex a)
:=
begin
  exact finset.finite_to_set X.simplices,
end       

-- Converting a simplicial_complex that is finite 
-- to a fin_simplicial_complex 
noncomputable
def to_fin_sc
    {a : Type*}
    (X : simplicial_complex a)
    (fin_X : is_finite_simplicial_complex X)
  : fin_simplicial_complex a  
:= 
begin
  let SX : set (finset a) := X.simplices,
  have fin_SX : set.finite SX, by assumption,

  let S : finset (finset a) 
        := set.finite.to_finset fin_SX, -- non-computable!

  -- The finset S is closed under taking subsets, 
  -- because this holds for the set of simplices of X
  have sub_S : is_subset_closed (↑S : set (finset a)), from
  begin
    assume s : finset a,
    assume s_in_S : s ∈ S,
    have s_in_SX : s ∈ X.simplices, by finish,

    assume t : finset a, 
    assume t_sub_s : t ⊆ s,

    show t ∈ S, 
         by simp[X.subset_closed s s_in_SX t t_sub_s],
  end,

  -- We now have all the finiteness/subset guarantees 
  -- to build the desired finite simplicial complex:
  exact fin_simplicial_complex.mk S sub_S,
end

-- The dimension of a finite complex is the maximum
-- dimension of its simplices.
@[simp]
def dim_of_fin_complex
    {a : Type*}
    (X : fin_simplicial_complex a)
  : int
:= match finset.max (finset.bUnion X.simplices (λ s, {dim s})) with
    | option.none := -1   -- degenerate ∅ case
    | option.some z := z
  end

@[simp]
def fin_vertices
    {a : Type*} [decidable_eq a]
    (X : fin_simplicial_complex a)
  : finset a
:= finset.bUnion X.simplices (λ s, s)