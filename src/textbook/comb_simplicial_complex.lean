/-
Copyright (c) 2022 Clara Löh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.txt.
Author: Clara Löh.
-/

import tactic          -- standard proof tactics
import data.set        -- basics on sets
import data.set.finite -- basics on finite sets
import data.finset     -- type-level finite sets
import .simplicial_complex     -- basics on simplicial complexes
import .gen_simplicial_complex -- generation of finite simplicial complexes

open classical  -- we work in classical logic

/-
# The union/intersection of two simplicial complexes
-/

-- Union of two finite simplicial complexes

lemma union_is_subset_closed 
    {a : Type*} [decidable_eq a]
    (S : finset (finset a))
    (T : finset (finset a))
    (S_sub_closed : is_subset_closed (S : set (finset a)))
    (T_sub_closed : is_subset_closed (T : set (finset a)))
  : is_subset_closed (↑(S ∪ T) : set (finset a))
:=
begin
  assume s,
  assume s_in_ST : s ∈ ↑(S ∪ T),
  assume t,
  assume t_sub_s : t ⊆ s,
  simp only [is_subset_closed, finset.mem_coe] at *,

  have case_s_in_S : s ∈ S → t ∈ S ∪ T, from
  begin
    assume s_in_S: s ∈ S,
    have t_in_S : t ∈ S, 
         by exact S_sub_closed s s_in_S t t_sub_s,
    show t ∈ S ∪ T, by finish, 
    -- or: exact or.inl (S_sub_closed s s_in_S t t_sub_s),
  end,

  have case_s_in_T : s ∈ T → t ∈ S ∪ T, from
  begin 
    assume s_in_T : s ∈ T,
    have t_in_T : t ∈ T, 
         by exact T_sub_closed s s_in_T t t_sub_s,
    show t ∈ S ∪ T, by finish,
  end,

  show _, 
       by {simp only[finset.mem_union] at s_in_ST, 
           exact or.elim s_in_ST case_s_in_S case_s_in_T},
end    

def union_sc 
    {a : Type*} [decidable_eq a]
    (X : fin_simplicial_complex a)
    (Y : fin_simplicial_complex a)
  : fin_simplicial_complex a
:= fin_simplicial_complex.mk
      (X.simplices ∪ Y.simplices)
      (union_is_subset_closed X.simplices Y.simplices 
                              X.subset_closed Y.subset_closed)   

-- Intersection of two finite simplicial complexes

lemma inter_is_subset_closed 
    {a : Type*} [decidable_eq a]
    (S : finset (finset a))
    (T : finset (finset a))
    (S_sub_closed : is_subset_closed (S : set (finset a)))
    (T_sub_closed : is_subset_closed (T : set (finset a)))
  : is_subset_closed (↑(S ∩ T) : set (finset a))
:=
begin
  assume s,
  assume s_in_ST : s ∈ ↑(S ∩ T),
  assume t,
  assume t_sub_s : t ⊆ s,
  simp only [is_subset_closed, finset.mem_coe] at *,

  have t_in_S : t ∈ S, from 
  begin
    have s_in_S : s ∈ S, by finish,
    show t ∈ S, by exact S_sub_closed s s_in_S t t_sub_s,
  end,

  have t_in_T : t ∈ T, from
  begin
    have s_in_T : s ∈ T, by finish,
    show t ∈ T, by exact T_sub_closed s s_in_T t t_sub_s,
  end,

  show _, 
       by {simp only[finset.mem_inter],  
           exact and.intro t_in_S t_in_T},
end

def inter_sc 
    {a : Type*} [decidable_eq a]
    (X : fin_simplicial_complex a)
    (Y : fin_simplicial_complex a)
  : fin_simplicial_complex a
:= fin_simplicial_complex.mk
     (X.simplices ∩ Y.simplices)
     (inter_is_subset_closed X.simplices Y.simplices
                             X.subset_closed Y.subset_closed)


/-
# An example: The zigzag complex
-/

-- A simplicial complex that looks like a zigzag chain of triangles;
-- and the computation of its Euler characteristic

def zig
    (n : nat)
  : fin_simplicial_complex (int × int)
:= fingen_simplicial_complex 
     { {(n,0), (n+1,0)}, {(n,0), (n,1)}, {(n,1), (n+1,0)} }    

def zigzag
  : nat → fin_simplicial_complex (int × int)
| 0            := fingen_simplicial_complex { {(0,0)} }  
| (nat.succ n) := union_sc (zigzag n) (zig n)