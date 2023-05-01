/-
Copyright (c) 2022 Clara Löh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.txt.
Author: Clara Löh.
-/

import tactic          -- standard proof tactics
import .simplicial_complex      -- basics on simplicial complexes
import .gen_simplicial_complex  -- generation of finite simplicial complexes (including examples)
import .comb_simplicial_complex -- union/intersection of two simplicial complexes (and zigzag)
import algebra.big_operators.basic
import algebra.big_operators.order
open_locale big_operators -- to enable ∑ notation

open classical  -- we work in classical logic

/-
# The Euler characteristic
-/

/- The Euler characteristic of a finite simplicial complex 
   is the alternating sum of the numbers of simplices 
   in each dimension. 
   It is more convenient to define this as 
   the sum of signed parities over the simplices.
-/

/- The parity of an even number is 1;
   the parity of an odd number is -1;
   and negative numbers get the value 0 
   (as we will need to discard the empty set 
   in the count for the Euler characteristic)
-/
def parity 
    (x : int)
  : int
:= if x < 0 then 0
            else if int.mod x 2 = 0 then  1 
                                    else -1

-- some examples
#eval parity (-1) -- 0
#eval parity 0    -- 1
#eval parity 2022 -- 1
#eval parity 2023 -- -1


def euler_char 
    {a : Type*}
    (X : fin_simplicial_complex a)
  : int
:= ∑ (s : finset a) in X.simplices, parity (dim s) 

notation `χ` := euler_char 

/-
# Examples
-/

#eval χ cylinder -- 0
#eval χ moebius -- 0
#eval χ octahedron -- 2
#eval χ torus -- 0
#eval χ klein_bottle -- 0
#eval χ projective_plane -- 1

-- Spheres

#eval χ (sphere 0) -- 2
#eval χ (sphere 1) -- 0
#eval χ (sphere 2) -- 2
#eval χ (sphere 3) -- 0
#eval χ (sphere 4) -- 2

lemma euler_char_sphere_2
    : χ (sphere 2) = 2
:= 
begin
  refl,
end    

/-
# The Euler characteristic of unions
-/

/- We compute the Euler characteristic of a union of two simplicial complexes 
   in terms of the Euler characteristic of the two given simplicial complexes 
   and their intersection.

   The inclusion/exclusion additivity formula for the 
   Euler characteristic of the union of two finite simplicial complexes 
-/
theorem euler_char_union 
    {a : Type*} [decidable_eq a]
    (X : fin_simplicial_complex a)
    (Y : fin_simplicial_complex a)
  : χ (union_sc X Y) 
  = χ X + χ Y - χ (inter_sc X Y) 
:= 
begin
  -- The sum over a union equals 
  -- the sum of the individual sums minus the sum over the intersection
  calc χ (union_sc X Y) 
       = ∑ s in X.simplices ∪ Y.simplices, parity (dim s)
       : by refl
   ... = ∑ s in X.simplices ∪ Y.simplices, parity (dim s)
       + ∑ s in X.simplices ∩ Y.simplices, parity (dim s)
       - ∑ s in X.simplices ∩ Y.simplices, parity (dim s)
       : by ring
   ... = ∑ s in X.simplices, parity (dim s)
       + ∑ s in Y.simplices, parity (dim s)
       - ∑ s in X.simplices ∩ Y.simplices, parity (dim s)
       : by simp[finset.sum_union_inter]        
   ... = χ X + χ Y - χ (inter_sc X Y) 
       : by refl,
end    

/-
# Example: The Euler characteristic of the zigzag
-/

#eval χ (zigzag 0) -- 1
#eval χ (zigzag 1) -- 0
#eval χ (zigzag 2) -- -1
#eval χ (zigzag 3) -- -2

lemma euler_char_zig
    (n : nat)
  : χ (zig n) = 0
:= 
begin
  sorry,
end

lemma euler_char_zigzag_inter
    (n : nat)
  : χ (inter_sc (zigzag n) (zig n)) = 1
:=
begin
  let X := inter_sc (zigzag n) (zig n),

  have inter_simplices : X.simplices = { {(n,0)}, ∅ }, from
  begin

    sorry,

  end,

  show χ X = 1, 
       by {simp only[euler_char, inter_simplices], finish},
end      

lemma euler_char_zigzag
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
         : by simp[ind_hyp,euler_char_zig,euler_char_zigzag_inter]  
     ... = 1 - (m+1) 
         : by ring,
  end
end
