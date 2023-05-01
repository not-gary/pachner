/-
Copyright (c) 2022 Clara Löh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.txt.
Author: Clara Löh.
-/

import tactic -- standard proof tactics
import data.real.basic
import data.real.sqrt

open classical -- we work in classical logic

/-
# Exercise [an estimate]
-/

lemma an_estimate 
      -- hypotheses
    : sorry -- claim
:=
begin
  -- by calc 
  -- ring_nf, linarith, nlinarith might help
  sorry
end      

/-
# Exercise [two points in a square]
-/

-- Preparation:
-- we first take care of the case of intervals
def lies_in_interval 
    (a : real)
    -- hypotheses 
  : Prop  
:= sorry -- defining predicate for a given point to lie in the interval [0,a]

-- Distance estimate for two points in the interval [0,a]
lemma dist_in_interval 
      -- hypotheses 
    : sorry -- claim
:= 
begin
  -- abs_le.mpr might help
  sorry
end

-- Possibly a helpful intermediate step: 
-- squared version of dist_in_interval
lemma dist_in_interval_2
      -- hypotheses 
    : sorry -- claim      
:= 
begin
  sorry
end

-- We are now prepared to prove the distance estimate 
-- for two points in a square:
def lies_in_square 
    (a : real)
    -- hypotheses
  : Prop
:= sorry -- defining predicate for a given point to lie in the interval [0,a];
         -- lies_in_interval can be used!

-- The Euclidean distance on the real plane
noncomputable
def d2 
    (x : real × real)
    (y : real × real)
  : real
:= sorry 

-- The actual distance estimate
lemma dist_in_square 
      (a : real)
      (a_nonneg : 0 ≤ a)
      (x : real × real)
      (y : real × real)
      -- complete the hypotheses!
    : d2 x y ≤ real.sqrt 2 * a
:= 
begin
  -- using the result on intervals, 
  -- we bound the argument of the square root:
  have d2_sq_estimate : (x.1-y.1)^2 + (x.2-y.2)^2 ≤ 2 * a^2, 
       by {sorry},

  -- the actual estimate, using monotonicity of the root
  -- and the previous estimates
  calc d2 x y ≤ real.sqrt 2 * a : 
       by {sorry},
end

