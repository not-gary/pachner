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
      (x : real)
      (y : real)
    : x^2 + 2 * x + y^2 - 2 * y + 2024 ≥ 2022
:=
begin
  calc x^2 + 2 * x + y^2 - 2 * y + 2024
         = x^2 + 2 * x + 1 + y^2 - 2 * y + 1 + 2022
         : by ring_nf 
     ... = (x+1)^2 + y^2 - 2 * y + 1 + 2022 
         : by ring_nf
     ... = (x+1)^2 + (y-1)^2 + 2022
         : by ring_nf    
     ... ≥ 2022 
         : by nlinarith, 
end      

/-
# Exercise [two points in a square]
-/

-- Preparation:
-- we first take care of the case of intervals
def lies_in_interval 
    (a : real)
    (a_nonneg : 0 ≤ a)
    (x : real)
  : Prop  
:= x ≥ 0 ∧ x ≤ a

lemma dist_in_interval 
      (a : real)
      (a_nonneg : 0 ≤ a)
      (x : real)
      (y : real)
      (x_in_0a : lies_in_interval a a_nonneg x)
      (y_in_0a : lies_in_interval a a_nonneg y)
    : |x - y| ≤ a      
:= 
begin
  have xy_estimate : x - y ≤ a, by 
  calc x - y ≤ a - y : by linarith[x_in_0a.2]
         ... ≤ a     : by linarith[y_in_0a.1],

  have yx_estimate : -a ≤ x - y, by 
  calc -a ≤ -y     : by linarith[y_in_0a.2]
      ... ≤  x - y : by linarith[x_in_0a.1],

  show _, by exact abs_le.mpr (and.intro yx_estimate xy_estimate),
end

lemma dist_in_interval_2
      (a : real)
      (a_nonneg : 0 ≤ a)
      (x : real)
      (y : real)
      (x_in_0a : lies_in_interval a a_nonneg x)
      (y_in_0a : lies_in_interval a a_nonneg y)
    : (x - y)^2 ≤ a^2      
:= 
begin
  have xy_leq_absa : |x - y| ≤ |a|, by 
  calc  |x - y| ≤ a   : by exact dist_in_interval a a_nonneg x y x_in_0a y_in_0a
            ... ≤ |a| : by exact le_abs_self a,

  calc (x-y)^2 ≤ a^2 : by exact (sq_le_sq xy_leq_absa),
end

-- We are now prepared to prove the distance estimate 
-- for two points in a square:
def lies_in_square 
    (a : real)
    (a_nonneg : 0 ≤ a)
    (x : real × real)
  : Prop
:= lies_in_interval a a_nonneg x.1
 ∧ lies_in_interval a a_nonneg x.2

-- The Euclidean distance on the real plane
noncomputable
def d2 
    (x : real × real)
    (y : real × real)
  : real
:= real.sqrt ( (x.1 - y.1)^2 + (x.2 - y.2)^2 )      

lemma dist_in_square 
      (a : real)
      (a_nonneg : 0 ≤ a)
      (x : real × real)
      (y : real × real)
      (x_in_sq : lies_in_square a a_nonneg x)
      (y_in_sq : lies_in_square a a_nonneg y)
    : d2 x y ≤ real.sqrt 2 * a
:= 
begin
  -- using the result on intervals, 
  -- we bound the argument of the square root:
  have d2_sq_estimate : (x.1-y.1)^2 + (x.2-y.2)^2 ≤ 2 * a^2, by 
  calc (x.1-y.1)^2 + (x.2-y.2)^2 
           ≤ a^2 + a^2 
           : by {linarith[dist_in_interval_2 a a_nonneg x.1 y.1 x_in_sq.1 y_in_sq.1,
                          dist_in_interval_2 a a_nonneg x.2 y.2 x_in_sq.2 y_in_sq.2]} 
       ... = 2 * a^2 
           : by ring,

  -- further prep:
  have a2_nonneg : 0 ≤ 2 * a^2, by 
  calc 0 ≤ a^2 + a^2 : by nlinarith
     ... = 2 * a^2   : by ring,

  -- the actual estimate, using monotonicity of the root
  -- and the previous estimates
  calc d2 x y = real.sqrt ( (x.1-y.1)^2 + (x.2-y.2)^2 ) 
              : by refl
          ... ≤ real.sqrt (2 * a^2) 
              : by {apply (real.sqrt_le_sqrt_iff a2_nonneg).mpr 
                          d2_sq_estimate}
          ... = real.sqrt 2 * real.sqrt (a^2) 
              : by {apply real.sqrt_mul _ (a^2), linarith}
          ... = real.sqrt 2 * a
              : by {congr, exact real.sqrt_sq a_nonneg},
end

