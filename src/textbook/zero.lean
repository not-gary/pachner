/-
Copyright (c) 2022 Clara Löh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.txt.
Author: Clara Löh.
-/

import tactic -- standard proof tactics
import data.real.basic
import analysis.specific_limits -- for the proof via limits
import order.filter.basic       -- dito

open classical -- we work in classical logic

/-
# A criterion for being zero
-/

lemma zero_via_1_over_n 
    (x : real)
    (c : real)
    (x_le_c_over_n : ∀ n : nat, n > 0 → abs x ≤ c / (n : real))
  : x = 0
:= 
begin
  -- we first show that the absolute value of x is zero
  let y : real := abs x,

  have y_is_0 : y = 0, from
  begin
    have y_geq_0 : y ≥ 0,
         by apply abs_nonneg,
  
    have y_leq_0 : y ≤ 0, from
    begin
      -- we proceed by contradiction, assuming that y is not non-positive
      by_contradiction,
      have y_pos : y > 0, 
           by linarith,

      -- using that ℝ is archimedean, we find a large positive natural number
      have ex_m_big : ∃ m : nat, ↑m > c/y, 
           by exact exists_nat_gt (c / y),
      rcases ex_m_big with ⟨ m : nat, m_gt_cy ⟩,
      -- we enforce positivity by adding 1
      let n : nat := m + 1,    
      have n_pos : n > 0, 
           by exact nat.succ_pos m, 
      have n_big : ↑n > c/y, by
           calc ↑n > ↑m  : by simp
               ... > c/y : by exact m_gt_cy,

      -- using n, we show that n * y < n * y (which is the desired contradiction)
      have : ↑n * y > ↑n * y, by 
           calc ↑n * y > (c/y) * y   : by exact (mul_lt_mul_right y_pos).mpr n_big
                   ... ≥ c           : by finish
                   ... ≥ ↑n * y      : by {apply (le_div_iff' _).mp (x_le_c_over_n n n_pos), 
                                           exact nat.cast_pos.mpr n_pos},

      show false, 
           by linarith,
    end,

    show y = 0, 
         by exact le_antisymm y_leq_0 y_geq_0, -- or: finish
  end,

  -- with abs x = y = 0 also x must be zero
  show x = 0,
    by {dsimp only[y] at y_is_0, 
        exact abs_eq_zero.mp y_is_0},
end 

/-
# A much weaker version of the same criterion
-/

lemma zero_via_1_over_n' 
    (x : real)
    (c : real)
    (x_le_c_over_n : ∀ n : nat, abs x ≤ c / (n : real))
  : x = 0
:= 
begin
  -- we first show that the absolute value of x is zero
  let y : real := abs x,

  have y_is_0 : y = 0, from
  begin
    have y_geq_0 : y ≥ 0,
         by apply abs_nonneg,
  
    have y_leq_0 : y ≤ 0, by
         calc y = |x|   : by refl
            ... ≤ c/0   : by exact x_le_c_over_n 0
            ... = 0     : by ring, -- !!    

    show y = 0, 
         by exact le_antisymm y_leq_0 y_geq_0, -- or: finish
  end,

  -- with abs x = y = 0 also x must be zero
  show x = 0,
    by {dsimp only[y] at y_is_0, 
        exact abs_eq_zero.mp y_is_0},
end

/-
# A proof using limits
-/

lemma zero_via_1_over_n_usinglimits 
    (x : real)
    (c : real)
    (x_le_c_over_n : ∀ n : nat, n > 0 → abs x ≤ c / (n : real))
  : x = 0
:= 
begin
  -- we first show that the absolute value of x is zero
  let y : real := abs x,

  have y_is_0 : y = 0, from
  begin
    have y_geq_0 : y ≥ 0,
         by apply abs_nonneg,

    -- we use that lim_n c/n = 0 
    -- and that limits respect inequalities  
    have y_leq_0 : y ≤ 0, from
    begin
       have lim_c_over_n_eq_0 : filter.tendsto (λ n : nat, c/↑n) 
                                       filter.at_top (nhds 0), 
            by exact tendsto_const_div_at_top_nhds_0_nat c, 

       have y_leq_c_over_almost_all_n : 
            ∀ᶠ n : nat in filter.at_top, y ≤ c/n, from
       begin
         have y_leq_c_over_ngeq1: ∃ a : nat, ∀ n : nat, n ≥ a → y ≤ c / n, 
              by {use 1, apply x_le_c_over_n},
         exact filter.eventually_at_top.mpr y_leq_c_over_ngeq1,
       end,

       show _, 
            by exact ge_of_tendsto lim_c_over_n_eq_0 
                                   y_leq_c_over_almost_all_n,
    end,   

    show y = 0, 
         by exact le_antisymm y_leq_0 y_geq_0, -- or: finish
  end,

  -- with abs x = y = 0 also x must be zero
  show x = 0,
    by {dsimp only[y] at y_is_0, 
        exact abs_eq_zero.mp y_is_0},
end