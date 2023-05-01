/-
Copyright (c) 2022 Clara Löh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.txt.
Author: Clara Löh.
-/

import tactic   -- standard proof tactics

open classical  -- we work in classical logic

/-
# A simple induction proof
-/

-- we define geometric sums (at base 2) ...
def geometric_sum
  : nat → nat
| 0            := 1 
| (nat.succ n) := geometric_sum n + 2^(n+1)

-- ... and show how they can be computed
lemma geometric_sum_eval
    (n : nat)
  : geometric_sum n = 2^(n+1) - 1
:= 
begin
  -- we prove this claim by induction (over the natural number argument n);
  -- here, m is the variable used in the induction step 
  -- and ind_hyp is the induction hypothesis used in the induction step
  induction n with m ind_hyp,

  -- base case: 0
  case nat.zero : {simp[geometric_sum]},

  -- induction step: m -> m+1
  case nat.succ : 
  begin
    calc geometric_sum (m+1) = geometric_sum m + 2^(m+1) : by simp[geometric_sum]
                        ...  = 2^(m+1) - 1 + 2^(m+1)     : by simp[ind_hyp]
                        ...  = 2^(m+1) + 2^(m+1) - 1     : by omega
                        ...  = 2 * 2^(m+1) - 1           : by ring_nf
                        ...  = 2^(m+2) - 1               : by ring,
  end
end      

-- beware of the pitfalls of aritmetic on natural numbers:
#eval 1 - 2 + 1 
#eval 1 + 1 - 2

-- computing some examples:
#eval geometric_sum 0 -- 1
#eval geometric_sum 5 -- 63


/-
# Using the ∑ notation
-/

open finset -- for the range operator
open_locale big_operators -- to enable ∑ notation

-- and another simple sum, 
-- using the sum operator from mathlib (big_operators);
-- range n corresponds to {0,...,n-1}
def one_sum 
  : nat → nat
:= λ n : nat, 
   ∑ (i : nat) in range n, 1

lemma one_sum_eval
    (n : nat)
  : one_sum n = n
:=
begin
  -- we prove this claim by induction (over the natural number argument n)
  induction n with m ind_hyp,

  -- base case: 0 
  case nat.zero : {simp[one_sum]},

  -- induction step: m -> m+1
  case nat.succ : 
  begin
    calc one_sum (m+1) = ∑ (i : nat) in range (m+1), 1   : by simp[one_sum]
                   ... = (∑ (i : nat) in range m, 1) + 1 : by simp
                   ... = m + 1                           : by simp[ind_hyp],
  end, 
  /-
  -- such simple sums can also be resolved directly: 
  unfold one_sum,
  -- found by library_search :
  by exact sum_range_induction (λ (k : ℕ), 1) (λ (n : ℕ), n) rfl (congr_fun rfl) n,
  -/
end

-- handling geometric sums with ∑ operator
def geometric_sum'
  : nat → nat 
:= λ n, 
   ∑ (i : nat) in range n, 2^i  

lemma geometric_sum_eval'
    (n : nat)
  : geometric_sum' n =  2^n - 1
:=
begin   
   -- we prove this claim by induction (over the natural number argument n)
  induction n with m ind_hyp,

  -- base case: 0 
  case nat.zero : {simp[geometric_sum'], ring},

  -- induction step: m -> m+1
  case nat.succ : 
  begin
    calc geometric_sum' (m+1) 
             = ∑ i in range (m+1), 2^i 
             : by simp[geometric_sum']
         ... = ∑ i in range m, 2^i + 2^m 
             : by exact sum_range_succ (λ x, 2^x) m
         ... = geometric_sum' m + 2^m 
             : by simp[geometric_sum']
         ... = 2^m - 1 + 2^m 
             : by simp[ind_hyp]
         ... = 2^m + 2^m - 1
             : by omega    
         ... = 2^(m+1) - 1 
             : by ring_nf,
  end, 
end 