/-
Copyright (c) 2022 Clara Löh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.txt.
Author: Clara Löh.
-/

import tactic -- standard proof tactics
import algebra.group.basic -- basic group theory
open finset   -- for range operator
open_locale big_operators -- to enable ∑ notation


open classical -- we work in classical logic


/-
# Exercise [the sum of the first natural numbers] 
-/

-- the sum of the natural numbers 0,...,n (times 2)
def first_nat_sum
  : nat → nat
| 0            := 0
| (nat.succ n) := first_nat_sum n + 2 * (n + 1)

-- ... and its value in closed form
lemma first_nat_sum_eval
      (n : nat)
    : first_nat_sum n = n * (n+1)
:=
begin
  -- we prove this claim by induction (over the natural number arugment n)
  induction n with m ind_hyp,

  -- base case: 0
  case nat.zero : {simp[first_nat_sum]},

  -- induction step: m -> m+1 with induction hypothesis ind_hyp
  case nat.succ : 
  begin
    calc first_nat_sum (m+1) = first_nat_sum m + 2 * (m+1) 
                             : by simp[first_nat_sum]
                         ... = m * (m+1) + 2 * (m+1)
                             : by simp[ind_hyp]
                         ... = (m+2) * (m+1)
                             : by ring        
                         ... = (m+1) * (m+2) 
                             : by ring,
  end
end     

-- alternatively: using ∑

def first_nat_sum'
  : nat → nat
:= λ n, 2 * ∑ (i : nat) in range (n+1), i   

lemma first_nat_sum'_eval
      (n : nat)
    : first_nat_sum' n = n * (n+1)
:=
begin
  -- we prove this claim by induction (over the natural number arugment n)
  induction n with m ind_hyp,

  -- base case: 0
  case nat.zero : {simp[first_nat_sum']},

  -- induction step: m -> m+1 with induction hypothesis ind_hyp
  case nat.succ : 
  begin
    calc first_nat_sum' (m+1) = 2 * ∑ (i : nat) in range (m+2), i
                              : by unfold first_nat_sum'
                          ... = 2 * ((∑ (i : nat) in range (m+1), i) + m + 1)
                              : by {congr, simp only[sum_range_succ], ring} 
                          ... = 2 * ∑ (i : nat) in  range (m+1), i + 2 * (m+1)
                              : by ring       
                          ... = m * (m+1) + 2 * (m+1)
                              : by {unfold first_nat_sum' at ind_hyp, simp[ind_hyp]}
                          ... = (m+2) * (m+1)
                              : by ring        
                          ... = (m+1) * (m+2)
                              : by ring,
  end,                            
end      

/- 
# Exercise [powers in groups] 
-/

lemma powers_of_conjugates
      {G : Type*} [group G]
      (a : G)
      (b : G)
      (n : nat)
    : (a * b * a⁻¹)^n = a * b^n * a⁻¹
:=
begin
  -- we prove this claim by induction (over the natural number arugment n)
  induction n with m ind_hyp,

  -- base case: 0
  case nat.zero : {group},

  case nat.succ : 
  begin
    calc (a * b * a⁻¹)^(m+1) = (a * b * a⁻¹)^m * (a * b * a⁻¹) : by simp[pow_succ' _ m]
                         ... = (a * b^m * a⁻¹) * (a * b * a⁻¹) : by simp[ind_hyp]
                         ... = a * b^m * b * a⁻¹               : by group 
                         ... = a * b^(m+1) * a⁻¹               : by group,
  end,
end      

lemma commuting_powers 
      {G : Type*} [group G]
      (a : G)
      (b : G)
      (ab_comm : a * b = b * a)
      (n : nat)
    : b^n * a = a * b^n
:=
begin
  -- we prove this claim by induction (over the natural number arugment n)
  induction n with m ind_hyp,

  -- base case: 0
  case nat.zero : {group},

  -- induction step: m -> m+1 with induction hypothesis ind_hyp
  case nat.succ :
  begin
    calc b^(m+1) * a = b^m * b * a : by group 
                 ... = b^m * (b*a) : by group
                 ... = b^m * (a*b) : by simp[ab_comm]
                 ... = b^m * a * b : by group
                 ... = a * b^m * b : by simp[ind_hyp]
                 ... = a * b^(m+1) : by group,
  end
end