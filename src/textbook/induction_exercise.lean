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
| 0            := sorry -- add definition
| (nat.succ n) := sorry -- add definition

-- ... and its value in closed form
lemma first_nat_sum_eval
      (n : nat)
    : first_nat_sum n = n * (n+1)
:=
begin
  -- we prove this claim by induction (over the natural number arugment n)
  induction n with m ind_hyp,

  -- base case: 0
  case nat.zero : {sorry},

  -- induction step: m -> m+1 with induction hypothesis ind_hyp
  case nat.succ : 
  begin

    sorry,

  end
end     

-- alternatively: using ∑ (optional)

/-

def first_nat_sum'
  : nat → nat
:= λ n, 2 * ∑ (i : nat) in range (n+1), sorry -- complete definition

lemma first_nat_sum'_eval
      (n : nat)
    : first_nat_sum' n = n * (n+1)
:=
begin
  -- induction proof
  -- sum_range_succ might help
  induction n with m ind_hyp,

  sorry,
end      

-/

/- 
# Exercise [powers in groups] 
-/

lemma powers_of_conjugates
      {G : Type*} [group G]
      (a : G)
      (b : G)
      (n : nat)
    : sorry -- complete statement
:=
begin
  -- we prove this claim by induction (over the natural number arugment n)

  sorry,

end      

lemma commuting_powers 
      {G : Type*} [group G]
      (a : G)
      (b : G)
      -- complete the hypotheses
      (n : nat)
    : sorry -- complete the statemnt
:=
begin

   sorry,

end      


