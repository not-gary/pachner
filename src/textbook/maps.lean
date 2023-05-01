/-
Copyright (c) 2022 Clara Löh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.txt.
Author: Clara Löh.
-/

import tactic   -- standard proof tactics

open classical  -- we work in classical logic

/- 
# Injective, surjective, bijective maps 
-/

def is_injective 
    {X Y : Type*}
    (f : X → Y)
 := ∀ x : X, ∀ x' : X, 
    f x = f x' → x = x'

def is_surjective 
    {X Y : Type*}
    (f : X → Y)
 := ∀ y : Y, 
    ∃ x : X, f x = y  

def is_bijective
    {X Y : Type*}
    (f : X → Y)
 := is_injective f ∧ is_surjective f    

/- 
# Simple inheritance properties of injective, surjective, bijective maps 
-/

lemma bij_inj
    {X Y : Type*}
    (f : X → Y)
    (f_bijective: is_bijective f)
  : is_injective f 
:= 
-- we extract the correct part of the and-statement
-- in the definition of is_bijective
   and.elim_left f_bijective
-- alternatively: f_bijective.1

lemma bij_surj
    {X Y : Type*}
    (f : X → Y)
    (f_bijective: is_bijective f)
  : is_surjective f  
:= 
-- we extract the correct part of the and-statement
-- in the definition of is_bijective
   and.elim_right f_bijective
-- alternatively: f_bijective.2

lemma surj_inj_bij
    {X Y : Type*}
    (f : X → Y)
    (f_surjective: is_surjective f)
    (f_injective:  is_injective f)
  : is_bijective f  
:=
-- we construct the and-statement 
-- in the definition of is_bijective
-- in the correct order 
   and.intro f_injective f_surjective

/- If a composition is injective, 
   then the first map is injective -/
lemma inj_comp_injfirst 
    {X Y Z : Type*}
    (f : X → Y)
    (g : Y → Z)
    (gf_injective : is_injective (g ∘ f))
  : is_injective f
:=  
begin
  -- we prove the all-statement (double ∀)
  -- in the definition of is_injective
  assume x  : X, 
  assume x' : X, 
  -- we assume the hypothesis of the implication
  -- in the definition of is_injective
  assume f_xx' : f x = f x',
  
  -- and then show that this implies x = x',
  -- using injectivity of g ∘ f
  have gf_xx' : (g ∘ f) x = (g ∘ f) x', from 
    calc (g ∘ f) x = g (f x)    : by simp
               ... = g (f x')   : by simp[f_xx']
               ... = (g ∘ f) x' : by simp,

  show x = x', 
       by {apply gf_injective, apply gf_xx'},
end
/- 
-- alternatively: 
begin
  intros _ _ h,
  apply gf_injective,
  simp[h],
end
-/

/- If a composition is surjective,
   then the last map is surjective -/
lemma surj_comp_surjsecond
    {X Y Z : Type*}
    (f : X → Y)
    (g : Y → Z)
    (gf_surjective : is_surjective (g ∘ f))
  : is_surjective g  
:= 
begin
  -- we prove the all-statement 
  -- in the definition of is_surjective
  assume z : Z,

  -- we use surjectivity of g ∘ f on z
  -- we extract such a preimage
  rcases gf_surjective z with ⟨ x : X, gf_x_z : (g ∘ f) x = z⟩,
  -- and use it to define a g-preimage of z
  let y : Y := f x,

  -- we construct the existential statement 
  -- in the definition of is_surjective,
  -- by using the example y
  use y,
  -- it remains to show that y indeed is a g-preimage of z
  show g y = z, from
    calc g y = g (f x)   : by simp
         ... = (g ∘ f) x : by simp
         ... = z         : by exact gf_x_z,
end  

/- If the square of a self-map is bijective, 
   then the self-map is bijective -/
lemma square_bij_bij
    {X : Type*}
    (f : X → X)
    (ff_bijective : is_bijective (f ∘ f))
  : is_bijective f
:=
begin
  -- the map f is injective
  have f_injective : is_injective f, from
  begin
    -- the composition f ∘ f is bijective, whence injective
    have ff_injective : is_injective (f ∘ f), 
         by exact bij_inj (f ∘ f) ff_bijective,
    -- thus, the first map (namely f) is injective    
    show _,
         by exact inj_comp_injfirst f f ff_injective,
  end,

  -- the map f is surjective
  have f_surjective: is_surjective f, from
  begin
    -- the composition f ∘ f is bijective, whence surjective
    have ff_surjective : is_surjective (f ∘ f),
         by exact bij_surj (f ∘ f) ff_bijective,
    -- thus, the second map (namely f) is surjective
    show _,
         by exact surj_comp_surjsecond f f ff_surjective,     
  end,

  -- thus, f is bijective
  show is_bijective f, 
       by exact and.intro f_injective f_surjective,
       -- alternatively: by {exact surj_inj_bij f f_surjective f_injective}
end      

/- 
# Examples 
-/

/- The map {1,2,3} -> {1,2,3}, 
   1 -> 1, 2 -> 1, 3 -> 2
   is neither injective nor surjective -/
inductive A : Type
| A_1
| A_2
| A_3

def f 
  : A → A
| A.A_1 := A.A_1
| A.A_2 := A.A_1
| A.A_3 := A.A_2

lemma not_inj_f 
    : ¬ is_injective f
:=
begin
  -- idea: f A_1 = f A_2, even though A_1 ≠ A_2
  let x  : A := A.A_1,
  let x' : A := A.A_2,

  -- x and x' are witnesses for non-injectivity:
  have f_xx'_x_neq_x' : f x = f x' ∧ x ≠ x', from
  begin
    have f_xx' : f x  = f x', 
         by simp[f],
    have x_neq_x' :  x ≠ x', 
         by finish,

    show _, by exact and.intro f_xx' x_neq_x',
  end,

  -- we simplify (and thus move the negation into the expression), 
  -- use x and x' as examples for the existential quantifier,  
  -- and then conclude via f_xx'_x_neg_x'
  show ¬ is_injective f, from
  begin
    simp only [is_injective, not_forall], 
    use x,
    use x',
    show _, by exact f_xx'_x_neq_x',
  end
end

lemma not_surj_f
    : ¬ is_surjective f
:=
begin
  -- we first move the negation through the all-quantifier
  simp only[is_surjective, not_forall],
  show ∃ y : A, ¬(∃ x : A, f x = y), by
  begin
    -- we show that A_3 does not lie in the image
    use A.A_3,
    have A3_not_in_im : ∀ x : A, ¬ f x = A.A_3, from
    begin
      assume x : A,
      -- we now just consider all three cases
      cases x,
        case A.A_1 : {simp[f]}, -- alternatively: {finish}
        case A.A_2 : {simp[f]},
        case A.A_3 : {simp[f]},
    end,
    show _, 
         by {simp only[not_exists], exact A3_not_in_im}
  end 
end

/- The map {1,2} -> {1,2},
   1 -> 2, 2 -> 1
   is bijective -/
inductive B 
| B_1
| B_2

def g : B → B
| B.B_1 := B.B_2
| B.B_2 := B.B_1

lemma bij_g 
    : is_bijective g
:= 
begin
  -- we check injectivity and surjectivity
  -- by going through all the cases  
  have inj_g : is_injective g, from 
  begin
    assume x  : B,
    assume x' : B,
    assume g_xx' : g x = g x',
    cases x,
      case B.B_1 : begin cases x', finish, finish end,
      case B.B_2 : begin cases x', finish, finish end,
  end,

  have surj_g :  is_surjective g, from
  begin
    assume y : B,
    cases y,
      case B.B_1 : begin use B.B_2, finish end,
      case B.B_2 : begin use B.B_1, finish end,
  end,

  show _,
       by exact surj_inj_bij g surj_g inj_g
end

/- And (parts of) the same thing, 
   but with (types from) sets instead of sum types -/
def set_123 : set ℕ 
:= {1,2,3}

lemma one_in_123 : 1 ∈ set_123 
:= by {fconstructor,linarith}

lemma two_in_123 : 2 ∈ set_123
:= by {apply or.inr, finish}

lemma three_in_123 : 3 ∈ set_123
:= by {apply or.inr, finish}

def map_const1
  : set_123 → set_123 
:= λ ⟨x, _⟩, ⟨1, one_in_123⟩ 

def f'
  : set_123 → set_123
:= λ ⟨x, x_in_123⟩, 
   if x = 3 then ⟨ 2, two_in_123 ⟩
            else ⟨ 1, one_in_123 ⟩

lemma not_inj_f' 
    : ¬ is_injective f'
:=
begin
  -- idea: f' 1 = f' 2, even though 1 ≠ 2
  let x1 : ↥set_123 := ⟨ 1, one_in_123 ⟩,
  let x2 : ↥set_123 := ⟨ 2, two_in_123 ⟩,

  -- we move the negation through the first all-quantifier
  refine not_forall.mpr _,
  -- we use A_1 as first input
  use x1,
  -- we move the negation through the second all-quantifier
  refine not_forall.mpr _,
  -- we use A_2 as second input
  use x2,
  -- we use the definition of f'
  show _, by finish
end

