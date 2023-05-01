/-
Copyright (c) 2022 Clara Löh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.txt.
Author: Clara Löh.
-/

import tactic
import maps

open classical


/- 
# Exercise [the identity map] 
-/

-- the identity map
def id_map 
    (X : Type*)
  : X → X
:= λ x, x

lemma id_bijective 
    (X : Type*)
  : is_bijective (id_map X) 
:=
begin
  let f : X → X := id_map X,

  -- injectivity
  have id_inj : is_injective f, from
  begin
    assume x x' : X,
    assume f_xx' : f x = f x',

    show x = x', by 
      calc x = f x  : by refl
         ... = f x' : by simp[f_xx']
         ... = x'   : by refl,
  end,

  -- surjectivity
  have id_surj : is_surjective f, from
  begin
    assume y : X,
    use y,

    show f y = y, by refl,
  end,

  show _, 
       by exact surj_inj_bij f id_surj id_inj,
end  

/- 
# Exercise [compositions of injective maps] 
-/

lemma comp_inj_is_inj 
      {X Y Z: Type*}
      (f : X → Y)
      (g : Y → Z)
      (f_injective : is_injective f)
      (g_injective : is_injective g)
    : is_injective (g ∘ f)
:=
begin
  assume x x' : X,
  assume gf_xx' : (g ∘ f) x = (g ∘ f) x',

  show x = x', by
  begin
    -- first, we use injectivity of g
    have f_xx' : f x = f x', from
    begin
      have g_fxfx' : g (f x) = g (f x'), from
        calc g (f x) = (g ∘ f) x  : by simp
                 ... = (g ∘ f) x' : by simp[gf_xx']
                 ... = g (f x')   : by simp,
   
      show _, by {apply g_injective, apply g_fxfx'},
    end, 

    -- then, we use injectivity of f
    show _, by {apply f_injective, apply f_xx'},
  end
end      

/- 
# Exercise [formalising the first example] 
-/

lemma inj_from_examples 
      {X Y : Type*}
      (f : X → Y)
      (x : X)
      (x' : X)
      (x_neq_x' : x ≠ x')
      (f_xx' : f x = f x')
    : ¬ is_injective f  
:= 
begin
  -- we simplify (and thus move the negation into the expression),
  -- and use the given examples
  simp only[is_injective, not_forall],
  use x, 
  use x',
  show _, by exact ⟨ f_xx', x_neq_x' ⟩,
end

-- redoing the first example
lemma not_inj_f_alt 
    : ¬ is_injective f
:=
begin
  -- we use inj_from_examples
  let x  : A := A.A_1,
  let x' : A := A.A_2,

  have x_neq_x' : x ≠ x', by finish,
  have f_xx' : f x = f x', by refl,

  show _, by exact inj_from_examples f x x' x_neq_x' f_xx',
end

/- 
# Exercise [formalising the second example] 
-/

-- redoing the second example
lemma gg_id 
    : g ∘ g = id_map B
:=
begin
  -- we check this claim case by case
  have g_id : ∀ x : B, (g ∘ g) x = id_map B x, from
  begin
     assume x : B,

     cases x,
       case B.B_1 : {finish},
       case B.B_2 : {finish},
  end,

  show _, by {ext1, tauto},
end    

lemma bij_g_alt
    : is_bijective g
:=
begin
  -- g ∘ g is bijective, because it is the identity 
  -- (which is bijective)
  have gg_bij : is_bijective (g ∘ g), from
  begin
    have gg_id : g ∘ g = id_map B, by exact gg_id,
    show _, by {simp only[gg_id], apply id_bijective B},
  end, 
  -- hence, also g itself is bijective
  show _, by exact square_bij_bij g gg_bij,
end    