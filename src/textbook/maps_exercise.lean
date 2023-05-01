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
    sorry,
  end,

  -- surjectivity
  have id_surj : is_surjective f, from
  begin
    sorry,
  end,

  show _, 
       by exact surj_inj_bij f id_surj id_inj,
end  

/- 
# Exercise [composition of injective maps] 
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
 
  sorry,

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

  sorry,

end

-- redoing the first example
lemma not_inj_f_alt 
    : ¬ is_injective f
:=
begin

  sorry,

end

/- 
# Exercise [formalising the second example] 
-/

-- redoing the second example
lemma gg_id 
    : g ∘ g = id_map B
:=
begin

  sorry,

end    

lemma bij_g_alt
    : is_bijective g
:=
begin

  sorry,

end    