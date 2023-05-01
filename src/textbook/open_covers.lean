/-
Copyright (c) 2022 Clara Löh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.txt.
Author: Clara Löh.
-/

import tactic -- standard proof tactics
import algebra.category.Group.basic -- the category of groups
import group_theory.subgroup.basic  -- subgroups
import category_theory.category.basic -- basic category theory
import category_theory.functor -- functors
import category_theory.limits.shapes.zero -- categories with zero objects/morphisms
import data.nat.enat -- extended naturals

open classical -- we work in classical logic
open category_theory

noncomputable theory

/- The backbone of the lower bounds strategy
   for generalised LS-cat invariants via classifying spaces 
   of families of subgroups
-/

universes u v -- u: the standard universe for everything

/-
# Classifying spaces
-/  

-- For a given group G: 
-- The homotopy category of G-CW-complexes:
-- * objects: G-CW-complexes
-- * morphisms: G-homotopy classes of G-maps
constant CWh (G : Type u) [group G] : Type u
constant dim (G : Type u) [group G] : CWh G → enat

@[instance] 
axiom CWh_cat (G : Type u) [group G] : (category.{u u} (CWh G)) 

-- Families of subgroups
-- (conjugation closed, finite intersection closed, containing the trivial subgroup)
constant family (G: Type u) [group G] : Type u  

-- the trivial family, consisting only of the trivial subgroup   
constant one (G : Type u) [group G] : family G

constant has_isotropy_in 
    {G : Type u} [group G] 
    (F : family G) 
    (X : CWh G) 
  : Prop  

axiom isotropy_one_implies_all 
    {G : Type u} [group G]
    (F : family G)
    (X : CWh G)
    (X_is_free : has_isotropy_in (one G) X)
  : has_isotropy_in F X  

-- classifying spaces of a family of subgroups
structure classifying_space
    (G : Type u) [group G]
    (F : family G)
:= mk :: (space : CWh G)
         (isotropy : has_isotropy_in F space)
         (universal_property : ∀ X : CWh G, 
                               has_isotropy_in F X 
                             → unique (X ⟶ space)) -- terminal in CWh G with isotropy in F

-- existence/construction of classifying spaces
constant E 
    (G : Type u) [group G] 
    (F : family G)
  : classifying_space G F

-- classifying maps:
-- the unique morphisms provided by the universal property
-- of classifying spaces
def cm
    (G : Type u) [group G]
    (F : family G)
    (X : CWh G)
    (X_has_isotropy_in_F : has_isotropy_in F X)
  : X ⟶ (E G F).space
:= ((E G F).universal_property X X_has_isotropy_in_F).to_inhabited.default

-- for notational simplicity: the case of the trivial family
def E1
    (G : Type u) [group G]
  : classifying_space G (one G)
:= E G (one G)    

lemma E1_isotropy
    (G : Type u) [group G]
    (F : family G)
  : has_isotropy_in F (E1 G).space  
:= 
begin
  exact isotropy_one_implies_all F
          (E G (one G)).space
          (E G (one G)).isotropy
end

-- the classifying map EG ⟶ E_F G
def cm1_E 
    (G : Type u) [group G]
    (F : family G)
  : (E G (one G)).space ⟶ (E G F).space
:= cm G F (E G (one G)).space   
          (E1_isotropy G F)

/-
# Restricted covers and their equivariant nerves
-/  

-- The category of CW-complexes:
-- * objects: connected CW-complexes (with an implicit basepoint)
-- * morphisms: continuous maps
constant CW1 : Type u
  
@[instance] 
axiom CW1_cat : category_theory.category.{u u} CW1

-- The fundamental group 
-- (with respect to the implicit basepoint)
constant pi_1 (X : CW1.{u}) : Type u

@[instance] 
axiom fundamental_group (X : CW1.{u}) : group (pi_1 X)

-- The universal covering
constant universal_covering (X : CW1) : CWh (pi_1 X)

axiom universal_covering_is_free (X : CW1)
  : has_isotropy_in (one (pi_1 X)) (universal_covering X)

lemma universal_covering_isotropy
    (X : CW1)
    (F : family (pi_1 X))
  : has_isotropy_in F (universal_covering X)
:= 
begin
  exact isotropy_one_implies_all 
          F 
          (universal_covering X) 
          (universal_covering_is_free X),
end

-- The classifying map of the universal covering
def cm1_universal_covering
    (X : CW1)
  : universal_covering X ⟶ (E1 (pi_1 X)).space
:=
cm (pi_1 X) (one (pi_1 X)) 
   (universal_covering X)
   (universal_covering_is_free X)

-- Open covers
-- (a set of path-connected open subsets, 
-- whose union covers X, and 
-- such that the images of the fundamental groups 
-- are "conjugate to" elements of F)
constant open_cover 
    (X : CW1)
    (F : family (pi_1 X))
  : Type u

constant multiplicity
    {X : CW1}
    {F : family (pi_1 X)}
    (U : open_cover X F)
  : enat 

-- The nerve of the lifted cover of U
constant nerve 
    {X : CW1}
    {F : family (pi_1 X)}
    (U : open_cover X F)
  : CWh (pi_1 X)  

constant nerve_map
    {X : CW1}
    {F : family (pi_1 X)}
    (U : open_cover X F)
  : (universal_covering X) ⟶ (nerve U)  

axiom nerve_dim
    {X : CW1}
    {F : family (pi_1 X)}
    (U : open_cover X F)
  : dim (pi_1 X) (nerve U) + 1 = multiplicity U

-- The essential connection between covers
-- and their equivariant nerves:
axiom nerve_isotropy
    {X : CW1}
    {F : family (pi_1 X)}
    (U : open_cover X F)
  : has_isotropy_in F (nerve U) 

/-
# The lower bound strategy
-/  

-- The key commutative diagram (with G = pi_1 X):
--   cm nerve EFG ∘ nerve_map
-- = cm EG EFG ∘ cm ucov EG
lemma commutative_diagram
    (X : CW1)
    (F : family (pi_1 X))
    (U : open_cover X F)
  : (nerve_map U)             -- nerve map: ucov X ⟶ nerve
    ≫ 
    (cm (pi_1 X) F (nerve U)  -- nerve ⟶ E_F G
        (nerve_isotropy U))
  = (cm1_universal_covering X)    -- ucov X ⟶ EG
    ≫
    (cm1_E (pi_1 X) F)            -- EG ⟶ E_F G     
:=
begin
  -- notation for the relevant classifying space
  let EFG := E (pi_1 X) F,
  -- the universal property of E_F G with domain ucov X:
  -- there exists a unique morphism ucov X ⟶ E_F G 
  have unique_X_EFG : unique (universal_covering X ⟶ EFG.space),
       by exact EFG.universal_property (universal_covering X) 
                                       (universal_covering_isotropy X F),

  -- the two maps are morphisms ucov X ⟶ E_F G
  let f1 : universal_covering X ⟶ EFG.space
         := (nerve_map U)       
            ≫ 
            (cm (pi_1 X) F (nerve U)  
                (nerve_isotropy U)),
  let f2 : universal_covering X ⟶ EFG.space
         := (cm1_universal_covering X)    
            ≫
            (cm1_E (pi_1 X) F),            

  -- therefore, the universal property of E_F G proves the claim
  calc f1 = unique_X_EFG.to_inhabited.default 
          : by exact @unique.eq_default _ unique_X_EFG f1
      ... = f2 
          : by exact @unique.default_eq _ unique_X_EFG f2,
end

-- We now apply functors to this commutative diagram

-- The target category for our functors
-- is a category with a zero object
constant C : Type u

@[instance]
constant C_is_cat : category.{u u} C

@[instance]
constant C_has_zero : category_theory.limits.has_zero_object.{u u} C

-- allows us to use 0 for the zero object C_has_zero.zero
instance : has_zero C 
:= category_theory.limits.has_zero_object.has_zero
-- and to use 0 for the zero morphisms
instance : category_theory.limits.has_zero_morphisms C 
:= category_theory.limits.has_zero_object.zero_morphisms_of_zero_object 

-- relevant properties for our functors
def is_aspherical_for
    (X : CW1)
    (H : CWh (pi_1 X) ⥤ C)
:= is_iso (H.map (cm1_universal_covering X))

def is_admissible_family_for 
    {G : Type u} [group G]
    (F : family G)
    (H : CWh G ⥤ C)
:= is_iso (H.map (cm1_E G F))    

def dim_vanishing 
    {G : Type u} [group G]
    (H : CWh G ⥤ C)
    (n : nat)
:= ∀ Y : CWh G, dim G Y + 1 ≤ n 
                → (H.obj Y ≅ 0)

structure admissible_functor 
    (X : CW1)
    (F : family (pi_1 X))
:= mk :: (functor  : (CWh (pi_1 X)) ⥤ C )
         (ucov_iso : is_aspherical_for X functor)      -- iso for ucov X → EG
         (family_admissible : is_admissible_family_for 
                                 F functor)            -- iso for EG → EFG


-- Preparation: 
-- Using the commutative diagram, we show that 
-- the identity under admissible functors factors over H(nerve map)
lemma admissible_functors_factor_over_nerve 
    (X : CW1)
    (F : family (pi_1 X))
    (U : open_cover X F)
    (H : admissible_functor X F)
  : ∃ g : H.functor.obj (nerve U) ⟶ H.functor.obj (universal_covering X),
       (H.functor.map (nerve_map U)) ≫ g 
     = 𝟙 (H.functor.obj (universal_covering X))
:= 
begin
  -- simplified notation 
  let G := pi_1 X,
  let HX : C := H.functor.obj (universal_covering X),
  let EG  := E1 (pi_1 X),
  let EFG := E (pi_1 X) F,
  let HN : C := H.functor.obj (nerve U), 

  -- the commutative diagram:
  -- both ways of getting from ucov X to E_FG coincide
  let f11 : universal_covering X ⟶ (nerve U)
          := nerve_map U,
  let f12 : nerve U ⟶ EFG.space
          := cm (pi_1 X) F (nerve U) (nerve_isotropy U),
  
  let f21 : universal_covering X ⟶ EG.space
          := cm1_universal_covering X,
  let f22 : EG.space ⟶ EFG.space
          := cm1_E G F,

  have comm_diag : f11 ≫ f12 = f21 ≫ f22, 
       by exact commutative_diagram X F U,

  -- using the commutative diagram, 
  -- we show that id HX factors over HN;
  -- More precisely:
    -- id_HX =  H f11 
    --       ≫ H f12 ≫ inv (H (f21 ≫ f22))
  -- the first part of the factorisation:  
  let f : HX ⟶ HN
        := H.functor.map f11,

  -- the second part of the factorisation: 
  -- preparation: 
  -- admissibility of H with respect to F shows that H (f21 ≫ f22) is an iso
  have H_f2_is_iso : is_iso (H.functor.map (f21 ≫ f22)), from
  begin
    -- H (f21 ≫ f22) = H f21 ≫ H f22 is an iso, 
    -- because H f21 and H f22 are isos
    have H_f2_comp : H.functor.map (f21 ≫ f22) = (H.functor.map f21) ≫ (H.functor.map f22), 
         by simp,

    have : is_iso (H.functor.map f21 ≫ H.functor.map f22), 
         by exact @is_iso.comp_is_iso C C_is_cat _ _ _ 
                      (H.functor.map f21) (H.functor.map f22)
                      H.ucov_iso H.family_admissible,

    show _, by {simp only[H_f2_comp], assumption},
  end,

  let i_H_f2 := @inv C C_is_cat _ _ (H.functor.map (f21 ≫ f22)) H_f2_is_iso,
  let g : HN ⟶ HX 
        := H.functor.map f12 ≫ i_H_f2, 

  -- the computation that id HX indeed factors over HN: 
  have id_HX_factors_over_HN : f ≫ g  = 𝟙 HX, from
  calc f ≫ g = H.functor.map f11  
             ≫ H.functor.map f12 ≫ i_H_f2 
              : by simp -- by definition 
          ... = H.functor.map (f11 ≫ f12) 
              ≫ i_H_f2
              : by simp -- by functoriality
          ... = H.functor.map (f21 ≫ f22)
              ≫ i_H_f2 
              : by simp[comm_diag] -- finally, we use the commutative diagram   
          ... = 𝟙 HX 
              : by exact @is_iso.hom_inv_id C C_is_cat _ _ 
                         (H.functor.map (f21 ≫ f22)) H_f2_is_iso,

  -- thus, f and g witness the claimed factorisation
  show _, 
       by {use g, exact id_HX_factors_over_HN}, 
end   

-- Preparation:
-- If the multiplicity is small, then H (nerve) ≅ 0
-- in presence of the dim-vanishing property. 
-- We use the expression of the dimension of the nerve 
-- via the multiplicity of U
lemma dim_vanishing_functors_vanish_on_small_nerves 
    (n : nat)
    (X : CW1)
    (F : family (pi_1 X))
    (U : open_cover X F)
    (mult_U_leq_n : multiplicity U ≤ n)
    (H : CWh (pi_1 X) ⥤ C)
    (H_dim_vanishing : dim_vanishing H n)
  : H.obj (nerve U) ≅ 0
:= 
begin 
  -- simplified notation:
  let G := pi_1 X,
  let HN : C := H.obj (nerve U), 

  -- the dimension of the nerve is smaller than n
  have dim_N_leq_n : dim G (nerve U) + 1 ≤ n, by
  calc dim G (nerve U) + 1 = multiplicity U  
                           : by exact nerve_dim U
                       ... ≤ n 
                           : by exact mult_U_leq_n,
  -- thus, we apply the dim-vanishing property                             
  exact H_dim_vanishing (nerve U) dim_N_leq_n,
end

-- If the identity of an object factors over zero, 
-- the object is zero
lemma id_factors_over_zero_iso_zero
    (X : C)
    (f : X ⟶ 0)
    (g : 0 ⟶ X)
    (id_factors : 𝟙 X = f ≫ g)
  : X ≅ 0
:=
begin
  -- we use f and g as isomorphisms
  exact { hom := f, 
          inv := g, 
          hom_inv_id' := _, 
          inv_hom_id' := _},
  -- f ≫ g = id by assumption:        
  show f ≫ g = 𝟙 X, by exact id_factors.symm,
  -- g ≫ f = id by the universal property of the zero object
  show g ≫ f = 𝟙 0, by ext1,
end    



/- Theorem:
   Dim-vanishing admissible functors lead to lower bounds 
   for the multiplicity of F-covers
-/
theorem restricted_cover_lower_bound 
    (n : nat)
    (X : CW1)
    (F : family (pi_1 X))
    (U : open_cover X F)
    (mult_U_leq_n : multiplicity U ≤ n)
    (H : admissible_functor X F)
    (H_dim_vanishing : dim_vanishing H.functor n)
  : H.functor.obj (universal_covering X) ≅ 0
:= 
begin 
  -- we first show that H(nerve) ≅ 0, 
  -- using the dim-vanishing property
  let HN : C := H.functor.obj (nerve U), 

  have HN_is_zero : HN ≅ 0, 
       by exact dim_vanishing_functors_vanish_on_small_nerves 
                  n X F U mult_U_leq_n H.functor H_dim_vanishing,

  -- the resulting isomorphisms to and from the zero object
  let nz : HN ⟶ 0 := HN_is_zero.hom,                 
  let zn : 0 ⟶ HN := HN_is_zero.inv,

  -- second, the preparation on classifying spaces shows that   
  -- the identity on H(ucov X) factors over H(nerve)
  let HX := H.functor.obj (universal_covering X),
  let f  := H.functor.map (nerve_map U),

  -- we choose such a factorisation
  choose g fg_idHX using admissible_functors_factor_over_nerve X F U H,

  let fz : HX ⟶ 0 := f ≫ nz,
  let zg : 0 ⟶ HX := zn ≫ g,

  -- thus, the identity on H(ucov X) factors over 0
  have id_HX_factors_over_0 : fz ≫ zg = 𝟙 HX, from 
  calc fz ≫ zg = f ≫ nz ≫ zn ≫ g 
                : by simp
            ... = f ≫ g 
                : by simp -- nz ≫ zn cancels
            ... = 𝟙 HX 
                : by exact fg_idHX,

  -- hence, H(ucov X) must be zero
  show HX ≅ 0, 
       by exact id_factors_over_zero_iso_zero HX fz zg 
                id_HX_factors_over_0.symm,
end

-- We also formulate the result in a contrapositive form, 
-- which makes the "lower bound" aspect more explicit:

-- Preparation: basic handling of "not isomorphic to"
def not_isomorphic
    {C : Type v}
    [category.{u v} C]
    (X : C)
    (Y : C)
:= ¬ ∃ f : X ⟶ Y, is_iso f     

lemma iso_implies_not_not_isomorphic 
    {C : Type v}
    [category.{u v} C]
    (X : C)
    (Y : C)
    (X_iso_Y : X ≅ Y)
   : ¬ not_isomorphic X Y
:=
begin
  -- X ≅ Y shows that there exists an isomorphism X ⟶ Y
  have ex_iso : ∃ f : X ⟶ Y, is_iso f, from
  begin
    let f := X_iso_Y.hom,
    have f_is_iso : is_iso f,
         by exact category_theory.is_iso.of_iso X_iso_Y,
    use f,
    show _, by exact f_is_iso,    
  end,

  -- thus, there does not not exist an iso
  unfold not_isomorphic,
  exact not_not.mpr ex_iso,
end      

-- If the value under an admissible functor is non-zero, 
-- then this results in a lower bound on the multiplicity
theorem restricted_cover_lower_bound_cp 
    (n : nat)
    (X : CW1)
    (F : family (pi_1 X))
    (U : open_cover X F)
    (H : admissible_functor X F)
    (H_dim_vanishing : dim_vanishing H.functor n)
    (H_non_zero : not_isomorphic (H.functor.obj (universal_covering X)) 
                                 0)
  : multiplicity U > n        
:=
begin
  -- we apply the theorem and convert the contraposition
  by_contradiction negation,
  have mult_leq_n : multiplicity U ≤ n, 
       by exact not_lt.mp negation,
  have HX_zero : H.functor.obj (universal_covering X) ≅ 0,
       by exact restricted_cover_lower_bound n X F U mult_leq_n H H_dim_vanishing,
  have not_HX_non_zero : ¬ not_isomorphic (H.functor.obj (universal_covering X)) 
                                          0, 
       by exact iso_implies_not_not_isomorphic _ _ HX_zero,

  -- not_HX_non_zero contradicts HX_non_zero; thus we are done
  finish,
end


/-
# The lower bound strategy, refined version with two functors
-/  

structure admissible_functor_2 
    (X : CW1)
    (F : family (pi_1 X))
extends admissible_functor X F 
:= mk :: (functor2  : (CWh (pi_1 X)) ⥤ C )
         (nat_trafo : functor2 ⟶ functor)

theorem restricted_cover_lower_bound_2 
    (n : nat)
    (X : CW1)
    (F : family (pi_1 X))
    (U : open_cover X F)
    (mult_U_leq_n : multiplicity U ≤ n)
    (H : admissible_functor_2 X F)
    (K_dim_vanishing : dim_vanishing H.functor2 n)
  : H.nat_trafo.app (universal_covering X) = 0
:=
begin
  -- simplified notation:
  let G  := pi_1 X,
  -- the first functor
  let HX := H.functor.obj (universal_covering X),
  let H' : admissible_functor X F 
         := admissible_functor.mk H.functor H.ucov_iso H.family_admissible,
  -- the second functor
  let K  : CWh G ⥤ C 
         := H.functor2,
  let KN := K.obj (nerve U), 
  let KX := K.obj (universal_covering X), 
  -- the natural transformation
  let T  := H.nat_trafo,

  -- we combine 
  -- * the factorisation of id on H(ucov X) over H(nerve)
  -- * with the natural transformation
  -- * and the vanishing of K(nerve)

  -- we first show that K(nerve) ≅ 0, 
  -- using the dim-vanishing property
  have KN_is_zero : KN ≅ 0, 
       by exact dim_vanishing_functors_vanish_on_small_nerves 
                  n X F U mult_U_leq_n K K_dim_vanishing,

  -- the resulting isomorphisms to and from the zero object
  let nz : KN ⟶ 0 := KN_is_zero.hom,                 
  let zn : 0 ⟶ KN := KN_is_zero.inv,

  -- second, the preparation on classifying spaces shows that   
  -- H(ucov X) factors over H(nerve map)
  let f := H.functor.map (nerve_map U),
  choose g fg_idHX using admissible_functors_factor_over_nerve X F U H',

  -- we now combine both aspects
  -- and show that T(ucov X) factors over 0
  let TX := T.app (universal_covering X),
  let TN := T.app (nerve U),
  let Kn := K.map (nerve_map U),

  let fz : KX ⟶ 0 := Kn ≫ nz,
  let zg : 0 ⟶ HX := zn ≫ TN ≫ g,

  show _, by 
  calc TX = TX ≫ 𝟙 HX 
          : by simp
      ... = TX ≫ f ≫ g 
          : by {congr, rw fg_idHX}
      ... = Kn ≫ TN ≫ g 
          : by simp -- natural transformation
      ... = Kn ≫ nz ≫ zn ≫ TN ≫ g
          : by simp -- nz ≫ zn cancels
      ... = fz ≫ zg 
          : by simp
      ... = (0 : KX ⟶ 0) ≫ (0 : 0 ⟶ HX)   
          : by {congr, ext, ext}
      ... = 0 
          : by simp,
end