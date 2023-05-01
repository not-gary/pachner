/-
Copyright (c) 2022 Clara Löh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.txt.
Author: Clara Löh.
-/

import tactic   -- standard proof tactics
import algebra.group.basic -- basic group theory

open classical  -- we work in classical logic

/-
# Commutators in groups
-/

-- we define the commutator of two given group elements
def cmtr 
    {G : Type*} [group G]
    (g : G)
    (h : G)
:= g * h * g⁻¹ * h⁻¹

-- images of commutators under homomorphisms are commutators
lemma cmtr_hom
    {G : Type*} [group G]
    {H : Type*} [group H]
    (f : monoid_hom G H) -- f is a group homomorphism
    (g : G)
    (h : G)
  : f (cmtr g h) = cmtr (f g) (f h)
:= 
begin
  -- this is a straightforward computation,
  -- using that f is a homomorphism
  calc f (cmtr g h) = f (g * h * g⁻¹ * h⁻¹) 
                    : by simp[cmtr]
                ... = f g * f h * f (g⁻¹) * f (h⁻¹) 
                    : by simp[mul_hom.map_mul]
                ... = f g * f h * (f g)⁻¹ * (f h)⁻¹ 
                    : by {congr, simp only[monoid_hom.map_inv], simp only[monoid_hom.map_inv]}
                ... = cmtr (f g) (f h) 
                    : by simp[cmtr],
end      

-- as a preparation for triple powers of commutators,
-- we establish that g^3 = g * g * g:
lemma pow_three
    {G : Type*} [group G]
    (g : G)
  : g^3 = g * g * g
:= 
begin
  group,
end

-- triple powers of commutators are products of _two_ commutators
lemma cmtr_pow_three
    {G : Type*} [group G]
    (a : G) {A : G} {A_def : A = a⁻¹}
    (b : G) {B : G} {B_def : B = b⁻¹}
  : (cmtr a b)^3 = cmtr (a*b*A) (B*a*b*A^2) * cmtr (B*a*b) (b^2)
:=
begin
  -- with the help of pow_three, 
  -- the group tactic can perform the computation
  simp only[cmtr,pow_three,A_def,B_def], 
  group,
end