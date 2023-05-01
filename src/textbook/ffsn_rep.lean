/-
Copyright (c) 2022 Clara Löh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.txt.
Author: Clara Löh.
-/

import tactic -- standard proof tactics
import data.real.basic
import zero -- a criterion for real numbers to be zero
import algebra.category.Group.basic -- the category of Abelian groups
import category_theory.functor -- functors
import analysis.normed.group.SemiNormedGroup -- the category of semi-normed Abelian groups with maps of norm ≤ 1

open classical -- we work in classical logic

/- 
  This is an implementation of parts of the article:
  C. L"oh.  
  "Finite functorial semi-norms and representability", 
  IMRN, 2016(12), 3616--3638, 2016.
-/

/-
# Semi-norms
-/

/- The category SemiNormedGroup₁ from analysis.normed.group.SemiNormedGroup
   is the (concrete) category, consisting of: 
   * objects: semi-normed Abelian groups;
   * morphisms: group homomorphisms that do not increase the semi-norm.
-/

-- We use the following abbreviations:
notation `Ab`   := AddCommGroup
notation `Absn` := SemiNormedGroup₁

-- The forgetful functor Absn ⥤ Ab 
noncomputable
instance has_forget_Absn_Ab : category_theory.has_forget₂ Absn Ab 
:= { forget₂ :=
     { obj := λ X, AddCommGroup.of X,
       map := λ X Y, λ f : X ⟶ Y, 
              AddCommGroup.of_hom (normed_group_hom.to_add_monoid_hom f)
     }
   }

notation `forget_sn` := has_forget_Absn_Ab.forget₂

/-
# Functorial semi-norms
-/

-- A functorial semi-norm on a functor F 
-- is a factorisation of F  
-- over the forget functor SemiNormedGroup₁ ⥤ AddCommGroup
-- (up to a natural isomorphism)
def ffsn_on
    {C : Type*} [C_is_cat : category_theory.category C]
    (F : C ⥤ Ab)
    (Fsn : C ⥤ Absn)   
:= F ≅ Fsn ⋙ forget_sn 
-- note that ≅ does not mean "is isomorphic to", 
-- but denotes the type of isomorphisms;

-- A functorial semi-norm is homogeneous 
-- if it is object-wise homogeneous
def is_homogeneous_fsn
    {C : Type*} [C_is_cat : category_theory.category C]
    (Fsn : C ⥤ Absn) 
  : Prop
:= ∀ X : C, ∀ a : (Fsn.obj) X, 
   ∀ n : ℤ, ∥ n • a ∥ = |↑n| * ∥ a ∥       

-- Setup: 
-- In the following, we consider a functor 
-- from some category to the category of Abelian groups 
-- and a (finite homogeneous) functorial semi-norm on F.
structure ffsn_setup 
   (C : Type*) 
   [C_is_cat : category_theory.category C]
:= mk :: (F : C ⥤ Ab)
         (Fsn : C ⥤ Absn)
         (Fsn_ffsn_on_F      : ffsn_on F Fsn)
         (Fsn_is_homogeneous : is_homogeneous_fsn Fsn)

-- The key property of functorial semi-norms:
-- norms of classes decrease under morphisms
lemma fsn_est_explicit
      {C : Type*} [C_is_cat : category_theory.category C]
      (s : ffsn_setup C)
      {Y : C}
      {X : C}
      (f : Y ⟶ X)
      (b : s.Fsn.obj Y)
    : ∥ s.Fsn.map f b ∥ ≤ ∥ b ∥   
:=
begin
  -- we just spell out the properties of morphisms in Absn
  let f' := s.Fsn.map f,
  have f_noninc : normed_group_hom.norm_noninc f'.1, 
       by exact f'.2,
  show _, 
       by exact f_noninc b,
end 


/-
# Viewing F-classes as Fsn-classes
-/

-- Functors connected through forget_sn, 
-- on objects, lead to the same underlying Abelian group
noncomputable
def underlying_add_comm_group_iso
      {C : Type*} [C_is_cat : category_theory.category C]
      (s : ffsn_setup C)
      (X : C)
    : s.F.obj X ≅ AddCommGroup.of (s.Fsn.obj X).1 
:= s.Fsn_ffsn_on_F.app X 

-- Hence, for a functorial semi-norm Fsn on F,
-- we can view F-classes as Fsn-classes:
 
-- We split this lifting process into two steps:
-- * lift1 lifts from F X to AddCommGroup.of (Fsn X),
--   using the natural isomorphism from F to Fsn ⋙ forget_sn
-- * lift2 lifts from AddCommGroup.of (Fsn X) to Fsn X
--   using built-in conversions of carriers

noncomputable
def lift1
    {C : Type*} [C_is_cat : category_theory.category C]
    (s : ffsn_setup C)
    {X : C}
  : s.F.obj X → AddCommGroup.of (s.Fsn.obj X)
:= (s.Fsn_ffsn_on_F.app X).hom

def lift2
    {C : Type*} [C_is_cat : category_theory.category C]
    (s : ffsn_setup C)
    {X : C}
  : AddCommGroup.of (s.Fsn.obj X) → (s.Fsn.obj X)
:= by tauto

@[simp]
noncomputable
def lift_elt
    {C : Type*} [C_is_cat : category_theory.category C]
    (s : ffsn_setup C)
    {X : C}
  : (s.F.obj X) → (s.Fsn.obj X)
:= (lift2 s) ∘ (lift1 s)

-- Thus: 
-- Using a functorial semi-norm Fsn on F,
-- we can measure the size of F-classes,
-- by viewing F-classes as Fsn-classes
@[simp]
noncomputable
def sn 
    {C : Type*} [C_is_cat : category_theory.category C]
    (s : ffsn_setup C)
    {X : C}
    (a : s.F.obj X)
  : ℝ 
:= ∥ lift_elt s a ∥


-- To use lift_elt in computations, it is useful to know that 
-- lift_elt is compatible with zsmul and that it is natural.

-- compatibility of lift_elt with zsmul;
-- we first prove the corresponding statements for lift1, lift2, 
-- and then combine them
lemma lift1_zsmul
    {C : Type*} [C_is_cat : category_theory.category C]
    (s : ffsn_setup C)
    (X : C)
  : ∀ n : int, ∀ a : s.F.obj X, 
    lift1 s (n • a) = n • lift1 s a
:=
begin
  simp[lift1],
end     

lemma lift2_zsmul 
    {C : Type*} [C_is_cat : category_theory.category C]
    (s : ffsn_setup C)
    {X : C}
  : ∀ n : int, ∀ a : AddCommGroup.of (s.Fsn.obj X), 
    lift2 s (n • a) = n • lift2 s a
:=
begin
  tauto,
end

lemma lift_elt_zsmul
    {C : Type*} [C_is_cat : category_theory.category C]
    (s : ffsn_setup C)
    {X : C}
  : ∀ n : int, ∀ a : s.F.obj X, 
    lift_elt s (n • a) = n • lift_elt s a
:=
begin
  simp[lift1_zsmul, lift2_zsmul],
end


-- compatibility of lift_elt with morphisms;
-- we first prove the corresponding statements for lift1, lift2, 
-- and then combine them
noncomputable
def underlying_hom
    {C : Type*} [C_is_cat : category_theory.category C]
    (s : ffsn_setup C)
    {Y : C}
    {X : C}
    (f : Y ⟶ X)  
:= AddCommGroup.of_hom 
   (normed_group_hom.to_add_monoid_hom (s.Fsn.map f).1)

lemma lift1_map
      {C : Type*} [C_is_cat : category_theory.category C]
      (s : ffsn_setup C)
      {Y : C}
      {X : C}
      (f : Y ⟶ X)
      (b : s.F.obj Y)
    : lift1 s (s.F.map f b) 
    = (underlying_hom s f) (lift1 s b)  
:= 
begin
  -- the natural iso translating between F and Fsn ⋙ forget_sn
  let t := s.Fsn_ffsn_on_F,
  
  calc lift1 s (s.F.map f b)
        = ((s.F.map f) ≫ (t.hom.app X)) b
        : by congr
    ... = ((t.hom.app Y) ≫ ((s.Fsn ⋙ forget_sn).map f)) b  
        : by rw [t.hom.naturality']
    ... = underlying_hom s f (lift1 s b)
        : by refl,
end

lemma lift2_map
      {C : Type*} [C_is_cat : category_theory.category C]
      (s : ffsn_setup C)
      {Y : C}
      {X : C}
      (f : Y ⟶ X)
      (b : AddCommGroup.of (s.Fsn.obj Y))
    : lift2 s (underlying_hom s f b)
    = s.Fsn.map f (lift2 s b) 
:= 
begin
  tauto,
end

lemma lift_elt_map
      {C : Type*} [C_is_cat : category_theory.category C]
      (s : ffsn_setup C)
      {Y : C}
      {X : C}
      (f : Y ⟶ X)
      (b : s.F.obj Y)
    : lift_elt s (s.F.map f b) = s.Fsn.map f (lift_elt s b)
:=
begin
  simp[lift1_map,lift2_map],
end


/-
# Weakly flexible classes
-/

-- the set of "degrees" between two classes
def deg 
    {C : Type*} [C_is_cat : category_theory.category C]
    (s : ffsn_setup C)
    {X : C}
    (a : s.F.obj X)
    {Y : C}
    (b : s.F.obj Y)
  : set ℤ   
:= { n : ℤ | ∃ f : Y ⟶ X, 
             (s.F.map f) b = n • a}    

-- a class a is weakly flexible if there exists a class b
-- such that the set of degrees from b to a is infinite 
def is_weakly_flexible
    {C : Type*} [C_is_cat : category_theory.category C]
    (s : ffsn_setup C)
    {X : C}
    (a : s.F.obj X)
:= ∃ Y : C, ∃ b : s.F.obj Y,  
   ∀ k : ℕ, ∃ n : ℤ, n ∈ deg s a b  
                   ∧ |n| ≥ k

-- straightforward degree estimate for norms 
lemma deg_estimate
      {C : Type*} [C_is_cat : category_theory.category C]
      (s : ffsn_setup C)
      {X : C}
      (a : s.F.obj X)
      {Y : C}
      (b : s.F.obj Y)
      (n : ℤ)
      (n_deg_ba : n ∈ deg s a b)
      (abs_n_pos : 0 < (|n| : real))
    : sn s a  ≤ sn s b / |↑n|
:= 
begin
  -- we introduce notation    
  let a' := lift_elt s a,
  let b' := lift_elt s b,
  -- hence: sn s a = ∥ a' ∥ and sn s b = ∥ b' ∥

  -- we extract a morphism witnessing the degree condition
  have ex_f_bna : ∃ f : Y ⟶ X, (s.F.map f) b = n • a, from
  begin
    dsimp only[deg] at n_deg_ba,
    assumption,
  end, 
  rcases ex_f_bna with ⟨ f : Y ⟶ X, f_deg ⟩,

  -- using the monotonicity of f, 
  -- we first prove a division-free version of the claim
  have n_times_thesis : |↑n| * ∥ a' ∥ ≤ ∥ b' ∥, from 
  calc |↑n| * ∥ a' ∥ = ∥ n • a' ∥ 
                     : by rw s.Fsn_is_homogeneous
                 ... = ∥ lift_elt s ((s.F.map f) b) ∥
                     : by {congr, simp only[f_deg], dsimp only[a'], 
                           exact (lift_elt_zsmul s n a).symm} 
                 ... = ∥ s.Fsn.map f b' ∥ 
                     : by {congr, exact (lift_elt_map s f b)}    
                 ... ≤ ∥ b' ∥ 
                     : by exact fsn_est_explicit _ _ b',

  -- from the division-free version, we conclude the actual claim
  calc ∥ a' ∥ ≤ ∥ b' ∥ / |n| 
          : by exact (le_div_iff' abs_n_pos).mpr n_times_thesis,
end  

/-
# Vanishing of functorial semi-norms on weakly flexible classes
-/

-- Proposition 3.4 of the article:
--   Functorial semi-norms have zero semi-norm
--   on all weakly flexible classes
theorem weakly_flexible_zero_fsn
     {C : Type*} [C_is_cat : category_theory.category C]
     (s : ffsn_setup C)
     {X : C}
     (a : s.F.obj X)
     (a_is_weakly_flexible : is_weakly_flexible s a)
   : sn s a = 0
:= 
begin
  let a' := lift_elt s a,
  -- thus, we need to show that ∥ a' ∥ = 0

  -- weak flexibility gives us a class b 
  -- that has infinitely many degrees to a
  rcases a_is_weakly_flexible with ⟨ Y : C, ⟨ b : s.F.obj Y, deg_ba_infinite ⟩ ⟩,

  let c := sn s b,
  have c_geq_0 : 0 ≤ c, 
       by {dsimp only[c], exact norm_nonneg (lift_elt s b)},

  -- from the degrees, we obtain the following estimate:
  have a_leq_c_over_n : ∀ n : nat, n > 0 → abs (∥ a' ∥) ≤ c / (n : real), from
  begin
    assume n : nat,
    assume n_pos : n > 0,

    -- we extract a suitable degree ...
    rcases (deg_ba_infinite n) with ⟨ m : ℤ, ⟨ m_is_deg, abs_m_geq_n ⟩⟩,
   
    -- ... make some basic observations ... 
    have pos_n : 0 < (n : real), 
         by exact nat.cast_pos.mpr n_pos,
    have n_leq_abs_m : (n : real) ≤ |↑m|, 
         by {norm_cast at *, exact abs_m_geq_n},
    have pos_abs_m : 0 < (|m| : real), 
         by exact gt_of_ge_of_gt n_leq_abs_m pos_n,

    -- ... and combine the estimates
    calc abs (∥ a' ∥) 
             = ∥ a' ∥ 
             : by exact abs_norm_eq_norm a'
         ... ≤ ∥ lift_elt s b ∥ / |m|
             : by exact deg_estimate _ a b m m_is_deg pos_abs_m
         ... ≤ c / |m|
             : by refl
         ... ≤ c / (n : real)
             : by exact div_le_div_of_le_left c_geq_0 pos_n n_leq_abs_m,    
  end,

  -- we conclude using the archimedean property of ℝ 
  -- through zero_via_1_over_n
  show _, 
       by exact zero_via_1_over_n (∥ a' ∥) c a_leq_c_over_n,
end

/-
# Representable functors only admit trivial finite functorial semi-norms
-/

-- The forgetful functor Ab ⥤ Type ...
@[simp]
def forget_Ab := category_theory.forget Ab


-- Preparation:
-- For a representable functor F to Ab, 
-- every F-class is a push-forward of the universal class
lemma representable_rep 
     {C : Type*} [C_is_cat : category_theory.category C]
     (F : C ⥤ Ab)
     (F_is_corep : category_theory.functor.corepresentable 
                   (F ⋙ forget_Ab))
     {X : C}
     (a : F.obj X)
   : ∃ f : (F ⋙ forget_Ab).corepr_X ⟶ X, 
     (F.map f) (F ⋙ forget_Ab).corepr_x = a
:=
begin
  let G := F ⋙ forget_Ab,
  let Y := G.corepr_X, -- "the" representing object
  let b := G.corepr_x, -- "the" universal element

  -- the underlying carriers of F X and G X coincide
  have eq_GX : G.obj X = (F.obj X).1, by refl,
  have eq_GY : G.obj Y = (F.obj Y).1, by refl,

  -- the morphism corresponding to a via representability ...
  let f := (G.corepr_w.app X).inv a,
  -- ... is the desired morphism, because ...
  use f,
  -- ... it maps the universal element to a
  show _, by 
  calc F.map f b = G.map f b 
                 : by tauto
             ... = (G.corepr_w.app X).hom f  
                 : by exact (category_theory.functor.corepr_w_app_hom G X f).symm
             ... = a 
                 : by simp,
end

-- Preparation:
-- If a degree set is Z, 
-- then clearly the corresponding class is weakly flexible
lemma deg_Z_weakly_flexible
     {C : Type*} [C_is_cat : category_theory.category C]
     (s : ffsn_setup C)
     {X : C}
     (a : s.F.obj X)
     {Y : C}
     (b : s.F.obj Y)
     (deg_ab_Z : deg s a b = { n : ℤ | tt })
   : is_weakly_flexible s a
:=
begin
  unfold is_weakly_flexible,
  use Y,
  use b,
  assume k : ℕ,

  use ↑k,
  finish,
end   

-- Corollary 4.1 of the article:
-- Functorial semi-norms on representable functors are trivial
theorem representable_zero_fsn 
     {C : Type*} [C_is_cat : category_theory.category C]
     (s : ffsn_setup C)
     (F_is_corep : category_theory.functor.corepresentable 
                   (s.F ⋙ forget_Ab))
     {X : C}
     (a : s.F.obj X)
   : sn s a = 0
:= 
begin
  let G := s.F ⋙ forget_Ab,

  -- we use the universal element for F (resp. G) 
  -- to show that a is weakly flexible;
  let Y := category_theory.functor.corepr_X G, -- "the" representing object
  let b := category_theory.functor.corepr_x G, -- "the" universal element

  -- more precisely, we show that the degree set is all of ℤ 
  have deg_ab_Z : deg s a b = { n : ℤ | tt }, from 
  begin
    -- by definition, every degree is an integer
    have deg_sub_Z : deg s a b ⊆ { n : ℤ | tt }, from 
    begin
      unfold deg,
      finish,
    end,

    -- conversely, universality shows 
    -- that every integer can be realised as degree
    have Z_sub_deg : {n : ℤ | tt } ⊆ deg s a b, from
    begin
      assume n : ℤ,
      assume n_in_Z : n ∈ { m : ℤ | tt },

      simp only[deg, set.mem_set_of_eq],

      show ∃ (f : Y ⟶ X), (s.F.map f) b = n • a, 
           by exact representable_rep s.F F_is_corep (n • a),
    end,

    show _, 
         by exact set.subset.antisymm deg_sub_Z Z_sub_deg,
  end,

  -- we use the universal class as witness; 
  -- because the degree set is all of ℤ, 
  -- the weak flexiblity condition is clearly satisfied
  have a_is_weakly_flexible : is_weakly_flexible s a, 
       by exact deg_Z_weakly_flexible s a b deg_ab_Z,

  -- thus, we can apply the theorem on vanishing of functorial semi-norms
  -- on weakly flexible classes
  show _, 
       by exact weakly_flexible_zero_fsn s a a_is_weakly_flexible,
end

