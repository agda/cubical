{-# OPTIONS --cubical --no-import-sorts --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.Groups.WedgeOfSpheres where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.Groups.Wedge
open import Cubical.ZCohomology.Groups.Connected
open import Cubical.Data.Int renaming (_+_ to _ℤ+_)

open import Cubical.HITs.Sn
open import Cubical.HITs.S1
open import Cubical.Foundations.Prelude
open import Cubical.HITs.Susp
open import Cubical.HITs.Wedge
open import Cubical.HITs.Pushout
open import Cubical.HITs.Truncation renaming (elim to trElim) hiding (map ; elim2)
open import Cubical.Algebra.Group
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; rec2 to sRec2 ; elim to sElim)

{-
open import Cubical.Data.Nat
open import Cubical.Foundations.Equiv
open import Cubical.Data.Empty
open import Cubical.Foundations.HLevels
open import Cubical.Homotopy.WedgeConnectivity
open import Cubical.Foundations.Isomorphism
n≥ : (n m : ℕ) → isOfHLevel ((2 + n) + (2 + n)) (S₊ (2 + n)) → ⊥
n≥ n zero hlev = {!!}
n≥ n (suc m) hlev = {!!}
  where
  +-mega = wedgeConSn (suc n) (suc n) (λ _ _ → hlev) (λ x → x) (λ x → x) refl

  _+*_ : S₊ (2 + n) → S₊ (2 + n) → S₊ (2 + n)
  _+*_ = +-mega .fst

  isEq : (x : S₊ (2 + n)) → isEquiv (x +*_)
  isEq = sphereElim _ (λ _ → isProp→isOfHLevelSuc _ (isPropIsEquiv _)) (idIsEquiv _)

  -*_ : S₊ (2 + n) → S₊ (2 + n)
  -* x = invEq (_ , (isEq x)) north

  _-*_ : S₊ (2 + n) → S₊ (2 + n) → S₊ (2 + n)
  _-*_ x y = x +* (-* y)
  
  LUNIT : (x : S₊ (2 + n)) → north +* x ≡ x
  LUNIT x = refl

  RUNIT : (x : S₊ (2 + n)) → x +* north ≡ x
  RUNIT x = +-mega .snd .snd x

  COMM : (x y : S₊ (2 + n)) → (x +* y) ≡ (y +* x)
  COMM = wedgeConSn _ _ (λ _ _ → isOfHLevelPath ((2 + n) + (2 + n)) hlev _ _)
                        (λ _ → sym (RUNIT _))
                        (λ _ → RUNIT _)
                        refl .fst
  
  RCANCEL : (x : S₊ (2 + n)) → (x -* x) ≡ north
  RCANCEL x = retEq (_ , isEq x) north

  LCANCEL : (x : S₊ (2 + n)) → ((-* x) +* x) ≡ north
  LCANCEL x = COMM _ _ ∙ RCANCEL _
  
  open import Cubical.Foundations.Univalence 
  CODE : S₊ (3 + n) → Type₀
  CODE north = S₊ (2 + n)
  CODE south = S₊ (2 + n)
  CODE (merid a i) = ua (_ , isEq a) i
-}

S¹⋁S¹ : Type₀
S¹⋁S¹ = S₊∙ 1 ⋁ S₊∙ 1

S²⋁S¹⋁S¹ : Type₀
S²⋁S¹⋁S¹ = S₊∙ 2 ⋁ (S¹⋁S¹ , inl base)

------------- H⁰(S¹⋁S¹) ------------
H⁰-S¹⋁S¹ : GroupIso (coHomGr 0 S¹⋁S¹) intGroup
H⁰-S¹⋁S¹ = H⁰-connected (inl base) (wedgeConnected _ _ (Sn-connected 0) (Sn-connected 0))

------------- H¹(S¹⋁S¹) ------------
H¹-S¹⋁S¹ : GroupIso (coHomGr 1 S¹⋁S¹) (dirProd intGroup intGroup)
H¹-S¹⋁S¹ =  (Hⁿ-⋁ _ _ 0) □ dirProdGroupIso coHom1S1≃ℤ coHom1S1≃ℤ

------------- H⁰(S²⋁S¹⋁S¹) ---------
H⁰-S²⋁S¹⋁S¹ : GroupIso (coHomGr 0 S²⋁S¹⋁S¹) intGroup
H⁰-S²⋁S¹⋁S¹ = H⁰-connected (inl north)
                  (wedgeConnected _ _
                    (Sn-connected 1)
                    (wedgeConnected _ _
                      (Sn-connected 0)
                      (Sn-connected 0)))

------------- H¹(S²⋁S¹⋁S¹) ---------
H¹-S²⋁S¹⋁S¹ : GroupIso (coHomGr 1 S²⋁S¹⋁S¹) (dirProd intGroup intGroup)
H¹-S²⋁S¹⋁S¹ =
    Hⁿ-⋁ (S₊∙ 2) (S¹⋁S¹ , inl base) 0
  □ dirProdGroupIso (H¹-Sⁿ≅0 0) H¹-S¹⋁S¹
  □ lUnitGroupIso

------------- H²(S²⋁S¹⋁S¹) ---------

H²-S²⋁S¹⋁S¹ : GroupIso (coHomGr 2 S²⋁S¹⋁S¹) intGroup
H²-S²⋁S¹⋁S¹ =
  compGroupIso
  (Hⁿ-⋁ _ _ 1)
  (dirProdGroupIso {B = trivialGroup}
    (Hⁿ-Sⁿ≅ℤ 1)
    ((Hⁿ-⋁ _ _ 1)  □ dirProdGroupIso (Hⁿ-S¹≅0 0) (Hⁿ-S¹≅0 0) □ rUnitGroupIso)
  □ rUnitGroupIso)

module _ where -- private
  open import Cubical.Data.Int
  open import Cubical.Foundations.Equiv
  open import Cubical.Data.Sigma
  to₂ : coHom 2 S²⋁S¹⋁S¹ → Int
  to₂ = GroupHom.fun (GroupIso.map H²-S²⋁S¹⋁S¹)
  from₂ : Int → coHom 2 S²⋁S¹⋁S¹
  from₂ = GroupIso.inv H²-S²⋁S¹⋁S¹

  to₁ : coHom 1 S²⋁S¹⋁S¹ → Int × Int
  to₁ = GroupHom.fun (GroupIso.map H¹-S²⋁S¹⋁S¹)
  from₁ : Int × Int → coHom 1 S²⋁S¹⋁S¹
  from₁ = GroupIso.inv H¹-S²⋁S¹⋁S¹

  to₀ : coHom 0 S²⋁S¹⋁S¹ → Int
  to₀ = GroupHom.fun (GroupIso.map H⁰-S²⋁S¹⋁S¹)
  from₀ : Int → coHom 0 S²⋁S¹⋁S¹
  from₀ = GroupIso.inv H⁰-S²⋁S¹⋁S¹

{-

-- Compute pretty fast
test1 : to₁ (from₁ (1 , 0) +ₕ from₁ (0 , 1)) ≡ (1 , 1)
test1 = refl

-- Computes, but only when computing some smaller numbers first
test2 : to₁ (from₁ (50 , 3) +ₕ from₁ (2 , -2)) ≡ (52 , 1)
test2 = refl

test3 : to₂ (from₂ 0) ≡ 0
test3 = refl

test4 : to₂ (from₂ 3) ≡ 3
test4 = refl

-- Does not compute:

test5 : to₂ (from₂ 1 +ₕ from₂ 1) ≡ 2
test5 = refl

-- This does however compute with the induced addition
test5' : to₂ (induced+ H²-S²⋁S¹⋁S¹ (from₂ 1) (from₂ 1)) ≡ 2
test5' = refl
-}
