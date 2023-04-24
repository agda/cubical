{-# OPTIONS --safe --lossy-unification #-}
module Cubical.ZCohomology.Groups.S2wedgeS1wedgeS1 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat
open import Cubical.Data.Int renaming (_+_ to _ℤ+_)
open import Cubical.Data.Sigma

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Bool
open import Cubical.Algebra.Group.Instances.Int
open import Cubical.Algebra.Group.Instances.Unit

open import Cubical.HITs.Sn
open import Cubical.HITs.S1
open import Cubical.HITs.Susp
open import Cubical.HITs.Wedge
open import Cubical.HITs.Pushout

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.Groups.Wedge
open import Cubical.ZCohomology.Groups.Connected
open import Cubical.ZCohomology.RingStructure.CupProduct




S¹⋁S¹ : Type₀
S¹⋁S¹ = S₊∙ 1 ⋁ S₊∙ 1

S²⋁S¹⋁S¹ : Type₀
S²⋁S¹⋁S¹ = S₊∙ 2 ⋁ (S¹⋁S¹ , inl base)

------------- H⁰(S¹⋁S¹) ------------
H⁰-S¹⋁S¹ : GroupIso (coHomGr 0 S¹⋁S¹) ℤGroup
H⁰-S¹⋁S¹ = H⁰-connected (inl base) (wedgeConnected _ _ (Sn-connected 0) (Sn-connected 0))

------------- H¹(S¹⋁S¹) ------------
H¹-S¹⋁S¹ : GroupIso (coHomGr 1 S¹⋁S¹) (DirProd ℤGroup ℤGroup)
H¹-S¹⋁S¹ =  (Hⁿ-⋁ _ _ 0) □ GroupIsoDirProd H¹-S¹≅ℤ H¹-S¹≅ℤ

------------- H⁰(S²⋁S¹⋁S¹) ---------
H⁰-S²⋁S¹⋁S¹ : GroupIso (coHomGr 0 S²⋁S¹⋁S¹) ℤGroup
H⁰-S²⋁S¹⋁S¹ = H⁰-connected (inl north)
                  (wedgeConnected _ _
                    (Sn-connected 1)
                    (wedgeConnected _ _
                      (Sn-connected 0)
                      (Sn-connected 0)))

------------- H¹(S²⋁S¹⋁S¹) ---------
H¹-S²⋁S¹⋁S¹ : GroupIso (coHomGr 1 S²⋁S¹⋁S¹) (DirProd ℤGroup ℤGroup)
H¹-S²⋁S¹⋁S¹ =
    Hⁿ-⋁ (S₊∙ 2) (S¹⋁S¹ , inl base) 0
  □ GroupIsoDirProd (H¹-Sⁿ≅0 0) H¹-S¹⋁S¹
  □ lUnitGroupIso

------------- H²(S²⋁S¹⋁S¹) ---------

H²-S²⋁S¹⋁S¹ : GroupIso (coHomGr 2 S²⋁S¹⋁S¹) ℤGroup
H²-S²⋁S¹⋁S¹ =
  compGroupIso
  (Hⁿ-⋁ _ _ 1)
  (GroupIsoDirProd {B = UnitGroup₀}
    (Hⁿ-Sⁿ≅ℤ 1)
    ((Hⁿ-⋁ _ _ 1)  □ GroupIsoDirProd (Hⁿ-S¹≅0 0) (Hⁿ-S¹≅0 0) □ rUnitGroupIso)
  □ rUnitGroupIso)

open Iso

to₂ : coHom 2 S²⋁S¹⋁S¹ → ℤ
to₂ = fun (fst H²-S²⋁S¹⋁S¹)
from₂ : ℤ → coHom 2 S²⋁S¹⋁S¹
from₂ = inv (fst H²-S²⋁S¹⋁S¹)

to₁ : coHom 1 S²⋁S¹⋁S¹ → ℤ × ℤ
to₁ = fun (fst H¹-S²⋁S¹⋁S¹)
from₁ : ℤ × ℤ → coHom 1 S²⋁S¹⋁S¹
from₁ = inv (fst H¹-S²⋁S¹⋁S¹)

to₀ : coHom 0 S²⋁S¹⋁S¹ → ℤ
to₀ = fun (fst H⁰-S²⋁S¹⋁S¹)
from₀ : ℤ → coHom 0 S²⋁S¹⋁S¹
from₀ = inv (fst H⁰-S²⋁S¹⋁S¹)

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

test5 : to₂ (from₂ 1 +ₕ from₂ 1) ≡ 2
test5 = refl
-}
{-
  g : S²⋁S¹⋁S¹ → ∥ Susp S¹ ∥ 4
  g (inl x) = ∣ x ∣
  g (inr x) = 0ₖ _
  g (push a i) = 0ₖ _

  G = ∣ g ∣₂

-- Does not compute:
test₀ : to₂ (G +ₕ G) ≡ 2
test₀ = refl

but this does:
test₀ : to₂ (G +'ₕ G) ≡ 2
test₀ = refl
-}


-- Cup product is trivial
⌣-gen₁ : to₂ (from₁ (1 , 0) ⌣ from₁ (0 , 1)) ≡ 0
⌣-gen₁ = refl

-- Even better:
⌣-gen : (x y : ℤ × ℤ) → to₂ (from₁ x ⌣ from₁ y) ≡ 0
⌣-gen x y = refl
