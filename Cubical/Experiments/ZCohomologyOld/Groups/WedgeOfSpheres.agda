{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Experiments.ZCohomologyOld.Groups.WedgeOfSpheres where

open import Cubical.ZCohomology.Base
open import Cubical.Experiments.ZCohomologyOld.Properties
open import Cubical.Experiments.ZCohomologyOld.Groups.Unit
open import Cubical.Experiments.ZCohomologyOld.Groups.Sn
open import Cubical.Experiments.ZCohomologyOld.Groups.Wedge
open import Cubical.Experiments.ZCohomologyOld.Groups.Connected

open import Cubical.HITs.Sn
open import Cubical.HITs.S1
open import Cubical.Foundations.Prelude
open import Cubical.HITs.Susp
open import Cubical.HITs.Wedge
open import Cubical.HITs.Pushout
open import Cubical.HITs.Truncation renaming (elim to trElim)
open import Cubical.Algebra.Group

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
    (invGroupIso (Hⁿ-Sⁿ≅ℤ 1))
    ((Hⁿ-⋁ _ _ 1)  □ dirProdGroupIso (Hⁿ-S¹≅0 0) (Hⁿ-S¹≅0 0) □ rUnitGroupIso)
  □ rUnitGroupIso)

private
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
-- Computes (a lot slower than for the torus)
test : to₁ (from₁ (1 , 0) +ₕ from₁ (0 , 1)) ≡ (1 , 1)
test = refl

-- Does not compute:
test2 : to₂ (from₂ 0) ≡ 0
test2 = refl
-}
