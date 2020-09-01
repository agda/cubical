{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.ZCohomology.Groups.WedgeOfSpheres where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.Groups.Wedge
open import Cubical.ZCohomology.Groups.Connected

open import Cubical.HITs.Sn
open import Cubical.Foundations.Prelude
open import Cubical.HITs.Susp
open import Cubical.HITs.Wedge
open import Cubical.HITs.Pushout
open import Cubical.HITs.Truncation renaming (elim to trElim)
open import Cubical.Algebra.Group

S¹⋁S¹ : Type₀
S¹⋁S¹ = S₊∙ 1 ⋁ S₊∙ 1

S²⋁S¹⋁S¹ : Type₀
S²⋁S¹⋁S¹ = S₊∙ 2 ⋁ (S¹⋁S¹ , inl north)

------------- H⁰(S¹⋁S¹) ------------
H⁰-S¹⋁S¹ : GroupEquiv (coHomGr 0 S¹⋁S¹) intGroup
H⁰-S¹⋁S¹ = H⁰-connected (inl north) (wedgeConnected _ _  (Sn-connected _) (Sn-connected _))

------------- H¹(S¹⋁S¹) ------------
H¹-S¹⋁S¹ : GroupEquiv (coHomGr 1 S¹⋁S¹) (dirProd intGroup intGroup)
H¹-S¹⋁S¹ =  (Hⁿ-⋁ _ _ 0) □ dirProdEquiv coHom1S1≃ℤ coHom1S1≃ℤ

------------- H⁰(S²⋁S¹⋁S¹) ---------
H⁰-S²⋁S¹⋁S¹ : GroupEquiv (coHomGr 0 S²⋁S¹⋁S¹) intGroup
H⁰-S²⋁S¹⋁S¹ = H⁰-connected (inl north)
                  (wedgeConnected _ _
                    (Sn-connected _)
                    (wedgeConnected _ _
                      (Sn-connected _)
                      (Sn-connected _)))

------------- H¹(S²⋁S¹⋁S¹) ---------
H¹-S²⋁S¹⋁S¹ : GroupEquiv (coHomGr 1 S²⋁S¹⋁S¹) (dirProd intGroup intGroup)
H¹-S²⋁S¹⋁S¹ =
    Hⁿ-⋁ (S₊∙ 2) (S¹⋁S¹ , inl north) 0
  □ dirProdEquiv (H¹-Sⁿ≅0 0) H¹-S¹⋁S¹
  □ lUnitGroupIso

------------- H²(S²⋁S¹⋁S¹) ---------
H²-S²⋁S¹⋁S¹ : GroupEquiv (coHomGr 2 S²⋁S¹⋁S¹) intGroup
H²-S²⋁S¹⋁S¹ =
  compGroupEquiv
  (Hⁿ-⋁ _ _ 1)
  (dirProdEquiv (invGroupEquiv (Hⁿ-Sⁿ≅ℤ 1))
                  ((Hⁿ-⋁ _ _ 1)
                 □ dirProdEquiv H²-S¹≅0 H²-S¹≅0
                 □ rUnitGroupIso)
  □ rUnitGroupIso)

private
  open import Cubical.Data.Int
  open import Cubical.Foundations.Equiv
  open import Cubical.Data.Sigma
  to₂ : coHom 2 S²⋁S¹⋁S¹ → Int
  to₂ = fst (GroupEquiv.eq H²-S²⋁S¹⋁S¹)
  from₂ : Int → coHom 2 S²⋁S¹⋁S¹
  from₂ = invEq (GroupEquiv.eq H²-S²⋁S¹⋁S¹)

  to₁ : coHom 1 S²⋁S¹⋁S¹ → Int × Int
  to₁ = fst (GroupEquiv.eq H¹-S²⋁S¹⋁S¹)
  from₁ : Int × Int → coHom 1 S²⋁S¹⋁S¹
  from₁ = invEq (GroupEquiv.eq H¹-S²⋁S¹⋁S¹)

  to₀ : coHom 0 S²⋁S¹⋁S¹ → Int
  to₀ = fst (GroupEquiv.eq H⁰-S²⋁S¹⋁S¹)
  from₀ : Int → coHom 0 S²⋁S¹⋁S¹
  from₀ = invEq (GroupEquiv.eq H⁰-S²⋁S¹⋁S¹)
