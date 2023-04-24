{-# OPTIONS --safe --lossy-unification #-}
module Cubical.ZCohomology.Groups.Coproduct where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.DirectProd

open import Cubical.HITs.SetTruncation as ST

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure

private variable
  ℓ ℓ' : Level

module _
  {X : Type ℓ}
  {Y : Type ℓ'}
  where

  open Iso
  open IsGroupHom
  open GroupStr

  Equiv-Coproduct-CoHom : {n : ℕ} → GroupIso (coHomGr n (X ⊎ Y)) (DirProd (coHomGr n X) (coHomGr n Y))
  Iso.fun (fst Equiv-Coproduct-CoHom)      = ST.rec (isSet× squash₂ squash₂) (λ f → ∣ f ∘ inl ∣₂ , ∣ (f ∘ inr) ∣₂)
  Iso.inv (fst Equiv-Coproduct-CoHom)      = uncurry
                           (ST.rec (λ u v p q i j y → squash₂ (u y) (v y) (λ X → p X y) (λ X → q X y) i j)
                           (λ g → ST.rec squash₂ (λ h → ∣ Sum.rec g h ∣₂)))
  Iso.rightInv (fst Equiv-Coproduct-CoHom) = uncurry
                           (ST.elim (λ x → isProp→isSet λ u v i y → isSet× squash₂ squash₂ _ _ (u y) (v y) i)
                           (λ g → ST.elim (λ _ → isProp→isSet (isSet× squash₂ squash₂ _ _))
                                   (λ h → refl)))
  Iso.leftInv (fst Equiv-Coproduct-CoHom) = ST.elim (λ _ → isProp→isSet (squash₂ _ _))
                          λ f → cong ∣_∣₂ (funExt (Sum.elim (λ x → refl) (λ x → refl)))
  snd Equiv-Coproduct-CoHom =               makeIsGroupHom
                          (ST.elim (λ x → isProp→isSet λ u v i y → isSet× squash₂ squash₂ _ _ (u y) (v y) i)
                          (λ g → ST.elim (λ _ → isProp→isSet (isSet× squash₂ squash₂ _ _))
                          λ h → refl))
