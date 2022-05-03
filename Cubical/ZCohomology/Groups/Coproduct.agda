{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.Groups.Coproduct where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat renaming (_+_ to _+n_ ; _·_ to _·n_ ; snotz to nsnotz)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum renaming (elim to elim-sum ; rec to rec-sum)

open import Cubical.Algebra.Group hiding (UnitGroup₀ ; ℤ; Bool ; _/_ )
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.DirectProd

open import Cubical.Algebra.Direct-Sum.Base

open import Cubical.HITs.SetTruncation
  renaming (rec to sRec ; elim to sElim ; elim2 to sElim2)

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
  Iso.fun (fst Equiv-Coproduct-CoHom)      = sRec (isSet× squash₂ squash₂) (λ f → ∣ f ∘ inl ∣₂ , ∣ (f ∘ inr) ∣₂)
  Iso.inv (fst Equiv-Coproduct-CoHom)      = uncurry
                           (sRec (λ u v p q i j y → squash₂ (u y) (v y) (λ X → p X y) (λ X → q X y) i j)
                           (λ g → sRec squash₂ (λ h → ∣ rec-sum g h ∣₂)))
  Iso.rightInv (fst Equiv-Coproduct-CoHom) = uncurry
                           (sElim (λ x → isProp→isSet λ u v i y → isSet× squash₂ squash₂ _ _ (u y) (v y) i)
                           (λ g → sElim (λ _ → isProp→isSet (isSet× squash₂ squash₂ _ _))
                                   (λ h → refl)))
  Iso.leftInv (fst Equiv-Coproduct-CoHom) = sElim (λ _ → isProp→isSet (squash₂ _ _))
                          λ f → cong ∣_∣₂ (funExt (elim-sum (λ x → refl) (λ x → refl)))
  snd Equiv-Coproduct-CoHom =               makeIsGroupHom
                          (sElim (λ x → isProp→isSet λ u v i y → isSet× squash₂ squash₂ _ _ (u y) (v y) i)
                          (λ g → sElim (λ _ → isProp→isSet (isSet× squash₂ squash₂ _ _))
                          λ h → refl))
