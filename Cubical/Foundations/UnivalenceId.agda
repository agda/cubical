{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.UnivalenceId where

open import Cubical.Core.Glue
  renaming ( isEquiv      to isEquivPath
           ; _≃_          to EquivPath
           ; equivFun     to equivFunPath )
open import Cubical.Core.Id

open import Cubical.Foundations.Prelude public
  hiding ( _≡_ ; _≡⟨_⟩_ ; _∎ )
open import Cubical.Foundations.Id
open import Cubical.Foundations.Equiv
  renaming ( isPropIsEquiv to isPropIsEquivPath )
open import Cubical.Foundations.Univalence
  renaming ( EquivContr   to EquivContrPath )
open import Cubical.Foundations.Isomorphism

path≡Id : ∀ {ℓ} {A B : Type ℓ} → Path _ (Path _ A B) (Id A B)
path≡Id = isoToPath (iso pathToId idToPath idToPathToId pathToIdToPath )

equivPathToEquivPath : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ} → (p : EquivPath A B) →
                       Path _ (equivToEquivPath (equivPathToEquiv p)) p
equivPathToEquivPath (f , p) i =
  ( f , isPropIsEquivPath f (equivToEquivPath (equivPathToEquiv (f , p)) .snd) p i )

equivPath≡Equiv : ∀ {ℓ} {A B : Type ℓ} → Path _ (EquivPath A B) (A ≃ B)
equivPath≡Equiv {ℓ} = isoToPath (iso (equivPathToEquiv {ℓ}) equivToEquivPath equivToEquiv equivPathToEquivPath)

univalenceId : ∀ {ℓ} {A B : Type ℓ} → (A ≡ B) ≃ (A ≃ B)
univalenceId {ℓ} {A = A} {B = B} = equivPathToEquiv rem
  where
  rem0 : Path _ (Lift (EquivPath A B)) (Lift (A ≃ B))
  rem0 = congPath Lift equivPath≡Equiv

  rem1 : Path _ (Id A B) (Lift (A ≃ B))
  rem1 i = hcomp (λ j → λ { (i = i0) → path≡Id {A = A} {B = B} j
                          ; (i = i1) → rem0 j })
                 (univalencePath {A = A} {B = B} i)

  rem : EquivPath (Id A B) (A ≃ B)
  rem = compEquiv (eqweqmap rem1) (invEquiv LiftEquiv)
