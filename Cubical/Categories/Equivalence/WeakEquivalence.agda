{-# OPTIONS --safe #-}

module Cubical.Categories.Equivalence.WeakEquivalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
  renaming (isEquiv to isEquivMap)
open import Cubical.Functions.Surjection
open import Cubical.Functions.Embedding
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Morphism
open import Cubical.Categories.Equivalence
open import Cubical.HITs.PropositionalTruncation.Base

open Category
open Functor
open NatIso
open isIso
open NatTrans
open isEquivalence
open _≃ᶜ_

private
  variable
    ℓC ℓC' ℓD ℓD' : Level
    C : Category ℓC ℓC'
    D : Category ℓD ℓD'
    F : Functor C D


record isWeakEquivalence {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
        (func : Functor C D) : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
  field

    fullfaith : isFullyFaithful   func
    esssurj   : isEssentiallySurj func

record WeakEquivalence (C : Category ℓC ℓC') (D : Category ℓD ℓD')
  : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
  field

    func : Functor C D
    isWeakEquiv : isWeakEquivalence func


open isWeakEquivalence
open WeakEquivalence


isEquiv→isWeakEquiv : isEquivalence F → isWeakEquivalence F
isEquiv→isWeakEquiv isequiv .fullfaith = isEquiv→FullyFaithful isequiv
isEquiv→isWeakEquiv isequiv .esssurj   = isEquiv→Surj isequiv


module _
  (isUnivC : isUnivalent C)
  (isUnivD : isUnivalent D)
  where

  open isUnivalent


  isEquivF-ob : {F : Functor C D} → isWeakEquivalence F → isEquivMap (F .F-ob)
  isEquivF-ob {F = F} is-w-equiv = isEmbedding×isSurjection→isEquiv
    (isFullyFaithful→isEmbb-ob isUnivC isUnivD {F = F} (is-w-equiv .fullfaith) ,
     isSurj→isSurj-ob isUnivD {F = F} (is-w-equiv .esssurj))


  isWeakEquiv→isEquiv : isWeakEquivalence F → isEquivalence F
  isWeakEquiv→isEquiv is-w-equiv = {!!}
