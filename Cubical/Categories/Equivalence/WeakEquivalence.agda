{-# OPTIONS --safe #-}

module Cubical.Categories.Equivalence.WeakEquivalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
  renaming (isEquiv to isEquivMap)
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
open CatIso
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

    full  : isFull func
    faith : isFaithful func
    surj  : isEssentiallySurj func

record WeakEquivalence (C : Category ℓC ℓC') (D : Category ℓD ℓD')
  : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
  field

    func : Functor C D
    isWeakEquiv : isWeakEquivalence func


open isWeakEquivalence
open WeakEquivalence


isEquiv→isWeakEquiv : isEquivalence F → isWeakEquivalence F
isEquiv→isWeakEquiv isequiv .full  = isEquiv→Full isequiv
isEquiv→isWeakEquiv isequiv .faith = isEquiv→Faithful isequiv
isEquiv→isWeakEquiv isequiv .surj  = isEquiv→Surj isequiv


module _
  {C : Category ℓC ℓC'}(isUnivC : isUnivalent C)
  {D : Category ℓD ℓD'}(isUnivD : isUnivalent D)
  where

  open isUnivalent


  module _ {F : WeakEquivalence C D} where

    isEquivF-ob : isEquivMap (F .func .F-ob)
    isEquivF-ob = {!!}


  isWeakEquiv→isEquiv : isWeakEquivalence F → isEquivalence F
  isWeakEquiv→isEquiv is-w-equiv = {!!}
