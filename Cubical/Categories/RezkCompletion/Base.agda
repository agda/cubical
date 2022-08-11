{-

The Rezk Completion

-}
{-# OPTIONS --safe #-}

module Cubical.Categories.RezkCompletion.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Functor.ComposeProperty
open import Cubical.Categories.Equivalence
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Categories.Instances.Functors

private
  variable
    ℓC ℓC' ℓD ℓD' : Level
    C : Category ℓC ℓC'
    D : Category ℓD ℓD'

-- Rezk Completion of a given category is the initial functor from it towards univalent categories.

-- It's a bit technical to formulate the universal property of Rezk completion,
-- because the universal property is naturally universal polymorphic,
-- and so the predicate is not inside any universe of finite level.

-- The product type with one parameter in Typeω
record _×_ {a} (A : Type a) (B : Typeω) : Typeω where
  constructor _,_
  field
    fst : A
    snd : B

isRezkCompletion : (F : Functor C D) → Typeω
isRezkCompletion {D = D} F =
    isUnivalent D
  × ({ℓ ℓ' : Level}{E : Category ℓ ℓ'} → isUnivalent E → isEquivalence (precomposeF E F))

-- The criterion of being Rezk completion, c.f. HoTT Book Chapter 9.9.

open _×_

makeIsRezkCompletion : {F : Functor C D} → isUnivalent D → isWeakEquivalence F → isRezkCompletion F
makeIsRezkCompletion univ w-equiv .fst = univ
makeIsRezkCompletion univ w-equiv .snd univE = isWeakEquiv→isEquivPrecomp univE _ w-equiv
