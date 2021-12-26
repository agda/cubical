{-# OPTIONS --safe #-}
module Cubical.Categories.Limits.Initial where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation.Base

open import Cubical.Data.Sigma

open import Cubical.Categories.Category

private
  variable
    ℓ ℓ' : Level

module _ (C : Category ℓ ℓ') where
  open Category C

  isInitial : (x : ob) → Type (ℓ-max ℓ ℓ')
  isInitial x = ∀ (y : ob) → isContr (C [ x , y ])

  Initial : Type (ℓ-max ℓ ℓ')
  Initial = Σ[ x ∈ ob ] isInitial x

  initialOb : Initial → ob
  initialOb = fst

  initialArrow : (T : Initial) (y : ob) → C [ initialOb T , y ]
  initialArrow T y = T .snd y .fst

  initialArrowUnique : {T : Initial} {y : ob} (f : C [ initialOb T , y ])
                      → initialArrow T y ≡ f
  initialArrowUnique {T} {y} f = T .snd y .snd f

  initialEndoIsId : (T : Initial) (f : C [ initialOb T , initialOb T ])
                   → f ≡ id
  initialEndoIsId T f = isContr→isProp (T .snd (initialOb T)) f id

  hasInitial : Type (ℓ-max ℓ ℓ')
  hasInitial = ∥ Initial ∥

  -- Initiality of an object is a proposition.
  isPropIsInitial : (x : ob) → isProp (isInitial x)
  isPropIsInitial _ = isPropΠ λ _ → isPropIsContr

  open CatIso

  -- Objects that are initial are isomorphic.
  initialToIso : (x y : Initial) → CatIso C (initialOb x) (initialOb y)
  mor (initialToIso x y) = initialArrow x (initialOb y)
  inv (initialToIso x y) = initialArrow y (initialOb x)
  sec (initialToIso x y) = initialEndoIsId y _
  ret (initialToIso x y) = initialEndoIsId x _

  open isUnivalent

  -- The type of initial objects of a univalent category is a proposition,
  -- i.e. all initial objects are equal.
  isPropInitial : (hC : isUnivalent C) → isProp Initial
  isPropInitial hC x y =
    Σ≡Prop isPropIsInitial (CatIsoToPath hC (initialToIso x y))
