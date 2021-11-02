{-# OPTIONS --safe #-}

module Cubical.Categories.Limits.Terminal where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Foundations.HLevels
-- open import Cubical.Categories.Limits.Base
open import Cubical.Categories.Category
open import Cubical.Categories.Functor

private
  variable
    ℓ ℓ' : Level

module _ (C : Precategory ℓ ℓ') where
  open Precategory C

  isInitial : (x : ob) → Type (ℓ-max ℓ ℓ')
  isInitial x = ∀ (y : ob) → isContr (C [ x , y ])

  isFinal : (x : ob) → Type (ℓ-max ℓ ℓ')
  isFinal x = ∀ (y : ob) → isContr (C [ y , x ])

  hasInitialOb : Type (ℓ-max ℓ ℓ')
  hasInitialOb = Σ[ x ∈ ob ] isInitial x

  hasFinalOb : Type (ℓ-max ℓ ℓ')
  hasFinalOb = Σ[ x ∈ ob ] isFinal x

  -- Initiality of an object is a proposition.
  isPropIsInitial : (x : ob) → isProp (isInitial x)
  isPropIsInitial x = isPropΠ λ y → isPropIsContr

  -- Objects that are initial are isomorphic.
  isInitialToIso : {x y : ob} (hx : isInitial x) (hy : isInitial y) →
    CatIso {C = C} x y
  isInitialToIso {x = x} {y = y} hx hy =
    let x→y : C [ x , y ]
        x→y = fst (hx y) -- morphism forwards
        y→x : C [ y , x ]
        y→x = fst (hy x) -- morphism backwards
        x→y→x : x→y ⋆⟨ C ⟩ y→x ≡ id x
        x→y→x = isContr→isProp (hx x) _ _ -- compose to id by uniqueness
        y→x→y : y→x ⋆⟨ C ⟩ x→y ≡ id y
        y→x→y = isContr→isProp (hy y) _ _ -- similar.
    in catiso x→y y→x y→x→y x→y→x

  open isUnivalent

  -- The type of initial objects of a univalent precategory is a proposition,
  -- i.e. all initial objects are equal.
  isPropInitial : (hC : isUnivalent C) → isProp (hasInitialOb)
  isPropInitial hC x y =
    -- Being initial is a prop ∴ Suffices equal as objects in C.
    Σ≡Prop (isPropIsInitial)
    -- C is univalent ∴ Suffices isomorphic as objects in C.
    (CatIsoToPath hC (isInitialToIso (snd x) (snd y)))

  -- Now the dual argument for final objects.

  -- Finality of an object is a proposition.
  isPropIsFinal : (x : ob) → isProp (isFinal x)
  isPropIsFinal x = isPropΠ λ y → isPropIsContr

  -- Objects that are initial are isomorphic.
  isFinalToIso : {x y : ob} (hx : isFinal x) (hy : isFinal y) →
    CatIso {C = C} x y
  isFinalToIso {x = x} {y = y} hx hy =
    let x→y : C [ x , y ]
        x→y = fst (hy x) -- morphism forwards
        y→x : C [ y , x ]
        y→x = fst (hx y) -- morphism backwards
        x→y→x : x→y ⋆⟨ C ⟩ y→x ≡ id x
        x→y→x = isContr→isProp (hx x) _ _ -- compose to id by uniqueness
        y→x→y : y→x ⋆⟨ C ⟩ x→y ≡ id y
        y→x→y = isContr→isProp (hy y) _ _ -- similar.
    in catiso x→y y→x y→x→y x→y→x

  -- The type of final objects of a univalent precategory is a proposition,
  -- i.e. all final objects are equal.
  isPropFinal : (hC : isUnivalent C) → isProp (hasFinalOb)
  isPropFinal hC x y =
    -- Being final is a prop ∴ Suffices equal as objects in C.
    Σ≡Prop (isPropIsFinal)
    -- C is univalent ∴ Suffices isomorphic as objects in C.
    (CatIsoToPath hC (isFinalToIso (snd x) (snd y)))
