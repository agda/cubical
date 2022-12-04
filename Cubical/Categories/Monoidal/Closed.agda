-- Closed Monoidal Categories
{-# OPTIONS --safe #-}
module Cubical.Categories.Monoidal.Closed where

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Monoidal
open import Cubical.Categories.Monoidal.Symmetric
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Adjoint.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Categories.Instances.Functors

open NaturalBijection

-- Closed monoidal categories as defined here:
-- https://ncatlab.org/nlab/show/closed+monoidal+category
module _ {ℓ ℓ' : Level} (C : Category ℓ ℓ') where
  open Category C
  open Iso
  open _⊣_

  record ClosedMonStr : Type (ℓ-max ℓ ℓ') where
    field
      symmmonstr : SymmMonStr C

    open SymmMonStr symmmonstr public

    -- private name to make the adjunction look nicer
    private
      _⊗- : ob → Functor C C
      b ⊗- = ─⊗─ ∘F rinj C C b

    field
      [_,-] : ob → Functor C C
      closed : (b : ob) → (b ⊗-) ⊣ [ b ,-]

    -- Internal Hom Functor
    [─,─] : Functor (C ^op × C) C
    [─,─] = F-Curry .inv (fillsOut-Bifunctor (F-Curry .fun ─⊗─) (λ c → [ c ,-] , closed c))

    eval : ∀ {a b} → C [ a ⊗ ([ a ,-] ⟅ b ⟆) , b ]
    eval {a} = (closed a ♯) id

record ClosedMonCategory ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    C : Category ℓ ℓ'
    closedmonstr : ClosedMonStr C

  open Category C public
  open ClosedMonStr closedmonstr public
