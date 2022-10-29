-- Closed Monoidal Categories
{-# OPTIONS --safe #-}
module Cubical.Categories.Monoidal.Closed where

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functor.BinProduct
open import Cubical.Categories.Morphism
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Symmetric
open import Cubical.Categories.Adjoint

open UnitCounit

module _ {ℓ ℓ' : Level} (C : Category ℓ ℓ') where
  open Category C
  open Functor

  -- the closed structure
  record ClosedStr : Type (ℓ-max ℓ ℓ') where
    field
      [─,─] : Functor (C ^op × C) C

    -- useful internal hom notation
    [_,_] : ob → ob → ob
    [ a , b ] = [─,─] .F-ob (a , b)

    [_,_]ₕ : ∀ {a b c d} → Hom[ c , a ] → Hom[ b , d ] → Hom[ [ a ,  b ] , [ c , d ] ]
    [ f , g ]ₕ = [─,─] .F-hom (f , g)

  record ClosedMonStr : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    field
      closedstr : ClosedStr
      symmmonstr : SymmMonStr C

    open ClosedStr closedstr public
    open SymmMonStr symmmonstr public

    -- private names to make the adjunction look nicer
    private
      _⊗[-] : (b : ob) → Functor C C
      b ⊗[-] = ─⊗─ ∘F rinj C C b

      [_,-] : (b : ob) → Functor C C
      [ b ,-] = [─,─] ∘F rinj (C ^op) C b

    field
      -- the adjunction
      closed : (b : ob) → (b ⊗[-]) ⊣ [ b ,-]

record ClosedMonCategory ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    C : Category ℓ ℓ'
    closedmonstr : ClosedMonStr C

  open Category C public
  open ClosedMonStr closedmonstr public
