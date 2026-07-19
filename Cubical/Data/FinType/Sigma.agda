{-

This file contains:
- Rijke finiteness is closed under forming Σ-type.

-}

module Cubical.Data.FinType.Sigma where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.HITs.SetTruncation as Set
open import Cubical.HITs.SetTruncation.Fibers

open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.DecidablePredicate
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.FinSet.Quotients
open import Cubical.Data.FinType

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidablePropositions
  hiding (DecProp) renaming (DecProp' to DecProp)

private
  variable
    ℓ ℓ' : Level

module _
  (X : Type ℓ )
  (Y : Type ℓ') (h : isFinType 1 Y)
  (f : X → Y)
  (q : (y : Y) → isFinType 0 (fiber f y)) where

  private
    ∥f∥₂ : ∥ X ∥₂ → ∥ Y ∥₂
    ∥f∥₂ = Set.map f

  module _ (y : Y) where

    isDecPropFiberRel : (x x' : ∥ fiber f y ∥₂) → isDecProp (fiberRel f y x x')
    isDecPropFiberRel x x' =
      isDecPropRespectEquiv (fiberRel1≃2 f y x x')
        (isDecProp∃ (_ , h .snd y y) (λ _ → _ , isDecProp≡ (_ , q y) _ _))

    isFinSetFiber∥∥₂' : isFinSet (fiber ∥f∥₂ ∣ y ∣₂)
    isFinSetFiber∥∥₂' =
      EquivPresIsFinSet (∥fiber∥₂/R≃fiber∥∥₂ f y)
        (isFinSetQuot (_ , q y) (fiberRel f y) (isEquivRelFiberRel f y) isDecPropFiberRel)

  isFinSetFiber∥∥₂ : (y : ∥ Y ∥₂) → isFinSet (fiber ∥f∥₂ y)
  isFinSetFiber∥∥₂ = Set.elim (λ _ → isProp→isSet isPropIsFinSet) isFinSetFiber∥∥₂'

  isFinType0Total : isFinType 0 X
  isFinType0Total = isFinSetTotal ∥ X ∥₂ (∥ Y ∥₂ , h .fst) ∥f∥₂ isFinSetFiber∥∥₂

module _
  (X : FinType ℓ 1)
  (Y : X .fst → FinType ℓ' 0) where

  isFinType0Σ : isFinType 0 (Σ (X .fst) (λ x → Y x .fst))
  isFinType0Σ =
    isFinType0Total (Σ (X .fst) (λ x → Y x .fst)) (X .fst) (X .snd) fst
      (λ x → EquivPresIsFinType 0 (fiberProjEquiv _ _ x) (Y x .snd))

-- the main result

isFinTypeΣ : {n : ℕ}
  (X : FinType ℓ (1 + n))
  (Y : X .fst → FinType ℓ' n)
  → isFinType n (Σ (X .fst) (λ x → Y x .fst))
isFinTypeΣ {n = 0} = isFinType0Σ
isFinTypeΣ {n = suc n} X Y .fst =
  isFinType0Σ (_ , isFinTypeSuc→isFinType1 {n = suc n} (X .snd))
    (λ x → _ , isFinType→isFinType0 {n = suc n} (Y x .snd))
isFinTypeΣ {n = suc n} X Y .snd a b =
  EquivPresIsFinType n (ΣPathTransport≃PathΣ a b)
    (isFinTypeΣ {n = n} (_ , X .snd .snd _ _) (λ _ → _ , Y _ .snd .snd _ _))
