{-

Definition and properties of finite types

This file formalize the notion of Rijke finite type,
which is a direct generalization of Bishop finite set.
Basically, a type is (Rijke) n-finite if all its i-th
order homotopy groups πᵢ for i ≤ n are Bishop finite.

https://github.com/EgbertRijke/OEIS-A000001

-}
{-# OPTIONS --safe #-}

module Cubical.Data.FinSet.FinType where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Path

open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.HITs.SetTruncation as Set
open import Cubical.HITs.SetTruncation.Fibers
open import Cubical.HITs.SetQuotients as SetQuot

open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.Data.FinSet.Base
open import Cubical.Data.FinSet.Properties
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.FinSet.Quotients
open import Cubical.Data.FinSet.Cardinality

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary

private
  variable
    ℓ ℓ' : Level
    n : ℕ
    X : Type ℓ
    Y : Type ℓ'

-- the (Rijke) finite type

isFinType : (n : ℕ) → Type ℓ → Type ℓ
isFinType 0 X = isFinSet ∥ X ∥₂
isFinType (suc n) X = (isFinType 0 X) × ((a b : X) → isFinType n (a ≡ b))

isPropIsFinType : isProp (isFinType n X)
isPropIsFinType {n = 0} = isPropIsFinSet
isPropIsFinType {n = suc n} = isProp× isPropIsFinSet (isPropΠ2 (λ _ _ → isPropIsFinType {n = n}))

-- the type of finite types

FinType : (ℓ : Level)(n : ℕ) → Type (ℓ-suc ℓ)
FinType ℓ n = TypeWithStr ℓ (isFinType n)

-- basic numerical implications

isFinTypeSuc→isFinType : isFinType (suc n) X → isFinType n X
isFinTypeSuc→isFinType {n = 0} p = p .fst
isFinTypeSuc→isFinType {n = suc n} p .fst = p .fst
isFinTypeSuc→isFinType {n = suc n} p .snd a b = isFinTypeSuc→isFinType {n = n} (p .snd a b)

isFinType→isFinType0 : isFinType n X → isFinType 0 X
isFinType→isFinType0 {n = 0} p = p
isFinType→isFinType0 {n = suc n} p = p .fst

isFinTypeSuc→isFinType1 : isFinType (suc n) X → isFinType 1 X
isFinTypeSuc→isFinType1 {n = 0} p = p
isFinTypeSuc→isFinType1 {n = suc n} p .fst = p .fst
isFinTypeSuc→isFinType1 {n = suc n} p .snd a b = isFinType→isFinType0 (p .snd a b)

-- useful properties

EquivPresIsFinType : (n : ℕ) → X ≃ Y → isFinType n X → isFinType n Y
EquivPresIsFinType 0 e = EquivPresIsFinSet (isoToEquiv (setTruncIso (equivToIso e)))
EquivPresIsFinType (suc n) e (p , q) .fst = EquivPresIsFinType 0 e p
EquivPresIsFinType (suc n) e (p , q) .snd a b =
  EquivPresIsFinType n (invEquiv (congEquiv (invEquiv e))) (q _ _)

isFinSet→isFinType : (n : ℕ) → isFinSet X → isFinType n X
isFinSet→isFinType 0 p = EquivPresIsFinSet (invEquiv (setTruncIdempotent≃ (isFinSet→isSet p))) p
isFinSet→isFinType (suc n) p .fst = isFinSet→isFinType 0 p
isFinSet→isFinType (suc n) p .snd a b = isFinSet→isFinType n (isFinSet≡ (_ , p) _ _)

isPathConnected→isFinType0 : isContr ∥ X ∥₂ → isFinType 0 X
isPathConnected→isFinType0 p = isContr→isFinSet p

{- finite types are closed under forming Σ-types -}

module _
  (X : Type ℓ )
  (Y : Type ℓ')(h : isFinType 1 Y)
  (f : X → Y)
  (q : (y : Y) → isFinType 0 (fiber f y)) where

  ∥f∥₂ : ∥ X ∥₂ → ∥ Y ∥₂
  ∥f∥₂ = Set.map f

  module _
    (y : Y) where

    isDecFiberRel : (x x' : ∥ fiber f y ∥₂) → Dec (fiberRel2 _ _ f y x x')
    isDecFiberRel x x' =
      isFinSet→Dec∥∥ (isFinSetΣ (_ , h .snd y y) (λ _ → _ , isFinSet≡ (_ , q y) _ _))

    isFinSetFiber∥∥₂' : isFinSet (fiber ∥f∥₂ ∣ y ∣₂)
    isFinSetFiber∥∥₂' =
      EquivPresIsFinSet (∥fiber∥₂/Rel≃fiber∥∥₂ _ _ f y)
        (isFinSetQuot (_ , q y) (fiberRel2 _ _ _ _) (isEquivRelFiberRel _ _ _ _) isDecFiberRel)

  isFinSetFiber∥∥₂ : (y : ∥ Y ∥₂) → isFinSet (fiber ∥f∥₂ y)
  isFinSetFiber∥∥₂ = Set.elim (λ _ → isProp→isSet isPropIsFinSet) isFinSetFiber∥∥₂'

  isFinType0Total : isFinType 0 X
  isFinType0Total = isFinSetTotal _ (_ , h .fst) ∥f∥₂ isFinSetFiber∥∥₂

module _
  (X : FinType ℓ 1)
  (Y : X .fst → FinType ℓ' 0) where

  isFinType0Σ : isFinType 0 (Σ (X .fst) (λ x → Y x .fst))
  isFinType0Σ =
    isFinType0Total (Σ (X .fst) (λ x → Y x .fst)) (X .fst) (X .snd)
      (λ (x , y) → x) (λ x → EquivPresIsFinType 0 (fiberProjEquiv _ _ x) (Y x .snd))

-- the closedness result

isFinTypeΣ :
  {n : ℕ}
  (X : FinType ℓ (1 + n))
  (Y : X .fst → FinType ℓ' n)
  → isFinType n (Σ (X .fst) (λ x → Y x .fst))
isFinTypeΣ {n = 0} = isFinType0Σ
isFinTypeΣ {n = suc n} X Y .fst =
  isFinType0Σ (_ , isFinTypeSuc→isFinType1 (X .snd)) (λ x → _ , isFinType→isFinType0 (Y x .snd))
isFinTypeΣ {n = suc n} X Y .snd a b =
  EquivPresIsFinType n (ΣPathTransport≃PathΣ a b)
    (isFinTypeΣ {n = n} (_ , X .snd .snd _ _) (λ _ → _ , Y _ .snd .snd _ _))
