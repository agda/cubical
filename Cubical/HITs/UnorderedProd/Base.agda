{-# OPTIONS --safe #-}
module Cubical.HITs.UnorderedProd.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

private variable
  ℓ ℓ′ : Level
  A : Type ℓ

infixr 4 _,_

data UnorderedProd (A : Type ℓ) : Type ℓ where
  _,_ : (x y : A) → UnorderedProd A
  swap : (x y : A) → (x , y) ≡ (y , x)
  trunc : isSet (UnorderedProd A)

module Elim {B : UnorderedProd A → Type ℓ′}
  (_,*_ : (x y : A) → B (x , y))
  (swap* : (x y : A) → PathP (λ i → B (swap x y i)) (x ,* y) (y ,* x))
  (trunc* : (xs : UnorderedProd A) → isSet (B xs)) where

  f : (xs : UnorderedProd A) → B xs
  f (x , y) = x ,* y
  f (swap x y i) = swap* x y i
  f (trunc x y p q i j) =
    isOfHLevel→isOfHLevelDep 2 trunc* (f x) (f y) (cong f p) (cong f q) (trunc x y p q) i j

module ElimProp {B : UnorderedProd A → Type ℓ′}
  (BProp : {xs : UnorderedProd A} → isProp (B xs))
  (_,*_ : (x y : A) → B (x , y)) where

  f : (xs : UnorderedProd A) → B xs
  f = Elim.f _,*_ (λ x y → toPathP (BProp (transport (λ i → B (swap x y i)) (x ,* y)) (y ,* x)))
    λ _ → isProp→isSet BProp

module Rec {B : Type ℓ′} (BType : isSet B)
  (_,*_ : (x y : A) → B) (swap* : (x y : A) → (x ,* y) ≡ (y ,* x)) where

  f : UnorderedProd A → B
  f = Elim.f _,*_ swap* λ _ → BType
