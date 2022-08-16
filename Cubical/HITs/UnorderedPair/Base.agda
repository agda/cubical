{-# OPTIONS --safe #-}
module Cubical.HITs.UnorderedPair.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

private variable
  ℓ ℓ′ : Level
  A : Type ℓ

infixr 4 _,_

data UnorderedPair (A : Type ℓ) : Type ℓ where
  _,_ : (x y : A) → UnorderedPair A
  swap : (x y : A) → (x , y) ≡ (y , x)
  trunc : isSet (UnorderedPair A)

module _ {B : UnorderedPair A → Type ℓ′}
  (_,*_ : (x y : A) → B (x , y))
  (swap* : (x y : A) → PathP (λ i → B (swap x y i)) (x ,* y) (y ,* x))
  (trunc* : (xs : UnorderedPair A) → isSet (B xs)) where

  elim : (xs : UnorderedPair A) → B xs
  elim (x , y) = x ,* y
  elim (swap x y i) = swap* x y i
  elim (trunc x y p q i j) =
    isOfHLevel→isOfHLevelDep 2 trunc* (elim x) (elim y) (cong elim p) (cong elim q) (trunc x y p q) i j

module _ {B : UnorderedPair A → Type ℓ′}
  (BProp : {xs : UnorderedPair A} → isProp (B xs))
  (_,*_ : (x y : A) → B (x , y)) where

  elimProp : (xs : UnorderedPair A) → B xs
  elimProp = elim _,*_ (λ x y → toPathP (BProp (transport (λ i → B (swap x y i)) (x ,* y)) (y ,* x)))
    λ _ → isProp→isSet BProp

module _ {B : Type ℓ′} (BType : isSet B)
  (_,*_ : (x y : A) → B) (swap* : (x y : A) → (x ,* y) ≡ (y ,* x)) where

  rec : UnorderedPair A → B
  rec = elim _,*_ swap* λ _ → BType
