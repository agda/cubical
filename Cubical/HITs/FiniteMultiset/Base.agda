{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.FiniteMultiset.Base where

open import Cubical.Core.Everything
open import Cubical.HITs.SetTruncation

private
  variable
    A : Set

infixr 20 _∷_

data FMSet (A : Set) : Set where
  []    : FMSet A
  _∷_   : (x : A) → (xs : FMSet A) → FMSet A
  comm  : ∀ x y xs → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
  trunc : isSet (FMSet A)

pattern [_] x = x ∷ []

module FMSetElim {ℓ} {B : FMSet A → Set ℓ}
  ([]* : B []) (_∷*_ : (x : A) {xs : FMSet A} → B xs → B (x ∷ xs))
  (comm* : (x y : A) {xs : FMSet A} (b : B xs)
         → PathP (λ i → B (comm x y xs i)) (x ∷* (y ∷* b)) (y ∷* (x ∷* b)))
  (trunc* : (xs : FMSet A) → isSet (B xs)) where

  f : (xs : FMSet A) → B xs
  f [] = []*
  f (x ∷ xs) = x ∷* f xs
  f (comm x y xs i) = comm* x y (f xs) i
  f (trunc xs zs p q i j) =
    elimSquash₀ trunc* (trunc xs zs p q) (f xs) (f zs) (cong f p) (cong f q) i j

module FMSetElimProp {ℓ} {B : FMSet A → Set ℓ} (BProp : {xs : FMSet A} → isProp (B xs))
  ([]* : B []) (_∷*_ : (x : A) {xs : FMSet A} → B xs → B (x ∷ xs)) where

  f : (xs : FMSet A) → B xs
  f = FMSetElim.f []* _∷*_
        (λ x y {xs} b →
          toPathP (BProp (transp (λ i → B (comm x y xs i)) i0 (x ∷* (y ∷* b))) (y ∷* (x ∷* b))))
        (λ xs → isProp→isSet BProp)

module FMSetRec {ℓ} {B : Set ℓ} (BSet : isSet B)
  ([]* : B) (_∷*_ : A → B → B)
  (comm* : (x y : A) (b : B) → x ∷* (y ∷* b) ≡ y ∷* (x ∷* b)) where

  f : FMSet A → B
  f = FMSetElim.f []* (λ x b → x ∷* b) (λ x y b → comm* x y b) (λ _ → BSet)
