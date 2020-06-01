{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.FiniteMultiset.Base where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.SetTruncation
open import Cubical.Foundations.HLevels

private
  variable
    ℓ : Level
    A : Type ℓ

infixr 5 _∷_

data FMSet (A : Type ℓ) : Type ℓ where
  []    : FMSet A
  _∷_   : (x : A) → (xs : FMSet A) → FMSet A
  comm  : ∀ x y xs → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
  trunc : isSet (FMSet A)

pattern [_] x = x ∷ []

module Elim {ℓ'} {B : FMSet A → Type ℓ'}
  ([]* : B []) (_∷*_ : (x : A) {xs : FMSet A} → B xs → B (x ∷ xs))
  (comm* : (x y : A) {xs : FMSet A} (b : B xs)
         → PathP (λ i → B (comm x y xs i)) (x ∷* (y ∷* b)) (y ∷* (x ∷* b)))
  (trunc* : (xs : FMSet A) → isSet (B xs)) where

  f : (xs : FMSet A) → B xs
  f [] = []*
  f (x ∷ xs) = x ∷* f xs
  f (comm x y xs i) = comm* x y (f xs) i
  f (trunc xs zs p q i j) =
    isOfHLevel→isOfHLevelDep 2 trunc*  (f xs) (f zs) (cong f p) (cong f q) (trunc xs zs p q) i j

module ElimProp {ℓ'} {B : FMSet A → Type ℓ'} (BProp : {xs : FMSet A} → isProp (B xs))
  ([]* : B []) (_∷*_ : (x : A) {xs : FMSet A} → B xs → B (x ∷ xs)) where

  f : (xs : FMSet A) → B xs
  f = Elim.f []* _∷*_
        (λ x y {xs} b →
          toPathP (BProp (transp (λ i → B (comm x y xs i)) i0 (x ∷* (y ∷* b))) (y ∷* (x ∷* b))))
        (λ xs → isProp→isSet BProp)

module Rec {ℓ'} {B : Type ℓ'} (BType : isSet B)
  ([]* : B) (_∷*_ : A → B → B)
  (comm* : (x y : A) (b : B) → x ∷* (y ∷* b) ≡ y ∷* (x ∷* b)) where

  f : FMSet A → B
  f = Elim.f []* (λ x b → x ∷* b) (λ x y b → comm* x y b) (λ _ → BType)
