{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.FiniteMultiset.Base where

open import Cubical.Core.Everything
open import Cubical.HITs.TypeTruncation

private
  variable
    A : Type

infixr 20 _∷_

data FMType (A : Type) : Type where
  []    : FMType A
  _∷_   : (x : A) → (xs : FMType A) → FMType A
  comm  : ∀ x y xs → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
  trunc : isType (FMType A)

pattern [_] x = x ∷ []

module FMTypeElim {ℓ} {B : FMType A → Type ℓ}
  ([]* : B []) (_∷*_ : (x : A) {xs : FMType A} → B xs → B (x ∷ xs))
  (comm* : (x y : A) {xs : FMType A} (b : B xs)
         → PathP (λ i → B (comm x y xs i)) (x ∷* (y ∷* b)) (y ∷* (x ∷* b)))
  (trunc* : (xs : FMType A) → isType (B xs)) where

  f : (xs : FMType A) → B xs
  f [] = []*
  f (x ∷ xs) = x ∷* f xs
  f (comm x y xs i) = comm* x y (f xs) i
  f (trunc xs zs p q i j) =
    elimSquash₀ trunc* (trunc xs zs p q) (f xs) (f zs) (cong f p) (cong f q) i j

module FMTypeElimProp {ℓ} {B : FMType A → Type ℓ} (BProp : {xs : FMType A} → isProp (B xs))
  ([]* : B []) (_∷*_ : (x : A) {xs : FMType A} → B xs → B (x ∷ xs)) where

  f : (xs : FMType A) → B xs
  f = FMTypeElim.f []* _∷*_
        (λ x y {xs} b →
          toPathP (BProp (transp (λ i → B (comm x y xs i)) i0 (x ∷* (y ∷* b))) (y ∷* (x ∷* b))))
        (λ xs → isProp→isType BProp)

module FMTypeRec {ℓ} {B : Type ℓ} (BType : isType B)
  ([]* : B) (_∷*_ : A → B → B)
  (comm* : (x y : A) (b : B) → x ∷* (y ∷* b) ≡ y ∷* (x ∷* b)) where

  f : FMType A → B
  f = FMTypeElim.f []* (λ x b → x ∷* b) (λ x y b → comm* x y b) (λ _ → BType)
