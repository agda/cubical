{-

Basic properties of James construction

This file contains:

  - The type James X has h-monoid structure, namely being a monoid in "homotopy category".

  - The equivalence "James X₊ ≃ List X" for type X,
    where X₊ denotes the type formed by freely adjoining a base point to X.

-}
module Cubical.HITs.James.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed

open import Cubical.Data.Maybe
open import Cubical.Data.List hiding (_++_)

open import Cubical.HITs.James.Base

private
  variable
    ℓ : Level

-- The h-monoid structure on James X

module _
  (X∙@(X , x₀) : Pointed ℓ) where

  ++lUnit : (xs : James X∙) → xs ≡ [] ++ xs
  ++lUnit _ = refl

  ++rUnit : (xs : James X∙) → xs ≡ xs ++ []
  ++rUnit [] = refl
  ++rUnit (x ∷ xs) t = x ∷ ++rUnit xs t
  ++rUnit (unit xs i) t = unit (++rUnit xs t) i

  ++Assoc :  (xs ys zs : James X∙) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  ++Assoc [] _ _ = refl
  ++Assoc (x ∷ xs) ys zs t = x ∷ ++Assoc xs ys zs t
  ++Assoc (unit xs i) ys zs t = unit (++Assoc xs ys zs t) i


-- Freely adjoining a point

module _
  (X : Type ℓ) where

  private
    X₊ = Maybe∙ X


  J₊→List : James X₊ → List X
  J₊→List [] = []
  J₊→List (just x  ∷ xs) = x ∷ J₊→List xs
  J₊→List (nothing ∷ xs) = J₊→List xs
  J₊→List (unit xs i) = J₊→List xs

  List→J₊ : List X → James X₊
  List→J₊ [] = []
  List→J₊ (x ∷ xs) = just x ∷ List→J₊ xs

  List→J₊→List : (xs : List X) → J₊→List (List→J₊ xs) ≡ xs
  List→J₊→List [] = refl
  List→J₊→List (x ∷ xs) i = x ∷ List→J₊→List xs i

  J₊→List→J₊ : (xs : James X₊) → List→J₊ (J₊→List xs) ≡ xs
  J₊→List→J₊ [] = refl
  J₊→List→J₊ (just x  ∷ xs) i = just x ∷ J₊→List→J₊ xs i
  J₊→List→J₊ (nothing ∷ xs) = J₊→List→J₊ xs ∙ unit xs
  J₊→List→J₊ (unit xs i) j =
    hcomp (λ k → λ
      { (i = i0) → J₊→List→J₊ xs j
      ; (i = i1) → compPath-filler (J₊→List→J₊ xs) (unit xs) k j
      ; (j = i0) → List→J₊ (J₊→List xs)
      ; (j = i1) → unit xs (i ∧ k) })
    (J₊→List→J₊ xs j)

  J₊≃List : James X₊ ≃ List X
  J₊≃List = isoToEquiv (iso J₊→List List→J₊ List→J₊→List J₊→List→J₊)
