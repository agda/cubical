{-

The James Construction,
  also known as James Reduced Product

A very fundamental and useful construction in classical homotopy theory.
It can be seen as the free A∞-monoid constructed out of a given type,
namely the "correct higher version" of free monoid that is meaningful for all types,
instead of only h-Sets.

Referrence:
  Guillaume Brunerie,
  "The James construction and π₄(𝕊³) in homotopy type theory"
  (https://arxiv.org/abs/1710.10307)

-}
module Cubical.HITs.James.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed

private
  variable
    ℓ ℓ' : Level

module _
  ((X , x₀) : Pointed ℓ) where

  infixr 5 _∷_

  -- The James Construction

  data James : Type ℓ where
    []   : James
    _∷_  : X → James → James
    unit : (xs : James) → xs ≡ x₀ ∷ xs

  James∙ : Pointed ℓ
  James∙ = James , []


-- Basic operations on James construction, imitating those in Cubical.Data.List.Base

module _
  {X∙@(X , x₀) : Pointed ℓ} where

  infixr 5 _++_
  infixl 5 _∷ʳ_

  [_] : X → James X∙
  [ x ] = x ∷ []

  _++_ : James X∙ → James X∙ → James X∙
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ xs ++ ys
  (unit xs i) ++ ys = unit (xs ++ ys) i

  ++₀ : (xs : James X∙) → xs ≡ xs ++ [ x₀ ]
  ++₀ [] = unit []
  ++₀ (x ∷ xs) i = x ∷ ++₀ xs i
  ++₀ (unit xs i) j = unit (++₀ xs j) i

  rev : James X∙ → James X∙
  rev [] = []
  rev (x ∷ xs) = rev xs ++ [ x ]
  rev (unit xs i) = ++₀ (rev xs) i

  _∷ʳ_ : James X∙ → X → James X∙
  xs ∷ʳ x = xs ++ x ∷ []

map : {X : Pointed ℓ}{Y : Pointed ℓ'} → (X →∙ Y) → James X → James Y
map f [] = []
map f (x ∷ xs) = f .fst x ∷ map f xs
map f (unit xs i) = (unit (map f xs) ∙ (λ i → f .snd (~ i) ∷ map f xs)) i

map∙ : {X : Pointed ℓ}{Y : Pointed ℓ'} → (X →∙ Y) → James∙ X →∙ James∙ Y
map∙ f .fst = map f
map∙ f .snd = refl
