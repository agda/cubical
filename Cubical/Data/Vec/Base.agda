{- Definition of vectors. Inspired by the Agda Standard Library -}

module Cubical.Data.Vec.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
open import Cubical.Data.FinData.Base

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    B : Type ℓ'

infixr 5 _∷_

data Vec (A : Type ℓ) : ℕ → Type ℓ where
  []  : Vec A zero
  _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)


-- Basic functions

length : ∀ {n} → Vec A n → ℕ
length {n = n} _ = n

head : ∀ {n} → Vec A (1 + n) → A
head (x ∷ xs) = x

tail : ∀ {n} → Vec A (1 + n) → Vec A n
tail (x ∷ xs) = xs

map : ∀ {A : Type ℓ} {B : Type ℓ'} {n} → (A → B) → Vec A n → Vec B n
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

replicate : ∀ {n} {A : Type ℓ} → A → Vec A n
replicate {n = zero}  x = []
replicate {n = suc n} x = x ∷ replicate x

zipWith : ∀ {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {n : ℕ}
        → (A → B → C) → Vec A n → Vec B n → Vec C n
zipWith {n = zero} _∗_ [] [] = []
zipWith {n = suc n} _∗_ (x ∷ xs) (y ∷ ys) = (x ∗ y) ∷ zipWith _∗_ xs ys

foldr : ∀ {n : ℕ} → (A → B → B) → B → Vec A n → B
foldr {n = zero} _∗_ x [] = x
foldr {n = suc n} _∗_ x (y ∷ xs) = y ∗ (foldr _∗_ x xs)

-- Concatenation

infixr 5 _++_

_++_ : ∀ {m n} → Vec A m → Vec A n → Vec A (m + n)
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

concat : ∀ {m n} → Vec (Vec A m) n → Vec A (n · m)
concat []         = []
concat (xs ∷ xss) = xs ++ concat xss

lookup : ∀ {n} {A : Type ℓ} → Fin n → Vec A n → A
lookup zero    (x ∷ xs) = x
lookup (suc i) (x ∷ xs) = lookup i xs

