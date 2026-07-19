module Cubical.Data.List.Base where

open import Agda.Builtin.List public

open import Cubical.Foundations.Prelude

open import Cubical.Data.Maybe.Base as Maybe hiding (rec ; elim)
open import Cubical.Data.Nat.Base hiding (elim)

module _ {ℓ} {A : Type ℓ} where

  infixr 5 _++_
  infixl 5 _∷ʳ_

  [_] : A → List A
  [ a ] = a ∷ []

  _++_ : List A → List A → List A
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ xs ++ ys

  rev : List A → List A
  rev [] = []
  rev (x ∷ xs) = rev xs ++ [ x ]

  _∷ʳ_ : List A → A → List A
  xs ∷ʳ x = xs ++ x ∷ []

  length : List A → ℕ
  length [] = 0
  length (x ∷ l) = 1 + length l

  map : ∀ {ℓ'} {B : Type ℓ'} → (A → B) → List A → List B
  map f [] = []
  map f (x ∷ xs) = f x ∷ map f xs

  map2 : ∀ {ℓ' ℓ''} {B : Type ℓ'} {C : Type ℓ''}
    → (A → B → C) → List A → List B → List C
  map2 f [] _ = []
  map2 f _ [] = []
  map2 f (x ∷ xs) (y ∷ ys) = f x y ∷ map2 f xs ys

  filterMap : ∀ {ℓ'} {B : Type ℓ'} → (A → Maybe B) → List A → List B
  filterMap f [] = []
  filterMap f (x ∷ xs) = Maybe.rec (filterMap f xs) (_∷ filterMap f xs) (f x)

  foldr : ∀ {ℓ'} {B : Type ℓ'} → (A → B → B) → B → List A → B
  foldr f b [] = b
  foldr f b (x ∷ xs) = f x (foldr f b xs)

  foldl : ∀ {ℓ'} {B : Type ℓ'} → (B → A → B) → B → List A → B
  foldl f b [] = b
  foldl f b (x ∷ xs) = foldl f (f b x) xs

  drop : ℕ → List A → List A
  drop zero xs = xs
  drop (suc n) [] = []
  drop (suc n) (x ∷ xs) = drop n xs

  take : ℕ → List A → List A
  take zero xs = []
  take (suc n) [] = []
  take (suc n) (x ∷ xs) = x ∷ take n xs

  elim : ∀ {ℓ'} {B : List A → Type ℓ'}
           → B []
           → (∀ {a l} → B l → B (a ∷ l))
           → ∀ l → B l
  elim b _ [] = b
  elim {B = B} b[] b (a ∷ l) = b (elim {B = B} b[] b l )

  rec : ∀ {ℓ'} {B : Type ℓ'}
           → B
           → (A → B → B)
           → List A → B
  rec b _ [] = b
  rec b f (x ∷ xs) = f x (rec b f xs)

ℓ-maxList : List Level → Level
ℓ-maxList [] = ℓ-zero
ℓ-maxList (x ∷ x₁) = ℓ-max x (ℓ-maxList x₁)
