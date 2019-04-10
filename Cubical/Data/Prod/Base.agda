{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Prod.Base where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

-- If × is defined using Σ then transp/hcomp will be compute
-- "negatively", that is, they won't reduce unless we project out the
-- first of second component. This is not always what we want so the
-- default implementation is done using a datatype which computes
-- positively.


private
  variable
    ℓ ℓ' : Level

data _×_ (A : Set ℓ) (B : Set ℓ') : Set (ℓ-max ℓ ℓ') where
  _,_ : A → B → A × B

infixr 5 _×_

proj₁ : {A : Set ℓ} {B : Set ℓ'} → A × B → A
proj₁ (x , _) = x

proj₂ : {A : Set ℓ} {B : Set ℓ'} → A × B → B
proj₂ (_ , x) = x

-- We still export the version using Σ
_×Σ_ : (A : Set ℓ) (B : Set ℓ') → Set (ℓ-max ℓ ℓ')
A ×Σ B = Σ A (λ _ → B)

infixr 5 _×Σ_

private
  variable
    A    : Set ℓ
    B C  : A → Set ℓ

intro-× : (∀ a → B a) → (∀ a → C a) → ∀ a → B a × C a
intro-× f g a = f a , g a

map-× : {B : Set ℓ} {D : B → Set ℓ'}
   → (∀ a → C a) → (∀ b → D b) → (x : A × B) → C (proj₁ x) × D (proj₂ x)
map-× f g = intro-× (f ∘ proj₁) (g ∘ proj₂)
