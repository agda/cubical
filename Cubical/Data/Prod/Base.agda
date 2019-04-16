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

data _×_ (A : Type ℓ) (B : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  _,_ : A → B → A × B

infixr 5 _×_

proj₁ : {A : Type ℓ} {B : Type ℓ'} → A × B → A
proj₁ (x , _) = x

proj₂ : {A : Type ℓ} {B : Type ℓ'} → A × B → B
proj₂ (_ , x) = x

-- We still export the version using Σ
_×Σ_ : (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
A ×Σ B = Σ A (λ _ → B)

infixr 5 _×Σ_

private
  variable
    A    : Type ℓ
    B C  : A → Type ℓ

intro-× : (∀ a → B a) → (∀ a → C a) → ∀ a → B a × C a
intro-× f g a = f a , g a

map-× : {B : Type ℓ} {D : B → Type ℓ'}
   → (∀ a → C a) → (∀ b → D b) → (x : A × B) → C (proj₁ x) × D (proj₂ x)
map-× f g = intro-× (f ∘ proj₁) (g ∘ proj₂)
