module Cubical.Data.Prod.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

-- Here we define an inductive version of the product type, see below
-- for its uses.

-- See `Cubical.Data.Sigma` for `_×_` defined as a special case of
-- sigma types, which is the generally preferred one.

-- If × is defined using Σ then transp/hcomp will be compute
-- "negatively", that is, they won't reduce unless we project out the
-- first of second component. This is not always what we want so this
-- implementation is done using a datatype which computes positively.


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


private
  variable
    A    : Type ℓ
    B C  : A → Type ℓ

intro : (∀ a → B a) → (∀ a → C a) → ∀ a → B a × C a
intro f g a = f a , g a

map : {B : Type ℓ} {D : B → Type ℓ'}
   → (∀ a → C a) → (∀ b → D b) → (x : A × B) → C (proj₁ x) × D (proj₂ x)
map f g = intro (f ∘ proj₁) (g ∘ proj₂)


×-η : {A : Type ℓ} {B : Type ℓ'} (x : A × B) → x ≡ ((proj₁ x) , (proj₂ x))
×-η (x , x₁) = refl


-- The product type with one parameter in Typeω

record _×ω_ {a} (A : Type a) (B : Typeω) : Typeω where
  constructor _,_
  field
    fst : A
    snd : B
