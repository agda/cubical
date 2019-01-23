{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Interval where

open import Cubical.Core.Primitives
open import Cubical.Core.Prelude

data Interval : Set where
  zero : Interval
  one  : Interval
  seg  : zero ≡ one

funExtInterval : ∀ {ℓ} (A B : Set ℓ) (f g : A → B) → ((x : A) → f x ≡ g x) → f ≡ g
funExtInterval A B f g p = λ i x → hmtpy x (seg i)
  where
  hmtpy : A → Interval → B
  hmtpy x zero    = f x
  hmtpy x one     = g x
  hmtpy x (seg i) = p x i

intervalElim : ∀ {A : Set} (x y : A) (p : x ≡ y) → Interval → A
intervalElim x y p zero    = x
intervalElim x y p one     = y
intervalElim x y p (seg i) = p i

-- Note that this is not definitional (it is not proved by refl)
intervalEta : ∀ {A : Set} (f : Interval → A) → intervalElim (f zero) (f one) (λ i → f (seg i)) ≡ f
intervalEta f i zero    = f zero
intervalEta f i one     = f one
intervalEta f i (seg j) = f (seg j)
