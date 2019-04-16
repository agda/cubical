{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Interval.Base where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude

data Interval : Type₀ where
  zero : Interval
  one  : Interval
  seg  : zero ≡ one

isContrInterval : isContr Interval
isContrInterval = (zero , (λ x → rem x))
  where
  rem : (x : Interval) → zero ≡ x
  rem zero      = refl
  rem one       = seg
  rem (seg i) j = seg (i ∧ j)

funExtInterval : ∀ {ℓ} (A B : Type ℓ) (f g : A → B) → ((x : A) → f x ≡ g x) → f ≡ g
funExtInterval A B f g p = λ i x → hmtpy x (seg i)
  where
  hmtpy : A → Interval → B
  hmtpy x zero    = f x
  hmtpy x one     = g x
  hmtpy x (seg i) = p x i

intervalElim : (A : Interval → Type₀) (x : A zero) (y : A one)
               (p : PathP (λ i → A (seg i)) x y) → (x : Interval) → A x
intervalElim A x y p zero    = x
intervalElim A x y p one     = y
intervalElim A x y p (seg i) = p i

-- Note that this is not definitional (it is not proved by refl)
intervalEta : ∀ {A : Type₀} (f : Interval → A) → intervalElim _ (f zero) (f one) (λ i → f (seg i)) ≡ f
intervalEta f i zero    = f zero
intervalEta f i one     = f one
intervalEta f i (seg j) = f (seg j)
