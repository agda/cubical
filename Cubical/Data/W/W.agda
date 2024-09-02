{-# OPTIONS --safe #-}

module Cubical.Data.W.W where

open import Cubical.Foundations.Prelude

private
  variable
    ℓ ℓ' ℓ'' : Level

data W (S : Type ℓ) (P : S → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  sup-W : (s : S) → (P s → W S P) → W S P

WInd : (S : Type ℓ) (P : S → Type ℓ') (M : W S P → Type ℓ'') →
       (e : {s : S} {f : P s → W S P} → ((p : P s) → M (f p)) → M (sup-W s f)) →
       (w : W S P) → M w
WInd S P M e (sup-W s f) = e (λ p → WInd S P M e (f p))
