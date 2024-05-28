{-# OPTIONS --safe #-}

open import Cubical.Foundations.Prelude

module Cubical.Data.W.W where

data W (S : Type) (P : S → Type) : Type where
  sup-W : (s : S) → (P s → W S P) → W S P

WInd : (S : Type) (P : S → Type) (M : W S P → Type) →
        (e : {s : S} {f : P s → W S P} → ((p : P s) → M (f p)) → M (sup-W s f)) →
        (w : W S P) → M w
WInd S P M e (sup-W s f) = e {s} {f} (λ p → WInd S P M e (f p))
