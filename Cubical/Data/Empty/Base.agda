{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Empty.Base where

open import Cubical.Core.Everything

data ⊥ : Set where

⊥-elim : ∀ {l} {A : Set l} → ⊥ → A
⊥-elim ()

