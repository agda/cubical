{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.Equiv.Base where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude

open import Cubical.Core.Glue public
  using ( isEquiv ; equiv-proof ; _≃_ ; equivFun ; equivProof )

-- The identity equivalence
idIsEquiv : ∀ {ℓ} (A : Type ℓ) → isEquiv (idfun A)
equiv-proof (idIsEquiv A) y =
  ((y , refl) , λ z i → z .snd (~ i) , λ j → z .snd (~ i ∨ j))

idEquiv : ∀ {ℓ} (A : Type ℓ) → A ≃ A
idEquiv A .fst = idfun A
idEquiv A .snd = idIsEquiv A
