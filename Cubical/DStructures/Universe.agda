{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Universe where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma

open import Cubical.DStructures.Base
open import Cubical.DStructures.Properties

private
  variable
    ℓ ℓ' ℓ'' ℓ₁ ℓ₁' ℓ₁'' ℓ₂ ℓA ℓ≅A ℓB ℓ≅B ℓ≅ᴰ : Level

-- Universes and equivalences form a URGStr
UGRStrUniverse : URGStr (Type ℓ) ℓ
UGRStrUniverse
  = makeURGStr {_≅_ = _≃_}
               idEquiv
               λ A → isOfHLevelRespectEquiv 0
                                            (Σ-cong-equiv-snd (λ A' → isoToEquiv (iso invEquiv
                                                                                      invEquiv
                                                                                      (λ e → equivEq (invEquiv (invEquiv e)) e (funExt (λ x → refl)))
                                                                                      λ e → equivEq (invEquiv (invEquiv e)) e (funExt (λ x → refl)))))
                                            (EquivContr A)
