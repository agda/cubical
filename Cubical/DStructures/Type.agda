
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Type where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path
open import Cubical.Foundations.SIP
open import Cubical.Data.Sigma

open import Cubical.Data.Unit
open import Cubical.DStructures.DispSIP
open import Cubical.Relation.Binary
open BinaryRelation

private
  variable
    ℓ ℓ' ℓ'' ℓ₁ ℓ₁' ℓ₁'' ℓ₂ ℓA ℓ≅A ℓB ℓ≅B ℓ≅ᴰ : Level

-- a type is a URGStr with the relation given by its identity type
URGStrType : (A : Type ℓ) → URGStr A ℓ
URGStrType A = makeURGStr {_≅_ = _≡_} (λ _ → refl) isContrSingl

-- subtypes are displayed structures
URGStrᴰSubtype : {A : Type ℓ} (P : A → hProp ℓ') → URGStrᴰ (URGStrType A) (λ a → P a .fst) ℓ-zero
URGStrᴰSubtype P
  = makeURGStrᴰ (λ a → P a .fst)
                ℓ-zero
                (λ _ _ _ → Unit)
                (λ _ → tt)
                λ a p → isOfHLevelRespectEquiv 0
                                               (invEquiv (Σ-contractSnd (λ _ → isContrUnit)))
                                               (inhProp→isContr p (P a .snd))
