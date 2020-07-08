-- Displayed SIP
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.DispSIP where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path
open import Cubical.Foundations.SIP
open import Cubical.Data.Sigma

open import Cubical.Relation.Binary
open BinaryRelation

private
  variable
    ℓ ℓ' ℓ₁ ℓ₁' ℓ₂ : Level

-- a univalent reflexive graph structure on a type
record URGStr (A : Type ℓ) (ℓ₁ : Level) : Type (ℓ-max ℓ (ℓ-suc ℓ₁)) where
  constructor urgstr
  field
    _≅_ : Rel A A ℓ₁
    ρ : isRefl _≅_
    uni : isUnivalent _≅_ ρ

makeURGStr : {A : Type ℓ} {ℓ₁ : Level} {_≅_ : Rel A A ℓ₁} (ρ : isRefl _≅_) (contrTotal : contrTotalSpace _≅_) → URGStr A ℓ₁
makeURGStr {A = A} {ℓ₁ = ℓ₁} {_≅_ = _≅_} ρ contrTotal = urgstr _≅_ ρ {!!}

-- a displayed univalent reflexive graph structure over a URGStr on a type
record URGStrᴰ {A : Type ℓ} {ℓ₁} (StrA : URGStr A ℓ₁)
                  (B : A → Type ℓ') (ℓ₁' : Level) : Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓ₁) (ℓ-suc ℓ₁')) where
  open URGStr StrA

  field
    _≅ᴰ⟨_⟩_ : {a a' : A} → B a → a ≅ a' → B a' → Type ℓ₁'
    ρᴰ : {a : A} → isRefl _≅ᴰ⟨ ρ a ⟩_
    uniᴰ : {a : A} → isUnivalent _≅ᴰ⟨ ρ a ⟩_ ρᴰ

URGStrᴰ→URGStr : {A : Type ℓ} {ℓ₁ : Level} (StrA : URGStr A ℓ₁)
                 (B : A → Type ℓ') {ℓ₁' : Level} (DispStrB : URGStrᴰ StrA B ℓ₁')
                 → URGStr (Σ A B) (ℓ-max ℓ₁ ℓ₁')
URGStr._≅_ (URGStrᴰ→URGStr StrA B DispStrB) (a , b) (a' , b') = Σ (URGStr._≅_ StrA a a') λ e → URGStrᴰ._≅ᴰ⟨_⟩_ DispStrB b e b'
URGStr.ρ (URGStrᴰ→URGStr StrA B DispStrB) (a , b) = URGStr.ρ StrA a , URGStrᴰ.ρᴰ DispStrB b
URGStr.uni (URGStrᴰ→URGStr StrA B DispStrB) = {!!}

{- Stuff to do:
 * make the above more readable and fill hole
 * a family of props has a canonical URGStrᴰ with DRel = Unit
 * get URGStr from univalent 1- or bi-category
 * URGStr on Type with Equiv
 *
-}
