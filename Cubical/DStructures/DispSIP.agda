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

private
  variable
    ℓ ℓ' ℓ₁ ℓ₁' ℓ₂ : Level

module _ {A : Type ℓ} where
  Rel→TotalSpace : (_≅_ : A → A → Type ℓ') (a : A) → Type (ℓ-max ℓ ℓ')
  Rel→TotalSpace _≅_ a = Σ[ a' ∈ A ] (a ≅ a')

  -- reflexive relations will be denoted by ≅
  relIsReflexive : (_≅_ : A → A → Type ℓ') → Type (ℓ-max ℓ ℓ')
  relIsReflexive _≅_ = (a : A) → a ≅ a

  module _ {_≅_ : A → A → Type ℓ'} where
    ≡→≅ : (ρ : relIsReflexive _≅_) → (a a' : A) → a ≡ a' → a ≅ a'
    ≡→≅ ρ a a' p = subst (λ z → a ≅ z) p (ρ a)

    relIsUnivalent : (ρ : relIsReflexive _≅_) → Type (ℓ-max ℓ ℓ')
    relIsUnivalent ρ = (a a' : A) → isEquiv (≡→≅ ρ a a')


  -- ≅→ContrTotalSpace→Identity :



-- a univalent reflexive graph structure on a type
record URGStr (A : Type ℓ) (ℓ₁ : Level) : Type (ℓ-max ℓ (ℓ-suc ℓ₁)) where
  field
    _≅_ : A → A → Type ℓ₁
    -- ρ    : (a : A) → a ≅ a
    ρ    : relIsReflexive _≅_

  -- ≡→≅ : (a a' : A) → a ≡ a' → a ≅ a'
  -- ≡→≅ a a' p = subst (λ z → a ≅ z) p (ρ a)

  field
    uni : (a a' : A) → isEquiv (≡→≅ ρ a a')



-- makeURGStr : {A : Type ℓ} {ℓ₁ : Level}

-- a displayed univalent reflexive graph structure over a URGStr on a type
record URGStrᴰ {A : Type ℓ} {ℓ₁} (StrA : URGStr A ℓ₁)
                  (B : A → Type ℓ') (ℓ₁' : Level) : Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓ₁) (ℓ-suc ℓ₁')) where
  open URGStr StrA
  field
    -- DRel : {a a' : A} → a ≅ a' → B a → B a' → Type ℓ₁'
    _≅ᴰ⟨_⟩_ : {a a' : A} → B a → a ≅ a' → B a' → Type ℓ₁'
    -- Dρ   : {a : A} → (b : B a) → DRel (ρ a) b b
    ρᴰ : {a : A} → relIsReflexive _≅ᴰ⟨ ρ a ⟩_
    -- ρᴰ : {a : A} → (b : B a) → b ≅ᴰ⟨ ρ a ⟩ b

  ≡→≅ᴰ : {a : A} (b b' : B a) → b ≡ b' → b ≅ᴰ⟨ ρ a ⟩ b'
  ≡→≅ᴰ {a} b b' p = subst (λ z → b ≅ᴰ⟨ ρ a ⟩ z) p (ρᴰ b)

  field
    uniᴰ : {a : A} (b b' : B a) → isEquiv (≡→≅ᴰ b b')

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
