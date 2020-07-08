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

-- a univalent reflexive graph structure on a type
record URGStr (A : Type ℓ) (ℓ₁ : Level) : Type (ℓ-max ℓ (ℓ-suc ℓ₁)) where
  field
    _≅_ : A → A → Type ℓ₁
    ρ    : (a : A) → a ≅ a

  ≡→≅ : (a a' : A) → a ≡ a' → a ≅ a'
  ≡→≅ a a' p = subst (λ z → a ≅ z) p (ρ a)

  field
    uni : (a a' : A) → isEquiv (≡→≅ a a')

record DispURGStr {A : Type ℓ} {ℓ₁} (StrA : URGStr A ℓ₁)
                  (B : A → Type ℓ') (ℓ₁' : Level) : Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓ₁) (ℓ-suc ℓ₁')) where
  open URGStr StrA
  field
    DRel : {a a' : A} → a ≅ a' → B a → B a' → Type ℓ₁'
    Dρ   : {a : A} → (b : B a) → DRel (ρ a) b b

  ≡→DRel : {a : A} (b b' : B a) → b ≡ b' → DRel (ρ a) b b'
  ≡→DRel {a} b b' p = subst (λ z → DRel (ρ a) b z) p (Dρ b)

  field
    Duni : {a : A} (b b' : B a) → isEquiv (≡→DRel b b')

DispURGStr→URGStr : {A : Type ℓ} {ℓ₁ : Level} (StrA : URGStr A ℓ₁)
                    (B : A → Type ℓ') {ℓ₁' : Level} (DispStrB : DispURGStr StrA B ℓ₁')
                    → URGStr (Σ A B) (ℓ-max ℓ₁ ℓ₁')
URGStr._≅_ (DispURGStr→URGStr StrA B DispStrB) (a , b) (a' , b') = Σ (URGStr._≅_ StrA a a') λ e → DispURGStr.DRel DispStrB e b b'
URGStr.ρ (DispURGStr→URGStr StrA B DispStrB) (a , b) = URGStr.ρ StrA a , DispURGStr.Dρ DispStrB b
URGStr.uni (DispURGStr→URGStr StrA B DispStrB) = {!!}

{- Stuff to do:
 * make the above more readable and fill hole
 * a family of props has a canonical DispURGStr with DRel = Unit
 * get URGStr from univalent 1- or bi-category
 * URGStr on Type with Equiv
 * 
-}
