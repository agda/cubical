-- Displayed SIP
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Base where

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

open import Cubical.Relation.Binary
open BinaryRelation

private
  variable
    ℓ ℓ' ℓ'' ℓ₁ ℓ₁' ℓ₁'' ℓ₂ ℓA ℓ≅A ℓB ℓ≅B ℓC ℓ≅C ℓ≅ᴰ : Level

{- Stuff to do:
 * get URGStr from univalent bi-category
 * (Bonus: (A : Type ℓ) → isContr (URGStr A ℓ))
 * functoriality for free for e : (a : A) → B a → B' a
 * standard notion of structure
 * associativity of URGStr towers


  Next steps:
  - URGStr on Groups
  - Two arms going up:
  -+ 1. SectRetr over G, RGGp over that, Peiffer over that, Str2Gp over/equiv to that
  -+ 2. GpAction over G, PreXMod over that, XMod over that

-}
-- a univalent reflexive graph structure on a type
record URGStr (A : Type ℓA) (ℓ≅A : Level) : Type (ℓ-max ℓA (ℓ-suc ℓ≅A)) where
  constructor urgstr
  field
    _≅_ : Rel A A ℓ≅A
    ρ : isRefl _≅_
    uni : isUnivalent _≅_ ρ

-- wrapper to create instances of URGStr
makeURGStr : {A : Type ℓA} {_≅_ : Rel A A ℓ≅A}
             (ρ : isRefl _≅_) (contrTotal : contrTotalSpace _≅_)
             → URGStr A ℓ≅A
makeURGStr {A = A} {_≅_ = _≅_}
           ρ contrTotal
           = urgstr _≅_
                    ρ
                    λ a a' → contrTotalSpace→isUnivalent _≅_ ρ contrTotal a a'


-- a displayed univalent reflexive graph structure over a URGStr on a type
record URGStrᴰ {A : Type ℓA} (StrA : URGStr A ℓ≅A)
                  (B : A → Type ℓB) (ℓ≅ᴰ : Level) : Type (ℓ-max (ℓ-max (ℓ-max ℓA ℓB) ℓ≅A) (ℓ-suc ℓ≅ᴰ)) where
  constructor urgstrᴰ
  open URGStr StrA

  field
    _≅ᴰ⟨_⟩_ : {a a' : A} → B a → a ≅ a' → B a' → Type ℓ≅ᴰ
    ρᴰ : {a : A} → isRefl _≅ᴰ⟨ ρ a ⟩_
    uniᴰ : {a : A} → isUnivalent _≅ᴰ⟨ ρ a ⟩_ ρᴰ

-- wrapper to create instances of URGStrᴰ
module _ {A : Type ℓ} {StrA : URGStr A ℓ₁}
         (B : A → Type ℓ') (ℓ₁' : Level)
         where
           open URGStr StrA

           makeURGStrᴰ : {B : A → Type ℓ'} {ℓ₁' : Level}
                         (_≅ᴰ⟨_⟩_ : {a a' : A} → B a → a ≅ a' → B a' → Type ℓ₁')
                         (ρᴰ : {a : A} → isRefl _≅ᴰ⟨ ρ a ⟩_)
                         (contrTotal : (a : A) → contrTotalSpace _≅ᴰ⟨ ρ a ⟩_)
                         → URGStrᴰ StrA B ℓ₁'
           makeURGStrᴰ _≅ᴰ⟨_⟩_ ρᴰ contrTotal
             = urgstrᴰ _≅ᴰ⟨_⟩_
                       ρᴰ
                       λ {a : A} b b' → contrTotalSpace→isUnivalent (_≅ᴰ⟨ ρ a ⟩_)
                                                                    (ρᴰ {a})
                                                                    (contrTotal a)
                                                                    b b'

-- abbreviation to obtain contractibility of total space
URGStr→cTS : {A : Type ℓA} (StrA : URGStr A ℓ≅A) → contrTotalSpace (URGStr._≅_ StrA)
URGStr→cTS StrA = isUnivalent→contrTotalSpace _≅_ ρ uni
  where open URGStr StrA
