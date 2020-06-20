{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.Group.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)

open import Cubical.Data.Sigma

open import Cubical.Structures.Macro
open import Cubical.Structures.NAryOp
open import Cubical.Structures.Pointed
open import Cubical.Structures.Semigroup hiding (⟨_⟩)
open import Cubical.Structures.Monoid hiding (⟨_⟩)

open Iso

private
  variable
    ℓ ℓ' : Level

record IsGroup {G : Type ℓ}
               (0g : G) (_+_ : G → G → G) (-_ : G → G) : Type ℓ where

  constructor isgroup

  field
    isMonoid  : IsMonoid 0g _+_
    inverse   : (x : G) → (x + (- x) ≡ 0g) × ((- x) + x ≡ 0g)

  open IsMonoid isMonoid public

  infixl 6 _-_

  _-_ : G → G → G
  x - y = x + (- y)

  invl : (x : G) → (- x) + x ≡ 0g
  invl x = inverse x .snd

  invr : (x : G) → x + (- x) ≡ 0g
  invr x = inverse x .fst

  -- uniqueness of inverse?

record Group : Type (ℓ-suc ℓ) where

  constructor group

  field
    Carrier : Type ℓ
    0g      : Carrier
    _+_     : Carrier → Carrier → Carrier
    -_      : Carrier → Carrier
    isGroup : IsGroup 0g _+_ -_

  infix  8 -_
  infixl 7 _+_

  open IsGroup isGroup public

-- Extractor for the carrier type
⟨_⟩ : Group → Type ℓ
⟨_⟩ = Group.Carrier

-- TODO: we don't need all of these arguments...
makeIsGroup : {G : Type ℓ} {0g : G} {_+_ : G → G → G} { -_ : G → G}
              (is-setG : isSet G)
              (assoc : (x y z : G) → x + (y + z) ≡ (x + y) + z)
              (rid : (x : G) → x + 0g ≡ x)
              (lid : (x : G) → 0g + x ≡ x)
              (rinv : (x : G) → x + (- x) ≡ 0g)
              (linv : (x : G) → (- x) + x ≡ 0g)
            → IsGroup 0g _+_ -_
makeIsGroup is-setG assoc rid lid rinv linv =
   isgroup (makeIsMonoid is-setG assoc rid lid) λ x → rinv x , linv x

makeGroup : {G : Type ℓ} (0g : G) (_+_ : G → G → G) (-_ : G → G)
            (is-setG : isSet G)
            (assoc : (x y z : G) → x + (y + z) ≡ (x + y) + z)
            (rid : (x : G) → x + 0g ≡ x)
            (lid : (x : G) → 0g + x ≡ x)
            (rinv : (x : G) → x + (- x) ≡ 0g)
            (linv : (x : G) → (- x) + x ≡ 0g)
          → Group
makeGroup 0g _+_ -_ is-setG assoc rid lid rinv linv =
  group _ 0g _+_ -_ (makeIsGroup is-setG assoc rid lid rinv linv)

isPropIsGroup : {G : Type ℓ} (0g : G) (_+_ : G → G → G) (-_ : G → G)
              → isProp (IsGroup 0g _+_ -_)
isPropIsGroup 0g _+_ -_ (isgroup GM Ginv) (isgroup HM Hinv) =
  λ i → isgroup (isPropIsMonoid _ _ GM HM i) (isPropInv Ginv Hinv i)
  where
  isSetG : isSet _
  isSetG = IsSemigroup.is-set (IsMonoid.isSemigroup GM)

  isPropInv : isProp ((x : _) → ((x + (- x)) ≡ 0g) × (((- x) + x) ≡ 0g))
  isPropInv = isPropΠ λ _ → isProp× (isSetG _ _) (isSetG _ _)
