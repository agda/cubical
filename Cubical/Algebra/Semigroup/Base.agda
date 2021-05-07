{-# OPTIONS --safe #-}
module Cubical.Algebra.Semigroup.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.StrictEquiv

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open Iso


private
  variable
    ℓ : Level

-- Semigroups as a record, inspired by the Agda standard library:
--
--  https://github.com/agda/agda-stdlib/blob/master/src/Algebra/Bundles.agda#L48
--  https://github.com/agda/agda-stdlib/blob/master/src/Algebra/Structures.agda#L50
--
-- Note that as we are using Path for all equations the IsMagma record
-- would only contain isSet A if we had it.
record IsSemigroup {A : Type ℓ} (_·_ : A → A → A) : Type ℓ where
  no-eta-equality
  constructor issemigroup

  field
    is-set : isSet A
    assoc  : (x y z : A) → x · (y · z) ≡ (x · y) · z

unquoteDecl IsSemigroupIsoΣ = declareRecordIsoΣ IsSemigroupIsoΣ (quote IsSemigroup)

record SemigroupStr (A : Type ℓ) : Type ℓ where

  constructor semigroupstr

  field
    _·_         : A → A → A
    isSemigroup : IsSemigroup _·_

  infixl 7 _·_

  open IsSemigroup isSemigroup public

Semigroup : ∀ ℓ → Type (ℓ-suc ℓ)
Semigroup ℓ = TypeWithStr ℓ SemigroupStr

semigroup : (A : Type ℓ) (_·_ : A → A → A) (h : IsSemigroup _·_) → Semigroup ℓ
semigroup A _·_ h = A , semigroupstr _·_ h

record IsSemigroupEquiv {A : Type ℓ} {B : Type ℓ}
  (M : SemigroupStr A) (e : A ≃ B) (N : SemigroupStr B)
  : Type ℓ
  where

  -- Shorter qualified names
  private
    module M = SemigroupStr M
    module N = SemigroupStr N

  field
    isHom : (x y : A) → equivFun e (x M.· y) ≡ equivFun e x N.· equivFun e y

open SemigroupStr
open IsSemigroup
open IsSemigroupEquiv

SemigroupEquiv : (M N : Semigroup ℓ) → Type ℓ
SemigroupEquiv M N = Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] IsSemigroupEquiv (M .snd) e (N .snd)

isPropIsSemigroup : {A : Type ℓ} (_·_ : A → A → A) → isProp (IsSemigroup _·_)
isPropIsSemigroup _·_ =
  isOfHLevelRetractFromIso 1 IsSemigroupIsoΣ
    (isPropΣ
      isPropIsSet
      (λ isSetA → isPropΠ3 λ _ _ _ → isSetA _ _))

𝒮ᴰ-Semigroup : DUARel (𝒮-Univ ℓ) SemigroupStr ℓ
𝒮ᴰ-Semigroup =
  𝒮ᴰ-Record (𝒮-Univ _) IsSemigroupEquiv
    (fields:
      data[ _·_ ∣ autoDUARel _ _ ∣ isHom ]
      prop[ isSemigroup ∣ (λ _ _ → isPropIsSemigroup _) ])

SemigroupPath : (M N : Semigroup ℓ) → SemigroupEquiv M N ≃ (M ≡ N)
SemigroupPath = ∫ 𝒮ᴰ-Semigroup .UARel.ua
