{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.Semigroup where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)

open import Cubical.Data.Sigma

open import Cubical.Structures.Pointed
open import Cubical.Structures.NAryOp

private
  variable
    ℓ ℓ' : Level

-- Semygroup as a record, inspired by the standard library.
-- Note that as we are using ≡ for all equations the IsMagma record would only contain isSet A if we had it.
record IsSemigroup {A : Type ℓ} (_·_ : A → A → A) : Type ℓ where

  field
    is-set : isSet A -- TODO: rename and move to IsMagma?
    assoc  : (x y z : A) → x · (y · z) ≡ (x · y) · z

record Semigroup : Type (ℓ-suc ℓ) where

  -- TODO: add a constructor?

  infixl 7 _·_

  field
    Carrier     : Type ℓ
    _·_         : Carrier → Carrier → Carrier
    isSemigroup : IsSemigroup _·_

  open IsSemigroup isSemigroup public

module semigroup-sip where

  raw-semigroup-structure : Type ℓ → Type ℓ
  raw-semigroup-structure A = A → A → A

  raw-semigroup-is-SNS : SNS {ℓ} raw-semigroup-structure _
  raw-semigroup-is-SNS = binaryFunSNS pointed-iso pointed-is-SNS

  semigroup-axioms : (A : Type ℓ) → raw-semigroup-structure A → Type ℓ
  semigroup-axioms A _·_ = isSet A
                         × ((x y z : A) → x · (y · z) ≡ (x · y) · z)

  semigroup-structure : Type ℓ → Type ℓ
  semigroup-structure = add-to-structure (raw-semigroup-structure) semigroup-axioms

  Semigroup' : Type (ℓ-suc ℓ)
  Semigroup' {ℓ} = TypeWithStr ℓ semigroup-structure

  semigroup-iso : StrIso semigroup-structure ℓ
  semigroup-iso = add-to-iso (binaryFunIso pointed-iso) semigroup-axioms

  semigroup-axioms-isProp : (A : Type ℓ)
                          → (s : raw-semigroup-structure A)
                          → isProp (semigroup-axioms A s)
  semigroup-axioms-isProp A _·_ = isPropΣ isPropIsSet λ isSetA → isPropΠ3 λ _ _ _ → isSetA _ _

  open Iso

  semigroup-axiomsIsoIsSemigroup : (A : Type ℓ) → (s : raw-semigroup-structure A) → Iso (semigroup-axioms A s) (IsSemigroup s)
  fun (semigroup-axiomsIsoIsSemigroup A s) (x , y) = record { is-set = x ; assoc = y }
  inv (semigroup-axiomsIsoIsSemigroup A s) record { is-set = x ; assoc = y } = (x , y)
  rightInv (semigroup-axiomsIsoIsSemigroup A s) _ = refl
  leftInv (semigroup-axiomsIsoIsSemigroup A s) _ = refl

  semigroup-axioms≡IsSemigroup : (A : Type ℓ) → (s : raw-semigroup-structure A) → semigroup-axioms A s ≡ IsSemigroup s
  semigroup-axioms≡IsSemigroup A s = isoToPath (semigroup-axiomsIsoIsSemigroup A s)

  isPropIsSemiGroup : {A : Type ℓ} (_·_ : A → A → A) → isProp (IsSemigroup _·_)
  isPropIsSemiGroup {A = A} s = subst isProp (semigroup-axioms≡IsSemigroup A s) (semigroup-axioms-isProp _ s)

  Semigroup→Semigroup' : Semigroup {ℓ} → Semigroup'
  Semigroup→Semigroup' x = Semigroup.Carrier x , Semigroup._·_ x , semigroup-axiomsIsoIsSemigroup _ _ .inv (Semigroup.isSemigroup x)

  Semigroup'→Semigroup : Semigroup' {ℓ} → Semigroup
  Semigroup'→Semigroup x = record { Carrier = x .fst
                                  ; _·_ = x .snd .fst
                                  ; isSemigroup = semigroup-axiomsIsoIsSemigroup _ _ .fun (x .snd .snd)}

  SemigroupIsoSemigroup' : Iso (Semigroup {ℓ}) Semigroup'
  SemigroupIsoSemigroup' = iso Semigroup→Semigroup' Semigroup'→Semigroup (λ _ → refl) (λ _ → refl)

  Semigroup≡Semigroup' : Semigroup {ℓ} ≡ Semigroup'
  Semigroup≡Semigroup' = isoToPath SemigroupIsoSemigroup'

  semigroup-is-SNS : SNS {ℓ} semigroup-structure semigroup-iso
  semigroup-is-SNS = add-axioms-SNS _ semigroup-axioms-isProp raw-semigroup-is-SNS

  SemigroupPath' : (M N : Semigroup' {ℓ}) → (M ≃[ semigroup-iso ] N) ≃ (M ≡ N)
  SemigroupPath' = SIP semigroup-is-SNS

  SemigroupIso : (M N : Semigroup {ℓ}) → Type ℓ
  SemigroupIso M N = Semigroup→Semigroup' M ≃[ semigroup-iso ] Semigroup→Semigroup' N

  SemigroupPath : (M N : Semigroup {ℓ}) → (SemigroupIso M N) ≃ (M ≡ N)
  SemigroupPath M N = compEquiv (SemigroupPath' (Semigroup→Semigroup' M) (Semigroup→Semigroup' N))
                                (isoToEquiv (invIso (congIso SemigroupIsoSemigroup')))


-- TODO: define a more natural version of SemigroupIso and prove that it is equal to the SemigroupIso from above






-- TODO: do we need any of the code below now that we have a Record?

-- Operations for extracting components

-- ⟨_⟩ : Semigroup' → Type ℓ
-- ⟨ G , _ ⟩ = G

-- semigroup-operation : (G : Semigroup' {ℓ}) → ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
-- semigroup-operation (_ , f , _) = f

-- module semigroup-operation-syntax where

--   semigroup-operation-syntax : (G : Semigroup' {ℓ}) → ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
--   semigroup-operation-syntax = semigroup-operation

--   infixl 20 semigroup-operation-syntax
--   syntax semigroup-operation-syntax G x y = x ·⟨ G ⟩ y

-- open semigroup-operation-syntax

-- semigroup-isSet : (G : Semigroup' {ℓ}) → isSet ⟨ G ⟩
-- semigroup-isSet (_ , _ , P , _) = P

-- semigroup-assoc : (G : Semigroup' {ℓ})
--                 → (x y z : ⟨ G ⟩) → (x ·⟨ G ⟩ (y ·⟨ G ⟩ z)) ≡ ((x ·⟨ G ⟩ y) ·⟨ G ⟩ z)
-- semigroup-assoc (_ , _ , _ , P) = P

-- -- Semigroup ·syntax

-- module semigroup-·syntax (G : Semigroup' {ℓ}) where

--   infixr 18 _·_

--   _·_ : ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
--   _·_ = semigroup-operation G
