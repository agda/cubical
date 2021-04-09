{-# OPTIONS --cubical --no-import-sorts --safe #-}
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

open import Cubical.Reflection.StrictEquiv

open import Cubical.Structures.Axioms
open import Cubical.Structures.Auto
open import Cubical.Structures.Record

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

  constructor issemigroup

  field
    is-set : isSet A
    assoc  : (x y z : A) → x · (y · z) ≡ (x · y) · z

record SemigroupStr (A : Type ℓ) : Type (ℓ-suc ℓ) where

  constructor semigroupstr

  field
    _·_         : A → A → A
    isSemigroup : IsSemigroup _·_

  infixl 7 _·_

  open IsSemigroup isSemigroup public

Semigroup : Type (ℓ-suc ℓ)
Semigroup = TypeWithStr _ SemigroupStr

semigroup : (A : Type ℓ) (_·_ : A → A → A) (h : IsSemigroup _·_) → Semigroup
semigroup A _·_ h = A , semigroupstr _·_ h

record SemigroupEquiv (M N : Semigroup {ℓ}) (e : ⟨ M ⟩ ≃ ⟨ N ⟩) : Type ℓ where

  constructor semigroupequiv

  -- Shorter qualified names
  private
    module M = SemigroupStr (snd M)
    module N = SemigroupStr (snd N)

  field
    isHom : (x y : ⟨ M ⟩) → equivFun e (x M.· y) ≡ equivFun e x N.· equivFun e y

open SemigroupStr
open IsSemigroup
open SemigroupEquiv

-- Develop some theory about Semigroups using various general results
-- that are stated using Σ-types. For this we define Semigroup as a
-- nested Σ-type, prove that it's equivalent to the above record
-- definition and then transport results along this equivalence.
module SemigroupΣTheory {ℓ} where

  RawSemigroupStructure : Type ℓ → Type ℓ
  RawSemigroupStructure X = X → X → X

  RawSemigroupEquivStr = AutoEquivStr RawSemigroupStructure

  rawSemigroupUnivalentStr : UnivalentStr _ RawSemigroupEquivStr
  rawSemigroupUnivalentStr = autoUnivalentStr RawSemigroupStructure

  SemigroupAxioms : (A : Type ℓ) → RawSemigroupStructure A → Type ℓ
  SemigroupAxioms A _·_ = isSet A
                        × ((x y z : A) → x · (y · z) ≡ (x · y) · z)

  SemigroupStructure : Type ℓ → Type ℓ
  SemigroupStructure = AxiomsStructure RawSemigroupStructure SemigroupAxioms

  SemigroupΣ : Type (ℓ-suc ℓ)
  SemigroupΣ = TypeWithStr ℓ SemigroupStructure

  isPropSemigroupAxioms : (A : Type ℓ) (_·_ : RawSemigroupStructure A)
                        → isProp (SemigroupAxioms A _·_)
  isPropSemigroupAxioms _ _ = isPropΣ isPropIsSet λ isSetA → isPropΠ3 λ _ _ _ → isSetA _ _

  SemigroupEquivStr : StrEquiv SemigroupStructure ℓ
  SemigroupEquivStr = AxiomsEquivStr RawSemigroupEquivStr SemigroupAxioms

  SemigroupAxiomsIsoIsSemigroup : {A : Type ℓ} (_·_ : RawSemigroupStructure A)
                                → Iso (SemigroupAxioms A _·_) (IsSemigroup _·_)
  fun (SemigroupAxiomsIsoIsSemigroup s) (x , y)           = issemigroup x y
  inv (SemigroupAxiomsIsoIsSemigroup s) M                 = is-set M , assoc M
  rightInv (SemigroupAxiomsIsoIsSemigroup s) _            = refl
  leftInv (SemigroupAxiomsIsoIsSemigroup s) _             = refl

  SemigroupAxioms≡IsSemigroup : {A : Type ℓ} (_·_ : RawSemigroupStructure A)
                              → SemigroupAxioms _ _·_ ≡ IsSemigroup _·_
  SemigroupAxioms≡IsSemigroup s = isoToPath (SemigroupAxiomsIsoIsSemigroup s)

  Semigroup→SemigroupΣ : Semigroup → SemigroupΣ
  Semigroup→SemigroupΣ (A , semigroupstr _·_ isSemigroup) =
    A , _·_ , SemigroupAxiomsIsoIsSemigroup _ .inv isSemigroup

  SemigroupΣ→Semigroup : SemigroupΣ → Semigroup
  SemigroupΣ→Semigroup (A , _·_ , isSemigroupΣ) =
    semigroup A _·_ (SemigroupAxiomsIsoIsSemigroup _ .fun isSemigroupΣ)

  SemigroupIsoSemigroupΣ : Iso Semigroup SemigroupΣ
  SemigroupIsoSemigroupΣ =
    iso Semigroup→SemigroupΣ SemigroupΣ→Semigroup (λ _ → refl) (λ _ → refl)

  semigroupUnivalentStr : UnivalentStr SemigroupStructure SemigroupEquivStr
  semigroupUnivalentStr = axiomsUnivalentStr _ isPropSemigroupAxioms rawSemigroupUnivalentStr

  SemigroupΣPath : (M N : SemigroupΣ) → (M ≃[ SemigroupEquivStr ] N) ≃ (M ≡ N)
  SemigroupΣPath = SIP semigroupUnivalentStr

  SemigroupEquivΣ : (M N : Semigroup) → Type ℓ
  SemigroupEquivΣ M N = Semigroup→SemigroupΣ M ≃[ SemigroupEquivStr ] Semigroup→SemigroupΣ N

  SemigroupIsoΣPath : {M N : Semigroup} → Iso (Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] SemigroupEquiv M N e) (SemigroupEquivΣ M N)
  fun SemigroupIsoΣPath (e , x) = e , isHom x
  inv SemigroupIsoΣPath (e , h) = e , semigroupequiv h
  rightInv SemigroupIsoΣPath _  = refl
  leftInv SemigroupIsoΣPath _   = refl

  SemigroupPath : (M N : Semigroup) → (Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] SemigroupEquiv M N e) ≃ (M ≡ N)
  SemigroupPath M N =
    Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] SemigroupEquiv M N e ≃⟨ strictIsoToEquiv SemigroupIsoΣPath ⟩
    SemigroupEquivΣ M N ≃⟨ SemigroupΣPath _ _ ⟩
    Semigroup→SemigroupΣ M ≡ Semigroup→SemigroupΣ N ≃⟨ isoToEquiv (invIso (congIso SemigroupIsoSemigroupΣ)) ⟩
    M ≡ N ■

-- We now extract the important results from the above module

isPropIsSemigroup : {A : Type ℓ} (_·_ : A → A → A) → isProp (IsSemigroup _·_)
isPropIsSemigroup _·_ =
  subst isProp (SemigroupΣTheory.SemigroupAxioms≡IsSemigroup _·_)
        (SemigroupΣTheory.isPropSemigroupAxioms _ _·_)

SemigroupPath : (M N : Semigroup {ℓ}) → (Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] SemigroupEquiv M N e) ≃ (M ≡ N)
SemigroupPath {ℓ = ℓ} =
  SIP
    (autoUnivalentRecord
      (autoRecordSpec (SemigroupStr {ℓ}) SemigroupEquiv
        (fields:
          data[ _·_ ∣ isHom ]
          prop[ isSemigroup ∣ (λ _ → isPropIsSemigroup _) ]))
      _ _)
