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

open import Cubical.Structures.Axioms
open import Cubical.Structures.Auto

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

  -- no-eta-equality
  constructor issemigroup
  field
    is-set : isSet A
    assoc  : (x y z : A) → x · (y · z) ≡ (x · y) · z

record Semigroup : Type (ℓ-suc ℓ) where

  constructor semigroup

  field
    Carrier     : Type ℓ
    _·_         : Carrier → Carrier → Carrier
    isSemigroup : IsSemigroup _·_

  infixl 7 _·_

  open IsSemigroup isSemigroup public

-- Extractor for the carrier type
⟨_⟩ : Semigroup → Type ℓ
⟨_⟩ = Semigroup.Carrier


record SemigroupEquiv (M N : Semigroup {ℓ}) : Type ℓ where
  no-eta-equality
  constructor semigroupequiv

  -- Shorter qualified names
  private
    module M = Semigroup M
    module N = Semigroup N

  field
    e     : ⟨ M ⟩ ≃ ⟨ N ⟩
    isHom : (x y : ⟨ M ⟩) → equivFun e (x M.· y) ≡ equivFun e x N.· equivFun e y

open Semigroup
open IsSemigroup
open SemigroupEquiv

η-isSemiGroup : {A : Type ℓ} {_·_ : A → A → A} (b : IsSemigroup _·_)
             → issemigroup (is-set b) (assoc b) ≡ b
is-set (η-isSemiGroup b i) = is-set b
assoc (η-isSemiGroup b i) = assoc b

η-SemigroupEquiv : {M N : Semigroup {ℓ}} (p : SemigroupEquiv M N)
                 → semigroupequiv (e p) (isHom p) ≡ p
e (η-SemigroupEquiv p i) = e p
isHom (η-SemigroupEquiv p i) = isHom p

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
  rightInv (SemigroupAxiomsIsoIsSemigroup s) M            = η-isSemiGroup M
  leftInv (SemigroupAxiomsIsoIsSemigroup s) _             = refl

  SemigroupAxioms≡IsSemigroup : {A : Type ℓ} (_·_ : RawSemigroupStructure A)
                              → SemigroupAxioms _ _·_ ≡ IsSemigroup _·_
  SemigroupAxioms≡IsSemigroup s = isoToPath (SemigroupAxiomsIsoIsSemigroup s)

  Semigroup→SemigroupΣ : Semigroup → SemigroupΣ
  Semigroup→SemigroupΣ (semigroup A _·_ isSemigroup) =
    A , _·_ , SemigroupAxiomsIsoIsSemigroup _ .inv isSemigroup

  SemigroupΣ→Semigroup : SemigroupΣ → Semigroup
  SemigroupΣ→Semigroup (A , _·_ , isSemigroupΣ) =
    semigroup A _·_ (SemigroupAxiomsIsoIsSemigroup _ .fun isSemigroupΣ)

  SemigroupIsoSemigroupΣ : Iso Semigroup SemigroupΣ
  SemigroupIsoSemigroupΣ =
    iso Semigroup→SemigroupΣ SemigroupΣ→Semigroup (λ _ → refl) helper
    where
    helper : (a : Semigroup) → SemigroupΣ→Semigroup (Semigroup→SemigroupΣ a) ≡ a
    Carrier (helper a i) = ⟨ a ⟩
    _·_ (helper a i) = _·_ a
    isSemigroup (helper a i) = η-isSemiGroup (isSemigroup a) i

  semigroupUnivalentStr : UnivalentStr SemigroupStructure SemigroupEquivStr
  semigroupUnivalentStr = axiomsUnivalentStr _ isPropSemigroupAxioms rawSemigroupUnivalentStr

  SemigroupΣPath : (M N : SemigroupΣ) → (M ≃[ SemigroupEquivStr ] N) ≃ (M ≡ N)
  SemigroupΣPath = SIP semigroupUnivalentStr

  SemigroupEquivΣ : (M N : Semigroup) → Type ℓ
  SemigroupEquivΣ M N = Semigroup→SemigroupΣ M ≃[ SemigroupEquivStr ] Semigroup→SemigroupΣ N

  open SemigroupEquiv

  SemigroupIsoΣPath : {M N : Semigroup} → Iso (SemigroupEquiv M N) (SemigroupEquivΣ M N)
  fun SemigroupIsoΣPath x                 = e x , isHom x
  inv SemigroupIsoΣPath (e , h)            = semigroupequiv e h
  rightInv SemigroupIsoΣPath _             = refl
  leftInv SemigroupIsoΣPath _              = η-SemigroupEquiv _

  SemigroupPath : (M N : Semigroup) → (SemigroupEquiv M N) ≃ (M ≡ N)
  SemigroupPath M N =
    SemigroupEquiv M N                                ≃⟨ isoToEquiv SemigroupIsoΣPath ⟩
    SemigroupEquivΣ M N                               ≃⟨ SemigroupΣPath _ _ ⟩
    Semigroup→SemigroupΣ M ≡ Semigroup→SemigroupΣ N ≃⟨ isoToEquiv (invIso (congIso SemigroupIsoSemigroupΣ)) ⟩
    M ≡ N ■

-- We now extract the important results from the above module

isPropIsSemigroup : {A : Type ℓ} (_·_ : A → A → A) → isProp (IsSemigroup _·_)
isPropIsSemigroup _·_ =
  subst isProp (SemigroupΣTheory.SemigroupAxioms≡IsSemigroup _·_)
        (SemigroupΣTheory.isPropSemigroupAxioms _ _·_)

SemigroupPath : (M N : Semigroup {ℓ}) → (SemigroupEquiv M N) ≃ (M ≡ N)
SemigroupPath = SemigroupΣTheory.SemigroupPath


-- To rename the fields when using a Semigroup use for example the following:
--
-- open Semigroup M renaming ( Carrier to M ; _·_ to _·M_ )
