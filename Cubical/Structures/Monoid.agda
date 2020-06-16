{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.Monoid where

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
open import Cubical.Structures.Semigroup hiding (⟨_⟩)

open Iso

private
  variable
    ℓ : Level

record IsMonoid {A : Type ℓ} (ε : A) (_·_ : A → A → A) : Type ℓ where

  -- TODO: add no-eta-equality for efficiency?

  constructor ismonoid

  field
    isSemigroup : IsSemigroup _·_
    identity    : (x : A) → (x · ε ≡ x) × (ε · x ≡ x)

  open IsSemigroup isSemigroup public

  lid : (x : A) → ε · x ≡ x
  lid x = identity x .snd

  rid : (x : A) → x · ε ≡ x
  rid x = identity x .fst


record Monoid : Type (ℓ-suc ℓ) where

  constructor monoid

  field
    Carrier  : Type ℓ
    ε        : Carrier
    _·_      : Carrier → Carrier → Carrier
    isMonoid : IsMonoid ε _·_

  infixl 7 _·_

  open IsMonoid isMonoid public

  -- semigrp : Semigroup
  -- semigrp = record { isSemigroup = isSemigroup }

  -- open Semigroup semigrp public

-- Extractor for the carrier type
⟨_⟩ : Monoid → Type ℓ
⟨_⟩ = Monoid.Carrier

-- Easier to use constructor
makeMonoid : (A : Type ℓ) (ε : A) (_·_ : A → A → A)
             (is-setA : isSet A)
             (assoc : (x y z : A) → x · (y · z) ≡ (x · y) · z)
             (rid : (x : A) → (x · ε) ≡ x)
             (lid : (x : A) → (ε · x) ≡ x)
           → Monoid {ℓ}
makeMonoid A ε _·_ is-setA assoc rid lid =
  monoid A ε _·_ (ismonoid (issemigroup is-setA assoc) λ x → rid x , lid x)

record MonoidIso (M N : Monoid {ℓ}) : Type ℓ where

  constructor monoidiso

  private
    module M = Monoid M
    module N = Monoid N

  field
    e     : ⟨ M ⟩ ≃ ⟨ N ⟩
    presε : equivFun e M.ε ≡ N.ε
    isHom : (x y : ⟨ M ⟩) → equivFun e (x M.· y) ≡ equivFun e x N.· equivFun e y



module MonoidΣ-theory {ℓ} where

  open Macro ℓ (var , recvar (recvar var)) public renaming
    ( structure to raw-monoid-structure
    ; iso to raw-monoid-iso
    ; isSNS to raw-monoid-is-SNS
    )

  monoid-axioms : (A : Type ℓ) → raw-monoid-structure A → Type ℓ
  monoid-axioms A (e , _·_) = IsSemigroup _·_
                            × ((x : A) → (x · e ≡ x) × (e · x ≡ x))

  monoid-structure : Type ℓ → Type ℓ
  monoid-structure = add-to-structure raw-monoid-structure monoid-axioms

  MonoidΣ : Type (ℓ-suc ℓ)
  MonoidΣ = TypeWithStr ℓ monoid-structure

  monoid-axioms-isProp : (A : Type ℓ) (s : raw-monoid-structure A) → isProp (monoid-axioms A s)
  monoid-axioms-isProp A (e , _·_) =
    isPropΣ (isPropIsSemigroup _·_)
            λ α → isPropΠ λ _ → isProp× (IsSemigroup.is-set α _ _) (IsSemigroup.is-set α _ _)

  monoid-iso : StrIso monoid-structure ℓ
  monoid-iso = add-to-iso raw-monoid-iso monoid-axioms

  monoid-axiomsIsoIsMonoid : {A : Type ℓ} (s : raw-monoid-structure A)
                           → Iso (monoid-axioms A s) (IsMonoid (s .fst) (s .snd))
  fun (monoid-axiomsIsoIsMonoid s) (x , y)        = ismonoid x y
  inv (monoid-axiomsIsoIsMonoid s) (ismonoid x y) = (x , y)
  rightInv (monoid-axiomsIsoIsMonoid s) _         = refl
  leftInv (monoid-axiomsIsoIsMonoid s) _          = refl

  monoid-axioms≡IsMonoid : {A : Type ℓ} (s : raw-monoid-structure A)
                         → monoid-axioms A s ≡ IsMonoid (s .fst) (s .snd)
  monoid-axioms≡IsMonoid s = isoToPath (monoid-axiomsIsoIsMonoid s)

  Monoid→MonoidΣ : Monoid {ℓ} → MonoidΣ
  Monoid→MonoidΣ (monoid A ε _·_ isMonoid) =
    A , (ε , _·_) , monoid-axiomsIsoIsMonoid (ε , _·_) .inv isMonoid

  MonoidΣ→Monoid : MonoidΣ → Monoid
  MonoidΣ→Monoid (A , (ε , _·_) , isMonoidΣ) =
    monoid A ε _·_ (monoid-axiomsIsoIsMonoid (ε , _·_) .fun isMonoidΣ)

  MonoidIsoMonoidΣ : Iso (Monoid {ℓ}) MonoidΣ
  MonoidIsoMonoidΣ =
    iso Monoid→MonoidΣ MonoidΣ→Monoid (λ _ → refl) (λ _ → refl)

  Monoid≡MonoidΣ : Monoid {ℓ} ≡ MonoidΣ
  Monoid≡MonoidΣ = isoToPath MonoidIsoMonoidΣ

  monoid-is-SNS : SNS {ℓ} monoid-structure monoid-iso
  monoid-is-SNS = add-axioms-SNS _ monoid-axioms-isProp raw-monoid-is-SNS

  MonoidΣPath : (M N : MonoidΣ) → (M ≃[ monoid-iso ] N) ≃ (M ≡ N)
  MonoidΣPath = SIP monoid-is-SNS

  MonoidIsoΣ : (M N : Monoid {ℓ}) → Type ℓ
  MonoidIsoΣ M N = Monoid→MonoidΣ M ≃[ monoid-iso ] Monoid→MonoidΣ N

  MonoidIsoΣPath : {M N : Monoid {ℓ}} → Iso (MonoidIso M N) (MonoidIsoΣ M N)
  fun MonoidIsoΣPath (monoidiso e h1 h2) = (e , h1 , h2)
  inv MonoidIsoΣPath (e , h1 , h2)       = monoidiso e h1 h2
  rightInv MonoidIsoΣPath _              = refl
  leftInv MonoidIsoΣPath _               = refl

  MonoidPath : (M N : Monoid {ℓ}) → (MonoidIso M N) ≃ (M ≡ N)
  MonoidPath M N =
    MonoidIso M N                       ≃⟨ isoToEquiv MonoidIsoΣPath ⟩
    MonoidIsoΣ M N                      ≃⟨ MonoidΣPath (Monoid→MonoidΣ M) (Monoid→MonoidΣ N) ⟩
    Monoid→MonoidΣ M ≡ Monoid→MonoidΣ N ≃⟨ isoToEquiv (invIso (congIso MonoidIsoMonoidΣ)) ⟩
    M ≡ N ■


-- We now extract the important results from the above module

isPropIsMonoid : {A : Type ℓ} (ε : A) (_·_ : A → A → A) → isProp (IsMonoid ε _·_)
isPropIsMonoid ε _·_ =
  subst isProp (MonoidΣ-theory.monoid-axioms≡IsMonoid (ε , _·_))
        (MonoidΣ-theory.monoid-axioms-isProp _ (ε , _·_))

MonoidPath : (M N : Monoid {ℓ}) → (MonoidIso M N) ≃ (M ≡ N)
MonoidPath = MonoidΣ-theory.MonoidPath


module monoid-theory {ℓ} (M : Monoid {ℓ}) where

  open Monoid M renaming ( Carrier to A )

  -- Added for its use in groups
  -- If there exists a inverse of an element it is unique
  inv-lemma : (x y z : A) → y · x ≡ ε → x · z ≡ ε → y ≡ z
  inv-lemma x y z left-inverse right-inverse =
    y           ≡⟨ sym (rid y) ⟩
    y · ε       ≡⟨ cong (λ - → y · -) (sym right-inverse) ⟩
    y · (x · z) ≡⟨ assoc y x z ⟩
    (y · x) · z ≡⟨ cong (λ - → - · z) left-inverse ⟩
    ε · z       ≡⟨ lid z ⟩
    z ∎
