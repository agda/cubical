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

-- Easier to use constructors

makeIsMonoid : {M : Type ℓ} {ε : M} {_·_ : M → M → M}
               (is-setM : isSet M)
               (assoc : (x y z : M) → x · (y · z) ≡ (x · y) · z)
               (rid : (x : M) → x · ε ≡ x)
               (lid : (x : M) → ε · x ≡ x)
             → IsMonoid ε _·_
makeIsMonoid is-setM assoc rid lid =
  ismonoid (issemigroup is-setM assoc) λ x → rid x , lid x

makeMonoid : {M : Type ℓ} (ε : M) (_·_ : M → M → M)
             (is-setM : isSet M)
             (assoc : (x y z : M) → x · (y · z) ≡ (x · y) · z)
             (rid : (x : M) → x · ε ≡ x)
             (lid : (x : M) → ε · x ≡ x)
           → Monoid
makeMonoid ε _·_ is-setM assoc rid lid =
  monoid _ ε _·_ (makeIsMonoid is-setM assoc rid lid)

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
    ; isSNS to raw-monoid-is-SNS )

  monoid-axioms : (M : Type ℓ) → raw-monoid-structure M → Type ℓ
  monoid-axioms M (e , _·_) = IsSemigroup _·_
                            × ((x : M) → (x · e ≡ x) × (e · x ≡ x))

  monoid-structure : Type ℓ → Type ℓ
  monoid-structure = add-to-structure raw-monoid-structure monoid-axioms

  MonoidΣ : Type (ℓ-suc ℓ)
  MonoidΣ = TypeWithStr ℓ monoid-structure

  monoid-axioms-isProp : (M : Type ℓ) (s : raw-monoid-structure M) → isProp (monoid-axioms M s)
  monoid-axioms-isProp M (e , _·_) =
    isPropΣ (isPropIsSemigroup _·_)
            λ α → isPropΠ λ _ → isProp× (IsSemigroup.is-set α _ _) (IsSemigroup.is-set α _ _)

  monoid-iso : StrIso monoid-structure ℓ
  monoid-iso = add-to-iso raw-monoid-iso monoid-axioms

  monoid-axiomsIsoIsMonoid : {M : Type ℓ} (s : raw-monoid-structure M)
                           → Iso (monoid-axioms M s) (IsMonoid (s .fst) (s .snd))
  fun (monoid-axiomsIsoIsMonoid s) (x , y)        = ismonoid x y
  inv (monoid-axiomsIsoIsMonoid s) (ismonoid x y) = (x , y)
  rightInv (monoid-axiomsIsoIsMonoid s) _         = refl
  leftInv (monoid-axiomsIsoIsMonoid s) _          = refl

  monoid-axioms≡IsMonoid : {M : Type ℓ} (s : raw-monoid-structure M)
                         → monoid-axioms M s ≡ IsMonoid (s .fst) (s .snd)
  monoid-axioms≡IsMonoid s = isoToPath (monoid-axiomsIsoIsMonoid s)

  Monoid→MonoidΣ : Monoid → MonoidΣ
  Monoid→MonoidΣ (monoid M ε _·_ isMonoid) =
    M , (ε , _·_) , monoid-axiomsIsoIsMonoid (ε , _·_) .inv isMonoid

  MonoidΣ→Monoid : MonoidΣ → Monoid
  MonoidΣ→Monoid (M , (ε , _·_) , isMonoidΣ) =
    monoid M ε _·_ (monoid-axiomsIsoIsMonoid (ε , _·_) .fun isMonoidΣ)

  MonoidIsoMonoidΣ : Iso Monoid MonoidΣ
  MonoidIsoMonoidΣ =
    iso Monoid→MonoidΣ MonoidΣ→Monoid (λ _ → refl) (λ _ → refl)

  monoid-is-SNS : SNS monoid-structure monoid-iso
  monoid-is-SNS = add-axioms-SNS _ monoid-axioms-isProp raw-monoid-is-SNS

  MonoidΣPath : (M N : MonoidΣ) → (M ≃[ monoid-iso ] N) ≃ (M ≡ N)
  MonoidΣPath = SIP monoid-is-SNS

  MonoidIsoΣ : (M N : Monoid) → Type ℓ
  MonoidIsoΣ M N = Monoid→MonoidΣ M ≃[ monoid-iso ] Monoid→MonoidΣ N

  MonoidIsoΣPath : {M N : Monoid} → Iso (MonoidIso M N) (MonoidIsoΣ M N)
  fun MonoidIsoΣPath (monoidiso e h1 h2) = (e , h1 , h2)
  inv MonoidIsoΣPath (e , h1 , h2)       = monoidiso e h1 h2
  rightInv MonoidIsoΣPath _              = refl
  leftInv MonoidIsoΣPath _               = refl

  MonoidPath : (M N : Monoid) → (MonoidIso M N) ≃ (M ≡ N)
  MonoidPath M N =
    MonoidIso M N                       ≃⟨ isoToEquiv MonoidIsoΣPath ⟩
    MonoidIsoΣ M N                      ≃⟨ MonoidΣPath _ _ ⟩
    Monoid→MonoidΣ M ≡ Monoid→MonoidΣ N ≃⟨ isoToEquiv (invIso (congIso MonoidIsoMonoidΣ)) ⟩
    M ≡ N ■


-- We now extract the important results from the above module

isPropIsMonoid : {M : Type ℓ} (ε : M) (_·_ : M → M → M) → isProp (IsMonoid ε _·_)
isPropIsMonoid ε _·_ =
  subst isProp (MonoidΣ-theory.monoid-axioms≡IsMonoid (ε , _·_))
        (MonoidΣ-theory.monoid-axioms-isProp _ (ε , _·_))

MonoidPath : (M N : Monoid {ℓ}) → (MonoidIso M N) ≃ (M ≡ N)
MonoidPath = MonoidΣ-theory.MonoidPath


module monoid-theory {ℓ} (M' : Monoid {ℓ}) where

  open Monoid M' renaming ( Carrier to M )

  -- Added for its use in groups
  -- If there exists a inverse of an element it is unique
  inv-lemma : (x y z : M) → y · x ≡ ε → x · z ≡ ε → y ≡ z
  inv-lemma x y z left-inverse right-inverse =
    y           ≡⟨ sym (rid y) ⟩
    y · ε       ≡⟨ cong (λ - → y · -) (sym right-inverse) ⟩
    y · (x · z) ≡⟨ assoc y x z ⟩
    (y · x) · z ≡⟨ cong (λ - → - · z) left-inverse ⟩
    ε · z       ≡⟨ lid z ⟩
    z ∎
