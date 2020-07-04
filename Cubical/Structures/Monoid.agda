{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.Monoid where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Structures.Axioms
open import Cubical.Structures.Auto
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

record MonoidEquiv (M N : Monoid {ℓ}) : Type ℓ where

  constructor monoidiso

  private
    module M = Monoid M
    module N = Monoid N

  field
    e     : ⟨ M ⟩ ≃ ⟨ N ⟩
    presε : equivFun e M.ε ≡ N.ε
    isHom : (x y : ⟨ M ⟩) → equivFun e (x M.· y) ≡ equivFun e x N.· equivFun e y



module MonoidΣTheory {ℓ} where

  RawMonoidStructure : Type ℓ → Type ℓ
  RawMonoidStructure X = X × (X → X → X)

  RawMonoidEquivStr = AutoEquivStr RawMonoidStructure

  rawMonoidUnivalentStr : UnivalentStr _ RawMonoidEquivStr
  rawMonoidUnivalentStr = autoUnivalentStr RawMonoidStructure

  MonoidAxioms : (M : Type ℓ) → RawMonoidStructure M → Type ℓ
  MonoidAxioms M (e , _·_) = IsSemigroup _·_
                            × ((x : M) → (x · e ≡ x) × (e · x ≡ x))

  MonoidStructure : Type ℓ → Type ℓ
  MonoidStructure = AxiomsStructure RawMonoidStructure MonoidAxioms

  MonoidΣ : Type (ℓ-suc ℓ)
  MonoidΣ = TypeWithStr ℓ MonoidStructure

  isPropMonoidAxioms : (M : Type ℓ) (s : RawMonoidStructure M) → isProp (MonoidAxioms M s)
  isPropMonoidAxioms M (e , _·_) =
    isPropΣ (isPropIsSemigroup _·_)
            λ α → isPropΠ λ _ → isProp× (IsSemigroup.is-set α _ _) (IsSemigroup.is-set α _ _)

  MonoidEquivStr : StrEquiv MonoidStructure ℓ
  MonoidEquivStr = AxiomsEquivStr RawMonoidEquivStr MonoidAxioms

  MonoidAxiomsIsoIsMonoid : {M : Type ℓ} (s : RawMonoidStructure M)
    → Iso (MonoidAxioms M s) (IsMonoid (s .fst) (s .snd))
  fun (MonoidAxiomsIsoIsMonoid s) (x , y)        = ismonoid x y
  inv (MonoidAxiomsIsoIsMonoid s) (ismonoid x y) = (x , y)
  rightInv (MonoidAxiomsIsoIsMonoid s) _         = refl
  leftInv (MonoidAxiomsIsoIsMonoid s) _          = refl

  MonoidAxioms≡IsMonoid : {M : Type ℓ} (s : RawMonoidStructure M)
    → MonoidAxioms M s ≡ IsMonoid (s .fst) (s .snd)
  MonoidAxioms≡IsMonoid s = isoToPath (MonoidAxiomsIsoIsMonoid s)

  Monoid→MonoidΣ : Monoid → MonoidΣ
  Monoid→MonoidΣ (monoid M ε _·_ isMonoid) =
    M , (ε , _·_) , MonoidAxiomsIsoIsMonoid (ε , _·_) .inv isMonoid

  MonoidΣ→Monoid : MonoidΣ → Monoid
  MonoidΣ→Monoid (M , (ε , _·_) , isMonoidΣ) =
    monoid M ε _·_ (MonoidAxiomsIsoIsMonoid (ε , _·_) .fun isMonoidΣ)

  MonoidIsoMonoidΣ : Iso Monoid MonoidΣ
  MonoidIsoMonoidΣ =
    iso Monoid→MonoidΣ MonoidΣ→Monoid (λ _ → refl) (λ _ → refl)

  monoidUnivalentStr : UnivalentStr MonoidStructure MonoidEquivStr
  monoidUnivalentStr = axiomsUnivalentStr _ isPropMonoidAxioms rawMonoidUnivalentStr

  MonoidΣPath : (M N : MonoidΣ) → (M ≃[ MonoidEquivStr ] N) ≃ (M ≡ N)
  MonoidΣPath = SIP monoidUnivalentStr

  MonoidEquivΣ : (M N : Monoid) → Type ℓ
  MonoidEquivΣ M N = Monoid→MonoidΣ M ≃[ MonoidEquivStr ] Monoid→MonoidΣ N

  MonoidIsoΣPath : {M N : Monoid} → Iso (MonoidEquiv M N) (MonoidEquivΣ M N)
  fun MonoidIsoΣPath (monoidiso e h1 h2) = (e , h1 , h2)
  inv MonoidIsoΣPath (e , h1 , h2)       = monoidiso e h1 h2
  rightInv MonoidIsoΣPath _              = refl
  leftInv MonoidIsoΣPath _               = refl

  MonoidPath : (M N : Monoid) → (MonoidEquiv M N) ≃ (M ≡ N)
  MonoidPath M N =
    MonoidEquiv M N                       ≃⟨ isoToEquiv MonoidIsoΣPath ⟩
    MonoidEquivΣ M N                      ≃⟨ MonoidΣPath _ _ ⟩
    Monoid→MonoidΣ M ≡ Monoid→MonoidΣ N ≃⟨ isoToEquiv (invIso (congIso MonoidIsoMonoidΣ)) ⟩
    M ≡ N ■


  -- TODO: clean and generalize the following?
  RawMonoidΣ : Type (ℓ-suc ℓ)
  RawMonoidΣ = TypeWithStr ℓ RawMonoidStructure

  MonoidΣ→RawMonoidΣ : MonoidΣ → RawMonoidΣ
  MonoidΣ→RawMonoidΣ (X , Y , Z) = X , Y

  InducedMonoidΣ : (M : MonoidΣ) (N : RawMonoidΣ) (e : M .fst ≃ N .fst) → RawMonoidEquivStr (MonoidΣ→RawMonoidΣ M) N e → MonoidΣ
  InducedMonoidΣ (M , opsM , ax) (N , opsN) e r =
    N , opsN , subst (uncurry MonoidAxioms) (sip rawMonoidUnivalentStr (M , opsM) (N , opsN) (e , r)) ax

  InducedMonoidΣPath : (M : MonoidΣ) (N : RawMonoidΣ) (e : M .fst ≃ N .fst)
                       (E : RawMonoidEquivStr (MonoidΣ→RawMonoidΣ M) N e)
                     → M ≡ InducedMonoidΣ M N e E
  InducedMonoidΣPath M N e E = MonoidΣPath M (InducedMonoidΣ M N e E) .fst (e , E)

-- We now extract the important results from the above module

isPropIsMonoid : {M : Type ℓ} (ε : M) (_·_ : M → M → M) → isProp (IsMonoid ε _·_)
isPropIsMonoid ε _·_ =
  subst isProp (MonoidΣTheory.MonoidAxioms≡IsMonoid (ε , _·_))
        (MonoidΣTheory.isPropMonoidAxioms _ (ε , _·_))

MonoidPath : (M N : Monoid {ℓ}) → (MonoidEquiv M N) ≃ (M ≡ N)
MonoidPath = MonoidΣTheory.MonoidPath

InducedMonoid : (M : Monoid {ℓ}) (N : MonoidΣTheory.RawMonoidΣ) (e : M .Monoid.Carrier ≃ N .fst)
              → MonoidΣTheory.RawMonoidEquivStr (MonoidΣTheory.MonoidΣ→RawMonoidΣ (MonoidΣTheory.Monoid→MonoidΣ M)) N e
              → Monoid
InducedMonoid M N e H = MonoidΣTheory.MonoidΣ→Monoid (MonoidΣTheory.InducedMonoidΣ (MonoidΣTheory.Monoid→MonoidΣ M) N e H)

InducedMonoidPath : (M : Monoid {ℓ}) (N : MonoidΣTheory.RawMonoidΣ) (e : M .Monoid.Carrier ≃ N .fst)
                    (E : MonoidΣTheory.RawMonoidEquivStr (MonoidΣTheory.MonoidΣ→RawMonoidΣ (MonoidΣTheory.Monoid→MonoidΣ M)) N e)
                  → M ≡ InducedMonoid M N e E
InducedMonoidPath M N e E = cong MonoidΣTheory.MonoidΣ→Monoid (MonoidΣTheory.InducedMonoidΣPath (MonoidΣTheory.Monoid→MonoidΣ M) N e E)


module MonoidTheory {ℓ} (M' : Monoid {ℓ}) where

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
