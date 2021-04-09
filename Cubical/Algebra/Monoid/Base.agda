{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Monoid.Base where

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
open import Cubical.Structures.Record
open import Cubical.Algebra.Semigroup

open import Cubical.Reflection.StrictEquiv

open Iso

private
  variable
    ℓ : Level

record IsMonoid {A : Type ℓ} (ε : A) (_·_ : A → A → A) : Type ℓ where
  constructor ismonoid

  field
    isSemigroup : IsSemigroup _·_
    identity    : (x : A) → (x · ε ≡ x) × (ε · x ≡ x)

  open IsSemigroup isSemigroup public

  lid : (x : A) → ε · x ≡ x
  lid x = identity x .snd

  rid : (x : A) → x · ε ≡ x
  rid x = identity x .fst


record MonoidStr (A : Type ℓ) : Type (ℓ-suc ℓ) where
  constructor monoidstr

  field
    ε        : A
    _·_      : A → A → A
    isMonoid : IsMonoid ε _·_

  infixl 7 _·_

  open IsMonoid isMonoid public

  -- semigrp : Semigroup
  -- semigrp = record { isSemigroup = isSemigroup }

  -- open Semigroup semigrp public

Monoid : Type (ℓ-suc ℓ)
Monoid = TypeWithStr _ MonoidStr

monoid : (A : Type ℓ) (ε : A) (_·_ : A → A → A) (h : IsMonoid ε _·_) → Monoid
monoid A ε _·_ h = A , monoidstr ε _·_ h

-- Easier to use constructors

makeIsMonoid : {M : Type ℓ} {ε : M} {_·_ : M → M → M}
               (is-setM : isSet M)
               (assoc : (x y z : M) → x · (y · z) ≡ (x · y) · z)
               (rid : (x : M) → x · ε ≡ x)
               (lid : (x : M) → ε · x ≡ x)
             → IsMonoid ε _·_
IsMonoid.isSemigroup (makeIsMonoid is-setM assoc rid lid) = issemigroup is-setM assoc
IsMonoid.identity (makeIsMonoid is-setM assoc rid lid) = λ x → rid x , lid x

makeMonoid : {M : Type ℓ} (ε : M) (_·_ : M → M → M)
             (is-setM : isSet M)
             (assoc : (x y z : M) → x · (y · z) ≡ (x · y) · z)
             (rid : (x : M) → x · ε ≡ x)
             (lid : (x : M) → ε · x ≡ x)
           → Monoid
makeMonoid ε _·_ is-setM assoc rid lid =
  monoid _ ε _·_ (makeIsMonoid is-setM assoc rid lid)

record MonoidEquiv (M N : Monoid {ℓ}) (e : ⟨ M ⟩ ≃ ⟨ N ⟩) : Type ℓ where

  constructor monoidiso

  private
    module M = MonoidStr (snd M)
    module N = MonoidStr (snd N)

  field
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
  inv (MonoidAxiomsIsoIsMonoid s) a = (IsMonoid.isSemigroup a) , IsMonoid.identity a
  rightInv (MonoidAxiomsIsoIsMonoid s) _         = refl
  leftInv (MonoidAxiomsIsoIsMonoid s) _          = refl

  MonoidAxioms≡IsMonoid : {M : Type ℓ} (s : RawMonoidStructure M)
    → MonoidAxioms M s ≡ IsMonoid (s .fst) (s .snd)
  MonoidAxioms≡IsMonoid s = ua (strictIsoToEquiv (MonoidAxiomsIsoIsMonoid s))

  open MonoidStr

  Monoid→MonoidΣ : Monoid → MonoidΣ
  Monoid→MonoidΣ (A , M) =
    A , (ε M , _·_ M) , MonoidAxiomsIsoIsMonoid (ε M , _·_ M) .inv (isMonoid M)

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

  MonoidIsoΣPath : {M N : Monoid} → Iso (Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] (MonoidEquiv M N e)) (MonoidEquivΣ M N)
  fun MonoidIsoΣPath (e , monoidiso h1 h2) = (e , h1 , h2)
  inv MonoidIsoΣPath (e , h1 , h2)         = (e , monoidiso h1 h2)
  rightInv MonoidIsoΣPath _                = refl
  leftInv MonoidIsoΣPath _                 = refl

  MonoidPath : (M N : Monoid {ℓ}) → (Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] (MonoidEquiv M N e)) ≃ (M ≡ N)
  MonoidPath M N =
    Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] MonoidEquiv M N e ≃⟨ isoToEquiv MonoidIsoΣPath ⟩
    MonoidEquivΣ M N                      ≃⟨ MonoidΣPath _ _ ⟩
    Monoid→MonoidΣ M ≡ Monoid→MonoidΣ N ≃⟨ isoToEquiv (invIso (congIso MonoidIsoMonoidΣ)) ⟩
    M ≡ N ■

  RawMonoidΣ : Type (ℓ-suc ℓ)
  RawMonoidΣ = TypeWithStr ℓ RawMonoidStructure

  Monoid→RawMonoidΣ : Monoid → RawMonoidΣ
  Monoid→RawMonoidΣ (A , M) = A , (ε M) , (_·_ M)

  InducedMonoid : (M : Monoid) (N : RawMonoidΣ) (e : M .fst ≃ N .fst)
                 → RawMonoidEquivStr (Monoid→RawMonoidΣ M) N e → Monoid
  InducedMonoid M N e r =
    MonoidΣ→Monoid (inducedStructure rawMonoidUnivalentStr (Monoid→MonoidΣ M) N (e , r))

  InducedMonoidPath : (M : Monoid {ℓ}) (N : RawMonoidΣ) (e : M .fst ≃ N .fst)
                      (E : RawMonoidEquivStr (Monoid→RawMonoidΣ M) N e)
                    → M ≡ InducedMonoid M N e E
  InducedMonoidPath M N e E =
    MonoidPath M (InducedMonoid M N e E) .fst (e , monoidiso (E .fst) (E .snd))

-- We now extract the important results from the above module

isPropIsMonoid : {M : Type ℓ} (ε : M) (_·_ : M → M → M) → isProp (IsMonoid ε _·_)
isPropIsMonoid ε _·_ =
  subst isProp (MonoidΣTheory.MonoidAxioms≡IsMonoid (ε , _·_))
        (MonoidΣTheory.isPropMonoidAxioms _ (ε , _·_))

MonoidPath : (M N : Monoid {ℓ}) → (Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] MonoidEquiv M N e) ≃ (M ≡ N)
MonoidPath {ℓ = ℓ} =
  SIP
    (autoUnivalentRecord
      (autoRecordSpec (MonoidStr {ℓ}) MonoidEquiv
        (fields:
          data[ ε ∣ presε ]
          data[ _·_ ∣ isHom ]
          prop[ isMonoid ∣ (λ _ → isPropIsMonoid _ _) ]))
      _ _)
  where
  open MonoidStr
  open MonoidEquiv

InducedMonoid : (M : Monoid {ℓ}) (N : MonoidΣTheory.RawMonoidΣ) (e : M .fst ≃ N .fst)
              → MonoidΣTheory.RawMonoidEquivStr (MonoidΣTheory.Monoid→RawMonoidΣ M) N e
              → Monoid
InducedMonoid = MonoidΣTheory.InducedMonoid

InducedMonoidPath : (M : Monoid {ℓ}) (N : MonoidΣTheory.RawMonoidΣ) (e : M .fst ≃ N .fst)
                    (E : MonoidΣTheory.RawMonoidEquivStr (MonoidΣTheory.Monoid→RawMonoidΣ M) N e)
                  → M ≡ InducedMonoid M N e E
InducedMonoidPath = MonoidΣTheory.InducedMonoidPath

module MonoidTheory {ℓ} (M : Monoid {ℓ}) where

  open MonoidStr (snd M)

  -- Added for its use in groups
  -- If there exists a inverse of an element it is unique
  inv-lemma : (x y z : ⟨ M ⟩) → y · x ≡ ε → x · z ≡ ε → y ≡ z
  inv-lemma x y z left-inverse right-inverse =
    y           ≡⟨ sym (rid y) ⟩
    y · ε       ≡⟨ cong (λ - → y · -) (sym right-inverse) ⟩
    y · (x · z) ≡⟨ assoc y x z ⟩
    (y · x) · z ≡⟨ cong (λ - → - · z) left-inverse ⟩
    ε · z       ≡⟨ lid z ⟩
    z ∎

