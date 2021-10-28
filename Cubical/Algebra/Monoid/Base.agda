{-# OPTIONS --safe #-}
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

open import Cubical.Algebra.Semigroup

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.Reflection.RecordEquiv

open Iso

private
  variable
    ℓ ℓ' : Level

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

unquoteDecl IsMonoidIsoΣ = declareRecordIsoΣ IsMonoidIsoΣ (quote IsMonoid)

record MonoidStr (A : Type ℓ) : Type ℓ where
  constructor monoidstr

  field
    ε        : A
    _·_      : A → A → A
    isMonoid : IsMonoid ε _·_

  infixl 7 _·_

  open IsMonoid isMonoid public

Monoid : ∀ ℓ → Type (ℓ-suc ℓ)
Monoid ℓ = TypeWithStr ℓ MonoidStr

monoid : (A : Type ℓ) (ε : A) (_·_ : A → A → A) (h : IsMonoid ε _·_) → Monoid ℓ
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
           → Monoid ℓ
makeMonoid ε _·_ is-setM assoc rid lid =
  monoid _ ε _·_ (makeIsMonoid is-setM assoc rid lid)

record IsMonoidHom {A : Type ℓ} {B : Type ℓ'}
  (M : MonoidStr A) (f : A → B) (N : MonoidStr B)
  : Type (ℓ-max ℓ ℓ')
  where

  constructor monoidequiv

  -- Shorter qualified names
  private
    module M = MonoidStr M
    module N = MonoidStr N

  field
    presε : f M.ε ≡ N.ε
    isHom : (x y : A) → f (x M.· y) ≡ f x N.· f y

MonoidHom : (L : Monoid ℓ) (M : Monoid ℓ') → Type (ℓ-max ℓ ℓ')
MonoidHom L M = Σ[ f ∈ (⟨ L ⟩ → ⟨ M ⟩) ] IsMonoidHom (L .snd) f (M .snd)

IsMonoidEquiv : {A : Type ℓ} {B : Type ℓ'} (M : MonoidStr A) (e : A ≃ B) (N : MonoidStr B)
  → Type (ℓ-max ℓ ℓ')
IsMonoidEquiv M e N = IsMonoidHom M (e .fst) N

MonoidEquiv : (M : Monoid ℓ) (N : Monoid ℓ') → Type (ℓ-max ℓ ℓ')
MonoidEquiv M N = Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] IsMonoidEquiv (M .snd) e (N .snd)

-- We now extract the important results from the above module

isPropIsMonoid : {M : Type ℓ} (ε : M) (_·_ : M → M → M) → isProp (IsMonoid ε _·_)
isPropIsMonoid ε _·_ =
  isOfHLevelRetractFromIso 1 IsMonoidIsoΣ
    (isPropΣ
      (isPropIsSemigroup _·_)
      (λ semi → isPropΠ λ _ → isProp× (semi .is-set _ _) (semi .is-set _ _)))
  where
  open IsSemigroup

𝒮ᴰ-Monoid : DUARel (𝒮-Univ ℓ) MonoidStr ℓ
𝒮ᴰ-Monoid =
  𝒮ᴰ-Record (𝒮-Univ _) IsMonoidEquiv
    (fields:
      data[ ε ∣ autoDUARel _ _ ∣ presε ]
      data[ _·_ ∣ autoDUARel _ _ ∣ isHom ]
      prop[ isMonoid ∣ (λ _ _ → isPropIsMonoid _ _) ])
  where
  open MonoidStr
  open IsMonoidHom

MonoidPath : (M N : Monoid ℓ) → MonoidEquiv M N ≃ (M ≡ N)
MonoidPath = ∫ 𝒮ᴰ-Monoid .UARel.ua

module MonoidTheory {ℓ} (M : Monoid ℓ) where

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

