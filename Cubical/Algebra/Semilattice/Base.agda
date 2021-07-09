{-
 following Johnstone we define semilattices to be commutative monoids
 such that every element is idempotent. In particular, we take every
 semilattice to have a neutral element that is either the maximal or
 minimal element depending on whether we have a join or meet semilattice
-}

{-# OPTIONS --safe #-}
module Cubical.Algebra.Semilattice.Base where

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
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.CommMonoid

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.Relation.Binary

open import Cubical.Reflection.RecordEquiv

open Iso

private
  variable
    ℓ ℓ' : Level

record IsSemilattice {A : Type ℓ} (ε : A) (_·_ : A → A → A) : Type ℓ where
  constructor issemilattice

  field
   isCommMonoid : IsCommMonoid ε _·_
   idem : (x : A) → x · x ≡ x

  open IsCommMonoid isCommMonoid public

unquoteDecl IsSemilatticeIsoΣ = declareRecordIsoΣ IsSemilatticeIsoΣ (quote IsSemilattice)

record SemilatticeStr (A : Type ℓ) : Type ℓ where
  constructor semilatticestr

  field
    ε        : A
    _·_      : A → A → A
    isSemilattice : IsSemilattice ε _·_

  infixl 7 _·_

  open IsSemilattice isSemilattice public

Semilattice : ∀ ℓ → Type (ℓ-suc ℓ)
Semilattice ℓ = TypeWithStr ℓ SemilatticeStr

semilattice : (A : Type ℓ) (ε : A) (_·_ : A → A → A) (h : IsSemilattice ε _·_) → Semilattice ℓ
semilattice A ε _·_ h = A , semilatticestr ε _·_ h

-- Easier to use constructors
makeIsSemilattice : {L : Type ℓ} {ε : L} {_·_ : L → L → L}
               (is-setL : isSet L)
               (assoc : (x y z : L) → x · (y · z) ≡ (x · y) · z)
               (rid : (x : L) → x · ε ≡ x)
               (lid : (x : L) → ε · x ≡ x)
               (comm : (x y : L) → x · y ≡ y · x)
               (idem : (x : L) → x · x ≡ x)
             → IsSemilattice ε _·_
IsSemilattice.isCommMonoid (makeIsSemilattice is-setL assoc rid lid comm idem) =
                                        makeIsCommMonoid is-setL assoc rid lid comm
IsSemilattice.idem (makeIsSemilattice is-setL assoc rid lid comm idem) = idem

makeSemilattice : {L : Type ℓ} (ε : L) (_·_ : L → L → L)
             (is-setL : isSet L)
             (assoc : (x y z : L) → x · (y · z) ≡ (x · y) · z)
             (rid : (x : L) → x · ε ≡ x)
             (lid : (x : L) → ε · x ≡ x)
             (comm : (x y : L) → x · y ≡ y · x)
             (idem : (x : L) → x · x ≡ x)
             → Semilattice ℓ
makeSemilattice ε _·_ is-setL assoc rid lid comm idem =
  semilattice _ ε _·_ (makeIsSemilattice is-setL assoc rid lid comm idem)


SemilatticeStr→MonoidStr : {A : Type ℓ} → SemilatticeStr A → MonoidStr A
SemilatticeStr→MonoidStr (semilatticestr _ _ H) =
                          monoidstr _ _ (H .IsSemilattice.isCommMonoid .IsCommMonoid.isMonoid)

Semilattice→Monoid : Semilattice ℓ → Monoid ℓ
Semilattice→Monoid (_ , semilatticestr _ _ H) =
                    _ , monoidstr _ _ (H .IsSemilattice.isCommMonoid .IsCommMonoid.isMonoid)

IsSemilatticeEquiv : {A : Type ℓ} {B : Type ℓ'}
  (M : SemilatticeStr A) (e : A ≃ B) (N : SemilatticeStr B) → Type (ℓ-max ℓ ℓ')
IsSemilatticeEquiv M e N = IsMonoidEquiv (SemilatticeStr→MonoidStr M) e (SemilatticeStr→MonoidStr N)

SemilatticeEquiv : (M : Semilattice ℓ) (N : Semilattice ℓ') → Type (ℓ-max ℓ ℓ')
SemilatticeEquiv M N = Σ[ e ∈ (M .fst ≃ N .fst) ] IsSemilatticeEquiv (M .snd) e (N .snd)

isPropIsSemilattice : {L : Type ℓ} (ε : L) (_·_ : L → L → L)
             → isProp (IsSemilattice ε _·_)
isPropIsSemilattice ε _·_ (issemilattice LL LC) (issemilattice SL SC) =
  λ i → issemilattice (isPropIsCommMonoid _ _ LL SL i) (isPropIdem LC SC i)
  where
  isSetL : isSet _
  isSetL = LL .IsCommMonoid.isMonoid .IsMonoid.isSemigroup .IsSemigroup.is-set

  isPropIdem : isProp ((x : _) → x · x ≡ x)
  isPropIdem = isPropΠ λ _ → isSetL _ _

𝒮ᴰ-Semilattice : DUARel (𝒮-Univ ℓ) SemilatticeStr ℓ
𝒮ᴰ-Semilattice =
  𝒮ᴰ-Record (𝒮-Univ _) IsSemilatticeEquiv
    (fields:
      data[ ε ∣ autoDUARel _ _ ∣ presε ]
      data[ _·_ ∣ autoDUARel _ _ ∣ isHom ]
      prop[ isSemilattice ∣ (λ _ _ → isPropIsSemilattice _ _) ])
  where
  open SemilatticeStr
  open IsMonoidEquiv

SemilatticePath : (L K : Semilattice ℓ) → SemilatticeEquiv L K ≃ (L ≡ K)
SemilatticePath = ∫ 𝒮ᴰ-Semilattice .UARel.ua


-- TODO: decide if that's the right approach
module JoinSemilattice (L' : Semilattice ℓ) where
 private L = fst L'
 open SemilatticeStr (snd L') renaming (_·_ to _∨l_ ; ε to 1l)

 _≤_ : L → L → Type ℓ
 x ≤ y = x ∨l y ≡ y


module MeetSemilattice (L' : Semilattice ℓ) where
 private L = fst L'
 open SemilatticeStr (snd L') renaming (_·_ to _∧l_ ; ε to 0l)

 _≤_ : L → L → Type ℓ
 x ≤ y = x ∧l y ≡ x
