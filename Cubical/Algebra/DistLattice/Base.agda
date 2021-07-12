{-# OPTIONS --safe #-}
module Cubical.Algebra.DistLattice.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Lattice.Base

open Iso

private
  variable
    ℓ ℓ' : Level

record IsDistLattice {L : Type ℓ}
                     (0l 1l : L) (_∨l_ _∧l_ : L → L → L) : Type ℓ where

  constructor isdistlattice

  field
    isLattice : IsLattice 0l 1l _∨l_ _∧l_
    ∨l-dist-∧l : (x y z : L) → (x ∨l (y ∧l z) ≡ (x ∨l y) ∧l (x ∨l z))
                              × ((y ∧l z) ∨l x ≡ (y ∨l x) ∧l (z ∨l x))
    ∧l-dist-∨l : (x y z : L) → (x ∧l (y ∨l z) ≡ (x ∧l y) ∨l (x ∧l z))
                              × ((y ∨l z) ∧l x ≡ (y ∧l x) ∨l (z ∧l x))

  open IsLattice isLattice public

  ∨lLdist∧l :  (x y z : L) → x ∨l (y ∧l z) ≡ (x ∨l y) ∧l (x ∨l z)
  ∨lLdist∧l x y z = ∨l-dist-∧l x y z .fst

  ∨lRdist∧l : (x y z : L) → (y ∧l z) ∨l x ≡ (y ∨l x) ∧l (z ∨l x)
  ∨lRdist∧l x y z = ∨l-dist-∧l x y z .snd

  ∧lLdist∨l : (x y z : L) → x ∧l (y ∨l z) ≡ (x ∧l y) ∨l (x ∧l z)
  ∧lLdist∨l x y z = ∧l-dist-∨l x y z .fst

  ∧lRdist∨l : (x y z : L) → (y ∨l z) ∧l x ≡ (y ∧l x) ∨l (z ∧l x)
  ∧lRdist∨l x y z = ∧l-dist-∨l x y z .snd

record DistLatticeStr (A : Type ℓ) : Type (ℓ-suc ℓ) where

  constructor distlatticestr

  field
    0l            : A
    1l            : A
    _∨l_         : A → A → A
    _∧l_         : A → A → A
    isDistLattice : IsDistLattice 0l 1l _∨l_ _∧l_

  infix 7 _∨l_
  infix 6 _∧l_

  open IsDistLattice isDistLattice public

DistLattice : ∀ ℓ → Type (ℓ-suc ℓ)
DistLattice ℓ = TypeWithStr ℓ DistLatticeStr


-- makeIsDistLattice : {R : Type ℓ} {0r 1r : R} {_+_ _·_ : R → R → R} { -_ : R → R}
--                  (is-setR : isSet R)
--                  (+-assoc : (x y z : R) → x + (y + z) ≡ (x + y) + z)
--                  (+-rid : (x : R) → x + 0r ≡ x)
--                  (+-rinv : (x : R) → x + (- x) ≡ 0r)
--                  (+-comm : (x y : R) → x + y ≡ y + x)
--                  (·-assoc : (x y z : R) → x · (y · z) ≡ (x · y) · z)
--                  (·-rid : (x : R) → x · 1r ≡ x)
--                  (·-rdist-+ : (x y z : R) → x · (y + z) ≡ (x · y) + (x · z))
--                  (·-comm : (x y : R) → x · y ≡ y · x)
--                → IsDistLattice 0r 1r _+_ _·_ -_
-- makeIsDistLattice {_+_ = _+_} is-setR +-assoc +-rid +-rinv +-comm ·-assoc ·-rid ·-rdist-+ ·-comm =
--   iscommring (makeIsLattice is-setR +-assoc +-rid +-rinv +-comm ·-assoc ·-rid
--                          (λ x → ·-comm _ _ ∙ ·-rid x) ·-rdist-+
--                          (λ x y z → ·-comm _ _ ∙∙ ·-rdist-+ z x y ∙∙ λ i → (·-comm z x i) + (·-comm z y i))) ·-comm

-- makeDistLattice : {R : Type ℓ} (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R)
--                (is-setR : isSet R)
--                (+-assoc : (x y z : R) → x + (y + z) ≡ (x + y) + z)
--                (+-rid : (x : R) → x + 0r ≡ x)
--                (+-rinv : (x : R) → x + (- x) ≡ 0r)
--                (+-comm : (x y : R) → x + y ≡ y + x)
--                (·-assoc : (x y z : R) → x · (y · z) ≡ (x · y) · z)
--                (·-rid : (x : R) → x · 1r ≡ x)
--                (·-rdist-+ : (x y z : R) → x · (y + z) ≡ (x · y) + (x · z))
--                (·-comm : (x y : R) → x · y ≡ y · x)
--              → DistLattice ℓ
-- makeDistLattice 0r 1r _+_ _·_ -_ is-setR +-assoc +-rid +-rinv +-comm ·-assoc ·-rid ·-rdist-+ ·-comm =
--   _ , commringstr _ _ _ _ _ (makeIsDistLattice is-setR +-assoc +-rid +-rinv +-comm ·-assoc ·-rid ·-rdist-+ ·-comm)

-- DistLatticeStr→LatticeStr : {A : Type ℓ} → DistLatticeStr A → LatticeStr A
-- DistLatticeStr→LatticeStr (commringstr _ _ _ _ _ H) = ringstr _ _ _ _ _ (IsDistLattice.isLattice H)

-- DistLattice→Lattice : DistLattice ℓ → Lattice ℓ
-- DistLattice→Lattice (_ , commringstr _ _ _ _ _ H) = _ , ringstr _ _ _ _ _ (IsDistLattice.isLattice H)

-- DistLatticeHom : (R : DistLattice ℓ) (S : DistLattice ℓ') → Type (ℓ-max ℓ ℓ')
-- DistLatticeHom R S = LatticeHom (DistLattice→Lattice R) (DistLattice→Lattice S)

-- IsDistLatticeEquiv : {A : Type ℓ} {B : Type ℓ'}
--   (R : DistLatticeStr A) (e : A ≃ B) (S : DistLatticeStr B) → Type (ℓ-max ℓ ℓ')
-- IsDistLatticeEquiv R e S = IsLatticeHom (DistLatticeStr→LatticeStr R) (e .fst) (DistLatticeStr→LatticeStr S)

-- DistLatticeEquiv : (R : DistLattice ℓ) (S : DistLattice ℓ') → Type (ℓ-max ℓ ℓ')
-- DistLatticeEquiv R S = Σ[ e ∈ (R .fst ≃ S .fst) ] IsDistLatticeEquiv (R .snd) e (S .snd)

-- isPropIsDistLattice : {R : Type ℓ} (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R)
--              → isProp (IsDistLattice 0r 1r _+_ _·_ -_)
-- isPropIsDistLattice 0r 1r _+_ _·_ -_ (iscommring RR RC) (iscommring SR SC) =
--   λ i → iscommring (isPropIsLattice _ _ _ _ _ RR SR i)
--                    (isPropComm RC SC i)
--   where
--   isSetR : isSet _
--   isSetR = RR .IsLattice.·IsMonoid .IsMonoid.isSemigroup .IsSemigroup.is-set

--   isPropComm : isProp ((x y : _) → x · y ≡ y · x)
--   isPropComm = isPropΠ2 λ _ _ → isSetR _ _

-- 𝒮ᴰ-DistLattice : DUARel (𝒮-Univ ℓ) DistLatticeStr ℓ
-- 𝒮ᴰ-DistLattice =
--   𝒮ᴰ-Record (𝒮-Univ _) IsDistLatticeEquiv
--     (fields:
--       data[ 0r ∣ null ∣ pres0 ]
--       data[ 1r ∣ null ∣ pres1 ]
--       data[ _+_ ∣ bin ∣ pres+ ]
--       data[ _·_ ∣ bin ∣ pres· ]
--       data[ -_ ∣ autoDUARel _ _ ∣ pres- ]
--       prop[ isDistLattice ∣ (λ _ _ → isPropIsDistLattice _ _ _ _ _) ])
--  where
--   open DistLatticeStr
--   open IsLatticeHom

--   -- faster with some sharing
--   null = autoDUARel (𝒮-Univ _) (λ A → A)
--   bin = autoDUARel (𝒮-Univ _) (λ A → A → A → A)

-- DistLatticePath : (R S : DistLattice ℓ) → DistLatticeEquiv R S ≃ (R ≡ S)
-- DistLatticePath = ∫ 𝒮ᴰ-DistLattice .UARel.ua

-- isSetDistLattice : ((R , str) : DistLattice ℓ) → isSet R
-- isSetDistLattice (R , str) = str .DistLatticeStr.is-set

