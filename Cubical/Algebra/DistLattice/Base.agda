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

isSetDistLattice : (L : DistLattice ℓ) → isSet ⟨ L ⟩
isSetDistLattice L = L .snd .DistLatticeStr.is-set

-- when proving the axioms for a distributive lattice
-- we use the fact that from distributivity and absorption
-- of ∧l over ∨l we can derive distributivity and absorption
-- of ∨l over ∧l and vice versa. We give provide thus two
-- ways of making a distributive lattice...
makeIsDistLattice∧lOver∨l : {L : Type ℓ} {0l 1l : L} {_∨l_ _∧l_ : L → L → L}
             (is-setL : isSet L)
             (∨l-assoc : (x y z : L) → x ∨l (y ∨l z) ≡ (x ∨l y) ∨l z)
             (∨l-rid : (x : L) → x ∨l 0l ≡ x)
             (∨l-comm : (x y : L) → x ∨l y ≡ y ∨l x)
             (∧l-assoc : (x y z : L) → x ∧l (y ∧l z) ≡ (x ∧l y) ∧l z)
             (∧l-rid : (x : L) → x ∧l 1l ≡ x)
             (∧l-comm : (x y : L) → x ∧l y ≡ y ∧l x)
             (∧l-absorb-∨l : (x y : L) → x ∧l (x ∨l y) ≡ x)
             (∧l-ldist-∨l : (x y z : L) → x ∧l (y ∨l z) ≡ (x ∧l y) ∨l (x ∧l z))
           → IsDistLattice 0l 1l _∨l_ _∧l_
makeIsDistLattice∧lOver∨l {_∨l_ = _∨l_} {_∧l_ = _∧l_} is-setL
                                                      ∨l-assoc ∨l-rid ∨l-comm
                                                      ∧l-assoc ∧l-rid ∧l-comm
                                                      ∧l-absorb-∨l ∧l-ldist-∨l =
 isdistlattice (makeIsLattice is-setL ∨l-assoc ∨l-rid (λ x → ∨l-comm _ x ∙ ∨l-rid x) ∨l-comm
                                      ∧l-assoc ∧l-rid (λ x → ∧l-comm _ x ∙ ∧l-rid x) ∧l-comm
                                      ∨l-absorb-∧l ∧l-absorb-∨l)
               (λ x y z → ∨l-ldist-∧l _ _ _ , ∨l-rdist-∧l _ _ _)
               (λ x y z → ∧l-ldist-∨l _ _ _ , ∧l-rdist-∨l _ _ _)
 where
 ∧l-idem : ∀ x → x ∧l x ≡ x
 ∧l-idem x = cong (x ∧l_) (sym (∨l-rid _)) ∙ ∧l-absorb-∨l _ _

 ∨l-absorb-∧l : ∀ x y → x ∨l (x ∧l y) ≡ x
 ∨l-absorb-∧l x y =
              cong (_∨l (x ∧l y)) (sym (∧l-idem _)) ∙∙ sym (∧l-ldist-∨l _ _ _) ∙∙ ∧l-absorb-∨l _ _

 ∧l-rdist-∨l : ∀ x y z → (y ∨l z) ∧l x ≡ (y ∧l x) ∨l (z ∧l x)
 ∧l-rdist-∨l _ _ _ = ∧l-comm _ _ ∙∙ ∧l-ldist-∨l _ _ _ ∙∙ cong₂ (_∨l_) (∧l-comm _ _) (∧l-comm _ _)

 ∨l-ldist-∧l : ∀ x y z → x ∨l (y ∧l z) ≡ (x ∨l y) ∧l (x ∨l z)
 ∨l-ldist-∧l x y z = x ∨l (y ∧l z)
                   ≡⟨ cong (_∨l (y ∧l z)) (sym (∨l-absorb-∧l _ _)) ⟩
                     (x ∨l (x ∧l z)) ∨l (y ∧l z)
                   ≡⟨ sym (∨l-assoc _ _ _) ⟩
                     x ∨l ((x ∧l z) ∨l (y ∧l z))
                   ≡⟨ cong (_∨l ((x ∧l z) ∨l (y ∧l z))) (sym (∧l-comm _ _ ∙ ∧l-absorb-∨l _ _)) ⟩
                     ((x ∨l y) ∧l x) ∨l ((x ∧l z) ∨l (y ∧l z))
                   ≡⟨ cong (((x ∨l y) ∧l x) ∨l_) (sym (∧l-rdist-∨l _ _ _)) ⟩
                     ((x ∨l y) ∧l x) ∨l ((x ∨l y) ∧l z)
                   ≡⟨ sym (∧l-ldist-∨l _ _ _) ⟩
                     (x ∨l y) ∧l (x ∨l z) ∎

 ∨l-rdist-∧l : ∀ x y z → (y ∧l z) ∨l x ≡ (y ∨l x) ∧l (z ∨l x)
 ∨l-rdist-∧l x y z = ∨l-comm _ x ∙∙ ∨l-ldist-∧l _ _ _ ∙∙ cong₂ (_∧l_) (∨l-comm _ _) (∨l-comm _ _)

makeDistLattice∧lOver∨l : {L : Type ℓ} (0l 1l : L) (_∨l_ _∧l_ : L → L → L)
             (is-setL : isSet L)
             (∨l-assoc : (x y z : L) → x ∨l (y ∨l z) ≡ (x ∨l y) ∨l z)
             (∨l-rid : (x : L) → x ∨l 0l ≡ x)
             (∨l-comm : (x y : L) → x ∨l y ≡ y ∨l x)
             (∧l-assoc : (x y z : L) → x ∧l (y ∧l z) ≡ (x ∧l y) ∧l z)
             (∧l-rid : (x : L) → x ∧l 1l ≡ x)
             (∧l-comm : (x y : L) → x ∧l y ≡ y ∧l x)
             (∧l-absorb-∨l : (x y : L) → x ∧l (x ∨l y) ≡ x)
             (∧l-ldist-∨l : (x y z : L) → x ∧l (y ∨l z) ≡ (x ∧l y) ∨l (x ∧l z))
           → DistLattice ℓ
makeDistLattice∧lOver∨l 0l 1l _∨l_ _∧l_ is-setL ∨l-assoc ∨l-rid ∨l-comm
                                                   ∧l-assoc ∧l-rid ∧l-comm
                                                   ∧l-absorb-∨l ∧l-ldist-∨l =
                _ , distlatticestr _ _ _ _
                (makeIsDistLattice∧lOver∨l is-setL ∨l-assoc ∨l-rid ∨l-comm
                                                    ∧l-assoc ∧l-rid ∧l-comm
                                                    ∧l-absorb-∨l ∧l-ldist-∨l)

makeIsDistLattice∨lOver∧l : {L : Type ℓ} {0l 1l : L} {_∨l_ _∧l_ : L → L → L}
                    (is-setL : isSet L)
                    (∨l-assoc : (x y z : L) → x ∨l (y ∨l z) ≡ (x ∨l y) ∨l z)
                    (∨l-rid : (x : L) → x ∨l 0l ≡ x)
                    (∨l-comm : (x y : L) → x ∨l y ≡ y ∨l x)
                    (∧l-assoc : (x y z : L) → x ∧l (y ∧l z) ≡ (x ∧l y) ∧l z)
                    (∧l-rid : (x : L) → x ∧l 1l ≡ x)
                    (∧l-comm : (x y : L) → x ∧l y ≡ y ∧l x)
                    (∨l-absorb-∧l : (x y : L) → x ∨l (x ∧l y) ≡ x)
                    (∨l-ldist-∧l : (x y z : L) → x ∨l (y ∧l z) ≡ (x ∨l y) ∧l (x ∨l z))
                  → IsDistLattice 0l 1l _∨l_ _∧l_
makeIsDistLattice∨lOver∧l {_∨l_ = _∨l_} {_∧l_ = _∧l_} is-setL
                                                      ∨l-assoc ∨l-rid ∨l-comm
                                                      ∧l-assoc ∧l-rid ∧l-comm
                                                      ∨l-absorb-∧l ∨l-ldist-∧l =
  isdistlattice
  (makeIsLattice is-setL ∨l-assoc ∨l-rid (λ x → ∨l-comm _ x ∙ ∨l-rid x) ∨l-comm
                         ∧l-assoc ∧l-rid (λ x → ∧l-comm _ x ∙ ∧l-rid x) ∧l-comm
                         ∨l-absorb-∧l ∧l-absorb-∨l)
                         (λ x y z → ∨l-ldist-∧l _ _ _ , ∨l-rdist-∧l _ _ _)
                         (λ x y z → ∧l-ldist-∨l _ _ _ , ∧l-rdist-∨l _ _ _)
  where
  ∨l-idem : ∀ x → x ∨l x ≡ x
  ∨l-idem x = cong (x ∨l_) (sym (∧l-rid _)) ∙ ∨l-absorb-∧l _ _

  ∧l-absorb-∨l : ∀ x y → x ∧l (x ∨l y) ≡ x
  ∧l-absorb-∨l x y =
    cong (_∧l (x ∨l y)) (sym (∨l-idem _)) ∙∙ sym (∨l-ldist-∧l _ _ _) ∙∙ ∨l-absorb-∧l _ _

  ∨l-rdist-∧l : ∀ x y z → (y ∧l z) ∨l x ≡ (y ∨l x) ∧l (z ∨l x)
  ∨l-rdist-∧l _ _ _ = ∨l-comm _ _ ∙∙ ∨l-ldist-∧l _ _ _ ∙∙ cong₂ (_∧l_) (∨l-comm _ _) (∨l-comm _ _)

  ∧l-ldist-∨l : ∀ x y z → x ∧l (y ∨l z) ≡ (x ∧l y) ∨l (x ∧l z)
  ∧l-ldist-∨l x y z = x ∧l (y ∨l z)
                    ≡⟨ cong (_∧l (y ∨l z)) (sym (∧l-absorb-∨l _ _)) ⟩
                      (x ∧l (x ∨l z)) ∧l (y ∨l z)
                    ≡⟨ sym (∧l-assoc _ _ _) ⟩
                      x ∧l ((x ∨l z) ∧l (y ∨l z))
                    ≡⟨ cong (_∧l ((x ∨l z) ∧l (y ∨l z))) (sym (∨l-comm _ _ ∙ ∨l-absorb-∧l _ _)) ⟩
                      ((x ∧l y) ∨l x) ∧l ((x ∨l z) ∧l (y ∨l z))
                    ≡⟨ cong (((x ∧l y) ∨l x) ∧l_) (sym (∨l-rdist-∧l _ _ _)) ⟩
                      ((x ∧l y) ∨l x) ∧l ((x ∧l y) ∨l z)
                    ≡⟨ sym (∨l-ldist-∧l _ _ _) ⟩
                      (x ∧l y) ∨l (x ∧l z) ∎

  ∧l-rdist-∨l : ∀ x y z → (y ∨l z) ∧l x ≡ (y ∧l x) ∨l (z ∧l x)
  ∧l-rdist-∨l x y z = ∧l-comm _ x ∙∙ ∧l-ldist-∨l _ _ _ ∙∙ cong₂ (_∨l_) (∧l-comm _ _) (∧l-comm _ _)

makeDistLattice∨lOver∧l : {L : Type ℓ} (0l 1l : L) (_∨l_ _∧l_ : L → L → L)
                    (is-setL : isSet L)
                    (∨l-assoc : (x y z : L) → x ∨l (y ∨l z) ≡ (x ∨l y) ∨l z)
                    (∨l-rid : (x : L) → x ∨l 0l ≡ x)
                    (∨l-comm : (x y : L) → x ∨l y ≡ y ∨l x)
                    (∧l-assoc : (x y z : L) → x ∧l (y ∧l z) ≡ (x ∧l y) ∧l z)
                    (∧l-rid : (x : L) → x ∧l 1l ≡ x)
                    (∧l-comm : (x y : L) → x ∧l y ≡ y ∧l x)
                    (∨l-absorb-∧l : (x y : L) → x ∨l (x ∧l y) ≡ x)
                    (∨l-ldist-∧l : (x y z : L) → x ∨l (y ∧l z) ≡ (x ∨l y) ∧l (x ∨l z))
                  → DistLattice ℓ
makeDistLattice∨lOver∧l  0l 1l _∨l_ _∧l_ is-setL ∨l-assoc ∨l-rid ∨l-comm
                                                    ∧l-assoc ∧l-rid ∧l-comm
                                                    ∨l-absorb-∧l ∨l-ldist-∧l =
                _ , distlatticestr _ _ _ _
                (makeIsDistLattice∨lOver∧l is-setL ∨l-assoc ∨l-rid ∨l-comm
                                            ∧l-assoc ∧l-rid ∧l-comm ∨l-absorb-∧l ∨l-ldist-∧l)


DistLatticeStr→LatticeStr : {A : Type ℓ} → DistLatticeStr A → LatticeStr A
DistLatticeStr→LatticeStr (distlatticestr  _ _ _ _ H) =
                           latticestr  _ _ _ _ (IsDistLattice.isLattice H)

DistLattice→Lattice : DistLattice ℓ → Lattice ℓ
DistLattice→Lattice (_ , distlatticestr _ _ _ _  H) =
                     _ , latticestr  _ _ _ _ (IsDistLattice.isLattice H)

DistLatticeHom : (L : DistLattice ℓ) (M : DistLattice ℓ') → Type (ℓ-max ℓ ℓ')
DistLatticeHom L M = LatticeHom (DistLattice→Lattice L) (DistLattice→Lattice M)

idDistLatticeHom : (L : DistLattice ℓ) → DistLatticeHom L L
idDistLatticeHom L = idLatticeHom (DistLattice→Lattice L)

IsDistLatticeEquiv : {A : Type ℓ} {B : Type ℓ'}
  (L : DistLatticeStr A) (e : A ≃ B) (M : DistLatticeStr B) → Type (ℓ-max ℓ ℓ')
IsDistLatticeEquiv L e M =
                   IsLatticeHom (DistLatticeStr→LatticeStr L) (e .fst) (DistLatticeStr→LatticeStr M)

DistLatticeEquiv : (L : DistLattice ℓ) (M : DistLattice ℓ') → Type (ℓ-max ℓ ℓ')
DistLatticeEquiv L M = Σ[ e ∈ (L .fst ≃ M .fst) ] IsDistLatticeEquiv (L .snd) e (M .snd)

isPropIsDistLattice : {L : Type ℓ} (0l 1l : L) (_∨l_ _∧l_ : L → L → L)
             → isProp (IsDistLattice 0l 1l _∨l_ _∧l_)
isPropIsDistLattice 0l 1l _∨l_ _∧l_ (isdistlattice LL LD1 LD2) (isdistlattice ML MD1 MD2) =
  λ i → isdistlattice (isPropIsLattice _ _ _ _ LL ML i) (isPropDist1 LD1 MD1 i)
                                                        (isPropDist2 LD2 MD2 i)
  where
  isSetL : isSet _
  isSetL = LL .IsLattice.joinSemilattice .IsSemilattice.isCommMonoid .IsCommMonoid.isMonoid
              .IsMonoid.isSemigroup .IsSemigroup.is-set

  isPropDist1 : isProp ((x y z : _) → (x ∨l (y ∧l z) ≡ (x ∨l y) ∧l (x ∨l z))
                                    × ((y ∧l z) ∨l x ≡ (y ∨l x) ∧l (z ∨l x)))
  isPropDist1 = isPropΠ3 (λ _ _ _ → isProp× (isSetL _ _) (isSetL _ _))

  isPropDist2 : isProp ((x y z : _) → (x ∧l (y ∨l z) ≡ (x ∧l y) ∨l (x ∧l z))
                                    × ((y ∨l z) ∧l x ≡ (y ∧l x) ∨l (z ∧l x)))
  isPropDist2 = isPropΠ3 (λ _ _ _ → isProp× (isSetL _ _) (isSetL _ _))

𝒮ᴰ-DistLattice : DUARel (𝒮-Univ ℓ) DistLatticeStr ℓ
𝒮ᴰ-DistLattice =
  𝒮ᴰ-Record (𝒮-Univ _) IsDistLatticeEquiv
    (fields:
      data[ 0l ∣ null ∣ pres0 ]
      data[ 1l ∣ null ∣ pres1 ]
      data[ _∨l_ ∣ bin ∣ pres∨l ]
      data[ _∧l_ ∣ bin ∣ pres∧l ]
      prop[ isDistLattice ∣ (λ _ _ → isPropIsDistLattice  _ _ _ _) ])
 where
  open DistLatticeStr
  open IsLatticeHom

  -- faster with some sharing
  null = autoDUARel (𝒮-Univ _) (λ A → A)
  bin = autoDUARel (𝒮-Univ _) (λ A → A → A → A)

DistLatticePath : (L M : DistLattice ℓ) → DistLatticeEquiv L M ≃ (L ≡ M)
DistLatticePath = ∫ 𝒮ᴰ-DistLattice .UARel.ua
