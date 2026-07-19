module Cubical.Algebra.Lattice.Base where

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
open import Cubical.Algebra.Semilattice

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.Reflection.RecordEquiv

open Iso

private
  variable
    ℓ ℓ' : Level


record IsLattice {L : Type ℓ}
                 (0l 1l : L) (_∨l_ _∧l_ : L → L → L) : Type ℓ where

  constructor islattice

  field
   joinSemilattice : IsSemilattice 0l _∨l_
   meetSemilattice : IsSemilattice 1l _∧l_
   absorb : (x y : L) → (x ∨l (x ∧l y) ≡ x)
                      × (x ∧l (x ∨l y) ≡ x)

  open IsSemilattice joinSemilattice public
   renaming
     ( ·Assoc to ∨lAssoc
     ; ·IdL to ∨lLid
     ; ·IdR to ∨lRid
     ; ·Comm to ∨lComm
     ; idem to ∨lIdem
     ; isCommMonoid to ∨lIsCommMonoid
     ; isMonoid to ∨lIsMonoid
     ; isSemigroup to ∨lIsSemigroup )

  open IsSemilattice meetSemilattice public
   renaming
     ( ·Assoc to ∧lAssoc
     ; ·IdL to ∧lLid
     ; ·IdR to ∧lRid
     ; ·Comm to ∧lComm
     ; idem to ∧lIdem
     ; isCommMonoid to ∧lIsCommMonoid
     ; isMonoid to ∧lIsMonoid
     ; isSemigroup to ∧lIsSemigroup )
   hiding
     ( is-set )

  ∨lAbsorb∧l : (x y : L) → x ∨l (x ∧l y) ≡ x
  ∨lAbsorb∧l x y = absorb x y .fst

  ∧lAbsorb∨l : (x y : L) → x ∧l (x ∨l y) ≡ x
  ∧lAbsorb∨l x y = absorb x y .snd

record LatticeStr (A : Type ℓ)  : Type (ℓ-suc ℓ) where

  constructor latticestr

  field
    0l : A
    1l : A
    _∨l_ : A → A → A
    _∧l_ : A → A → A
    isLattice : IsLattice 0l 1l _∨l_ _∧l_

  infix 6 _∨l_
  infix 6 _∧l_

  open IsLattice isLattice public


Lattice : ∀ ℓ → Type (ℓ-suc ℓ)
Lattice ℓ = TypeWithStr ℓ LatticeStr

makeIsLattice : {L : Type ℓ} {0l 1l : L} {_∨l_ _∧l_ : L → L → L}
             (is-setL : isSet L)
             (∨l-assoc : (x y z : L) → x ∨l (y ∨l z) ≡ (x ∨l y) ∨l z)
             (∨l-rid : (x : L) → x ∨l 0l ≡ x)
             (∨l-comm : (x y : L) → x ∨l y ≡ y ∨l x)
             (∧l-assoc : (x y z : L) → x ∧l (y ∧l z) ≡ (x ∧l y) ∧l z)
             (∧l-rid : (x : L) → x ∧l 1l ≡ x)
             (∧l-comm : (x y : L) → x ∧l y ≡ y ∧l x)
             (∨l-absorb-∧l : (x y : L) → x ∨l (x ∧l y) ≡ x)
             (∧l-absorb-∨l : (x y : L) → x ∧l (x ∨l y) ≡ x)
           → IsLattice 0l 1l _∨l_ _∧l_
makeIsLattice {0l = 0l} {1l = 1l} {_∨l_ = _∨l_} {_∧l_ = _∧l_}
              is-setL ∨l-assoc ∨l-rid ∨l-comm
                      ∧l-assoc ∧l-rid ∧l-comm ∨l-absorb-∧l ∧l-absorb-∨l =
     islattice (makeIsSemilattice is-setL ∨l-assoc ∨l-rid ∨l-comm ∨l-idem)
               (makeIsSemilattice is-setL ∧l-assoc ∧l-rid ∧l-comm ∧l-idem)
               λ x y → ∨l-absorb-∧l x y , ∧l-absorb-∨l x y
 where
 ∨l-idem : ∀ x → x ∨l x ≡ x
 ∨l-idem x = cong (x ∨l_) (sym (∧l-rid _)) ∙ ∨l-absorb-∧l _ _

 ∧l-idem : ∀ x → x ∧l x ≡ x
 ∧l-idem x = cong (x ∧l_) (sym (∨l-rid _)) ∙ ∧l-absorb-∨l _ _

makeLattice : {L : Type ℓ} (0l 1l : L) (_∨l_ _∧l_ : L → L → L)
             (is-setL : isSet L)
             (∨l-assoc : (x y z : L) → x ∨l (y ∨l z) ≡ (x ∨l y) ∨l z)
             (∨l-rid : (x : L) → x ∨l 0l ≡ x)
             (∨l-comm : (x y : L) → x ∨l y ≡ y ∨l x)
             (∨l-idem : (x : L) → x ∨l x ≡ x)
             (∧l-assoc : (x y z : L) → x ∧l (y ∧l z) ≡ (x ∧l y) ∧l z)
             (∧l-rid : (x : L) → x ∧l 1l ≡ x)
             (∧l-comm : (x y : L) → x ∧l y ≡ y ∧l x)
             (∧l-idem : (x : L) → x ∧l x ≡ x)
             (∨l-absorb-∧l : (x y : L) → x ∨l (x ∧l y) ≡ x)
             (∧l-absorb-∨l : (x y : L) → x ∧l (x ∨l y) ≡ x)
           → Lattice ℓ
makeLattice 0l 1l _∨l_ _∧l_ is-setL ∨l-assoc ∨l-rid ∨l-comm ∨l-idem
            ∧l-assoc ∧l-rid ∧l-comm ∧l-idem ∨l-absorb-∧l ∧l-absorb-∨l =
   _ , latticestr 0l 1l _∨l_ _∧l_
   (makeIsLattice is-setL ∨l-assoc ∨l-rid ∨l-comm
                          ∧l-assoc ∧l-rid ∧l-comm ∨l-absorb-∧l ∧l-absorb-∨l)

record IsLatticeHom {A : Type ℓ} {B : Type ℓ'} (L : LatticeStr A) (f : A → B) (M : LatticeStr B)
  : Type (ℓ-max ℓ ℓ')
  where

  -- Shorter qualified names
  private
    module L = LatticeStr L
    module M = LatticeStr M

  field
    pres0 : f L.0l ≡ M.0l
    pres1 : f L.1l ≡ M.1l
    pres∨l : (x y : A) → f (x L.∨l y) ≡ f x M.∨l f y
    pres∧l : (x y : A) → f (x L.∧l y) ≡ f x M.∧l f y


unquoteDecl IsLatticeHomIsoΣ = declareRecordIsoΣ IsLatticeHomIsoΣ (quote IsLatticeHom)

LatticeHom : (L : Lattice ℓ) (M : Lattice ℓ') → Type (ℓ-max ℓ ℓ')
LatticeHom L M = Σ[ f ∈ (⟨ L ⟩ → ⟨ M ⟩) ] IsLatticeHom (L .snd) f (M .snd)

idLatticeHom : (L : Lattice ℓ) → LatticeHom L L
fst (idLatticeHom L) x = x
IsLatticeHom.pres0 (snd (idLatticeHom L)) = refl
IsLatticeHom.pres1 (snd (idLatticeHom L)) = refl
IsLatticeHom.pres∨l (snd (idLatticeHom L)) x y = refl
IsLatticeHom.pres∧l (snd (idLatticeHom L)) x y = refl

IsLatticeEquiv : {A : Type ℓ} {B : Type ℓ'} (M : LatticeStr A) (e : A ≃ B) (N : LatticeStr B)
  → Type (ℓ-max ℓ ℓ')
IsLatticeEquiv M e N = IsLatticeHom M (e .fst) N

LatticeEquiv : (L : Lattice ℓ) (M : Lattice ℓ') → Type (ℓ-max ℓ ℓ')
LatticeEquiv L M = Σ[ e ∈ (⟨ L ⟩ ≃ ⟨ M ⟩) ] IsLatticeEquiv (L .snd) e (M .snd)

isPropIsLattice : {L : Type ℓ} (0l 1l : L) (_∨l_ _∧l_ : L → L → L)
             → isProp (IsLattice 0l 1l _∨l_ _∧l_)
isPropIsLattice 0l 1l _∨l_ _∧l_ (islattice LJ LM LA) (islattice MJ MM MA) =
  λ i → islattice (isPropIsSemilattice _ _ LJ MJ i)
                  (isPropIsSemilattice _ _ LM MM i)
                  (isPropAbsorb LA MA i)
  where
  open IsSemilattice LJ using (is-set)

  isPropAbsorb : isProp ((x y : _) → (x ∨l (x ∧l y) ≡ x) × (x ∧l (x ∨l y) ≡ x))
  isPropAbsorb = isPropΠ2 λ _ _ → isProp× (is-set _ _) (is-set _ _)

isPropIsLatticeHom : {A : Type ℓ} {B : Type ℓ'} (R : LatticeStr A) (f : A → B) (S : LatticeStr B)
                   → isProp (IsLatticeHom R f S)
isPropIsLatticeHom R f S = isOfHLevelRetractFromIso 1 IsLatticeHomIsoΣ
                           (isProp×3 (is-set _ _)
                                     (is-set _ _)
                                     (isPropΠ2 λ _ _ → is-set _ _)
                                     (isPropΠ2 λ _ _ → is-set _ _))
  where
  open LatticeStr S


isSetLatticeHom : (A : Lattice ℓ) (B : Lattice ℓ') → isSet (LatticeHom A B)
isSetLatticeHom A B = isSetΣSndProp (isSetΠ λ _ → is-set) (λ f → isPropIsLatticeHom (snd A) f (snd B))
  where
  open LatticeStr (str B) using (is-set)

isSetLatticeEquiv : (A : Lattice ℓ) (B : Lattice ℓ') → isSet (LatticeEquiv A B)
isSetLatticeEquiv A B = isSetΣSndProp (isOfHLevel≃ 2 A.is-set B.is-set)
                                      (λ e → isPropIsLatticeHom (snd A) (fst e) (snd B))
  where
  module A = LatticeStr (str A)
  module B = LatticeStr (str B)


𝒮ᴰ-Lattice : DUARel (𝒮-Univ ℓ) LatticeStr ℓ
𝒮ᴰ-Lattice =
  𝒮ᴰ-Record (𝒮-Univ _) IsLatticeEquiv
    (fields:
      data[ 0l ∣ null ∣ pres0 ]
      data[ 1l ∣ null ∣ pres1 ]
      data[ _∨l_ ∣ bin ∣ pres∨l ]
      data[ _∧l_ ∣ bin ∣ pres∧l ]
      prop[ isLattice ∣ (λ _ _ → isPropIsLattice _ _ _ _) ])
 where
  open LatticeStr
  open IsLatticeHom

  -- faster with some sharing
  null = autoDUARel (𝒮-Univ _) (λ A → A)
  bin = autoDUARel (𝒮-Univ _) (λ A → A → A → A)

LatticePath : (L M : Lattice ℓ) → LatticeEquiv L M ≃ (L ≡ M)
LatticePath = ∫ 𝒮ᴰ-Lattice .UARel.ua


Lattice→JoinSemilattice : Lattice ℓ → Semilattice ℓ
Lattice→JoinSemilattice (A , latticestr _ _ _ _ L) = semilattice _ _ _ (L .IsLattice.joinSemilattice )

LatticeHom→JoinSemilatticeHom : {L : Lattice ℓ} {L' : Lattice ℓ'}
   → LatticeHom L L'
   → SemilatticeHom (Lattice→JoinSemilattice L) (Lattice→JoinSemilattice L')
fst (LatticeHom→JoinSemilatticeHom φ) = fst φ
IsMonoidHom.presε (snd (LatticeHom→JoinSemilatticeHom φ)) = φ .snd .IsLatticeHom.pres0
IsMonoidHom.pres· (snd (LatticeHom→JoinSemilatticeHom φ)) = φ .snd .IsLatticeHom.pres∨l

Lattice→MeetSemilattice : Lattice ℓ → Semilattice ℓ
Lattice→MeetSemilattice (A , latticestr _ _ _ _ L) = semilattice _ _ _ (L .IsLattice.meetSemilattice )

LatticeHom→MeetSemilatticeHom : {L : Lattice ℓ} {L' : Lattice ℓ'}
   → LatticeHom L L'
   → SemilatticeHom (Lattice→MeetSemilattice L) (Lattice→MeetSemilattice L')
fst (LatticeHom→MeetSemilatticeHom φ) = fst φ
IsMonoidHom.presε (snd (LatticeHom→MeetSemilatticeHom φ)) = φ .snd .IsLatticeHom.pres1
IsMonoidHom.pres· (snd (LatticeHom→MeetSemilatticeHom φ)) = φ .snd .IsLatticeHom.pres∧l
