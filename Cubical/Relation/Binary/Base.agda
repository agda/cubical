{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Base where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Fiberwise
open import Cubical.Data.Sigma
open import Cubical.HITs.SetQuotients.Base
open import Cubical.HITs.PropositionalTruncation.Base

private
  variable
    ℓA ℓ≅A ℓA' ℓ≅A' : Level

Rel : ∀ {ℓ} (A B : Type ℓ) (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
Rel A B ℓ' = A → B → Type ℓ'

PropRel : ∀ {ℓ} (A B : Type ℓ) (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
PropRel A B ℓ' = Σ[ R ∈ Rel A B ℓ' ] ∀ a b → isProp (R a b)

idPropRel : ∀ {ℓ} (A : Type ℓ) → PropRel A A ℓ
idPropRel A .fst a a' = ∥ a ≡ a' ∥
idPropRel A .snd _ _ = squash

invPropRel : ∀ {ℓ ℓ'} {A B : Type ℓ}
  → PropRel A B ℓ' → PropRel B A ℓ'
invPropRel R .fst b a = R .fst a b
invPropRel R .snd b a = R .snd a b

compPropRel : ∀ {ℓ ℓ' ℓ''} {A B C : Type ℓ}
  → PropRel A B ℓ' → PropRel B C ℓ'' → PropRel A C (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
compPropRel R S .fst a c = ∥ Σ[ b ∈ _ ] (R .fst a b × S .fst b c) ∥
compPropRel R S .snd _ _ = squash

graphRel : ∀ {ℓ} {A B : Type ℓ} → (A → B) → Rel A B ℓ
graphRel f a b = f a ≡ b

module BinaryRelation {ℓ ℓ' : Level} {A : Type ℓ} (R : Rel A A ℓ') where
  isRefl : Type (ℓ-max ℓ ℓ')
  isRefl = (a : A) → R a a

  isSym : Type (ℓ-max ℓ ℓ')
  isSym = (a b : A) → R a b → R b a

  isAntisym : Type (ℓ-max ℓ ℓ')
  isAntisym = (a b : A) → R a b → R b a → a ≡ b

  isTrans : Type (ℓ-max ℓ ℓ')
  isTrans = (a b c : A)  → R a b → R b c → R a c

  record isEquivRel : Type (ℓ-max ℓ ℓ') where
    constructor equivRel
    field
      reflexive : isRefl
      symmetric : isSym
      transitive : isTrans

  isPropValued : Type (ℓ-max ℓ ℓ')
  isPropValued = (a b : A) → isProp (R a b)

  isSetValued : Type (ℓ-max ℓ ℓ')
  isSetValued = (a b : A) → isSet (R a b)

  isEffective : Type (ℓ-max ℓ ℓ')
  isEffective =
    (a b : A) → isEquiv (eq/ {R = R} a b)


  impliesIdentity : Type _
  impliesIdentity = {a a' : A} → (R a a') → (a ≡ a')

  -- the total space corresponding to the binary relation w.r.t. a
  relSinglAt : (a : A) → Type (ℓ-max ℓ ℓ')
  relSinglAt a = Σ[ a' ∈ A ] (R a a')

  -- the statement that the total space is contractible at any a
  contrRelSingl : Type (ℓ-max ℓ ℓ')
  contrRelSingl = (a : A) → isContr (relSinglAt a)

  isUnivalent : Type (ℓ-max ℓ ℓ')
  isUnivalent = (a a' : A) → (R a a') ≃ (a ≡ a')

  contrRelSingl→isUnivalent : isRefl → contrRelSingl → isUnivalent
  contrRelSingl→isUnivalent ρ c a a' = isoToEquiv i
    where
      h : isProp (relSinglAt a)
      h = isContr→isProp (c a)
      aρa : relSinglAt a
      aρa = a , ρ a
      Q : (y : A) → a ≡ y → _
      Q y _ = R a y
      i : Iso (R a a') (a ≡ a')
      Iso.fun i r = cong fst (h aρa (a' , r))
      Iso.inv i = J Q (ρ a)
      Iso.rightInv i = J (λ y p → cong fst (h aρa (y , J Q (ρ a) p)) ≡ p)
                         (J (λ q _ → cong fst (h aρa (a , q)) ≡ refl)
                           (J (λ α _ → cong fst α ≡ refl) refl
                             (isProp→isSet h _ _ refl (h _ _)))
                           (sym (JRefl Q (ρ a))))
      Iso.leftInv i r = J (λ w β → J Q (ρ a) (cong fst β) ≡ snd w)
                          (JRefl Q (ρ a)) (h aρa (a' , r))

  isUnivalent→contrRelSingl : isUnivalent → contrRelSingl
  isUnivalent→contrRelSingl u a = q
    where
      abstract
        f : (x : A) → a ≡ x → R a x
        f x p = invEq (u a x) p

        t : singl a → relSinglAt a
        t (x , p) = x , f x p

        q : isContr (relSinglAt a)
        q = isOfHLevelRespectEquiv 0 (t , totalEquiv _ _ f λ x → invEquiv (u a x) .snd)
                                   (isContrSingl a)

EquivRel : ∀ {ℓ} (A : Type ℓ) (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
EquivRel A ℓ' = Σ[ R ∈ Rel A A ℓ' ] BinaryRelation.isEquivRel R

EquivPropRel : ∀ {ℓ} (A : Type ℓ) (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
EquivPropRel A ℓ' = Σ[ R ∈ PropRel A A ℓ' ] BinaryRelation.isEquivRel (R .fst)

record RelIso {A : Type ℓA} (_≅_ : Rel A A ℓ≅A)
              {A' : Type ℓA'} (_≅'_ : Rel A' A' ℓ≅A') : Type (ℓ-max (ℓ-max ℓA ℓA') (ℓ-max ℓ≅A ℓ≅A')) where
  constructor reliso
  field
    fun : A → A'
    inv : A' → A
    rightInv : (a' : A') → fun (inv a') ≅' a'
    leftInv : (a : A) → inv (fun a) ≅ a

open BinaryRelation

RelIso→Iso : {A : Type ℓA} {A' : Type ℓA'}
             (_≅_ : Rel A A ℓ≅A) (_≅'_ : Rel A' A' ℓ≅A')
             (uni : impliesIdentity _≅_) (uni' : impliesIdentity _≅'_)
             (f : RelIso _≅_ _≅'_)
             → Iso A A'
Iso.fun (RelIso→Iso _ _ _ _ f) = RelIso.fun f
Iso.inv (RelIso→Iso _ _ _ _ f) = RelIso.inv f
Iso.rightInv (RelIso→Iso _ _ uni uni' f) a'
  = uni' (RelIso.rightInv f a')
Iso.leftInv (RelIso→Iso _ _ uni uni' f) a
  = uni (RelIso.leftInv f a)
