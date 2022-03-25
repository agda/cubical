{-

This file contains:
- The quotient of finite sets by decidable equivalence relation is still finite, by using equivalence class.

-}
{-# OPTIONS --safe #-}

module Cubical.Data.FinSet.Quotients where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)

open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.HITs.SetQuotients as SetQuot
open import Cubical.HITs.SetQuotients.EqClass

open import Cubical.Data.Sigma

open import Cubical.Data.FinSet.Base
open import Cubical.Data.FinSet.Properties
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.FinSet.Cardinality

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidablePropositions
open import Cubical.Relation.Binary

private
  variable
    ℓ ℓ' ℓ'' : Level

open Iso

module _
  (ℓ : Level) where

  Iso-DecProp-FinProp : Iso (DecProp ℓ) (FinProp ℓ)
  Iso-DecProp-FinProp .fun ((P , p) , dec) = (P , isDecProp→isFinSet p dec) , p
  Iso-DecProp-FinProp .inv ((P , h) , p) = (P , p) , isFinProp→Dec h p
  Iso-DecProp-FinProp .leftInv ((P , p) , dec) i .fst .fst = P
  Iso-DecProp-FinProp .leftInv ((P , p) , dec) i .fst .snd = p
  Iso-DecProp-FinProp .leftInv ((P , p) , dec) i .snd =
    isProp→PathP {B = λ i → Dec P}
      (λ i → isPropDec (Iso-DecProp-FinProp .leftInv ((P , p) , dec) i .fst .snd))
      (Iso-DecProp-FinProp .inv (Iso-DecProp-FinProp .fun ((P , p) , dec)) .snd) dec i
  Iso-DecProp-FinProp .rightInv ((P , h) , p) i .fst .fst = P
  Iso-DecProp-FinProp .rightInv ((P , h) , p) i .fst .snd =
    isProp→PathP {B = λ i → isFinSet P} (λ i → isPropIsFinSet)
      (Iso-DecProp-FinProp .fun (Iso-DecProp-FinProp .inv ((P , h) , p)) .fst .snd) h i
  Iso-DecProp-FinProp .rightInv ((P , h) , p) i .snd = p

module _
    {ℓ ℓ' : Level}
    (X : Type ℓ) where

    ℙFin : Type (ℓ-max ℓ (ℓ-suc ℓ'))
    ℙFin = X → FinProp ℓ'

    isSetℙFin : isSet ℙFin
    isSetℙFin = isSetΠ (λ _ → isSetFinProp)

    ℙFin→ℙDec :  ℙFin → ℙDec {ℓ' = ℓ'} X
    ℙFin→ℙDec P .fst x = P x .fst .fst , P x .snd
    ℙFin→ℙDec P .snd x = isFinProp→Dec (P x .fst .snd) (P x .snd)

    Iso-ℙFin-ℙDec : Iso ℙFin (ℙDec {ℓ' = ℓ'} X)
    Iso-ℙFin-ℙDec .fun = ℙFin→ℙDec
    Iso-ℙFin-ℙDec .inv (P , dec) x .fst .fst = P x .fst
    Iso-ℙFin-ℙDec .inv (P , dec) x .fst .snd = isDecProp→isFinSet (P x .snd) (dec x)
    Iso-ℙFin-ℙDec .inv (P , dec) x .snd = P x .snd
    Iso-ℙFin-ℙDec .leftInv P i x .fst .fst = P x .fst .fst
    Iso-ℙFin-ℙDec .leftInv P i x .fst .snd =
      isProp→PathP {B = λ i → isFinSet (P x .fst .fst)} (λ i → isPropIsFinSet)
        (isDecProp→isFinSet (P x .snd) (ℙFin→ℙDec P .snd x)) (P x .fst .snd) i
    Iso-ℙFin-ℙDec .leftInv P i x .snd = P x .snd
    Iso-ℙFin-ℙDec .rightInv (P , dec) i .fst x = P x .fst , P x .snd
    Iso-ℙFin-ℙDec .rightInv (P , dec) i .snd x =
      isProp→PathP {B = λ i → Dec (P x .fst)} (λ i → isPropDec (P x .snd))
        (Iso-ℙFin-ℙDec .fun (Iso-ℙFin-ℙDec .inv (P , dec)) .snd x) (dec x) i

    ℙFin≃ℙDec : ℙFin ≃ (ℙDec {ℓ' = ℓ'} X)
    ℙFin≃ℙDec = isoToEquiv Iso-ℙFin-ℙDec

module _
  (X : FinSet ℓ) where

  isFinSetℙFin : isFinSet (ℙFin {ℓ' = ℓ'} (X .fst))
  isFinSetℙFin = isFinSet→ X (_ , isFinSetFinProp)

open BinaryRelation

module _
  (X : FinSet ℓ)
  (R : X .fst → X .fst → Type ℓ')
  (dec : (x x' : X .fst) → Dec (R x x')) where

  _∥Fin_ : Type (ℓ-max ℓ (ℓ-suc ℓ'))
  _∥Fin_ = Σ[ P ∈ ℙFin {ℓ' = ℓ'} (X .fst) ] isEqClass (X .fst) R (ℙFin→ℙDec (X .fst) P .fst)

  isFinSetIsEqClass : (P : ℙFin {ℓ' = ℓ'} (X .fst))
    → isFinSet (isEqClass (X .fst) R (ℙFin→ℙDec (X .fst) P .fst))
  isFinSetIsEqClass P =
    isFinSet∥∥ (_ , isFinSetΣ X (λ x → _ ,
      isFinSetΠ X (λ a → _ ,
        isFinSetType≡ (_ , P a .fst .snd) (_ ,
          isDec→isFinSet∥∥ (dec a x)))))

  ∥Fin≃∥Dec : _∥Fin_ ≃ _∥Dec_ (X .fst) R dec
  ∥Fin≃∥Dec = Σ-cong-equiv-fst (ℙFin≃ℙDec (X .fst))

  isFinSet∥Fin : isFinSet _∥Fin_
  isFinSet∥Fin = isFinSetΣ (_ , isFinSetℙFin X) (λ P → _ , isFinSetIsEqClass P)

module _
  (X : FinSet ℓ)
  (R : X .fst → X .fst → Type ℓ')
  (h : isEquivRel R)
  (dec : (x x' : X .fst) → Dec (R x x')) where

  -- the quotient of finite set by decidable equivalence relation is still finite set
  isFinSetQuot : isFinSet (X .fst / R)
  isFinSetQuot =
    EquivPresIsFinSet
      (∥Fin≃∥Dec X _ dec ⋆ ∥Dec≃∥ _ _ dec ⋆ invEquiv (equivQuot _ _ h)) (isFinSet∥Fin X _ dec)
