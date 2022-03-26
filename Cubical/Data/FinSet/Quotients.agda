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
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Univalence

open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.HITs.SetQuotients as SetQuot
open import Cubical.HITs.SetQuotients.EqClass

open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Sigma

open import Cubical.Data.SumFin
open import Cubical.Data.FinSet.Base
open import Cubical.Data.FinSet.Properties
open import Cubical.Data.FinSet.DecidablePredicate
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.FinSet.Cardinality

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidablePropositions
open import Cubical.Relation.Binary

private
  variable
    ℓ ℓ' ℓ'' : Level

LiftDecProp : {ℓ ℓ' : Level}{P : Type ℓ} → (p : isDecProp P) → P ≃ Bool→Type* {ℓ'} (p .fst)
LiftDecProp p = p .snd ⋆ BoolProp≃BoolProp*

open Iso

module _
  (X : Type ℓ) where

  ℙEff : Type ℓ
  ℙEff = X → Bool

  isSetℙEff : isSet ℙEff
  isSetℙEff = isSetΠ (λ _ → isSetBool)

  ℙEff→ℙDec : ℙEff → ℙDec {ℓ' = ℓ'} X
  ℙEff→ℙDec f .fst x = Bool→Type* (f x) , isPropBool→Type*
  ℙEff→ℙDec f .snd x = DecBool→Type*

  Iso-ℙEff-ℙDec : Iso ℙEff (ℙDec {ℓ' = ℓ'} X)
  Iso-ℙEff-ℙDec .fun = ℙEff→ℙDec
  Iso-ℙEff-ℙDec .inv (P , dec) x = Dec→Bool (dec x)
  Iso-ℙEff-ℙDec {ℓ' = ℓ'} .leftInv f i x = Bool≡BoolDec* {ℓ = ℓ'} {a = f x} (~ i)
  Iso-ℙEff-ℙDec .rightInv (P , dec) i .fst x .fst = ua (Dec≃DecBool* (P x .snd) (dec x)) (~ i)
  Iso-ℙEff-ℙDec .rightInv (P , dec) i .fst x .snd =
    isProp→PathP {B = λ i → isProp (Iso-ℙEff-ℙDec .rightInv (P , dec) i .fst x .fst)}
      (λ i → isPropIsProp)
      (Iso-ℙEff-ℙDec .fun (Iso-ℙEff-ℙDec .inv (P , dec)) .fst x .snd) (P x .snd) i
  Iso-ℙEff-ℙDec .rightInv (P , dec) i .snd x =
    isProp→PathP {B = λ i → Dec (Iso-ℙEff-ℙDec .rightInv (P , dec) i .fst x .fst)}
      (λ i → isPropDec (Iso-ℙEff-ℙDec .rightInv (P , dec) i .fst x .snd))
      (Iso-ℙEff-ℙDec .fun (Iso-ℙEff-ℙDec .inv (P , dec)) .snd x) (dec x) i

  ℙEff≃ℙDec : ℙEff ≃ (ℙDec {ℓ' = ℓ'} X)
  ℙEff≃ℙDec = isoToEquiv Iso-ℙEff-ℙDec

module _
  (X : Type ℓ)(p : isFinOrd X) where

  private
    e = p .snd

  isFinOrdℙEff : isFinOrd (ℙEff X)
  isFinOrdℙEff = _ , preCompEquiv (invEquiv e) ⋆ SumFinℙ≃ _

module _
  (X : FinSet ℓ) where

  isFinSetℙEff : isFinSet (ℙEff (X .fst))
  isFinSetℙEff = 2 ^ (card X) ,
    Prop.elim (λ _ → isPropPropTrunc {A = _ ≃ Fin _})
      (λ p → ∣ isFinOrdℙEff (X .fst) (_ , p) .snd ∣)
      (X .snd .snd)

module _
  (X : FinSet ℓ)
  (R : X .fst → X .fst → Type ℓ')
  (dec : (x x' : X .fst) → isDecProp (R x x')) where

  isEqClassEff : ℙEff (X .fst) → Type ℓ
  isEqClassEff f = ∥ Σ[ x ∈ X .fst ] ((a : X .fst) → f a ≡ dec a x .fst) ∥

  isDecPropIsEqClassEff : {f : ℙEff (X .fst)} → isDecProp (isEqClassEff f)
  isDecPropIsEqClassEff = isDecProp∃ X (λ _ → _ , isDecProp∀ X (λ _ → _ , _ , Bool≡≃ _ _))

  isEqClassEff→isEqClass' : (f : ℙEff (X .fst))(x : X .fst)
    → ((a : X .fst) → f a ≡ dec a x .fst)
    → (a : X .fst) → Bool→Type* {ℓ = ℓ'} (f a) ≃ ∥ R a x ∥
  isEqClassEff→isEqClass' f x h a =
      pathToEquiv (cong Bool→Type* (h a))
    ⋆ invEquiv (LiftDecProp (dec a x))
    ⋆ invEquiv (propTruncIdempotent≃ (isDecProp→isProp (dec a x)))

  isEqClass→isEqClassEff' : (f : ℙEff (X .fst))(x : X .fst)
    → ((a : X .fst) → Bool→Type* {ℓ = ℓ'} (f a) ≃ ∥ R a x ∥)
    → (a : X .fst) → f a ≡ dec a x .fst
  isEqClass→isEqClassEff' f x h a =
    Bool→TypeInj* _ _
        (h a ⋆ propTruncIdempotent≃ (isDecProp→isProp (dec a x)) ⋆ LiftDecProp (dec a x))

  isEqClassEff→isEqClass : (f : ℙEff (X .fst)) → isEqClassEff f ≃ isEqClass {ℓ' = ℓ'} _ R (ℙEff→ℙDec  _ f .fst)
  isEqClassEff→isEqClass f =
    propBiimpl→Equiv isPropPropTrunc isPropPropTrunc
      (Prop.map (λ (x , p) → x , isEqClassEff→isEqClass' f x p))
      (Prop.map (λ (x , p) → x , isEqClass→isEqClassEff' f x p))

  _∥Eff_ : Type ℓ
  _∥Eff_ = Σ[ f ∈ ℙEff (X .fst) ] isEqClassEff f

  ∥Eff≃∥Dec : _∥Eff_ ≃ _∥Dec_ (X .fst) R (λ x x' → isDecProp→Dec (dec x x'))
  ∥Eff≃∥Dec = Σ-cong-equiv (ℙEff≃ℙDec (X .fst)) isEqClassEff→isEqClass

  isFinSet∥Eff : isFinSet _∥Eff_
  isFinSet∥Eff = isFinSetSub (_ , isFinSetℙEff X) (λ _ → _ , isDecPropIsEqClassEff)

open BinaryRelation

module _
  (X : FinSet ℓ)
  (R : X .fst → X .fst → Type ℓ')
  (h : isEquivRel R)
  (dec : (x x' : X .fst) → isDecProp (R x x')) where

  isFinSetQuot : isFinSet (X .fst / R)
  isFinSetQuot =
    EquivPresIsFinSet
      ( ∥Eff≃∥Dec X _ dec
      ⋆ ∥Dec≃∥ _ _ (λ x x' → isDecProp→Dec (dec x x'))
      ⋆ invEquiv (equivQuot {ℓ' = ℓ'} _ _ h))
      (isFinSet∥Eff X _ dec)
