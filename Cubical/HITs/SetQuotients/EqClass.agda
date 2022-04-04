{-# OPTIONS --safe #-}

module Cubical.HITs.SetQuotients.EqClass where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.HITs.SetQuotients as SetQuot

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary

open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection

private
  variable
    ℓ ℓ' ℓ'' : Level

-- another definition using equivalence classes

open BinaryRelation
open isEquivRel

open Iso

module _
  {ℓ ℓ' : Level}
  (X : Type ℓ) where

  ℙ : Type (ℓ-max ℓ (ℓ-suc ℓ'))
  ℙ = X → hProp ℓ'

  ℙDec : Type (ℓ-max ℓ (ℓ-suc ℓ'))
  ℙDec = Σ[ P ∈ ℙ ] ((x : X) → Dec (P x .fst))

  isSetℙ : isSet ℙ
  isSetℙ = isSetΠ λ x → isSetHProp

  isSetℙDec : isSet ℙDec
  isSetℙDec = isOfHLevelΣ 2 isSetℙ (λ P → isSetΠ (λ x → isProp→isSet (isPropDec (P x .snd))))

  module _
    (R : X → X → Type ℓ'') where

    isEqClass : ℙ → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    isEqClass P = ∥ Σ[ x ∈ X ] ((a : X) → P a .fst ≃ ∥ R a x ∥) ∥

    isPropIsEqClass : (P : ℙ) → isProp (isEqClass P)
    isPropIsEqClass P = isPropPropTrunc

    _∥_ : Type (ℓ-max (ℓ-max ℓ (ℓ-suc ℓ')) ℓ'')
    _∥_ = Σ[ P ∈ ℙ ] isEqClass P

    isSet∥ : isSet _∥_
    isSet∥ = isOfHLevelΣ 2 isSetℙ (λ _ → isProp→isSet isPropPropTrunc)

    module _
      (dec : (x x' : X) → Dec (R x x')) where

      _∥Dec_ : Type (ℓ-max (ℓ-max ℓ (ℓ-suc ℓ')) ℓ'')
      _∥Dec_ = Σ[ P ∈ ℙDec ] isEqClass (P .fst)

      isDecEqClass : (P : _∥_) → (x : X) → Dec (P .fst x .fst)
      isDecEqClass (P , h) a =
        Prop.rec (isPropDec (P a .snd)) (λ (x , p) → EquivPresDec (invEquiv (p a)) (Dec∥∥ (dec a x))) h

      Iso-∥Dec-∥ : Iso _∥Dec_ _∥_
      Iso-∥Dec-∥ .fun P = P .fst .fst , P .snd
      Iso-∥Dec-∥ .inv P = (P .fst , isDecEqClass P) , P .snd
      Iso-∥Dec-∥ .rightInv P = refl
      Iso-∥Dec-∥ .leftInv P i .fst .fst = P .fst .fst
      Iso-∥Dec-∥ .leftInv P i .fst .snd x =
        isProp→PathP {B = λ i → Dec (P .fst .fst x .fst)}
          (λ i → isPropDec (P .fst .fst x .snd))
          (isDecEqClass (Iso-∥Dec-∥ .fun P) x) (P .fst .snd x) i
      Iso-∥Dec-∥ .leftInv P i .snd = P .snd

      ∥Dec≃∥ : _∥Dec_ ≃ _∥_
      ∥Dec≃∥ = isoToEquiv Iso-∥Dec-∥

module _
  {ℓ ℓ' ℓ'' : Level}
  (X : Type ℓ)
  (R : X → X → Type ℓ'')
  (h : isEquivRel R) where

  ∥Rx∥Iso : (x x' : X)(r : R x x') → (a : X) → Iso ∥ R a x ∥ ∥ R a x' ∥
  ∥Rx∥Iso x x' r a .fun = Prop.rec isPropPropTrunc (λ r' → ∣ h .transitive _ _ _ r' r ∣)
  ∥Rx∥Iso x x' r a .inv = Prop.rec isPropPropTrunc (λ r' → ∣ h .transitive _ _ _ r' (h .symmetric _ _ r) ∣)
  ∥Rx∥Iso x x' r a .leftInv _ = isPropPropTrunc _ _
  ∥Rx∥Iso x x' r a .rightInv _ = isPropPropTrunc _ _

  isEqClass∥Rx∥ : (x : X) → isEqClass X R (λ a → ∥ R a x ∥ , isPropPropTrunc)
  isEqClass∥Rx∥ x = ∣ x , (λ _ → idEquiv _) ∣

  ∥R∥ : (x : X) → X ∥ R
  ∥R∥ x = (λ a → ∥ R a x ∥ , isPropPropTrunc) , isEqClass∥Rx∥ x

  ∥Rx∥Path : (x x' : X)(r : R x x') → ∥R∥ x ≡ ∥R∥ x'
  ∥Rx∥Path x x' r i .fst a .fst = ua (isoToEquiv (∥Rx∥Iso x x' r a)) i
  ∥Rx∥Path x x' r i .fst a .snd =
    isProp→PathP {B = λ i → isProp (∥Rx∥Path x x' r i .fst a .fst)}
                 (λ i → isPropIsProp) isPropPropTrunc isPropPropTrunc i
  ∥Rx∥Path x x' r i .snd =
    isProp→PathP {B = λ i → isEqClass X R (∥Rx∥Path x x' r i .fst)}
                 (λ i → isPropIsEqClass X R (∥Rx∥Path x x' r i .fst))
                 (isEqClass∥Rx∥ x) (isEqClass∥Rx∥ x') i

  /→∥ : X / R → X ∥ R
  /→∥ = SetQuot.rec (isSet∥ X R) ∥R∥ (λ x x' r → ∥Rx∥Path x x' r)

  inj/→∥' : (x x' : X) → ∥R∥ x ≡ ∥R∥ x' → ∥ R x x' ∥
  inj/→∥' x x' p = transport (λ i → p i .fst x .fst) ∣ h .reflexive x ∣

  inj/→∥ : (x y : X / R) → /→∥ x ≡ /→∥ y → x ≡ y
  inj/→∥ =
    SetQuot.elimProp2 {P = λ x y → /→∥ x ≡ /→∥ y → x ≡ y}
      (λ _ _ → isPropΠ (λ _ → squash/ _ _))
      (λ x y q → Prop.rec (squash/ _ _) (λ r → eq/ _ _ r) (inj/→∥' x y q))

  isEmbedding/→∥ : isEmbedding /→∥
  isEmbedding/→∥ = injEmbedding squash/ (isSet∥ X R) (λ {x} {y} → inj/→∥ x y)

  surj/→∥ : (P : X ∥ R) → ((x , _) : Σ[ x ∈ X ] ((a : X) → P .fst a .fst ≃ ∥ R a x ∥)) → ∥R∥ x ≡ P
  surj/→∥ P (x , p) i .fst a .fst = ua (p a) (~ i)
  surj/→∥ P (x , p) i .fst a .snd =
    isProp→PathP {B = λ i → isProp (surj/→∥ P (x , p) i .fst a .fst)}
                 (λ i → isPropIsProp) isPropPropTrunc (P .fst a .snd) i
  surj/→∥ P (x , p) i .snd =
    isProp→PathP {B = λ i → isEqClass X R (surj/→∥ P (x , p) i .fst)}
                 (λ i → isPropIsEqClass X R (surj/→∥ P (x , p) i .fst))
                 (isEqClass∥Rx∥ x) (P .snd) i

  isSurjection/→∥ : isSurjection /→∥
  isSurjection/→∥ P = Prop.rec isPropPropTrunc (λ p → ∣ [ p .fst ] , surj/→∥ P p ∣) (P .snd)

  -- both definitions are equivalent
  equivQuot : X / R ≃ X ∥ R
  equivQuot = /→∥ , isEmbedding×isSurjection→isEquiv (isEmbedding/→∥ , isSurjection/→∥)
