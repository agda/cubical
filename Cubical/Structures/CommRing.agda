{-# OPTIONS --cubical --safe #-}

module Cubical.Structures.CommRing where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)

open import Cubical.Structures.NAryOp
open import Cubical.Structures.Pointed
open import Cubical.Structures.Ring hiding (⟨_⟩)

private
  variable
    ℓ ℓ' : Level

comm-ring-axioms : (X : Type ℓ) (s : raw-ring-structure X) → Type ℓ
comm-ring-axioms X (_+_ , ₁ , _·_) = (ring-axioms X (_+_ , ₁ , _·_)) ×
                                     ((x y : X) → x · y ≡ y · x)

comm-ring-structure : Type ℓ → Type ℓ
comm-ring-structure = add-to-structure raw-ring-structure comm-ring-axioms


CommRing : Type (ℓ-suc ℓ)
CommRing {ℓ} = TypeWithStr ℓ comm-ring-structure

comm-ring-iso : StrIso comm-ring-structure ℓ
comm-ring-iso = add-to-iso (join-iso (nAryFunIso 2) (join-iso pointed-iso (nAryFunIso 2))) comm-ring-axioms

comm-ring-axioms-isProp : (X : Type ℓ) (s : raw-ring-structure X) → isProp (comm-ring-axioms X s)
comm-ring-axioms-isProp X (_·_ , ₀ , _+_) = isPropΣ (ring-axioms-isProp X (_·_ , ₀ , _+_))
                                            λ ((((isSetX , _) , _) , _) , _) → isPropΠ2 λ _ _ → isSetX _ _

comm-ring-is-SNS : SNS {ℓ} comm-ring-structure comm-ring-iso
comm-ring-is-SNS = add-axioms-SNS _ comm-ring-axioms-isProp raw-ring-is-SNS

CommRingPath : (M N : CommRing {ℓ}) → (M ≃[ comm-ring-iso ] N) ≃ (M ≡ N)
CommRingPath = SIP comm-ring-is-SNS

-- CommRing is Ring

CommRing→Ring : CommRing {ℓ} → Ring
CommRing→Ring (R , str , isRing , ·comm) = R , str , isRing

-- CommRing Extractors

⟨_⟩ : CommRing {ℓ} → Type ℓ
⟨ R , _ ⟩ = R

module _ (R : CommRing {ℓ}) where

  commring+-operation = ring+-operation (CommRing→Ring R)

  commring-is-set = ring-is-set (CommRing→Ring R)

  commring+-assoc = ring+-assoc (CommRing→Ring R)

  commring+-id = ring+-id (CommRing→Ring R)

  commring+-rid = ring+-rid (CommRing→Ring R)

  commring+-lid = ring+-lid (CommRing→Ring R)

  commring+-inv = ring+-inv (CommRing→Ring R)

  commring+-rinv = ring+-rinv (CommRing→Ring R)

  commring+-linv = ring+-linv (CommRing→Ring R)

  commring+-comm = ring+-comm (CommRing→Ring R)

  commring·-operation = ring·-operation (CommRing→Ring R)

  commring·-assoc = ring·-assoc (CommRing→Ring R)

  commring·-id = ring·-id (CommRing→Ring R)

  commring·-rid = ring·-rid (CommRing→Ring R)

  commring·-lid = ring·-lid (CommRing→Ring R)

  commring-ldist = ring-ldist (CommRing→Ring R)

  commring-rdist = ring-rdist (CommRing→Ring R)

module commring-operation-syntax where

  commring+-operation-syntax : (R : CommRing {ℓ}) → ⟨ R ⟩ → ⟨ R ⟩ → ⟨ R ⟩
  commring+-operation-syntax R = commring+-operation R
  infixr 14 commring+-operation-syntax
  syntax commring+-operation-syntax G x y = x +⟨ G ⟩ y

  commring·-operation-syntax : (R : CommRing {ℓ}) → ⟨ R ⟩ → ⟨ R ⟩ → ⟨ R ⟩
  commring·-operation-syntax R = commring·-operation R
  infixr 18 commring·-operation-syntax
  syntax commring·-operation-syntax G x y = x ·⟨ G ⟩ y

open commring-operation-syntax

commring-comm : (R : CommRing {ℓ}) (x y : ⟨ R ⟩) → x ·⟨ R ⟩ y ≡ y ·⟨ R ⟩ x
commring-comm (_ , _ , _ , P) = P

-- CommRing ·syntax

module commring-·syntax (R : CommRing {ℓ}) where
  open ring-·syntax (CommRing→Ring R) public
