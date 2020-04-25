{-# OPTIONS --cubical --safe #-}

module Cubical.Structures.CommRing where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)

open import Cubical.Structures.NAryOp
open import Cubical.Structures.Pointed
open import Cubical.Structures.Ring

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
                                            λ ((((isSetX , _) , _) , _) , _) → isPropΠ2 λ _ _ → isSetX _ _ --Change this when extractors
-- of rings are added

comm-ring-is-SNS : SNS {ℓ} comm-ring-structure comm-ring-iso
comm-ring-is-SNS = add-axioms-SNS _ comm-ring-axioms-isProp raw-ring-is-SNS

CommRingPath : (M N : CommRing {ℓ}) → (M ≃[ comm-ring-iso ] N) ≃ (M ≡ N)
CommRingPath = SIP comm-ring-is-SNS
