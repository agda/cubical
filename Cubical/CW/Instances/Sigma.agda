{-# OPTIONS --safe #-}
{-
CW structure on Σ-types (and binary products)
-}

module Cubical.CW.Instances.Sigma where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv

open import Cubical.CW.Base

open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Cubical.HITs.Pushout
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.CW.Instances.Pushout
open import Cubical.CW.Instances.Empty

-- Σ A B as as finite CW complex
isFinCWΣ : (A : finCW ℓ-zero) (B : fst A → finCW ℓ-zero)
  → isFinCW (Σ (fst A) (fst ∘ B))
isFinCWΣ A = elimPropFinCW
   (λ A → (B : A → finCW ℓ-zero) → isFinCW (Σ A (fst ∘ B)))
   (λ B → subst isFinCW (sym (ua (ΣUnit (fst ∘ B)))) (snd (B tt)))
   (λ _ → subst isFinCW (ua (invEquiv (ΣEmpty _))) ∣ hasFinCWskel⊥ ∣₁)
   (λ A0 A1 A2 f g p q r B
     → subst isFinCW (ua (invEquiv (ΣPushout≃PushoutΣ f g (fst ∘ B))))
             (isFinCWPushout
               (_ , p (λ x → B (inl (f x)))) (_ , q λ x → B (inl x))
               (_ , r λ a → B (inr a)) _ _))
   A (isPropΠ λ _ → squash₁)

-- A × B as as finite CW complex
isFinCW× : (A B : finCW ℓ-zero) → isFinCW (fst A × fst B)
isFinCW× A B = isFinCWΣ A (λ _ → B)

-- Todo: excplicit construction of products of arbtirary CW complexes
