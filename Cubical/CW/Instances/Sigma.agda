{-
CW structure on Σ-types (and binary products)
-}

module Cubical.CW.Instances.Sigma where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.CW.Base

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Empty

open import Cubical.HITs.Pushout
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.CW.Instances.Pushout
open import Cubical.CW.Instances.Empty
open import Cubical.CW.Instances.Lift

isFinCWΣ : ∀ {ℓ ℓ'} (A : finCW ℓ) (B : fst A → finCW ℓ')
  → isFinCW (Σ (fst A) (fst ∘ B))
isFinCWΣ {ℓ} {ℓ'} A B =
  subst isFinCW (ua
    (isoToEquiv (iso (λ { (lift (lift x , lift y)) → x , y})
                     (λ x → lift ((lift (fst x)) , (lift (snd x))))
                     (λ _ → refl) (λ _ → refl))))
    (finCWLift ℓ (_
      , main (finCWLift ℓ' A)
             λ {(lift x) → finCWLift ℓ (B x)}) .snd)
  where
  ℓ* = ℓ-max ℓ ℓ'

  main : (A : finCW ℓ*) (B : fst A → finCW ℓ*)
    → isFinCW (Σ (fst A) (fst ∘ B))
  main A = elimPropFinCW
   (λ A → (B : A → finCW ℓ*) → isFinCW (Σ A (fst ∘ B)))
   (λ B → subst isFinCW
            (isoToPath (compIso
                  (invIso lUnit×Iso)
                  (Σ-cong-iso-fst LiftIso)))
            (snd (B tt*))) --
   (λ _ → subst isFinCW (ua (uninhabEquiv {A = ⊥*} (λ()) λ()))
                ∣ hasFinCWskel⊥* _ ∣₁) --
   (λ A0 A1 A2 f g p q r B
     → subst isFinCW (ua (invEquiv (ΣPushout≃PushoutΣ f g (fst ∘ B))))
         (isFinCWPushout (_ , p (λ x → B (inl (f x))))
                         (_ , q λ x → B (inl x))
                         (_ , r λ a → B (inr a)) _ _))
   A (isPropΠ λ _ → squash₁)

-- A × B as as finite CW complex
isFinCW× : ∀ {ℓ ℓ'} (A : finCW ℓ) (B : finCW ℓ')
  → isFinCW (fst A × fst B)
isFinCW× A B = isFinCWΣ A (λ _ → B)

-- Todo: explicit construction of products of arbtirary CW complexes
