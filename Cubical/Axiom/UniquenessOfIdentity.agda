{-

Uniqueness of identity proofs and axiom K

-}


module Cubical.Axiom.UniquenessOfIdentity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Cubical.Relation.Nullary

private
 variable
  ℓ : Level

-- Define uniqueness of identity proofs and Axiom K for an individual type

module _ (A : Type ℓ) where

  UIP : Type ℓ
  UIP = (x : A) (p : x ≡ x) → refl ≡ p

  AxiomK : (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
  AxiomK ℓ' = (x : A) (P : x ≡ x → Type ℓ') → P refl → (∀ p → P p)

-- UIP, K, and isSet are logically equivalent

module _ {A : Type ℓ} where

  UIP→AxiomK : UIP A → ∀ ℓ' → AxiomK A ℓ'
  UIP→AxiomK uip _ x P Prefl p = subst P (uip x p) Prefl

  AxiomK→UIP : AxiomK A ℓ → UIP A
  AxiomK→UIP K x p = K x (refl ≡_) refl p

  UIP→isSet : UIP A → isSet A
  UIP→isSet uip x = J> (uip x)

  isSet→UIP : isSet A → UIP A
  isSet→UIP setA x p = setA _ _ _ _

-- Univalence implies that universes fail UIP

¬UIPType : ∀ {ℓ} → ¬ UIP (Type ℓ)
¬UIPType {ℓ} uip =
  false≢true (cong lower (transport-uip p (lift true)))
  where
  B = Lift {j = ℓ} Bool
  p = cong (Lift {j = ℓ}) (ua notEquiv)

  transport-uip : (p : B ≡ B) → ∀ b → transport p b ≡ b
  transport-uip = UIP→AxiomK uip _ B _ transportRefl
