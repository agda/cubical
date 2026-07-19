{-

Pointed structure: X ↦ X

-}
module Cubical.Structures.Pointed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.SIP

open import Cubical.Foundations.Pointed.Base

private
  variable
    ℓ : Level

-- Structured isomorphisms

PointedStructure : Type ℓ → Type ℓ
PointedStructure X = X

PointedEquivStr : StrEquiv PointedStructure ℓ
PointedEquivStr A B f = equivFun f (pt A) ≡ pt B

pointedUnivalentStr : UnivalentStr {ℓ} PointedStructure PointedEquivStr
pointedUnivalentStr f = invEquiv (ua-ungluePath-Equiv f)

pointedSIP : (A B : Pointed ℓ) → A ≃[ PointedEquivStr ] B ≃ (A ≡ B)
pointedSIP = SIP pointedUnivalentStr

pointed-sip : (A B : Pointed ℓ) → A ≃[ PointedEquivStr ] B → (A ≡ B)
pointed-sip A B = equivFun (pointedSIP A B) -- ≡ λ (e , p) i → ua e i , ua-gluePath e p i

pointed-sip-idEquiv∙ : (A : Pointed ℓ) → pointed-sip A A (idEquiv∙ A) ≡ refl
fst (pointed-sip-idEquiv∙ A i j) = uaIdEquiv i j
snd (pointed-sip-idEquiv∙ A i j) = glue {φ = i ∨ ~ j ∨ j} (λ _ → pt A) (pt A)

{-
  The following terms have huge normal forms, so they are abstract to avoid
  type checking speed problems, for example in

    Cubical.Homotopy.HSpace
-}
abstract
  pointed-sip⁻ : (A B : Pointed ℓ) → (A ≡ B) → A ≃[ PointedEquivStr ] B
  pointed-sip⁻ A B = invEq (pointedSIP A B)

  pointed-sip⁻-refl : (A : Pointed ℓ) → pointed-sip⁻ A A refl ≡ idEquiv∙ A
  pointed-sip⁻-refl A = sym (invEq (equivAdjointEquiv (pointedSIP A A)) (pointed-sip-idEquiv∙ A))

pointedEquivAction : EquivAction {ℓ} PointedStructure
pointedEquivAction e = e

pointedTransportStr : TransportStr {ℓ} pointedEquivAction
pointedTransportStr e s = sym (transportRefl _)
