{-# OPTIONS --cubical --safe #-}
module Cubical.ZCohomology.FunLoopSpace2 where



open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.FunExtEquiv
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Nat
open import Cubical.Data.HomotopyGroup
open import Cubical.HITs.Nullification
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.Truncation
open import Cubical.Data.NatMinusTwo

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'





{- Beware: Use of J -}
cancelReflMid : ∀ {ℓ} {A : Type ℓ} {a b : A} (p : a ≡ b) (q : b ≡ a) → p ∙ refl ∙ q ≡ p ∙ q
cancelReflMid {ℓ = ℓ}{A = A} {a = a} {b = b} p q = J {ℓ} {A} {a} {ℓ} (λ b p → ((q : b ≡ a) →  p ∙ refl ∙ q ≡ p ∙ q)) (λ r → sym (lUnit (refl  ∙ r ))) {b} p q

