{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.S1.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.HITs.S1.Base
open import Cubical.HITs.PropositionalTruncation as PropTrunc

isConnectedS¹ : (s : S¹) → ∥ base ≡ s ∥
isConnectedS¹ base = ∣ refl ∣
isConnectedS¹ (loop i) =
  squash ∣ (λ j → loop (i ∧ j)) ∣ ∣ (λ j → loop (i ∨ ~ j)) ∣ i

isGroupoidS¹ : isGroupoid S¹
isGroupoidS¹ s t =
  PropTrunc.rec isPropIsSet
    (λ p →
      subst (λ s → isSet (s ≡ t)) p
        (PropTrunc.rec isPropIsSet
          (λ q → subst (λ t → isSet (base ≡ t)) q isSetΩS¹)
          (isConnectedS¹ t)))
    (isConnectedS¹ s)


toPropElim : ∀ {ℓ} {B : S¹ → Type ℓ} → ((s : S¹) → isProp (B s)) → B base → (s : S¹) → B s
toPropElim {B = B} isprop b base = b
toPropElim {B = B} isprop b (loop i) = hcomp (λ k → λ {(i = i0) → b
                                                     ; (i = i1) → isprop base (subst B (loop) b) b k})
                                      (transp (λ j → B (loop (i ∧ j))) (~ i) b)
