{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Universe.Properties where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence

isInjectiveTransport : ∀ {ℓ : Level} {A B : Type ℓ} {p q : A ≡ B}
  → transport p ≡ transport q → p ≡ q
isInjectiveTransport {p = p} {q} α i =
  hcomp
    (λ j → λ
      { (i = i0) → secEq univalence p j
      ; (i = i1) → secEq univalence q j
      })
    (invEq univalence ((λ a → α i a) , t i))
  where
  t : PathP (λ i → isEquiv (λ a → α i a)) (pathToEquiv p .snd) (pathToEquiv q .snd)
  t = isProp→isContrPathP (λ i → isPropIsEquiv (λ a → α i a)) _ _ .fst
