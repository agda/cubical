{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.Surjection where

open import Cubical.Core.Everything
open import Cubical.Data.Prod
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Embedding
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.HITs.PropositionalTruncation

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'
    f : A → B

isSurjection : (A → B) → Type _
isSurjection f = ∀ b → ∥ fiber f b ∥

section→isSurjection : {g : B → A} → section f g → isSurjection f
section→isSurjection {g = g} s b = ∣ g b , s b ∣

isSurjectionIsProp : isProp (isSurjection f)
isSurjectionIsProp = isPropPi λ _ → squash

isEquiv→isSurjection : isEquiv f → isSurjection f
isEquiv→isSurjection e b = ∣ fst (equiv-proof e b) ∣

isEquiv→isEmbedding×isSurjection : isEquiv f → isEmbedding f × isSurjection f
isEquiv→isEmbedding×isSurjection e = isEquiv→isEmbedding e , isEquiv→isSurjection e

isEmbedding×isSurjection→isEquiv : isEmbedding f × isSurjection f → isEquiv f
equiv-proof (isEmbedding×isSurjection→isEquiv {f = f} (emb , sur)) b =
  inhProp→isContr (recPropTrunc fib' (λ x → x) fib) fib'
  where
  hpf : hasPropFibers f
  hpf = isEmbedding→hasPropFibers emb

  fib : ∥ fiber f b ∥
  fib = sur b

  fib' : isProp (fiber f b)
  fib' = hpf b

isEquiv≃isEmbedding×isSurjection : isEquiv f ≃ isEmbedding f × isSurjection f
isEquiv≃isEmbedding×isSurjection = isoToEquiv (iso
  isEquiv→isEmbedding×isSurjection
  isEmbedding×isSurjection→isEquiv
  (λ _ → hLevelProd 1 isEmbeddingIsProp isSurjectionIsProp _ _)
  (λ _ → isPropIsEquiv _ _ _))
