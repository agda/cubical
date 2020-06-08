{-# OPTIONS --cubical --safe #-}
module Cubical.Functions.Surjection where

open import Cubical.Core.Everything
open import Cubical.Data.Sigma
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Embedding
open import Cubical.HITs.PropositionalTruncation as PropTrunc

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
isSurjectionIsProp = isPropΠ λ _ → squash

isEquiv→isSurjection : isEquiv f → isSurjection f
isEquiv→isSurjection e b = ∣ fst (equiv-proof e b) ∣

isEquiv→isEmbedding×isSurjection : isEquiv f → isEmbedding f × isSurjection f
isEquiv→isEmbedding×isSurjection e = isEquiv→isEmbedding e , isEquiv→isSurjection e

isEmbedding×isSurjection→isEquiv : isEmbedding f × isSurjection f → isEquiv f
equiv-proof (isEmbedding×isSurjection→isEquiv {f = f} (emb , sur)) b =
  inhProp→isContr (PropTrunc.rec fib' (λ x → x) fib) fib'
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
  (λ _ → isOfHLevelΣ 1 isEmbeddingIsProp (\ _ → isSurjectionIsProp) _ _)
  (λ _ → isPropIsEquiv _ _ _))

isPropIsSurjection : isProp (isSurjection f)
isPropIsSurjection = isPropΠ λ _ → propTruncIsProp
