{-# OPTIONS --safe #-}
module Cubical.Functions.Surjection where

open import Cubical.Core.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
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

_↠_ : Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
A ↠ B = Σ[ f ∈ (A → B) ] isSurjection f

section→isSurjection : {g : B → A} → section f g → isSurjection f
section→isSurjection {g = g} s b = ∣ g b , s b ∣

isPropIsSurjection : isProp (isSurjection f)
isPropIsSurjection = isPropΠ λ _ → squash

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
  (λ _ → isOfHLevelΣ 1 isPropIsEmbedding (\ _ → isPropIsSurjection) _ _)
  (λ _ → isPropIsEquiv _ _ _))

-- obs: for epi⇒surjective to go through we require a stronger
-- hypothesis that one would expect:
-- f must cancel functions from a higher universe.
rightCancellable : (f : A → B) → Type _
rightCancellable {ℓ} {A} {ℓ'} {B} f = ∀ {C : Type (ℓ-suc (ℓ-max ℓ ℓ'))}
  → ∀ (g g' : B → C) → (∀ x → g (f x) ≡ g' (f x)) → ∀ y → g y ≡ g' y

-- This statement is in Mac Lane & Moerdijk (page 143, corollary 5).
epi⇒surjective : (f : A → B) → rightCancellable f → isSurjection f
epi⇒surjective f rc y = transport (fact₂ y) tt*
    where hasPreimage : (A → B) → B → _
          hasPreimage f y = ∥ fiber f y ∥

          fact₁ : ∀ x → Unit* ≡ hasPreimage f (f x)
          fact₁ x = hPropExt isPropUnit*
                             isPropPropTrunc
                             (λ _ → ∣ (x , refl) ∣)
                             (λ _ → tt*)

          fact₂ : ∀ y → Unit* ≡ hasPreimage f y
          fact₂ = rc _ _ fact₁
