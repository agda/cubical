{-# OPTIONS --cubical --guardedness #-} --safe

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Function using (_∘_)

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )
open import Cubical.Data.Sum
open import Cubical.Data.Sigma

open import Cubical.Foundations.Transport

open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

open import Cubical.M-types.helper

module Cubical.M-types.M-type.Properties where

open import Cubical.M-types.M-type.Base
open import Cubical.M-types.Container

-- in-fun and out-fun are inverse

out-inverse-in : ∀ {ℓ} {S : Container {ℓ}} -> (out-fun {S = S} ∘ in-fun {S = S}) ≡ idfun (P₀ (M-type S))
out-inverse-in {S = S} i a = transport⁻Transport {A = P₀ {S = S} (M-type S)} {B = M-type S} (shift {S = S}) a i

in-inverse-out : ∀ {ℓ} {S : Container {ℓ}} -> (in-fun ∘ out-fun {S = S}) ≡ idfun (M-type S)
in-inverse-out {S = S} i a = transportTransport⁻ {A = P₀ (M-type S)} {B = M-type S} (shift {S = S}) a i

-- constructor properties

in-inj : ∀ {ℓ} {S : Container {ℓ}} {Z : Set ℓ} -> ∀ {f g : Z → P₀ (M-type S)} -> (in-fun ∘ f ≡ in-fun ∘ g) ≡ (f ≡ g)
in-inj = ≡-rel-a-inj in-fun out-fun in-inverse-out out-inverse-in

out-inj : ∀ {ℓ} {S : Container {ℓ}} {Z : Set ℓ} -> ∀ {f g : Z → M-type S} -> (out-fun ∘ f ≡ out-fun ∘ g) ≡ (f ≡ g)
out-inj = ≡-rel-b-inj in-fun out-fun in-inverse-out out-inverse-in

-- isInjectiveTransport
