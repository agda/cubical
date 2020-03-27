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
open import Cubical.Foundations.Embedding
open import Cubical.Foundations.Equiv

open import Cubical.M-types.helper

module Cubical.M-types.M-type.Properties where

open import Cubical.M-types.M-type.Base
open import Cubical.M-types.Container

-- in-fun and out-fun are inverse

open Iso

in-inverse-out : ∀ {ℓ} {S : Container {ℓ}} -> (in-fun ∘ out-fun {S = S}) ≡ idfun (M-type S)
in-inverse-out {S = S} i a = rightInv {A = P₀ (M-type S)} {B = M-type S} (shift-iso {S = S}) a i

out-inverse-in : ∀ {ℓ} {S : Container {ℓ}} -> (out-fun {S = S} ∘ in-fun {S = S}) ≡ idfun (P₀ (M-type S))
out-inverse-in {S = S} i a = leftInv {A = P₀ {S = S} (M-type S)} {B = M-type S} (shift-iso {S = S}) a i

in-out-id : ∀ {ℓ} {S : Container {ℓ}} -> ∀ {x y} → (in-fun (out-fun {S = S} x) ≡ in-fun (out-fun {S = S} y)) ≡ (x ≡ y)
in-out-id {x = x} {y} =
  (in-fun (out-fun x) ≡ in-fun (out-fun y))
    ≡⟨ cong₂ _≡_ (funExt⁻ in-inverse-out x) (funExt⁻ in-inverse-out y) ⟩
  (x ≡ y) ∎

-- Embeddings

in-embedding : ∀ {ℓ} {S : Container {ℓ}} → isEmbedding {A = P₀ (M-type S)} {B = M-type S} (in-fun {S = S})
in-embedding = isEquiv→isEmbedding (equivIsEquiv (isoToEquiv shift-iso))

out-embedding : ∀ {ℓ} {S : Container {ℓ}} → isEmbedding (out-fun {S = S})
out-embedding = isEquiv→isEmbedding (equivIsEquiv (isoToEquiv (sym-iso shift-iso)))

-- constructor properties

in-inj : ∀ {ℓ} {S : Container {ℓ}} {Z : Set ℓ} -> ∀ {f g : Z → P₀ (M-type S)} -> (in-fun ∘ f ≡ in-fun ∘ g) ≡ (f ≡ g)
in-inj = ≡-rel-a-inj shift-iso

out-inj : ∀ {ℓ} {S : Container {ℓ}} {Z : Set ℓ} -> ∀ {f g : Z → M-type S} -> (out-fun ∘ f ≡ out-fun ∘ g) ≡ (f ≡ g)
out-inj = ≡-rel-b-inj (iso in-fun out-fun (funExt⁻ in-inverse-out) (funExt⁻ out-inverse-in))

in-inj-x : ∀ {ℓ} {S : Container {ℓ}} -> ∀ {x y : P₀ (M-type S)} -> (in-fun x ≡ in-fun y) ≡ (x ≡ y)
in-inj-x {ℓ} {S = S} {x = x} {y} = ≡-rel-a-inj-x shift-iso

out-inj-x : ∀ {ℓ} {S : Container {ℓ}} -> ∀ {x y : M-type S} -> (out-fun x ≡ out-fun y) ≡ (x ≡ y)
out-inj-x {ℓ} {S = S} {x = x} {y} = ≡-rel-b-inj-x shift-iso
