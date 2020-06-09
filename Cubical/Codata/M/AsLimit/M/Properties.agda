{-# OPTIONS --cubical --guardedness --safe #-}

module Cubical.Codata.M.AsLimit.M.Properties where

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )
open import Cubical.Data.Sum
open import Cubical.Data.Sigma

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv

open import Cubical.Functions.Embedding

open import Cubical.Codata.M.AsLimit.helper
open import Cubical.Codata.M.AsLimit.M.Base
open import Cubical.Codata.M.AsLimit.Container

-- in-fun and out-fun are inverse

open Iso

in-inverse-out : ∀ {ℓ} {S : Container ℓ} → (in-fun {S = S} ∘ out-fun {S = S}) ≡ idfun (M S)
in-inverse-out {S = S} = subst (λ inv → in-fun {S = S} ∘ inv ≡ idfun (M S)) idpath def where
  -- substituting refl makes type-checking work a lot faster, but introduces a transport
  -- TODO (2020-05-23): revisit this at some point to see if it's still needed in future versions of agda
  def : (in-fun {S = S} ∘ inv (shift-iso S)) ≡ idfun (M S)
  def = funExt (rightInv (shift-iso S))
  idpath : inv (shift-iso S) ≡ out-fun {S = S}
  idpath = refl

out-inverse-in : ∀ {ℓ} {S : Container ℓ} → (out-fun {S = S} ∘ in-fun {S = S}) ≡ idfun (P₀ S (M S))
out-inverse-in {S = S} = subst (λ fun → out-fun {S = S} ∘ fun ≡ idfun (P₀ S (M S))) idpath def where
  def : (out-fun {S = S} ∘ fun (shift-iso S)) ≡ idfun (P₀ S (M S))
  def = funExt (leftInv (shift-iso S))
  idpath : fun (shift-iso S) ≡ in-fun {S = S}
  idpath = refl

in-out-id : ∀ {ℓ} {S : Container ℓ} -> ∀ {x y : M S} → (in-fun (out-fun x) ≡ in-fun (out-fun y)) ≡ (x ≡ y)
in-out-id {x = x} {y} i = (in-inverse-out i x) ≡ (in-inverse-out i y)

-- constructor properties

in-inj : ∀ {ℓ} {S : Container ℓ} {Z : Type ℓ} → ∀ {f g : Z → P₀ S (M S)} → (in-fun ∘ f ≡ in-fun ∘ g) ≡ (f ≡ g)
in-inj {ℓ} {S = S} {Z = Z} {f = f} {g = g} = iso→fun-Injection-Path {ℓ = ℓ} {A = P₀ S (M S)} {B = M S} {C = Z} (shift-iso S) {f = f} {g = g}

out-inj : ∀ {ℓ} {S : Container ℓ} {Z : Type ℓ} → ∀ {f g : Z → M S} → (out-fun ∘ f ≡ out-fun ∘ g) ≡ (f ≡ g)
out-inj {ℓ} {S = S} {Z = Z} {f = f} {g = g} = iso→inv-Injection-Path {ℓ = ℓ} {A = P₀ S (M S)} {B = M S} {C = Z} (shift-iso S) {f = f} {g = g}

in-inj-x : ∀ {ℓ} {S : Container ℓ} → ∀ {x y : P₀ S (M S)} → (in-fun x ≡ in-fun y) ≡ (x ≡ y)
in-inj-x {ℓ} {S = S} {x = x} {y} = iso→fun-Injection-Path-x (shift-iso S) {x} {y}

out-inj-x : ∀ {ℓ} {S : Container ℓ} → ∀ {x y : M S} → (out-fun x ≡ out-fun y) ≡ (x ≡ y)
out-inj-x {ℓ} {S = S} {x = x} {y} = iso→inv-Injection-Path-x (shift-iso S) {x} {y}
