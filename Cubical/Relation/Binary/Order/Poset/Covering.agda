-- The covering relation
{-# OPTIONS --safe #-}

module Cubical.Relation.Binary.Order.Poset.Covering where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport

open import Cubical.Functions.Embedding
open import Cubical.Functions.Fibration

open import Cubical.Data.Bool as B using (Bool; true; false)
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Empty as ⊥

open import Cubical.Relation.Binary.Order.Poset.Base
open import Cubical.Relation.Binary.Order.Poset.Properties
open import Cubical.Relation.Binary.Order.Poset.Subset
open import Cubical.Relation.Binary.Order.Poset.Interval
open import Cubical.Relation.Nullary

open import Cubical.Reflection.RecordEquiv

private variable
  ℓ ℓ' : Level

module Cover (P' : Poset ℓ ℓ') where
  private P = ⟨ P' ⟩
  open PosetStr (snd P')

  infixl 20 _covers_

  _covers_ : P → P → Type (ℓ-max ℓ ℓ')
  y covers x = Σ[ x≤y ∈ x ≤ y ] isEquiv (2→Interval P' x y x≤y)

  isPropCovers : ∀ y x → isProp (y covers x)
  isPropCovers y x = isPropΣ (is-prop-valued x y) (λ _ → isPropIsEquiv _)

  module _ (x y : P) (x≤y : x ≤ y) (x≠y : ¬ x ≡ y)
           (cov : ∀ z → x ≤ z → z ≤ y → (z ≡ x) ⊎ (z ≡ y)) where
    open Iso

    private
      cov' : (i : Interval P' x y) → (i .Interval.z ≡ x) ⊎ (i .Interval.z ≡ y)
      cov' (interval z x≤z z≤y) = cov z x≤z z≤y

    makeCovers : y covers x
    makeCovers = x≤y , isoToIsEquiv isom where

      isom : Iso Bool (Interval P' x y)
      isom .fun = 2→Interval P' x y x≤y
      isom .inv i with cov' i
      ... | inl z≡x = false
      ... | inr z≡y = true
      isom .rightInv i with cov' i
      ... | inl z≡x = Interval≡ P' x y _ _ (sym z≡x)
      ... | inr z≡y = Interval≡ P' x y _ _ (sym z≡y)
      isom .leftInv b with cov' (2→Interval P' x y x≤y b)
      isom .leftInv false | inl _ = refl
      isom .leftInv false | inr x≡y = ⊥.rec (x≠y x≡y)
      isom .leftInv true  | inl y≡x = ⊥.rec (x≠y (sym y≡x))
      isom .leftInv true  | inr _ = refl

  -- Subset of faces and cofaces
  -- terminology from "Combinatorics of higher-categorical diagrams" by Amar Hadzihasanovic
  Δ : P → Embedding P (ℓ-max ℓ ℓ')
  Δ x = (Σ[ y ∈ P ] x covers y) , EmbeddingΣProp λ _ → isPropCovers _ _

  ∇ : P → Embedding P (ℓ-max ℓ ℓ')
  ∇ x = (Σ[ y ∈ P ] y covers x) , EmbeddingΣProp λ _ → isPropCovers _ _

  ΔMembership : ∀ x y → x covers y ≃ y ∈ₑ Δ x
  ΔMembership x y = invEquiv (fiberEquiv _ _)

  ∇Membership : ∀ x y → y covers x ≃ y ∈ₑ ∇ x
  ∇Membership x y = invEquiv (fiberEquiv _ _)
