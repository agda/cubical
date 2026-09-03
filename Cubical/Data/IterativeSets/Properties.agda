-- This module provides Propositions 3.3 and 3.31 of https://doi.org/10.1017/S0960129524000288
-- i.e. the codes for a type are its embeddings into V⁰, and V⁰ is not univalent

module Cubical.Data.IterativeSets.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Embedding
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.Relation.Nullary using (¬_)

open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.Bool

private
  variable
    ℓ : Level

Embedding≃Code : {A : Type ℓ} → (A ↪ V⁰ {ℓ}) ≃ (Σ[ a ∈ V⁰ {ℓ} ] El⁰ a ≡ A)
Embedding≃Code {ℓ} {A} =
  (A ↪ V⁰)                               ≃⟨ fiberProjEquiv (Type ℓ) (λ X → X ↪ V⁰) A ⟩
  (Σ[ E ∈ Embedding V⁰ ℓ ] E .fst ≡ A)   ≃⟨ Σ-cong-equiv-fst Emb≃V⁰ ⟩
  (Σ[ a ∈ V⁰ ] El⁰ a ≡ A)                ■

-- bool⁰ ≡ bool⁰ is a proposition, but Bool* ≃ Bool* is not
¬univalentV⁰ : ¬ ((x y : V⁰ {ℓ}) → (x ≡ y) ≃ (El⁰ x ≃ El⁰ y))
¬univalentV⁰ {ℓ} univ = true*≢false* (cong (λ e → equivFun e true*) idEquiv≡notEquiv)
  where
    isPropBool*≃Bool* : isProp (Bool* {ℓ} ≃ Bool* {ℓ})
    isPropBool*≃Bool* = isOfHLevelRespectEquiv 1 (univ bool⁰ bool⁰) (isSetV⁰ bool⁰ bool⁰)

    idEquiv≡notEquiv : idEquiv (Bool* {ℓ}) ≡ Lift≃Lift notEquiv
    idEquiv≡notEquiv = isPropBool*≃Bool* _ _
