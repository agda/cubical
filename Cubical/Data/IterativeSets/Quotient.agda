-- This module provides set quotients of iterative sets, i.e. the elements of x /⁰ R are the
-- equivalence classes (Proposition 31 of https://doi.org/10.1017/S0960129524000288)

module Cubical.Data.IterativeSets.Quotient where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Embedding
open import Cubical.HITs.SetQuotients as SQ using (_/_ ; [_] ; squash/)

open import Cubical.Data.IterativeSets.Base

private
  variable
    ℓ : Level

module _ (x : V⁰ {ℓ}) (R : El⁰ x → El⁰ x → Type ℓ) where

  -- the equivalence class u as a subset of x
  eqClass⁰ : El⁰ x / R → V⁰ {ℓ}
  eqClass⁰ u = fromEmb E
    where
      E : Embedding (V⁰ {ℓ}) ℓ
      E .fst = fiber [_] u
      E .snd = compEmbedding (Embedding-elements x) (EmbeddingΣProp (λ a → squash/ [ a ] u))

  ∈eqClass⁰-≃ : (u : El⁰ x / R) (a : El⁰ x) → (elements x a ∈⁰ eqClass⁰ u) ≃ ([ a ] ≡ u)
  ∈eqClass⁰-≃ u a = propBiimpl→Equiv
    (isProp∈⁰ {x = eqClass⁰ u} {z = elements x a}) (squash/ [ a ] u)
    (λ ((b , p) , q) →
      subst (λ c → [ c ] ≡ u) (isEmbedding→Inj (isEmbedding-elements x) b a q) p)
    (λ p → (a , p) , refl)

  isEmbedding-eqClass⁰ : isEmbedding eqClass⁰
  isEmbedding-eqClass⁰ = injEmbedding isSetV⁰ (λ {u} {v} → inj u v)
    where
      inj : (u v : El⁰ x / R) → eqClass⁰ u ≡ eqClass⁰ v → u ≡ v
      inj = SQ.elimProp (λ u → isPropΠ2 λ v _ → squash/ u v) λ a v p →
        ∈eqClass⁰-≃ v a .fst (subst (elements x a ∈⁰_) p (invEq (∈eqClass⁰-≃ [ a ] a) refl))

_/⁰_ : (x : V⁰ {ℓ}) → (El⁰ x → El⁰ x → Type ℓ) → V⁰ {ℓ}
x /⁰ R = fromEmb (El⁰ x / R , eqClass⁰ x R , isEmbedding-eqClass⁰ x R)

El⁰/⁰Is/ : {x : V⁰ {ℓ}} {R : El⁰ x → El⁰ x → Type ℓ} → El⁰ (x /⁰ R) ≡ (El⁰ x / R)
El⁰/⁰Is/ = refl
