-- from a set x we can build the set ∪ x.
module Cubical.Data.IterativeSets.Union where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Smallness
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Functions.Image
open import Cubical.HITs.Replacement
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Displayed.Base
open import Cubical.Data.Sigma
open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.UnorderedPair.Base
open import Cubical.Data.IterativeMultisets.Base renaming (index to index∞ ; elements to elements∞)
open import Cubical.Functions.Embedding

-- I don't know if more things should be public? Should the replacement
-- machinery be exposed?
module _ {ℓ : Level} where
  ∪⁰-index : (x : V⁰ {ℓ}) → Type ℓ
  ∪⁰-index x = Σ (index x) λ a → index (elements x a)
  ∪⁰-elements : (x : V⁰) → ∪⁰-index x → V⁰
  ∪⁰-elements x (a , b) = elements (elements x a) b

  private
    uar : (x : V⁰ {ℓ}) → UARel V⁰ ℓ
    uar x = locallySmall→UARel isLocallySmallV (∪⁰-elements x)

  -- Morally, ∪ x has for indexing set the (union of indices of the) image of
  -- elements x. But this fails for level reasons, which is why we need the
  -- notion of smallness and replacement.
  ∪⁰ : V⁰ {ℓ} → V⁰ {ℓ}
  ∪⁰ x = fromEmb (idx , elm)
    where
      idx : Type ℓ
      idx = Replacement' isLocallySmallV (∪⁰-elements x) .fst
      elm : idx ↪ V⁰
      elm .fst = unrep (uar x) (∪⁰-elements x)
      elm .snd = isEmbeddingUnrep (locallySmall→UARel isLocallySmallV (∪⁰-elements x)) (∪⁰-elements x)

  -- This indeed satisfies the union axiom. Unfortunately, computationally, we
  -- lose track of which original set each element of the union comes from.
  ∈∪⁰-≃ : ∀ x z → (z ∈⁰ (∪⁰ x)) ≃ (∃[ a ∈ index x ] z ∈⁰ elements x a)
  ∈∪⁰-≃ x z =
      (z ∈⁰ ∪⁰ x)
    ≃⟨ idEquiv _ ⟩
      fiber (unrep _ _) z
    ≃⟨ invEquiv (propTruncIdempotent≃ (isEmbedding→hasPropFibers (isEmbeddingUnrep (uar x) (∪⁰-elements x)) z)) ⟩
      isInImage (unrep (uar x) (∪⁰-elements x)) z
    ≃⟨ idEquiv _ ⟩
      ∃[ x₁ ∈ Replacement (uar x) (∪⁰-elements x)] unrep (uar x) (∪⁰-elements x) x₁ ≡ z
    ≃⟨ propBiimpl→Equiv squash₁ squash₁
         (rec squash₁ λ (r , p) →
           rec squash₁ (λ ((a , b) , q) →
             ∣ a , ∣ b , cong (unrep (uar x) (∪⁰-elements x)) q ∙ p ∣₁ ∣₁)
             (isSurjectiveRep (uar x) (∪⁰-elements x) r))
         (rec squash₁ λ (a , h) →
           rec squash₁ (λ (b , p) → ∣ rep (a , b) , p ∣₁) h)
      ⟩
      ∃[ a ∈ index x ] ∃[ b ∈ index (elements x a) ] elements (elements x a) b ≡ z
    ≃⟨ propTrunc≃ (Σ-cong-equiv-snd (λ a → propTruncIdempotent≃ (isProp∈⁰ {x = elements x a} {z = z}))) ⟩
      ∃[ a ∈ index x ] z ∈⁰ elements x a
    ■
