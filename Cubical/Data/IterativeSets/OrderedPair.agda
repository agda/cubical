-- This modules provides the Norbert-Wiener encoding of ordered pairs
-- i.e. ⟨ x , y ⟩ = {{{x}, ∅}, {{y}}}

{-# OPTIONS --lossy-unification #-}

module Cubical.Data.IterativeSets.OrderedPair where

open import Cubical.Foundations.Prelude

open import Cubical.Functions.Embedding
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (elim to ⊥-elim)
open import Cubical.Data.Sum
open import Cubical.Data.Unit.Properties
open import Cubical.Data.Bool.Properties
open import Cubical.Relation.Nullary using (¬_)

open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.Empty
open import Cubical.Data.IterativeSets.Singleton.Base
open import Cubical.Data.IterativeSets.Singleton.Properties
open import Cubical.Data.IterativeSets.UnorderedPair.Base
open import Cubical.Data.IterativeSets.UnorderedPair.Properties

private
  variable
    ℓ : Level
    x y z : V⁰ {ℓ}

private
  variable
    x≢y : ¬ (x ≡ y)

-- Norbert Wiener encoding
⟨_,_⟩⁰ : V⁰ {ℓ} → V⁰ {ℓ} → V⁰ {ℓ}
⟨ x , y ⟩⁰ = unorderedPair⁰ (unorderedPair⁰ (singleton⁰ x) empty⁰ singleton⁰≢empty⁰)
                            (singleton⁰ (singleton⁰ y))
                            unorderedPair⁰≢singleton⁰

orderedPair⁰≡orderedPair⁰ : {x y a b : V⁰ {ℓ}} → ((⟨ x , y ⟩⁰ ≡ ⟨ a , b ⟩⁰) ≃ ((x ≡ a) × (y ≡ b)))
orderedPair⁰≡orderedPair⁰ {ℓ = ℓ} {x = x} {y = y} {a = a} {b = b} = compEquiv (compEquiv (compEquiv step₁ step₂) step₃) step₄
  where
    step₁ : (⟨ x , y ⟩⁰ ≡ ⟨ a , b ⟩⁰)
            ≃
            (unorderedPair⁰ (singleton⁰ x) empty⁰ singleton⁰≢empty⁰ ≡ unorderedPair⁰ (singleton⁰ a) empty⁰ singleton⁰≢empty⁰)
            × (singleton⁰ (singleton⁰ y) ≡ singleton⁰ (singleton⁰ b))
    step₁ = unorderedPair⁰≡unorderedPair⁰' {x = unorderedPair⁰ (singleton⁰ x) empty⁰ (singleton⁰≢empty⁰ {x = x})}
                                           {y = singleton⁰ (singleton⁰ y)}
                                           {a = unorderedPair⁰ (singleton⁰ a) empty⁰ (singleton⁰≢empty⁰ {x = a})}
                                           {b = singleton⁰ (singleton⁰ b)}
                                           {x≢y = unorderedPair⁰≢singleton⁰}
                                           {a≢b = unorderedPair⁰≢singleton⁰}
                                           unorderedPair⁰≢singleton⁰

    step₂ : (unorderedPair⁰ (singleton⁰ x) empty⁰ singleton⁰≢empty⁰ ≡ unorderedPair⁰ (singleton⁰ a) empty⁰ singleton⁰≢empty⁰)
            × (singleton⁰ (singleton⁰ y) ≡ singleton⁰ (singleton⁰ b))
            ≃
            (((singleton⁰ x ≡ singleton⁰ a) × (empty⁰ {ℓ} ≡ empty⁰))
              × ((singleton⁰ y ≡ singleton⁰ b)))
    step₂ = ≃-× (unorderedPair⁰≡unorderedPair⁰' {x = singleton⁰ x}
                                                         {y = empty⁰}
                                                         {a = singleton⁰ a}
                                                         {b = empty⁰}
                                                         {x≢y = singleton⁰≢empty⁰ {x = x}}
                                                         {a≢b = singleton⁰≢empty⁰ {x = a}}
                                                         (singleton⁰≢empty⁰ {x = x}))
                (invEquiv (singleton⁰≡singleton⁰ {x = singleton⁰ y} {y = singleton⁰ b}))

    step₃ : (((singleton⁰ x ≡ singleton⁰ a) × (empty⁰ {ℓ} ≡ empty⁰))
              × ((singleton⁰ y ≡ singleton⁰ b)))
            ≃
            ((singleton⁰ x ≡ singleton⁰ a) × (singleton⁰ y ≡ singleton⁰ b))
    step₃ = ≃-× (Σ-contractSnd (λ _ → inhProp→isContr refl (isSetV⁰ empty⁰ empty⁰)))
                (idEquiv (singleton⁰ y ≡ singleton⁰ b))
    step₄ : ((singleton⁰ x ≡ singleton⁰ a) × (singleton⁰ y ≡ singleton⁰ b))
            ≃
            ((x ≡ a) × (y ≡ b))
    step₄ = ≃-× (invEquiv (singleton⁰≡singleton⁰ {x = x} {y = a}))
                (invEquiv (singleton⁰≡singleton⁰ {x = y} {y = b}))

orderedPair⁰ : (V⁰ {ℓ} × V⁰ {ℓ}) → V⁰ {ℓ}
orderedPair⁰ = uncurry ⟨_,_⟩⁰

isEmbOrderedPair⁰ : isEmbedding (orderedPair⁰ {ℓ})
isEmbOrderedPair⁰ s t = E .snd
  where
    F : ((s .fst ≡ t .fst) × (s .snd ≡ t .snd)) ≃ (orderedPair⁰ s ≡ orderedPair⁰ t)
    F = propBiimpl→Equiv (isProp× (isSetV⁰ (s .fst) (t .fst))
                                  (isSetV⁰ (s .snd) (t .snd)))
                         (isSetV⁰ (orderedPair⁰ s) (orderedPair⁰ t))
                         (λ P i → ⟨ P .fst i , P .snd i ⟩⁰)
                         (orderedPair⁰≡orderedPair⁰ .fst)

    E : (s ≡ t) ≃ (orderedPair⁰ s ≡ orderedPair⁰ t)
    E = compEquiv (isoToEquiv (invIso (ΣPathPIsoPathPΣ {x = s} {y = t}))) F
