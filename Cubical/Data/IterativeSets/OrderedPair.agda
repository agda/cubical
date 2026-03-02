{-# OPTIONS --lossy-unification #-}

module Cubical.Data.IterativeSets.OrderedPair where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Cubical.Functions.Embedding
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (elim to ⊥-elim)
open import Cubical.Data.Sum
open import Cubical.Relation.Nullary using (¬_)

open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.Empty
open import Cubical.Data.IterativeSets.Singleton

open import Cubical.Data.IterativeSets.UnorderedPair

private
  variable
    ℓ : Level
    x y z : V⁰ {ℓ}

private
  variable
    x≢y : ¬ (x ≡ y)

-- TODO: maybe move to some better place together with empty⁰≢unit⁰
empty⁰≢singleton⁰ : ¬ (empty⁰ {ℓ} ≡ singleton⁰ x)
empty⁰≢singleton⁰ p = ⊥*≢Unit* (cong El⁰ p)

singleton⁰≢empty⁰ : ¬ (singleton⁰ x ≡ empty⁰ {ℓ})
singleton⁰≢empty⁰ p = Unit*≢⊥* (cong El⁰ p)

singleton⁰≢unorderedPair⁰ : ¬ (singleton⁰ z ≡ unorderedPair⁰ x y x≢y)
singleton⁰≢unorderedPair⁰ p = Unit*≢Bool* (cong El⁰ p)

unorderedPair⁰≢singleton⁰ : ¬ (unorderedPair⁰ x y x≢y ≡ singleton⁰ z)
unorderedPair⁰≢singleton⁰ p = Bool*≢Unit* (cong El⁰ p)


-- Norbert Wiener encoding
⟨_,_⟩⁰ : V⁰ {ℓ} → V⁰ {ℓ} → V⁰ {ℓ}
⟨ x , y ⟩⁰ = unorderedPair⁰ (unorderedPair⁰ (singleton⁰ x) empty⁰ singleton⁰≢empty⁰) (singleton⁰ (singleton⁰ y)) unorderedPair⁰≢singleton⁰

orderedPair⁰ : (V⁰ {ℓ} × V⁰ {ℓ}) → V⁰ {ℓ}
orderedPair⁰ = uncurry ⟨_,_⟩⁰

isEmbOrderedPair⁰ : isEmbedding (orderedPair⁰ {ℓ})
isEmbOrderedPair⁰ {ℓ} = injEmbedding isSetV⁰ inj
    where
        inj : {s t : V⁰ {ℓ} × V⁰ {ℓ}} → orderedPair⁰ s ≡ orderedPair⁰ t → s ≡ t
        inj {s = x , y} {t = a , b} p = ΣPathP (helper (unorderedPair⁰≡unorderedPair⁰ .fst p)) -- x≡a,y≡b
            where
                x≡a-helper : ((singleton⁰ x ≡ singleton⁰ a) × (empty⁰ {ℓ} ≡ empty⁰ {ℓ})) ⊎ ((singleton⁰ x ≡ empty⁰) × (empty⁰ ≡ singleton⁰ a)) → x ≡ a
                x≡a-helper (inl (p , _)) = invEq singleton⁰≡singleton⁰ p
                x≡a-helper (inr (p , _)) = ⊥-elim (singleton⁰≢empty⁰ p)
                helper : ((unorderedPair⁰ (singleton⁰ x) empty⁰ singleton⁰≢empty⁰ ≡ unorderedPair⁰ (singleton⁰ a) empty⁰ singleton⁰≢empty⁰) × (singleton⁰ (singleton⁰ y) ≡ singleton⁰ (singleton⁰ b))) ⊎ ((unorderedPair⁰ (singleton⁰ x) empty⁰ singleton⁰≢empty⁰ ≡ singleton⁰ (singleton⁰ b)) × (singleton⁰ (singleton⁰ y) ≡ unorderedPair⁰ (singleton⁰ a) empty⁰ singleton⁰≢empty⁰)) → ((x ≡ a) × (y ≡ b))
                helper (inl (u , s)) .fst = x≡a-helper (unorderedPair⁰≡unorderedPair⁰ .fst u)
                helper (inl (u , s)) .snd = invEq singleton⁰≡singleton⁰ (invEq singleton⁰≡singleton⁰ s)
                helper (inr (p , _)) = ⊥-elim {A = λ _ → (x ≡ a) × (y ≡ b)} (unorderedPair⁰≢singleton⁰ p)
                -- x≡a,y≡b : (x ≡ a) × (y ≡ b)
                -- x≡a,y≡b = helper (unorderedPair⁰≡unorderedPair⁰ .fst p)

orderedPair⁰≡orderedPair⁰ : {x y a b : V⁰ {ℓ}} → ((⟨ x , y ⟩⁰ ≡ ⟨ a , b ⟩⁰) ≃ ((x ≡ a) × (y ≡ b)))
orderedPair⁰≡orderedPair⁰ {x = x} {y = y} {a = a} {b = b} = propBiimpl→Equiv (isSetV⁰ _ _) (isProp× (isSetV⁰ _ _) (isSetV⁰ _ _)) (PathPΣ ∘ (isEmbedding→Inj isEmbOrderedPair⁰ (x , y) (a , b))) (λ (x≡a , y≡b) → cong ⟨_, y ⟩⁰ x≡a ∙ cong ⟨ a ,_⟩⁰ y≡b)
