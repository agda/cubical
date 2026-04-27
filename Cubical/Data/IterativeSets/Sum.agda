{-# OPTIONS --lossy-unification #-}

module Cubical.Data.IterativeSets.Sum where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Embedding
open import Cubical.Data.Sum renaming (rec to ⊎-rec)
open import Cubical.Relation.Nullary using (¬_)

open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.Empty
open import Cubical.Data.IterativeSets.Unit
open import Cubical.Data.IterativeSets.Singleton.Properties
open import Cubical.Data.IterativeSets.OrderedPair

private
    variable
        ℓ : Level
        
private
    module _ {x y : V⁰ {ℓ}} where
        fl : El⁰ x → V⁰ {ℓ}
        fl a = ⟨ empty⁰ , elements x a ⟩⁰

        fr : El⁰ y → V⁰ {ℓ}
        fr b = ⟨ unit⁰ , elements y b ⟩⁰
        
        f : El⁰ x ⊎ El⁰ y → V⁰ {ℓ}
        f = ⊎-rec fl fr

        embfl : isEmbedding fl
        embfl = compEmbedding ((curry orderedPair⁰ empty⁰)
                                , (Embedding-×-fst-const isSetV⁰ empty⁰ orderedPair⁰ isEmbOrderedPair⁰))
                              ((elements x) , (isEmbedding-elements x)) .snd

        embfr : isEmbedding fr
        embfr = compEmbedding ((curry orderedPair⁰ unit⁰)
                                , (Embedding-×-fst-const isSetV⁰ unit⁰ orderedPair⁰ isEmbOrderedPair⁰))
                              ((elements y) , (isEmbedding-elements y)) .snd

        fla≢frb : (a : El⁰ x) (b : El⁰ y) → ¬ fl a ≡ fr b
        fla≢frb a b fla≡frb = empty⁰≢unit⁰ (orderedPair⁰≡orderedPair⁰ .fst fla≡frb .fst)

        femb : isEmbedding f
        femb = isEmbeddingPair fl fr embfl embfr fla≢frb

_+⁰_ : V⁰ {ℓ} → V⁰ {ℓ} → V⁰ {ℓ}
x +⁰ y = fromEmb E
  where
    E : Embedding V⁰ _
    E .fst = El⁰ x ⊎ El⁰ y
    E .snd .fst = f
    E .snd .snd = femb

El⁰+⁰Is⊎ : {x y : V⁰ {ℓ}} → El⁰ (x +⁰ y) ≡ El⁰ x ⊎ El⁰ y
El⁰+⁰Is⊎ = refl
