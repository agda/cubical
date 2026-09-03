-- This module provides W-types of iterative sets. A tree sup-W a g is encoded by the ordered
-- pair of its label and the graph of its encoded subtrees, i.e. ⟨ a , { ⟨ b , g b ⟩ ∣ b } ⟩

{-# OPTIONS --lossy-unification #-}

module Cubical.Data.IterativeSets.W where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Functions.Embedding
open import Cubical.Functions.FunExtEquiv using (funExtNonDep)
open import Cubical.Data.Sigma
open import Cubical.Data.W.W using (W ; sup-W)

open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.OrderedPair

private
  variable
    ℓ : Level

private
  -- the graph of h as a set of ordered pairs
  graphV⁰ : (z : V⁰ {ℓ}) → (El⁰ z → V⁰ {ℓ}) → V⁰ {ℓ}
  graphV⁰ {ℓ} z h = fromEmb E
    where
      E : Embedding (V⁰ {ℓ}) ℓ
      E .fst = El⁰ z
      E .snd .fst b = ⟨ elements z b , h b ⟩⁰
      E .snd .snd = injEmbedding isSetV⁰ λ {b} {b'} p →
        isEmbedding→Inj (isEmbedding-elements z) b b'
          (orderedPair⁰≡orderedPair⁰ {x = elements z b} {y = h b}
                                     {a = elements z b'} {b = h b'} .fst p .fst)

  graphV⁰-inj : (z z' : V⁰ {ℓ}) (h : El⁰ z → V⁰ {ℓ}) (h' : El⁰ z' → V⁰ {ℓ})
              → graphV⁰ z h ≡ graphV⁰ z' h'
              → (b : El⁰ z) (b' : El⁰ z') → elements z b ≡ elements z' b' → h b ≡ h' b'
  graphV⁰-inj z z' h h' p b b' q = sym (pair≡ .snd) ∙ cong h' c≡b'
    where
      mem : ⟨ elements z b , h b ⟩⁰ ∈⁰ graphV⁰ z' h'
      mem = subst (⟨ elements z b , h b ⟩⁰ ∈⁰_) p (b , refl)

      c : El⁰ z'
      c = mem .fst

      pair≡ : (elements z' c ≡ elements z b) × (h' c ≡ h b)
      pair≡ = orderedPair⁰≡orderedPair⁰ {x = elements z' c} {y = h' c}
                                        {a = elements z b} {b = h b} .fst (mem .snd)

      c≡b' : c ≡ b'
      c≡b' = isEmbedding→Inj (isEmbedding-elements z') c b' (pair≡ .fst ∙ q)

module _ (x : V⁰ {ℓ}) (y : El⁰ x → V⁰ {ℓ}) where

  private
    encode : W (El⁰ x) (λ a → El⁰ (y a)) → V⁰ {ℓ}
    encode (sup-W a g) = ⟨ elements x a , graphV⁰ (y a) (encode ∘ g) ⟩⁰

    encode-inj : (u v : W (El⁰ x) (λ a → El⁰ (y a))) → encode u ≡ encode v → u ≡ v
    encode-inj (sup-W a g) (sup-W a' g') p i = sup-W (a≡a' i) (subtrees≡ i)
      where
        pair≡ : (elements x a ≡ elements x a')
              × (graphV⁰ (y a) (encode ∘ g) ≡ graphV⁰ (y a') (encode ∘ g'))
        pair≡ = orderedPair⁰≡orderedPair⁰
                  {x = elements x a} {y = graphV⁰ (y a) (encode ∘ g)}
                  {a = elements x a'} {b = graphV⁰ (y a') (encode ∘ g')} .fst p

        a≡a' : a ≡ a'
        a≡a' = isEmbedding→Inj (isEmbedding-elements x) a a' (pair≡ .fst)

        subtrees≡ : PathP (λ i → El⁰ (y (a≡a' i)) → W (El⁰ x) (λ a → El⁰ (y a))) g g'
        subtrees≡ = funExtNonDep λ {b} {b'} q →
          encode-inj (g b) (g' b')
            (graphV⁰-inj (y a) (y a') (encode ∘ g) (encode ∘ g') (pair≡ .snd) b b'
                         (λ i → elements (y (a≡a' i)) (q i)))

  W⁰ : V⁰ {ℓ}
  W⁰ = fromEmb E
    where
      E : Embedding (V⁰ {ℓ}) ℓ
      E .fst = W (El⁰ x) (λ a → El⁰ (y a))
      E .snd .fst = encode
      E .snd .snd = injEmbedding isSetV⁰ λ {u} {v} → encode-inj u v

El⁰W⁰IsW : {x : V⁰ {ℓ}} {y : El⁰ x → V⁰ {ℓ}} → El⁰ (W⁰ x y) ≡ W (El⁰ x) (λ a → El⁰ (y a))
El⁰W⁰IsW = refl
