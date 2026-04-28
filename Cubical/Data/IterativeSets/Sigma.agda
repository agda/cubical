{-# OPTIONS --lossy-unification #-}
module Cubical.Data.IterativeSets.Sigma where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Functions.Embedding
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Fiberwise
open import Cubical.Homotopy.Base
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport

open import Cubical.Data.Sigma

open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.OrderedPair

private
  variable
    ℓ : Level
    x : V⁰ {ℓ}
    y : El⁰ x → V⁰ {ℓ}

private
    module _ {ℓ ℓ' : Level} {M : Type ℓ} {N : Type ℓ'} (h : M → N) where
        Inj : Type (ℓ-max ℓ ℓ')
        Inj = {x y : M} → h x ≡ h y → x ≡ y

module _ {ℓA ℓA' ℓB ℓB' : Level} {A : Type ℓA} {B : A → Type ℓB}
                                 {A' : Type ℓA'} {B' : A' → Type ℓB'}
                                 (f : A → A')
                                 (g : (a : A) → B a → B' (f a)) where
    Σfun : Σ A B → Σ A' B'
    Σfun (a , _) .fst = f a
    Σfun (a , b) .snd = g a b

    Inj-Σfun : isEmbedding f → ((a : A) → isEmbedding (g a)) → Inj Σfun
    Inj-Σfun embf embg {a , b} {a' , b'} p = ΣPathP (q₁ , q₂)
        where
            ΣP₁ : Σ[ q ∈ f a ≡ f a' ] subst B' q (g a b) ≡ (g a' b')
            ΣP₁ = PathΣ→ΣPathTransport _ _ p

            ΣP₂ : Σ[ q ∈ a ≡ a' ] subst (λ a → B' (f a)) q (g a b) ≡ (g a' b')
            ΣP₂ = invEq (Σ-cong-equiv-fst
                          {B = λ q → subst B' q (g a b) ≡ (g a' b')}
                          ((cong f :> (a ≡ a' → f a ≡ f a')), embf a a')) ΣP₁

            q₁ : a ≡ a'
            q₁ = ΣP₂ .fst

            Pg₁ : g a' (subst B q₁ b) ≡ subst (λ a → B' (f a)) q₁ (g a b)
            Pg₁ = sym (substCommSlice B (λ a → B' (f a)) g {a} {a'} q₁ b)

            Pg₂ : g a' (subst B q₁ b) ≡ g a' b'
            Pg₂ = Pg₁ ∙ ΣP₂ .snd

            P : subst B q₁ b ≡ b'
            P = isEmbedding→Inj (embg a') (subst B q₁ b) b' Pg₂

            q₂ : PathP (λ i → B (q₁ i)) b b'
            q₂ = toPathP P

    Emb-Σfun : isSet (Σ A' B') → isEmbedding f → ((a : A) → isEmbedding (g a)) → isEmbedding Σfun
    Emb-Σfun setΣ embf embg = injEmbedding setΣ (Inj-Σfun embf embg)

Σ⁰ : (x : V⁰ {ℓ}) → (El⁰ x → V⁰ {ℓ}) → V⁰ {ℓ}
Σ⁰ {ℓ = ℓ} x y = fromEmb E
  where
    E : Embedding (V⁰ {ℓ}) ℓ
    E .fst = (Σ[ a ∈ El⁰ {ℓ} x ] El⁰ {ℓ} (y a))
    E .snd .fst (a , b) = ⟨ (elements x a) , (elements (y a) b) ⟩⁰
    E .snd .snd = isEmbedding-∘ isEmbOrderedPair⁰
                                (Emb-Σfun _ _ (isSetΣ isSetV⁰ (λ _ → isSetV⁰))
                                              (isEmbedding-elements x) λ a → isEmbedding-elements (y a))

El⁰Σ⁰IsΣ : {x : V⁰ {ℓ}} {y : El⁰ x → V⁰ {ℓ}} → El⁰ (Σ⁰ x y) ≡ (Σ (El⁰ x) (λ a → El⁰ (y a)))
El⁰Σ⁰IsΣ = refl

_×⁰_ : V⁰ {ℓ} → V⁰ {ℓ} → V⁰ {ℓ}
x ×⁰ y = Σ⁰ x (λ _ → y)

El⁰×⁰Is× : {x y : V⁰ {ℓ}} → El⁰ (x ×⁰ y) ≡ ((El⁰ x) × (El⁰ y))
El⁰×⁰Is× = refl
