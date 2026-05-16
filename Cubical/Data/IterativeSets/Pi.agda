{-# OPTIONS --lossy-unification #-}

-- TODO: make type checking terminate
    
module Cubical.Data.IterativeSets.Pi where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Functions.Embedding
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Homotopy.Base
open import Cubical.Foundations.Transport

open import Cubical.Data.IterativeMultisets.Base renaming (index to index∞ ; elements to elements-V∞)
open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.OrderedPair

private
  variable
    ℓ : Level
    x : V⁰ {ℓ}
    y : El⁰ x → V⁰ {ℓ}

private
  module _ {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} (f : A → B) where
    Inj : Type (ℓ-max ℓ ℓ')
    Inj = {x y : A} → f x ≡ f y → x ≡ y

apply⁰ : {ℓ : Level} {x : V⁰ {ℓ}} {y : El⁰ x → V⁰ {ℓ}} → ((a : El⁰ {ℓ} x) → El⁰ {ℓ} (y a)) → El⁰ x → V⁰ {ℓ}
apply⁰ {ℓ} {x} {y} Φ a = ⟨ elements x a , elements (y a) (Φ a) ⟩⁰

apply⁰-inj : {ℓ : Level} {x : V⁰ {ℓ}} {y : El⁰ x → V⁰ {ℓ}} → (Φ : (a : El⁰ {ℓ} x) → El⁰ {ℓ} (y a)) → Inj (apply⁰ {ℓ} {x} {y} Φ)
apply⁰-inj {ℓ} {x} {y} Φ {a} {b} p = isEmbedding→Inj {A = El⁰ x} {B = V⁰ {ℓ}} {f = elements x} (isEmbedding-elements x) a b (fst (orderedPair⁰≡orderedPair⁰ {x = elements x a} {y = elements (y a) (Φ a)} {a = elements x b} {b = elements (y b) (Φ b)} .fst p))

apply⁰-emb : {ℓ : Level} {x : V⁰ {ℓ}} {y : El⁰ x → V⁰ {ℓ}} → (Φ : (a : El⁰ {ℓ} x) → El⁰ {ℓ} (y a)) → isEmbedding (apply⁰ {ℓ} {x} {y} Φ)
apply⁰-emb {ℓ} {x} {y} Φ = injEmbedding {A = El⁰ x} {B = V⁰ {ℓ}} isSetV⁰ (apply⁰-inj {ℓ} {x} {y} Φ)

graph⁰ : {ℓ : Level} {x : V⁰ {ℓ}} {y : El⁰ x → V⁰ {ℓ}} → ((a : El⁰ {ℓ} x) → El⁰ {ℓ} (y a)) → V⁰ {ℓ}
graph⁰ {ℓ} {x} {y} Φ = fromEmb E
  where
    E : Embedding V⁰ ℓ
    E .fst = El⁰ x
    E .snd .fst = apply⁰ {ℓ} {x} {y} Φ
    E .snd .snd = apply⁰-emb {ℓ} {x} {y} Φ

graph⁰-helper : {ℓ : Level} {x : V⁰ {ℓ}} {y : El⁰ x → V⁰ {ℓ}} (Φ : (a : El⁰ {ℓ} x) → El⁰ {ℓ} (y a)) (z : V⁰ {ℓ})
                  → ((z ∈⁰ graph⁰ Φ) ≡ fiber (apply⁰ {ℓ} {x} {y} Φ) z) -- (Σ[ a ∈ El⁰ x ] apply⁰ {ℓ} {x} {y} Φ a ≡ z))
graph⁰-helper {ℓ} {x} {y} Φ z = refl
   
apply⁰-inj2' : {ℓ : Level} {x : V⁰ {ℓ}} {y : El⁰ x → V⁰ {ℓ}} (Φ Ψ : (a : El⁰ {ℓ} x) → El⁰ {ℓ} (y a)) (a : El⁰ x) → apply⁰ {ℓ} {x} {y} Φ ≡ apply⁰ {ℓ} {x} {y} Ψ → Φ a ≡ Ψ a
apply⁰-inj2' {ℓ} {x} {y} Φ Ψ a p = isEmbedding→Inj {A = index (y a)} {B = V⁰} (isEmbedding-elements (y a)) (Φ a) (Ψ a) (P .snd)
  where
    p' : apply⁰ Φ a ≡ apply⁰ Ψ a
    p' = funExt⁻ p a

    P : (elements x a ≡ elements x a) ×
         (elements (y a) (Φ a) ≡ elements (y a) (Ψ a))
    P = orderedPair⁰≡orderedPair⁰ {x = elements x a} {y = elements (y a) (Φ a)} {a = elements x a} {b = elements (y a) (Ψ a)} .fst p'


apply⁰-inj2 : {ℓ : Level} {x : V⁰ {ℓ}} {y : El⁰ x → V⁰ {ℓ}} → Inj (apply⁰ {ℓ} {x} {y})
apply⁰-inj2 {ℓ} {x} {y} {Φ} {Ψ} p = funExt λ a → apply⁰-inj2' {ℓ} {x} {y} Φ Ψ a p

apply⁰-emb2 : {ℓ : Level} {x : V⁰ {ℓ}} {y : El⁰ x → V⁰ {ℓ}} → isEmbedding (apply⁰ {ℓ} {x} {y})
apply⁰-emb2 {ℓ} {x} {y} = injEmbedding {A = (a : El⁰ x) → El⁰ (y a)} {B = El⁰ x → V⁰} {f = apply⁰ {ℓ} {x} {y}} (isSet→ {A' = V⁰ {ℓ}} {A = El⁰ {ℓ} x} (isSetV⁰ {ℓ})) (apply⁰-inj2 {ℓ} {x} {y})

graph⁰-inj : {ℓ : Level} {x : V⁰ {ℓ}} {y : El⁰ x → V⁰ {ℓ}} → Inj (graph⁰ {ℓ} {x} {y})
graph⁰-inj {ℓ} {x} {y} {Φ} {Ψ} p = apply⁰-inj2 {ℓ} {x} {y} P
  where
    F : ((z : V⁰) → z ∈⁰ graph⁰ Φ → z ∈⁰ graph⁰ Ψ)
         × ((z : V⁰) → z ∈⁰ graph⁰ Ψ → z ∈⁰ graph⁰ Φ)
    F = ≡V⁰-≃-≃V⁰ {x = graph⁰ Φ} {y = graph⁰ Ψ} .fst p

    F₁ : (z : V⁰) → z ∈⁰ graph⁰ Φ → z ∈⁰ graph⁰ Ψ
    F₁ = F .fst

    F₂ : (z : V⁰) → z ∈⁰ graph⁰ Ψ → z ∈⁰ graph⁰ Φ
    F₂ = F .snd

    module _ (a : El⁰ x) where
      s : V⁰
      s = apply⁰ {ℓ} {x} {y} Ψ a

      s∈Ψ : s ∈⁰ graph⁰ Ψ
      s∈Ψ .fst = a
      s∈Ψ .snd = refl

      s∈Φ : s ∈⁰ graph⁰ Φ
      s∈Φ = F₂ s s∈Ψ

      a' : El⁰ x
      a' = s∈Φ .fst

      q : apply⁰ {ℓ} {x} {y} Φ a' ≡ apply⁰ {ℓ} {x} {y} Ψ a
      q = s∈Φ .snd

      r : elements x a' ≡ elements x a
      r = orderedPair⁰≡orderedPair⁰ {x = elements x a'} {y = elements (y a') (Φ a')} {a = elements x a} {b = elements (y a) (Ψ a)} .fst q .fst

      a'≡a : a' ≡ a
      a'≡a = isEmbedding→Inj {A = El⁰ x} {B = V⁰ {ℓ}} {f = elements x}
              (isEmbedding-elements x) a' a r

      gg : apply⁰ {ℓ} {x} {y} Φ a ≡ apply⁰ {ℓ} {x} {y} Ψ a
      gg = transport (cong (λ m → apply⁰ {ℓ} {x} {y} Φ m ≡ apply⁰ {ℓ} {x} {y} Ψ a) a'≡a) q
      
    
    P : apply⁰ {ℓ} {x} {y} Φ ≡ apply⁰ {ℓ} {x} {y} Ψ
    P = funExt gg

graph⁰-emb : {ℓ : Level} {x : V⁰ {ℓ}} {y : El⁰ x → V⁰ {ℓ}} → isEmbedding (graph⁰ {ℓ} {x} {y})
graph⁰-emb {ℓ} {x} {y} = injEmbedding {A = (a : El⁰ x) → El⁰ (y a)} {B = V⁰} {f = graph⁰} (isSetV⁰ {ℓ}) (graph⁰-inj {ℓ} {x} {y})

Π⁰ : (x : V⁰ {ℓ}) → (El⁰ x → V⁰ {ℓ}) → V⁰ {ℓ}
Π⁰ {ℓ} x y = fromEmb E
  where
    E : Embedding V⁰ ℓ
    E .fst = (a : El⁰ x) → El⁰ (y a)
    E .snd .fst = graph⁰
    E .snd .snd = graph⁰-emb {ℓ} {x} {y}

El⁰Π⁰isΠ : El⁰ (Π⁰ x y) ≡ ((a : El⁰ x) → El⁰ (y a))
El⁰Π⁰isΠ = refl

_→⁰_ : V⁰ {ℓ} → V⁰ {ℓ} → V⁰ {ℓ}
x →⁰ y = Π⁰ x (λ _ → y)

El⁰→⁰is→ : {x y : V⁰ {ℓ}} → El⁰ (x →⁰ y) ≡ (El⁰ x → El⁰ y)
El⁰→⁰is→ = refl
