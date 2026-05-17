{-# OPTIONS --lossy-unification #-}

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
  module _ {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} (f : A → B) where
    Inj : Type (ℓ-max ℓ ℓ')
    Inj = {x y : A} → f x ≡ f y → x ≡ y

module GraphElements {ℓ : Level} {x : V⁰ {ℓ}} {y : El⁰ {ℓ} x → V⁰ {ℓ}} where
  graphEl⁰ : ((a : El⁰ {ℓ} x) → El⁰ {ℓ} (y a)) → El⁰ x → V⁰ {ℓ}
  graphEl⁰ Φ a = ⟨ elements x a , elements (y a) (Φ a) ⟩⁰

  module FstConst (Φ : (a : El⁰ {ℓ} x) → El⁰ {ℓ} (y a)) where
    -- this is the same as graphEl⁰
    graphEl⁰' : El⁰ x → V⁰ {ℓ}
    graphEl⁰' = graphEl⁰ Φ

    inj : Inj graphEl⁰'
    inj {a} {b} p = isEmbedding→Inj
                      {A = El⁰ x} {B = V⁰ {ℓ}} {f = elements x}
                      (isEmbedding-elements x) a b
                        (fst (orderedPair⁰≡orderedPair⁰
                          {x = elements x a} {y = elements (y a) (Φ a)}
                          {a = elements x b} {b = elements (y b) (Φ b)} .fst p))

    emb : isEmbedding graphEl⁰'
    emb = injEmbedding {A = El⁰ x} {B = V⁰ {ℓ}} isSetV⁰ inj

  graphEl⁰-inj' : (Φ Ψ : (a : El⁰ {ℓ} x) → El⁰ {ℓ} (y a)) (a : El⁰ x)
                   → graphEl⁰ Φ ≡ graphEl⁰ Ψ → Φ a ≡ Ψ a
  graphEl⁰-inj' Φ Ψ a p = isEmbedding→Inj {A = index (y a)} {B = V⁰}
                                          (isEmbedding-elements (y a)) (Φ a) (Ψ a) els≡₂
    where
      p' : graphEl⁰ Φ a ≡ graphEl⁰ Ψ a
      p' = funExt⁻ p a

      els≡ : (elements x a ≡ elements x a) ×
         (elements (y a) (Φ a) ≡ elements (y a) (Ψ a))
      els≡ = orderedPair⁰≡orderedPair⁰ {x = elements x a} {y = elements (y a) (Φ a)}
                                    {a = elements x a} {b = elements (y a) (Ψ a)} .fst p'
      els≡₂ : elements (y a) (Φ a) ≡ elements (y a) (Ψ a)
      els≡₂ = els≡ .snd

  graphEl⁰-inj : Inj graphEl⁰
  graphEl⁰-inj {Φ} {Ψ} p = funExt λ a → graphEl⁰-inj' Φ Ψ a p

  graphEl⁰-emb : isEmbedding graphEl⁰
  graphEl⁰-emb = injEmbedding {A = (a : El⁰ x) → El⁰ (y a)} {B = El⁰ x → V⁰} {f = graphEl⁰}
                              (isSet→ {A' = V⁰ {ℓ}} {A = El⁰ {ℓ} x} (isSetV⁰ {ℓ})) graphEl⁰-inj

module Graph {ℓ : Level} {x : V⁰ {ℓ}} {y : El⁰ {ℓ} x → V⁰ {ℓ}} where
  open GraphElements {ℓ} {x} {y}

  graph⁰ : ((a : El⁰ {ℓ} x) → El⁰ {ℓ} (y a)) → V⁰ {ℓ}
  graph⁰ Φ = fromEmb E
    where
      E : Embedding V⁰ ℓ
      E .fst = El⁰ x
      E .snd .fst = FstConst.graphEl⁰' Φ
      E .snd .snd = FstConst.emb Φ

  graph⁰-inj : Inj graph⁰
  graph⁰-inj {Φ} {Ψ} p = graphEl⁰-inj P
    where
      F : ((z : V⁰) → z ∈⁰ graph⁰ Φ → z ∈⁰ graph⁰ Ψ)
           × ((z : V⁰) → z ∈⁰ graph⁰ Ψ → z ∈⁰ graph⁰ Φ)
      F = ≡V⁰-≃-≃V⁰ {x = graph⁰ Φ} {y = graph⁰ Ψ} .fst p

      F₂ : (z : V⁰) → z ∈⁰ graph⁰ Ψ → z ∈⁰ graph⁰ Φ
      F₂ = F .snd

      module _ (a : El⁰ x) where
        s : V⁰
        s = graphEl⁰ Ψ a

        s∈Ψ : s ∈⁰ graph⁰ Ψ
        s∈Ψ .fst = a
        s∈Ψ .snd = refl

        s∈Φ : s ∈⁰ graph⁰ Φ
        s∈Φ = F₂ s s∈Ψ

        a' : El⁰ x
        a' = s∈Φ .fst

        graphEl⁰≡' : graphEl⁰ Φ a' ≡ graphEl⁰ Ψ a
        graphEl⁰≡' = s∈Φ .snd

        els≡ : elements x a' ≡ elements x a
        els≡ = orderedPair⁰≡orderedPair⁰ {x = elements x a'} {y = elements (y a') (Φ a')}
                                         {a = elements x a } {b = elements (y a)  (Ψ a) } .fst graphEl⁰≡' .fst

        a'≡a : a' ≡ a
        a'≡a = isEmbedding→Inj {A = El⁰ x} {B = V⁰ {ℓ}} {f = elements x}
                (isEmbedding-elements x) a' a els≡

        graphEl⁰≡ : graphEl⁰ Φ a ≡ graphEl⁰ Ψ a
        graphEl⁰≡ = transport (cong (λ m → graphEl⁰ Φ m ≡ graphEl⁰ Ψ a) a'≡a) graphEl⁰≡'

      P : graphEl⁰ Φ ≡ graphEl⁰ Ψ
      P = funExt graphEl⁰≡

  graph⁰-emb : isEmbedding graph⁰
  graph⁰-emb = injEmbedding {A = (a : El⁰ x) → El⁰ (y a)} {B = V⁰} {f = graph⁰} (isSetV⁰ {ℓ}) graph⁰-inj

private
  variable
    ℓ : Level
    x : V⁰ {ℓ}
    y : El⁰ x → V⁰ {ℓ}

Π⁰ : (x : V⁰ {ℓ}) → (El⁰ x → V⁰ {ℓ}) → V⁰ {ℓ}
Π⁰ {ℓ} x y = fromEmb E
  where
    E : Embedding V⁰ ℓ
    E .fst = (a : El⁰ x) → El⁰ (y a)
    E .snd .fst = Graph.graph⁰ {ℓ} {x} {y}
    E .snd .snd = Graph.graph⁰-emb {ℓ} {x} {y}

El⁰Π⁰isΠ : El⁰ (Π⁰ x y) ≡ ((a : El⁰ x) → El⁰ (y a))
El⁰Π⁰isΠ = refl

_→⁰_ : V⁰ {ℓ} → V⁰ {ℓ} → V⁰ {ℓ}
x →⁰ y = Π⁰ x (λ _ → y)

El⁰→⁰is→ : {x y : V⁰ {ℓ}} → El⁰ (x →⁰ y) ≡ (El⁰ x → El⁰ y)
El⁰→⁰is→ = refl
