{-# OPTIONS --cubical #-}

module Cubical.Categories.Category where

open import Cubical.Foundations.Prelude

record Precategory ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  no-eta-equality
  field
    ob : Type ℓ
    hom : ob → ob → Type ℓ'
    idn : ∀ x → hom x x
    seq : ∀ {x y z} (f : hom x y) (g : hom y z) → hom x z
    seq-λ : ∀ {x y : ob} (f : hom x y) → seq (idn x) f ≡ f
    seq-ρ : ∀ {x y} (f : hom x y) → seq f (idn y) ≡ f
    seq-α : ∀ {u v w x} (f : hom u v) (g : hom v w) (h : hom w x) → seq (seq f g) h ≡ seq f (seq g h)

open Precategory public

record isCategory {ℓ ℓ'} (𝒞 : Precategory ℓ ℓ') : Type (ℓ-max ℓ ℓ') where
  field
    homIsSet : ∀ {x y} → isSet (𝒞 .hom x y)

open isCategory public

_^op : ∀ {ℓ ℓ'} → Precategory ℓ ℓ' → Precategory ℓ ℓ'
(𝒞 ^op) .ob = 𝒞 .ob
(𝒞 ^op) .hom x y = 𝒞 .hom y x
(𝒞 ^op) .idn = 𝒞 .idn
(𝒞 ^op) .seq f g = 𝒞 .seq g f
(𝒞 ^op) .seq-λ = 𝒞 .seq-ρ
(𝒞 ^op) .seq-ρ = 𝒞 .seq-λ
(𝒞 ^op) .seq-α f g h = sym (𝒞 .seq-α _ _ _)
