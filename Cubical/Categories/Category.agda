{-
  Definition of various kinds of categories.

  This library follows the UniMath terminology, that is:

  Concept              Ob C   Hom C  Univalence

  Precategory          Type   Type   No
  Category             Type   Set    No
  Univalent Category   Type   Set    Yes

  This file also contains
    - pathToIso : Turns a path between two objects into an isomorphism between them
    - opposite categories


-}

{-# OPTIONS --cubical --no-import-sorts --safe #-}


module Cubical.Categories.Category where

open import Cubical.Core.Glue
open import Cubical.Foundations.Prelude

-- Precategories

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

-- Categories

record isCategory {ℓ ℓ'} (𝒞 : Precategory ℓ ℓ') : Type (ℓ-max ℓ ℓ') where
  field
    homIsSet : ∀ {x y} → isSet (𝒞 .hom x y)

open isCategory public

-- Isomorphisms and paths in precategories

record CatIso {ℓ ℓ' : Level} {𝒞 : Precategory ℓ ℓ'} (x y : 𝒞 .ob) : Type ℓ' where
  constructor catiso
  field
    h : 𝒞 .hom x y
    h⁻¹ : 𝒞 .hom y x
    sec : 𝒞 .seq h⁻¹ h ≡ 𝒞 .idn y
    ret : 𝒞 .seq h h⁻¹ ≡ 𝒞 .idn x

idCatIso : {ℓ ℓ' : Level} {𝒞 : Precategory ℓ ℓ'} (x : 𝒞 .ob) → CatIso {𝒞 = 𝒞} x x
idCatIso {𝒞 = 𝒞} x = catiso (𝒞 .idn x) (𝒞 .idn x) (𝒞 .seq-λ (𝒞 .idn x)) (𝒞 .seq-λ (𝒞 .idn x))

pathToIso : {ℓ ℓ' : Level} {𝒞 : Precategory ℓ ℓ'} (x y : 𝒞 .ob) (p : x ≡ y) → CatIso {𝒞 = 𝒞} x y
pathToIso {𝒞 = 𝒞} x y p = J (λ z _ → CatIso x z) (catiso (𝒞 .idn x) idx (𝒞 .seq-λ idx) (𝒞 .seq-λ idx)) p
  where
    idx = 𝒞 .idn x

-- Univalent Categories

record isUnivalent {ℓ ℓ'} (𝒞 : Precategory ℓ ℓ') : Type (ℓ-max ℓ ℓ') where
  field
    univ : (x y : 𝒞 .ob) → isEquiv (pathToIso {𝒞 = 𝒞} x y)

open isUnivalent public

-- Opposite Categories

_^op : ∀ {ℓ ℓ'} → Precategory ℓ ℓ' → Precategory ℓ ℓ'
(𝒞 ^op) .ob = 𝒞 .ob
(𝒞 ^op) .hom x y = 𝒞 .hom y x
(𝒞 ^op) .idn = 𝒞 .idn
(𝒞 ^op) .seq f g = 𝒞 .seq g f
(𝒞 ^op) .seq-λ = 𝒞 .seq-ρ
(𝒞 ^op) .seq-ρ = 𝒞 .seq-λ
(𝒞 ^op) .seq-α f g h = sym (𝒞 .seq-α _ _ _)
