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

private
  variable
    ℓ ℓ' : Level

-- Precategories

record Precategory ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  no-eta-equality
  field
    ob : Type ℓ
    Hom[_,_] : ob → ob → Type ℓ'
    id : ∀ x → Hom[ x , x ]
    _⋆_ : ∀ {x y z} (f : Hom[ x , y ]) (g : Hom[ y , z ]) → Hom[ x , z ]
    seq-λ : ∀ {x y : ob} (f : Hom[ x , y ]) → (id x) ⋆ f ≡ f
    seq-ρ : ∀ {x y} (f : Hom[ x , y ]) → f ⋆ (id y) ≡ f
    seq-α : ∀ {u v w x} (f : Hom[ u , v ]) (g : Hom[ v , w ]) (h : Hom[ w , x ]) → (f ⋆ g) ⋆ h ≡ f ⋆ (g ⋆ h)

  -- composition: alternative to diagramatic order
  _∘_ : ∀ {x y z} (g : Hom[ y , z ]) (f : Hom[ x , y ]) → Hom[ x , z ]
  g ∘ f = f ⋆ g

open Precategory public


-- Helpful syntax/notation

_[_,_] : (C : Precategory ℓ ℓ') → (x y : C .ob) → Type ℓ'
_[_,_] = Hom[_,_]

-- needed to define this in order to be able to make the subsequence syntax declaration
seq' : ∀ (C : Precategory ℓ ℓ') {x y z} (f : C [ x , y ]) (g : C [ y , z ]) → C [ x , z ]
seq' = _⋆_

infix 15 seq'
syntax seq' C f g = f ⋆⟨ C ⟩ g

-- composition
comp' : ∀ (C : Precategory ℓ ℓ') {x y z} (g : C [ y , z ]) (f : C [ x , y ]) → C [ x , z ]
comp' = _∘_

infix 16 comp'
syntax comp' C g f = g ∘⟨ C ⟩ f



-- Categories

record isCategory (C : Precategory ℓ ℓ') : Type (ℓ-max ℓ ℓ') where
  field
    homIsSet : ∀ {x y} → isSet (C [ x , y ])


-- Isomorphisms and paths in precategories

record CatIso {C : Precategory ℓ ℓ'} (x y : C .Precategory.ob) : Type ℓ' where
  constructor catiso
  field
    h : C [ x , y ]
    h⁻¹ : C [ y , x ]
    sec : (h⁻¹ ⋆⟨ C ⟩ h) ≡ C .id y
    ret : h ⋆⟨ C ⟩ h⁻¹ ≡ C .id x

pathToIso : {C : Precategory ℓ ℓ'} (x y : C .ob) (p : x ≡ y) → CatIso {C = C} x y
pathToIso {C = C} x y p = J (λ z _ → CatIso x z) (catiso (C .id x) idx (C .seq-λ idx) (C .seq-λ idx)) p
  where
    idx = C .id x

-- Univalent Categories

record isUnivalent (C : Precategory ℓ ℓ') : Type (ℓ-max ℓ ℓ') where
  field
    univ : (x y : C .ob) → isEquiv (pathToIso {C = C} x y)

open isUnivalent public

-- Opposite Categories

_^op : Precategory ℓ ℓ' → Precategory ℓ ℓ'
(C ^op) .ob = C .ob
(C ^op) .Hom[_,_] x y = C .Hom[_,_] y x
(C ^op) .id = C .id
(C ^op) ._⋆_ f g = C ._⋆_ g f
(C ^op) .seq-λ = C .seq-ρ
(C ^op) .seq-ρ = C .seq-λ
(C ^op) .seq-α f g h = sym (C .seq-α _ _ _)

open isCategory public
