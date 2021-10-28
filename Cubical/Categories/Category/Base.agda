{-# OPTIONS --safe #-}


module Cubical.Categories.Category.Base where

open import Cubical.Core.Glue
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

private
  variable
    ℓ ℓ' : Level

-- Precategories

record Precategory ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  -- no-eta-equality ; NOTE: need eta equality for `opop`
  field
    ob : Type ℓ
    Hom[_,_] : ob → ob → Type ℓ'
    id : ∀ x → Hom[ x , x ]
    _⋆_ : ∀ {x y z} (f : Hom[ x , y ]) (g : Hom[ y , z ]) → Hom[ x , z ]
    -- TODO: change these to implicit argument
    ⋆IdL : ∀ {x y : ob} (f : Hom[ x , y ]) → (id x) ⋆ f ≡ f
    ⋆IdR : ∀ {x y} (f : Hom[ x , y ]) → f ⋆ (id y) ≡ f
    ⋆Assoc : ∀ {u v w x} (f : Hom[ u , v ]) (g : Hom[ v , w ]) (h : Hom[ w , x ]) → (f ⋆ g) ⋆ h ≡ f ⋆ (g ⋆ h)

  -- composition: alternative to diagramatic order
  _∘_ : ∀ {x y z} (g : Hom[ y , z ]) (f : Hom[ x , y ]) → Hom[ x , z ]
  g ∘ f = f ⋆ g

open Precategory


-- Helpful syntax/notation

_[_,_] : (C : Precategory ℓ ℓ') → (x y : C .ob) → Type ℓ'
_[_,_] = Hom[_,_]

-- needed to define this in order to be able to make the subsequence syntax declaration
seq' : ∀ (C : Precategory ℓ ℓ') {x y z} (f : C [ x , y ]) (g : C [ y , z ]) → C [ x , z ]
seq' = _⋆_

infixl 15 seq'
syntax seq' C f g = f ⋆⟨ C ⟩ g

-- composition
comp' : ∀ (C : Precategory ℓ ℓ') {x y z} (g : C [ y , z ]) (f : C [ x , y ]) → C [ x , z ]
comp' = _∘_

infixr 16 comp'
syntax comp' C g f = g ∘⟨ C ⟩ f


-- Categories

record isCategory (C : Precategory ℓ ℓ') : Type (ℓ-max ℓ ℓ') where
  field
    isSetHom : ∀ {x y} → isSet (C [ x , y ])

-- Isomorphisms and paths in precategories

record CatIso {C : Precategory ℓ ℓ'} (x y : C .Precategory.ob) : Type ℓ' where
  constructor catiso
  field
    mor : C [ x , y ]
    inv : C [ y , x ]
    sec : inv ⋆⟨ C ⟩ mor ≡ C .id y
    ret : mor ⋆⟨ C ⟩ inv ≡ C .id x


pathToIso : {C : Precategory ℓ ℓ'} (x y : C .ob) (p : x ≡ y) → CatIso {C = C} x y
pathToIso {C = C} x y p = J (λ z _ → CatIso x z) (catiso (C .id x) idx (C .⋆IdL idx) (C .⋆IdL idx)) p
  where
    idx = C .id x

-- Univalent Categories

record isUnivalent (C : Precategory ℓ ℓ') : Type (ℓ-max ℓ ℓ') where
  field
    univ : (x y : C .ob) → isEquiv (pathToIso {C = C} x y)

  -- package up the univalence equivalence
  univEquiv : ∀ (x y : C .ob) → (x ≡ y) ≃ (CatIso x y)
  univEquiv x y = (pathToIso {C = C} x y) , (univ x y)

  -- The function extracting paths from category-theoretic isomorphisms.
  CatIsoToPath : {x y : C .ob} (p : CatIso x y) → x ≡ y
  CatIsoToPath {x = x} {y = y} p =
    equivFun (invEquiv (univEquiv x y)) p

open isUnivalent public

-- Opposite Categories

_^op : Precategory ℓ ℓ' → Precategory ℓ ℓ'
(C ^op) .ob = C .ob
(C ^op) .Hom[_,_] x y = C .Hom[_,_] y x
(C ^op) .id = C .id
(C ^op) ._⋆_ f g = C ._⋆_ g f
(C ^op) .⋆IdL = C .⋆IdR
(C ^op) .⋆IdR = C .⋆IdL
(C ^op) .⋆Assoc f g h = sym (C .⋆Assoc _ _ _)

open isCategory public
