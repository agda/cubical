{-# OPTIONS --safe #-}
module Cubical.Categories.Category.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

private
  variable
    ℓ ℓ' : Level

-- Categories with hom-sets
record Category ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  -- no-eta-equality ; NOTE: need eta equality for `opop`
  field
    ob : Type ℓ
    Hom[_,_] : ob → ob → Type ℓ'
    id   : ∀ {x} → Hom[ x , x ]
    _⋆_  : ∀ {x y z} (f : Hom[ x , y ]) (g : Hom[ y , z ]) → Hom[ x , z ]
    ⋆IdL : ∀ {x y} (f : Hom[ x , y ]) → id ⋆ f ≡ f
    ⋆IdR : ∀ {x y} (f : Hom[ x , y ]) → f ⋆ id ≡ f
    ⋆Assoc : ∀ {x y z w} (f : Hom[ x , y ]) (g : Hom[ y , z ]) (h : Hom[ z , w ])
           → (f ⋆ g) ⋆ h ≡ f ⋆ (g ⋆ h)
    isSetHom : ∀ {x y} → isSet Hom[ x , y ]

  -- composition: alternative to diagramatic order
  _∘_ : ∀ {x y z} (g : Hom[ y , z ]) (f : Hom[ x , y ]) → Hom[ x , z ]
  g ∘ f = f ⋆ g

  infixr 9 _⋆_
  infixr 9 _∘_

open Category

-- Helpful syntax/notation
_[_,_] : (C : Category ℓ ℓ') → (x y : C .ob) → Type ℓ'
_[_,_] = Hom[_,_]

-- Needed to define this in order to be able to make the subsequence syntax declaration
seq' : ∀ (C : Category ℓ ℓ') {x y z} (f : C [ x , y ]) (g : C [ y , z ]) → C [ x , z ]
seq' = _⋆_

infixl 15 seq'
syntax seq' C f g = f ⋆⟨ C ⟩ g

-- composition
comp' : ∀ (C : Category ℓ ℓ') {x y z} (g : C [ y , z ]) (f : C [ x , y ]) → C [ x , z ]
comp' = _∘_

infixr 16 comp'
syntax comp' C g f = g ∘⟨ C ⟩ f

-- Isomorphisms and paths in categories
record CatIso (C : Category ℓ ℓ') (x y : C .ob) : Type ℓ' where
  constructor catiso
  field
    mor : C [ x , y ]
    inv : C [ y , x ]
    sec : inv ⋆⟨ C ⟩ mor ≡ C .id
    ret : mor ⋆⟨ C ⟩ inv ≡ C .id

pathToIso : {C : Category ℓ ℓ'} {x y : C .ob} (p : x ≡ y) → CatIso C x y
pathToIso {C = C} p = J (λ z _ → CatIso _ _ z) (catiso idx idx (C .⋆IdL idx) (C .⋆IdL idx)) p
  where
    idx = C .id

-- Univalent Categories
record isUnivalent (C : Category ℓ ℓ') : Type (ℓ-max ℓ ℓ') where
  field
    univ : (x y : C .ob) → isEquiv (pathToIso {C = C} {x = x} {y = y})

  -- package up the univalence equivalence
  univEquiv : ∀ (x y : C .ob) → (x ≡ y) ≃ (CatIso _ x y)
  univEquiv x y = pathToIso , univ x y

  -- The function extracting paths from category-theoretic isomorphisms.
  CatIsoToPath : {x y : C .ob} (p : CatIso _ x y) → x ≡ y
  CatIsoToPath {x = x} {y = y} p =
    equivFun (invEquiv (univEquiv x y)) p

-- Opposite category
_^op : Category ℓ ℓ' → Category ℓ ℓ'
ob (C ^op)           = ob C
Hom[_,_] (C ^op) x y = C [ y , x ]
id (C ^op)           = id C
_⋆_ (C ^op) f g      = g ⋆⟨ C ⟩ f
⋆IdL (C ^op)         = C .⋆IdR
⋆IdR (C ^op)         = C .⋆IdL
⋆Assoc (C ^op) f g h = sym (C .⋆Assoc _ _ _)
isSetHom (C ^op)     = C .isSetHom
