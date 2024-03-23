{-
  wild categories, analogous to the formalization in Coq-HoTT

  https://github.com/HoTT/Coq-HoTT/tree/master/theories/WildCat

-}
{-# OPTIONS --safe #-}
module Cubical.WildCat.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma renaming (_×_ to _×'_)

private
  variable
    ℓ ℓ' : Level

record WildCat ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  no-eta-equality
  field
    ob : Type ℓ
    Hom[_,_] : ob → ob → Type ℓ'
    id   : ∀ {x} → Hom[ x , x ]
    _⋆_  : ∀ {x y z} (f : Hom[ x , y ]) (g : Hom[ y , z ]) → Hom[ x , z ]
    ⋆IdL : ∀ {x y} (f : Hom[ x , y ]) → id ⋆ f ≡ f
    ⋆IdR : ∀ {x y} (f : Hom[ x , y ]) → f ⋆ id ≡ f
    ⋆Assoc : ∀ {u v w x} (f : Hom[ u , v ]) (g : Hom[ v , w ]) (h : Hom[ w , x ])
      → (f ⋆ g) ⋆ h ≡ f ⋆ (g ⋆ h)

  -- composition: alternative to diagramatic order
  _∘_ : ∀ {x y z} (g : Hom[ y , z ]) (f : Hom[ x , y ]) → Hom[ x , z ]
  g ∘ f = f ⋆ g

open WildCat

-- Helpful syntax/notation
_[_,_] : (C : WildCat ℓ ℓ') → (x y : C .ob) → Type ℓ'
_[_,_] = Hom[_,_]

-- Needed to define this in order to be able to make the subsequence syntax declaration
seq' : ∀ (C : WildCat ℓ ℓ') {x y z} (f : C [ x , y ]) (g : C [ y , z ]) → C [ x , z ]
seq' = _⋆_

infixl 15 seq'
syntax seq' C f g = f ⋆⟨ C ⟩ g

-- composition
comp' : ∀ (C : WildCat ℓ ℓ') {x y z} (g : C [ y , z ]) (f : C [ x , y ]) → C [ x , z ]
comp' = _∘_

infixr 16 comp'
syntax comp' C g f = g ∘⟨ C ⟩ f

-- Isomorphisms in wild categories (analogous to HoTT-terminology for maps between types)
record WildCatIso (C : WildCat ℓ ℓ') (x y : C .ob) : Type ℓ' where
  no-eta-equality
  constructor wildiso
  field
    mor : C [ x , y ]
    inv : C [ y , x ]
    sec : inv ⋆⟨ C ⟩ mor ≡ C .id
    ret : mor ⋆⟨ C ⟩ inv ≡ C .id

idIso : {C : WildCat ℓ ℓ'} {x : C .ob} → WildCatIso C x x
idIso {C = C} = wildiso (C .id ) (C .id) (C .⋆IdL (C .id)) (C .⋆IdL (C .id))

pathToIso : {C : WildCat ℓ ℓ'} {x y : C .ob} (p : x ≡ y) → WildCatIso C x y
pathToIso {C = C} p = J (λ z _ → WildCatIso C _ z) idIso p

-- Natural isomorphisms
module _ {C : WildCat ℓ ℓ'}
  {x y : C .ob} (f : Hom[_,_] C x y) where
  record wildIsIso : Type (ℓ-max ℓ ℓ') where
    no-eta-equality
    field
      inv' : Hom[_,_] C y x
      sect : _⋆_ C inv' f ≡ id C {y}
      retr : _⋆_ C f inv' ≡ id C {x}

-- Opposite wild category
_^op : WildCat ℓ ℓ' → WildCat ℓ ℓ'
(C ^op) .ob = C .ob
(C ^op) .Hom[_,_] x y = C .Hom[_,_] y x
(C ^op) .id = C .id
(C ^op) ._⋆_ f g = C ._⋆_ g f
(C ^op) .⋆IdL = C .⋆IdR
(C ^op) .⋆IdR = C .⋆IdL
(C ^op) .⋆Assoc f g h = sym (C .⋆Assoc _ _ _)
