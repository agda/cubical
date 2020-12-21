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


-- Other useful operations on categories

-- whisker the parallel morphisms g and g' with f
lPrecatWhisker : {C : Precategory ℓ ℓ'} {x y z : C .ob} (f : C [ x , y ]) (g g' : C [ y , z ]) (p : g ≡ g') → f ⋆⟨ C ⟩ g ≡ f ⋆⟨ C ⟩ g'
lPrecatWhisker {C = C} f _ _ p = cong (_⋆_ C f) p

-- working with equal objects
module _ {C : Precategory ℓ ℓ'} {x x'} (p : x ≡ x') where
  -- id≡ : ∀ {x x'}
  --     → (x ≡ x')
  id≡ : C [ x , x' ]
  id≡ = subst (λ v → C [ x , v ]) p (C .id x)

  ⋆IdL≡ : ∀ {y : C .ob} {f' : C [ x' , y ]}
        → PathP (λ i → C [ p i , y ]) (id≡ ⋆⟨ C ⟩ f') f'
  ⋆IdL≡ {y} {f'} = symP {A = λ i → C [ p (~ i) , y ]} (toPathP (sym (idf'≡idf ∙ idf≡f))) --  compPathP' {A = C .ob} {B = λ a → {!C [ a , y ]!}} {p = refl} (idf'≡idf ∙ idf≡f) f≡f'
    where
      idl : (C .id x') ⋆⟨ C ⟩ f' ≡ f'
      idl = {!!}
      id≡id : PathP (λ i → C [ x , p (~ i) ]) id≡ (C .id _)
      id≡id = symP {A = (λ i → C [ x , p i ])} (toPathP refl)

      f = subst (C [_, y ]) (sym p) f'

      f≡f' : PathP (λ i → C [ p i , y ]) f f'
      f≡f' = symP {A = λ i → C [ p (~ i) , y ]} (toPathP refl)

      idf'≡idf : id≡ ⋆⟨ C ⟩ f' ≡ (C .id x) ⋆⟨ C ⟩ f
      idf'≡idf i = id≡id i ⋆⟨ C ⟩ f≡f' (~ i)

      idf≡f : (C .id x) ⋆⟨ C ⟩ f ≡ f
      idf≡f = C .⋆IdL _

module _ {C : Precategory ℓ ℓ'} {x x'} (p : x ≡ x') where

  id' = id≡ {C = C} (sym p)

  ⋆IdR≡ : ∀ {w : C .ob} {f : C [ w , x ]}
        → PathP (λ i → C [ w , p (~ i) ]) (f ⋆⟨ C ⟩ (id')) f
  ⋆IdR≡ {w} {f} = {!!}
    where
      id≡id : PathP (λ i → C [ p i , x' ]) (id') (C .id _)
      id≡id = symP {A = {!!}} (toPathP {!!})

      f' = subst (C [ w ,_]) p f

      f≡f' : PathP (λ i → C [ w , p i ]) f f'
      f≡f' = toPathP refl

      fid≡f'id : (f ⋆⟨ C ⟩ (id')) ≡ f' ⋆⟨ C ⟩ (C .id _)
      fid≡f'id i = f≡f' i ⋆⟨ C ⟩ {!id≡id (~ i)!}

      idf≡f : f' ⋆⟨ C ⟩ (C .id _) ≡ f'
      idf≡f = C .⋆IdR _
