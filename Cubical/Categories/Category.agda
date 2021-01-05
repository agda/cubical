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

module _ {C : Precategory ℓ ℓ'} ⦃ isC : isCategory C ⦄ where
  open isCategory isC
  -- isSet where your allowed to compare paths where one side is only
  -- equal up to path. Is there a generalization of this?
  isSetHomP1 : ∀ {x y : C .ob} {n : C [ x , y ]}
            → isOfHLevelDep 1 (λ m → m ≡ n)
  isSetHomP1 {x = x} {y} {n} = isOfHLevel→isOfHLevelDep 1 (λ m → isSetHom m n)

  -- isSet where the arrows can be between non-definitionally equal obs
  isSetHomP2l : ∀ {y : C .ob}
            → isOfHLevelDep 2 (λ x → C [ x , y ])
  isSetHomP2l = isOfHLevel→isOfHLevelDep 2 (λ a → isSetHom {x = a})

  isSetHomP2r : ∀ {x : C .ob}
              → isOfHLevelDep 2 (λ y → C [ x , y ])
  isSetHomP2r = isOfHLevel→isOfHLevelDep 2 (λ a → isSetHom {y = a})


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

module _ {C : Precategory ℓ ℓ'} ⦃ isU : isUnivalent C ⦄ where

  -- package up the univalence equivalence
  univEquiv : ∀ (x y : C .ob) → (x ≡ y) ≃ (CatIso x y)
  univEquiv x y = (pathToIso {C = C} x y) , (isU .univ x y)

-- Opposite Categories

_^op : Precategory ℓ ℓ' → Precategory ℓ ℓ'
(C ^op) .ob = C .ob
(C ^op) .Hom[_,_] x y = C .Hom[_,_] y x
(C ^op) .id = C .id
(C ^op) ._⋆_ f g = C ._⋆_ g f
(C ^op) .⋆IdL = C .⋆IdR
(C ^op) .⋆IdR = C .⋆IdL
(C ^op) .⋆Assoc f g h = sym (C .⋆Assoc _ _ _)

-- instance
--   open isCategory
--   isCatOp : {C : Precategory ℓ ℓ'} ⦃ isCatC : isCategory C ⦄
--           → isCategory (C ^op)
--   isCatOp {C = C} ⦃ isCatC ⦄ .isSetHom = isCatC .isSetHom

-- opposite of opposite is cool
opop : ∀ {C : Precategory ℓ ℓ'} → (C ^op) ^op ≡ C
opop = refl

open isCategory public

-- opposite of opposite is definitionally equal to itself
involutiveOp : ∀ {C : Precategory ℓ ℓ'} → (C ^op) ^op ≡ C
involutiveOp = refl

module _ {C : Precategory ℓ ℓ'} where
  -- Other useful operations on categories

  -- whisker the parallel morphisms g and g' with f
  lPrecatWhisker : {x y z : C .ob} (f : C [ x , y ]) (g g' : C [ y , z ]) (p : g ≡ g') → f ⋆⟨ C ⟩ g ≡ f ⋆⟨ C ⟩ g'
  lPrecatWhisker f _ _ p = cong (_⋆_ C f) p

  rPrecatWhisker : {x y z : C .ob} (f f' : C [ x , y ]) (g : C [ y , z ]) (p : f ≡ f') → f ⋆⟨ C ⟩ g ≡ f' ⋆⟨ C ⟩ g
  rPrecatWhisker _ _ g p = cong (λ v → v ⋆⟨ C ⟩ g) p

  -- working with equal objects
  idP : ∀ {x x'} {p : x ≡ x'} → C [ x , x' ]
  idP {x = x} {x'} {p} = subst (λ v → C [ x , v ]) p (C .id x)

  -- heterogeneous seq
  seqP : ∀ {x y y' z} {p : y ≡ y'}
       → (f : C [ x , y ]) (g : C [ y' , z ])
       → C [ x , z ]
  seqP {x = x} {_} {_} {z} {p} f g = f ⋆⟨ C ⟩ (subst (λ a → C [ a , z ]) (sym p) g)

  -- also heterogeneous seq, but substituting on the left
  seqP' : ∀ {x y y' z} {p : y ≡ y'}
       → (f : C [ x , y ]) (g : C [ y' , z ])
       → C [ x , z ]
  seqP' {x = x} {_} {_} {z} {p} f g = subst (λ a → C [ x , a ]) p f ⋆⟨ C ⟩ g

  -- show that they're equal
  seqP≡seqP' : ∀ {x y y' z} {p : y ≡ y'}
             → (f : C [ x , y ]) (g : C [ y' , z ])
             → seqP {p = p} f g ≡ seqP' {p = p} f g
  seqP≡seqP' {x = x} {z = z} {p = p} f g i =
    (toPathP {A = λ i' → C [ x , p i' ]} {f} refl i)
      ⋆⟨ C ⟩
    (toPathP {A = λ i' → C [ p (~ i') , z ]} {x = g} (sym refl) (~ i))

  -- seqP is equal to normal seq when y ≡ y'
  seqP≡seq : ∀ {x y z}
             → (f : C [ x , y ]) (g : C [ y , z ])
             → seqP {p = refl} f g ≡ f ⋆⟨ C ⟩ g
  seqP≡seq {y = y} {z} f g i = f ⋆⟨ C ⟩ toPathP {A = λ _ → C [ y , z ]} {x = g} refl (~ i)


  -- whiskering with heterogenous seq -- (maybe should let z be heterogeneous too)
  lPrecatWhiskerP : {x y z y' : C .ob} {p : y ≡ y'}
                  → (f : C [ x , y ]) (g : C [ y , z ]) (g' : C [ y' , z ])
                  → (r : PathP (λ i → C [ p i , z ]) g g')
                  → f ⋆⟨ C ⟩ g ≡ seqP {p = p} f g'
  lPrecatWhiskerP f g g' r = cong (λ v → f ⋆⟨ C ⟩ v) (sym (fromPathP (symP r)))

  rPrecatWhiskerP : {x y' y z : C .ob} {p : y' ≡ y}
                  → (f' : C [ x , y' ]) (f : C [ x , y ]) (g : C [ y , z ])
                  → (r : PathP (λ i → C [ x , p i ]) f' f)
                  → f ⋆⟨ C ⟩ g ≡ seqP' {p = p} f' g
  rPrecatWhiskerP f' f g r = cong (λ v → v ⋆⟨ C ⟩ g) (sym (fromPathP r))
