{-# OPTIONS --safe #-}
module Cubical.Categories.Category.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Powerset

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

idCatIso : {C : Category ℓ ℓ'} {x : C .ob} → CatIso C x x
idCatIso {C = C} = (catiso (C .id) (C .id) (C .⋆IdL (C .id)) (C .⋆IdL (C .id)))

isSet-CatIso : {C : Category ℓ ℓ'} → ∀ x y → isSet (CatIso C x y)
isSet-CatIso {C = C} x y F G p q = w
  where
    w : _
    CatIso.mor (w i j) = isSetHom C _ _ (cong CatIso.mor p) (cong CatIso.mor q) i j
    CatIso.inv (w i j) = isSetHom C _ _ (cong CatIso.inv p) (cong CatIso.inv q) i j
    CatIso.sec (w i j) =
       isSet→SquareP
       (λ i j → isProp→isSet {A = CatIso.inv (w i j) ⋆⟨ C ⟩ CatIso.mor (w i j) ≡ C .id} (isSetHom C _ _))
       (cong CatIso.sec p) (cong CatIso.sec q) (λ _ → CatIso.sec F) (λ _ → CatIso.sec G) i j
    CatIso.ret (w i j) =
       isSet→SquareP
       (λ i j → isProp→isSet {A = CatIso.mor (w i j) ⋆⟨ C ⟩ CatIso.inv (w i j) ≡ C .id} (isSetHom C _ _))
       (cong CatIso.ret p) (cong CatIso.ret q) (λ _ → CatIso.ret F) (λ _ → CatIso.ret G) i j


pathToIso : {C : Category ℓ ℓ'} {x y : C .ob} (p : x ≡ y) → CatIso C x y
pathToIso {C = C} p = J (λ z _ → CatIso _ _ z) idCatIso p

pathToIso-refl : {C : Category ℓ ℓ'} {x : C .ob} → pathToIso {C = C} {x} refl ≡ idCatIso
pathToIso-refl {C = C} {x} = JRefl (λ z _ → CatIso C x z) (idCatIso)

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

  isGroupoid-ob : isGroupoid (C .ob)
  isGroupoid-ob = isOfHLevelPath'⁻ 2 (λ _ _ → isOfHLevelRespectEquiv 2 (invEquiv (univEquiv _ _)) (isSet-CatIso _ _))

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


ΣPropCat : (C : Category ℓ ℓ') (P : ℙ (ob C)) → Category ℓ ℓ'
ob (ΣPropCat C P) = Σ[ x ∈ ob C ] x ∈ P
Hom[_,_] (ΣPropCat C P) x y = C [ fst x , fst y ]
id (ΣPropCat C P) = id C
_⋆_ (ΣPropCat C P) = _⋆_ C
⋆IdL (ΣPropCat C P) = ⋆IdL C
⋆IdR (ΣPropCat C P) = ⋆IdR C
⋆Assoc (ΣPropCat C P) = ⋆Assoc C
isSetHom (ΣPropCat C P) = isSetHom C
