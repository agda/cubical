{-# OPTIONS --safe #-}
module Cubical.Categories.Category.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Powerset
open import Cubical.Data.Sigma

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

record isIso (C : Category ℓ ℓ'){x y : C .ob}(f : C [ x , y ]) : Type ℓ' where
  constructor isiso
  field
    inv : C [ y , x ]
    sec : inv ⋆⟨ C ⟩ f ≡ C .id
    ret : f ⋆⟨ C ⟩ inv ≡ C .id

open isIso

isPropIsIso : {C : Category ℓ ℓ'}{x y : C .ob}(f : C [ x , y ]) → isProp (isIso C f)
isPropIsIso {C = C} f p q i .inv =
    (sym (C .⋆IdL _)
  ∙ (λ i → q .sec (~ i) ⋆⟨ C ⟩ p .inv)
  ∙ C .⋆Assoc _ _ _
  ∙ (λ i → q .inv ⋆⟨ C ⟩ p .ret i)
  ∙ C .⋆IdR _) i
isPropIsIso {C = C} f p q i .sec j =
  isSet→SquareP (λ i j → C .isSetHom)
    (p .sec) (q .sec) (λ i → isPropIsIso {C = C} f p q i .inv ⋆⟨ C ⟩ f) refl i j
isPropIsIso {C = C} f p q i .ret j =
  isSet→SquareP (λ i j → C .isSetHom)
    (p .ret) (q .ret) (λ i → f ⋆⟨ C ⟩ isPropIsIso {C = C} f p q i .inv) refl i j


CatIso : (C : Category ℓ ℓ') (x y : C .ob) → Type ℓ'
CatIso C x y = Σ[ f ∈ C [ x , y ] ] isIso C f

CatIso≡ : {C : Category ℓ ℓ'}{x y : C .ob}(f g : CatIso C x y) → f .fst ≡ g .fst → f ≡ g
CatIso≡ f g = Σ≡Prop isPropIsIso

-- `constructor` of CatIso
catiso : {C : Category ℓ ℓ'}{x y : C .ob}
  → (mor : C [ x , y ])
  → (inv : C [ y , x ])
  → (sec : inv ⋆⟨ C ⟩ mor ≡ C .id)
  → (ret : mor ⋆⟨ C ⟩ inv ≡ C .id)
  → CatIso C x y
catiso mor inv sec ret = mor , isiso inv sec ret


idCatIso : {C : Category ℓ ℓ'} {x : C .ob} → CatIso C x x
idCatIso {C = C} = C .id , isiso (C .id) (C .⋆IdL (C .id)) (C .⋆IdL (C .id))

isSet-CatIso : {C : Category ℓ ℓ'} → ∀ x y → isSet (CatIso C x y)
isSet-CatIso {C = C} x y = isOfHLevelΣ 2 (C .isSetHom) (λ f → isProp→isSet (isPropIsIso f))


pathToIso : {C : Category ℓ ℓ'} {x y : C .ob} (p : x ≡ y) → CatIso C x y
pathToIso {C = C} p = J (λ z _ → CatIso C _ z) idCatIso p

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
  CatIsoToPath = invEq (univEquiv _ _)

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
