module Cubical.Categories.Category.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Powerset

open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

private
  variable
    ℓ ℓ' : Level

-- Categories with hom-sets
record Category ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  -- TODO: document the impetus for this change
  no-eta-equality
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

  ⟨_⟩⋆⟨_⟩ : {x y z : ob} {f f' : Hom[ x , y ]} {g g' : Hom[ y , z ]}
          → f ≡ f' → g ≡ g' → f ⋆ g ≡ f' ⋆ g'
  ⟨ ≡f ⟩⋆⟨ ≡g ⟩ = cong₂ _⋆_ ≡f ≡g

  ⟨_⟩⋆⟨⟩ : {x y z : ob} {f f' : Hom[ x , y ]} {g : Hom[ y , z ]}
          → f ≡ f' → f ⋆ g ≡ f' ⋆ g
  ⟨ ≡f ⟩⋆⟨⟩ = cong (_⋆ _) ≡f

  ⟨⟩⋆⟨_⟩ : {x y z : ob} {f : Hom[ x , y ]} {g g' : Hom[ y , z ]}
          → g ≡ g' → f ⋆ g ≡ f ⋆ g'
  ⟨⟩⋆⟨ ≡g ⟩ = cong (_ ⋆_) ≡g

  infixr 9 _⋆_
  infixr 9 _∘_

open Category

-- Helpful syntax/notation
_[_,_] : (C : Category ℓ ℓ') → (x y : C .ob) → Type ℓ'
_[_,_] = Hom[_,_]

_End[_] : (C : Category ℓ ℓ') → (x : C .ob) → Type ℓ'
C End[ x ] = C [ x , x ]


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

pathToMorphism : {C : Category ℓ ℓ'} {x y : C .ob} (p : x ≡ y) → C [ x , y ]
pathToMorphism {C = C} p = pathToIso {C = C} p .fst

pathToIso-refl : {C : Category ℓ ℓ'} {x : C .ob} → pathToIso {C = C} {x} refl ≡ idCatIso
pathToIso-refl {C = C} {x} = JRefl (λ z _ → CatIso C x z) (idCatIso)

eqToIso : {C : Category ℓ ℓ'} {x y : C .ob} (p : x Eq.≡ y) → CatIso C x y
eqToIso {C = C} Eq.refl = idCatIso

eqToIso-refl : {C : Category ℓ ℓ'} {x : C .ob} → eqToIso {C = C} {x} Eq.refl ≡ idCatIso
eqToIso-refl = refl

eqToMorphism : {C : Category ℓ ℓ'} {x y : C .ob} (p : x Eq.≡ y) → C [ x , y ]
eqToMorphism {C = C} p = eqToIso {C = C} p .fst

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

isPropIsUnivalent : {C : Category ℓ ℓ'} → isProp (isUnivalent C)
isPropIsUnivalent =
 isPropRetract isUnivalent.univ _ (λ _ → refl)
  (isPropΠ2 λ _ _ → isPropIsEquiv _ )

-- Opposite category
-- TODO: move all of this to Constructions.Opposite?
_^op : Category ℓ ℓ' → Category ℓ ℓ'
ob (C ^op)           = ob C
Hom[_,_] (C ^op) x y = C [ y , x ]
id (C ^op)           = id C
_⋆_ (C ^op) f g      = g ⋆⟨ C ⟩ f
⋆IdL (C ^op)         = C .⋆IdR
⋆IdR (C ^op)         = C .⋆IdL
⋆Assoc (C ^op) f g h = sym (C .⋆Assoc _ _ _)
isSetHom (C ^op)     = C .isSetHom
