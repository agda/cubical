{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

-- Displayed categories with hom-sets
record DisplayedCat (C : Category ℓC ℓC') ℓD ℓD' : Type (ℓ-suc (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD'))) where
  no-eta-equality
  open Category C
  field
    ob[_] : ob → Type ℓD
    Hom[_][_,_] : {x y : ob} → Hom[ x , y ] → ob[ x ] → ob[ y ] → Type ℓD'
    idᴰ : ∀ {x} {p : ob[ x ]} → Hom[ id ][ p , p ]
    _⋆ᴰ_ : ∀ {x y z} {f : Hom[ x , y ]} {g : Hom[ y , z ]} {xᴰ yᴰ zᴰ}
      → Hom[ f ][ xᴰ , yᴰ ] → Hom[ g ][ yᴰ , zᴰ ] → Hom[ f ⋆ g ][ xᴰ , zᴰ ]

  infixr 9 _∘ᴰ_

  _≡[_]_ : ∀ {x y xᴰ yᴰ} {f g : Hom[ x , y ]} → Hom[ f ][ xᴰ , yᴰ ] → f ≡ g → Hom[ g ][ xᴰ , yᴰ ] → Type ℓD'
  _≡[_]_ {x} {y} {xᴰ} {yᴰ} fᴰ p gᴰ = PathP (λ i → Hom[ p i ][ xᴰ , yᴰ ]) fᴰ gᴰ

  infix 2 _≡[_]_

  field
    ⋆IdLᴰ : ∀ {x y} {f : Hom[ x , y ]} {xᴰ yᴰ} (fᴰ : Hom[ f ][ xᴰ , yᴰ ]) → idᴰ ⋆ᴰ fᴰ ≡[ ⋆IdL f ] fᴰ
    ⋆IdRᴰ : ∀ {x y} {f : Hom[ x , y ]} {xᴰ yᴰ} (fᴰ : Hom[ f ][ xᴰ , yᴰ ]) → fᴰ ⋆ᴰ idᴰ ≡[ ⋆IdR f ] fᴰ
    ⋆Assocᴰ : ∀ {x y z w} {f : Hom[ x , y ]} {g : Hom[ y , z ]}  {h : Hom[ z , w ]} {xᴰ yᴰ zᴰ wᴰ}
      (fᴰ : Hom[ f ][ xᴰ , yᴰ ]) (gᴰ : Hom[ g ][ yᴰ , zᴰ ]) (hᴰ : Hom[ h ][ zᴰ , wᴰ ])
      → (fᴰ ⋆ᴰ gᴰ) ⋆ᴰ hᴰ ≡[ ⋆Assoc f g h ] fᴰ ⋆ᴰ (gᴰ ⋆ᴰ hᴰ)
    isSetHomᴰ : ∀ {x y} {f : Hom[ x , y ]} {xᴰ yᴰ} → isSet Hom[ f ][ xᴰ , yᴰ ]

  -- composition: alternative to diagramatic order
  _∘ᴰ_ : ∀ {x y z} {f : Hom[ x , y ]} {g : Hom[ y , z ]} {xᴰ yᴰ zᴰ}
      → Hom[ g ][ yᴰ , zᴰ ] → Hom[ f ][ xᴰ , yᴰ ] → Hom[ f ⋆ g ][ xᴰ , zᴰ ]
  g ∘ᴰ f = f ⋆ᴰ g

open DisplayedCat

-- Helpful syntax/notation
_[_][_,_] = Hom[_][_,_]
