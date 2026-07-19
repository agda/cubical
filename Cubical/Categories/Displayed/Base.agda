{-
  Definition of a category displayed over another category.
  Some definitions were guided by those at https://1lab.dev
-}
module Cubical.Categories.Displayed.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base

private
  variable
    ℓC ℓC' ℓD ℓD' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' : Level

-- Displayed categories with hom-sets
record Categoryᴰ (C : Category ℓC ℓC') ℓCᴰ ℓCᴰ' : Type (ℓ-suc (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓCᴰ ℓCᴰ'))) where
  no-eta-equality
  open Category C
  field
    ob[_] : ob → Type ℓCᴰ
    Hom[_][_,_] : {x y : ob} → Hom[ x , y ] → ob[ x ] → ob[ y ] → Type ℓCᴰ'
    idᴰ : ∀ {x} {p : ob[ x ]} → Hom[ id ][ p , p ]
    _⋆ᴰ_ : ∀ {x y z} {f : Hom[ x , y ]} {g : Hom[ y , z ]} {xᴰ yᴰ zᴰ}
      → Hom[ f ][ xᴰ , yᴰ ] → Hom[ g ][ yᴰ , zᴰ ] → Hom[ f ⋆ g ][ xᴰ , zᴰ ]

  infixr 9 _⋆ᴰ_
  infixr 9 _∘ᴰ_

  _≡[_]_ : ∀ {x y xᴰ yᴰ} {f g : Hom[ x , y ]} → Hom[ f ][ xᴰ , yᴰ ] → f ≡ g → Hom[ g ][ xᴰ , yᴰ ] → Type ℓCᴰ'
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

-- Helpful syntax/notation
_[_][_,_] = Categoryᴰ.Hom[_][_,_]

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  open Category C
  open Categoryᴰ Cᴰ

  record isIsoᴰ {a b : ob} {f : C [ a , b ]} (f-isIso : isIso C f)
    {aᴰ : ob[ a ]} {bᴰ : ob[ b ]} (fᴰ : Hom[ f ][ aᴰ , bᴰ ])
    : Type ℓCᴰ'
    where
    constructor isisoᴰ
    open isIso f-isIso
    field
      invᴰ : Hom[ inv ][ bᴰ , aᴰ ]
      secᴰ : invᴰ ⋆ᴰ fᴰ ≡[ sec ] idᴰ
      retᴰ : fᴰ ⋆ᴰ invᴰ ≡[ ret ] idᴰ

  CatIsoᴰ : {a b : ob} → CatIso C a b → ob[ a ] → ob[ b ] → Type ℓCᴰ'
  CatIsoᴰ (f , f-isIso) aᴰ bᴰ = Σ[ fᴰ ∈ Hom[ f ][ aᴰ , bᴰ ] ] isIsoᴰ f-isIso fᴰ

  idᴰCatIsoᴰ : {x : ob} {xᴰ : ob[ x ]} → CatIsoᴰ idCatIso xᴰ xᴰ
  idᴰCatIsoᴰ = idᴰ , isisoᴰ idᴰ (⋆IdLᴰ idᴰ) (⋆IdLᴰ idᴰ)

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  open Category
  private
    module Cᴰ = Categoryᴰ Cᴰ

  open Categoryᴰ
  _^opᴰ : Categoryᴰ (C ^op) ℓCᴰ ℓCᴰ'
  _^opᴰ .ob[_] x = Cᴰ.ob[ x ]
  _^opᴰ .Hom[_][_,_] f xᴰ yᴰ = Cᴰ.Hom[ f ][ yᴰ , xᴰ ]
  _^opᴰ .idᴰ = Cᴰ.idᴰ
  _^opᴰ ._⋆ᴰ_ fᴰ gᴰ = gᴰ Cᴰ.⋆ᴰ fᴰ
  _^opᴰ .⋆IdLᴰ = Cᴰ .⋆IdRᴰ
  _^opᴰ .⋆IdRᴰ = Cᴰ .⋆IdLᴰ
  _^opᴰ .⋆Assocᴰ fᴰ gᴰ hᴰ = symP (Cᴰ.⋆Assocᴰ _ _ _)
  _^opᴰ .isSetHomᴰ = Cᴰ .isSetHomᴰ
