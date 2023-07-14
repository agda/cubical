{-
  Definition of a category displayed over another category.
  Some definitions were guided by those at https://1lab.dev
-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' : Level

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

-- Total category of a displayed category
module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where

  open Category
  open Categoryᴰ Cᴰ
  private
    module C = Category C

  ∫C : Category (ℓ-max ℓC ℓCᴰ) (ℓ-max ℓC' ℓCᴰ')
  ∫C .ob = Σ _ ob[_]
  ∫C .Hom[_,_] (_ , xᴰ) (_ , yᴰ) = Σ _ Hom[_][ xᴰ , yᴰ ]
  ∫C .id = _ , idᴰ
  ∫C ._⋆_ (_ , fᴰ) (_ , gᴰ) = _ , fᴰ ⋆ᴰ gᴰ
  ∫C .⋆IdL _ = ΣPathP (_ , ⋆IdLᴰ _)
  ∫C .⋆IdR _ = ΣPathP (_ , ⋆IdRᴰ _)
  ∫C .⋆Assoc _ _ _ = ΣPathP (_ , ⋆Assocᴰ _ _ _)
  ∫C .isSetHom = isSetΣ C.isSetHom (λ _ → isSetHomᴰ)

-- Displayed total category, i.e. Σ for displayed categories
module _ {C : Category ℓC ℓC'}
  (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  (Dᴰ : Categoryᴰ (∫C Cᴰ) ℓDᴰ ℓDᴰ')
  where

  open Categoryᴰ
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module Dᴰ = Categoryᴰ Dᴰ

  ∫Cᴰ : Categoryᴰ C (ℓ-max ℓCᴰ ℓDᴰ) (ℓ-max ℓCᴰ' ℓDᴰ')
  ∫Cᴰ .ob[_] x = Σ[ xᴰ ∈ Cᴰ.ob[ x ] ] Dᴰ.ob[ x , xᴰ ]
  ∫Cᴰ .Hom[_][_,_] f (_ , zᴰ) (_ , wᴰ) = Σ[ fᴰ ∈ Cᴰ.Hom[ f ][ _ , _ ] ] Dᴰ.Hom[ f , fᴰ ][ zᴰ , wᴰ ]
  ∫Cᴰ .idᴰ = Cᴰ.idᴰ , Dᴰ.idᴰ
  ∫Cᴰ ._⋆ᴰ_ (_ , hᴰ) (_ , kᴰ) = _ , hᴰ Dᴰ.⋆ᴰ kᴰ
  ∫Cᴰ .⋆IdLᴰ _ = ΣPathP (_ , Dᴰ.⋆IdLᴰ _)
  ∫Cᴰ .⋆IdRᴰ _ = ΣPathP (_ , Dᴰ.⋆IdRᴰ _)
  ∫Cᴰ .⋆Assocᴰ _ _ _ = ΣPathP (_ , Dᴰ.⋆Assocᴰ _ _ _)
  ∫Cᴰ .isSetHomᴰ = isSetΣ Cᴰ.isSetHomᴰ (λ _ → Dᴰ.isSetHomᴰ)

module _ {C : Category ℓC ℓC'}
  (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  (Dᴰ : Categoryᴰ C ℓDᴰ ℓDᴰ')
  where

  open Categoryᴰ
  private
    module Dᴰ = Categoryᴰ Dᴰ

  weakenᴰ : Categoryᴰ (∫C Cᴰ) ℓDᴰ ℓDᴰ'
  weakenᴰ .ob[_] (x , _) = Dᴰ.ob[ x ]
  weakenᴰ .Hom[_][_,_] (f , _) = Dᴰ.Hom[ f ][_,_]
  weakenᴰ .idᴰ = Dᴰ.idᴰ
  weakenᴰ ._⋆ᴰ_ = Dᴰ._⋆ᴰ_
  weakenᴰ .⋆IdLᴰ = Dᴰ.⋆IdLᴰ
  weakenᴰ .⋆IdRᴰ = Dᴰ.⋆IdRᴰ
  weakenᴰ .⋆Assocᴰ = Dᴰ.⋆Assocᴰ
  weakenᴰ .isSetHomᴰ = Dᴰ.isSetHomᴰ

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
