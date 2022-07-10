-- (Pre)additive categories
{-# OPTIONS --safe #-}

module Cubical.Categories.Additive.Base where

open import Cubical.Algebra.AbGroup.Base
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Limits.Initial
open import Cubical.Categories.Limits.Terminal
open import Cubical.Foundations.Prelude

private
  variable
    ℓ ℓ' : Level


-- Preadditive categories
module _ (C : Category ℓ ℓ') where
  open Category C

  record PreaddCategoryStr : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
    field
      homAbStr : (x y : ob) → AbGroupStr Hom[ x , y ]

    -- Polymorphic abelian group operations
    0h = λ {x} {y} → AbGroupStr.0g (homAbStr x y)
    -_ = λ {x} {y} → AbGroupStr.-_ (homAbStr x y)
    _+_ = λ {x} {y} → AbGroupStr._+_ (homAbStr x y)

    _-_ : ∀ {x y} (f g : Hom[ x , y ]) → Hom[ x , y ]
    f - g = f + (- g)

    infixr 7   _+_
    infixl 7.5 _-_
    infix  8    -_

    field
      ⋆distl+ : {x y z : ob} → (f : Hom[ x , y ]) → (g g' : Hom[ y , z ]) →
          f ⋆ (g + g') ≡ (f ⋆ g) + (f ⋆ g')

      ⋆distr+ : {x y z : ob} → (f f' : Hom[ x , y ]) → (g : Hom[ y , z ]) →
          (f + f') ⋆ g ≡ (f ⋆ g) + (f' ⋆ g)


record PreaddCategory (ℓ ℓ' : Level) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    cat : Category ℓ ℓ'
    preadd : PreaddCategoryStr cat

  open Category cat public
  open PreaddCategoryStr preadd public



-- Additive categories
module _ (C : PreaddCategory ℓ ℓ') where
  open PreaddCategory C

  -- Zero object
  record ZeroObject : Type (ℓ-max ℓ ℓ') where
    field
      z : ob
      zInit : isInitial cat z
      zTerm : isTerminal cat z


  -- Biproducts
  record IsBiproduct {x y x⊕y : ob}
      (i₁ : Hom[ x , x⊕y ]) (i₂ : Hom[ y , x⊕y ])
      (π₁ : Hom[ x⊕y , x ]) (π₂ : Hom[ x⊕y , y ])
          : Type (ℓ-max ℓ ℓ') where

    field
      i₁⋆π₁ : i₁ ⋆ π₁ ≡ id
      i₁⋆π₂ : i₁ ⋆ π₂ ≡ 0h
      i₂⋆π₁ : i₂ ⋆ π₁ ≡ 0h
      i₂⋆π₂ : i₂ ⋆ π₂ ≡ id
      ∑π⋆i : π₁ ⋆ i₁ + π₂ ⋆ i₂ ≡ id


  record Biproduct (x y : ob) : Type (ℓ-max ℓ ℓ') where
    field
      x⊕y : ob
      i₁ : Hom[ x , x⊕y ]
      i₂ : Hom[ y , x⊕y ]
      π₁ : Hom[ x⊕y , x ]
      π₂ : Hom[ x⊕y , y ]
      isBipr : IsBiproduct i₁ i₂ π₁ π₂

    open IsBiproduct isBipr public


  -- Additive categories
  record AdditiveCategoryStr : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
    field
      zero : ZeroObject
      biprod : ∀ x y → Biproduct x y

    -- Biproduct notation
    open Biproduct
    _⊕_ = λ (x y : ob) → biprod x y .x⊕y
    infixr 6 _⊕_


record AdditiveCategory (ℓ ℓ' : Level) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    preaddcat : PreaddCategory ℓ ℓ'
    addit : AdditiveCategoryStr preaddcat

  open PreaddCategory preaddcat public
  open AdditiveCategoryStr addit public
