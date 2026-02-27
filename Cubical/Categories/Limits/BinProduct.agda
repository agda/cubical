-- Binary products

module Cubical.Categories.Limits.BinProduct where

open import Cubical.Categories.Category.Base
open import Cubical.Data.Sigma.Base
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation.Base

private
  variable
    ℓ ℓ' : Level

module _ (C : Category ℓ ℓ') where
  open Category C

  module _ {x y x×y : ob}
           (π₁ : Hom[ x×y , x ])
           (π₂ : Hom[ x×y , y ]) where

    isBinProduct : Type (ℓ-max ℓ ℓ')
    isBinProduct = ∀ {z : ob} (f₁ : Hom[ z , x ]) (f₂ : Hom[ z , y ]) →
        ∃![ f ∈ Hom[ z , x×y ] ] (f ⋆ π₁ ≡ f₁) × (f ⋆ π₂ ≡ f₂)

    isPropIsBinProduct : isProp (isBinProduct)
    isPropIsBinProduct = isPropImplicitΠ (λ _ → isPropΠ2 (λ _ _ → isPropIsContr))


  record BinProduct (x y : ob) : Type (ℓ-max ℓ ℓ') where
    field
      binProdOb : ob
      binProdPr₁ : Hom[ binProdOb , x ]
      binProdPr₂ : Hom[ binProdOb , y ]
      univProp : isBinProduct binProdPr₁ binProdPr₂

    binProdArrow : {z : ob} -> Hom[ z , x ] -> Hom[ z , y ] -> Hom[ z , binProdOb ]
    binProdArrow f g = univProp f g .fst .fst

    binProdArrowUnique : {z : ob} {f : Hom[ z , x ]} {g : Hom[ z , y ]} {h : Hom[ z , binProdOb ]}
      -> h ⋆ binProdPr₁ ≡ f -> h ⋆ binProdPr₂ ≡ g -> binProdArrow f g ≡ h
    binProdArrowUnique {f = f} {g = g} {h = h} p q i = univProp f g .snd (h , p , q) i .fst

    -- Beta rules for products:

    binProdArrowPr₁ : {z : ob} {f : Hom[ z , x ]} {g : Hom[ z , y ]} -> binProdArrow f g ⋆ binProdPr₁ ≡ f
    binProdArrowPr₁ {f = f} {g = g} = univProp f g .fst .snd .fst

    binProdArrowPr₂ : {z : ob} {f : Hom[ z , x ]} {g : Hom[ z , y ]} -> binProdArrow f g ⋆ binProdPr₂ ≡ g
    binProdArrowPr₂ {f = f} {g = g} = univProp f g .fst .snd .snd


  BinProducts : Type (ℓ-max ℓ ℓ')
  BinProducts = (x y : ob) → BinProduct x y

  hasBinProducts : Type (ℓ-max ℓ ℓ')
  hasBinProducts = ∥ BinProducts ∥₁

  module BinProducts (prod : BinProducts) where
    open module AllProductsExpl (x y : ob) = BinProduct (prod x y) public using (binProdOb; univProp)
    open module AllProductsImpl {x y : ob} = BinProduct (prod x y) public hiding (binProdOb; univProp)

    private
      variable
        x y z w x' y' : ob
        f g h k : Hom[ x , y ]

    binProdMap : Hom[ x , x' ] -> Hom[ y , y' ] -> Hom[ binProdOb x y , binProdOb x' y' ]
    binProdMap f g = binProdArrow (binProdPr₁ ⋆ f) (binProdPr₂ ⋆ g)

    binProdArrowCompLeft : h ⋆ binProdArrow f g ≡ binProdArrow (h ⋆ f) (h ⋆ g)
    binProdArrowCompLeft = sym (binProdArrowUnique
      (⋆Assoc _ _ _ ∙ ⟨ refl ⟩⋆⟨ binProdArrowPr₁ ⟩)
      (⋆Assoc _ _ _ ∙ ⟨ refl ⟩⋆⟨ binProdArrowPr₂ ⟩))

    binProdArrowCompRight : (binProdArrow f g) ⋆ (binProdMap h k) ≡ binProdArrow (f ⋆ h) (g ⋆ k)
    binProdArrowCompRight = sym (binProdArrowUnique
      ( ⋆Assoc _ _ _
      ∙ cong (_ ⋆_) binProdArrowPr₁
      ∙ sym (⋆Assoc _ _ _)
      ∙ cong (_⋆ _) binProdArrowPr₁ )

      ( ⋆Assoc _ _ _
      ∙ cong (_ ⋆_) binProdArrowPr₂
      ∙ sym (⋆Assoc _ _ _)
      ∙ cong (_⋆ _) binProdArrowPr₂ ) )