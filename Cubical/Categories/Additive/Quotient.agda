-- Quotients of additive categories

module Cubical.Categories.Additive.Quotient where

open import Cubical.Algebra.AbGroup.Base
open import Cubical.Categories.Additive.Base
open import Cubical.Categories.Additive.Properties
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Instances.Quotient
open import Cubical.Categories.Limits.Terminal
open import Cubical.Foundations.Prelude
open import Cubical.HITs.SetQuotients renaming ([_] to ⟦_⟧)

private
  variable
    ℓ ℓ' ℓq : Level

-- Quotients of preadditive categories
module _ (C : PreaddCategory ℓ ℓ') where
  open PreaddCategory C
  open PreaddCategoryTheory C

  module _ (_~_ : {x y : ob} (f g : Hom[ x , y ] ) → Type ℓq)
           (~refl : {x y : ob} (f : Hom[ x , y ] ) → f ~ f)
           (~cong⋆ : {x y z : ob}
                     (f f' : Hom[ x , y ]) → f ~ f'
                   → (g g' : Hom[ y , z ]) → g ~ g'
                   → (f ⋆ g) ~ (f' ⋆ g'))
           (~cong+ : {x y : ob} (f f' g g' : Hom[ x , y ])
                   → f ~ f' → g ~ g' → (f + g) ~ (f' + g'))
           (~cong- : {x y : ob} (f f' : Hom[ x , y ])
                   → f ~ f' → (- f) ~ (- f'))           where

    private
      C/~ = QuotientCategory cat _~_ ~refl ~cong⋆
      Hom[_,_]/~ = λ (x y : ob) → (Hom[ x , y ]) / _~_
      _⋆/~_ = C/~ .Category._⋆_

      _+/~_ : {x y : ob} (f g : Hom[ x , y ]/~) → Hom[ x , y ]/~
      _+/~_ = setQuotBinOp ~refl ~refl _+_ ~cong+

    -- Quotient group structure on homsets
    private
      open AbGroupStr renaming (_+_ to add; -_ to inv)
      homAbStr/~ : (x y : ob) → AbGroupStr Hom[ x , y ]/~
      homAbStr/~ x y .0g        = ⟦ 0h ⟧
      homAbStr/~ x y .add       = _+/~_
      homAbStr/~ x y .inv       = (setQuotUnaryOp -_ ~cong-)
      homAbStr/~ x y .isAbGroup = makeIsAbGroup squash/
          (elimProp3 (λ _ _ _ → squash/ _ _)  λ _ _ _ → cong ⟦_⟧ (+assoc _ _ _))
          (elimProp  (λ _     → squash/ _ _)  λ _     → cong ⟦_⟧ (+idr _))
          (elimProp  (λ _     → squash/ _ _)  λ _     → cong ⟦_⟧ (+invr _))
          (elimProp2 (λ _ _   → squash/ _ _)  λ _ _   → cong ⟦_⟧ (+comm _ _))

    -- Distributivity
    ⋆distl+/~ : {x y z : ob} → (f : Hom[ x , y ]/~) → (g g' : Hom[ y , z ]/~) →
        f  ⋆/~  (g  +/~  g')  ≡  (f  ⋆/~  g)  +/~  (f  ⋆/~  g')
    ⋆distl+/~ = elimProp3 (λ _ _ _ → squash/ _ _) λ _ _ _ → cong ⟦_⟧ (⋆distl+ _ _ _)

    ⋆distr+/~ : {x y z : ob} → (f f' : Hom[ x , y ]/~) → (g : Hom[ y , z ]/~) →
        (f  +/~  f')  ⋆/~  g  ≡  (f  ⋆/~  g)  +/~  (f'  ⋆/~  g)
    ⋆distr+/~ = elimProp3 (λ _ _ _ → squash/ _ _) λ _ _ _ → cong ⟦_⟧ (⋆distr+ _ _ _)


    -- Quotient of preadditive category
    open PreaddCategory
    open PreaddCategoryStr
    PreaddQuotient : PreaddCategory ℓ (ℓ-max ℓ' ℓq)
    PreaddQuotient .cat = QuotientCategory (cat C) _~_ ~refl ~cong⋆
    PreaddQuotient .preadd .homAbStr = homAbStr/~
    PreaddQuotient .preadd .⋆distl+ = ⋆distl+/~
    PreaddQuotient .preadd .⋆distr+ = ⋆distr+/~


-- Quotients of additive categories
module _ (A : AdditiveCategory ℓ ℓ') where
  open AdditiveCategory A

  module _ (_~_ : {x y : ob} (f g : Hom[ x , y ] ) → Type ℓq)
           (~refl : {x y : ob} (f : Hom[ x , y ] ) → f ~ f)
           (~cong⋆ : {x y z : ob}
                     (f f' : Hom[ x , y ]) → f ~ f'
                   → (g g' : Hom[ y , z ]) → g ~ g'
                   → (f ⋆ g) ~ (f' ⋆ g'))
           (~cong+ : {x y : ob} (f f' g g' : Hom[ x , y ])
                   → f ~ f' → g ~ g' → (f + g) ~ (f' + g'))
           (~cong- : {x y : ob} (f f' : Hom[ x , y ])
                   → f ~ f' → (- f) ~ (- f'))           where

    private
      A/~ = PreaddQuotient preaddcat _~_ ~refl ~cong⋆ ~cong+ ~cong-

    -- Zero object
    open ZeroObject
    zero/~ : ZeroObject A/~
    zero/~ .z = zero .z
    zero/~ .zInit = isInitial/~ cat _~_ ~refl ~cong⋆ (zInit zero)
    zero/~ .zTerm = isTerminal/~ cat _~_ ~refl ~cong⋆ (zTerm zero)

    -- Biproducts
    module _ (x y : ob) where
      open Biproduct
      open IsBiproduct

      biprod/~ : Biproduct A/~ x y
      biprod/~ .x⊕y = x ⊕ y
      biprod/~ .i₁ = ⟦ i₁ (biprod x y) ⟧
      biprod/~ .i₂ = ⟦ i₂ (biprod x y) ⟧
      biprod/~ .π₁ = ⟦ π₁ (biprod x y) ⟧
      biprod/~ .π₂ = ⟦ π₂ (biprod x y) ⟧
      biprod/~ .isBipr .i₁⋆π₁ = cong ⟦_⟧ (i₁⋆π₁ (biprod x y))
      biprod/~ .isBipr .i₁⋆π₂ = cong ⟦_⟧ (i₁⋆π₂ (biprod x y))
      biprod/~ .isBipr .i₂⋆π₁ = cong ⟦_⟧ (i₂⋆π₁ (biprod x y))
      biprod/~ .isBipr .i₂⋆π₂ = cong ⟦_⟧ (i₂⋆π₂ (biprod x y))
      biprod/~ .isBipr .∑π⋆i  = cong ⟦_⟧ (∑π⋆i  (biprod x y))


    open AdditiveCategoryStr
    AdditiveQuotient : AdditiveCategory ℓ (ℓ-max ℓ' ℓq)
    AdditiveQuotient .preaddcat = A/~
    AdditiveQuotient .addit .zero = zero/~
    AdditiveQuotient .addit .biprod = biprod/~
