-- Quotients of additive categories
{-# OPTIONS --safe #-}

module Cubical.Categories.Additive.Quotient where

open import Cubical.Algebra.AbGroup.Base renaming (_/_ to _/G_)
open import Cubical.Categories.Additive.Base
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.Quotient
open import Cubical.Categories.Limits.Terminal
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.HITs.SetQuotients renaming (_/_ to _/s_; [_] to ⟦_⟧)

private
  variable
    ℓ ℓ' ℓq : Level

-- Quotients of preadditive categories
module _ (C : PreaddCategory ℓ ℓ') where
  open PreaddCategory C

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
      Hom[_,_]/~ = λ (x y : ob) → (Hom[ x , y ]) /s _~_
      _⋆/~_ = C/~ .Category._⋆_

      _+/~_ : {x y : ob} (f g : Hom[ x , y ]/~) → Hom[ x , y ]/~
      _+/~_ = setQuotBinOp ~refl _+_ ~cong+

    -- Quotient group structure on homsets
    private
      habstr/~ : HomAbStr C/~ --(x y : ob) → AbGroupStr Hom[ x , y ]/~
      habstr/~ = homabstr
        λ x y → abgroupstr
          ⟦ 0h ⟧
          _+/~_
          (setQuotUnaryOp -_ ~cong-)
          (makeIsAbGroup
            squash/
            (elimProp3 (λ _ _ _ → squash/ _ _)
              λ _ _ _ → cong ⟦_⟧ (+assoc _ _ _))
            (elimProp (λ _ → squash/ _ _)
              λ _ → cong ⟦_⟧ (idr _))
            (elimProp (λ _ → squash/ _ _)
              λ _ → cong ⟦_⟧ (invr _))
            (elimProp2 (λ _ _ → squash/ _ _)
              λ _ _ → cong ⟦_⟧ (+comm _ _))
          )

    -- Distributivity
    distl/~ : {x y z : ob} → (f : Hom[ x , y ]/~) → (g g' : Hom[ y , z ]/~) →
        f  ⋆/~  (g  +/~  g')  ≡  (f  ⋆/~  g)  +/~  (f  ⋆/~  g')
    distl/~ = elimProp (λ _ → isPropΠ2 (λ _ _ → squash/ _ _))
              λ _ → elimProp2 (λ _ _ → squash/ _ _)
                  (λ _ _ → cong ⟦_⟧ (distl _ _ _))

    distr/~ : {x y z : ob} → (f f' : Hom[ x , y ]/~) → (g : Hom[ y , z ]/~) →
        (f  +/~  f')  ⋆/~  g  ≡  (f  ⋆/~  g)  +/~  (f'  ⋆/~  g)
    distr/~ = elimProp2 (λ _ _ → isPropΠ (λ _ → squash/ _ _))
              λ _ _ → elimProp (λ _ → squash/ _ _)
                  (λ _ → cong ⟦_⟧ (distr _ _ _))


    -- Quotient of preadditive category
    PreaddQuotient : PreaddCategory ℓ (ℓ-max ℓ' ℓq)
    PreaddQuotient = record {
        cat = C/~;
        preadd = record {
          habstr = habstr/~;
          distl = distl/~;
          distr = distr/~
        }
      }


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
      preaddquo = PreaddQuotient (AddCat→PreaddCat A)
          _~_ ~refl ~cong⋆ ~cong+ ~cong-
      A/~ = preaddquo .PreaddCategory.cat
      habstr/~ = preaddquo .PreaddCategory.habstr
    
    -- Zero object
    open ZeroObject zero
    z/~ = z

    z/~Init : isInitial A/~ z/~
    z/~Init = isInitial/~ cat _~_ ~refl ~cong⋆ zInit

    z/~Final : isFinal A/~ z/~
    z/~Final = isFinal/~ cat _~_ ~refl ~cong⋆ zFinal

    -- Biproducts
    module _ (x y : ob) where
      open Biproduct (biprod x y)

      isBiprod/~ : isBiproduct A/~ habstr/~ ⟦ i₁ ⟧ ⟦ i₂ ⟧ ⟦ π₁ ⟧ ⟦ π₂ ⟧
      isBiprod/~ = record {
          i₁⋆π₁ = cong ⟦_⟧ i₁⋆π₁;
          i₁⋆π₂ = cong ⟦_⟧ i₁⋆π₂;
          i₂⋆π₁ = cong ⟦_⟧ i₂⋆π₁;
          i₂⋆π₂ = cong ⟦_⟧ i₂⋆π₂;
          ∑π⋆i  = cong ⟦_⟧ ∑π⋆i
        }
      
      biprod/~ : Biproduct A/~ habstr/~ x y
      biprod/~ = record {
          x⊕y = x⊕y;
          i₁ = ⟦ i₁ ⟧;
          i₂ = ⟦ i₂ ⟧;
          π₁ = ⟦ π₁ ⟧;
          π₂ = ⟦ π₂ ⟧;
          isBipr = isBiprod/~
        }

    open PreaddCategory
    AdditiveQuotient : AdditiveCategory ℓ (ℓ-max ℓ' ℓq)
    AdditiveQuotient = record {
        cat = A/~;
        addit = record {
          preadd = preadd (PreaddQuotient
              (AddCat→PreaddCat A) _~_
              ~refl ~cong⋆ ~cong+ ~cong-);
          zero = record {
            z = z/~;
            zInit = z/~Init;
            zFinal = z/~Final
          } ;
          biprod = biprod/~
        }
      }
