-- Quotient category
{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.Quotient where

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Initial
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.HITs.SetQuotients renaming ([_] to ⟦_⟧)

private
  variable
    ℓ ℓ' ℓq : Level

module _ (C : Category ℓ ℓ') where
  open Category C

  module _ (_~_ : {x y : ob} (f g : Hom[ x , y ] ) → Type ℓq)
           (~refl : {x y : ob} (f : Hom[ x , y ] ) → f ~ f)
           (~cong : {x y z : ob}
                    (f f' : Hom[ x , y ]) → f ~ f'
                  → (g g' : Hom[ y , z ]) → g ~ g'
                  → (f ⋆ g) ~ (f' ⋆ g')) where

    private
      Hom[_,_]/~ = λ (x y : ob) → Hom[ x , y ] / _~_

      module _ {x y z : ob} where
        _⋆/~_ : Hom[ x , y ]/~ → Hom[ y , z ]/~ → Hom[ x , z ]/~
        _⋆/~_ = rec2 squash/ (λ f g → ⟦ f ⋆ g ⟧)
                    (λ f f' g f~f' → eq/ _ _ (~cong _ _ f~f' _ _ (~refl _)))
                    (λ f g g' g~g' → eq/ _ _ (~cong _ _ (~refl _) _ _ g~g'))

    module _ {x y : ob} where
      ⋆/~IdL : (f : Hom[ x , y ]/~) → (⟦ id ⟧ ⋆/~ f) ≡ f
      ⋆/~IdL = elimProp (λ _ → squash/ _ _) (λ _ → cong ⟦_⟧ (⋆IdL _))

      ⋆/~IdR : (f : Hom[ x , y ]/~) → (f ⋆/~ ⟦ id ⟧) ≡ f
      ⋆/~IdR = elimProp (λ _ → squash/ _ _) (λ _ → cong ⟦_⟧ (⋆IdR _))

    module _ {x y z w : ob} where
      ⋆/~Assoc : (f : Hom[ x , y ]/~)
                (g : Hom[ y , z ]/~)
                (h : Hom[ z , w ]/~)
        → ((f ⋆/~ g) ⋆/~ h) ≡ (f ⋆/~ (g ⋆/~ h))

      ⋆/~Assoc = elimProp3 (λ _ _ _ → squash/ _ _) (λ _ _ _ → cong ⟦_⟧ (⋆Assoc _ _ _))


    open Category
    QuotientCategory : Category ℓ (ℓ-max ℓ' ℓq)
    QuotientCategory .ob = ob C
    QuotientCategory .Hom[_,_] x y = (C [ x , y ]) / _~_
    QuotientCategory .id = ⟦ id C ⟧
    QuotientCategory ._⋆_ = _⋆/~_
    QuotientCategory .⋆IdL = ⋆/~IdL
    QuotientCategory .⋆IdR = ⋆/~IdR
    QuotientCategory .⋆Assoc = ⋆/~Assoc
    QuotientCategory .isSetHom = squash/


    private
      C/~ = QuotientCategory

    -- Quotient map
    open Functor
    QuoFunctor : Functor C C/~
    QuoFunctor .F-ob x = x
    QuoFunctor .F-hom = ⟦_⟧
    QuoFunctor .F-id = refl
    QuoFunctor .F-seq f g = refl

    -- Quotients preserve initial / terminal objects
    isInitial/~ : {z : ob C} → isInitial C z → isInitial C/~ z
    isInitial/~ zInit x = ⟦ zInit x .fst ⟧ , elimProp (λ _ → squash/ _ _)
        λ f → eq/ _ _ (subst (_~ f) (sym (zInit x .snd f)) (~refl _))

    isTerminal/~ : {z : ob C} → isTerminal C z → isTerminal C/~ z
    isTerminal/~ zTerminal x = ⟦ zTerminal x .fst ⟧ , elimProp (λ _ → squash/ _ _)
        λ f → eq/ _ _ (subst (_~ f) (sym (zTerminal x .snd f)) (~refl _))
