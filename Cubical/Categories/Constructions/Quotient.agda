-- Quotient category
{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.Quotient where

open import Cubical.Categories.Category.Base
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.HITs.SetQuotients renaming ([_] to ⟦_⟧)

private
  variable
    ℓ ℓ' ℓq : Level

module _ (C : Category ℓ ℓ') where
  open Category C

  module _  (_~_ : {x y : ob} (f g : Hom[ x , y ] ) → Type ℓq)
            (~refl : {x y : ob} (f : Hom[ x , y ] ) → f ~ f)
            (~cong : {x y z : ob}
                    (f f' : Hom[ x , y ]) → f ~ f'
                  → (g g' : Hom[ y , z ]) → g ~ g'
                  → (f ⋆ g) ~ (f' ⋆ g')) where

    private
      Hom[_,_]/~ = λ (x y : ob) → Hom[ x , y ] / _~_

    module _ {x y z : ob} where
      pre⋆/~ : Hom[ x , y ] → Hom[ y , z ]/~ → Hom[ x , z ]/~
      pre⋆/~ f = rec squash/ (λ g → ⟦ f ⋆ g ⟧)
                     λ g g' g~g' → eq/ _ _ (~cong _ _ (~refl _) _ _ g~g')

      _⋆/~_ : Hom[ x , y ]/~ → Hom[ y , z ]/~ → Hom[ x , z ]/~
      _⋆/~_ = rec (isSetΠ λ _ → squash/)
                  (λ f → pre⋆/~ f)
                  λ f f' f~f' → funExt (elimProp
                                       (λ ⟦g⟧ → squash/ (pre⋆/~ f ⟦g⟧) (pre⋆/~ f' ⟦g⟧))
                                       λ g → eq/ _ _ (~cong _ _ f~f' _ _ (~refl _)))

      ⋆/~WellDef : (f : Hom[ x , y ]) → (g : Hom[ y , z ])
         → ⟦ f ⟧ ⋆/~ ⟦ g ⟧ ≡ ⟦ f ⋆ g ⟧
      ⋆/~WellDef f g i = ⟦ refl {x = f ⋆ g} i ⟧

    module _ {x y : ob} where
      ⋆/~IdL : (f : Hom[ x , y ]/~) → (⟦ id ⟧ ⋆/~ f) ≡ f
      ⋆/~IdL = elimProp (λ ⟦f⟧ → squash/ (⟦ id ⟧ ⋆/~ ⟦f⟧) ⟦f⟧) λ f →
          ⟦ id ⟧ ⋆/~ ⟦ f ⟧      ≡⟨ ⋆/~WellDef _ _ ⟩
          ⟦ id ⋆ f ⟧            ≡⟨ cong ⟦_⟧ (⋆IdL _) ⟩
          ⟦ f ⟧                 ∎

      ⋆/~IdR : (f : Hom[ x , y ]/~) → (f ⋆/~ ⟦ id ⟧) ≡ f
      ⋆/~IdR = elimProp (λ ⟦f⟧ → squash/ (⟦f⟧ ⋆/~ ⟦ id ⟧) ⟦f⟧) λ f →
          ⟦ f ⟧ ⋆/~ ⟦ id ⟧      ≡⟨ ⋆/~WellDef _ _ ⟩
          ⟦ f ⋆ id ⟧            ≡⟨ cong ⟦_⟧ (⋆IdR _) ⟩
          ⟦ f ⟧                 ∎

    module _ {x y z w : ob} where
      ⋆/~Assoc : (f : Hom[ x , y ]/~)
                 (g : Hom[ y , z ]/~)
                 (h : Hom[ z , w ]/~)
        → ((f ⋆/~ g) ⋆/~ h) ≡ (f ⋆/~ (g ⋆/~ h))

      ⋆/~Assoc = elimProp (λ ⟦f⟧ → isPropΠ2 (λ ⟦g⟧ ⟦h⟧ → squash/ _ _))
                 λ f → elimProp (λ ⟦g⟧ → isPropΠ (λ ⟦h⟧ → squash/ _ _))
                 λ g → elimProp (λ ⟦h⟧ → squash/ ((⟦ f ⟧ ⋆/~ ⟦ g ⟧) ⋆/~ ⟦h⟧)
                          (⟦ f ⟧ ⋆/~ (⟦ g ⟧ ⋆/~ ⟦h⟧))) λ h →

          (⟦ f ⟧ ⋆/~ ⟦ g ⟧) ⋆/~ ⟦ h ⟧       ≡⟨ cong (λ k → ⟦ k ⟧ ⋆/~ ⟦ h ⟧) refl ⟩
          ⟦ f ⋆ g ⟧ ⋆/~ ⟦ h ⟧               ≡⟨ ⋆/~WellDef _ _ ⟩
          ⟦ (f ⋆ g) ⋆ h ⟧                   ≡⟨ cong ⟦_⟧ (⋆Assoc _ _ _) ⟩
          ⟦ f ⋆ (g ⋆ h) ⟧                   ≡⟨ sym (⋆/~WellDef _ _) ⟩
          ⟦ f ⟧ ⋆/~ ⟦ g ⋆ h ⟧               ≡⟨ cong (λ k → ⟦ f ⟧ ⋆/~ ⟦ k ⟧) refl ⟩
          ⟦ f ⟧ ⋆/~ (⟦ g ⟧ ⋆/~ ⟦ h ⟧)       ∎


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
