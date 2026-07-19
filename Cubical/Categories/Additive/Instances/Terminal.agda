
module Cubical.Categories.Additive.Instances.Terminal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Categories.Category
open import Cubical.Categories.Additive.Base
open import Cubical.Categories.Instances.Terminal

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.Unit

open import Cubical.Data.Unit

private
  variable
    ℓ ℓ' : Level

open PreaddCategory
open PreaddCategoryStr
open AdditiveCategory
open AdditiveCategoryStr

private
  terminalAbGroupStr : AbGroupStr {ℓ = ℓ} Unit*
  terminalAbGroupStr = snd UnitAbGroup

  homProp : (x y : Category.ob {ℓ = ℓ} TerminalCategory) → isProp (TerminalCategory [ x , y ])
  homProp x y = isOfHLevelUnit* 2 x y

  homContr : (x y : Category.ob {ℓ = ℓ} TerminalCategory) → isContr (TerminalCategory [ x , y ])
  homContr x y = isProp→isContrPath (isOfHLevelUnit* 1) x y

  terminalPreAdd : PreaddCategory ℓ ℓ
  cat terminalPreAdd = TerminalCategory
  homAbStr (preadd terminalPreAdd) =
    λ x y →
      subst
        AbGroupStr
        (sym (isContr→≡Unit* (homContr x y)))
        terminalAbGroupStr
  ⋆distl+ (preadd terminalPreAdd) = λ _ _ _ _ → refl
  ⋆distr+ (preadd terminalPreAdd) = λ _ _ _ → refl

terminalAdditiveCategory : AdditiveCategory ℓ ℓ
preaddcat terminalAdditiveCategory = terminalPreAdd
ZeroObject.z (zero (addit terminalAdditiveCategory)) = tt*
ZeroObject.zInit (zero (addit terminalAdditiveCategory)) y = homContr _ _
ZeroObject.zTerm (zero (addit terminalAdditiveCategory)) y = homContr _ _
biprod (addit terminalAdditiveCategory) x y = trivProd
  where trivProd : Biproduct terminalPreAdd x y
        Biproduct.x⊕y trivProd = tt*
        Biproduct.i₁ trivProd = refl
        Biproduct.i₂ trivProd = refl
        Biproduct.π₁ trivProd = refl
        Biproduct.π₂ trivProd = refl
        IsBiproduct.i₁⋆π₁ (Biproduct.isBipr trivProd) = homProp _ _ _ _
        IsBiproduct.i₁⋆π₂ (Biproduct.isBipr trivProd) = homProp _ _ _ _
        IsBiproduct.i₂⋆π₁ (Biproduct.isBipr trivProd) = homProp _ _ _ _
        IsBiproduct.i₂⋆π₂ (Biproduct.isBipr trivProd) = homProp _ _ _ _
        IsBiproduct.∑π⋆i (Biproduct.isBipr trivProd) = homProp _ _ _ _
