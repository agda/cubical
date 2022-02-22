{-# OPTIONS --safe #-}
module Cubical.Algebra.Group.Instances.SetsAutomorphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Properties


module _ {ℓ} (A : Type ℓ) (isSet-A : isSet A) where

  open GroupStr


  SetAut≡ = SetsIso≡  isSet-A isSet-A
  SetAut≡-ext = SetsIso≡-ext  isSet-A isSet-A


  SetAut : Group ℓ
  fst SetAut = Iso A A
  1g (snd SetAut) = idIso
  _·_ (snd SetAut) = compIso
  inv (snd SetAut) = invIso
  isGroup (snd SetAut) = isGroupSetAut 
     where
     abstract
       isGroupSetAut : IsGroup {G = Iso A A} idIso compIso invIso
       isGroupSetAut =
          makeIsGroup
            (isSet-SetsIso isSet-A isSet-A)
            (λ _ _ _ → SetAut≡ refl refl)
            (λ _ → SetAut≡ refl refl)
            (λ _ → SetAut≡ refl refl)
            (λ x → SetAut≡-ext (Iso.leftInv x) (Iso.leftInv x))
            λ x → SetAut≡-ext (Iso.rightInv x) (Iso.rightInv x)


-- action of group on its carrier
G→SetAut⟨G⟩ : ∀ {ℓ} (G : Group ℓ) → GroupHom G (SetAut _ (isSetGroup G) )
G→SetAut⟨G⟩ G'@(G , G-struct) = f , f-isHom
  where
    open GroupStr G-struct

    open GroupTheory G'

    isSet-G = (isSetGroup G')

    GAut≡ = SetAut≡ _ isSet-G
    GAut≡-ext = SetAut≡-ext _ isSet-G


    f : G → Iso G G
    Iso.fun (f x) = _· x  
    Iso.inv (f x) =  _· (inv x)
    Iso.rightInv (f x) b = sym (assoc _ _ _) ∙ cong (b ·_) (invl _) ∙ rid _
    Iso.leftInv (f x) b = sym (assoc _ _ _) ∙ cong (b ·_) (invr _) ∙ rid _

    f-isHom : IsGroupHom G-struct f _
    IsGroupHom.pres· f-isHom x y =
      GAut≡ (funExt λ _ → assoc _ _ _)
            (funExt λ _ →  cong (_ ·_) (invDistr _ _) ∙ assoc _ _ _) 
    IsGroupHom.pres1 f-isHom =
      GAut≡ (funExt rid)
            (funExt λ _ → cong (_ ·_) inv1g ∙ rid _)
    IsGroupHom.presinv f-isHom x =
      GAut≡ refl (funExt λ _ → cong (_ ·_) (invInv _))
    
