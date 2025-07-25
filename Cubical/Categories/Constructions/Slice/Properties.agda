
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.Slice.Base
import Cubical.Categories.Constructions.Elements as Elements
open import Cubical.Categories.Equivalence
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.NaturalTransformation

open Category

module Cubical.Categories.Constructions.Slice.Properties
  {ℓC ℓ'C : Level}
  (C : Category ℓC ℓ'C)
  (c : C .ob)
  where

open Elements.Contravariant {C = C}

open _≃ᶜ_
open Functor
open WeakInverse

slice→el : Functor (SliceCat C c) (∫ᴾ (C [-, c ]))
slice→el .F-ob s = s .S-ob , s .S-arr
slice→el .F-hom f = f .S-hom , f .S-comm
slice→el .F-id = ΣPathP (refl , (isOfHLevelPath' 1 (C .isSetHom) _ _ _ _))
slice→el .F-seq _ _ = ΣPathP (refl , (isOfHLevelPath' 1 (C .isSetHom) _ _ _ _))

el→slice : Functor (∫ᴾ (C [-, c ])) (SliceCat C c)
el→slice .F-ob (_ , s) = sliceob s
el→slice .F-hom (f , comm) = slicehom f comm
el→slice .F-id = SliceHom-≡-intro C c refl (isOfHLevelPath' 1 (C .isSetHom) _ _ _ _)
el→slice .F-seq _ _ = SliceHom-≡-intro C c refl (isOfHLevelPath' 1 (C .isSetHom) _ _ _ _)

open NatTrans
open NatIso

sliceIsElementsOfRep : SliceCat C c ≃ᶜ (∫ᴾ (C [-, c ]))
sliceIsElementsOfRep .func = slice→el
sliceIsElementsOfRep .isEquiv  = ∣ w-inv ∣₁
  where
    w-inv : WeakInverse slice→el
    w-inv .invFunc = el→slice
    w-inv .η .trans .N-ob s = SliceCat C c .id
    w-inv .η .trans .N-hom f = (SliceCat C c .⋆IdR f)
                             ∙ sym (SliceCat C c .⋆IdL f)
    w-inv .η .nIso x = isiso (SliceCat C c .id)
                             (SliceCat C c .⋆IdR _)
                             (SliceCat C c .⋆IdR _)
    w-inv .ε .trans .N-ob s = (∫ᴾ (C [-, c ])) .id
    w-inv .ε .trans .N-hom f = ((∫ᴾ (C [-, c ])) .⋆IdR f)
                             ∙ sym ((∫ᴾ (C [-, c ])) .⋆IdL f)
    w-inv .ε .nIso x = isiso ((∫ᴾ (C [-, c ])) .id)
                             ((∫ᴾ (C [-, c ])) .⋆IdR _)
                             ((∫ᴾ (C [-, c ])) .⋆IdR _)
