module Cubical.Categories.Displayed.Instances.Element where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Instances.BinProduct as BP
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.TotalCategory.Base as TotalCat

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.StructureOver.Base
open import Cubical.Categories.Displayed.HLevels

private
  variable
    ℓ ℓC ℓC' ℓD ℓD' ℓP ℓQ ℓS : Level

open Category
open StructureOver
open Functor
open Functorᴰ
open Iso

module _ {C : Category ℓC ℓC'} (P : Presheaf C ℓP) where
  open StructureOver
  private
    module P = PresheafNotation P
  ElementStr : StructureOver C _ _
  ElementStr .ob[_] = P.p[_]
  ElementStr .Hom[_][_,_] f p q = (f P.⋆ q) ≡ p
  ElementStr .idᴰ = P.⋆IdL _
  ElementStr ._⋆ᴰ_ fy≡x gz≡y = P.⋆Assoc _ _ _ ∙∙ cong (_ P.⋆_) gz≡y ∙∙ fy≡x
  ElementStr .isPropHomᴰ = P.isSetPsh _ _

  Element : Categoryᴰ C ℓP ℓP
  Element = StructureOver→Catᴰ ElementStr

  hasPropHomsElement : hasPropHoms Element
  hasPropHomsElement = hasPropHomsStructureOver ElementStr

  open Categoryᴰ
  isUnivalentᴰElement : isUnivalentᴰ Element
  isUnivalentᴰElement x y px py x≡y = propBiimpl→isEquiv
    (isOfHLevelPathP' 1 P.isSetPsh _ _)
    (hasPropHoms→isPropCatIsoᴰ Element hasPropHomsElement)
    (isoᴰ→PathP x≡y py)
    where
    isoᴰ→PathP-motive : ∀ y → (x ≡ y) → Type _
    isoᴰ→PathP-motive y x≡y = ∀ (py : P.p[ y ])
      → CatIsoᴰ Element (pathToIso x≡y) px py → PathP (λ i → ob[ Element ] (x≡y i)) px py

    isoᴰ→PathP : ∀ {y} (x≡y : x ≡ y) → isoᴰ→PathP-motive y x≡y
    isoᴰ→PathP = J isoᴰ→PathP-motive λ px' px≅px' →
      px
        ≡⟨ (sym $ P.⋆IdL _) ⟩
      C .id P.⋆ px
        ≡⟨ P.⟨ sym $ transportRefl (C .id) ⟩⋆⟨⟩ ⟩
      transport (λ i → C [ x , x ]) (C .id) P.⋆ px
        ≡⟨ px≅px' .snd .isIsoᴰ.invᴰ ⟩
      px' ∎

module _ {C : Category ℓC ℓC'} {P Q : Presheaf C ℓP} where
  open StructureOver
  open NatTrans
  private
    module P = PresheafNotation P
    module Q = PresheafNotation Q

  ElementF : NatTrans P Q → Functorⱽ (Element P) (Element Q)
  ElementF α = mkPropHomsFunctor (hasPropHomsElement Q)
    (α .N-ob _)
    λ {f = f}{p}{p'} fp'≡p →
      f Q.⋆ (α .N-ob _ p')
        ≡[ i ]⟨ α .N-hom f (~ i) p' ⟩
      α .N-ob _ (f P.⋆ p')
        ≡[ i ]⟨ α .N-ob _ (fp'≡p i) ⟩
      α .N-ob _ p ∎
