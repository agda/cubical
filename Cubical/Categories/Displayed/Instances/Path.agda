{-
  Paths between objects as a category displayed over C × C.

  If C is univalent, this is equivalent to the IsoComma category.

  Universal property: a section of the Path bundle is a path between
  functors

-}
module Cubical.Categories.Displayed.Instances.Path where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.StructureOver

private
  variable
    ℓC ℓC' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓS ℓR : Level

open Section
open Functor

module _  (C : Category ℓC ℓC') where
  private
    module C = Category C
    open StructureOver
    PathC' : StructureOver (C ×C C) _ _
    PathC' .ob[_] (c , d) = c ≡ d
    PathC' .Hom[_][_,_] (f , g) c≡c' d≡d' =
      PathP (λ i → C.Hom[ c≡c' i , d≡d' i ]) f g
    PathC' .idᴰ = λ i → C.id
    PathC' ._⋆ᴰ_ f≡f' g≡g' = λ i → f≡f' i ⋆⟨ C ⟩ g≡g' i
    PathC' .isPropHomᴰ = isOfHLevelPathP' 1 C.isSetHom _ _

  PathC : Categoryᴰ (C ×C C) ℓC ℓC'
  PathC = StructureOver→Catᴰ PathC'

  hasPropHomsPathC : hasPropHoms PathC
  hasPropHomsPathC = hasPropHomsStructureOver PathC'

  -- The universal functor into PathC
  Refl : Section (Δ C) PathC
  Refl = mkPropHomsSection hasPropHomsPathC (λ _ → refl) λ _ → refl

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         {F1 F2 : Functor D C}
         where
  -- "Equality/Path Reflection Rule"
  PathReflection :
    ∀ (Fᴰ : Section (F1 ,F F2) (PathC C)) → F1 ≡ F2
  PathReflection Fᴰ = Functor≡ Fᴰ.F-obᴰ Fᴰ.F-homᴰ
    where module Fᴰ = Section Fᴰ

  -- Could also implement this using J and Refl, not sure which is
  -- preferable
  PathReflection⁻ :
    F1 ≡ F2 → Section (F1 ,F F2) (PathC C)
  PathReflection⁻ P = mkPropHomsSection (hasPropHomsPathC C)
    (λ x i → P i .F-ob x)
    λ f i → P i .F-hom f

-- TODO: there should also be a "J"-style elimination principle.
