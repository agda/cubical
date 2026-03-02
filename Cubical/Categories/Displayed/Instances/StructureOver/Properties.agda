-- | Structure displayed over a category.
module Cubical.Categories.Displayed.Instances.StructureOver.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Instances.StructureOver.Base
open import Cubical.Categories.Instances.TotalCategory

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

module _ {C : Category ℓC ℓC'} (Pᴰ : StructureOver C ℓCᴰ ℓCᴰ') where
  open Functor
  open StructureOver

  isFaithfulFst : isFaithful (Fst {Cᴰ = StructureOver→Catᴰ Pᴰ})
  isFaithfulFst x y f g p =
    ΣPathP (p ,
      isProp→PathP (λ i → Pᴰ .isPropHomᴰ {f = p i}) (f .snd) (g .snd))
