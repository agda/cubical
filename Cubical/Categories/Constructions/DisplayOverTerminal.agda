{-
  A category displayed over the terminal category is isomorphic to
  just a category.
-}

module Cubical.Categories.Constructions.DisplayOverTerminal where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit
open import Cubical.Categories.Category
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Instances.Terminal


private
  variable
    ℓC ℓ'C ℓD ℓ'D ℓCᴰ ℓ'Cᴰ ℓDᴰ ℓ'Dᴰ : Level
module _ {ℓ* : Level} (Cᴰ : Categoryᴰ (TerminalCategory {ℓ*}) ℓCᴰ ℓ'Cᴰ) where
  open Categoryᴰ Cᴰ
  open Category

  DispOverTerminal→Category : Category ℓCᴰ ℓ'Cᴰ
  DispOverTerminal→Category .ob = ob[ tt* ]
  DispOverTerminal→Category .Hom[_,_] = Hom[ refl ][_,_]
  DispOverTerminal→Category .id = idᴰ
  DispOverTerminal→Category ._⋆_ = _⋆ᴰ_
  DispOverTerminal→Category .⋆IdL = ⋆IdLᴰ
  DispOverTerminal→Category .⋆IdR = ⋆IdRᴰ
  DispOverTerminal→Category .⋆Assoc = ⋆Assocᴰ
  DispOverTerminal→Category .isSetHom = isSetHomᴰ
