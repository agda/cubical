-- Free category over a directed graph/quiver

module Cubical.Categories.Constructions.Free where

open import Cubical.Categories.Category.Base
open import Cubical.Data.Graph.Base
open import Cubical.Data.Graph.Path
open import Cubical.Foundations.Prelude hiding (Path)

module _ {ℓv ℓe : Level}
         (G : Graph ℓv ℓe)
         (isSetEdge : ∀ v w → isSet (Hom G v w)) where
  open Category

  FreeCat : Category ℓv (ℓ-max ℓv ℓe)
  FreeCat .ob = Obj G
  FreeCat .Hom[_,_] = Path G
  FreeCat .id = pnil
  FreeCat ._⋆_ = ccat G
  FreeCat .⋆IdL = pnil++ G
  FreeCat .⋆IdR P = refl
  FreeCat .⋆Assoc = ++assoc G

  FreeCat .isSetHom = {!   !}