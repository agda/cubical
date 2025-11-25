-- Free category over a directed graph/quiver

module Cubical.Categories.Constructions.Free where

open import Cubical.Categories.Category.Base
open import Cubical.Data.Graph.Base
open import Cubical.Data.Graph.Path
open import Cubical.Foundations.Prelude hiding (Path)

module _ {ℓv ℓe : Level} where

  module _ (G : Graph ℓv ℓe)
          (isSetNode : isSet (Node G))
          (isSetEdge : ∀ v w → isSet (Edge G v w)) where
    open Category

    FreeCategory : Category ℓv (ℓ-max ℓv ℓe)
    FreeCategory .ob = Node G
    FreeCategory .Hom[_,_] = Path G
    FreeCategory .id = pnil
    FreeCategory ._⋆_ = _++_
    FreeCategory .⋆IdL = pnil++
    FreeCategory .⋆IdR P = ++pnil _
    FreeCategory .⋆Assoc = ++assoc
    FreeCategory .isSetHom = isSetPath isSetNode isSetEdge _ _
