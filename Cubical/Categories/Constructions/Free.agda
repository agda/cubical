-- Free category over a directed graph/quiver
{-# OPTIONS --safe #-}

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
    FreeCategory ._⋆_ = ccat G
    FreeCategory .⋆IdL = pnil++ G
    FreeCategory .⋆IdR P = refl
    FreeCategory .⋆Assoc = ++assoc G
    FreeCategory .isSetHom = isSetPath G isSetNode isSetEdge _ _
