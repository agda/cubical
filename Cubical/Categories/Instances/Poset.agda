{-# OPTIONS --safe #-}
module Cubical.Categories.Instances.Poset where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Binary.Poset

open import Cubical.Categories.Category

open Category

private
  variable
    ℓ ℓ' : Level

module _ (P : Poset ℓ ℓ') where

  open PosetStr (snd P)

  PosetCategory : Category ℓ ℓ'
  ob PosetCategory           = fst P
  Hom[_,_] PosetCategory     = _≤_
  id PosetCategory           = is-refl _
  _⋆_ PosetCategory          = is-trans _ _ _
  ⋆IdL PosetCategory _       = is-prop-valued _ _ _ _
  ⋆IdR PosetCategory _       = is-prop-valued _ _ _ _
  ⋆Assoc PosetCategory _ _ _ = is-prop-valued _ _ _ _
  isSetHom PosetCategory     = isProp→isSet (is-prop-valued _ _)
