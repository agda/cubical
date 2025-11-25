
module Cubical.WildCat.Instances.NonWild where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor

module _ {ℓ ℓ' : Level} (C : Category ℓ ℓ') where

  open WildCat
  open Category

  AsWildCat : WildCat ℓ ℓ'
  ob AsWildCat = ob C
  Hom[_,_] AsWildCat = Hom[_,_] C
  id AsWildCat = id C
  _⋆_ AsWildCat = _⋆_ C
  ⋆IdL AsWildCat = ⋆IdL C
  ⋆IdR AsWildCat = ⋆IdR C
  ⋆Assoc AsWildCat = ⋆Assoc C


module _ {ℓC ℓC' ℓD ℓD' : Level} {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} (F : Functor C D) where

  open Functor
  open WildFunctor

  AsWildFunctor : WildFunctor (AsWildCat C) (AsWildCat D)
  F-ob AsWildFunctor = F-ob F
  F-hom AsWildFunctor = F-hom F
  F-id AsWildFunctor = F-id F
  F-seq AsWildFunctor = F-seq F
