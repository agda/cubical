module Cubical.Categories.Dagger.Instances.Functors where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.FullSubcategory
open import Cubical.Categories.Instances.Functors

open import Cubical.Categories.Dagger.Base
open import Cubical.Categories.Dagger.Properties
open import Cubical.Categories.Dagger.Functor

private variable
  ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level

module _ (C : †Category ℓC ℓC') (D : †Category ℓD ℓD') where

  open Category
  open †Category
  open DaggerStr
  open IsDagger
  open NatTrans

  †FUNCTOR : †Category (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) (ℓ-max (ℓ-max ℓC ℓC') ℓD')
  †FUNCTOR .cat = FullSubcategory (FUNCTOR (C .cat) (D .cat)) (Is†Functor C D)
  †FUNCTOR .dagstr ._† {x = F} {y = G} = NT† F G
  †FUNCTOR .dagstr .is-dag .†-invol n = makeNatTransPath (funExt λ x → D .†-invol (n ⟦ x ⟧))
  †FUNCTOR .dagstr .is-dag .†-id = makeNatTransPath (funExt λ x → D .†-id)
  †FUNCTOR .dagstr .is-dag .†-seq m n = makeNatTransPath (funExt λ x → D .†-seq (m ⟦ x ⟧) (n ⟦ x ⟧))
