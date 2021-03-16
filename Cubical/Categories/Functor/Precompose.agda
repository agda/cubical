{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Categories.Functor.Precompose where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base

open import Cubical.Categories.Instances.Functors

module _ {ℓC ℓC' ℓD ℓD' ℓE ℓE'}
  {C : Precategory ℓC ℓC'} {D : Precategory ℓD ℓD'}
  (E : Precategory ℓE ℓE') ⦃ isCatE : isCategory E ⦄ 
  (F : Functor C D)
  where

  open Functor
  open NatTrans

  precomposeF : Functor (FUNCTOR D E) (FUNCTOR C E)
  precomposeF .F-ob G = funcComp G F
  precomposeF .F-hom α .N-ob c = α .N-ob (F .F-ob c)
  precomposeF .F-hom α .N-hom f = α .N-hom (F .F-hom f)
  precomposeF .F-id = refl
  precomposeF .F-seq f g = refl
