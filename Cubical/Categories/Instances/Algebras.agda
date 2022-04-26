{-# OPTIONS --safe #-}
module Cubical.Categories.Instances.Algebras where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.Ring
open import Cubical.Algebra.Algebra

open import Cubical.Categories.Category

open Category
open AlgebraHoms

private
 variable
  ℓ ℓ' : Level

module _ (R : Ring ℓ) where
  AlgebrasCategory : Category (ℓ-suc (ℓ-max ℓ ℓ')) (ℓ-max ℓ ℓ')
  ob AlgebrasCategory       = Algebra R _
  Hom[_,_] AlgebrasCategory = AlgebraHom
  id AlgebrasCategory {A}   = idAlgebraHom A
  _⋆_ AlgebrasCategory      = compAlgebraHom
  ⋆IdL AlgebrasCategory     = compIdAlgebraHom
  ⋆IdR AlgebrasCategory     = idCompAlgebraHom
  ⋆Assoc AlgebrasCategory   = compAssocAlgebraHom
  isSetHom AlgebrasCategory = isSetAlgebraHom _ _
