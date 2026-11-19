{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebra.FreeCommAlgebra.RepresentedFunctor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.FreeCommAlgebra
open import Cubical.Algebra.Algebra using (_$a_)

open import Cubical.Categories.Presheaf
open import Cubical.Categories.Instances.CommAlgebras
open import Cubical.Categories.Category
open import Cubical.Categories.Functor


private
  variable
    ℓ ℓ' : Level

module _
  {R : CommRing ℓ}
  (I : Type ℓ')
  where

  open Functor

  private
    ℓA = ℓ-max ℓ ℓ'

    Alg : Category (ℓ-suc ℓA) ℓA
    Alg = CommAlgebrasCategory R {ℓ' = ℓA}

  -- Note: One could think about constructing the 'representedFunctor' as
  -- the 'I'-th power (self-product) of the underlying-set functor instead.

  representedFunctor : Presheaf (Alg ^op) ℓA
  F-ob representedFunctor A = (I → ⟨ A ⟩) , isSet→ (CommAlgebraStr.is-set (str A))
  F-hom representedFunctor f xs i = f $a xs i
  F-id representedFunctor = refl
  F-seq representedFunctor f g = refl

  isUniversalFreeCommAlgebra :
    isUniversal
      (Alg ^op)
      representedFunctor
      (R [ I ])
      Construction.var
  isUniversalFreeCommAlgebra A = isoToIsEquiv (homMapIso A)
