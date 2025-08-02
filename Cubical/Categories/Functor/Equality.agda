{-
  A version of Eq for functors, convenient for parameterizing
  constructions that use J where the equalities are refl.
-}

module Cubical.Categories.Functor.Equality where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
import      Cubical.Data.Equality as Eq

private
  variable
    ℓ ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level

module _
  {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  (F : Functor C D)
  where
  open Functor

  private
    module C = Category C
    module D = Category D

  FunctorSingl : Type _
  FunctorSingl = Σ[ ob' ∈ Eq.singl (F .F-ob) ]
    Eq.singlP (Eq.ap (λ F-ob → ∀ {x}{y} → C [ x , y ] → D [ F-ob x , F-ob y ])
              (ob' .snd))
    (F .F-hom)

  module _ (G : Functor C D) where
    FunctorEq : Type _
    FunctorEq = Σ[ FG-ob ∈ F .F-ob Eq.≡ G .F-ob ]
      Eq.HEq (Eq.ap (λ F-ob → ∀ {x} {y} → C [ x , y ] → D [ F-ob x , F-ob y ])
             FG-ob)
        (F .F-hom)
        (G .F-hom)
