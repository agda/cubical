module Cubical.Categories.Instances.ZFunctors where

{-

  The category of ℤ-functors is the category of functors from rings to sets.
  It contains the category of schemes as a full subcategory and is thus of
  special interest to algebraic geometers. The basic notions needed to
  develop algebraic geometry using ℤ-functors can be found in:

-}

open import Cubical.AlgebraicGeometry.Functorial.ZFunctors.Base public

{-

  In Cubical Agda we can define the full subcategory of qcqs-schemes.
  This is done in:

-}

open import Cubical.AlgebraicGeometry.Functorial.ZFunctors.CompactOpen
open import Cubical.AlgebraicGeometry.Functorial.ZFunctors.QcQsScheme
open import Cubical.AlgebraicGeometry.Functorial.ZFunctors.OpenSubscheme
