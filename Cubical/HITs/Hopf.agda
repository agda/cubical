{-# OPTIONS --cubical #-}
module Cubical.HITs.Hopf where

open import Cubical.Core.Primitives
open import Cubical.Core.Prelude
open import Cubical.Core.Glue

open import Cubical.HITs.S1
open import Cubical.HITs.S2
open import Cubical.HITs.Susp

-- TODO: package up Glue?
-- Hopf fibration using S²
HopfS² : S² → Set
HopfS² base = S¹
HopfS² (surf i j) = Glue S¹ (λ _ → S¹)
                            (λ { (i = i0) → _ , idIsEquiv S¹
                               ; (i = i1) → _ , idIsEquiv S¹
                               ; (j = i0) → _ , rotIsEquiv (loop i)
                               ; (j = i1) → _ , idIsEquiv S¹ } )

-- Hopf fibration using suspension of S¹
HopfSuspS¹ : SuspS¹ → Set
HopfSuspS¹ north = S¹
HopfSuspS¹ south = S¹
HopfSuspS¹ (merid x i) = ua (_ , rotIsEquiv x) i
