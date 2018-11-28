{-# OPTIONS --cubical #-}
module Cubical.HITs.Hopf where

open import Cubical.Core.Primitives
open import Cubical.Core.Prelude
open import Cubical.Core.Glue

open import Cubical.HITs.S1
open import Cubical.HITs.S2
open import Cubical.HITs.Susp

-- Hopf fibration using S²
HopfS² : S² → Set
HopfS² base = S¹
HopfS² (surf i j) = Glue S¹ (λ { (i = i0) → _ , idEquiv S¹
                               ; (i = i1) → _ , idEquiv S¹
                               ; (j = i0) → _ , idEquiv S¹
                               ; (j = i1) → _ , _ , rotIsEquiv (loop i) } )

-- Alternative version of Hopf inspired from redtt. It seems to
-- compute slower than the one above.
HopfS²' : S² → Set
HopfS²' base = S¹
HopfS²' (surf i j) = hcomp (λ k → λ { (i = i0) → ua (idEquiv S¹) k
                                    ; (j = i0) → ua (idEquiv S¹) k
                                    ; (i = i1) → ua (_ , (rotIsEquiv (loop j))) k
                                    ; (j = i1) → ua (idEquiv S¹) k }) S¹

-- Hopf fibration using suspension of S¹
HopfSuspS¹ : SuspS¹ → Set
HopfSuspS¹ north = S¹
HopfSuspS¹ south = S¹
HopfSuspS¹ (merid x i) = ua (_ , rotIsEquiv x) i

