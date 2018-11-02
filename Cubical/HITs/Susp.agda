{-# OPTIONS --cubical #-}
module Cubical.HITs.Susp where

open import Cubical.Core.Primitives
open import Cubical.Core.Prelude
open import Cubical.Core.Glue

-- open import Cubical.Basics.Int
open import Cubical.Basics.Bool
open import Cubical.Basics.IsoToEquiv

open import Cubical.HITs.Circle

data Susp (A : Set) : Set where
  north : Susp A
  south : Susp A
  merid : (a : A) → north ≡ south


SuspBool : Set
SuspBool = Susp Bool

SuspBool→S¹ : SuspBool → S¹
SuspBool→S¹ north = base
SuspBool→S¹ south = base
SuspBool→S¹ (merid false i) = loop i
SuspBool→S¹ (merid true i)  = base

S¹→SuspBool : S¹ → SuspBool
S¹→SuspBool base     = north
S¹→SuspBool (loop i) = compPath (merid false) (sym (merid true)) i

S¹→SuspBool→S¹ : (x : S¹) → SuspBool→S¹ (S¹→SuspBool x) ≡ x
S¹→SuspBool→S¹ base = refl
S¹→SuspBool→S¹ (loop i) = rem2
  where
  -- This should be refl!
  rem : SuspBool→S¹ (compPath (merid false) (sym (merid true)) i) ≡ 
        compPath (λ i → SuspBool→S¹ (merid false i)) (λ i → SuspBool→S¹ (sym (merid true) i)) i
  rem = {!refl!}

  rem2 : SuspBool→S¹ (hcomp (λ j → \ { (i = i0) → north
                                     ; (i = i1) → merid true (~ j) }) (merid false i))
       ≡ loop i
  rem2 = {!!}

  -- This should be the goal!
  rem3 : compPath loop refl i ≡ loop i
  rem3 = {!!}
