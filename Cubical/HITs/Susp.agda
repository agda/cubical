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

SuspBool→S¹→SuspBool : (x : SuspBool) → S¹→SuspBool (SuspBool→S¹ x) ≡ x
SuspBool→S¹→SuspBool north = refl
SuspBool→S¹→SuspBool south = merid true 
SuspBool→S¹→SuspBool (merid false i) = {!!}
SuspBool→S¹→SuspBool (merid true i)  = λ j → merid true (i ∧ j)

S¹→SuspBool→S¹ : (x : S¹) → SuspBool→S¹ (S¹→SuspBool x) ≡ x
S¹→SuspBool→S¹ base     = refl
S¹→SuspBool→S¹ (loop i) = λ j →
  -- If transp in S¹ would be the identity function then we could do an hfill here...
  fill (λ _ → S¹) (λ k → \ { (i = i0) → base
                           ; (i = i1) → base })
                  (inc (loop i)) (~ j)


  -- where
  -- rem1 : SuspBool→S¹ (compPath (merid false) (sym (merid true)) i) ≡
  --        compPathcomp loop refl i -- (merid false) (sym (merid true)) i
  --        -- comp (λ _ → S¹) (λ j → \ { (i = i0) → SuspBool→S¹ north
  --        --                          ; (i = i1) → SuspBool→S¹ (merid true (~ j)) })
  --        --                          (inc (SuspBool→S¹ (merid false i)))
  -- rem1 = refl

  -- rem2 : comp (λ _ → S¹) (λ j → \ { (i = i0) → SuspBool→S¹ north
  --                                 ; (i = i1) → SuspBool→S¹ (merid true (~ j)) })
  --                        (inc (SuspBool→S¹ (merid false i))) ≡
  --        compPath loop refl i
  --        -- hcomp (λ j → \ { (i = i0) → base
  --        --                ; (i = i1) → base }) (loop i)
  -- rem2 = compS1 (i ∨ ~ i) (λ j → \ { (i = i0) → base     -- SuspBool→S¹ north
  --                                  ; (i = i1) → base } ) -- SuspBool→S¹ (merid true (~ j)) })
  --                         (inc (loop i))                 -- (SuspBool→S¹ (merid false i)))
  
  -- -- -- This should be the goal!
  -- rem4 : compPath loop refl i ≡ loop i
  -- rem4 j = hfill (λ k → \ { (i = i0) → base
  --                         ; (i = i1) → base })
  --                (inc (loop i)) (~ j)
                       



  -- -- This is hfill
  -- compRefl : compPath loop refl ≡ loop
  -- compRefl i j = hcomp (λ k → \ { (i = i1) → loop j
  --                               ; (j = i0) → base
  --                               ; (j = i1) → base })
  --                      (loop j)
