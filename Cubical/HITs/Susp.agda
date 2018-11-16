{-# OPTIONS --cubical #-}
module Cubical.HITs.Susp where

open import Cubical.Core.Primitives
open import Cubical.Core.Prelude
open import Cubical.Core.Glue

open import Cubical.Basics.Bool
open import Cubical.Basics.Equiv

open import Cubical.HITs.S1
open import Cubical.HITs.S2

data Susp {ℓ} (A : Set ℓ) : Set ℓ where
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

SuspBool→S¹→SuspBool : (x : SuspBool) → Path _ (S¹→SuspBool (SuspBool→S¹ x)) x
SuspBool→S¹→SuspBool north = refl
SuspBool→S¹→SuspBool south = merid true 
SuspBool→S¹→SuspBool (merid false i) = λ j → hcomp (λ k → (λ { (j = i1) → merid false i
                                                             ; (i = i0) → north
                                                             ; (i = i1) → merid true (j ∨ ~ k)}))
                                                   (merid false i)
SuspBool→S¹→SuspBool (merid true i)  = λ j → merid true (i ∧ j)

S¹→SuspBool→S¹ : (x : S¹) → SuspBool→S¹ (S¹→SuspBool x) ≡ x
S¹→SuspBool→S¹ base     = refl
S¹→SuspBool→S¹ (loop i) = λ j →
  hfill (λ k → \ { (i = i0) → base; (i = i1) → base }) (inc (loop i)) (~ j)

S¹≃SuspBool : S¹ ≃ SuspBool
S¹≃SuspBool = isoToEquiv S¹→SuspBool SuspBool→S¹ SuspBool→S¹→SuspBool S¹→SuspBool→S¹

S¹≡SuspBool : S¹ ≡ SuspBool
S¹≡SuspBool = isoToPath S¹→SuspBool SuspBool→S¹ SuspBool→S¹→SuspBool S¹→SuspBool→S¹


-- Now the sphere

SuspS¹ : Set
SuspS¹ = Susp S¹

-- SuspS¹→S² : SuspS¹ → S²
-- SuspS¹→S² north = base
-- SuspS¹→S² south = base
-- SuspS¹→S² (merid a i) = {!!}

S²→SuspS¹ : S² → SuspS¹
S²→SuspS¹ base = north
S²→SuspS¹ (surf i j) = hcomp (λ k → λ { (i = i0) → north
                                      ; (i = i1) → merid base (~ k)
                                      ; (j = i0) → merid base (~ k ∧ i)
                                      ; (j = i1) → merid base (~ k ∧ i) })
                             (merid (loop j) i)
