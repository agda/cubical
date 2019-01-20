{-# OPTIONS --cubical #-}
module Cubical.Basics.Bool where

open import Cubical.Core.Primitives
open import Cubical.Core.Prelude
open import Cubical.Core.Glue

open import Cubical.Basics.Equiv

-- Obtain the booleans
open import Agda.Builtin.Bool public

not : Bool → Bool
not true = false
not false = true

notnot : ∀ x → not (not x) ≡ x
notnot true  = refl
notnot false = refl

notIsEquiv : isEquiv not
notIsEquiv = isoToIsEquiv not not notnot notnot 

notEquiv : Bool ≃ Bool
notEquiv = not , notIsEquiv

notEq : Bool ≡ Bool
notEq = ua notEquiv

private
  -- This computes to false as expected
  nfalse : Bool
  nfalse = transp (λ i → notEq i) i0 true
  
  -- Sanity check
  nfalsepath : nfalse ≡ false
  nfalsepath = refl
