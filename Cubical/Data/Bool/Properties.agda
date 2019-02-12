{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Bool.Properties where

open import Cubical.Core.Everything

open import Cubical.Foundations.Equiv

open import Cubical.Data.Bool.Base

notnot : ∀ x → not (not x) ≡ x
notnot true  = refl
notnot false = refl

notIsEquiv : isEquiv not
notIsEquiv = isoToIsEquiv (iso not not notnot notnot) 

notEquiv : Bool ≃ Bool
notEquiv = (not , notIsEquiv)

notEq : Bool ≡ Bool
notEq = ua notEquiv

private
  -- This computes to false as expected
  nfalse : Bool
  nfalse = transp (λ i → notEq i) i0 true
  
  -- Sanity check
  nfalsepath : nfalse ≡ false
  nfalsepath = refl
