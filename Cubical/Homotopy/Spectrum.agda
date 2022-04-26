{-# OPTIONS --safe #-}
{-
  This uses ideas from Floris van Doorn's phd thesis and the code in
  https://github.com/cmu-phil/Spectral/blob/master/spectrum/basic.hlean
-}
module Cubical.Homotopy.Spectrum where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit.Pointed
open import Cubical.Foundations.Equiv

open import Cubical.Data.Int

open import Cubical.Homotopy.Prespectrum

private
  variable
    ℓ : Level

record Spectrum (ℓ : Level) : Type (ℓ-suc ℓ) where
  open GenericPrespectrum
  field
    prespectrum : Prespectrum ℓ
    equiv : (k : ℤ) → isEquiv (fst (map prespectrum k))
  open GenericPrespectrum prespectrum public
