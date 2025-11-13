{-
  This uses ideas from Floris van Doorn's phd thesis and the code in
  https://github.com/cmu-phil/Spectral/blob/master/spectrum/basic.hlean
-}
module Cubical.Homotopy.Spectrum where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Data.Unit.Pointed
open import Cubical.Foundations.Equiv
open import Cubical.Structures.Successor

open import Cubical.Data.Int

open import Cubical.Homotopy.Prespectrum
open import Cubical.Homotopy.Loopspace

private
  variable
    ℓ ℓ' : Level

record Spectrum (ℓ : Level) : Type (ℓ-suc ℓ) where
  open GenericPrespectrum
  field
    prespectrum : Prespectrum ℓ
    equiv : (k : ℤ) → isEquiv (fst (map prespectrum k))
  open GenericPrespectrum prespectrum public

open Spectrum
open GenericPrespectrum

module _ where
  open SuccStr ℤ+

  mkSpectrum : (X : Index → Pointed ℓ') → (e : (n : Index) → X n ≃∙ Ω (X (succ n))) → Spectrum ℓ'
  mkSpectrum {ℓ'} X e .prespectrum .space = X
  mkSpectrum {ℓ'} X e .prespectrum .map n = ≃∙map (e n)
  mkSpectrum {ℓ'} X e .equiv n = e n .fst .snd

  spectrumEquiv : (E : Spectrum ℓ) → (n : ℤ) → E .space n ≃∙ Ω (E .space (succ n))
  spectrumEquiv E n = (E .map n .fst , E .equiv n) , E .map n .snd

isSpectrumMap : (X Y : Spectrum ℓ) → (f : (n : ℤ) → (X .space n →∙ Y .space n)) → Type ℓ
isSpectrumMap X Y f = (n : ℤ) → (Y .map n ∘∙ f n) ∙∼ (Ω→ (f (sucℤ n)) ∘∙ X .map n)

_→Sp_ : (X Y : Spectrum ℓ) → Type ℓ
X →Sp Y = Σ ((n : ℤ) → (X .space n →∙ Y .space n)) (isSpectrumMap X Y)
