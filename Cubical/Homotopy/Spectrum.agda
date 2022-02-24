{-# OPTIONS --safe #-}
{-
  Define
  * Spectrum (Plural: Spectra)
  * Morphisms of spectra
  Construct
  * Π-spectrum of a parametrized spectrum (=dependent spectrum)

  This uses ideas from Floris van Doorn's phd thesis and the code in
  https://github.com/cmu-phil/Spectral/blob/master/spectrum/basic.hlean
-}
module Cubical.Homotopy.Spectrum where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed

open import Cubical.Data.Int

open import Cubical.Homotopy.Prespectrum
open import Cubical.Homotopy.Loopspace

open import Cubical.Foundations.Structure
open import Cubical.Syntax.⟨⟩

private
  variable
    ℓ : Level

record Spectrum (ℓ : Level) : Type (ℓ-suc ℓ) where
  open GenericPrespectrum public
  field
    prespectrum : Prespectrum ℓ
    equiv : (k : ℤ) → isEquiv (fst (map prespectrum k))
  open GenericPrespectrum prespectrum public

open Spectrum

_→ₛ_ : (A B : Spectrum ℓ) → Type ℓ
A →ₛ B = Σ[ f ∈ ((k : ℤ) → space A k →∙ space B k) ]
          IsPrespectrumMor {A = prespectrum A} {B = prespectrum B} f

{-
  A dependent spectrum over a type is a mathematically quite interesting object -
  classicly called 'parametrized spectrum'.
-}
module parametrized {X : Type ℓ} (A : X → Spectrum ℓ) where
  private
    Πₛ-type : (k : ℤ) → Pointed ℓ
    Πₛ-type k = Πᵘ∙ X (λ x → space (A x) k)
    pointwiseMap : (k : ℤ) → Πₛ-type k →∙ Ω (Πₛ-type (sucℤ k))
    pointwiseMap k = (λ ψ → λ i x → fst (map (A x) k) (ψ x) i) ,
                            λ i j x → snd (map (A x) k) i j
    pointwiseIso : (k : ℤ) (x : X) → Iso ⟨ space (A x) k ⟩ ⟨ Ω (space (A x) (sucℤ k)) ⟩
    pointwiseIso k x = equivToIso (fst (map (A x) k) , equiv (A x) k)
    
  Πₛ : Spectrum ℓ
  space (prespectrum Πₛ) k = Πₛ-type k
  map (prespectrum Πₛ) k = pointwiseMap k
  equiv Πₛ k =
    snd (isoToEquiv
          (iso
            (λ f → λ i x → fun (pointwiseIso k x) (f x) i)
            (λ g → λ x → inv (pointwiseIso k x) (λ i → g i x))
            (λ g → λ i j x → rightInv (pointwiseIso k x) (λ i → g i x) i j)
            λ f → λ i x → leftInv (pointwiseIso k x) (f x) i))

    where open Iso

