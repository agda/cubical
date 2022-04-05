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
open import Cubical.Foundations.GroupoidLaws

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

idₛ : (A : Spectrum ℓ) → A →ₛ A
idₛ A = (λ k → id∙ (space A k)) , λ k → {!!}
    where commΩid : (k : _) → Ω→ (id∙ (space (prespectrum A) (sucℤ k))) ≡ id∙ (Ω (space (prespectrum A) (sucℤ k)))
          commΩid k i = (λ p → eq p i) , {!!}
            where eq : (p : _ ≡ _) → sym refl ∙∙ p ∙∙ refl ≡ p
                  eq p = sym refl ∙∙ p ∙∙ refl ≡⟨ doubleCompPath-elim (sym refl) p refl ⟩
                         (sym refl ∙ p) ∙ refl ≡⟨ sym (rUnit _) ⟩
                         sym refl ∙ p          ≡⟨ cong (λ u → u ∙ p) (sym symRefl) ⟩
                         refl ∙ p              ≡⟨ sym (lUnit p) ⟩
                         p ∎

_∘ₛ_ : {A B C : Spectrum ℓ}
     → (B →ₛ C) → (A →ₛ B) → (A →ₛ C)
f ∘ₛ g = {!!}

{-
  A dependent spectrum over a type is a mathematically quite interesting object -
  classicly called 'parametrized spectrum'.
-}
module parametrized {X : Type ℓ} where
  {-
    The following proofs about Π-types of spectra are really only
    about applying function extensionality in various ways...
  -}
  module _  (A : X → Spectrum ℓ) where
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

  module _ {A B : X → Spectrum ℓ} (f : (x : X) → A x →ₛ B x) where
    Π→ₛ : Πₛ A →ₛ Πₛ B
    Π→ₛ = Πf , isMor
        where
          Πf = (λ k → (λ ϕ → λ x → fst (fst (f x) k) (ϕ x)) ,
                λ i → λ x → snd (fst (f x) k) i)
          isMor : IsPrespectrumMor {A = prespectrum (Πₛ A)} {B = prespectrum (Πₛ B)} Πf
          isMor k i = (λ ϕ → λ j x → fst (snd (f x) k i) (ϕ x) j) ,
                      λ l → λ j x → snd (snd (f x) k i) l j
