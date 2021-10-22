{-# OPTIONS --safe #-}
{-
  This uses ideas from Floris van Doorn's phd thesis and the code in
  https://github.com/cmu-phil/Spectral/blob/master/spectrum/basic.hlean
-}
module Cubical.Homotopy.Prespectrum where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Pointed
open import Cubical.Data.Unit.Pointed

open import Cubical.Structures.Successor

open import Cubical.Data.Nat
open import Cubical.Data.Int

open import Cubical.HITs.Susp

open import Cubical.Homotopy.Loopspace

private
  variable
    ℓ ℓ′ : Level

record GenericPrespectrum (S : SuccStr ℓ) (ℓ′ : Level) : Type (ℓ-max (ℓ-suc ℓ′) ℓ) where
  open SuccStr S
  field
    space : Index → Pointed ℓ′
    map : (i : Index) → (space i →∙ Ω (space (succ i)))

Prespectrum = GenericPrespectrum ℤ+

Unit∙→ΩUnit∙ : {ℓ : Level} → (Unit∙ {ℓ = ℓ}) →∙ Ω (Unit∙ {ℓ = ℓ})
Unit∙→ΩUnit∙ = (λ {tt* → refl}) , refl

makeℤPrespectrum : (space : ℕ → Pointed ℓ)
                  (map : (i : ℕ) → (space i) →∙ Ω (space (suc i)))
                → Prespectrum ℓ
GenericPrespectrum.space (makeℤPrespectrum space map) (pos n) = space n
GenericPrespectrum.space (makeℤPrespectrum space map) (negsuc n) = Unit∙
GenericPrespectrum.map (makeℤPrespectrum space map) (pos n) = map n
GenericPrespectrum.map (makeℤPrespectrum space map) (negsuc zero) = (λ {tt* → refl}) , refl
GenericPrespectrum.map (makeℤPrespectrum space map) (negsuc (suc n)) = Unit∙→ΩUnit∙

SuspensionPrespectrum : Pointed ℓ → Prespectrum ℓ
SuspensionPrespectrum A = makeℤPrespectrum space map
          where
            space : ℕ → Pointed _
            space zero = A
            space (suc n) = Susp∙ (typ (space n))

            map : (n : ℕ) → _
            map n = toSuspPointed (space n)
