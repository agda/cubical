module Cubical.Homotopy.Spectrum.Truncation where

open import Cubical.Data.Int
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Prelude
open import Cubical.HITs.Truncation as T
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Prespectrum
open import Cubical.Homotopy.Spectrum

private variable ℓ ℓ' : Level

open Spectrum
open GenericPrespectrum

hLevelTrunc∙-Ω-zero : (X : Pointed ℓ) → Ω (hLevelTrunc∙ zero X) ≃∙ hLevelTrunc∙ zero (Ω X)
hLevelTrunc∙-Ω-zero X .fst = isContr→≃Unit* (isContr→isContrPath isContrUnit* tt* tt*)
hLevelTrunc∙-Ω-zero X .snd = refl

hLevelTrunc∙-Ω-suc : (X : Pointed ℓ) (n : ℕ) → Ω (hLevelTrunc∙ (suc n) X) ≃∙ hLevelTrunc∙ n (Ω X)
hLevelTrunc∙-Ω-suc X n .fst = isoToEquiv (T.PathIdTruncIso n)
hLevelTrunc∙-Ω-suc X zero .snd = refl
hLevelTrunc∙-Ω-suc X (suc n) .snd = sym (T.ΩTrunc.encode-fill ∣ X .snd ∣ ∣ X .snd ∣ refl)

hLevelTrunc∙-≃-clamp : (X : Pointed ℓ) (k : ℤ) → Ω (hLevelTrunc∙ (clamp (sucℤ k)) X) ≃∙ hLevelTrunc∙ (clamp k) (Ω X)
hLevelTrunc∙-≃-clamp X (pos n) = hLevelTrunc∙-Ω-suc X n
hLevelTrunc∙-≃-clamp X (negsuc zero) = hLevelTrunc∙-Ω-zero X
hLevelTrunc∙-≃-clamp X (negsuc (suc n)) = hLevelTrunc∙-Ω-zero X

∥_∥ₛ :  (n : ℤ) (E : Spectrum ℓ) → Spectrum ℓ
∥_∥ₛ n  E = mkSpectrum
  (λ x → hLevelTrunc∙ (clamp x) (E .space x))
  (λ x → compEquiv∙ (hLevelTrunc∙-≃ (clamp x) (spectrumEquiv E x)) (invEquiv∙ (hLevelTrunc∙-≃-clamp (E .space (sucℤ x)) x)))
