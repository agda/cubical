{-# OPTIONS --cubical --safe #-}
module Cubical.ZCohomology.Base where

open import Cubical.Data.Int.Base
open import Cubical.Data.Nat.Base
open import Cubical.Data.NatMinusTwo.Base
open import Cubical.Data.Sigma

open import Cubical.Foundations.Pointed.Base

open import Cubical.HITs.Nullification.Base
open import Cubical.HITs.SetTruncation.Base
open import Cubical.HITs.Sn.Base
open import Cubical.HITs.Susp.Base
open import Cubical.HITs.Truncation.Base

private
  variable
    ℓ : Level
    A : Type ℓ


--- Cohomology ---

{- Types Kₙ from Brunerie 2016 -}
coHomK : (n : ℕ) → Type₀
coHomK zero = Int
coHomK (suc n) = ∥ S₊ (suc n) ∥  (ℕ→ℕ₋₂ (suc n))

{- Cohomology -}
coHom : (n : ℕ) → Type ℓ → Type ℓ
coHom n A = ∥ (A → coHomK n) ∥₀


--- Reduced cohomology ---

{- Pointed version of Kₙ  -}
coHomK-ptd : (n : ℕ) → Pointed (ℓ-zero)
coHomK-ptd zero = coHomK zero , (pos 0)
coHomK-ptd (suc n) = (coHomK (suc n) , ∣ north ∣)

{- Reduced cohomology -}
coHomRed : (n : ℕ) → (A : Pointed ℓ) → Type ℓ
coHomRed n A = ∥  (A →∙ (coHomK-ptd n)) ∥₀
