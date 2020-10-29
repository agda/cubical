{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.ZCohomology.Base where

open import Cubical.Data.Int.Base
open import Cubical.Data.Nat.Base
open import Cubical.Data.Sigma

open import Cubical.Foundations.Pointed.Base

open import Cubical.HITs.Nullification.Base
open import Cubical.HITs.SetTruncation.Base
open import Cubical.HITs.Sn.Base
open import Cubical.HITs.S1.Base
open import Cubical.HITs.Susp.Base
open import Cubical.HITs.Truncation.Base

private
  variable
    ℓ : Level
    A : Type ℓ

--- Cohomology ---

{- EM-spaces Kₙ from Brunerie 2016 -}
coHomK : (n : ℕ) → Type₀
coHomK zero = Int
coHomK (suc n) = ∥ S₊ (suc n) ∥ (2 + suc n)

{- Cohomology -}
coHom : (n : ℕ) → Type ℓ → Type ℓ
coHom n A = ∥ (A → coHomK n) ∥₂


--- Reduced cohomology ---

{- Pointed version of Kₙ  -}
coHomK-ptd : (n : ℕ) → Pointed (ℓ-zero)
coHomK-ptd 0 = coHomK 0 , 0
coHomK-ptd 1 = coHomK 1 , ∣ base ∣
coHomK-ptd (suc (suc n)) = coHomK (2 + n) , ∣ north ∣

{- Reduced cohomology -}
coHomRed : (n : ℕ) → (A : Pointed ℓ) → Type ℓ
coHomRed n A = ∥ A →∙ coHomK-ptd n ∥₂

coHom-pt : (n : ℕ) → coHomK n
coHom-pt 0 = 0
coHom-pt 1 = ∣ base ∣
coHom-pt (suc (suc n)) = ∣ north ∣
