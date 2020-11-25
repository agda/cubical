{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.ZCohomology.Base where

open import Cubical.Data.Int.Base
open import Cubical.Data.Nat.Base
open import Cubical.Data.Sigma

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed.Base

open import Cubical.HITs.Nullification.Base
open import Cubical.HITs.SetTruncation.Base
open import Cubical.HITs.Sn.Base
open import Cubical.HITs.Susp.Base
open import Cubical.HITs.Truncation.Base
open import Cubical.Homotopy.Loopspace

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

coHom-pt : (n : ℕ) → coHomK n
coHom-pt 0 = 0
coHom-pt (suc n) = ∣ (ptSn (suc n)) ∣

{- Pointed version of Kₙ  -}
coHomK-ptd : (n : ℕ) → Pointed (ℓ-zero)
coHomK-ptd n = coHomK n , coHom-pt n

{- Reduced cohomology -}
coHomRed : (n : ℕ) → (A : Pointed ℓ) → Type ℓ
coHomRed n A = ∥ A →∙ coHomK-ptd n ∥₂
