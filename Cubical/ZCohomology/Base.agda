{-# OPTIONS --cubical --safe #-}
module Cubical.ZCohomology.Base where


open import Cubical.Data.Int.Base
open import Cubical.Data.Nat.Base
open import Cubical.Data.NatMinusTwo.Base
open import Cubical.Data.Sigma.Base

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

{-
Definition of cohomology with cocefficients in the integers. For now, this definition uses ℕ₋₂, for instance defining H⁰ as
coHom neg2, H¹ as coHom (suc neg2), and so on. This has so far been easier to work with than a definition relying on ℕ→ℕ₋₂.
-}


--- Cohomology ---

{- Types Kₙ from Brunerie 2016 -}
coHomK : (n : ℕ₋₂) → Type₀
coHomK neg2 = Int
coHomK (suc n) = ∥ S₊ (2+ suc n) ∥  (suc (suc (suc n)))

{- Cohomology -}
coHom : (n : ℕ₋₂) → Type ℓ → Type ℓ
coHom n A = ∥ (A → coHomK n) ∥₀


--- Reduced cohomology ---

{- Pointed version of Kₙ  -}
coHomK-ptd : (n : ℕ₋₂) → Pointed (ℓ-zero)
coHomK-ptd neg2 = coHomK neg2 , (pos 0)
coHomK-ptd (suc n) = (coHomK (suc n) , ∣ north ∣)

{- Reduced cohomology -}
coHomRed : (n : ℕ₋₂) → (A : Pointed ℓ) → Type ℓ
coHomRed neg2 A = ∥  (A →* (coHomK-ptd neg2)) ∥₀
coHomRed (suc n) A = ∥  (A →* (coHomK-ptd (suc n))) ∥₀
