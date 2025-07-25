module Cubical.Data.FinData.DepFinVec where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; _·_; +-assoc)

open import Cubical.Data.FinData.Base
open import Cubical.Data.FinData.Properties

private
  variable
    ℓ ℓ' : Level

{-

  WARNING : If someone use dependent vector in a general case.
            One always think about the following definition.
            Yet because of the definition one to add (toℕ k).
            Which is going to introduce a lot of issues.
            One may consider depVec rather than depFinVec to avoid this issue?
-}

depFinVec : ((n : ℕ) → Type ℓ) → (m : ℕ) → Type ℓ
depFinVec G m = (k : Fin m) → G (toℕ k)
