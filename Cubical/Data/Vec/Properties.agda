{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Vec.Properties where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
open import Cubical.Data.Vec.Base

private
  variable
    ℓ : Level


-- This is really cool!
-- Compare with: https://github.com/agda/agda-stdlib/blob/master/src/Data/Vec/Properties/WithK.agda#L32
++-assoc : ∀ {m n k} {A : Type ℓ} (xs : Vec A m) (ys : Vec A n) (zs : Vec A k) →
           PathP (λ i → Vec A (+-assoc m n k (~ i))) ((xs ++ ys) ++ zs) (xs ++ ys ++ zs)
++-assoc {m = zero} [] ys zs = refl
++-assoc {m = suc m} (x ∷ xs) ys zs i = x ∷ ++-assoc xs ys zs i
