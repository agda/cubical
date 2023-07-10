{- Propositional truncation for the inductively defined equality type ≡, using paths internally -}

{-# OPTIONS --safe #-}
module Cubical.Data.Equality.PropositionalTruncation where

open import Cubical.HITs.PropositionalTruncation
  using ()
  renaming ( rec to recPropTruncPath
           ; elim to elimPropTruncPath
           ; squash₁ to squash₁Path
           )

open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; ∣_∣₁) public

open import Cubical.Data.Equality.Base
open import Cubical.Data.Equality.Conversion

private
 variable
  ℓ ℓ' : Level
  A B : Type ℓ
  x y z : A

squash₁ : (x y : ∥ A ∥₁) → x ≡ y
squash₁ x y = pathToEq (squash₁Path x y)

∥∥-rec : {A : Type ℓ} {P : Type ℓ'} → isProp P → (A → P) → ∥ A ∥₁ → P
∥∥-rec Pprop = recPropTruncPath (isPropToIsPropPath Pprop)

∥∥-elim : {A : Type ℓ} {P : ∥ A ∥₁ → Type ℓ'} → ((a : ∥ A ∥₁) → isProp (P a)) →
                ((x : A) → P ∣ x ∣₁) → (a : ∥ A ∥₁) → P a
∥∥-elim Pprop = elimPropTruncPath (λ a → isPropToIsPropPath (Pprop a))
