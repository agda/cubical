{-

This file contains:

- Definition of propositional truncation and its eliminator


It should *not* depend on the Agda standard library

-}
{-# OPTIONS --cubical #-}
module Cubical.Core.PropositionalTruncation where

open import Cubical.Core.Prelude

-- Propositional truncation as a higher inductive type:

data ∥_∥ {ℓ} (A : Set ℓ) : Set ℓ where
  ∣_∣ : A → ∥ A ∥
  squash : ∀ (x y : ∥ A ∥) → x ≡ y

recPropTrunc : ∀ {ℓ} {A : Set ℓ} {P : Set ℓ} → isProp P → (A → P) → ∥ A ∥ → P
recPropTrunc Pprop f ∣ x ∣          = f x
recPropTrunc Pprop f (squash x y i) =
  Pprop (recPropTrunc Pprop f x) (recPropTrunc Pprop f y) i

propTruncIsProp : ∀ {ℓ} {A : Set ℓ} → isProp ∥ A ∥
propTruncIsProp x y = squash x y

-- -- Maybe define this directly by induction as well?
-- elimPropTrunc : ∀ {ℓ} {A : Set ℓ} {P : ∥ A ∥ → Set ℓ} → ((a : ∥ A ∥) → isProp (P a)) →
--                 ((x : A) → P ∣ x ∣) → (a : ∥ A ∥) → P a
-- elimPropTrunc {P = P} Pprop f a =
--   recPropTrunc (Pprop a) (λ x → transp (λ i → P (squash ∣ x ∣ a i)) i0 (f x)) a

elimPropTrunc : ∀ {ℓ} {A : Set ℓ} {P : ∥ A ∥ → Set ℓ} → ((a : ∥ A ∥) → isProp (P a)) →
                ((x : A) → P ∣ x ∣) → (a : ∥ A ∥) → P a
elimPropTrunc                 Pprop f ∣ x ∣          = f x
elimPropTrunc {A = A} {P = P} Pprop f (squash x y i) = PpropOver (squash x y) (elimPropTrunc Pprop f x) (elimPropTrunc Pprop f y) i
   where
     PpropOver : {a b : ∥ A ∥} → (sq : a ≡ b) → ∀ x y → PathP (\ i → P (sq i)) x y
     PpropOver {a} = J (\ b (sq : a ≡ b) → ∀ x y → PathP (\ i → P (sq i)) x y) (Pprop a)
