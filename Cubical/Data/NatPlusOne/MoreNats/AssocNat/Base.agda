module Cubical.Data.NatPlusOne.MoreNats.AssocNat.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Nat hiding (_+_)

infixl 6 _+₁_

data ℕ₊₁ : Type where
  one : ℕ₊₁
  _+₁_ : ℕ₊₁ → ℕ₊₁ → ℕ₊₁
  assoc : (a b c : ℕ₊₁) →  a +₁ (b +₁ c) ≡ a +₁ b +₁ c
  trunc : isSet ℕ₊₁

module Elim {ℓ'} {B : ℕ₊₁ → Type ℓ'}
  (one* : B one) (_+₁*_ : {m n : ℕ₊₁} → B m → B n → B (m +₁ n))
  (assoc* : {x y z : ℕ₊₁} (x' : B x) (y' : B y) (z' : B z)
            → PathP (λ i → B (assoc x y z i))
            (x' +₁* (y' +₁* z')) ((x' +₁* y') +₁* z'))
  (trunc* : (n : ℕ₊₁) → isSet (B n)) where

  f : (n : ℕ₊₁) → B n
  f one = one*
  f (m +₁ n) = f m +₁* f n
  f (assoc x y z i) = assoc* (f x) (f y) (f z) i
  f (trunc m n p q i j) =
    isOfHLevel→isOfHLevelDep 2 trunc* (f m) (f n)
    (cong f p) (cong f q) (trunc m n p q) i j

module ElimProp {ℓ'} {B : ℕ₊₁ → Type ℓ'} (BProp : {n : ℕ₊₁} → isProp (B n))
  (one* : B one) (_+₁*_ : {m n : ℕ₊₁} → B m → B n → B (m +₁ n)) where

  f : (n : ℕ₊₁) → B n
  f = Elim.f {B = B} one* _+₁*_
        (λ {x} {y} {z} x' y' z' →
          toPathP (BProp (transport (λ i → B (assoc x y z i))
          (x' +₁* (y' +₁* z'))) ((x' +₁* y') +₁* z')))
        λ n → isProp→isSet BProp

module Rec {ℓ'} {B : Type ℓ'} (BType : isSet B)
  (one* : B) (_+₁*_ : B → B → B)
  (assoc* : (a b c : B) → a +₁* (b +₁* c) ≡ (a +₁* b) +₁* c) where

  f : ℕ₊₁ → B
  f = Elim.f one* (λ m n → m +₁* n) assoc* λ _ → BType

private
  constraintNumber : ℕ → Type
  constraintNumber zero = ⊥
  constraintNumber (suc _) = Unit

  fromNat' : (n : ℕ) ⦃ _ : constraintNumber n ⦄ → ℕ₊₁
  fromNat' zero ⦃ () ⦄
  fromNat' (suc zero) = one
  fromNat' (suc (suc n)) = fromNat' (suc n) +₁ one

instance
  NumN : HasFromNat ℕ₊₁
  NumN = record { Constraint = constraintNumber ; fromNat = fromNat' }
