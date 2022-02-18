{-# OPTIONS --safe #-}
module Cubical.Data.NatPlusOne.MoreNats.AssocNat.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat
open import Cubical.Data.NatPlusOne.MoreNats.AssocNat.Base
open import Cubical.Data.NatPlusOne renaming (ℕ₊₁ to ℕ₊₁'; one to one'; _+₁_ to _+₁'_)

to : ℕ₊₁' → ℕ₊₁
to one' = 1
to (2+ n) = 1 +₁ to (1+ n)

from : ℕ₊₁ → ℕ₊₁'
from one = 1
from (a +₁ b) = from a +₁' from b
from (assoc a b c i) = +₁-assoc (from a) (from b) (from c) i
from (trunc m n p q i j) =
  1+ (isSetℕ _ _ (λ k → -1+ (from (p k))) (λ k → -1+ (from (q k))) i j)

from∘to : ∀ n → from (to n) ≡ n
from∘to one' = refl
from∘to (2+ n) = cong (1+_ ∘ suc ∘ -1+_) (from∘to (1+ n))

private
  to-+ : ∀ a b → to (a +₁' b) ≡ to a +₁ to b
  to-+ one' b = refl
  to-+ (2+ a) b = cong (one +₁_) (to-+ (1+ a) b)
    ∙ assoc one (to (1+ a)) (to b)

to∘from : ∀ n → to (from n) ≡ n
to∘from = ElimProp.f (trunc _ _) (λ i → one)
  λ {a} {b} m n → to-+ (from a) (from b) ∙ (λ i → m i +₁ n i)

ℕ₊₁≃ℕ₊₁' : Iso ℕ₊₁ ℕ₊₁'
ℕ₊₁≃ℕ₊₁' = iso from to from∘to to∘from
