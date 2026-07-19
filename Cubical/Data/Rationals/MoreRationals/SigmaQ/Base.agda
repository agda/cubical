module Cubical.Data.Rationals.MoreRationals.SigmaQ.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Int.MoreInts.QuoInt

open import Cubical.Data.Nat as ℕ hiding (_·_)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma

open import Cubical.Data.Nat.GCD
open import Cubical.Data.Nat.Coprime


-- ℚ as the set of coprime pairs in ℤ × ℕ₊₁

ℚ : Type₀
ℚ = Σ[ (a , b) ∈ ℤ × ℕ₊₁ ] areCoprime (abs a , ℕ₊₁→ℕ b)

isSetℚ : isSet ℚ
isSetℚ = isSetΣ (isSet× isSetℤ (subst isSet 1+Path isSetℕ)) (λ _ → isProp→isSet isPropIsGCD)


signedPair : Sign → ℕ × ℕ₊₁ → ℤ × ℕ₊₁
signedPair s (a , b) = (signed s a , b)

[_] : ℤ × ℕ₊₁ → ℚ
[ signed s a , b ] = signedPair s (toCoprime (a , b)) , toCoprimeAreCoprime (a , b)
[ posneg i   , b ] = (posneg i , 1) , toCoprimeAreCoprime (0 , b)

[]-cancelʳ : ∀ ((a , b) : ℤ × ℕ₊₁) k → [ a · pos (ℕ₊₁→ℕ k) , b ·₊₁ k ] ≡ [ a , b ]
[]-cancelʳ (signed s zero    , b) k =
  Σ≡Prop (λ _ → isPropIsGCD) (λ i → signed-zero spos s i , 1)
[]-cancelʳ (signed s (suc a) , b) k =
  Σ≡Prop (λ _ → isPropIsGCD) (λ i → signedPair (·S-comm s spos i)
                                               (toCoprime-cancelʳ (suc a , b) k i))
[]-cancelʳ (posneg i ,         b) k j =
  isSet→isSet' isSetℚ ([]-cancelʳ (pos zero , b) k) ([]-cancelʳ (neg zero , b) k)
                      (λ i → [ posneg i · pos (ℕ₊₁→ℕ k) , b ·₊₁ k ]) (λ i → [ posneg i , b ]) i j


-- Natural number and negative integer literals for ℚ

open import Cubical.Data.Nat.Literals public

instance
  fromNatℚ : HasFromNat ℚ
  fromNatℚ = record { Constraint = λ _ → Unit ; fromNat = λ n → (pos n , 1) , oneGCD n }

instance
  fromNegℚ : HasFromNeg ℚ
  fromNegℚ = record { Constraint = λ _ → Unit ; fromNeg = λ n → (neg n , 1) , oneGCD n }
