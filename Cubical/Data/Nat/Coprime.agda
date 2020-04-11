{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Nat.Coprime where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.NatPlusOne.Base

open import Cubical.Data.Prod hiding (_×_) renaming (_×Σ_ to _×_)

open import Cubical.HITs.PropositionalTruncation as PropTrunc

open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Nat.Divisibility
open import Cubical.Data.Nat.GCD

areCoprime : ℕ × ℕ₊₁ → Type₀
areCoprime (m , n) = isGCD m (ℕ₊₁→ℕ n) 1

toCoprime : ℕ × ℕ₊₁ → Σ (ℕ × ℕ₊₁) areCoprime
toCoprime (m , n) with gcdIsGCD m (ℕ₊₁→ℕ n)
... | ((d∣m , d∣sn) , gr) = (c₁ , 1+ c₂) , (∣-oneˡ c₁ , ∣-oneˡ (suc c₂)) , gr'
  where c₁ = ∣-untrunc d∣m .fst; c₂ = ∣s-untrunc d∣sn .fst
        p₁ :      c₁  * gcd m (ℕ₊₁→ℕ n) ≡ m
        p₂ : (suc c₂) * gcd m (ℕ₊₁→ℕ n) ≡ ℕ₊₁→ℕ n
        p₁ = ∣-untrunc d∣m .snd
        p₂ = ∣s-untrunc d∣sn .snd

        lem : ∀ a {b c d e} → a * b ≡ c → c * d ≡ e → a * (b * d) ≡ e
        lem a p q = *-assoc a _ _ ∙ cong (_* _) p ∙ q

        f₁ : ∀ d → prediv d c₁ → prediv d (suc c₂) → (d * gcd m (ℕ₊₁→ℕ n)) ∣ (gcd m (ℕ₊₁→ℕ n))
        f₁ d (b₁ , q₁) (b₂ , q₂) = gr (d * gcd m (ℕ₊₁→ℕ n)) ((∣ b₁ , lem b₁ q₁ p₁ ∣) ,
                                                             (∣ b₂ , lem b₂ q₂ p₂ ∣))

        f₂ : ∀ d → (d * gcd m (ℕ₊₁→ℕ n)) ∣ (gcd m (ℕ₊₁→ℕ n)) → d ∣ 1
        f₂ d div = ∣-cancelʳ k (∣-trans (subst (λ x → (d * x) ∣ x) p div)
                                        (∣-refl (sym (*-identityˡ (suc k)))))
          where k = m∣sn→z<m d∣sn .fst
                p : gcd m (ℕ₊₁→ℕ n) ≡ suc k
                p = sym (+-comm 1 k ∙ m∣sn→z<m d∣sn .snd)

        gr' : (d : ℕ) → isCD c₁ (suc c₂) d → d ∣ 1
        gr' d (d∣c₁ , d∣sc₂) = PropTrunc.rec isProp∣ (λ a →
                               PropTrunc.rec isProp∣ (λ b →
                                 f₂ d (f₁ d a b)) d∣sc₂) d∣c₁
