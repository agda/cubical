{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Data.Nat.Coprime where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Data.NatPlusOne

open import Cubical.HITs.PropositionalTruncation as PropTrunc

open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Nat.Divisibility
open import Cubical.Data.Nat.GCD

areCoprime : ℕ × ℕ → Type₀
areCoprime (m , n) = isGCD m n 1

-- Any pair (m , n) can be converted to a coprime pair (m' , n') s.t.
--  m' ∣ m, n' ∣ n if and only if one of m or n is nonzero

module _ ((m , n) : ℕ × ℕ₊₁) where
  private
    d    = gcd m (ℕ₊₁→ℕ n)
    d∣m  = gcdIsGCD m (ℕ₊₁→ℕ n) .fst .fst
    d∣sn = gcdIsGCD m (ℕ₊₁→ℕ n) .fst .snd
    gr   = gcdIsGCD m (ℕ₊₁→ℕ n) .snd

    c₁ : ℕ
    p₁ : c₁ * d ≡ m
    c₁ = ∣-untrunc d∣m .fst; p₁ = ∣-untrunc d∣m .snd

    c₂ : ℕ₊₁
    p₂ : (ℕ₊₁→ℕ c₂) * d ≡ (ℕ₊₁→ℕ n)
    c₂ = 1+ (∣s-untrunc d∣sn .fst); p₂ = ∣s-untrunc d∣sn .snd

  toCoprime : ℕ × ℕ₊₁ → ℕ × ℕ₊₁
  toCoprime (m , n) = (c₁ , c₂)

  private
    lem : ∀ a {b c d e} → a * b ≡ c → c * d ≡ e → a * (b * d) ≡ e
    lem a p q = *-assoc a _ _ ∙ cong (_* _) p ∙ q

    gr' : ∀ d' → prediv d' c₁ → prediv d' (ℕ₊₁→ℕ c₂) → (d' * d) ∣ d
    gr' d' (b₁ , q₁) (b₂ , q₂) = gr (d' * d) ((∣ b₁ , lem b₁ q₁ p₁ ∣) ,
                                              (∣ b₂ , lem b₂ q₂ p₂ ∣))

    -- this only works because d > 0 (<=> m > 0 or n > 0)
    d-cancelʳ : ∀ d' → (d' * d) ∣ d → d' ∣ 1
    d-cancelʳ d' div = ∣-cancelʳ d-1 (∣-trans (subst (λ x → (d' * x) ∣ x) p div)
                                              (∣-refl (sym (*-identityˡ _))))
      where d-1 = m∣sn→z<m d∣sn .fst
            p : d ≡ suc d-1
            p = sym (+-comm 1 d-1 ∙ m∣sn→z<m d∣sn .snd)

  toCoprimeAreCoprime : areCoprime (c₁ , ℕ₊₁→ℕ c₂)
  fst toCoprimeAreCoprime = ∣-oneˡ c₁ , ∣-oneˡ (ℕ₊₁→ℕ c₂)
  snd toCoprimeAreCoprime d' (d'∣c₁ , d'∣sc₂) = PropTrunc.rec isProp∣ (λ a →
                                                PropTrunc.rec isProp∣ (λ b →
                                                 d-cancelʳ d' (gr' d' a b)) d'∣sc₂) d'∣c₁

  toCoprime∣ : (c₁ ∣ m) × (ℕ₊₁→ℕ c₂ ∣ ℕ₊₁→ℕ n)
  toCoprime∣ = ∣ d , *-comm d c₁ ∙ p₁ ∣ , ∣ d , *-comm d (ℕ₊₁→ℕ c₂) ∙ p₂ ∣
