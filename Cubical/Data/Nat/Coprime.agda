{-# OPTIONS --safe #-}
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

module ToCoprime ((m , n) : ℕ × ℕ₊₁) where
  d   = gcd m (ℕ₊₁→ℕ n)
  d∣m = gcdIsGCD m (ℕ₊₁→ℕ n) .fst .fst
  d∣n = gcdIsGCD m (ℕ₊₁→ℕ n) .fst .snd
  gr  = gcdIsGCD m (ℕ₊₁→ℕ n) .snd

  c₁ : ℕ
  p₁ : c₁ · d ≡ m
  c₁ = ∣-untrunc d∣m .fst; p₁ = ∣-untrunc d∣m .snd

  c₂ : ℕ₊₁
  p₂ : (ℕ₊₁→ℕ c₂) · d ≡ (ℕ₊₁→ℕ n)
  c₂ = 1+ (∣s-untrunc d∣n .fst); p₂ = ∣s-untrunc d∣n .snd

  toCoprime : ℕ × ℕ₊₁
  toCoprime = (c₁ , c₂)

  private
    lem : ∀ a {b c d e} → a · b ≡ c → c · d ≡ e → a · (b · d) ≡ e
    lem a p q = ·-assoc a _ _ ∙ cong (_· _) p ∙ q

    gr' : ∀ d' → prediv d' c₁ → prediv d' (ℕ₊₁→ℕ c₂) → (d' · d) ∣ d
    gr' d' (b₁ , q₁) (b₂ , q₂) = gr (d' · d) ((∣ b₁ , lem b₁ q₁ p₁ ∣) ,
                                              (∣ b₂ , lem b₂ q₂ p₂ ∣))

  d-1 = m∣sn→z<m d∣n .fst
  q : d ≡ suc d-1
  q = sym (+-comm 1 d-1 ∙ m∣sn→z<m d∣n .snd)

  private
    -- this only works because d > 0 (<=> m > 0 or n > 0)
    d-cancelʳ : ∀ d' → (d' · d) ∣ d → d' ∣ 1
    d-cancelʳ d' div = ∣-cancelʳ d-1 (∣-trans (subst (λ x → (d' · x) ∣ x) q div)
                                              (∣-refl (sym (·-identityˡ _))))

  toCoprimeAreCoprime : areCoprime (c₁ , ℕ₊₁→ℕ c₂)
  fst toCoprimeAreCoprime = ∣-oneˡ c₁ , ∣-oneˡ (ℕ₊₁→ℕ c₂)
  snd toCoprimeAreCoprime d' (d'∣c₁ , d'∣c₂) = PropTrunc.rec isProp∣ (λ a →
                                               PropTrunc.rec isProp∣ (λ b →
                                                d-cancelʳ d' (gr' d' a b)) d'∣c₂) d'∣c₁

  toCoprime∣ : (c₁ ∣ m) × (ℕ₊₁→ℕ c₂ ∣ ℕ₊₁→ℕ n)
  toCoprime∣ = ∣ d , ·-comm d c₁ ∙ p₁ ∣ , ∣ d , ·-comm d (ℕ₊₁→ℕ c₂) ∙ p₂ ∣

  toCoprime-idem : areCoprime (m , ℕ₊₁→ℕ n) → (c₁ , c₂) ≡ (m , n)
  toCoprime-idem cp i = q₁ i , ℕ₊₁→ℕ-inj q₂ i
    where q₁ = sym (·-identityʳ c₁) ∙ cong (c₁ ·_) (sym (isGCD→gcd≡ cp)) ∙ p₁
          q₂ = sym (·-identityʳ (ℕ₊₁→ℕ c₂)) ∙ cong (ℕ₊₁→ℕ c₂ ·_) (sym (isGCD→gcd≡ cp)) ∙ p₂

open ToCoprime using (toCoprime; toCoprimeAreCoprime; toCoprime∣; toCoprime-idem) public


toCoprime-cancelʳ : ∀ ((m , n) : ℕ × ℕ₊₁) k
                    → toCoprime (m · ℕ₊₁→ℕ k , n ·₊₁ k) ≡ toCoprime (m , n)
toCoprime-cancelʳ (m , n) (1+ k) i =
  inj-·sm {c₁'} {d-1} {c₁} r₁ i , ℕ₊₁→ℕ-inj (inj-·sm {ℕ₊₁→ℕ c₂'} {d-1} {ℕ₊₁→ℕ c₂} r₂) i
  where open ToCoprime (m , n)
        open ToCoprime (m · suc k , n ·₊₁ (1+ k)) using ()
          renaming (c₁ to c₁'; p₁ to p₁'; c₂ to c₂'; p₂ to p₂')

        q₁ : c₁' · d · suc k ≡ m · suc k
        q₁ =   sym (·-assoc c₁' (ToCoprime.d (m , n)) (suc k))
             ∙ cong (c₁' ·_) (sym (gcd-factorʳ m (ℕ₊₁→ℕ n) (suc k)))
             ∙ p₁'
        q₂ : ℕ₊₁→ℕ c₂' · (ToCoprime.d (m , n)) · suc k ≡ ℕ₊₁→ℕ n · suc k
        q₂ =   sym (·-assoc (ℕ₊₁→ℕ c₂') (ToCoprime.d (m , n)) (suc k))
             ∙ cong (ℕ₊₁→ℕ c₂' ·_) (sym (gcd-factorʳ m (ℕ₊₁→ℕ n) (suc k)))
             ∙ p₂'

        r₁ : c₁' · suc d-1 ≡ c₁ · suc d-1
        r₁ = subst (λ z → c₁' · z ≡ c₁ · z) q (inj-·sm q₁ ∙ sym p₁)
        r₂ : ℕ₊₁→ℕ c₂' · suc d-1 ≡ ℕ₊₁→ℕ c₂ · suc d-1
        r₂ = subst (λ z → ℕ₊₁→ℕ c₂' · z ≡ ℕ₊₁→ℕ c₂ · z) q (inj-·sm q₂ ∙ sym p₂)
