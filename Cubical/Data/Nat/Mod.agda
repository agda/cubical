{-# OPTIONS --cubical #-}
module Cubical.Data.Nat.Mod where

open import Agda.Builtin.Nat using () renaming (
  div-helper to hdiv ;
  mod-helper to hmod)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma

open import Cubical.Relation.Nullary

open import Cubical.Reflection.RecordEquiv
open import Cubical.Tactics.NatSolver

record QuotRemℕ (m n : ℕ) : Type where
  no-eta-equality
  constructor quotrem
  field
    div : ℕ
    rem : ℕ
    quotEq : rem + (suc n) · div ≡ m
    remIneq : rem < suc n

unquoteDecl QuotRemIsoΣ = declareRecordIsoΣ QuotRemIsoΣ (quote QuotRemℕ)

isPropQuotRemℕ : ∀ m n → isProp (QuotRemℕ m n)
isPropQuotRemℕ m n = isOfHLevelRetractFromIso 1 QuotRemIsoΣ
  λ (q₁ , r₁ , eq₁ , rem<₁) (q₂ , r₂ , eq₂ , rem<₂) →
  cong (Iso.fun Σ-assoc-Iso)
       (Σ≡Prop (λ (q , r) → isProp× (isSetℕ (r + (suc n) · q) m) isProp≤)
               (ΣPathP (proof q₁ r₁ eq₁ rem<₁ q₂ r₂ eq₂ rem<₂)))
  where
    open <-Reasoning

    lemma : ∀ (q  r  : ℕ) → (p  : r  + (suc n) · q  ≡ m) → (rem< : r < suc n)
            → (q' r' : ℕ) → (p' : r' + (suc n) · q' ≡ m)
            → ¬ (q < q')
    lemma q r p rem< q' r' p' q<q' = ¬m<m (
      m                   ≡<⟨ sym p ⟩
      r       + suc n · q <≤⟨ <-+k rem< ⟩
      (suc n) + suc n · q ≡≤⟨ cong (suc n +_) (·-comm (suc n) q) ⟩
      (suc n) + q · suc n ≡≤⟨ refl ⟩
      (suc q)     · suc n  ≤⟨ ≤-·k q<q' ⟩
      q'          · suc n ≤≡⟨ ≤SumRight ⟩
      r' + q' · suc n      ≡⟨ cong (r' +_) (·-comm q' (suc n)) ⟩
      r' + suc n · q'      ≡⟨ p' ⟩
      m                    ∎)

    proof : ∀ (q₁ r₁ : ℕ) → (eq₁ : r₁ + (suc n) · q₁ ≡ m) → (rem<₁ : r₁ < suc n)
            → (q₂ r₂ : ℕ) → (eq₂ : r₂ + (suc n) · q₂ ≡ m) → (rem<₂ : r₂ < suc n)
            → (q₁ ≡ q₂) × (r₁ ≡ r₂)
    proof q₁ r₁ eq₁ rem<₁ q₂ r₂ eq₂ rem<₂ = fst≡ , snd≡
      where
        fst≡ : q₁ ≡ q₂
        fst≡ with q₁ ≟ q₂
        ... | lt q₁<q₂ = ⊥.rec (lemma q₁ r₁ eq₁ rem<₁ q₂ r₂ eq₂ q₁<q₂)
        ... | eq q₁≡q₂ = q₁≡q₂
        ... | gt q₁>q₂ = ⊥.rec (lemma q₂ r₂ eq₂ rem<₂ q₁ r₁ eq₁ q₁>q₂)

        snd≡ : r₁ ≡ r₂
        snd≡ =
          r₁                           ≡⟨ sym (+∸ r₁ (suc n · q₁)) ⟩
          r₁ + suc n · q₁ ∸ suc n · q₁ ≡⟨ cong (_∸ suc n · q₁) eq₁ ⟩
          m ∸ suc n · q₁               ≡⟨ cong (λ t → m ∸ suc n · t) fst≡ ⟩
          m ∸ suc n · q₂               ≡⟨ sym (cong (_∸ suc n · q₂) eq₂) ⟩
          r₂ + suc n · q₂ ∸ suc n · q₂ ≡⟨ +∸ r₂ (suc n · q₂) ⟩
          r₂                           ∎

-- helper lemmas to prove the properties
private
  div-mod-lemma : ∀ accᵐ accᵈ d n →
    accᵐ + accᵈ · suc (accᵐ + n) + d
    ≡
    hmod accᵐ (accᵐ + n) d n + hdiv accᵈ (accᵐ + n) d n · suc (accᵐ + n)
  div-mod-lemma accᵐ accᵈ zero    n       = +-zero _
  div-mod-lemma accᵐ accᵈ (suc d) zero    =
    (accᵐ + accᵈ · suc (accᵐ + zero)) + suc d          ≡⟨ step0 ⟩
    suc (accᵐ + accᵈ · suc (accᵐ + zero)) + d          ≡⟨⟩
    ((suc accᵐ) + accᵈ · suc (accᵐ + zero)) + d        ≡⟨ step1 ⟩
    ((suc accᵐ) + accᵈ · (suc accᵐ)) + d               ≡⟨⟩
    0 + (suc accᵈ) · suc (0 + accᵐ) + d                ≡⟨ step2 ⟩
    hmod 0 (0 + accᵐ) d accᵐ +
    hdiv (suc accᵈ) (0 + accᵐ) d accᵐ · suc (0 + accᵐ) ≡⟨⟩
    hmod 0 accᵐ d accᵐ +
    hdiv (suc accᵈ) accᵐ d accᵐ · suc accᵐ             ≡⟨⟩
    hmod accᵐ accᵐ (suc d) 0 +
    hdiv accᵈ accᵐ (suc d) 0 · suc accᵐ                ≡⟨ step3 ⟩
    hmod accᵐ (accᵐ + 0) (suc d) 0 +
    hdiv accᵈ (accᵐ + 0) (suc d) 0 · suc (accᵐ + 0)    ∎
      where
        step0 = +-suc _ d
        step1 = λ i → ((suc accᵐ) + accᵈ · suc (+-zero accᵐ i)) + d
        step2 = div-mod-lemma 0 (suc accᵈ) d accᵐ
        step3 = cong (λ p → hmod accᵐ p (suc d) 0 + hdiv accᵈ p (suc d) 0 · suc p)
                     (sym (+-zero accᵐ))
  div-mod-lemma accᵐ accᵈ (suc d) (suc n) =
    (accᵐ + accᵈ · suc (accᵐ + suc n)) + suc d          ≡⟨ step0 ⟩
    (suc (accᵐ + accᵈ · suc (accᵐ + suc n))) + d        ≡⟨⟩
    ((suc accᵐ) + accᵈ · suc (accᵐ + suc n)) + d        ≡⟨ step1 ⟩
    ((suc accᵐ) + accᵈ · suc ((suc accᵐ) + n)) + d      ≡⟨ step2 ⟩
    hmod (suc accᵐ) (suc accᵐ + n) d n +
    hdiv accᵈ (suc accᵐ + n) d n · suc (suc accᵐ + n)   ≡⟨ step3 ⟩
    hmod (suc accᵐ) (accᵐ + suc n) d n +
    hdiv accᵈ (accᵐ + suc n) d n · suc (accᵐ + suc n)   ≡⟨⟩
    hmod accᵐ (accᵐ + suc n) (suc d) (suc n) +
    hdiv accᵈ (accᵐ + suc n) (suc d) (suc n) · suc (accᵐ + suc n) ∎
      where
        step0 = +-suc _ d
        step1 = λ i → ((suc accᵐ) + accᵈ · suc (+-suc accᵐ n i)) + d
        step2 = div-mod-lemma (suc accᵐ) accᵈ d n
        step3 = cong (λ p → hmod (suc accᵐ) p d n + hdiv accᵈ p d n · suc p)
                     (sym (+-suc accᵐ n))

  mod-lemma-≤ : ∀ acc d n → hmod acc (acc + n) d n ≤ acc + n
  mod-lemma-≤ acc zero    n       = ≤SumLeft
  mod-lemma-≤ acc (suc d) zero    = mod-lemma-≤ 0 d (acc + 0)
  mod-lemma-≤ acc (suc d) (suc n) =
    hmod acc (acc + suc n) (suc d) (suc n) ≡≤⟨ step0 ⟩
    hmod acc (suc acc + n) (suc d) (suc n) ≡≤⟨ refl ⟩
    hmod (suc acc) (suc acc + n) d n       ≤≡⟨ step1 ⟩
    suc acc + n                            ≡⟨ step2 ⟩
    acc + (suc n)                          ∎
    where
      open <-Reasoning
      step0 = λ i → hmod acc (+-suc acc n i) (suc d) (suc n)
      step1 = mod-lemma-≤ (suc acc) d n
      step2 = sym (+-suc acc n)

  hmod-skipTo0 : ∀ acc n a b → hmod acc n (b + a) a ≡ hmod (a + acc) n b 0
  hmod-skipTo0 acc n zero    b = cong (λ v → hmod acc n v 0) (+-zero b)
  hmod-skipTo0 acc n (suc a) b =
    hmod acc n (b + suc a) (suc a) ≡[ i ]⟨ hmod acc n (+-suc b a i) (suc a) ⟩
    hmod acc n (suc b + a) (suc a) ≡⟨⟩
    hmod (suc acc) n (b + a) a     ≡⟨ hmod-skipTo0 (suc acc) n a b ⟩
    hmod (a + suc acc) n b 0       ≡⟨ cong (λ v → hmod v n b 0) (+-suc a acc) ⟩
    hmod (suc a + acc) n b 0       ∎

  hmod<-id : ∀ acc n a b → hmod acc n a (a + b) ≡ acc + a
  hmod<-id acc n zero    b = sym (+-zero acc)
  hmod<-id acc n (suc a) b =
    hmod acc n (suc a) (suc a + b) ≡⟨⟩
    hmod (suc acc) n a (a + b)     ≡⟨ hmod<-id (suc acc) n a b ⟩
    suc acc + a                    ≡⟨ sym (+-suc acc a) ⟩
    acc + suc a                    ∎

  hmod-idem : ∀ acc a n
              → hmod 0 (acc + n) (hmod acc (acc + n) a n) (acc + n)
              ≡ hmod acc (acc + n) a n
  hmod-idem acc zero    n       = hmod<-id 0 (acc + n) acc n
  hmod-idem acc (suc a) zero    =
    hmod 0 (acc + 0) (hmod acc (acc + 0) (suc a) 0) (acc + 0) ≡⟨ step0 ⟩
    hmod 0 (0 + acc) (hmod 0 (0 + acc) a acc) (0 + acc)       ≡⟨ step1 ⟩
    hmod 0 (0 + acc) a acc                                    ≡⟨ step2 ⟩
    hmod acc (acc + zero) (suc a) zero                        ∎
      where
        step0 = cong (λ p → hmod 0 p (hmod acc p (suc a) 0) p) (+-zero acc)
        step1 = hmod-idem 0 a acc
        step2 = cong (λ p → hmod acc p (suc a) 0) (sym (+-zero acc))
  hmod-idem acc (suc a) (suc n) =
    hmod 0 (acc + suc n) (
      hmod acc (acc + suc n) (suc a) (suc n)
    ) (acc + suc n)                           ≡⟨ step0 ⟩
    hmod 0 (suc acc + n) (
      hmod (suc acc) (suc acc + n) a n
    ) (suc acc + n)                           ≡⟨ step1 ⟩
    hmod (suc acc) (suc acc + n) a n          ≡⟨ step2 ⟩
    hmod acc (acc + suc n) (suc a) (suc n)    ∎
      where
        step0 = cong (λ p → hmod 0 p (hmod acc p (suc a) (suc n)) p) (+-suc acc n)
        step1 = hmod-idem (suc acc) a n
        step2 = cong (λ p → hmod (suc acc) p a n) (sym (+-suc acc n))

  a+n[hmod]n≡a[hmod]n : ∀ acc a n
                        → hmod acc (acc + n) (acc + a + suc n) n
                        ≡ hmod acc (acc + n) a n
  a+n[hmod]n≡a[hmod]n acc zero n =
    hmod acc       (acc + n) (acc + 0 + suc n) n         ≡⟨ step0 ⟩
    hmod acc       (acc + n) (acc + suc n)     n         ≡⟨ step1 ⟩
    hmod acc       (acc + n) (suc acc + n)     n         ≡⟨ step2 ⟩
    hmod (acc + n) (acc + n) (suc acc)         0         ≡⟨⟩
    hmod 0         (acc + n) acc               (acc + n) ≡⟨ step3 ⟩
    acc                                                  ∎
      where
        step0 = cong (λ p → hmod acc (acc + n) (p + suc n) n) (+-zero acc)
        step1 = cong (λ p → hmod acc (acc + n) p n) (+-suc acc n)
        step2 = hmod-skipTo0 acc (acc + n) n (suc acc)
        step3 = hmod<-id 0 (acc + n) acc n
  a+n[hmod]n≡a[hmod]n acc (suc a) zero =
    hmod acc (acc + 0) (acc + suc a + 1)   0   ≡⟨ step0 ⟩
    hmod acc acc       (1 + (acc + suc a)) 0   ≡⟨⟩
    hmod 0   acc       (acc + suc a)       acc ≡⟨ step1 ⟩
    hmod 0   acc       (suc a + acc)       acc ≡⟨ step2 ⟩
    hmod 0   acc       (a + suc acc)       acc ≡⟨ step3 ⟩
    hmod 0   acc        a                  acc ≡⟨⟩
    hmod acc acc       (suc a)             0   ≡⟨ step4 ⟩
    hmod acc (acc + 0) (suc a)             0   ∎
      where
        step0 = cong₂ (λ p q → hmod acc p q 0) (+-zero acc) (+-comm (acc + suc a) 1)
        step1 = cong (λ p → hmod 0 acc p acc) (+-comm acc (suc a))
        step2 = cong (λ p → hmod 0 acc p acc) (sym (+-suc a acc))
        step3 = a+n[hmod]n≡a[hmod]n 0 a acc
        step4 = cong (λ p → hmod acc p (suc a) 0) (sym (+-zero acc))
  a+n[hmod]n≡a[hmod]n acc (suc a) (suc n) =
    hmod acc (acc + suc n) (acc + suc a + suc (suc n)) (suc n) ≡⟨ step0 ⟩
    mod₁ (acc + suc a + suc (suc n))     (suc n)               ≡⟨ step1 ⟩
    mod₁ (suc (acc + a) + suc (suc n))   (suc n)               ≡⟨⟩
    mod₂ (acc + a + (2 + n))             n                     ≡⟨ step2 ⟩
    mod₂ (acc + a + 1 + suc n)           n                     ≡⟨ step3 ⟩
    mod₂ (1 + (acc + a) + suc n)         n                     ≡⟨ step4 ⟩
    hmod (suc acc) (suc acc + n) a       n                     ≡⟨⟩
    hmod acc       (suc acc + n) (suc a) (suc n)               ≡⟨ step5 ⟩
    hmod acc       (acc + suc n) (suc a) (suc n)               ∎
      where
        mod₁  = hmod acc       (suc acc + n)
        mod₂  = hmod (suc acc) (suc acc + n)
        step0 = cong (λ p → hmod acc p (acc + suc a + suc (suc n)) (suc n))
                     (+-suc acc n)
        step1 = cong (λ v → mod₁ (v + suc (suc n)) (suc n)) (+-suc acc a)
        step2 = cong (λ p → mod₂ p n) (+-assoc (acc + a) 1 (suc n))
        step3 = cong (λ p → mod₂ p n) (cong (_+ suc n) (+-comm (acc + a) 1))
        step4 = a+n[hmod]n≡a[hmod]n (suc acc) a n
        step5 = cong (λ p → hmod acc p (suc a) (suc n)) (sym (+-suc acc n))

  a≤n⇒a[hmod]n≡a : ∀ acc n a b → hmod acc n a (a + b) ≡ acc + a
  a≤n⇒a[hmod]n≡a acc n zero    b = sym (+-zero acc)
  a≤n⇒a[hmod]n≡a acc n (suc a) b =
    hmod (suc acc) n a (a + b) ≡⟨ a≤n⇒a[hmod]n≡a (suc acc) n a b ⟩
    suc acc + a                ≡⟨ sym (+-suc acc a) ⟩
    acc + suc a                ∎

-- Defining x mod 0 to be 0. This way all the theorems below are true
-- for n : ℕ instead of n : ℕ₊₁.

_mod_ : ℕ → ℕ → ℕ
x mod zero  = 0
x mod suc n = hmod 0 n x n

mod< : ∀ n x → x mod suc n < suc n
mod< n x = suc-≤-suc (mod-lemma-≤ 0 x n)

-- remainder and quotient after division by n
-- Again, allowing for 0-division to get nicer syntax
remainder_/_ : (x n : ℕ) → ℕ
remainder x / zero  = x
remainder x / suc n = x mod suc n

quotient_/_ : (x n : ℕ) → ℕ
quotient x / zero  = 0
quotient x / suc n = hdiv 0 n x n

≡remainder+quotient : (n x : ℕ)
  → (remainder x / n) + n · (quotient x / n) ≡ x
≡remainder+quotient zero    x = +-zero x
≡remainder+quotient (suc n) x =
  remainder x / suc n + suc n · (quotient x / suc n)    ≡⟨ step0 ⟩
  remainder x / suc n + quotient x / suc n · suc n      ≡⟨⟩
  hmod 0 n x n + hdiv 0 n x n · suc n                   ≡⟨⟩
  hmod 0 (0 + n) x n + hdiv 0 (0 + n) x n · suc (0 + n) ≡⟨ step1 ⟩
  x                                                     ∎
    where
      step0 = cong (remainder x / suc n +_) (·-comm (suc n) (quotient x / suc n))
      step1 = sym (div-mod-lemma 0 0 x n)

mod-rUnit : (n x : ℕ) → x mod n ≡ ((x + n) mod n)
mod-rUnit zero    x = refl
mod-rUnit (suc n) x = sym (a+n[hmod]n≡a[hmod]n 0 x n)

mod-rUnitMul : (n x k : ℕ) → x mod n ≡ ((x + n · k) mod n)
mod-rUnitMul zero      x k    = refl
mod-rUnitMul d@(suc n) x zero =
   x          mod d ≡⟨ cong (_mod d) (sym (+-zero x)) ⟩
  (x + 0)     mod d ≡⟨ cong (λ p → (x + p) mod d) (0≡m·0 d) ⟩
  (x + d · 0) mod d ∎
mod-rUnitMul d@(suc n) x (suc k) =
   x                mod d ≡⟨ mod-rUnit d x ⟩
  (x + d)           mod d ≡⟨ mod-rUnitMul d (x + d) k ⟩
  (x + d + d · k)   mod d ≡⟨ cong (_mod d) (sym (+-assoc x d (d · k))) ⟩
  (x + (d + d · k)) mod d ≡⟨ cong (λ p → (x + p) mod d) (sym (·-suc d k)) ⟩
  (x + d · suc k)   mod d ∎

mod-lUnit : (n x : ℕ) → x mod n ≡ ((n + x) mod n)
mod-lUnit zero    _ = refl
mod-lUnit (suc n) x =
  x mod suc n           ≡⟨ mod-rUnit _ x ⟩
  (x + suc n) mod suc n ≡⟨ cong (_mod (suc n) ) (+-comm x (suc n)) ⟩
  (suc n + x) mod suc n ∎

mod+mod≡mod : (n x y : ℕ)
  → (x + y) mod n ≡ (((x mod n) + (y mod n)) mod n)
mod+mod≡mod zero    _ _ = refl
mod+mod≡mod d@(suc n) x y =
  (x                      + y       ) mod d ≡⟨ step0 ⟩
  (x mod d +  d · (x / d) + y       ) mod d ≡⟨ step1 ⟩
  (x mod d + (d · (x / d) + y)      ) mod d ≡⟨ step2 ⟩
  (x mod d + (y + d · (x / d))      ) mod d ≡⟨ step3 ⟩
  (x mod d +  y + d · (x / d)       ) mod d ≡⟨ step4 ⟩
  (x mod d +  y                     ) mod d ≡⟨ step5 ⟩
  (x mod d + (y mod d + d · (y / d))) mod d ≡⟨ step6 ⟩
  (x mod d +  y mod d + d · (y / d) ) mod d ≡⟨ step7 ⟩
  (x mod d +  y mod d               ) mod d ∎
    where
      _/_ = quotient_/_
      step0 = cong (_mod d) (cong (_+ y) (sym (≡remainder+quotient d x)))
      step1 = cong (_mod d) (sym (+-assoc (x mod d) (d · (x / d)) y))
      step2 = cong (_mod d) (cong ((x mod d) +_) (+-comm (d · (x / d)) y))
      step3 = cong (_mod d) (+-assoc (x mod d) y (d · (x / d)))
      step4 = sym (mod-rUnitMul d (x mod d + y) (x / d))
      step5 = cong (λ p → (x mod d + p) mod d) (sym (≡remainder+quotient d y))
      step6 = cong (_mod d) (+-assoc (x mod d) (y mod d) (d · (y / d)))
      step7 = sym (mod-rUnitMul d ((x mod d) + (y mod d)) (y / d))

mod-idempotent : {n : ℕ} (x : ℕ) → (x mod n) mod n ≡ x mod n
mod-idempotent {n = zero}  _ = refl
mod-idempotent {n = suc n} x = hmod-idem 0 x n

zero-charac : (n : ℕ) → n mod n ≡ 0
zero-charac zero    = refl
zero-charac (suc n) = hmod-skipTo0 0 n n 1

zero-charac-gen : (n x : ℕ) → ((x · n) mod n) ≡ 0
zero-charac-gen zero    x       = refl
zero-charac-gen (suc n) zero    = refl
zero-charac-gen (suc n) (suc x) =
  (suc n + x · suc n) mod suc n ≡⟨ sym (mod-lUnit (suc n) (x · (suc n))) ⟩
  (x · suc n) mod suc n         ≡⟨ zero-charac-gen (suc n) x ⟩
  0                             ∎

mod·mod≡mod : (n x y : ℕ)
  → (x · y) mod n ≡ (((x mod n) · (y mod n)) mod n)
mod·mod≡mod zero      _ _ = refl
mod·mod≡mod d@(suc n) x y =
  (x · y                                    ) mod d ≡⟨ step0 ⟩
  ((x′ + d · k) · (y′ + d · j)              ) mod d ≡⟨ step1 ⟩
  (x′ · y′ + d · (x′ · j + (y′ + j · d) · k)) mod d ≡⟨ step2 ⟩
  (x′ · y′                                  ) mod d ≡⟨⟩
  ((x mod d) · (y mod d)                    ) mod d ∎
  where
    _/_ = quotient_/_
    x′ = x mod d
    y′ = y mod d
    k  = x / d
    j  = y / d
    lemma : ∀ d x′ y′ j k
            → (x′ + d · k) · (y′ + d · j)
            ≡  x′ · y′ + d · (x′ · j + (y′ + j · d) · k)
    lemma _ _ _ _ _ = solveℕ!

    step0 = cong₂ (λ p q → (p · q) mod d)
              (sym (≡remainder+quotient d x)) (sym (≡remainder+quotient d y))
    step1 = cong (_mod d) (lemma d x′ y′ j k)
    step2 = sym (mod-rUnitMul d (x′ · y′) ((x mod d) · j + (y′ + j · d) · k))

mod-rCancel : (n x y : ℕ) → (x + y) mod n ≡ (x + y mod n) mod n
mod-rCancel zero      _ _ = refl
mod-rCancel d@(suc n) x y =
  (x +  y                     ) mod d ≡⟨ step0 ⟩
  (x + (y mod d + d · (y / d))) mod d ≡⟨ step1 ⟩
  (x +  y mod d + d · (y / d) ) mod d ≡⟨ step2 ⟩
  (x +  y mod d               ) mod d ∎
    where
      _/_ = quotient_/_
      step0 = cong (λ p → (x + p) mod d) (sym (≡remainder+quotient d y))
      step1 = cong (_mod d) (+-assoc x (y mod d) (d · (y / d)))
      step2 = sym (mod-rUnitMul d (x + y mod d) (y / d))

mod-lCancel : (n x y : ℕ) → (x + y) mod n ≡ (x mod n + y) mod n
mod-lCancel zero      _ _ = refl
mod-lCancel d@(suc n) x y =
  (x + y)       mod d ≡⟨ cong (_mod d) (+-comm x y) ⟩
  (y + x)       mod d ≡⟨ mod-rCancel d y x ⟩
  (y + x mod d) mod d ≡⟨ cong (_mod d) (+-comm y (x mod d)) ⟩
  (x mod d + y) mod d ∎

<→mod≡id : (m n : ℕ) → m < n → m mod n ≡ m
<→mod≡id m zero    m<0     = ⊥.rec (¬-<-zero m<0)
<→mod≡id m (suc n) (k , p) = cong (hmod 0 n m) (injSuc (sym p ∙ +-comm k (suc m)))
                           ∙ a≤n⇒a[hmod]n≡a 0 n m k

<→quotient≡0 : (m n : ℕ) → m < n → quotient m / n ≡ 0
<→quotient≡0 m zero    _    = refl
<→quotient≡0 m (suc n) m<sn = sym $ 0≡n·sm→0≡n $ sym $
  quotient m / suc n · suc n                                 ≡⟨ ·-comm _ (suc n) ⟩
  suc n · quotient m / suc n                                 ≡⟨ step0 ⟩
  suc n · quotient m / suc n + (m mod suc n) ∸ (m mod suc n) ≡⟨ step1 ⟩
  (m mod suc n) + suc n · quotient m / suc n ∸ (m mod suc n) ≡⟨ step2 ⟩
  m ∸ (m mod suc n)                                          ≡⟨ step3 ⟩
  m ∸ m                                                      ≡⟨ n∸n m ⟩
  0                                                          ∎
  where
    step0 = sym $ +∸ _ (m mod (suc n))
    step1 = cong (_∸ (m mod suc n)) (+-comm _ (m mod suc n))
    step2 = cong (_∸ (m mod suc n)) (≡remainder+quotient (suc n) m)
    step3 = cong (m ∸_) (<→mod≡id m (suc n) m<sn)

mod1≡0 : ∀ n → n mod 1 ≡ 0
mod1≡0 n with (n mod 1) ≟ 0
... | lt <0 = ⊥.rec (¬-<-zero <0)
... | eq ≡0 = ≡0
... | gt >0 = ⊥.rec (¬m<m (<≤-trans >0 (pred-≤-pred (mod< 0 n))))

-- Alternative definitions of quotient, mod and remainder

------ Preliminary definitions ------
modInd : (n : ℕ) → ℕ → ℕ
modInd n = +induction n (λ _ → ℕ) (λ x _ → x) λ _ x → x

modIndBase : (n m : ℕ) → m < suc n → modInd n m ≡ m
modIndBase n = +inductionBase n (λ _ → ℕ) (λ x _ → x) (λ _ x → x)

modIndStep : (n m : ℕ) → modInd n (suc n + m) ≡ modInd n m
modIndStep n = +inductionStep n (λ _ → ℕ) (λ x _ → x) (λ _ x → x)
-------------------------------------

_mod'_ : (x n : ℕ) → ℕ
x mod' zero = 0
x mod' (suc n) = modInd n x

mod'< : (n x : ℕ) → x mod' (suc n) < (suc n)
mod'< n =
  +induction n
    (λ x → x mod' (suc n) < suc n)
    (λ x base → fst base
               , (cong (λ x → fst base + suc x)
                       (modIndBase n x base)
                ∙ snd base))
     λ x ind → fst ind
              , cong (λ x → fst ind + suc x)
                     (modIndStep n x) ∙ snd ind

remainder'_/_ : (x n : ℕ) → ℕ
remainder' x / zero = x
remainder' x / suc n = x mod' (suc n)

quotient'_/_ : (x n : ℕ) → ℕ
quotient' x / zero = 0
quotient' x / suc n =
  +induction n (λ _ → ℕ) (λ _ _ → 0) (λ _ → suc) x

≡remainder'+quotient' : (n x : ℕ)
  → (remainder' x / n) + n · (quotient' x / n) ≡ x
≡remainder'+quotient' zero x = +-comm x 0
≡remainder'+quotient' (suc n) =
  +induction n
    (λ x → (remainder' x / (suc n)) + (suc n)
          · (quotient' x / (suc n)) ≡ x)
    (λ x base → cong₂ _+_ (modIndBase n x base)
                           (cong ((suc n) ·_)
                           (+inductionBase n _ _ _ x base))
              ∙∙ cong (x +_) (·-comm n 0)
              ∙∙ +-comm x 0)
     λ x ind → cong₂ _+_ (modIndStep n x)
                        (cong ((suc n) ·_) (+inductionStep n _ _ _ x))
          ∙∙ cong (modInd n x +_)
                  (·-suc (suc n) (+induction n _ _ _ x))
          ∙∙ cong (modInd n x +_)
                  (+-comm (suc n) ((suc n) · (+induction n _ _ _ x)))
          ∙∙ +-assoc (modInd n x) ((suc n) · +induction n _ _ _ x) (suc n)
          ∙∙ cong (_+ suc n) ind
           ∙ +-comm x (suc n)

-- Conversions between the two implementations:

quotRemℕ : ∀ m n → QuotRemℕ m n
quotRemℕ m n .QuotRemℕ.div     = quotient m / suc n
quotRemℕ m n .QuotRemℕ.rem     = remainder m / suc n
quotRemℕ m n .QuotRemℕ.quotEq  = ≡remainder+quotient (suc n) m
quotRemℕ m n .QuotRemℕ.remIneq = mod< n m

quotRemℕ' : ∀ m n → QuotRemℕ m n
quotRemℕ' m n .QuotRemℕ.div     = quotient' m / suc n
quotRemℕ' m n .QuotRemℕ.rem     = remainder' m / suc n
quotRemℕ' m n .QuotRemℕ.quotEq  = ≡remainder'+quotient' (suc n) m
quotRemℕ' m n .QuotRemℕ.remIneq = mod'< n m

quotient≡quotient' : ∀ m n → quotient m / n ≡ quotient' m / n
quotient≡quotient' m zero    = refl
quotient≡quotient' m (suc n) =
  cong (QuotRemℕ.div) (isPropQuotRemℕ m n (quotRemℕ m n) (quotRemℕ' m n))

remainder≡remainder' : ∀ m n → remainder m / n ≡ remainder' m / n
remainder≡remainder' m zero    = refl
remainder≡remainder' m (suc n) =
  cong (QuotRemℕ.rem) (isPropQuotRemℕ m n (quotRemℕ m n) (quotRemℕ' m n))

mod≡mod' : ∀ m n → m mod n ≡ m mod' n
mod≡mod' m zero    = refl
mod≡mod' m (suc n) = remainder≡remainder' m (suc n)

isContrQuotRemℕ : ∀ m n → isContr (QuotRemℕ m n)
isContrQuotRemℕ m n .fst = quotRemℕ m n
isContrQuotRemℕ m n .snd = isPropQuotRemℕ m n _

private
  test₀ : 100 mod 81 ≡ 19
  test₀ = refl

  test₁ : ((11 + (10 mod 3)) mod 3) ≡ 0
  test₁ = refl
