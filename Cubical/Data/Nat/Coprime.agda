module Cubical.Data.Nat.Coprime where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Empty as ⊥ using (⊥)

open import Cubical.HITs.PropositionalTruncation as PropTrunc

open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Nat.Divisibility
open import Cubical.Data.Nat.GCD

areCoprime : ℕ × ℕ → Type₀
areCoprime (m , n) = isGCD m n 1

zeroCoprime : {d-1 : ℕ} → (copr : areCoprime (0 , ℕ.suc d-1)) → d-1 ≡ 0
zeroCoprime {d-1} copr = injSuc (zeroGCD-unique (symGCD copr))

zeroCoprime' : {m : ℕ} → (copr : areCoprime (0 , m)) → m ≡ 1
zeroCoprime' {m} copr = zeroGCD-unique (symGCD copr)

isPropAreCoprime : (x : ℕ) (y : ℕ) → isProp (areCoprime (x , y))
isPropAreCoprime x y = isPropIsGCD

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
    gr' d' (b₁ , q₁) (b₂ , q₂) = gr (d' · d) ((∣ b₁ , lem b₁ q₁ p₁ ∣₁) ,
                                              (∣ b₂ , lem b₂ q₂ p₂ ∣₁))

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
  toCoprime∣ = ∣ d , ·-comm d c₁ ∙ p₁ ∣₁ , ∣ d , ·-comm d (ℕ₊₁→ℕ c₂) ∙ p₂ ∣₁

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


private
  lem₀ : ∀ i j m n → i · m ≡ j · m + n → (i ∸ j) · m ≡ n
  lem₀ i j m n eq₁ =
    (i ∸ j) · m            ≡⟨ ∸-distribʳ i j m ⟩
    (i · m) ∸ (j · m)      ≡⟨ cong (_∸ j · m) eq₁ ⟩
    (j · m + n) ∸ (j  · m)  ≡⟨ cong (_∸ j · m) (+-comm (j · m) n) ⟩
    (n + j · m) ∸ (j · m)  ≡⟨ +∸ n (j · m) ⟩
    n              ∎

  ·-on-left : ∀ a b c {d} → a · b ≡ d → a · (b · c) ≡ d · c
  ·-on-left a b c {d} eq₁ =
    a · (b · c)  ≡⟨ ·-assoc a b c ⟩
    a · b · c    ≡⟨ cong (_· c) eq₁ ⟩
    d · c       ∎

  ·-on-right : ∀ a b c {d} → b · c ≡ d → a · b · c ≡ a · d
  ·-on-right a b c {d} eq₁ =
    a · b · c   ≡⟨ sym (·-assoc a b c) ⟩
    a · (b · c) ≡⟨ cong (a ·_) eq₁ ⟩
    a · d       ∎

  -- lem₈ in Agda Standard Library
  lem : ∀ {i j k q} x y →
         1 + y · j ≡ x · i → j · k ≡ q · i →
         (x · k ∸ y · q) · i ≡ k
  lem {i}{j}{k}{q} x y eq1 eq2 = lem₀ (x · k) (y · q) i k lemma
    where
      lemma : x · k · i ≡ y · q · i + k
      lemma =
        x · k · i        ≡⟨ ·-on-right x k i ( ·-comm k i) ⟩
        x · (i · k)      ≡⟨ ·-on-left x i k (sym eq1) ⟩
        (1 + y · j) · k  ≡⟨ +-comm k _ ⟩
        (y · j) · k + k  ≡⟨ cong (_+ k) (sym (·-assoc y j k)) ⟩
        y · (j · k) + k   ≡⟨ cong (λ n → y · n + k) eq2 ⟩
        y · (q · i) + k   ≡⟨ cong (λ n → n + k) (·-assoc y q i) ⟩
        y · q · i  + k   ∎

  -- lem₉ in Agda Standard Library
  lem' : ∀ {i j k q} x y →
         1 + x · i ≡ y · j → j · k ≡ q · i →
         (y · q ∸ x · k) · i ≡ k
  lem' {i}{j}{k}{q} x y eq1 eq2 = lem₀ (y · q) (x · k) i k lemma
    where
      lemmaHlp : ∀ a b c → a · b · c ≡ b · c · a
      lemmaHlp a b c =
        a · b · c   ≡⟨ sym (·-assoc a b c) ⟩
        a · (b · c) ≡⟨ ·-comm a _ ⟩
        b · c · a   ∎
      lemma : y · q · i ≡ x · k · i + k
      lemma =
        y · q · i        ≡⟨ lemmaHlp y q i ⟩
        q · i · y        ≡⟨ cong (λ n → n · y) (sym eq2) ⟩
        j · k · y        ≡⟨ sym (lemmaHlp y j k) ⟩
        y · j · k        ≡⟨ cong (λ n → n · k) (sym eq1) ⟩
        (1 + x · i) · k  ≡⟨ +-comm k _ ⟩
        x · i · k + k    ≡⟨ cong (λ u -> u + k) ( ·-on-right x i k (·-comm i k)) ⟩
        x · (k · i) + k  ≡⟨ cong (λ u -> u + k) (·-assoc x k i) ⟩
        x · k · i + k  ∎

coprimeDivides∣' : ∀ {m n o} → areCoprime (m , n) → m ∣' (n · o) → m ∣' o
coprimeDivides∣' m@{zero} {zero} {o} c mno =
  ⊥.elim {ℓ-zero}{λ x → m ∣' o} (znots (zeroGCD-unique c))
coprimeDivides∣' m@{zero} {suc n} {o} c mno =
  sym (fst (m+n≡0→m≡0×n≡0 {o}{n · o} (sym mno)))
coprimeDivides∣' {suc m} {zero} {zero} c (k , mno') = 0 , refl
coprimeDivides∣' {suc zero} {zero} {suc o} c _ =
  (suc o) , cong suc (·-identityʳ o)
coprimeDivides∣' {suc (suc m)} {zero} {suc o} c _ =
  let m≡0 = injSuc (zeroGCD-unique c) in ⊥.elim {ℓ-zero}
    {λ x → Σ-syntax ℕ (λ c₁ → c₁ · suc (suc m) ≡ suc o)}
    (snotz m≡0)
coprimeDivides∣' m@{suc m'} n@{suc n'} {o} c (q , eq') with Bézout.identity c
... | Bézout.+- x y eq₁ =
  (x · o) ∸ (y · q) , lem {m}{n}{o}{q} x y eq₁ (sym eq')
... | Bézout.-+ x y eq₁ =
  (y · q) ∸ (x · o) , lem' {m}{n}{o}{q} x y eq₁ (sym eq')

coprimeDivides : ∀ {a b c} -> areCoprime (a , b) -> (a ∣ (c · b)) -> a ∣ c
coprimeDivides {a}{b}{c} copr acb = →∣ (coprimeDivides∣' copr
  (→|' ( subst (λ x → x) (cong (a ∣_) (·-comm c b)) acb)))

natDivisibility : ∀ {m n m' n'} -> areCoprime (m , (suc n)) ->
  areCoprime (m' , (suc n')) -> m · (suc n') ≡ m' · (suc n) -> m ≡ m'
natDivisibility {m}{n}{m'}{n'} mn m'n' mm' = antisym∣ {m}{m'}
  (coprimeDivides mn ∣ (suc n') , (·-comm (suc n') m) ∙ mm' ∣₁)
  (coprimeDivides m'n' ∣ (suc n) , ·-comm (suc n) m' ∙ (sym mm') ∣₁)

natDivisibility' : ∀ {m n m' n'} -> areCoprime (m , (suc n)) ->
  areCoprime (m' , (suc n')) -> m · (suc n') ≡ m' · (suc n) -> n ≡ n'
natDivisibility' {zero} {n} {zero} {n'} c c' mn =
  injSuc ((zeroCoprime' c) ∙ (sym (zeroCoprime' c')))
natDivisibility' {zero} {n} {suc m'} {n'} c c' mn =
  ⊥.elim {ℓ-zero}{λ x → n ≡ n'} (znots mn)
natDivisibility' {suc m} {n} {zero} {n'} c c' mn =
  ⊥.elim {ℓ-zero}{λ x → n ≡ n'} (snotz mn)
natDivisibility' m@{suc p} {n} m'@{suc q} {n'} c c' mn =
  injSuc (inj-sm· {p}{suc n} (cong (λ x → x · suc n)
    (natDivisibility c c' mn) ∙ sym mn))
