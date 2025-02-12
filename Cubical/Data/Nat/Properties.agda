{-# OPTIONS --no-exact-split --safe #-}
module Cubical.Data.Nat.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport

open import Cubical.Data.Nat.Base
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma
open import Cubical.Data.Sum.Base

open import Cubical.Relation.Nullary

private
  variable
    l m n : ℕ

min : ℕ → ℕ → ℕ
min zero m = zero
min (suc n) zero = zero
min (suc n) (suc m) = suc (min n m)

minComm : (n m : ℕ) → min n m ≡ min m n
minComm zero zero = refl
minComm zero (suc m) = refl
minComm (suc n) zero = refl
minComm (suc n) (suc m) = cong suc (minComm n m)

max : ℕ → ℕ → ℕ
max zero m = m
max (suc n) zero = suc n
max (suc n) (suc m) = suc (max n m)

maxComm : (n m : ℕ) → max n m ≡ max m n
maxComm zero zero = refl
maxComm zero (suc m) = refl
maxComm (suc n) zero = refl
maxComm (suc n) (suc m) = cong suc (maxComm n m)

znots : ¬ (0 ≡ suc n)
znots eq = subst (caseNat ℕ ⊥) eq 0

snotz : ¬ (suc n ≡ 0)
snotz eq = subst (caseNat ⊥ ℕ) eq 0

injSuc : suc m ≡ suc n → m ≡ n
injSuc p = cong predℕ p

-- encode decode caracterisation of equality
codeℕ : (n m : ℕ) → Type ℓ-zero
codeℕ zero zero = Unit
codeℕ zero (suc m) = ⊥
codeℕ (suc n) zero = ⊥
codeℕ (suc n) (suc m) = codeℕ n m

codeℕ-trans : codeℕ n m → codeℕ m l → codeℕ n l
codeℕ-trans {zero} {zero} {zero} _ _ = tt
codeℕ-trans {suc n} {suc m} {suc l} = codeℕ-trans {n} {m} {l}

encodeℕ : (n m : ℕ) → (n ≡ m) → codeℕ n m
encodeℕ n m p = subst (λ m → codeℕ n m) p (reflCode n)
 where
 reflCode : (n : ℕ) → codeℕ n n
 reflCode zero = tt
 reflCode (suc n) = reflCode n

compute-eqℕ : (n m : ℕ) → (n ≡ m ) → codeℕ n m
compute-eqℕ zero zero p = tt
compute-eqℕ zero (suc m) p = znots p
compute-eqℕ (suc n) zero p = snotz p
compute-eqℕ (suc n) (suc m) p = compute-eqℕ n m (injSuc p)

decodeℕ : (n m : ℕ) → codeℕ n m → (n ≡ m)
decodeℕ zero zero = λ _ → refl
decodeℕ zero (suc m) = ⊥.rec
decodeℕ (suc n) zero = ⊥.rec
decodeℕ (suc n) (suc m) = λ r → cong suc (decodeℕ n m r)

≡ℕ≃Codeℕ : (n m : ℕ) → (n ≡ m) ≃ codeℕ n m
≡ℕ≃Codeℕ n m = isoToEquiv is
  where
  is : Iso (n ≡ m) (codeℕ n m)
  Iso.fun is = encodeℕ n m
  Iso.inv is = decodeℕ n m
  Iso.rightInv is = sect n m
    where
    sect : (n m : ℕ) → (r : codeℕ n m) → (encodeℕ n m (decodeℕ n m r) ≡ r)
    sect zero zero tt = refl
    sect zero (suc m) r = ⊥.rec r
    sect (suc n) zero r = ⊥.rec r
    sect (suc n) (suc m) r = sect n m r
  Iso.leftInv is = retr n m
    where
    reflRetr : (n : ℕ) → decodeℕ n n (encodeℕ n n refl) ≡ refl
    reflRetr zero = refl
    reflRetr (suc n) i = cong suc (reflRetr n i)

    retr : (n m : ℕ) → (p : n ≡ m) → (decodeℕ n m (encodeℕ n m p) ≡ p)
    retr n m p = J (λ m p → decodeℕ n m (encodeℕ n m p) ≡ p) (reflRetr n) p


≡ℕ≃Codeℕ' : (n m : ℕ) → (n ≡ m) ≃ codeℕ n m
≡ℕ≃Codeℕ' n m = isoToEquiv is
  where
  is : Iso (n ≡ m) (codeℕ n m)
  Iso.fun is = compute-eqℕ n m
  Iso.inv is = decodeℕ n m
  Iso.rightInv is = sect n m
    where
    sect : (n m : ℕ) → (r : codeℕ n m) → compute-eqℕ n m (decodeℕ n m r) ≡ r
    sect zero zero tt = refl
    sect (suc n) (suc m) r = sect n m r
  Iso.leftInv is = retr n m
    where
    reflRetr : (n : ℕ) → decodeℕ n n (compute-eqℕ n n refl) ≡ refl
    reflRetr zero = refl
    reflRetr (suc n) i = cong suc (reflRetr n i)

    retr : (n m : ℕ) → (p : n ≡ m) → decodeℕ n m (compute-eqℕ n m p) ≡ p
    retr n m p = J (λ m p → decodeℕ n m (compute-eqℕ n m p) ≡ p) (reflRetr n) p


discreteℕ : Discrete ℕ
discreteℕ zero zero = yes refl
discreteℕ zero (suc n) = no znots
discreteℕ (suc m) zero = no snotz
discreteℕ (suc m) (suc n) with discreteℕ m n
... | yes p = yes (cong suc p)
... | no p = no (λ x → p (injSuc x))

separatedℕ : Separated ℕ
separatedℕ = Discrete→Separated discreteℕ

isSetℕ : isSet ℕ
isSetℕ = Discrete→isSet discreteℕ

-- Arithmetic facts about predℕ

suc-predℕ : ∀ n → ¬ n ≡ 0 → n ≡ suc (predℕ n)
suc-predℕ zero p = ⊥.rec (p refl)
suc-predℕ (suc n) p = refl

-- Arithmetic facts about +

+-zero : ∀ m → m + 0 ≡ m
+-zero zero = refl
+-zero (suc m) = cong suc (+-zero m)

+-suc : ∀ m n → m + suc n ≡ suc (m + n)
+-suc zero    n = refl
+-suc (suc m) n = cong suc (+-suc m n)

+-comm : ∀ m n → m + n ≡ n + m
+-comm m zero = +-zero m
+-comm m (suc n) = (+-suc m n) ∙ (cong suc (+-comm m n))

-- Addition is associative
+-assoc : ∀ m n o → m + (n + o) ≡ (m + n) + o
+-assoc zero _ _    = refl
+-assoc (suc m) n o = cong suc (+-assoc m n o)

inj-m+ : m + l ≡ m + n → l ≡ n
inj-m+ {zero} p = p
inj-m+ {suc m} p = inj-m+ (injSuc p)

inj-+m : l + m ≡ n + m → l ≡ n
inj-+m {l} {m} {n} p = inj-m+ ((+-comm m l) ∙ (p ∙ (+-comm n m)))

m+n≡n→m≡0 : m + n ≡ n → m ≡ 0
m+n≡n→m≡0 {n = zero} = λ p → (sym (+-zero _)) ∙ p
m+n≡n→m≡0 {n = suc n} p = m+n≡n→m≡0 (injSuc ((sym (+-suc _ n)) ∙ p))

m+n≡0→m≡0×n≡0 : m + n ≡ 0 → (m ≡ 0) × (n ≡ 0)
m+n≡0→m≡0×n≡0 {zero} = refl ,_
m+n≡0→m≡0×n≡0 {suc m} p = ⊥.rec (snotz p)

m+n≡1→m≡0×n≡1⊎m≡1n≡0 : m + n ≡ 1 → ((m ≡ 0) × (n ≡ 1)) ⊎ ((m ≡ 1) × (n ≡ 0))
m+n≡1→m≡0×n≡1⊎m≡1n≡0 {zero} x = inl (refl , x)
m+n≡1→m≡0×n≡1⊎m≡1n≡0 {suc m} {n} x =
 let (m≡0 , n≡0) = m+n≡0→m≡0×n≡0 (injSuc x)
 in inr (cong suc m≡0 , n≡0 )

-- Arithmetic facts about ·

0≡m·0 : ∀ m → 0 ≡ m · 0
0≡m·0 zero = refl
0≡m·0 (suc m) = 0≡m·0 m

·-suc : ∀ m n → m · suc n ≡ m + m · n
·-suc zero n = refl
·-suc (suc m) n
  = cong suc
  ( n + m · suc n ≡⟨ cong (n +_) (·-suc m n) ⟩
    n + (m + m · n) ≡⟨ +-assoc n m (m · n) ⟩
    (n + m) + m · n ≡⟨ cong (_+ m · n) (+-comm n m) ⟩
    (m + n) + m · n ≡⟨ sym (+-assoc m n (m · n)) ⟩
    m + (n + m · n) ∎
  )

·-comm : ∀ m n → m · n ≡ n · m
·-comm zero n = 0≡m·0 n
·-comm (suc m) n = cong (n +_) (·-comm m n) ∙ sym (·-suc n m)

·-distribʳ : ∀ m n o → (m · o) + (n · o) ≡ (m + n) · o
·-distribʳ zero _ _ = refl
·-distribʳ (suc m) n o = sym (+-assoc o (m · o) (n · o)) ∙ cong (o +_) (·-distribʳ m n o)

·-distribˡ : ∀ o m n → (o · m) + (o · n) ≡ o · (m + n)
·-distribˡ o m n = (λ i → ·-comm o m i + ·-comm o n i) ∙ ·-distribʳ m n o ∙ ·-comm (m + n) o

·-assoc : ∀ m n o → m · (n · o) ≡ (m · n) · o
·-assoc zero _ _ = refl
·-assoc (suc m) n o = cong (n · o +_) (·-assoc m n o) ∙ ·-distribʳ n (m · n) o

·-identityˡ : ∀ m → 1 · m ≡ m
·-identityˡ m = +-zero m

·-identityʳ : ∀ m → m · 1 ≡ m
·-identityʳ zero = refl
·-identityʳ (suc m) = cong suc (·-identityʳ m)

0≡n·sm→0≡n : 0 ≡ n · suc m → 0 ≡ n
0≡n·sm→0≡n {n = zero} p = refl
0≡n·sm→0≡n {n = suc n} p = ⊥.rec (znots p)

inj-·sm : l · suc m ≡ n · suc m → l ≡ n
inj-·sm {zero} {m} {n} p = 0≡n·sm→0≡n p
inj-·sm {l} {m} {zero} p = sym (0≡n·sm→0≡n (sym p))
inj-·sm {suc l} {m} {suc n} p = cong suc (inj-·sm (inj-m+ {m = suc m} p))

inj-sm· : suc m · l ≡ suc m · n → l ≡ n
inj-sm· {m} {l} {n} p = inj-·sm (·-comm l (suc m) ∙ p ∙ ·-comm (suc m) n)

integral-domain-· : {k l : ℕ} → (k ≡ 0 → ⊥) → (l ≡ 0 → ⊥) → (k · l ≡ 0 → ⊥)
integral-domain-· {zero} {l} ¬p ¬q r = ¬p refl
integral-domain-· {suc k} {zero} ¬p ¬q r = ¬q refl
integral-domain-· {suc k} {suc l} ¬p ¬q r = snotz r

-- Arithmetic facts about ∸

zero∸ : ∀ n → zero ∸ n ≡ zero
zero∸ zero = refl
zero∸ (suc _) = refl


n∸n : (n : ℕ) → n ∸ n ≡ 0
n∸n zero = refl
n∸n (suc n) = n∸n n

∸-cancelˡ : ∀ k m n → (k + m) ∸ (k + n) ≡ m ∸ n
∸-cancelˡ zero    = λ _ _ → refl
∸-cancelˡ (suc k) = ∸-cancelˡ k

+∸ : ∀ k n → (k + n) ∸ n ≡ k
+∸ zero n = n∸n n
+∸ (suc k) zero = cong suc (+-comm k zero)
+∸ (suc k) (suc n) = cong (_∸ n) (+-suc k n) ∙ +∸ (suc k) n

∸+ : ∀ k n → (n + k) ∸ n ≡ k
∸+ k n = cong (λ X → X ∸ n) (+-comm n k) ∙ +∸ k n

∸-cancelʳ : ∀ m n k → (m + k) ∸ (n + k) ≡ m ∸ n
∸-cancelʳ m n k = (λ i → +-comm m k i ∸ +-comm n k i) ∙ ∸-cancelˡ k m n

∸-distribʳ : ∀ m n k → (m ∸ n) · k ≡ m · k ∸ n · k
∸-distribʳ m       zero    k = refl
∸-distribʳ zero    (suc n) k = sym (zero∸ (k + n · k))
∸-distribʳ (suc m) (suc n) k = ∸-distribʳ m n k ∙ sym (∸-cancelˡ k (m · k) (n · k))



-- factorial:
_! : ℕ → ℕ
zero ! = 1
suc n ! = (suc n) · (n !)

--binomial coefficient:
_choose_ : ℕ → ℕ → ℕ
n choose zero = 1
zero choose suc k = 0
suc n choose suc k = n choose (suc k) + n choose k

evenOrOdd : (n : ℕ) → isEvenT n ⊎ isOddT n
evenOrOdd zero = inl tt
evenOrOdd (suc zero) = inr tt
evenOrOdd (suc (suc n)) = evenOrOdd n

¬evenAndOdd : (n : ℕ) → ¬ isEvenT n × isOddT n
¬evenAndOdd zero (p , ())
¬evenAndOdd (suc zero) ()
¬evenAndOdd (suc (suc n)) = ¬evenAndOdd n

isPropIsEvenT : (n : ℕ) → isProp (isEvenT n)
isPropIsEvenT zero x y = refl
isPropIsEvenT (suc zero) = isProp⊥
isPropIsEvenT (suc (suc n)) = isPropIsEvenT n

isPropIsOddT : (n : ℕ) → isProp (isOddT n)
isPropIsOddT n = isPropIsEvenT (suc n)

isPropEvenOrOdd : (n : ℕ) → isProp (isEvenT n ⊎ isOddT n)
isPropEvenOrOdd n (inl x) (inl x₁) = cong inl (isPropIsEvenT n x x₁)
isPropEvenOrOdd n (inl x) (inr x₁) = ⊥.rec (¬evenAndOdd n (x , x₁))
isPropEvenOrOdd n (inr x) (inl x₁) = ⊥.rec (¬evenAndOdd (suc n) (x , x₁))
isPropEvenOrOdd n (inr x) (inr x₁) = cong inr (isPropIsEvenT (suc n) x x₁)

module PlusBis where

  _+'_ : ℕ → ℕ → ℕ
  zero +' b = b
  suc a +' zero = suc a
  suc a +' suc b = 2 + (a + b)

  +'≡+ : (n m : ℕ) → n +' m ≡ n + m
  +'≡+ zero m = refl
  +'≡+ (suc n) zero = cong suc (sym (+-comm n zero))
  +'≡+ (suc n) (suc m) = cong suc (sym (+-suc n m))

  +'-comm : (n m : ℕ) → n +' m ≡ m +' n
  +'-comm n m = +'≡+ n m ∙∙ +-comm n m ∙∙ sym (+'≡+ m n)

  +'-assoc : (n m l : ℕ) → (n +' (m +' l)) ≡ ((n +' m) +' l)
  +'-assoc n m l =
       (λ i → +'≡+ n (+'≡+ m l i) i)
    ∙∙ +-assoc n m l
    ∙∙ (λ i → +'≡+ (+'≡+ n m (~ i)) l (~ i))

  +'-rid : (n : ℕ) → n +' 0 ≡ n
  +'-rid zero = refl
  +'-rid (suc n) = refl

  +'-lid : (n : ℕ) → 0 +' n ≡ n
  +'-lid n = refl

  +'-suc : (n m : ℕ) → suc (n +' m) ≡ suc n +' m
  +'-suc zero zero = refl
  +'-suc zero (suc m) = refl
  +'-suc (suc n) zero = refl
  +'-suc (suc n) (suc m) = refl

-- Neat transport lemma for ℕ
compSubstℕ : ∀ {ℓ} {A : ℕ → Type ℓ} {n m l : ℕ}
   (p : n ≡ m) (q : m ≡ l) (r : n ≡ l)
   → {x : _}
   → subst A q (subst A p x)
   ≡ subst A r x
compSubstℕ {A = A} p q r {x = x} =
  sym (substComposite A p q x)
  ∙ λ i → subst A (isSetℕ _ _ (p ∙ q) r i) x
