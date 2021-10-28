{-# OPTIONS --safe #-}
module Cubical.Data.Int.MoreInts.QuoInt.Properties where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Relation.Nullary

open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc)
open import Cubical.Data.Bool as Bool using (Bool; not; notnot)
open import Cubical.Data.Empty
open import Cubical.Data.Unit renaming (Unit to ⊤)

open import Cubical.Data.Int.MoreInts.QuoInt.Base

·S-comm : ∀ x y → x ·S y ≡ y ·S x
·S-comm = Bool.⊕-comm

·S-assoc : ∀ x y z → x ·S (y ·S z) ≡ (x ·S y) ·S z
·S-assoc = Bool.⊕-assoc

not-·Sˡ : ∀ x y → not (x ·S y) ≡ not x ·S y
not-·Sˡ = Bool.not-⊕ˡ


snotz : ∀ s n s' → ¬ (signed s (suc n) ≡ signed s' zero)
snotz s n s' eq = subst (λ { (signed s (suc n)) → ⊤
                           ; _                  → ⊥ }) eq tt


+-zeroʳ : ∀ s m → m + signed s zero ≡ m
+-zeroʳ s (signed s' zero) = signed-zero s s'
+-zeroʳ s (pos (suc n)) = cong sucℤ  (+-zeroʳ s (pos n))
+-zeroʳ s (neg (suc n)) = cong predℤ (+-zeroʳ s (neg n))
+-zeroʳ spos (posneg i) j = posneg (i ∧ j)
+-zeroʳ sneg (posneg i) j = posneg (i ∨ ~ j)

+-identityʳ : ∀ m → m + pos zero ≡ m
+-identityʳ = +-zeroʳ spos

sucℤ-+ʳ : ∀ m n → sucℤ (m + n) ≡ m + sucℤ n
sucℤ-+ʳ (signed _ zero) _ = refl
sucℤ-+ʳ (posneg _) _ = refl
sucℤ-+ʳ (pos (suc m)) n = cong sucℤ (sucℤ-+ʳ (pos m) n)
sucℤ-+ʳ (neg (suc m)) n =
  sucPredℤ (neg m + n) ∙∙
  sym (predSucℤ (neg m + n)) ∙∙
  cong predℤ (sucℤ-+ʳ (neg m) n)

-- I wonder if we could somehow use negEq to get this for free from the above...
predℤ-+ʳ : ∀ m n → predℤ (m + n) ≡ m + predℤ n
predℤ-+ʳ (signed _ zero) _ = refl
predℤ-+ʳ (posneg _) _ = refl
predℤ-+ʳ (neg (suc m)) n = cong predℤ (predℤ-+ʳ (neg m) n)
predℤ-+ʳ (pos (suc m)) n =
  predSucℤ (pos m + n) ∙∙
  sym (sucPredℤ (pos m + n)) ∙∙
  cong sucℤ (predℤ-+ʳ (pos m) n)

+-comm : ∀ m n → m + n ≡ n + m
+-comm (signed s zero) n = sym (+-zeroʳ s n)
+-comm (pos (suc m)) n = cong sucℤ  (+-comm (pos m) n) ∙ sucℤ-+ʳ  n (pos m)
+-comm (neg (suc m)) n = cong predℤ (+-comm (neg m) n) ∙ predℤ-+ʳ n (neg m)
+-comm (posneg i) n = lemma n i
  where
  -- get some help from:
  -- https://www.codewars.com/kata/reviews/5c878e3ef1abb10001e32eb1/groups/5cca3f9e840f4b0001d8ac98
  lemma : ∀ n → (λ i → (posneg i + n) ≡ (n + posneg i))
          [ sym (+-zeroʳ spos n) ≡ sym (+-zeroʳ sneg n) ]
  lemma (pos zero) i j = posneg (i ∧ j)
  lemma (pos (suc n)) i = cong sucℤ (lemma (pos n) i)
  lemma (neg zero) i j = posneg (i ∨ ~ j)
  lemma (neg (suc n)) i = cong predℤ (lemma (neg n) i)
  lemma (posneg i) j k = posneg ((i ∧ ~ k) ∨ (i ∧ j) ∨ (j ∧ k))

sucℤ-+ˡ : ∀ m n → sucℤ (m + n) ≡ sucℤ m + n
sucℤ-+ˡ (pos _) n = refl
sucℤ-+ˡ (neg zero) n = refl
sucℤ-+ˡ (neg (suc m)) n = sucPredℤ _
sucℤ-+ˡ (posneg _) n = refl

-- I wonder if we could somehow use negEq to get this for free from the above...
predℤ-+ˡ : ∀ m n → predℤ (m + n) ≡ predℤ m + n
predℤ-+ˡ (pos zero) n = refl
predℤ-+ˡ (pos (suc m)) n = predSucℤ _
predℤ-+ˡ (neg _) n = refl
predℤ-+ˡ (posneg _) n = refl

+-assoc : ∀ m n o → m + (n + o) ≡ m + n + o
+-assoc (signed s zero) n o = refl
+-assoc (posneg i) n o = refl
+-assoc (pos (suc m)) n o = cong sucℤ  (+-assoc (pos m) n o) ∙ sucℤ-+ˡ  (pos m + n) o
+-assoc (neg (suc m)) n o = cong predℤ (+-assoc (neg m) n o) ∙ predℤ-+ˡ (neg m + n) o


sucℤ-inj : ∀ m n → sucℤ m ≡ sucℤ n → m ≡ n
sucℤ-inj m n p = sym (predSucℤ m) ∙ cong predℤ p ∙ predSucℤ n

predℤ-inj : ∀ m n → predℤ m ≡ predℤ n → m ≡ n
predℤ-inj m n p = sym (sucPredℤ m) ∙ cong sucℤ p ∙ sucPredℤ n

+-injˡ : ∀ o m n → o + m ≡ o + n → m ≡ n
+-injˡ (signed _ zero) _ _ p = p
+-injˡ (posneg _)      _ _ p = p
+-injˡ (pos (suc o)) m n p = +-injˡ (pos o) m n (sucℤ-inj  _ _ p)
+-injˡ (neg (suc o)) m n p = +-injˡ (neg o) m n (predℤ-inj _ _ p)

+-injʳ : ∀ m n o → m + o ≡ n + o → m ≡ n
+-injʳ m n o p = +-injˡ o m n (+-comm o m ∙ p ∙ +-comm n o)


·-comm : ∀ m n → m · n ≡ n · m
·-comm m n i = signed (·S-comm (sign m) (sign n) i) (ℕ.·-comm (abs m) (abs n) i)

·-identityˡ : ∀ n → pos 1 · n ≡ n
·-identityˡ n = cong (signed (sign n)) (ℕ.+-zero (abs n)) ∙ signed-inv n

·-identityʳ : ∀ n → n · pos 1 ≡ n
·-identityʳ n = ·-comm n (pos 1) ∙ ·-identityˡ n

·-zeroˡ : ∀ {s} n → signed s zero · n ≡ signed s zero
·-zeroˡ _ = signed-zero _ _

·-zeroʳ : ∀ {s} n → n · signed s zero ≡ signed s zero
·-zeroʳ n = cong (signed _) (sym (ℕ.0≡m·0 (abs n))) ∙ signed-zero _ _

·-signed-pos : ∀ {s} m n → signed s m · pos n ≡ signed s (m ℕ.· n)
·-signed-pos {s} zero n = ·-zeroˡ {s} (pos n)
·-signed-pos {s} (suc m) n i = signed (·S-comm s (sign-pos n i) i) (suc m ℕ.· n)


-- this proof is why we defined ℤ using `signed` instead of `pos` and `neg`
-- based on that in: https://github.com/danr/Agda-Numerics
·-assoc : ∀ m n o → m · (n · o) ≡ m · n · o

·-assoc (signed s zero) n o =
  ·-zeroˡ (n · o)
·-assoc m@(signed _ (suc _)) (signed s zero) o =
  ·-zeroʳ {sign o} m ∙ signed-zero _ _ ∙ cong (_· o) (sym (·-zeroʳ {s} m))
·-assoc m@(signed _ (suc _)) n@(signed _ (suc _)) (signed s zero) =
  cong (m ·_) (·-zeroʳ {s} n) ∙ ·-zeroʳ {s} m ∙ sym (·-zeroʳ {s} (m · n))

·-assoc (signed sm (suc m)) (signed sn (suc n)) (signed so (suc o)) i =
  signed (·S-assoc sm sn so i) (ℕ.·-assoc (suc m) (suc n) (suc o) i)

·-assoc (posneg i) n o j =
  isSet→isSet' isSetℤ (·-assoc (pos zero) n o) (·-assoc (neg zero) n o)
                      (λ i → posneg i · (n · o)) (λ i → posneg i · n · o) i j
·-assoc m@(signed _ (suc _)) (posneg i) o j =
  isSet→isSet' isSetℤ (·-assoc m (pos zero) o) (·-assoc m (neg zero) o)
                      (λ i → m · (posneg i · o)) (λ i → m · posneg i · o) i j
·-assoc m@(signed _ (suc _)) n@(signed _ (suc _)) (posneg i) j =
  isSet→isSet' isSetℤ (·-assoc m n (pos zero)) (·-assoc m n (neg zero))
                      (λ i → m · (n · posneg i)) (λ i → m · n · posneg i) i j


negateSuc : ∀ n → - sucℤ n ≡ predℤ (- n)
negateSuc n i = - sucℤ (negate-invol n (~ i))

negatePred : ∀ n → - predℤ n ≡ sucℤ (- n)
negatePred n i = negate-invol (sucℤ (- n)) i

negate-+ : ∀ m n → - (m + n) ≡  (- m) + (- n)
negate-+ (signed _ zero) n = refl
negate-+ (posneg _)      n = refl
negate-+ (pos (suc m))   n = negateSuc  (pos m + n) ∙ cong predℤ (negate-+ (pos m) n)
negate-+ (neg (suc m))   n = negatePred (neg m + n) ∙ cong sucℤ  (negate-+ (neg m) n)


negate-·ˡ : ∀ m n → - (m · n) ≡ (- m) · n
negate-·ˡ (signed _ zero) n = signed-zero (not (sign n)) (sign n)
negate-·ˡ (signed ss (suc m)) n i = signed (not-·Sˡ ss (sign n) i) (suc m ℕ.· abs n)
negate-·ˡ (posneg i) n j =
  isSet→isSet' isSetℤ (signed-zero (not (sign n)) _) (signed-zero _ _)
                      refl (λ i → posneg (~ i) · n) i j


signed-distrib : ∀ s m n → signed s (m ℕ.+ n) ≡ signed s m + signed s n
signed-distrib s zero n = refl
signed-distrib spos (suc m) n = cong sucℤ  (signed-distrib spos m n)
signed-distrib sneg (suc m) n = cong predℤ (signed-distrib sneg m n)

·-pos-suc : ∀ m n → pos (suc m) · n ≡ n + pos m · n
·-pos-suc m n = signed-distrib (sign n) (abs n) (m ℕ.· abs n)
                ∙ (λ i → signed-inv n i + signed (sign-pos m (~ i) ·S sign n) (m ℕ.· abs n))


-- the below is based on that in: https://github.com/danr/Agda-Numerics

·-distribˡ-pos : ∀ o m n → (pos o · m) + (pos o · n) ≡ pos o · (m + n)
·-distribˡ-pos zero m n = signed-zero (sign n) (sign (m + n))
·-distribˡ-pos (suc o) m n =
  pos (suc o) · m + pos (suc o) · n ≡[ i ]⟨ ·-pos-suc o m i + ·-pos-suc o n i ⟩
  m + pos o · m + (n + pos o · n)   ≡⟨ +-assoc (m + pos o · m) n (pos o · n) ⟩
  m + pos o · m + n + pos o · n     ≡[ i ]⟨ +-assoc m (pos o · m) n (~ i) + pos o · n ⟩
  m + (pos o · m + n) + pos o · n   ≡[ i ]⟨ m + +-comm (pos o · m) n i + pos o · n ⟩
  m + (n + pos o · m) + pos o · n   ≡[ i ]⟨ +-assoc m n (pos o · m) i + pos o · n ⟩
  m + n + pos o · m + pos o · n     ≡⟨ sym (+-assoc (m + n) (pos o · m) (pos o · n)) ⟩
  m + n + (pos o · m + pos o · n)   ≡⟨ cong ((m + n) +_) (·-distribˡ-pos o m n) ⟩
  m + n + pos o · (m + n)           ≡⟨ sym (·-pos-suc o (m + n)) ⟩
  pos (suc o) · (m + n) ∎

·-distribˡ-neg : ∀ o m n → (neg o · m) + (neg o · n) ≡ neg o · (m + n)
·-distribˡ-neg o m n =
     neg o · m  +    neg o · n  ≡[ i ]⟨ negate-·ˡ (pos o) m (~ i) + negate-·ˡ (pos o) n (~ i) ⟩
  - (pos o · m) + - (pos o · n) ≡⟨ sym (negate-+ (pos o · m) (pos o · n)) ⟩
  - (pos o · m + pos o · n)     ≡⟨ cong -_ (·-distribˡ-pos o m n) ⟩
  - (pos o · (m + n))           ≡⟨ negate-·ˡ (pos o) (m + n) ⟩
     neg o · (m + n)            ∎

·-distribˡ : ∀ o m n → (o · m) + (o · n) ≡ o · (m + n)
·-distribˡ (pos o) m n = ·-distribˡ-pos o m n
·-distribˡ (neg o) m n = ·-distribˡ-neg o m n
·-distribˡ (posneg i) m n j =
  isSet→isSet' isSetℤ (·-distribˡ-pos zero m n) (·-distribˡ-neg zero m n)
                      (λ i → posneg i · n) (λ i → posneg i · (m + n)) i j

·-distribʳ : ∀ m n o → (m · o) + (n · o) ≡ (m + n) · o
·-distribʳ m n o = (λ i → ·-comm m o i + ·-comm n o i) ∙ ·-distribˡ o m n ∙ ·-comm o (m + n)


sign-pos-suc-· : ∀ m n → sign (pos (suc m) · n) ≡ sign n
sign-pos-suc-· m (signed s zero) = sign-pos (suc m ℕ.· zero)
sign-pos-suc-· m (posneg i)      = sign-pos (suc m ℕ.· zero)
sign-pos-suc-· m (signed s (suc n)) = refl

·-injˡ : ∀ o m n → pos (suc o) · m ≡ pos (suc o) · n → m ≡ n
·-injˡ o m n p = sym (signed-inv m) ∙ (λ i → signed (sign-eq i) (abs-eq i)) ∙ signed-inv n
  where sign-eq = sym (sign-pos-suc-· o m) ∙ cong sign p ∙ sign-pos-suc-· o n
        abs-eq = ℕ.inj-sm· {o} (cong abs p)

·-injʳ : ∀ m n o → m · pos (suc o) ≡ n · pos (suc o) → m ≡ n
·-injʳ m n o p = ·-injˡ o m n (·-comm (pos (suc o)) m ∙ p ∙ ·-comm n (pos (suc o)))
