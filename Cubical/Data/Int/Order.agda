{-# OPTIONS --safe #-}
module Cubical.Data.Int.Order where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Int.Base as ℤ
open import Cubical.Data.Int.Properties as ℤ
open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Sigma

open import Cubical.Relation.Nullary

infix 4 _≤_ _<_ _≥_ _>_

_≤_ : ℤ → ℤ → Type₀
m ≤ n = Σ[ k ∈ ℕ ] m +pos k ≡ n

_<_ : ℤ → ℤ → Type₀
m < n = sucℤ m ≤ n

_≥_ : ℤ → ℤ → Type₀
m ≥ n = n ≤ m

_>_ : ℤ → ℤ → Type₀
m > n = n < m

data Trichotomy (m n : ℤ) : Type₀ where
  lt : m < n → Trichotomy m n
  eq : m ≡ n → Trichotomy m n
  gt : n < m → Trichotomy m n

private
  variable
    m n o s : ℤ
    k l : ℕ

private
  witness-prop : ∀ j → isProp (m +pos j ≡ n)
  witness-prop {m} {n} j = isSetℤ (m +pos j) n

isProp≤ : isProp (m ≤ n)
isProp≤ {m} {n} (k , p) (l , q)
  = Σ≡Prop witness-prop lemma
  where
    lemma : k ≡ l
    lemma = injPos (inj-z+ (p ∙ sym q))

zero-≤pos : 0 ≤ pos l
zero-≤pos {l} = l , (sym (pos0+ (pos l)))

suc-≤-suc : m ≤ n → sucℤ m ≤ sucℤ n
suc-≤-suc {m} {n} (k , p) = k , (sym (sucℤ+pos k m) ∙ cong sucℤ p)

negsuc-≤-negsuc : pos k ≤ pos l → negsuc l ≤ negsuc k
negsuc-≤-negsuc {k} {l} (i , p) = i ,
  ((negsuc l +pos i)               ≡⟨ cong (λ x → negsuc x +pos i)
                                           (sym (injPos (pos+ k i ∙ p))) ⟩
   (negsuc (k ℕ.+ i) +pos i)       ≡⟨ cong (ℤ._+ pos i) (negsuc+ k i) ⟩
   ((negsuc k ℤ.+ - pos i) +pos i) ≡⟨ minusPlus (pos i) (negsuc k) ⟩
   negsuc k                        ∎)

pos-≤-pos : negsuc k ≤ negsuc l → pos l ≤ pos k
pos-≤-pos {k} {l} (i , p) = i ,
  ((pos l +pos i)
        ≡⟨ sym (cong (pos l ℤ.+_) (plusMinus (negsuc k) (pos i))) ⟩
   pos l ℤ.+ sucℤ ((pos i +negsuc k) +pos k)
        ≡[ j ]⟨ pos l ℤ.+ sucℤ ((+Comm (pos i) (negsuc k)) j +pos k) ⟩
   pos l ℤ.+ sucℤ ((negsuc k +pos i) +pos k)
        ≡[ j ]⟨ pos l ℤ.+ sucℤ (p j +pos k) ⟩
   pos l ℤ.+ sucℤ (negsuc l +pos k)
        ≡⟨ cong (pos l ℤ.+_) (sucℤ+ (negsuc l) (pos k)) ⟩
   pos l ℤ.+ (sucℤ (negsuc l) +pos k)
        ≡⟨ +Assoc (pos l) (sucℤ (negsuc l)) (pos k) ⟩
   ((pos l ℤ.+ sucℤ (negsuc l)) +pos k)
        ≡[ j ]⟨ (pos l ℤ.+ sucℤnegsucneg l j) +pos k ⟩
   ((pos l ℤ.+ neg l) +pos k)
        ≡[ j ]⟨ (pos l ℤ.+ (-pos l (~ j))) +pos k ⟩
   ((pos l - pos l) +pos k)
        ≡⟨ cong (_+pos k) (-Cancel (pos l)) ⟩
   0 +pos k ≡⟨ +Comm 0 (pos k) ⟩
   pos k ∎)

≤-+o : m ≤ n → m ℤ.+ o ≤ n ℤ.+ o
≤-+o {m} {n} {o} (i , p)
  = i , (((m ℤ.+ o) +pos i)  ≡⟨ sym (+Assoc m o (pos i)) ⟩
         m ℤ.+ (o ℤ.+ pos i) ≡⟨ cong (m ℤ.+_) (+Comm o (pos i)) ⟩
         m ℤ.+ (pos i ℤ.+ o) ≡⟨ +Assoc m (pos i) o ⟩
         (m +pos i) ℤ.+ o    ≡⟨ cong (ℤ._+ o) p ⟩
         n ℤ.+ o             ∎)

≤SumRightPos : n ≤ pos k ℤ.+ n
≤SumRightPos {n} {k} = subst (_≤ pos k ℤ.+ n) (sym (pos0+ n)) (≤-+o {o = n} (zero-≤pos {k}))

≤-o+ : m ≤ n → o ℤ.+ m ≤ o ℤ.+ n
≤-o+ {m} {n} {o}
  = subst (_≤ o ℤ.+ n) (+Comm m o)
  ∘ subst (m ℤ.+ o ≤_) (+Comm n o)
  ∘ ≤-+o {o = o}

≤SumLeftPos : n ≤ n ℤ.+ pos k
≤SumLeftPos {n} {k} = ≤-o+ {o = n} (zero-≤pos {k})

pred-≤-pred : sucℤ m ≤ sucℤ n → m ≤ n
pred-≤-pred {m} {n} (k , p) = k , cong (_+pos k) (sym (predSuc m))
                                 ∙ sym (predℤ+pos k (sucℤ m))
                                 ∙ cong predℤ p
                                 ∙ predSuc n

isRefl≤ : m ≤ m
isRefl≤ = 0 , refl

≤-suc : m ≤ n → m ≤ sucℤ n
≤-suc (k , p) = suc k , cong sucℤ p

suc-< : sucℤ m < n → m < n
suc-< p = pred-≤-pred (≤-suc p)

≤-sucℤ : n ≤ sucℤ n
≤-sucℤ = ≤-suc isRefl≤

≤-predℤ : predℤ n ≤ n
≤-predℤ {n} = 1 , sucPred n

isTrans≤ : m ≤ n → n ≤ o → m ≤ o
isTrans≤ {m} {n} {o} (i , p) (j , q) = (i ℕ.+ j)
  , ((m ℤ.+ pos (i ℕ.+ j)) ≡⟨ cong (m ℤ.+_) (pos+ i j) ⟩
     m ℤ.+ (pos i +pos j)   ≡⟨ +Assoc m (pos i) (pos j) ⟩
     ((m +pos i) +pos j)    ≡⟨ cong (_+pos j) p ⟩
     (n +pos j)             ≡⟨ q ⟩
     o                      ∎)

isAntisym≤ : m ≤ n → n ≤ m → m ≡ n
isAntisym≤ {m} {n} (i , p) (j , q)
  = cong (m +pos_) (injPos lemma₂) ∙ p
  where lemma₀ : pos (j ℕ.+ i) ℤ.+ m ≡ m
        lemma₀ = pos (j ℕ.+ i) ℤ.+ m     ≡⟨ cong (ℤ._+ m) (pos+ j i) ⟩
                 (pos j +pos i) ℤ.+ m    ≡⟨ sym (+Assoc (pos j) (pos i) m) ⟩
                 pos j ℤ.+ (pos i ℤ.+ m) ≡⟨ cong (pos j ℤ.+_) (+Comm (pos i) m) ⟩
                 pos j ℤ.+ (m ℤ.+ pos i) ≡⟨ cong (pos j ℤ.+_) p ⟩
                 pos j ℤ.+ n              ≡⟨ +Comm (pos j) n ⟩
                 (n +pos j)               ≡⟨ q ⟩
                 m                        ∎
        lemma₁ : pos (j ℕ.+ i) ≡ 0
        lemma₁ = n+z≡z→n≡0 (pos (j ℕ.+ i)) m lemma₀

        lemma₂ : 0 ≡ pos i
        lemma₂ = cong pos (sym (snd (m+n≡0→m≡0×n≡0 (injPos lemma₁))))

≤Monotone+ : m ≤ n → o ≤ s → m ℤ.+ o ≤ n ℤ.+ s
≤Monotone+ {o = o} p q = isTrans≤ (≤-+o {o = o} p) (≤-o+ q)

≤-o+-cancel : o ℤ.+ m ≤ o ℤ.+ n → m ≤ n
≤-o+-cancel {o} {m} (i , p) = i , inj-z+ {z = o} (+Assoc o m (pos i) ∙ p)

≤-+o-cancel : m ℤ.+ o ≤ n ℤ.+ o → m ≤ n
≤-+o-cancel {m} {o} {n} (i , p) = i , (inj-+z {z = o}
  ((m +pos i) ℤ.+ o    ≡⟨ sym (+Assoc m (pos i) o) ⟩
   m ℤ.+ (pos i ℤ.+ o) ≡⟨ cong (m ℤ.+_) (+Comm (pos i) o) ⟩
   m ℤ.+ (o +pos i)    ≡⟨ +Assoc m o (pos i) ⟩
   ((m ℤ.+ o) +pos i)  ≡⟨ p ⟩
   n ℤ.+ o             ∎))

≤-+pos-trans : m ℤ.+ pos k ≤ n → m ≤ n
≤-+pos-trans {m} {k} {n} p = isTrans≤ ≤SumRightPos (subst (_≤ n) (+Comm m (pos k)) p)

≤-pos+-trans : pos k ℤ.+ m ≤ n → m ≤ n
≤-pos+-trans {k} {m} {n} p = isTrans≤ ≤SumRightPos p

≤-·o : m ≤ n → m ℤ.· (pos k) ≤ n ℤ.· (pos k)
≤-·o {m} {n} {k} (i , p) = i ℕ.· k ,
  (((m ℤ.· pos k) +pos (i ℕ.· k))  ≡⟨ cong (m ℤ.· pos k ℤ.+_) (pos·pos i k) ⟩
   m ℤ.· pos k ℤ.+ pos i ℤ.· pos k ≡⟨ sym (·DistL+ m (pos i) (pos k)) ⟩
   (m +pos i) ℤ.· pos k             ≡⟨ cong (ℤ._· pos k) p ⟩
   n ℤ.· pos k                      ∎)

<-o+-cancel : o ℤ.+ m < o ℤ.+ n → m < n
<-o+-cancel {o} {m} {n} = ≤-o+-cancel ∘ subst (_≤ o ℤ.+ n) (+sucℤ o m)

¬-pos<-zero : ¬ (pos k) < 0
¬-pos<-zero {k} (i , p) = snotz (injPos (pos+ (suc k) i ∙ p))

negsuc<-zero : negsuc k < 0
negsuc<-zero {k} = k ,
  ((sucℤ (negsuc k) +pos k)    ≡⟨ sym (sucℤ+ (negsuc k) (pos k)) ⟩
   sucℤ (negsuc k +pos k)      ≡⟨ +sucℤ (negsuc k) (pos k) ⟩
   neg (suc k) ℤ.+ pos (suc k) ≡⟨ -Cancel' (pos (suc k)) ⟩
   pos zero                    ∎)

isIrrefl< : ¬ m < m
isIrrefl< {pos zero} (i , p) = snotz (injPos (pos+ (suc zero) i ∙ p))
isIrrefl< {pos (suc n)} (i , p) = isIrrefl< {m = pos n} (i ,
  (sym (pos+ (suc n) i)
   ∙ cong pos(+-comm (suc n) i
   ∙ +-suc i n
   ∙ cong suc (+-comm i n)
   ∙ injSuc (injPos (pos+ (suc (suc n)) i ∙ p)))))
isIrrefl< {negsuc zero} (i , p)
  = posNotnegsuc (zero ℕ.+ i) zero (+Comm (pos i) (pos zero) ∙ p)
isIrrefl< {negsuc (suc n)} (i , p) = isIrrefl< {m = negsuc n} (i ,
  ((sucℤ (negsuc n) +pos i) ≡⟨ sym (sucℤ+ (negsuc n) (pos i)) ⟩
   sucℤ (negsuc n +pos i)   ≡⟨ cong sucℤ p ⟩
   negsuc n                 ∎))

pos≤0→≡0 : pos k ≤ 0 → pos k ≡ 0
pos≤0→≡0 {zero} _ = refl
pos≤0→≡0 {suc k} p = ⊥.rec (¬-pos<-zero {k = k} p)

predℤ-≤-predℤ : m ≤ n → predℤ m ≤ predℤ n
predℤ-≤-predℤ {m} {n} (i , p) = i ,
  ((predℤ m +pos i) ≡⟨ sym (predℤ+ m (pos i)) ⟩
   predℤ (m +pos i) ≡⟨ cong predℤ p ⟩
   predℤ n          ∎)

¬m+posk<m : ¬ m ℤ.+ pos k < m
¬m+posk<m {m} {k} = ¬-pos<-zero ∘ <-o+-cancel {o = m} {m = pos k} {n = 0}

<-weaken : m < n → m ≤ n
<-weaken {m} (i , p) = (suc i) , sucℤ+ m (pos i) ∙ p

≤<-trans : o ≤ m → m < n → o < n
≤<-trans p = isTrans≤ (suc-≤-suc p)

<≤-trans : o < m → m ≤ n → o < n
<≤-trans = isTrans≤

isTrans< : o < m → m < n → o < n
isTrans< p = ≤<-trans (<-weaken p)

isAsym< : m < n → ¬ n ≤ m
isAsym< m<n = isIrrefl< ∘ <≤-trans m<n

<-+o : m < n → m ℤ.+ o < n ℤ.+ o
<-+o {m} {n} {o} = subst (_≤ n ℤ.+ o) (sym (sucℤ+ m o)) ∘ ≤-+o {o = o}

<-o+ : m < n → o ℤ.+ m < o ℤ.+ n
<-o+ {m} {n} {o} = subst (_≤ o ℤ.+ n) (sym (+sucℤ o m)) ∘ ≤-o+ {o = o}

<-+pos-trans : m ℤ.+ pos k < n → m < n
<-+pos-trans {k = k} = ≤<-trans (k , refl)

<-pos+-trans : pos k ℤ.+ m < n → m < n
<-pos+-trans {k} {m} = ≤<-trans (k , (+Comm m (pos k)))

<Monotone+ : m < n → o < s → m ℤ.+ o < n ℤ.+ s
<Monotone+ {o = o} m<n o<s = isTrans< (<-+o {o = o} m<n) (<-o+ o<s)

<-+-≤ : m < n → o ≤ s → m ℤ.+ o < n ℤ.+ s
<-+-≤ {o = o} m<n o≤s = <≤-trans (<-+o {o = o} m<n) (≤-o+ o≤s)

-pos≤ : m - (pos k) ≤ m
-pos≤ {m} {k} = k , minusPlus (pos k) m

≤-max : m ≤ ℤ.max m n
≤-max {pos zero} {pos m} = zero-≤pos
≤-max {pos (suc m)} {pos zero} = isRefl≤
≤-max {pos (suc m)} {pos (suc n)} = suc-≤-suc (≤-max {m = pos m} {n = pos n})
≤-max {pos zero} {negsuc n} = isRefl≤
≤-max {pos (suc m)} {negsuc n} = isRefl≤
≤-max {negsuc m} {pos zero} = negsuc<-zero
≤-max {negsuc m} {pos (suc n)} = isTrans≤ negsuc<-zero zero-≤pos
≤-max {negsuc zero} {negsuc n} = isRefl≤
≤-max {negsuc (suc m)} {negsuc zero} = negsuc-≤-negsuc zero-≤pos
≤-max {negsuc (suc m)} {negsuc (suc n)} = pred-≤-pred (subst (negsuc m ≤_)
                                        (sym (sucPred (ℤ.max (negsuc m) (negsuc n))))
                                        (≤-max {m = negsuc m} {n = negsuc n}))

min-≤ : ℤ.min m n ≤ m
min-≤ {pos zero} {pos n} = isRefl≤
min-≤ {pos (suc m)} {pos zero} = zero-≤pos
min-≤ {pos (suc m)} {pos (suc n)} = suc-≤-suc (min-≤ {m = pos m} {n = pos n})
min-≤ {pos zero} {negsuc n} = negsuc<-zero
min-≤ {pos (suc m)} {negsuc n} = isTrans≤ negsuc<-zero zero-≤pos
min-≤ {negsuc zero} {pos n} = isRefl≤
min-≤ {negsuc (suc m)} {pos n} = isRefl≤
min-≤ {negsuc zero} {negsuc zero} = isRefl≤
min-≤ {negsuc zero} {negsuc (suc n)} = negsuc-≤-negsuc zero-≤pos
min-≤ {negsuc (suc m)} {negsuc zero} = isRefl≤
min-≤ {negsuc (suc m)} {negsuc (suc n)} = pred-≤-pred (subst (_≤ negsuc m)
                                        (sym (sucPred (ℤ.min (negsuc m) (negsuc n))))
                                        (min-≤ {m = negsuc m} {n = negsuc n}))

≤Dec : ∀ m n → Dec (m ≤ n)
≤Dec (pos zero) (pos n) = yes zero-≤pos
≤Dec (pos (suc m)) (pos zero) = no ¬-pos<-zero
≤Dec (pos (suc m)) (pos (suc n)) with ≤Dec (pos m) (pos n)
... | yes m≤n = yes (suc-≤-suc m≤n)
... | no m≰n = no λ m+1≤n+1 → m≰n (pred-≤-pred m+1≤n+1)
≤Dec (pos m) (negsuc n) = no λ m≤n → ¬-pos<-zero (≤<-trans m≤n negsuc<-zero)
≤Dec (negsuc m) (pos n) = yes (isTrans≤ negsuc<-zero zero-≤pos)
≤Dec (negsuc zero) (negsuc zero) = yes isRefl≤
≤Dec (negsuc zero) (negsuc (suc n)) = no λ nsz≤nssn → ¬-pos<-zero (pos-≤-pos nsz≤nssn)
≤Dec (negsuc (suc m)) (negsuc zero) = yes (pred-≤-pred negsuc<-zero)
≤Dec (negsuc (suc m)) (negsuc (suc n)) with ≤Dec (negsuc m) (negsuc n)
... | yes m≤n = yes (pred-≤-pred m≤n)
... | no m≰n = no λ m+1≤n+1 → m≰n (suc-≤-suc m+1≤n+1)

≤Stable : ∀ m n → Stable (m ≤ n)
≤Stable m n = Dec→Stable (≤Dec m n)

<Dec : ∀ m n → Dec (m < n)
<Dec m n = ≤Dec (sucℤ m) n

<Stable : ∀ m n → Stable (m < n)
<Stable m n = Dec→Stable (<Dec m n)

Trichotomy-suc : Trichotomy m n → Trichotomy (sucℤ m) (sucℤ n)
Trichotomy-suc (lt m<n) = lt (suc-≤-suc m<n)
Trichotomy-suc (eq m≡n) = eq (cong sucℤ m≡n)
Trichotomy-suc (gt n<m) = gt (suc-≤-suc n<m)

Trichotomy-pred : Trichotomy (sucℤ m) (sucℤ n) → Trichotomy m n
Trichotomy-pred (lt m<n) = lt (pred-≤-pred m<n)
Trichotomy-pred {m} {n} (eq m≡n) = eq (sym (predSuc m)
                                      ∙ cong predℤ m≡n
                                      ∙ predSuc n)
Trichotomy-pred (gt n<m) = gt (pred-≤-pred n<m)

_≟_ : ∀ m n → Trichotomy m n
pos zero ≟ pos zero = eq refl
pos zero ≟ pos (suc n) = lt (suc-≤-suc zero-≤pos)
pos (suc m) ≟ pos zero = gt (suc-≤-suc zero-≤pos)
pos (suc m) ≟ pos (suc n) = Trichotomy-suc (pos m ≟ pos n)
pos m ≟ negsuc n = gt (<≤-trans negsuc<-zero zero-≤pos)
negsuc m ≟ pos n = lt (<≤-trans negsuc<-zero zero-≤pos)
negsuc zero ≟ negsuc zero = eq refl
negsuc zero ≟ negsuc (suc n) = gt (negsuc-≤-negsuc zero-≤pos)
negsuc (suc m) ≟ negsuc zero = lt (negsuc-≤-negsuc zero-≤pos)
negsuc (suc m) ≟ negsuc (suc n) = Trichotomy-pred (negsuc m ≟ negsuc n)
