module Cubical.Data.Int.Fast.Order where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Binary.Order.Pseudolattice.Instances.Nat renaming (
  ℕ≤Pseudolattice to ℕ≤)

open import Cubical.Data.Empty as ⊥ using (⊥)

open import Cubical.Data.Bool.Base hiding (_≟_)

open import Cubical.Data.Int.Fast.Base as ℤ
open import Cubical.Data.Int.Fast.Properties as ℤ
open import Cubical.Data.Nat as ℕ hiding (_<ᵇ_)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Nat.Order.Recursive as ℕrec using ()
open import Cubical.Data.NatPlusOne.Base as ℕ₊₁
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary

infix 4 _≤_ _<_ _≥_ _>_

_≤_ : ℤ → ℤ → Type₀
m ≤ n = Σ[ k ∈ ℕ ] m ℤ.+ pos k ≡ n

_<_ : ℤ → ℤ → Type₀
m < n = sucℤ m ≤ n

_≥_ : ℤ → ℤ → Type₀
m ≥ n = n ≤ m

_>_ : ℤ → ℤ → Type₀
m > n = n < m

-- Recursive order

_≤ᵗ_ : ℤ → ℤ → Type₀
pos m    ≤ᵗ pos n    = m ℕrec.≤ n
pos m    ≤ᵗ negsuc n = ⊥
negsuc m ≤ᵗ pos n    = Unit
negsuc m ≤ᵗ negsuc n = n ℕrec.≤ m

_<ᵗ_ : ℤ → ℤ → Type₀
pos m    <ᵗ pos n    = m ℕrec.< n
pos m    <ᵗ negsuc n = ⊥
negsuc m <ᵗ pos n    = Unit
negsuc m <ᵗ negsuc n = n ℕrec.< m

_≥ᵗ_ : ℤ → ℤ → Type₀
m ≥ᵗ n = n ≤ᵗ m

_>ᵗ_ : ℤ → ℤ → Type₀
m >ᵗ n = n <ᵗ m

-- Boolen order

_<ᵇ_ : ℤ → ℤ → Bool
pos m    <ᵇ pos n    = m ℕ.<ᵇ n
pos m    <ᵇ negsuc n = false
negsuc m <ᵇ pos n    = true
negsuc m <ᵇ negsuc n = n ℕ.<ᵇ m

_≤ᵇ_ : ℤ → ℤ → Bool
pos m    ≤ᵇ pos n    = m ℕ.≤ᵇ n
pos m    ≤ᵇ negsuc n = false
negsuc m ≤ᵇ pos n    = true
negsuc m ≤ᵇ negsuc n = n ℕ.≤ᵇ m

_>ᵇ_ : ℤ → ℤ → Bool
m >ᵇ n = n <ᵇ m

_≥ᵇ_ : ℤ → ℤ → Bool
m ≥ᵇ n = n ≤ᵇ m

-- The recursive and boolean order normalize in the same way:
≤ᵗ≡≤ᵇ : ∀ x y → x ≤ᵗ y ≡ Bool→Type (x ≤ᵇ y)
≤ᵗ≡≤ᵇ (pos zero)       (pos n)          = refl
≤ᵗ≡≤ᵇ (pos (suc m))    (pos zero)       = refl
≤ᵗ≡≤ᵇ (pos (suc m))    (pos (suc n))    = ≤ᵗ≡≤ᵇ (pos m) (pos n)
≤ᵗ≡≤ᵇ (pos m)          (negsuc n)       = refl
≤ᵗ≡≤ᵇ (negsuc m)       (pos n)          = refl
≤ᵗ≡≤ᵇ (negsuc m)       (negsuc zero)    = refl
≤ᵗ≡≤ᵇ (negsuc zero)    (negsuc (suc n)) = refl
≤ᵗ≡≤ᵇ (negsuc (suc m)) (negsuc (suc n)) = ≤ᵗ≡≤ᵇ (negsuc m) (negsuc n)

data Trichotomy (m n : ℤ) : Type₀ where
  lt : m < n → Trichotomy m n
  eq : m ≡ n → Trichotomy m n
  gt : n < m → Trichotomy m n

private
  variable
    m n o s : ℤ
    k l : ℕ

private
  witness-prop : ∀ j → isProp (m ℤ.+ pos j ≡ n)
  witness-prop {m} {n} j = isSetℤ (m ℤ.+ pos j) n

isProp≤ : isProp (m ≤ n)
isProp≤ {m} {n} (k , p) (l , q)
  = Σ≡Prop (witness-prop {m} {n}) lemma
  where
    lemma : k ≡ l
    lemma = injPos (inj-z+ {m} {pos k} {pos l} (p ∙ sym q))

isProp< : isProp (m < n)
isProp< {m} = isProp≤ {sucℤ m}

-- this proof warrants the particular order of summands in the definition of order
zero-≤pos : 0 ≤ pos l
zero-≤pos {l} = l , refl

zero-<possuc : 0 < pos (suc l)
zero-<possuc {l} = l , refl

negsuc≤-zero : negsuc k ≤ 0
negsuc≤-zero {k} = suc k , nℕ-n≡0 k

¬-pos<-zero : ¬ (pos k) < 0
¬-pos<-zero {k} (i , p) = snotz (injPos (pos+ (suc k) i ∙ p))

negsuc<-zero : negsuc k < 0
negsuc<-zero {k} .fst = k
negsuc<-zero {k} .snd =
  sucℤ (negsuc k) ℤ.+ pos k    ≡⟨ sym (sucℤ+ (negsuc k) (pos k)) ⟩
  sucℤ (negsuc k ℤ.+ pos k)    ≡⟨ +sucℤ (negsuc k) (pos k) ⟩
  neg (suc k) ℤ.+ pos (suc k)  ≡⟨ -Cancel' (pos (suc k)) ⟩
  pos zero                     ∎

¬pos≤negsuc : ¬ (pos k) ≤ negsuc l
¬pos≤negsuc {k} {l} (i , p) = posNotnegsuc (k ℕ.+ i) l (pos+ k i ∙ p)

negsuc≤pos : negsuc k ≤ pos l
negsuc≤pos {k} {l} .fst = l ℕ.+ suc k
negsuc≤pos {k} {l} .snd = plusMinus (pos (suc k)) (pos l)

negsuc<pos : negsuc k < pos l
negsuc<pos {zero} {zero}   = 0 , refl
negsuc<pos {zero} {suc l}  = suc l , sym (pos0+ (pos (suc l)))
negsuc<pos {suc k} {zero}  = suc k , -Cancel' (pos (suc k))
negsuc<pos {suc k} {suc l} = suc k ℕ.+ suc l
                           , cong (negsuc k ℤ.+_) (pos+ (suc k) (suc l)) ∙
                             +Assoc (negsuc k) (pos (suc k)) (pos (suc l)) ∙
                             cong (ℤ._+ pos (suc l)) (-Cancel' (pos (suc k))) ∙
                             sym (pos0+ (pos (suc l)))

suc-≤-suc : m ≤ n → sucℤ m ≤ sucℤ n
suc-≤-suc {m} {n} (k , p) = k , (sym (sucℤ+pos k m) ∙ cong sucℤ p)

negsuc-≤-negsuc : pos k ≤ pos l → negsuc l ≤ negsuc k
negsuc-≤-negsuc {k} {l} (i , p) .fst = i
negsuc-≤-negsuc {k} {l} (i , p) .snd =
  negsuc l ℤ.+ pos i                ≡⟨ +Comm (negsuc l) (pos i) ⟩
  pos i ℤ.+ negsuc l                ≡⟨ -AntiComm (pos i) (pos (suc l)) ⟩
  - (pos (suc l) - pos i)           ≡⟨ sym $ cong (-_ ∘ (_- pos i) ∘ sucℤ) p ⟩
  - (pos (suc k) ℤ.+ pos i - pos i) ≡⟨ cong -_ (plusMinus (pos i) _) ⟩
  negsuc k                          ∎

pos-≤-pos : negsuc k ≤ negsuc l → pos l ≤ pos k
pos-≤-pos {k} {l} (i , p) .fst = i
pos-≤-pos {k} {l} (i , p) .snd =
  pos l ℤ.+ pos i                       ≡⟨ sym $ -Involutive _ ⟩
  - (- (pos l ℤ.+ pos i))               ≡⟨ cong -_ (-Dist+ (pos l) (pos i)) ⟩
  - (- pos l - pos i)                   ≡⟨ sym $ cong (-_ ∘ (_- _)) (sucℤ[negsuc]-pos l) ⟩
  - (sucℤ (negsuc l) - pos i)           ≡⟨ sym $ cong (-_ ∘ (_- _) ∘ sucℤ) p ⟩
  - (sucℤ (negsuc k ℤ.+ pos i) - pos i) ≡⟨ cong (-_ ∘ (_- _)) (sucℤ+ (negsuc k) _) ⟩
  - (sucℤ (negsuc k) ℤ.+ pos i - pos i) ≡⟨ cong -_ (plusMinus (pos i) (sucℤ (negsuc k))) ⟩
  - sucℤ (negsuc k)                     ≡⟨ cong -_ (sucℤ[negsuc]-pos k) ⟩
  - (- pos k)                           ≡⟨ -Involutive _ ⟩
  pos k                                 ∎

-- Conversions between natural, integer and boolean orders

ℕ≤→≤ : ∀ {m n} → m ℕ.≤ n → pos m ≤ pos n
ℕ≤→≤ {m} (i , p) = i , cong pos (+-comm m i ∙ p)

ℕ≤→negsuc≥negsuc : ∀ {m n} → m ℕ.≤ n → negsuc m ≥ negsuc n
ℕ≤→negsuc≥negsuc = negsuc-≤-negsuc ∘ ℕ≤→≤

≤→ℕ≤ : ∀ {m n} → pos m ≤ pos n → m ℕ.≤ n
≤→ℕ≤ {m} (i , p) = i , injPos (+Comm (pos i) (pos m) ∙ p)

negsuc≥negsuc→ℕ≤ : ∀ {m n} → negsuc m ≥ negsuc n → m ℕ.≤ n
negsuc≥negsuc→ℕ≤ = ≤→ℕ≤ ∘ pos-≤-pos

<ᵇ→< : Bool→Type (m <ᵇ n) → m < n
<ᵇ→< {pos m}          {pos n}          t = ℕ≤→≤ (ℕ.<ᵇ→< t)
<ᵇ→< {negsuc m}       {pos n}          t = negsuc<pos {m} {n}
<ᵇ→< {negsuc (suc m)} {negsuc zero}    t = negsuc-≤-negsuc zero-≤pos
<ᵇ→< {negsuc (suc m)} {negsuc (suc n)} t = ℕ≤→negsuc≥negsuc (ℕ.<ᵇ→< t)

<→<ᵇ : m < n → Bool→Type (m <ᵇ n)
<→<ᵇ {pos m}          {pos n}    = ℕ.≤→≤ᵇ ∘ ≤→ℕ≤
<→<ᵇ {pos m}          {negsuc n} = ¬pos≤negsuc
<→<ᵇ {negsuc m}       {pos n}    = λ _ → tt
<→<ᵇ {negsuc zero}    {negsuc n} = ¬pos≤negsuc
<→<ᵇ {negsuc (suc m)} {negsuc n} = ℕ.≤→≤ᵇ ∘ negsuc≥negsuc→ℕ≤

≤ᵇ→≤ : Bool→Type (m ≤ᵇ n) → m ≤ n
≤ᵇ→≤ {pos m}    {pos n}    t = ℕ≤→≤ (ℕ.≤ᵇ→≤ t)
≤ᵇ→≤ {negsuc m} {pos n}    t = negsuc≤pos
≤ᵇ→≤ {negsuc m} {negsuc n} t = ℕ≤→negsuc≥negsuc (ℕ.≤ᵇ→≤ t)

≤→≤ᵇ : m ≤ n → Bool→Type (m ≤ᵇ n)
≤→≤ᵇ {pos m}    {pos n}    = ℕ.≤→≤ᵇ ∘ ≤→ℕ≤
≤→≤ᵇ {pos m}    {negsuc n} = ¬pos≤negsuc
≤→≤ᵇ {negsuc m} {pos n}    = λ _ → tt
≤→≤ᵇ {negsuc m} {negsuc n} = ℕ.≤→≤ᵇ ∘ negsuc≥negsuc→ℕ≤

≤-+o : m ≤ n → m ℤ.+ o ≤ n ℤ.+ o
≤-+o {m} {n} {o} (i , p) .fst = i
≤-+o {m} {n} {o} (i , p) .snd =
  (m ℤ.+ o) ℤ.+ pos i  ≡⟨ sym (+Assoc m o (pos i)) ⟩
  m ℤ.+ (o ℤ.+ pos i)  ≡⟨ cong (m ℤ.+_) (+Comm o (pos i)) ⟩
  m ℤ.+ (pos i ℤ.+ o)  ≡⟨ +Assoc m (pos i) o ⟩
  (m ℤ.+ pos i) ℤ.+ o  ≡⟨ cong (ℤ._+ o) p ⟩
  n ℤ.+ o              ∎

≤SumRightPos : n ≤ pos k ℤ.+ n
≤SumRightPos {n} {k} = k , +Comm n (pos k)

≤-o+ : m ≤ n → o ℤ.+ m ≤ o ℤ.+ n
≤-o+ {m} {n} {o} = subst2 (_≤_) (+Comm m o) (+Comm n o) ∘ ≤-+o {m} {o = o}

≤SumLeftPos : n ≤ n ℤ.+ pos k
≤SumLeftPos {n} {k} = k , refl

pred-≤-pred : sucℤ m ≤ sucℤ n → m ≤ n
pred-≤-pred {m} {n} (k , p) .fst = k
pred-≤-pred {m} {n} (k , p) .snd =
  m ℤ.+ pos k              ≡⟨ sym $ cong (ℤ._+ pos k) (predSuc m) ⟩
  predℤ (sucℤ m) ℤ.+ pos k ≡⟨ sym $ predℤ+ (sucℤ m) (pos k) ⟩
  predℤ (sucℤ m ℤ.+ pos k) ≡⟨ cong predℤ p ⟩
  predℤ (sucℤ n)           ≡⟨ predSuc n ⟩
  n                        ∎

isRefl≤ : m ≤ m
isRefl≤ = 0 , +IdR _

≤-suc : m ≤ n → m ≤ sucℤ n
≤-suc {m} {n} (k , p) = suc k , sym (+sucℤ m (pos k)) ∙ cong sucℤ p

suc-< : sucℤ m < n → m < n
suc-< {m} {n} p = pred-≤-pred {sucℤ m} (≤-suc {sucℤ (sucℤ m)} p)

≤-sucℤ : n ≤ sucℤ n
≤-sucℤ {n} = ≤-suc {n} isRefl≤

≤-predℤ : predℤ n ≤ n
≤-predℤ {n} = 1 , sym (predℤ+ n 1) ∙ cong predℤ (+Comm n 1 ∙ sym (sucℤ≡1+ _)) ∙ predSuc n

isTrans≤ : m ≤ n → n ≤ o → m ≤ o
isTrans≤ {m} {n} {o} (i , p) (j , q) .fst = i ℕ.+ j
isTrans≤ {m} {n} {o} (i , p) (j , q) .snd =
  m ℤ.+ (pos i ℤ.+ pos j) ≡⟨ +Assoc m (pos i) (pos j) ⟩
  (m ℤ.+ pos i) ℤ.+ pos j ≡⟨ cong (ℤ._+ pos j) p ⟩
  n ℤ.+ pos j             ≡⟨ q ⟩
  o                       ∎

isAntisym≤ : m ≤ n → n ≤ m → m ≡ n
isAntisym≤ {m} {n} (i , p) (j , q) =
  sym (+IdR _) ∙ cong ((m ℤ.+_) ∘ pos) (injPos lemma₂) ∙ p
  where lemma₀ : pos (j ℕ.+ i) ℤ.+ m ≡ m
        lemma₀ = pos (j ℕ.+ i) ℤ.+ m    ≡⟨ sym (+Assoc (pos j) (pos i) m) ⟩
                 pos j ℤ.+ (pos i ℤ.+ m) ≡⟨ cong (pos j ℤ.+_) (+Comm (pos i) m) ⟩
                 pos j ℤ.+ (m ℤ.+ pos i) ≡⟨ cong (pos j ℤ.+_) p ⟩
                 pos j ℤ.+ n             ≡⟨ +Comm (pos j) n ⟩
                 n ℤ.+ pos j             ≡⟨ q ⟩
                 m                       ∎
        lemma₁ : pos (j ℕ.+ i) ≡ 0
        lemma₁ = n+z≡z→n≡0 (pos (j ℕ.+ i)) m lemma₀

        lemma₂ : 0 ≡ pos i
        lemma₂ = cong pos (sym (snd (m+n≡0→m≡0×n≡0 (injPos lemma₁))))

≤Monotone+ : m ≤ n → o ≤ s → m ℤ.+ o ≤ n ℤ.+ s
≤Monotone+ {m} {n} {o} p q = isTrans≤ {m ℤ.+ o} (≤-+o {m} {o = o} p) (≤-o+ {o = n} q)

≤-o+-cancel : o ℤ.+ m ≤ o ℤ.+ n → m ≤ n
≤-o+-cancel {o} {m} (i , p) = i , inj-z+ {z = o} (+Assoc o m (pos i) ∙ p)

≤-+o-cancel : m ℤ.+ o ≤ n ℤ.+ o → m ≤ n
≤-+o-cancel {m} {o} {n} (i , p) .fst = i
≤-+o-cancel {m} {o} {n} (i , p) .snd = inj-+z {z = o} $
  (m ℤ.+  pos i) ℤ.+ o  ≡⟨ sym (+Assoc m (pos i) o) ⟩
   m ℤ.+ (pos i  ℤ.+ o) ≡⟨ cong (m ℤ.+_) (+Comm (pos i) o) ⟩
   m ℤ.+ (o  ℤ.+ pos i) ≡⟨ +Assoc m o (pos i) ⟩
  (m ℤ.+  o) ℤ.+ pos i  ≡⟨ p ⟩
  n ℤ.+ o               ∎

≤-+pos-trans : m ℤ.+ pos k ≤ n → m ≤ n
≤-+pos-trans {m} {k} {n} p = isTrans≤ {m} (≤SumRightPos {m}) (subst (_≤ n) (+Comm m _) p)

≤-pos+-trans : pos k ℤ.+ m ≤ n → m ≤ n
≤-pos+-trans {k} {m} p = isTrans≤ {m} (≤SumRightPos {m}) p

≤-·o : m ≤ n → m ℤ.· (pos k) ≤ n ℤ.· (pos k)
≤-·o {m} {n} {k} (i , p) .fst = i ℕ.· k
≤-·o {m} {n} {k} (i , p) .snd =
  m ℤ.· pos k ℤ.+ pos i ℤ.· pos k ≡⟨ sym (·DistL+ m (pos i) (pos k)) ⟩
  (m ℤ.+ pos i) ℤ.· pos k         ≡⟨ cong (ℤ._· pos k) p ⟩
  n ℤ.· pos k                     ∎

0≤o→≤-·o : 0 ≤ o → m ≤ n → m ℤ.· o ≤ n ℤ.· o
0≤o→≤-·o {pos o}    {m} 0≤o m≤n = ≤-·o {m} {k = o} m≤n
0≤o→≤-·o {negsuc o} {m} 0≤o _   = ⊥.rec (¬pos≤negsuc 0≤o)

<-·o : m < n → m ℤ.· (pos (suc k)) < n ℤ.· (pos (suc k))
<-·o {m} {n} {k} (i , p) .fst = i ℕ.· suc k ℕ.+ k
<-·o {m} {n} {k} (i , p) .snd =
  sucℤ (m ℤ.· pos (suc k)) ℤ.+
    (pos i ℤ.· pos (suc k) ℤ.+ pos k)       ≡⟨ cong (sucℤ (m ℤ.· pos (suc k)) ℤ.+_)
                                               (+Comm (pos _) (pos k)) ⟩
  sucℤ (m ℤ.· pos (suc k)) ℤ.+
    (pos k ℤ.+ pos i ℤ.· pos (suc k))       ≡⟨ +Assoc (sucℤ (m ℤ.· pos _)) _ _ ⟩
  (sucℤ (m ℤ.· pos (suc k)) ℤ.+ pos k) ℤ.+
    pos i ℤ.· pos (suc k)                   ≡⟨ sym $ cong (ℤ._+ pos _)
                                                     (sucℤ+ (m ℤ.· pos _) _) ⟩
  sucℤ (m ℤ.· pos (suc k) ℤ.+ pos k) ℤ.+
    pos i ℤ.· pos (suc k)                   ≡⟨ cong (ℤ._+ pos _) (+sucℤ (m ℤ.· pos _) _) ⟩
  (m ℤ.· pos (suc k) ℤ.+ pos (suc k)) ℤ.+
    pos i ℤ.· pos (suc k)                   ≡⟨ cong (ℤ._+ pos _)
                                                (+Comm (m ℤ.· pos (suc k)) _) ⟩
  (pos (suc k) ℤ.+ m ℤ.· pos (suc k)) ℤ.+
    pos i ℤ.· pos (suc k)                   ≡⟨ sym $ cong (ℤ._+ pos _) (sucℤ· m _) ⟩
  (sucℤ m ℤ.· pos (suc k)) ℤ.+
    pos i ℤ.· pos (suc k)                   ≡⟨ sym $ ·DistL+ (sucℤ m) (pos i) _ ⟩
  ((sucℤ m) ℤ.+ pos i) ℤ.· pos (suc k)      ≡⟨ cong (ℤ._· pos _) p ⟩
  n ℤ.· pos (suc k)                                              ∎

<-o+-cancel : o ℤ.+ m < o ℤ.+ n → m < n
<-o+-cancel {o} {m} {n} = ≤-o+-cancel {o} ∘ subst (_≤ o ℤ.+ n) (+sucℤ o m)

<-weaken : m < n → m ≤ n
<-weaken {m} (i , p) = (suc i) , sym (+sucℤ m (pos i)) ∙ sucℤ+ m (pos i) ∙ p

isIrrefl< : ¬ m < m
isIrrefl< {pos zero}       (i , p) = snotz (injPos p)
isIrrefl< {pos (suc n)}    (i , p) = isIrrefl< {pos n} (i , cong predℤ p)
isIrrefl< {negsuc zero}    (i , p) = posNotnegsuc i 0 p
isIrrefl< {negsuc (suc n)} (i , p) = isIrrefl< {negsuc n} (i ,
                                     sym (sucℤ+ (negsuc n) _) ∙ cong sucℤ p)

0<o→<-·o : 0 < o → m < n → m ℤ.· o < n ℤ.· o
0<o→<-·o {pos zero}        0<o _   = ⊥.rec (isIrrefl< 0<o)
0<o→<-·o {pos (suc o)} {m} _   m<n = <-·o {m} {k = o} m<n
0<o→<-·o {negsuc o}        0<o _   = ⊥.rec (¬pos≤negsuc (<-weaken {0} {negsuc o} 0<o))

pos≤0→≡0 : pos k ≤ 0 → pos k ≡ 0
pos≤0→≡0 {zero} _ = refl
pos≤0→≡0 {suc k} p = ⊥.rec (¬-pos<-zero {k = k} p)

predℤ-≤-predℤ : m ≤ n → predℤ m ≤ predℤ n
predℤ-≤-predℤ {m} {n} (i , p) .fst = i
predℤ-≤-predℤ {m} {n} (i , p) .snd =
  predℤ m ℤ.+ pos i   ≡⟨ sym (predℤ+ m _) ⟩
  predℤ (m ℤ.+ pos i) ≡⟨ cong predℤ p ⟩
  predℤ n             ∎

¬m+posk<m : ¬ m ℤ.+ pos k < m
¬m+posk<m {m} {k} = ¬-pos<-zero ∘ <-o+-cancel {o = m} {m = pos k} {n = 0}
                  ∘ subst (m ℤ.+ pos k <_) (+pos0 m)

≤<-trans : o ≤ m → m < n → o < n
≤<-trans {o} p = isTrans≤ {sucℤ o} (suc-≤-suc {o} p)

<≤-trans : o < m → m ≤ n → o < n
<≤-trans {o} = isTrans≤ {sucℤ o}

isTrans< : o < m → m < n → o < n
isTrans< {o} p = ≤<-trans {o} (<-weaken {o} p)

isAsym< : m < n → ¬ n ≤ m
isAsym< {m} m<n = isIrrefl< ∘ <≤-trans {m} m<n

<-+o : m < n → m ℤ.+ o < n ℤ.+ o
<-+o {m} {n} {o} = subst (_≤ n ℤ.+ o) (sym (sucℤ+ m o)) ∘ ≤-+o {sucℤ m} {o = o}

<-o+ : m < n → o ℤ.+ m < o ℤ.+ n
<-o+ {m} {n} {o} = subst (_≤ o ℤ.+ n) (sym (+sucℤ o m)) ∘ ≤-o+ {o = o}

<-+pos-trans : m ℤ.+ pos k < n → m < n
<-+pos-trans {m} {k} = ≤<-trans {m} (k , refl)

<-pos+-trans : pos k ℤ.+ m < n → m < n
<-pos+-trans {k} {m} = ≤<-trans {m} (k , (+Comm m (pos k)))

<Monotone+ : m < n → o < s → m ℤ.+ o < n ℤ.+ s
<Monotone+ {m} {n} {o} m<n o<s = isTrans< {m ℤ.+ o} (<-+o {m} m<n) (<-o+ {o} {o = n} o<s)

<-+-≤ : m < n → o ≤ s → m ℤ.+ o < n ℤ.+ s
<-+-≤ {m} {n} {o} m<n o≤s = <≤-trans {m ℤ.+ o} (<-+o {m} m<n) (≤-o+ {o = n} o≤s)

-pos≤ : m - (pos k) ≤ m
-pos≤ {m} {k} = k , minusPlus (pos k) m

·suc≤0 : m ℤ.· (pos (suc k)) ≤ 0 → m ≤ 0
·suc≤0 {pos n} {k} (i , p) .fst = n ℕ.· k ℕ.+ i
·suc≤0 {pos n} {k} (i , p) .snd =
  pos (n ℕ.+ (n ℕ.· k ℕ.+ i))  ≡⟨ +Assoc (pos n) (pos n ℤ.· pos k) (pos i) ⟩
  pos (n ℕ.+ n ℕ.· k ℕ.+ i)    ≡⟨ sym $ cong (pos ∘ (ℕ._+ i)) (·-suc n k) ⟩
  pos (n ℕ.· suc k ℕ.+ i)      ≡⟨ p ⟩
  0                             ∎
·suc≤0 {negsuc n} {k} _ = negsuc≤-zero

·suc<0 : m ℤ.· (pos (suc k)) < 0 → m < 0
·suc<0 {pos n}    = ⊥.rec ∘ ¬-pos<-zero
·suc<0 {negsuc n} = λ _ → negsuc<-zero {n}

≤-·o-cancel : m ℤ.· (pos (suc k)) ≤ n ℤ.· (pos (suc k)) → m ≤ n
≤-·o-cancel {m} {k} {n} mk≤nk = subst2 _≤_ (minusPlus n m) (+IdL n) $
  ≤-+o {m - n} $ ·suc≤0 {m - n} $ subst2 (_≤_)
    (sym (·DistL+ m (- n) (pos (suc k))))
    (cong (n ℤ.· pos _ ℤ.+_) (sym (-DistL· n (pos _))) ∙ -Cancel (n ℤ.· pos _))
    (≤-+o {m ℤ.· pos (suc k)} {n ℤ.· pos (suc k)} {(- n) ℤ.· pos (suc k)} mk≤nk)

0<o→≤-·o-cancel : 0 < o → m ℤ.· o ≤ n ℤ.· o → m ≤ n
0<o→≤-·o-cancel {pos zero}        0<o _     = ⊥.rec (isIrrefl< 0<o)
0<o→≤-·o-cancel {pos (suc o)} {m} _   mo≤no = ≤-·o-cancel {m} {o} mo≤no
0<o→≤-·o-cancel {negsuc o}        0<o _     = ⊥.rec (¬pos≤negsuc 0<o)

≤-o·-cancel : (pos (suc k)) ℤ.· m ≤ (pos (suc k)) ℤ.· n → m ≤ n
≤-o·-cancel {k} {m} {n} = ≤-·o-cancel {m} {k} {n} ∘ (subst2 _≤_ (·Comm _ m) (·Comm _ n))

<-·o-cancel : m ℤ.· (pos (suc k)) < n ℤ.· (pos (suc k)) → m < n
<-·o-cancel {m} {k} {n} mk<nk = subst2 _<_ (minusPlus n m) (+IdL n) $
  <-+o {m - n} $ ·suc<0 {m - n} $ subst2 _<_
    (sym (·DistL+ m (- n) (pos (suc k))))
    (cong (n ℤ.· pos _ ℤ.+_) (sym (-DistL· n (pos _))) ∙ -Cancel (n ℤ.· pos _))
    (<-+o {m ℤ.· pos (suc k)} {n ℤ.· pos (suc k)} {(- n) ℤ.· pos (suc k)} mk<nk)

0<o→<-·o-cancel : 0 < o → m ℤ.· o < n ℤ.· o → m < n
0<o→<-·o-cancel {pos zero}        0<o _     = ⊥.rec (isIrrefl< 0<o)
0<o→<-·o-cancel {pos (suc o)} {m} _   mo<no = <-·o-cancel {m} {o} mo<no
0<o→<-·o-cancel {negsuc o}        0<o _     = ⊥.rec (¬pos≤negsuc 0<o)

<-o·-cancel : (pos (suc k)) ℤ.· m < (pos (suc k)) ℤ.· n → m < n
<-o·-cancel {k} {m} {n} = <-·o-cancel {m} ∘ (subst2 _<_ (·Comm (pos (suc k)) m) (·Comm (pos (suc k)) n))

-Dist≤ : m ≤ n → (- n) ≤ (- m)
-Dist≤ {pos zero}       {pos zero}    = λ _ → isRefl≤
-Dist≤ {pos zero}       {pos (suc n)} = λ _ → negsuc≤-zero
-Dist≤ {pos (suc m)}    {pos zero}    = ⊥.rec ∘ snotz ∘ injPos ∘ pos≤0→≡0
-Dist≤ {pos (suc m)}    {pos (suc n)} = negsuc-≤-negsuc ∘ pred-≤-pred {pos m} {pos n}
-Dist≤ {pos m}          {negsuc n}    = ⊥.rec ∘ ¬pos≤negsuc
-Dist≤ {negsuc zero}    {pos zero}    = λ _ → zero-≤pos
-Dist≤ {negsuc zero}    {pos (suc n)} = λ _ → negsuc≤pos
-Dist≤ {negsuc (suc m)} {pos zero}    = λ _ → zero-≤pos
-Dist≤ {negsuc (suc m)} {pos (suc n)} = λ _ → negsuc≤pos
-Dist≤ {negsuc m}       {negsuc n}    = suc-≤-suc {pos n} {pos m} ∘ pos-≤-pos

-Dist< : m < n → (- n) < (- m)
-Dist< {m} {n} = subst (- n <_) (cong sucℤ (-sucℤ m) ∙ sucPred (- m))
               ∘ suc-≤-suc { - n} { - sucℤ m}
               ∘ -Dist≤ {sucℤ m} {n}

≤max : m ≤ ℤ.max m n
≤max {pos m}    {pos n}     = ℕ≤→≤ ℕ.left-≤-max
≤max {pos m}    {negsuc n}  = isRefl≤
≤max {negsuc m} {pos n}     = negsuc≤pos
≤max {negsuc m} {negsuc n}  = ℕ≤→negsuc≥negsuc ℕ.min-≤-left

≤→max : m ≤ n → ℤ.max m n ≡ n
≤→max {pos m}    {pos n}    = cong pos ∘ ∨Comm ℕ≤ {m} {n} ∙_ ∘ sym ∘ ≤→∨ ℕ≤ ∘ ≤→ℕ≤
≤→max {pos m}    {negsuc n} = ⊥.rec ∘ ¬pos≤negsuc
≤→max {negsuc m} {pos n}    = λ _ → refl
≤→max {negsuc m} {negsuc n} = cong negsuc ∘ ∧Comm ℕ≤ {m} {n} ∙_
                            ∘ sym ∘ ≤→∧ ℕ≤ ∘ negsuc≥negsuc→ℕ≤

min≤ : ℤ.min m n ≤ m
min≤ {pos m}    {pos n}    = ℕ≤→≤ ℕ.min-≤-left
min≤ {pos m}    {negsuc n} = negsuc≤pos
min≤ {negsuc m} {pos n}    = isRefl≤
min≤ {negsuc m} {negsuc n} = ℕ≤→negsuc≥negsuc ℕ.left-≤-max

≤→min : m ≤ n → ℤ.min m n ≡ m
≤→min {pos m}    {pos n}    = cong pos ∘ sym ∘ ≤→∧ ℕ≤ ∘ ≤→ℕ≤
≤→min {pos m}    {negsuc n} = ⊥.rec ∘ ¬pos≤negsuc
≤→min {negsuc m} {pos n}    = λ _ → refl
≤→min {negsuc m} {negsuc n} = cong negsuc ∘ sym ∘ ≤→∨ ℕ≤ ∘ negsuc≥negsuc→ℕ≤

≤MonotoneMin : m ≤ n → o ≤ s → ℤ.min m o ≤ ℤ.min n s
≤MonotoneMin {m} {n} {o} {s} m≤n o≤s
  = subst (_≤ ℤ.min n s)
          (sym (minAssoc n s (ℤ.min m o)) ∙
           cong (ℤ.min n) (minAssoc s m o ∙
                           cong (λ a → ℤ.min a o) (ℤ.minComm s m) ∙
                                 sym (minAssoc m s o)) ∙
                           minAssoc n m (ℤ.min s o) ∙
           cong₂ ℤ.min (ℤ.minComm n m ∙ ≤→min m≤n)
                       (ℤ.minComm s o ∙ ≤→min o≤s))
           (min≤ {m = ℤ.min n s} {n = ℤ.min m o})

≤MonotoneMax : m ≤ n → o ≤ s → ℤ.max m o ≤ ℤ.max n s
≤MonotoneMax {m} {n} {o} {s} m≤n o≤s
  = subst (ℤ.max m o ≤_)
          (sym (maxAssoc m o (ℤ.max n s)) ∙
           cong (ℤ.max m) (maxAssoc o n s ∙
                           cong (λ a → ℤ.max a s) (ℤ.maxComm o n) ∙
                                 sym (maxAssoc n o s)) ∙
                           maxAssoc m n (ℤ.max o s) ∙
           cong₂ ℤ.max (≤→max m≤n) (≤→max o≤s))
          (≤max {m = ℤ.max m o} {n = ℤ.max n s})

0<+ : ∀ m n → 0 < m ℤ.+ n → (0 < m) ⊎ (0 < n)
0<+ (pos zero)    (pos zero)    = ⊥.rec ∘ isIrrefl<
0<+ (pos zero)    (pos (suc n)) = inr
0<+ (pos (suc m)) (pos n)       = λ _ → inl (suc-≤-suc {0} zero-≤pos)
0<+ (pos zero)    (negsuc n)    = ⊥.rec ∘ ¬pos≤negsuc
0<+ (pos (suc m)) (negsuc n)    = λ _ → inl (suc-≤-suc {0} zero-≤pos)
0<+ (negsuc m)    (pos zero)    = ⊥.rec ∘ ¬pos≤negsuc
0<+ (negsuc m)    (pos (suc n)) = λ _ → inr (suc-≤-suc {0} zero-≤pos)
0<+ (negsuc m)    (negsuc n)    = ⊥.rec ∘ ¬pos≤negsuc

0<_ : ℤ → Type
0< pos zero = ⊥
0< pos (suc n) = Unit
0< negsuc n = ⊥

isProp0< : ∀ n → isProp (0< n)
isProp0< (pos (suc _)) _ _ = refl

·0< : ∀ m n → 0< m → 0< n → 0< (m ℤ.· n)
·0< (pos (suc m)) (pos (suc n)) _ _ = tt

0<·ℕ₊₁ : ∀ m n → 0< (m ℤ.· pos (ℕ₊₁→ℕ n)) → 0< m
0<·ℕ₊₁ (pos (suc m)) (1+ n) _ = tt

+0< : ∀ m n → 0< m → 0< n → 0< (m ℤ.+ n)
+0< (pos (suc m)) (pos (suc n)) _ _ = tt

0<→ℕ₊₁ : ∀ n → 0< n → Σ ℕ₊₁ λ m → n ≡ pos (ℕ₊₁→ℕ m)
0<→ℕ₊₁ (pos (suc n)) x = (1+ n) , refl

min-0< : ∀ m n → 0< m → 0< n → 0< (ℤ.min m n)
min-0< (pos (suc m)) (pos (suc n)) p q with m ℕ.<ᵇ n
... | false = tt
... | true  = tt

0≤x² : ∀ n → 0 ≤ n ℤ.· n
0≤x² (pos n)    = zero-≤pos
0≤x² (negsuc n) = zero-≤pos

≤Dec : ∀ m n → Dec (m ≤ n)
≤Dec (pos m)    (pos n)    with ℕ.≤Dec m n
... | yes p = yes (ℕ≤→≤ p)
... | no ¬p = no (¬p ∘ ≤→ℕ≤)
≤Dec (pos m)    (negsuc n) = no ¬pos≤negsuc
≤Dec (negsuc m) (pos n)    = yes negsuc≤pos
≤Dec (negsuc m) (negsuc n) with ℕ.≤Dec n m
... | yes p = yes (-Dist≤ (suc-≤-suc {pos n} (ℕ≤→≤ p)))
... | no ¬p = no (¬p ∘ negsuc≥negsuc→ℕ≤)

≤Stable : ∀ m n → Stable (m ≤ n)
≤Stable m n = Dec→Stable (≤Dec m n)

<Dec : ∀ m n → Dec (m < n)
<Dec m n = ≤Dec (sucℤ m) n

<Stable : ∀ m n → Stable (m < n)
<Stable m n = Dec→Stable (<Dec m n)

Trichotomy-suc : Trichotomy m n → Trichotomy (sucℤ m) (sucℤ n)
Trichotomy-suc {m}     (lt m<n) = lt (suc-≤-suc {sucℤ m} m<n)
Trichotomy-suc         (eq m≡n) = eq (cong sucℤ m≡n)
Trichotomy-suc {n = n} (gt n<m) = gt (suc-≤-suc {sucℤ n} n<m)

Trichotomy-pred : Trichotomy (sucℤ m) (sucℤ n) → Trichotomy m n
Trichotomy-pred {m}     (lt m<n) = lt (pred-≤-pred {sucℤ m} m<n)
Trichotomy-pred {m} {n} (eq m≡n) = eq (sym (predSuc m)
                                      ∙ cong predℤ m≡n
                                      ∙ predSuc n)
Trichotomy-pred {n = n} (gt n<m) = gt (pred-≤-pred {sucℤ n} n<m)

_≟_ : ∀ m n → Trichotomy m n
pos m    ≟ pos n    with m ℕ.≟ n
... | ℕ.lt m<n = lt (ℕ≤→≤ m<n)
... | ℕ.eq m≡n = eq (cong pos m≡n)
... | ℕ.gt m>n = gt (ℕ≤→≤ m>n)
pos m    ≟ negsuc n = gt (negsuc<pos {n})
negsuc m ≟ pos n    = lt (negsuc<pos {m})
negsuc m ≟ negsuc n with n ℕ.≟ m
... | ℕ.lt n<m = lt (-Dist< (suc-≤-suc {pos (suc n)} (ℕ≤→≤ n<m)))
... | ℕ.eq n≡m = eq (cong negsuc (sym n≡m))
... | ℕ.gt n>m = gt (-Dist< (suc-≤-suc {pos (suc m)} (ℕ≤→≤ n>m)))

-- alternative proof
_≟'_ : ∀ m n → Trichotomy m n
pos zero ≟' pos zero = eq refl
pos zero ≟' pos (suc n) = lt (suc-≤-suc {0} {pos n} zero-≤pos)
pos (suc m) ≟' pos zero = gt (suc-≤-suc {0} {pos m} zero-≤pos)
pos (suc m) ≟' pos (suc n) = Trichotomy-suc (pos m ≟' pos n)
pos m ≟' negsuc n = gt (negsuc<pos {n})
negsuc m ≟' pos n = lt (negsuc<pos {m})
negsuc zero ≟' negsuc zero = eq refl
negsuc zero ≟' negsuc (suc n) = gt (negsuc-≤-negsuc zero-≤pos)
negsuc (suc m) ≟' negsuc zero = lt (negsuc-≤-negsuc zero-≤pos)
negsuc (suc m) ≟' negsuc (suc n) = Trichotomy-pred (negsuc m ≟' negsuc n)

-- Raw comparisons, without the proof terms
compare : ℤ → ℤ → Ordering
compare m n with m ≟ n
... | lt _ = LT
... | eq _ = EQ
... | gt _ = GT

compare' : ℤ → ℤ → Ordering
compare' m n with m ≟' n
... | lt _ = LT
... | eq _ = EQ
... | gt _ = GT

private

  test₀ : compare -4294967296  4295967296 ≡ LT
  test₀ = refl

  test₁ : compare -4294967296 -4294967296 ≡ EQ
  test₁ = refl

  test₂ : compare -4294967296 -4295967296 ≡ GT
  test₂ = refl

  test₀' : compare' -4294967296  4295967296 ≡ LT
  test₀' = refl

  {- This would take much longer to typecheck:

  test₁' : compare' -4294967296 -4295967296 ≡ GT
  test₁' = refl

  test₂' : compare' -4294967296 -4295967296 ≡ GT
  test₂' = refl

  -}
