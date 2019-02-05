{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Int.Properties where

open import Cubical.Core.Everything

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Data.Empty
open import Cubical.Data.Nat hiding (_+_ ; +-assoc)
open import Cubical.Data.Sum
open import Cubical.Data.Int.Base

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq

sucPred : ∀ i → sucInt (predInt i) ≡ i
sucPred (pos zero)       = refl
sucPred (pos (suc n))    = refl
sucPred (negsuc zero)    = refl
sucPred (negsuc (suc n)) = refl

predSuc : ∀ i → predInt (sucInt i) ≡ i
predSuc (pos zero)       = refl
predSuc (pos (suc n))    = refl
predSuc (negsuc zero)    = refl
predSuc (negsuc (suc n)) = refl

suc-equiv : Int ≃ Int
suc-equiv = (sucInt , isoToIsEquiv sucInt predInt sucPred predSuc)

sucPathInt : Int ≡ Int
sucPathInt = ua suc-equiv

-- TODO: define multiplication by composing the addition equivalence
-- with itself.

private
  -- TODO: can we change this so that it's the proof suc-equiv?
  coherence : (n : Int) → Path (Path Int (sucInt (predInt (sucInt n))) (sucInt n))
                               (sucPred (sucInt n))
                               (cong sucInt (predSuc n))
  coherence (pos zero) = refl
  coherence (pos (suc n)) = refl
  coherence (negsuc zero) = refl
  coherence (negsuc (suc zero)) = refl
  coherence (negsuc (suc (suc n))) = refl

-- Some tests
private
  one : Int
  one = transport (λ i → sucPathInt i) (pos 0)

  onepath : one ≡ pos 1
  onepath = refl

  minusone : Int
  minusone = transport (λ i → sucPathInt (~ i)) (pos 0)

  minusonepath : minusone ≡ negsuc 0
  minusonepath = refl

injPos : ∀ {a b : ℕ} → pos a ≡ pos b → a ≡ b
injPos {a} h = subst T h refl
  where
  T : Int → Set
  T (pos x)    = a ≡ x
  T (negsuc _) = ⊥

injNegsuc : ∀ {a b : ℕ} → negsuc a ≡ negsuc b → a ≡ b
injNegsuc {a} h = subst T h refl
  where
  T : Int → Set
  T (pos _) = ⊥
  T (negsuc x) = a ≡ x

posNotnegsuc : ∀ (a b : ℕ) → ¬ (pos a ≡ negsuc b)
posNotnegsuc a b h = subst T h 0
  where
  T : Int → Set
  T (pos _)    = ℕ
  T (negsuc _) = ⊥

negsucNotpos : ∀ (a b : ℕ) → ¬ (negsuc a ≡ pos b)
negsucNotpos a b h = subst T h 0
  where
  T : Int → Set
  T (pos _)    = ⊥
  T (negsuc _) = ℕ

discreteInt : Discrete Int
discreteInt (pos n) (pos m) with discreteℕ n m
... | yes p = yes (cong pos p)
... | no p  = no (λ x → p (injPos x))
discreteInt (pos n) (negsuc m) = no (posNotnegsuc n m)
discreteInt (negsuc n) (pos m) = no (negsucNotpos n m)
discreteInt (negsuc n) (negsuc m) with discreteℕ n m
... | yes p = yes (cong negsuc p)
... | no p  = no (λ x → p (injNegsuc x))

isSetInt : isSet Int
isSetInt = Discrete→isSet discreteInt

-- Compose sucPathInt with itself n times. Transporting along this
-- will be addition, transporting with it backwards will be
-- subtraction.

addEq : ℕ → Int ≡ Int
addEq zero = refl
addEq (suc n) = compPath (addEq n) sucPathInt

subEq : ℕ → Int ≡ Int
subEq n i = addEq n (~ i)

_+_ : Int → Int → Int
m + pos n    = transport (addEq n) m
m + negsuc n = transport (subEq (suc n)) m

_-_ : Int → Int → Int
m - pos zero    = m
m - pos (suc n) = m + negsuc n
m - negsuc n    = m + pos (suc n)

-- We directly get that addition by a fixed number is an equivalence
-- without having to do any induction!
isEquivAddInt : (m : Int) → isEquiv (λ n → n + m)
isEquivAddInt (pos n)    = isEquivTransport (addEq n)
isEquivAddInt (negsuc n) = isEquivTransport (subEq (suc n))

-- TODO: define multiplication by composing the addition equivalence
-- with itself.

private
  +negsuc : ℕ → (Int → Int)
  +negsuc 0 = predInt
  +negsuc (suc n) z = predInt (+negsuc n z)

  L0 : ∀ n z → +negsuc (suc n) z ≡ +negsuc n (predInt z)
  L0 0 z = refl
  L0 (suc n) z = cong predInt (L0 n z)

  Lnegsuc : ∀ n z → z + negsuc n ≡ +negsuc n z
  Lnegsuc 0 z = refl
  Lnegsuc (suc n) z = compPath (Lnegsuc n (predInt z)) (sym (L0 n z))

  L' : ∀ m n → m + (negsuc (suc n)) ≡ predInt (m + negsuc n)
  L' m n = compPath (Lnegsuc (suc n) m) (cong predInt (sym (Lnegsuc n m)))

  L3- : ∀ m n → m + (sucInt (negsuc n)) ≡ sucInt (m + (negsuc n))
  L3- m 0 = sym (sucPred m)
  L3- m (suc n) = compPath (sym (sucPred _)) (cong sucInt (sym (L' m n)))
  
  Lsuc : ∀ m n → m + (sucInt n) ≡ sucInt (m + n)
  Lsuc m (pos n)    = refl
  Lsuc m (negsuc n) = L3- m n

  Lpred : ∀ m n → m + (predInt n) ≡ predInt (m + n)
  Lpred m (pos zero)    = refl
  Lpred m (pos (suc n)) = sym (predSuc _)
  Lpred m (negsuc n)    = L' m n

  ind-assoc : {A : Set} (_·_ : A → A → A) (f : ℕ → A)
        (g : A → A) (p : ∀ a b → a · (g b) ≡ g (a · b))
        (q : ∀ {c} → f (suc c) ≡ g (f c))
        (base : ∀ m n → m · (n · (f 0)) ≡ (m · n) · (f 0))
        (m n : A) (o : ℕ)
      → m · (n · (f o)) ≡ (m · n) · (f o)
  ind-assoc _·_ f g p q base m n 0 = base m n
  ind-assoc _·_ f g p q base m n (suc o) = 
    m · (n · (f (suc o))) ≡⟨ cong (_·_ m) (cong (_·_ n) q) ⟩
    m · (n · (g (f o)))   ≡⟨ cong (_·_ m) (p n (f o))⟩
    m · (g (n · (f o)))   ≡⟨ p m (n · (f o))⟩
    g (m · (n · (f o)))   ≡⟨ cong g (assoc m n o)⟩
    g ((m · n) · (f o))   ≡⟨ sym (p (m · n) (f o)) ⟩
    (m · n) · (g (f o))   ≡⟨ cong (_·_ (m · n)) (sym q)⟩
    (m · n) · (f (suc o)) ∎
    where
    assoc = ind-assoc _·_ f g p q base

+-assoc : ∀ m n o → m + (n + o) ≡ (m + n) + o
+-assoc m n (pos o) = ind-assoc _+_ pos sucInt Lsuc refl (λ _ _ → refl) m n o
+-assoc m n (negsuc o) = ind-assoc _+_ negsuc predInt Lpred refl Lpred m n o

private
  +pos : ℕ → Int → Int
  +pos 0 z = z
  +pos (suc n) z = sucInt (+pos n z)

  L0+ : ∀ n z → +pos (suc n) z ≡ +pos n (sucInt z)
  L0+ zero z = refl
  L0+ (suc n) z = cong sucInt (L0+ n z)

  Lpos : ∀ n z → z + pos n ≡ +pos n z
  Lpos zero z = refl
  Lpos (suc n) z = cong sucInt (Lpos n z)

  ind-comm : {A : Set} (_·_ : A → A → A) (f g : ℕ → A) (p q : A → A)
             (fp : {z : A} {n : ℕ} → z · (f (suc n)) ≡ p (z · f n))
             (gq : {z : A} {n : ℕ} → z · (g (suc n)) ≡ q (z · g n))
             (qp : {z : A} → q (p z) ≡ p (q z))
             (base : ∀ {n} → f 0 · g n ≡ g n · f 0)
             (base' : ∀ {n} → f n · g 0 ≡ g 0 · f n)
             → ∀ m n → (f m) · (g n) ≡ (g n) · (f m)
  ind-comm _·_ f g p q fp gq qp base base' 0 n = base
  ind-comm _·_ f g p q fp gq qp base base' (suc m) 0 = base'
  ind-comm _·_ f g p q fp gq qp base base' (suc m) (suc n) = 
    f (suc m) · g (suc n)  ≡⟨ gq ⟩
    q ( f (suc m) · g n)   ≡⟨ cong q (comm (suc m) n) ⟩
    q ( g n · f (suc m))   ≡⟨ cong q (fp {n = m})⟩
    q ( p (g n · f m))     ≡⟨ qp ⟩
    p ( q (g n · f m))     ≡⟨ cong p (cong q (sym (comm m n))) ⟩
    p ( q (f m · g n))     ≡⟨ cong p (sym gq) ⟩
    p ( f m · g (suc n))   ≡⟨ cong p (comm m (suc n)) ⟩
    p ( g (suc n) · f m)   ≡⟨ sym (fp {n = m} )⟩
    g (suc n) · f (suc m)  ∎
    where
    comm = ind-comm _·_ f g p q fp gq qp base base'

  L++base : ∀ {n} → pos 0 + pos n ≡ pos n
  L++base {0} = refl
  L++base {suc n} = cong sucInt (L++base {n})

  L+-base : ∀ {n} → pos 0 + negsuc n ≡ negsuc n + pos 0
  L+-base {0} = refl
  L+-base {suc n} = compPath (L' (pos 0) n) (cong predInt (L+-base {n}))

  L-+base : ∀ {n} → negsuc 0 + pos n ≡ pos n + negsuc 0
  L-+base {zero} = refl
  L-+base {suc n} = 
    negsuc 0 + pos (suc n)  ≡⟨ Lpos (suc n) (negsuc 0)⟩
    +pos (suc n) (negsuc 0) ≡⟨ L0+ n _ ⟩
    +pos n (pos 0)          ≡⟨ sym (Lpos n (pos 0)) ⟩
    pos 0 + pos n           ≡⟨ L++base ⟩ 
    pos (suc n) + negsuc 0 ∎
    
  L--base : ∀ {n} → negsuc 0 + negsuc n ≡ negsuc n + negsuc 0
  L--base {0} = refl
  L--base {suc n} = compPath (Lpred (negsuc 0) (negsuc n)) (cong predInt (L--base {n}))

+-comm : ∀ m n → m + n ≡ n + m
+-comm (pos m) (pos n) =
  ind-comm _+_ pos pos sucInt sucInt refl refl refl L++base (sym L++base) m n
+-comm (pos m) (negsuc n) =
  ind-comm _+_ pos negsuc sucInt predInt refl (λ {z n} → L' z n)
    (λ {z} → compPath (predSuc z) (sym (sucPred z))) L+-base (sym L-+base) m n
+-comm (negsuc m) (pos n)    =
  ind-comm _+_ negsuc pos predInt sucInt (λ {z n} → L' z n) refl
    (λ {z} → compPath (sucPred z) (sym (predSuc z))) L-+base (sym L+-base) m n
+-comm (negsuc m) (negsuc n) =
  ind-comm _+_ negsuc negsuc predInt predInt (λ {z n} → L' z n) (λ {z n} → L' z n)
    refl L--base (sym L--base) m n
