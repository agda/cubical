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

+pos : ℕ → Int → Int
+pos 0 z = z
+pos (suc n) z = sucInt (+pos n z)

+negsuc : ℕ → (Int → Int)
+negsuc 0 = predInt
+negsuc (suc n) z = predInt (+negsuc n z)

_+_ : Int → Int → Int
m + pos n = +pos n m
m + negsuc n = +negsuc n m

_-_ : Int → Int → Int
m - pos zero    = m
m - pos (suc n) = m + negsuc n
m - negsuc n    = m + pos (suc n)

sucInt+pos : ∀ n m → sucInt (+pos n m) ≡ +pos n (sucInt m)
sucInt+pos zero m = refl
sucInt+pos (suc n) m = cong sucInt (sucInt+pos n m)

predInt+negsuc : ∀ n m → predInt (+negsuc n m) ≡ +negsuc n (predInt m)
predInt+negsuc zero m = refl
predInt+negsuc (suc n) m = cong predInt (predInt+negsuc n m)

sucInt+negsuc : ∀ n m → sucInt (+negsuc n m) ≡ +negsuc n (sucInt m)
sucInt+negsuc zero m = compPath (sucPred _) (sym (predSuc _))
sucInt+negsuc (suc n) m =      _ ≡⟨ sucPred _ ⟩
  +negsuc n m                    ≡⟨ cong (+negsuc n) (sym (predSuc m)) ⟩
  +negsuc n (predInt (sucInt m)) ≡⟨ sym (predInt+negsuc n (sucInt m)) ⟩
  predInt (+negsuc n (sucInt m)) ∎

predInt+pos : ∀ n m → predInt (+pos n m) ≡ +pos n (predInt m)
predInt+pos zero m = refl
predInt+pos (suc n) m =     _ ≡⟨ predSuc _ ⟩
  +pos n m                    ≡⟨ cong (+pos n) (sym (sucPred _)) ⟩
  +pos n (sucInt (predInt m)) ≡⟨ sym (sucInt+pos n (predInt m))⟩
  _ ∎

predInt+ : ∀ m n → predInt (m + n) ≡ (predInt m) + n
predInt+ m (pos n) = predInt+pos n m 
predInt+ m (negsuc n) = predInt+negsuc n m 

+predInt : ∀ m n → predInt (m + n) ≡ m + (predInt n)
+predInt m (pos zero) = refl
+predInt m (pos (suc n)) = compPath (predSuc (m + pos n)) (cong (_+_ m) (sym (predSuc (pos n))))
+predInt m (negsuc n) = refl

sucInt+ : ∀ m n → sucInt (m + n) ≡ (sucInt m) + n
sucInt+ m (pos n) = sucInt+pos n m
sucInt+ m (negsuc n) = sucInt+negsuc n m

+sucInt : ∀ m n → sucInt (m + n) ≡  m + (sucInt n)
+sucInt m (pos n) = refl
+sucInt m (negsuc zero) = sucPred _
+sucInt m (negsuc (suc n)) = compPath (sucPred (+negsuc n m)) (cong (_+_ m) (sym (sucPred (negsuc n))))

pos0+ : ∀ z → z ≡ pos 0 + z
pos0+ (pos zero) = refl
pos0+ (pos (suc n)) = cong sucInt (pos0+ (pos n))
pos0+ (negsuc zero) = refl
pos0+ (negsuc (suc n)) = cong predInt (pos0+ (negsuc n))

negsuc0+ : ∀ z → predInt z ≡ negsuc 0 + z
negsuc0+ (pos zero) = refl
negsuc0+ (pos (suc n)) = compPath (sym (sucPred (pos n))) (cong sucInt (negsuc0+ _))
negsuc0+ (negsuc zero) = refl
negsuc0+ (negsuc (suc n)) = cong predInt (negsuc0+ (negsuc n))

ind-comm : {A : Set} (_∙_ : A → A → A) (f : ℕ → A) (g : A → A)
           (p : ∀ {n} → f (suc n) ≡ g (f n))
           (g∙ : ∀ a b → g (a ∙ b) ≡ g a ∙ b)
           (∙g : ∀ a b → g (a ∙ b) ≡ a ∙ g b)
           (base : ∀ z → z ∙ f 0 ≡ f 0 ∙ z)
         → ∀ z n → z ∙ f n ≡ f n ∙ z
ind-comm _∙_ f g p g∙ ∙g base z 0 = base z
ind-comm _∙_ f g p g∙ ∙g base z (suc n) = 
  z ∙ f (suc n) ≡⟨ cong (_∙_ z) p ⟩
  z ∙ g (f n)   ≡⟨ sym ( ∙g z (f n)) ⟩
  g (z ∙ f n)   ≡⟨ cong g IH ⟩
  g (f n ∙ z)   ≡⟨ g∙ (f n) z ⟩
  g (f n) ∙ z   ≡⟨ cong (λ x → x ∙ z) (sym p) ⟩
  f (suc n) ∙ z ∎
  where
  IH = ind-comm _∙_ f g p g∙ ∙g base z n

ind-assoc : {A : Set} (_·_ : A → A → A) (f : ℕ → A)
        (g : A → A) (p : ∀ a b → g (a · b) ≡ a · (g b))
        (q : ∀ {c} → f (suc c) ≡ g (f c))
        (base : ∀ m n → (m · n) · (f 0) ≡ m · (n · (f 0)))
        (m n : A) (o : ℕ)
      → m · (n · (f o)) ≡ (m · n) · (f o)
ind-assoc _·_ f g p q base m n 0 = sym (base m n)
ind-assoc _·_ f g p q base m n (suc o) = 
    m · (n · (f (suc o))) ≡⟨ cong (_·_ m) (cong (_·_ n) q) ⟩
    m · (n · (g (f o)))   ≡⟨ cong (_·_ m) (sym (p n (f o)))⟩
    m · (g (n · (f o)))   ≡⟨ sym (p m (n · (f o)))⟩
    g (m · (n · (f o)))   ≡⟨ cong g IH ⟩
    g ((m · n) · (f o))   ≡⟨ p (m · n) (f o) ⟩
    (m · n) · (g (f o))   ≡⟨ cong (_·_ (m · n)) (sym q)⟩
    (m · n) · (f (suc o)) ∎
    where
    IH = ind-assoc _·_ f g p q base m n o

+-comm : ∀ m n → m + n ≡ n + m
+-comm m (pos n) = ind-comm _+_ pos sucInt refl sucInt+ +sucInt pos0+ m n
+-comm m (negsuc n) = ind-comm _+_ negsuc predInt refl predInt+ +predInt negsuc0+ m n

+-assoc : ∀ m n o → m + (n + o) ≡ (m + n) + o
+-assoc m n (pos o) = ind-assoc _+_ pos sucInt +sucInt refl (λ _ _ → refl) m n o
+-assoc m n (negsuc o) = ind-assoc _+_ negsuc predInt +predInt refl +predInt m n o

-- Alternate definition: Compose sucPathInt with itself n times. Transporting along this
-- will be addition, transporting with it backwards will be subtraction.

addEq subEq : ℕ → Int ≡ Int
addEq zero = refl
addEq (suc n) = compPath (addEq n) sucPathInt

subEq n i = addEq n (~ i)

_+'_ : Int → Int → Int
m +' pos n    = transport (addEq n) m
m +' negsuc n = transport (subEq (suc n)) m

private
  FamilyOfEquiv : (f : Int → Int → Int) → Set
  FamilyOfEquiv f = (m : Int) → isEquiv (λ n → f n m)

  L0 : ∀ n z → +negsuc (suc n) z ≡ +negsuc n (predInt z)
  L0 0 z = refl
  L0 (suc n) z = cong predInt (L0 n z)
  
  Lnegsuc : ∀ n z → z +' negsuc n ≡ +negsuc n z
  Lnegsuc 0 z = refl
  Lnegsuc (suc n) z = compPath (Lnegsuc n (predInt z)) (sym (L0 n z))

  Lpos : ∀ n z → z +' pos n ≡ +pos n z
  Lpos zero z = refl
  Lpos (suc n) z = cong sucInt (Lpos n z)
  
  Lemma : ∀ m n → m +' n ≡ m + n
  Lemma m (pos n) = Lpos n m
  Lemma m (negsuc n) = Lnegsuc n m

+'≡+ : _+'_ ≡ _+_
+'≡+ i m n = Lemma m n i

-- We directly get that addition by a fixed number is an equivalence
-- without having to do any induction!
isEquivAddInt' : (m : Int) → isEquiv (λ n → n +' m)
isEquivAddInt' (pos n)    = isEquivTransport (addEq n)
isEquivAddInt' (negsuc n) = isEquivTransport (subEq (suc n))

isEquivAddInt : (m : Int) → isEquiv (λ n → n + m)
isEquivAddInt = subst FamilyOfEquiv +'≡+ isEquivAddInt'
