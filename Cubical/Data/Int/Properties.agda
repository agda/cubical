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

sucIntAddEq : ∀ n z → sucInt (transport (addEq n) z) ≡ transport (addEq n) (sucInt z)
sucIntAddEq zero z = refl
sucIntAddEq (suc n) z = cong sucInt (sucIntAddEq n z)

predIntSubEq : ∀ n z → predInt (transport (subEq n) z) ≡ transport (subEq n) (predInt z)
predIntSubEq zero z = refl
predIntSubEq (suc n) z = predIntSubEq n (predInt z)

sucIntSubEq : ∀ n z → sucInt (transport (subEq n) z) ≡ transport (subEq n) (sucInt z)
sucIntSubEq zero z = refl
sucIntSubEq (suc n) z = 
  sucInt (transport (subEq n) (predInt z)) ≡⟨ cong sucInt (sym (predIntSubEq n z)) ⟩
  sucInt (predInt (transport (subEq n) z)) ≡⟨ sucPred _ ⟩
  transport (subEq n) z                    ≡⟨ cong (transport (subEq n)) (sym (predSuc _))⟩
  _ ∎

predIntAddEq : ∀ n z → predInt (transport (addEq n) z) ≡ transport (addEq n) (predInt z)
predIntAddEq zero z = refl
predIntAddEq (suc n) z =
  predInt (sucInt (transport (addEq n) z)) ≡⟨ predSuc _ ⟩
  transport (addEq n) z                    ≡⟨ cong (transport (addEq n)) (sym (sucPred _))⟩
  transport (addEq n) (sucInt (predInt z)) ≡⟨ sym (sucIntAddEq n (predInt z)) ⟩
  _ ∎

predInt+ : ∀ m n → predInt (m + n) ≡ (predInt m) + n
predInt+ m (pos n) = predIntAddEq n m
predInt+ m (negsuc n) = predIntSubEq n (predInt m)

+predInt : ∀ m n → predInt (m + n) ≡ m + (predInt n)
+predInt m (pos zero)    = refl
+predInt m (pos (suc n)) = predSuc _
+predInt m (negsuc n)    = predIntSubEq n (predInt m)

sucInt+ : ∀ m n → sucInt (m + n) ≡ (sucInt m) + n
sucInt+ m n =
  sucInt (m + n)                  ≡⟨ cong sucInt (cong (λ z → z + n) (sym (predSuc m))) ⟩
  sucInt (predInt (sucInt m) + n) ≡⟨ cong sucInt (sym (predInt+ (sucInt m) n)) ⟩
  sucInt (predInt (sucInt m + n)) ≡⟨ sucPred _ ⟩
  sucInt m + n ∎

+sucInt : ∀ m n → sucInt (m + n) ≡  m + (sucInt n)
+sucInt m n =
  sucInt (m + n)                  ≡⟨ cong sucInt (cong (_+_ m) (sym (predSuc n))) ⟩
  sucInt (m + predInt (sucInt n)) ≡⟨ cong sucInt (sym (+predInt m (sucInt n))) ⟩
  sucInt (predInt (m + sucInt n)) ≡⟨ sucPred _ ⟩
  m + sucInt n ∎
  
pos0+ : ∀ z → z ≡ pos 0 + z
pos0+ (pos zero) = refl
pos0+ (pos (suc n)) = cong sucInt (pos0+ (pos n))
pos0+ (negsuc zero) = refl
pos0+ (negsuc (suc n)) = compPath (cong predInt (pos0+ (negsuc n))) (predIntSubEq n (negsuc 0)) 

negsuc0+ : ∀ z → predInt z ≡ negsuc 0 + z
negsuc0+ (pos zero) = refl
negsuc0+ (pos (suc n)) = 
  predInt (pos (suc n))                   ≡⟨ pos0+ (pos n) ⟩
  transport (addEq n) (pos 0)             ≡⟨ sym (sucIntAddEq n (negsuc 0)) ⟩
  sucInt (transport (addEq n) (negsuc 0)) ∎

negsuc0+ (negsuc zero) = refl
negsuc0+ (negsuc (suc n)) = 
  compPath (cong predInt (negsuc0+ (negsuc n))) (+predInt (negsuc 0) (negsuc n))

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

+-comm : ∀ m n → m + n ≡ n + m
+-comm m (pos n) = ind-comm _+_ pos sucInt refl sucInt+ +sucInt pos0+ m n
+-comm m (negsuc n) = ind-comm _+_ negsuc predInt refl predInt+ +predInt negsuc0+ m n

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

+-assoc : ∀ m n o → m + (n + o) ≡ (m + n) + o
+-assoc m n (pos o) = ind-assoc _+_ pos sucInt +sucInt refl (λ _ _ → refl) m n o
+-assoc m n (negsuc o) = ind-assoc _+_ negsuc predInt +predInt refl +predInt m n o
