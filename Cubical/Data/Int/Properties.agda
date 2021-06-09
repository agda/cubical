{-# OPTIONS --safe #-}
module Cubical.Data.Int.Properties where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.Empty
open import Cubical.Data.Nat
  hiding   (+-assoc ; +-comm ; ·-comm)
  renaming (_·_ to _·ℕ_; _+_ to _+ℕ_ ; ·-assoc to ·ℕ-assoc)
open import Cubical.Data.Bool
open import Cubical.Data.Sum
open import Cubical.Data.Int.Base

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq

sucPred : ∀ i → sucInt (predInt i) ≡ i
sucPred (pos zero)    = refl
sucPred (pos (suc n)) = refl
sucPred (negsuc n)    = refl

predSuc : ∀ i → predInt (sucInt i) ≡ i
predSuc (pos n)          = refl
predSuc (negsuc zero)    = refl
predSuc (negsuc (suc n)) = refl

injPos : ∀ {a b : ℕ} → pos a ≡ pos b → a ≡ b
injPos {a} h = subst T h refl
  where
  T : Int → Type₀
  T (pos x)    = a ≡ x
  T (negsuc _) = ⊥

injNegsuc : ∀ {a b : ℕ} → negsuc a ≡ negsuc b → a ≡ b
injNegsuc {a} h = subst T h refl
  where
  T : Int → Type₀
  T (pos _) = ⊥
  T (negsuc x) = a ≡ x

posNotnegsuc : ∀ (a b : ℕ) → ¬ (pos a ≡ negsuc b)
posNotnegsuc a b h = subst T h 0
  where
  T : Int → Type₀
  T (pos _)    = ℕ
  T (negsuc _) = ⊥

negsucNotpos : ∀ (a b : ℕ) → ¬ (negsuc a ≡ pos b)
negsucNotpos a b h = subst T h 0
  where
  T : Int → Type₀
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

-pos : ∀ n → - (pos n) ≡ neg n
-pos zero    = refl
-pos (suc n) = refl

-neg : ∀ n → - (neg n) ≡ pos n
-neg zero    = refl
-neg (suc n) = refl

-Involutive : ∀ z → - (- z) ≡ z
-Involutive (pos n)    = cong -_ (-pos n) ∙ -neg n
-Involutive (negsuc n) = refl

sucInt+pos : ∀ n m → sucInt (m +pos n) ≡ (sucInt m) +pos n
sucInt+pos zero m = refl
sucInt+pos (suc n) m = cong sucInt (sucInt+pos n m)

predInt+negsuc : ∀ n m → predInt (m +negsuc n) ≡ (predInt m) +negsuc n
predInt+negsuc zero m = refl
predInt+negsuc (suc n) m = cong predInt (predInt+negsuc n m)

sucInt+negsuc : ∀ n m → sucInt (m +negsuc n) ≡ (sucInt m) +negsuc n
sucInt+negsuc zero m = (sucPred _) ∙ (sym (predSuc _))
sucInt+negsuc (suc n) m =      _ ≡⟨ sucPred _ ⟩
  m +negsuc n                    ≡[ i ]⟨ predSuc m (~ i) +negsuc n ⟩
  (predInt (sucInt m)) +negsuc n ≡⟨ sym (predInt+negsuc n (sucInt m)) ⟩
  predInt (sucInt m +negsuc n) ∎

predInt+pos : ∀ n m → predInt (m +pos n) ≡ (predInt m) +pos n
predInt+pos zero m = refl
predInt+pos (suc n) m =     _ ≡⟨ predSuc _ ⟩
  m +pos n                    ≡[ i ]⟨ sucPred m (~ i) + pos n ⟩
  (sucInt (predInt m)) +pos n ≡⟨ sym (sucInt+pos n (predInt m))⟩
  (predInt m) +pos (suc n)    ∎

predInt-pos : ∀ n → predInt(- (pos n)) ≡ negsuc n
predInt-pos zero = refl
predInt-pos (suc n) = refl

predInt+ : ∀ m n → predInt (m + n) ≡ (predInt m) + n
predInt+ m (pos n) = predInt+pos n m
predInt+ m (negsuc n) = predInt+negsuc n m

+predInt : ∀ m n → predInt (m + n) ≡ m + (predInt n)
+predInt m (pos zero) = refl
+predInt m (pos (suc n)) = (predSuc (m + pos n)) ∙ (cong (_+_ m) (sym (predSuc (pos n))))
+predInt m (negsuc n) = refl

sucInt+ : ∀ m n → sucInt (m + n) ≡ (sucInt m) + n
sucInt+ m (pos n) = sucInt+pos n m
sucInt+ m (negsuc n) = sucInt+negsuc n m

+sucInt : ∀ m n → sucInt (m + n) ≡  m + (sucInt n)
+sucInt m (pos n) = refl
+sucInt m (negsuc zero) = sucPred _
+sucInt m (negsuc (suc n)) = (sucPred (m +negsuc n)) ∙ (cong (_+_ m) (sym (sucPred (negsuc n))))

pos0+ : ∀ z → z ≡ pos 0 + z
pos0+ (pos zero) = refl
pos0+ (pos (suc n)) = cong sucInt (pos0+ (pos n))
pos0+ (negsuc zero) = refl
pos0+ (negsuc (suc n)) = cong predInt (pos0+ (negsuc n))

negsuc0+ : ∀ z → predInt z ≡ negsuc 0 + z
negsuc0+ (pos zero) = refl
negsuc0+ (pos (suc n)) = (sym (sucPred (pos n))) ∙ (cong sucInt (negsuc0+ _))
negsuc0+ (negsuc zero) = refl
negsuc0+ (negsuc (suc n)) = cong predInt (negsuc0+ (negsuc n))

ind-comm : {A : Type₀} (_∙_ : A → A → A) (f : ℕ → A) (g : A → A)
           (p : ∀ {n} → f (suc n) ≡ g (f n))
           (g∙ : ∀ a b → g (a ∙ b) ≡ g a ∙ b)
           (∙g : ∀ a b → g (a ∙ b) ≡ a ∙ g b)
           (base : ∀ z → z ∙ f 0 ≡ f 0 ∙ z)
         → ∀ z n → z ∙ f n ≡ f n ∙ z
ind-comm _∙_ f g p g∙ ∙g base z 0 = base z
ind-comm _∙_ f g p g∙ ∙g base z (suc n) =
  z ∙ f (suc n) ≡[ i ]⟨ z ∙ p {n} i ⟩
  z ∙ g (f n)   ≡⟨ sym ( ∙g z (f n)) ⟩
  g (z ∙ f n)   ≡⟨ cong g IH ⟩
  g (f n ∙ z)   ≡⟨ g∙ (f n) z ⟩
  g (f n) ∙ z   ≡[ i ]⟨ p {n} (~ i) ∙ z ⟩
  f (suc n) ∙ z ∎
  where
  IH = ind-comm _∙_ f g p g∙ ∙g base z n

ind-assoc : {A : Type₀} (_·_ : A → A → A) (f : ℕ → A)
        (g : A → A) (p : ∀ a b → g (a · b) ≡ a · (g b))
        (q : ∀ {c} → f (suc c) ≡ g (f c))
        (base : ∀ m n → (m · n) · (f 0) ≡ m · (n · (f 0)))
        (m n : A) (o : ℕ)
      → m · (n · (f o)) ≡ (m · n) · (f o)
ind-assoc _·_ f g p q base m n 0 = sym (base m n)
ind-assoc _·_ f g p q base m n (suc o) =
    m · (n · (f (suc o))) ≡[ i ]⟨ m · (n · q {o} i) ⟩
    m · (n · (g (f o)))   ≡[ i ]⟨ m · (p n (f o) (~ i)) ⟩
    m · (g (n · (f o)))   ≡⟨ sym (p m (n · (f o)))⟩
    g (m · (n · (f o)))   ≡⟨ cong g IH ⟩
    g ((m · n) · (f o))   ≡⟨ p (m · n) (f o) ⟩
    (m · n) · (g (f o))   ≡[ i ]⟨ (m · n) · q {o} (~ i) ⟩
    (m · n) · (f (suc o)) ∎
    where
    IH = ind-assoc _·_ f g p q base m n o

+Comm : ∀ m n → m + n ≡ n + m
+Comm m (pos n) = ind-comm _+_ pos sucInt refl sucInt+ +sucInt pos0+ m n
+Comm m (negsuc n) = ind-comm _+_ negsuc predInt refl predInt+ +predInt negsuc0+ m n

+Assoc : ∀ m n o → m + (n + o) ≡ (m + n) + o
+Assoc m n (pos o) = ind-assoc _+_ pos sucInt +sucInt refl (λ _ _ → refl) m n o
+Assoc m n (negsuc o) = ind-assoc _+_ negsuc predInt +predInt refl +predInt m n o

-- Compose sucPathInt with itself n times. Transporting along this
-- will be addition, transporting with it backwards will be subtraction.
-- Use this to define _+'_ for which is easier to prove
-- isEquiv (λ n → n +' m) since _+'_ is defined by transport

sucPathInt : Int ≡ Int
sucPathInt = ua (sucInt , isoToIsEquiv (iso sucInt predInt sucPred predSuc))

addEq : ℕ → Int ≡ Int
addEq zero = refl
addEq (suc n) = (addEq n) ∙ sucPathInt

predPathInt : Int ≡ Int
predPathInt = ua (predInt , isoToIsEquiv (iso predInt sucInt predSuc sucPred))

subEq : ℕ → Int ≡ Int
subEq zero = refl
subEq (suc n) = (subEq n) ∙ predPathInt

_+'_ : Int → Int → Int
m +' pos n    = transport (addEq n) m
m +' negsuc n = transport (subEq (suc n)) m

+'≡+ : _+'_ ≡ _+_
+'≡+ i m (pos zero) = m
+'≡+ i m (pos (suc n)) = sucInt (+'≡+ i m (pos n))
+'≡+ i m (negsuc zero) = predInt m
+'≡+ i m (negsuc (suc n)) = predInt (+'≡+ i m (negsuc n)) --
  -- compPath (λ i → (+'≡+ i (predInt m) (negsuc n))) (sym (predInt+negsuc n m)) i

isEquivAddInt' : (m : Int) → isEquiv (λ n → n +' m)
isEquivAddInt' (pos n)    = isEquivTransport (addEq n)
isEquivAddInt' (negsuc n) = isEquivTransport (subEq (suc n))

isEquivAddInt : (m : Int) → isEquiv (λ n → n + m)
isEquivAddInt = subst (λ add → (m : Int) → isEquiv (λ n → add n m)) +'≡+ isEquivAddInt'

-- below is an alternate proof of isEquivAddInt for comparison
-- We also have two useful lemma here.

minusPlus : ∀ m n → (n - m) + m ≡ n
minusPlus (pos zero) n = refl
minusPlus (pos 1) = sucPred
minusPlus (pos (suc (suc m))) n =
  sucInt ((n +negsuc (suc m)) +pos (suc m)) ≡⟨ sucInt+pos (suc m) _ ⟩
  sucInt (n +negsuc (suc m)) +pos (suc m)   ≡[ i ]⟨ sucPred (n +negsuc m) i +pos (suc m) ⟩
  (n - pos (suc m)) +pos (suc m)            ≡⟨ minusPlus (pos (suc m)) n ⟩
  n ∎
minusPlus (negsuc zero) = predSuc
minusPlus (negsuc (suc m)) n =
  predInt (sucInt (sucInt (n +pos m)) +negsuc m) ≡⟨ predInt+negsuc m _ ⟩
  predInt (sucInt (sucInt (n +pos m))) +negsuc m ≡[ i ]⟨ predSuc (sucInt (n +pos m)) i +negsuc m ⟩
  sucInt (n +pos m) +negsuc m                    ≡⟨ minusPlus (negsuc m) n ⟩
  n ∎

plusMinus : ∀ m n → (n + m) - m ≡ n
plusMinus (pos zero) n = refl
plusMinus (pos (suc m)) = minusPlus (negsuc m)
plusMinus (negsuc m) = minusPlus (pos (suc m))

private
  alternateProof : (m : Int) → isEquiv (λ n → n + m)
  alternateProof m = isoToIsEquiv (iso (λ n → n + m)
                                       (λ n → n - m)
                                       (minusPlus m)
                                       (plusMinus m))

-Cancel : ∀ z → z - z ≡ 0
-Cancel z = cong (_- z) (pos0+ z) ∙ plusMinus z (pos zero)

pos+ : ∀ m n → pos (m +ℕ n) ≡ pos m + pos n
pos+ zero zero = refl
pos+ zero (suc n)    =
  pos (zero +ℕ suc n)    ≡⟨ +Comm (pos (suc n)) (pos zero) ⟩
  pos zero + pos (suc n) ∎
pos+ (suc m) zero    =
  pos (suc (m +ℕ zero))  ≡⟨ cong pos (cong suc (+-zero m)) ⟩
  pos (suc m) + pos zero ∎
pos+ (suc m) (suc n) =
  pos (suc m +ℕ suc n)            ≡⟨ cong pos (cong suc (+-suc m n)) ⟩
  sucInt (pos (suc (m +ℕ n)))     ≡⟨ cong sucInt (cong sucInt (pos+ m n)) ⟩
  sucInt (sucInt (pos m + pos n)) ≡⟨ sucInt+ (pos m) (sucInt (pos n)) ⟩
  pos (suc m) + pos (suc n)       ∎

negsuc+ : ∀ m n → negsuc (m +ℕ n) ≡ negsuc m - pos n
negsuc+ zero zero       = refl
negsuc+ zero (suc n)    =
  negsuc (zero +ℕ suc n)    ≡⟨ negsuc0+ (negsuc n) ⟩
  negsuc zero + negsuc n    ≡⟨ cong (negsuc zero +_) (-pos (suc n)) ⟩
  negsuc zero - pos (suc n) ∎
negsuc+ (suc m) zero    =
  negsuc (suc m +ℕ zero)    ≡⟨ cong negsuc (cong suc (+-zero m)) ⟩
  negsuc (suc m) - pos zero ∎
negsuc+ (suc m) (suc n) =
  negsuc (suc m +ℕ suc n)        ≡⟨ cong negsuc (sym (+-suc m (suc n))) ⟩
  negsuc (m +ℕ suc (suc n))      ≡⟨ negsuc+ m (suc (suc n)) ⟩
  negsuc m - pos (suc (suc n))   ≡⟨ sym (+predInt (negsuc m) (negsuc n)) ⟩
  predInt (negsuc m + negsuc n ) ≡⟨ predInt+ (negsuc m) (negsuc n) ⟩
  negsuc (suc m) - pos (suc n)   ∎

neg+ : ∀ m n → neg (m +ℕ n) ≡ neg m + neg n
neg+ zero zero       = refl
neg+ zero (suc n)    = neg (zero +ℕ suc n)    ≡⟨ +Comm (neg (suc n)) (pos zero) ⟩
                       neg zero + neg (suc n) ∎
neg+ (suc m) zero    = neg (suc (m +ℕ zero))  ≡⟨ cong neg (cong suc (+-zero m)) ⟩
                       neg (suc m) + neg zero ∎
neg+ (suc m) (suc n) = neg (suc m +ℕ suc n)      ≡⟨ negsuc+ m (suc n) ⟩
                       neg (suc m) + neg (suc n) ∎

ℕ-AntiComm : ∀ m n → m ℕ- n ≡ - (n ℕ- m)
ℕ-AntiComm zero zero       = refl
ℕ-AntiComm zero (suc n)    = refl
ℕ-AntiComm (suc m) zero    = refl
ℕ-AntiComm (suc m) (suc n) = suc m ℕ- suc n  ≡⟨ ℕ-AntiComm m n ⟩
                          - (suc n ℕ- suc m) ∎

pos- : ∀ m n → m ℕ- n ≡ pos m - pos n
pos- zero zero       = refl
pos- zero (suc n)    = zero ℕ- suc n          ≡⟨ +Comm (negsuc n) (pos zero) ⟩
                       pos zero - pos (suc n) ∎
pos- (suc m) zero    = refl
pos- (suc m) (suc n) =
  suc m ℕ- suc n                       ≡⟨ pos- m n ⟩
  pos m - pos n                        ≡⟨ sym (sucPred (pos m - pos n)) ⟩
  sucInt (predInt (pos m - pos n))     ≡⟨ cong sucInt (+predInt (pos m) (- pos n)) ⟩
  sucInt (pos m + predInt (- (pos n))) ≡⟨ cong sucInt (cong (pos m +_) (predInt-pos n)) ⟩
  sucInt (pos m + negsuc n)            ≡⟨ sucInt+negsuc n (pos m) ⟩
  pos (suc m) - pos (suc n)            ∎

-AntiComm : ∀ m n → m - n ≡ - (n - m)
-AntiComm (pos n) (pos m)       = pos n - pos m   ≡⟨ sym (pos- n m) ⟩
                                   n ℕ- m         ≡⟨ ℕ-AntiComm n m ⟩
                                - (m ℕ- n)        ≡⟨ cong -_ (pos- m n) ⟩
                                - (pos m - pos n) ∎
-AntiComm (pos n) (negsuc m)    =
     pos n - negsuc m     ≡⟨ +Comm (pos n) (pos (suc m)) ⟩
     pos (suc m) + pos n  ≡⟨ sym (pos+ (suc m) n) ⟩
     pos (suc m +ℕ n)     ≡⟨ sym (-neg (suc m +ℕ n)) ⟩
  -  neg (suc m +ℕ n)     ≡⟨ cong -_ (neg+ (suc m) n) ⟩
  - (neg (suc m) + neg n) ≡⟨ cong -_ (cong (negsuc m +_) (sym (-pos n))) ⟩
  - (negsuc m - pos n)    ∎
-AntiComm (negsuc n) (pos m)    =
     negsuc n - pos m     ≡⟨ sym (negsuc+ n m) ⟩
     negsuc (n +ℕ m)      ≡⟨ cong -_ (pos+ (suc n) m) ⟩
  - (pos (suc n) + pos m) ≡⟨ cong -_ (+Comm (pos (suc n)) (pos m)) ⟩
  - (pos m - negsuc n)    ∎
-AntiComm (negsuc n) (negsuc m) =
     negsuc n - negsuc m        ≡⟨ +Comm (negsuc n) (pos (suc m)) ⟩
     pos (suc m) + negsuc n     ≡⟨ sym (pos- (suc m) (suc n)) ⟩
     suc m ℕ- suc n             ≡⟨ ℕ-AntiComm (suc m) (suc n) ⟩
  - (suc n ℕ- suc m)            ≡⟨ cong -_ (pos- (suc n) (suc m)) ⟩
  - (pos (suc n) - pos (suc m)) ≡⟨ cong -_ (+Comm (pos (suc n)) (negsuc m)) ⟩
  - (negsuc m - negsuc n)       ∎

-Dist+ : ∀ m n → - (m + n) ≡ (- m) + (- n)
-Dist+ (pos n) (pos m)       =
   - (pos n + pos m)     ≡⟨ cong -_ (sym (pos+ n m)) ⟩
   -  pos (n +ℕ m)       ≡⟨ -pos (n +ℕ m) ⟩
      neg (n +ℕ m)       ≡⟨ neg+ n m ⟩
      neg n + neg m      ≡⟨ cong (neg n +_) (sym (-pos m)) ⟩
      neg n + (- pos m)  ≡⟨ cong (_+ (- pos m)) (sym (-pos n)) ⟩
  (-  pos n) + (- pos m) ∎
-Dist+ (pos n) (negsuc m)    =
   - (pos n + negsuc m)     ≡⟨ sym (-AntiComm (pos (suc m)) (pos n)) ⟩
      pos (suc m) - pos n   ≡⟨ +Comm (pos (suc m)) (- pos n) ⟩
  (-  pos n) + (- negsuc m) ∎
-Dist+ (negsuc n) (pos m)    =
   - (negsuc n + pos m)     ≡⟨ cong -_ (+Comm (negsuc n) (pos m)) ⟩
   - (pos m + negsuc n)     ≡⟨ sym (-AntiComm (- negsuc n) (pos m)) ⟩
  (-  negsuc n) + (- pos m) ∎
-Dist+ (negsuc n) (negsuc m) =
   - (negsuc n + negsuc m)     ≡⟨ cong -_ (sym (neg+ (suc n) (suc m))) ⟩
   -  neg (suc n +ℕ suc m)     ≡⟨ pos+ (suc n) (suc m) ⟩
  (-  negsuc n) + (- negsuc m) ∎


-- multiplication

pos·negsuc : (n m : ℕ) → pos n · negsuc m ≡ - (pos n · pos (suc m))
pos·negsuc zero m = refl
pos·negsuc (suc n) m =
     (λ i → negsuc m + (pos·negsuc n m i))
   ∙ sym (-Dist+ (pos (suc m)) (pos n · pos (suc m)))

negsuc·pos : (n m : ℕ) → negsuc n · pos m ≡ - (pos (suc n) · pos m)
negsuc·pos zero m = refl
negsuc·pos (suc n) m =
    cong ((- pos m) +_) (negsuc·pos n m)
  ∙ sym (-Dist+ (pos m) (pos m + (pos n · pos m)))

negsuc·negsuc : (n m : ℕ) → negsuc n · negsuc m ≡ pos (suc n) · pos (suc m)
negsuc·negsuc zero m = refl
negsuc·negsuc (suc n) m = cong (pos (suc m) +_) (negsuc·negsuc n m)

·Comm : (x y : Int) → x · y ≡ y · x
·Comm (pos n) (pos m) = lem n m
  where
  lem : (n m : ℕ) → (pos n · pos m) ≡ (pos m · pos n)
  lem zero zero = refl
  lem zero (suc m) i = +Comm (lem zero m i) (pos zero) i
  lem (suc n) zero i = +Comm (pos zero) (lem n zero i) i
  lem (suc n) (suc m) =
       (λ i → pos (suc m) + (lem n (suc m) i))
    ∙∙ +Assoc (pos (suc m)) (pos n) (pos m · pos n)
    ∙∙ (λ i → sucInt+ (pos m) (pos n) (~ i)  + (pos m · pos n))
    ∙∙ (λ i → +Comm (pos m) (pos (suc n)) i + (pos m · pos n))
    ∙∙ sym (+Assoc (pos (suc n)) (pos m) (pos m · pos n))
    ∙∙ (λ i → pos (suc n) + (pos m + (lem n m (~ i))))
    ∙∙ λ i → pos (suc n) + (lem (suc n) m i)
·Comm (pos n) (negsuc m) =
     pos·negsuc n m
  ∙∙ cong -_ (·Comm (pos n) (pos (suc m)))
  ∙∙ sym (negsuc·pos m n)
·Comm (negsuc n) (pos m) =
  sym (pos·negsuc m n
  ∙∙ cong -_ (·Comm (pos m) (pos (suc n)))
  ∙∙ sym (negsuc·pos n m))
·Comm (negsuc n) (negsuc m) =
  negsuc·negsuc n m ∙∙ ·Comm (pos (suc n)) (pos (suc m)) ∙∙ sym (negsuc·negsuc m n)

·Rid : (x : Int) → x · 1 ≡ x
·Rid x = ·Comm x 1

private
  distrHelper : (x y z w : Int) → (x + y) + (z + w) ≡ ((x + z) + (y + w))
  distrHelper x y z w =
      +Assoc (x + y) z w
   ∙∙ cong (_+ w) (sym (+Assoc x y z) ∙∙ cong (x +_) (+Comm y z) ∙∙ +Assoc x z y)
   ∙∙ sym (+Assoc (x + z) y w)

·DistR+ : (x y z : Int) → x · (y + z) ≡ x · y + x · z
·DistR+ (pos zero) y z = refl
·DistR+ (pos (suc n)) y z =
     cong ((y + z) +_) (·DistR+ (pos n) y z)
   ∙ distrHelper y z (pos n · y) (pos n · z)
·DistR+ (negsuc zero) y z = -Dist+ y z
·DistR+ (negsuc (suc n)) y z =
    cong₂ _+_ (-Dist+ y z) (·DistR+ (negsuc n) y z)
  ∙ distrHelper (- y) (- z) (negsuc n · y) (negsuc n · z)

·DistL+ : (x y z : Int) → (x + y) · z ≡ x · z + y · z
·DistL+ x y z = ·Comm (x + y) z ∙∙ ·DistR+ z x y ∙∙ cong₂ _+_ (·Comm z x) (·Comm z y)

-DistL· : (b c : Int) → - (b · c) ≡ - b · c
-DistL· (pos zero) c = refl
-DistL· (pos (suc n)) (pos m) = sym (negsuc·pos n m)
-DistL· (pos (suc zero)) (negsuc m) =
    -Dist+ (negsuc m) (pos zero · negsuc m)
  ∙ cong (pos (suc m) +_) (-DistL· (pos zero) (negsuc m))
-DistL· (pos (suc (suc n))) (negsuc m) =
    -Dist+ (negsuc m) (pos (suc n) · negsuc m)
  ∙ cong (pos (suc m) +_) (-DistL· (pos (suc n)) (negsuc m))
-DistL· (negsuc zero) c = -Involutive c
-DistL· (negsuc (suc n)) c =
   -Dist+ (- c) (negsuc n · c)
 ∙∙ cong (_+ (- (negsuc n · c))) (-Involutive c)
 ∙∙ cong (c +_) (-DistL· (negsuc n) c)

-DistR· : (b c : Int) → - (b · c) ≡ b · - c
-DistR· b c = cong (-_) (·Comm b c) ∙∙ -DistL· c b ∙∙ ·Comm (- c) b

·Assoc : (a b c : Int) → (a · (b · c)) ≡ ((a · b) · c)
·Assoc (pos zero) b c = refl
·Assoc (pos (suc n)) b c =
      cong ((b · c) +_) (·Assoc (pos n) b c)
   ∙∙ cong₂ _+_ (·Comm b c) (·Comm (pos n · b) c)
   ∙∙ sym (·DistR+ c b (pos n · b))
    ∙ sym (·Comm _ c)
·Assoc (negsuc zero) = -DistL·
·Assoc (negsuc (suc n)) b c =
     cong ((- (b · c)) +_) (·Assoc (negsuc n) b c)
  ∙∙ cong (_+ ((negsuc n · b) · c)) (-DistL· b c)
  ∙∙ sym (·DistL+ (- b) (negsuc n · b) c)
