{-# OPTIONS --cubical --no-import-sorts --safe #-}

{-

This file defines

sucPred : ∀ (i : Int) → sucInt (predInt i) ≡ i
predSuc : ∀ (i : Int) → predInt (sucInt i) ≡ i

discreteInt : discrete Int
isSetInt : isSet Int

addition of Int is defined _+_ : Int → Int → Int

as well as its commutativity and associativity
+-comm : ∀ (m n : Int) → m + n ≡ n + m
+-assoc : ∀ (m n o : Int) → m + (n + o) ≡ (m + n) + o

An alternate definition of _+_ is defined via ua,
namely _+'_, which helps us to easily prove

isEquivAddInt : (m : Int) → isEquiv (λ n → n + m)

-}

module Cubical.Data.Int.Properties where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.Empty
open import Cubical.Data.Nat  as ℕ using (ℕ; zero; suc; discreteℕ) renaming ( _·_ to _·ⁿ_ ; _+_ to _+ⁿ_ )
open import Cubical.Data.Bool
open import Cubical.Data.Sum
open import Cubical.Data.Int.Base

open import Cubical.Reflection.Base using (_$_) -- TODO: add this to Foundation.Function

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq

abs : Int → ℕ
abs (pos n) = n
abs (negsuc n) = suc n

Sign : Type₀
Sign = Bool

pattern spos = Bool.false
pattern sneg = Bool.true

_·ˢ_ : Sign → Sign → Sign
_·ˢ_ = _⊕_

sgn : Int → Bool
sgn (pos    n) = spos
sgn (negsuc n) = sneg

signed : Sign → ℕ → Int
signed spos      x  = pos x
signed sneg  zero   = pos 0
signed sneg (suc x) = neg (suc x)

signed-zero : ∀ s → signed s 0 ≡ 0
signed-zero spos = refl
signed-zero sneg = refl

signed-inv : ∀ a → signed (sgn a) (abs a) ≡ a
signed-inv (pos    n) = refl
signed-inv (negsuc n) = refl

sucPred : ∀ i → sucInt (predInt i) ≡ i
sucPred (pos zero)    = refl
sucPred (pos (suc n)) = refl
sucPred (negsuc n)    = refl

predSuc : ∀ i → predInt (sucInt i) ≡ i
predSuc (pos n)          = refl
predSuc (negsuc zero)    = refl
predSuc (negsuc (suc n)) = refl

-- TODO: define multiplication

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

_ℕ-_ : ℕ → ℕ → Int
a ℕ- 0 = pos a
0 ℕ- suc b = negsuc b
suc a ℕ- suc b = a ℕ- b

_+pos_ : Int → ℕ  → Int
z +pos 0 = z
z +pos (suc n) = sucInt (z +pos n)

_+negsuc_ : Int → ℕ → Int
z +negsuc 0 = predInt z
z +negsuc (suc n) = predInt (z +negsuc n)

infix  8 -_
infixl 7 _·_
infixl 6 _+_ _-_

_+_ : Int → Int → Int
m + pos n = m +pos n
m + negsuc n = m +negsuc n

-_ : Int → Int
- pos  zero   = pos zero
- pos (suc n) = negsuc n
- negsuc   n  = pos (suc n)

_-_ : Int → Int → Int
m - n = m + (- n)

_·_ : Int → Int → Int
x · y  = signed (sgn x ⊕ sgn y) (abs x ·ⁿ abs y)

neg-signed-not : ∀ s n → - signed s n ≡ signed (not s) n
neg-signed-not spos  zero   = refl
neg-signed-not sneg  zero   = refl
neg-signed-not spos (suc n) = refl
neg-signed-not sneg (suc n) = refl

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

+-comm : ∀ m n → m + n ≡ n + m
+-comm m (pos n) = ind-comm _+_ pos sucInt refl sucInt+ +sucInt pos0+ m n
+-comm m (negsuc n) = ind-comm _+_ negsuc predInt refl predInt+ +predInt negsuc0+ m n

+-assoc : ∀ m n o → m + (n + o) ≡ (m + n) + o
+-assoc m n (pos o) = ind-assoc _+_ pos sucInt +sucInt refl (λ _ _ → refl) m n o
+-assoc m n (negsuc o) = ind-assoc _+_ negsuc predInt +predInt refl +predInt m n o

+-identityʳ : ∀ x → x + 0 ≡ x
+-identityʳ x = refl

+-identityˡ : ∀ x → 0 + x ≡ x
+-identityˡ x = +-comm 0 x

negsuc+negsuc : ∀ a x → (negsuc a +negsuc x) ≡ negsuc (suc (a +ⁿ x))
negsuc+negsuc a zero = λ i → negsuc $ suc $ ℕ.+-comm 0 a i
negsuc+negsuc a (suc x) = let r = negsuc+negsuc a x in
  predInt (negsuc a +negsuc x)    ≡⟨ (λ i → predInt (r i)) ⟩
  predInt (negsuc (suc (a +ⁿ x))) ≡⟨ refl ⟩
  negsuc (suc (suc (a +ⁿ x)))     ≡⟨ (λ i → negsuc $ suc $ ℕ.+-suc a x (~ i)) ⟩
  negsuc (suc (a +ⁿ suc x))       ∎

signed-distrib : ∀ s m n → signed s (m +ⁿ n) ≡ signed s m + signed s n
signed-distrib s zero n = (sym $ +-identityˡ (signed s n)) ∙ λ i → signed-zero s (~ i) + signed s n
signed-distrib spos (suc m) n = cong sucInt (signed-distrib spos m n) ∙ sucInt+pos n (pos m)
signed-distrib sneg (suc m) zero i = negsuc (ℕ.+-comm m 0 i)
signed-distrib sneg (suc m) (suc n) = (λ i → negsuc (ℕ.+-suc m n i)) ∙  sym (negsuc+negsuc m n)

·-pos-suc : ∀ m n → pos (suc m) · n ≡ n + pos m · n
·-pos-suc m n = signed-distrib (sgn n) (abs n) (m ℕ.· abs n) ∙ λ i → signed-inv n i + signed (sgn n) (m ·ⁿ abs n)

·-negsuc-suc : ∀ m n → negsuc (suc m) · n ≡ - n + negsuc m · n
·-negsuc-suc m n = signed-distrib (not (sgn n)) (abs n) (suc m ℕ.· abs n) ∙ λ i → γ i + negsuc m · n
  where γ = sym (neg-signed-not (sgn n) (abs n)) ∙ cong -_ (signed-inv n)

predInt-neg : ∀ a → predInt (- a) ≡ - (sucInt a)
predInt-neg (pos     zero  ) = refl
predInt-neg (pos    (suc n)) = refl
predInt-neg (negsuc  zero  ) = refl
predInt-neg (negsuc (suc n)) = refl

sucInt-neg : ∀ a → sucInt (- a) ≡ - (predInt a)
sucInt-neg (pos     zero        ) = refl
sucInt-neg (pos    (suc zero)   ) = refl
sucInt-neg (pos    (suc (suc n))) = refl
sucInt-neg (negsuc  zero        ) = refl
sucInt-neg (negsuc (suc n)      ) = refl

·-neg1 : ∀ x → -1 · x ≡ - x
·-neg1 x = sym (neg-signed-not (sgn x) (abs x +ⁿ 0)) ∙ (λ i → - signed (sgn x) (ℕ.+-comm (abs x) 0 i)) ∙ cong -_ (signed-inv x)

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
