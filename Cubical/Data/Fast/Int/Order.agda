{- Order as an Indexed Data Type, as done in Agda stdlib and 1Lab -}
module Cubical.Data.Fast.Int.Order where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.Relation.Binary
open import Cubical.Relation.Nullary

open import Cubical.Data.Bool hiding (_≟_ ; _≤_ ; _≥_ ; isProp≤)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ using ()
open import Cubical.Data.Nat.Order.Inductive as ℕ
open import Cubical.Data.Fast.Int as ℤ

private
  variable
    m n o s : ℤ
    k l : ℕ

infix 4 _≤_ _<_ _≥_ _>_

data _≤_ : ℤ → ℤ → Type where
  pos≤pos       : ∀ {x y} → x ℕ.≤ᵗ y → pos x    ≤ pos y
  negsuc≤negsuc : ∀ {x y} → x ℕ.≥ᵗ y → negsuc x ≤ negsuc y
  negsuc≤pos    : ∀ {x y}            → negsuc x ≤ pos y

data _<_ : ℤ → ℤ → Type where
  pos<pos       : ∀ {x y} → x ℕ.<ᵗ y → pos x    < pos y
  negsuc<negsuc : ∀ {x y} → x ℕ.>ᵗ y → negsuc x < negsuc y
  negsuc<pos    : ∀ {x y}            → negsuc x < pos y

_≥_ _>_ : ℤ → ℤ → Type
_≥_ = flip _≤_
_>_ = flip _<_

¬pos≤negsuc : ∀ {x y} → ¬ pos x ≤ negsuc y
¬pos≤negsuc ()

¬pos<negsuc : ∀ {x y} → ¬ pos x < negsuc y
¬pos<negsuc ()

¬≤ℕ→¬pos≤pos : ∀ {x y} → ¬ (x ℕ.≤ᵗ y) → ¬ pos x ≤ pos y
¬≤ℕ→¬pos≤pos ¬p (pos≤pos p) = ¬p p

¬<ℕ→¬pos<pos : ∀ {x y} → ¬ (x ℕ.<ᵗ y) → ¬ pos x < pos y
¬<ℕ→¬pos<pos ¬p (pos<pos p) = ¬p p

¬≥ℕ→¬negsuc≤negsuc : ∀ {x y} → ¬ (x ℕ.≥ᵗ y) → ¬ negsuc x ≤ negsuc y
¬≥ℕ→¬negsuc≤negsuc ¬p (negsuc≤negsuc p) = ¬p p

¬>ℕ→¬negsuc<negsuc : ∀ {x y} → ¬ (x ℕ.>ᵗ y) → ¬ negsuc x < negsuc y
¬>ℕ→¬negsuc<negsuc ¬p (negsuc<negsuc p) = ¬p p

{-# DISPLAY negsuc≤negsuc {x} {y} _ = negsuc x ≤ negsuc y #-}
{-# DISPLAY pos≤pos       {x} {y} _ =    pos x ≤ pos y #-}
{-# DISPLAY negsuc≤pos    {x} {y}   = negsuc x ≤ pos y #-}

{-# DISPLAY negsuc<negsuc {x} {y} _ = negsuc x < negsuc y #-}
{-# DISPLAY pos<pos       {x} {y} _ =    pos x < pos y #-}
{-# DISPLAY negsuc<pos    {x} {y}   = negsuc x < pos y #-}

{-# DISPLAY ¬≤ℕ→¬pos≤pos       {x} {y} _ = ¬ pos x    ≤ pos y    #-}
{-# DISPLAY ¬≥ℕ→¬negsuc≤negsuc {x} {y} _ = ¬ negsuc x ≤ negsuc y #-}
{-# DISPLAY ¬pos≤negsuc        {x} {y}   = ¬    pos x ≤ negsuc y #-}

{-# DISPLAY ¬<ℕ→¬pos<pos       {x} {y} _ = ¬ pos x    < pos y    #-}
{-# DISPLAY ¬>ℕ→¬negsuc<negsuc {x} {y} _ = ¬ negsuc x < negsuc y #-}
{-# DISPLAY ¬pos<negsuc        {x} {y}   = ¬    pos x < negsuc y #-}

isProp≤ : isProp (m ≤ n)
isProp≤ (pos≤pos p)       (pos≤pos q)       = cong pos≤pos (isPropBool→Type p q)
isProp≤  negsuc≤pos        negsuc≤pos       = refl
isProp≤ (negsuc≤negsuc p) (negsuc≤negsuc q) = cong negsuc≤negsuc (isPropBool→Type p q)

isProp< : isProp (m < n)
isProp< (pos<pos p)       (pos<pos q)       = cong pos<pos (isPropBool→Type p q)
isProp<  negsuc<pos        negsuc<pos       = refl
isProp< (negsuc<negsuc p) (negsuc<negsuc q) = cong negsuc<negsuc (isPropBool→Type p q)

_≤?_ ≤Dec : ∀ m n → Dec (m ≤ n)
pos m    ≤? pos n    = mapDec pos≤pos ¬≤ℕ→¬pos≤pos DecBool→Type
pos m    ≤? negsuc n = no ¬pos≤negsuc
negsuc m ≤? pos n    = yes negsuc≤pos
negsuc m ≤? negsuc n = mapDec negsuc≤negsuc ¬≥ℕ→¬negsuc≤negsuc DecBool→Type

≤Dec = _≤?_

_<?_ <Dec : ∀ m n → Dec (m < n)
pos m    <? pos n    = mapDec pos<pos ¬<ℕ→¬pos<pos DecBool→Type
pos m    <? negsuc n = no ¬pos<negsuc
negsuc m <? pos n    = yes negsuc<pos
negsuc m <? negsuc n = mapDec negsuc<negsuc ¬>ℕ→¬negsuc<negsuc DecBool→Type

<Dec = _<?_

≤Stable : ∀ m n → Stable (m ≤ n)
≤Stable m n = Dec→Stable (m ≤? n)

<Stable : ∀ m n → Stable (m < n)
<Stable m n = Dec→Stable (m <? n)

-- auxilary functions to speed up proofs, relying on the decidability of order

recompute< : (m < n) → (m < n)
recompute< p = decRec (idfun _) (λ _ → p) (_ <? _)

recompute≤ : (m ≤ n) → (m ≤ n)
recompute≤ p = decRec (idfun _) (λ _ → p) (_ ≤? _)

recompute¬< : ¬ (m < n) → ¬ (m < n)
recompute¬< p = decRec (λ _ → p) (idfun _) (_ <? _)

recompute¬≤ : ¬ (m ≤ n) → ¬ (m ≤ n)
recompute¬≤ p = decRec (λ _ → p) (idfun _) (_ ≤? _)

-- properties of _<_ and _≤_

zero-≤pos : 0 ≤ pos l
zero-≤pos = pos≤pos tt

zero-<possuc : 0 < pos (suc l)
zero-<possuc = pos<pos tt

negsuc≤-zero : negsuc k ≤ 0
negsuc≤-zero = negsuc≤pos

negsuc<-zero : negsuc k < 0
negsuc<-zero = negsuc<pos

¬-pos<-zero : ¬ (pos k) < 0
¬-pos<-zero (pos<pos ())

suc-≤-suc : m ≤ n → sucℤ m ≤ sucℤ n
suc-≤-suc {pos m}          {pos n}          (pos≤pos p)       = pos≤pos p
suc-≤-suc {negsuc zero}    {pos n}           negsuc≤pos       = pos≤pos tt
suc-≤-suc {negsuc (suc m)} {pos n}           negsuc≤pos       = negsuc≤pos
suc-≤-suc {negsuc zero}    {negsuc zero}    (negsuc≤negsuc p) = pos≤pos tt
suc-≤-suc {negsuc (suc m)} {negsuc zero}    (negsuc≤negsuc p) = negsuc≤pos
suc-≤-suc {negsuc (suc m)} {negsuc (suc n)} (negsuc≤negsuc p) = negsuc≤negsuc p

suc-<-suc : m < n → sucℤ m < sucℤ n
suc-<-suc {pos m}          {pos n}          (pos<pos p)       = pos<pos p
suc-<-suc {negsuc zero}    {pos n}           negsuc<pos       = pos<pos tt
suc-<-suc {negsuc (suc m)} {pos n}           negsuc<pos       = negsuc<pos
suc-<-suc {negsuc (suc m)} {negsuc zero}    (negsuc<negsuc p) = negsuc<pos
suc-<-suc {negsuc (suc m)} {negsuc (suc n)} (negsuc<negsuc p) = negsuc<negsuc p

pred-≤-pred : sucℤ m ≤ sucℤ n → m ≤ n
pred-≤-pred {pos m}          {pos n}          (pos≤pos p)       = pos≤pos p
pred-≤-pred {pos zero}       {negsuc zero}    (pos≤pos ())
pred-≤-pred {negsuc m}       {pos n}           _                = negsuc≤pos
pred-≤-pred {negsuc zero}    {negsuc zero}    (pos≤pos p)       = negsuc≤negsuc tt
pred-≤-pred {negsuc (suc m)} {negsuc zero}     negsuc≤pos       = negsuc≤negsuc tt
pred-≤-pred {negsuc (suc m)} {negsuc (suc n)} (negsuc≤negsuc p) = negsuc≤negsuc p

pred-<-pred : sucℤ m < sucℤ n → m < n
pred-<-pred {pos m}          {pos n}          (pos<pos p)       = pos<pos p
pred-<-pred {pos zero}       {negsuc zero}    (pos<pos ())
pred-<-pred {negsuc m}       {pos n}           _                = negsuc<pos
pred-<-pred {negsuc zero}    {negsuc zero}    (pos<pos ())
pred-<-pred {negsuc (suc m)} {negsuc zero}     negsuc<pos       = negsuc<negsuc tt
pred-<-pred {negsuc (suc m)} {negsuc (suc n)} (negsuc<negsuc p) = negsuc<negsuc p

predℤ-≤-predℤ : m ≤ n → predℤ m ≤ predℤ n
predℤ-≤-predℤ {pos zero}    {pos zero}    (pos≤pos p)       = negsuc≤negsuc tt
predℤ-≤-predℤ {pos zero}    {pos (suc n)} (pos≤pos p)       = negsuc≤pos
predℤ-≤-predℤ {pos (suc m)} {pos (suc n)} (pos≤pos p)       = pos≤pos p
predℤ-≤-predℤ {negsuc m}    {pos zero}     negsuc≤pos       = negsuc≤negsuc tt
predℤ-≤-predℤ {negsuc m}    {pos (suc n)}  negsuc≤pos       = negsuc≤pos
predℤ-≤-predℤ {negsuc m}    {negsuc n}    (negsuc≤negsuc p) = negsuc≤negsuc p

predℤ-<-predℤ : m < n → predℤ m < predℤ n
predℤ-<-predℤ {pos zero}    {pos (suc n)} (pos<pos p)       = negsuc<pos
predℤ-<-predℤ {pos (suc m)} {pos (suc n)} (pos<pos p)       = pos<pos p
predℤ-<-predℤ {negsuc m}    {pos zero}     negsuc<pos       = negsuc<negsuc tt
predℤ-<-predℤ {negsuc m}    {pos (suc n)}  negsuc<pos       = negsuc<pos
predℤ-<-predℤ {negsuc m}    {negsuc n}    (negsuc<negsuc p) = negsuc<negsuc p

pos≤pos→negsuc≥negsuc : pos k ≤ pos l → negsuc k ≥ negsuc l
pos≤pos→negsuc≥negsuc (pos≤pos p) = negsuc≤negsuc p

pos<pos→negsuc>negsuc : pos k < pos l → negsuc k > negsuc l
pos<pos→negsuc>negsuc (pos<pos p) = negsuc<negsuc p

negsuc≤negsuc→pos≥pos : negsuc k ≤ negsuc l → pos k ≥ pos l
negsuc≤negsuc→pos≥pos (negsuc≤negsuc p) = pos≤pos p

negsuc<negsuc→pos>pos : negsuc k < negsuc l → pos k > pos l
negsuc<negsuc→pos>pos (negsuc<negsuc p) = pos<pos p

pos≤pos→neg≥neg : pos k ≤ pos l → neg k ≥ neg l
pos≤pos→neg≥neg {zero}  {zero}  (pos≤pos p) = pos≤pos tt
pos≤pos→neg≥neg {zero}  {suc l} (pos≤pos p) = negsuc≤pos
pos≤pos→neg≥neg {suc k} {suc l} (pos≤pos p) = negsuc≤negsuc p

pos<pos→neg>neg : pos k < pos l → neg k > neg l
pos<pos→neg>neg {zero}  {suc l} (pos<pos p) = negsuc<pos
pos<pos→neg>neg {suc k} {suc l} (pos<pos p) = negsuc<negsuc p

<→suc≤ : m < n → sucℤ m ≤ n
<→suc≤ {pos m}          {pos n}    (pos<pos p)       = pos≤pos p
<→suc≤ {negsuc zero}    {pos n}     negsuc<pos       = pos≤pos tt
<→suc≤ {negsuc (suc m)} {pos n}     negsuc<pos       = negsuc≤pos
<→suc≤ {negsuc (suc m)} {negsuc n} (negsuc<negsuc p) = negsuc≤negsuc p

suc≤→< : sucℤ m ≤ n → m < n
suc≤→< {pos m}          {pos n}    (pos≤pos p)       = pos<pos p
suc≤→< {negsuc m}       {pos n}     _                = negsuc<pos
suc≤→< {negsuc (suc m)} {negsuc n} (negsuc≤negsuc p) = negsuc<negsuc p

<≃suc≤ : (m < n) ≃ (sucℤ m ≤ n)
<≃suc≤ = propBiimpl→Equiv isProp< isProp≤ <→suc≤ suc≤→<

<≡suc≤ : (m < n) ≡ (sucℤ m ≤ n)
<≡suc≤ = ua <≃suc≤

≤→<suc : m ≤ n → m < sucℤ n
≤→<suc {pos m}    {pos n}          (pos≤pos p)       = pos<pos p
≤→<suc {negsuc m} {pos n}           negsuc≤pos       = negsuc<pos
≤→<suc {negsuc m} {negsuc zero}    (negsuc≤negsuc p) = negsuc<pos
≤→<suc {negsuc m} {negsuc (suc n)} (negsuc≤negsuc p) = negsuc<negsuc p

<suc→≤ : m < sucℤ n → m ≤ n
<suc→≤ {pos m}          {pos n}          (pos<pos p)       = pos≤pos p
<suc→≤ {negsuc m}       {pos n}           negsuc<pos       = negsuc≤pos
<suc→≤ {pos m}          {negsuc zero}    (pos<pos ())
<suc→≤ {negsuc m}       {negsuc zero}     negsuc<pos       = negsuc≤negsuc tt
<suc→≤ {negsuc (suc m)} {negsuc (suc n)} (negsuc<negsuc p) = negsuc≤negsuc p

≤≃<suc : (m ≤ n) ≃ (m < sucℤ n)
≤≃<suc = propBiimpl→Equiv isProp≤ isProp< ≤→<suc <suc→≤

≤≡<suc : (m ≤ n) ≡ (m < sucℤ n)
≤≡<suc = ua ≤≃<suc

≤-+o : m ≤ n → m ℤ.+ o ≤ n ℤ.+ o
≤-+o = recompute≤ ∘ proof _ _ _ where
  proof : ∀ m n o → m ≤ n → m ℤ.+ o ≤ n ℤ.+ o
  proof m n (pos zero)       = subst2 _≤_ (sym (ℤ.+IdR m)) (sym (ℤ.+IdR n))
  proof m n (pos (suc k))    = subst2 _≤_
    (+sucℤ m _) (+sucℤ n _) ∘ suc-≤-suc ∘ proof m n (pos k)
  proof m n (negsuc zero)    = subst2 _≤_ (+negsuc0 m) (+negsuc0 n) ∘ predℤ-≤-predℤ
  proof m n (negsuc (suc k)) = subst2 _≤_
    (+predℤ m _) (+predℤ n _) ∘ predℤ-≤-predℤ ∘ proof m n (negsuc k)

<-+o : m < n → (m ℤ.+ o) < (n ℤ.+ o)
<-+o {m} {n} {o} = recompute< ∘ suc≤→< ∘ subst (_≤ _) (sym (sucℤ+ m o)) ∘ ≤-+o ∘ <→suc≤

≤SumRightPos : n ≤ pos k ℤ.+ n
≤SumRightPos {n} {k} = recompute≤ $ subst (_≤ pos k ℤ.+ n) (ℤ.+IdL n) (≤-+o {o = n} zero-≤pos)

<SumRightPosSuc : n < pos (suc k) ℤ.+ n
<SumRightPosSuc {n} {k} = recompute< $ subst (_< pos (suc k) ℤ.+ n) (ℤ.+IdL n) (<-+o {o = n} zero-<possuc)

≤-o+ : m ≤ n → o ℤ.+ m ≤ o ℤ.+ n
≤-o+ {m} {n} {o} = recompute≤ ∘ subst2 (_≤_) (+Comm m o) (+Comm n o) ∘ ≤-+o

<-o+ : m < n → (o ℤ.+ m) < (o ℤ.+ n)
<-o+ {m} {n} {o} = recompute< ∘ subst2 (_<_) (+Comm m o) (+Comm n o) ∘ <-+o

≤SumLeftPos : n ≤ n ℤ.+ pos k
≤SumLeftPos {n} {k} = recompute≤ $ subst (n ≤_) (+Comm (pos k) n) ≤SumRightPos

<SumLeftPosSuc : n < n ℤ.+ pos (suc k)
<SumLeftPosSuc {n} {k} = recompute< $ subst (n <_) (+Comm (pos (suc k)) n) <SumRightPosSuc

isRefl≤ : m ≤ m
isRefl≤ = recompute≤ $ proof _ where
  proof : ∀ m → m ≤ m
  proof (pos zero)       = pos≤pos tt
  proof (pos (suc n))    = suc-≤-suc (proof (pos n))
  proof (negsuc zero)    = negsuc≤negsuc tt
  proof (negsuc (suc n)) = predℤ-≤-predℤ (proof (negsuc n))

≤-suc : m ≤ n → m ≤ sucℤ n
≤-suc = recompute≤ ∘ proof _ _ where
  proof : ∀ m n → m ≤ n → m ≤ sucℤ n
  proof (pos zero)       (pos zero)             (pos≤pos p)       = pos≤pos tt
  proof (pos zero)       (pos (suc n))          (pos≤pos p)       = pos≤pos tt
  proof (pos (suc m))    (pos (suc n))          (pos≤pos p)       =
    suc-≤-suc (proof (pos m) (pos n) (pos≤pos p))
  proof (negsuc m)       (pos n)                 negsuc≤pos       = negsuc≤pos
  proof (negsuc zero)    (negsuc zero)          (negsuc≤negsuc p) = negsuc≤pos
  proof (negsuc (suc m)) (negsuc zero)          (negsuc≤negsuc p) = negsuc≤pos
  proof (negsuc (suc m)) (negsuc (suc zero))    (negsuc≤negsuc p) = negsuc≤negsuc tt
  proof (negsuc (suc m)) (negsuc (suc (suc n))) (negsuc≤negsuc p) =
    predℤ-≤-predℤ (proof (negsuc m) (negsuc (suc n)) (negsuc≤negsuc p))

suc-< : sucℤ m < n → m < n
suc-< = suc≤→< ∘ pred-≤-pred ∘ ≤-suc ∘ <→suc≤

≤-sucℤ : n ≤ sucℤ n
≤-sucℤ = ≤-suc isRefl≤

<-sucℤ : n < sucℤ n
<-sucℤ = ≤→<suc isRefl≤

isTrans≤ : m ≤ n → n ≤ o → m ≤ o
isTrans≤ = (recompute≤ ∘_) ∘ proof _ _ _ where
  proof : ∀ m n o → m ≤ n → n ≤ o → m ≤ o
  proof (pos zero)       (pos zero)       (pos zero)       (pos≤pos p)       (pos≤pos q)       =
    pos≤pos tt
  proof (pos zero)       (pos zero)       (pos (suc o))    (pos≤pos p)       (pos≤pos q)       =
    pos≤pos tt
  proof (pos zero)       (pos (suc n))    (pos (suc o))    (pos≤pos p)       (pos≤pos q)       =
    pos≤pos tt
  proof (pos (suc m))    (pos (suc n))    (pos (suc o))    (pos≤pos p)       (pos≤pos q)       =
    suc-≤-suc (proof (pos m) (pos n) (pos o) (pos≤pos p) (pos≤pos q))
  proof (negsuc m)       (pos n)          (pos o)           negsuc≤pos       (pos≤pos q)       =
    negsuc≤pos
  proof (negsuc m)       (negsuc n)       (pos o)          (negsuc≤negsuc p)  negsuc≤pos       =
    negsuc≤pos
  proof (negsuc zero)    (negsuc zero)    (negsuc zero)    (negsuc≤negsuc p) (negsuc≤negsuc q) =
    negsuc≤negsuc tt
  proof (negsuc (suc m)) (negsuc zero)    (negsuc zero)    (negsuc≤negsuc p) (negsuc≤negsuc q) =
    negsuc≤negsuc tt
  proof (negsuc (suc m)) (negsuc (suc n)) (negsuc zero)    (negsuc≤negsuc p) (negsuc≤negsuc q) =
    negsuc≤negsuc tt
  proof (negsuc (suc m)) (negsuc (suc n)) (negsuc (suc o)) (negsuc≤negsuc p) (negsuc≤negsuc q) =
    predℤ-≤-predℤ (proof (negsuc m) (negsuc n) (negsuc o) (negsuc≤negsuc p) (negsuc≤negsuc q))

isTrans< : m < n → n < o → m < o
isTrans< = (recompute< ∘_) ∘ proof _ _ _ where
  proof : ∀ m n o → m < n → n < o → m < o
  proof (pos zero)       (pos (suc n))    (pos (suc o))    (pos<pos p)       (pos<pos q)       =
    pos<pos tt
  proof (pos (suc m))    (pos (suc n))    (pos (suc o))    (pos<pos p)       (pos<pos q)       =
    suc-<-suc (proof (pos m) (pos n) (pos o) (pos<pos p) (pos<pos q))
  proof (negsuc m)       (pos n)          (pos o)           negsuc<pos       (pos<pos q)       =
    negsuc<pos
  proof (negsuc m)       (negsuc n)       (pos o)          (negsuc<negsuc p)  negsuc<pos       =
    negsuc<pos
  proof (negsuc (suc m)) (negsuc (suc n)) (negsuc zero)    (negsuc<negsuc p) (negsuc<negsuc q) =
    negsuc<negsuc tt
  proof (negsuc (suc m)) (negsuc (suc n)) (negsuc (suc o)) (negsuc<negsuc p) (negsuc<negsuc q) =
    predℤ-<-predℤ (proof (negsuc m) (negsuc n) (negsuc o) (negsuc<negsuc p) (negsuc<negsuc q))

-- this proof will not normalize quickly when m and n are the same large number
isAntisym≤ : m ≤ n → n ≤ m → m ≡ n
isAntisym≤ {pos zero}       {pos zero}       (pos≤pos p)       (pos≤pos q)       = refl
isAntisym≤ {pos (suc m)}    {pos (suc n)}    (pos≤pos p)       (pos≤pos q)       =
  cong sucℤ (isAntisym≤ (pos≤pos p) (pos≤pos q))
isAntisym≤ {negsuc zero}    {negsuc zero}    (negsuc≤negsuc p) (negsuc≤negsuc q) = refl
isAntisym≤ {negsuc (suc m)} {negsuc (suc n)} (negsuc≤negsuc p) (negsuc≤negsuc q) =
  cong predℤ (isAntisym≤ (negsuc≤negsuc p) (negsuc≤negsuc q))

≤Monotone+ : m ≤ n → o ≤ s → m ℤ.+ o ≤ n ℤ.+ s
≤Monotone+ {n = n} p = isTrans≤ (≤-+o p) ∘ ≤-o+ {o = n}

<Monotone+ : m < n → o < s → m ℤ.+ o < n ℤ.+ s
<Monotone+ {n = n} p = isTrans< (<-+o p) ∘ <-o+ {o = n}

≤-o+-cancel : o ℤ.+ m ≤ o ℤ.+ n → m ≤ n
≤-o+-cancel {o} {m} {n} = recompute≤ ∘ subst2 _≤_
  (ℤ.+Assoc (ℤ.- o) o m ∙∙ cong (ℤ._+ m) (ℤ.-Cancel' o) ∙∙ ℤ.+IdL m)
  (ℤ.+Assoc (ℤ.- o) o n ∙∙ cong (ℤ._+ n) (ℤ.-Cancel' o) ∙∙ ℤ.+IdL n)
  ∘ ≤-o+ {o = ℤ.- o}

<-o+-cancel : o ℤ.+ m < o ℤ.+ n → m < n
<-o+-cancel {o} {m} {n} = recompute< ∘ subst2 _<_
  (ℤ.+Assoc (ℤ.- o) o m ∙∙ cong (ℤ._+ m) (ℤ.-Cancel' o) ∙∙ ℤ.+IdL m)
  (ℤ.+Assoc (ℤ.- o) o n ∙∙ cong (ℤ._+ n) (ℤ.-Cancel' o) ∙∙ ℤ.+IdL n)
  ∘ <-o+ {o = ℤ.- o}

≤-+o-cancel : m ℤ.+ o ≤ n ℤ.+ o → m ≤ n
≤-+o-cancel {m} {o} {n} = ≤-o+-cancel {o = o} ∘ subst2 _≤_ (ℤ.+Comm m o) (ℤ.+Comm n o)

<-+o-cancel : m ℤ.+ o < n ℤ.+ o → m < n
<-+o-cancel {m} {o} {n} = <-o+-cancel {o = o} ∘ subst2 _<_ (ℤ.+Comm m o) (ℤ.+Comm n o)

≤-+pos-trans : m ℤ.+ pos k ≤ n → m ≤ n
≤-+pos-trans = isTrans≤ ≤SumLeftPos

≤-pos+-trans : pos k ℤ.+ m ≤ n → m ≤ n
≤-pos+-trans = isTrans≤ ≤SumRightPos

≤-·o : m ≤ n → m ℤ.· pos k ≤ n ℤ.· pos k
≤-·o = recompute≤ ∘ proof _ _ _ where
  proof : ∀ m n k → m ≤ n → m ℤ.· pos k ≤ n ℤ.· pos k
  proof m n zero    _ = subst2 _≤_ (sym (ℤ.·AnnihilR m)) (sym (ℤ.·AnnihilR n)) zero-≤pos
  proof (pos zero)       (pos zero)       (suc k) (pos≤pos p)       = zero-≤pos
  proof (pos zero)       (pos (suc n))    (suc k) (pos≤pos p)       = zero-≤pos
  proof (pos (suc m))    (pos (suc n))    (suc k) (pos≤pos p)       =
    ≤-o+ {o = pos (suc k)} (proof (pos m) (pos n) (suc k) (pos≤pos p))
  proof (negsuc m)       (pos n)          (suc k)  negsuc≤pos       = negsuc≤pos
  proof (negsuc zero)    (negsuc zero)    (suc k) (negsuc≤negsuc p) = isRefl≤
  proof (negsuc (suc m)) (negsuc zero)    (suc k) (negsuc≤negsuc p) =
    pos≤pos→negsuc≥negsuc
      (subst (_≤ pos k ℤ.+ pos (suc m ℕ.· suc k)) (sym (ℤ.+IdR (pos k))) ≤SumLeftPos)
  proof (negsuc (suc m)) (negsuc (suc n)) (suc k) (negsuc≤negsuc p) =
    subst2 _≤_
      (sym (predℤ· (negsuc m) (pos (suc k)))) (sym (predℤ· (negsuc n) (pos (suc k))))
      (≤-o+ {o = negsuc k} (proof (negsuc m) (negsuc n) (suc k) (negsuc≤negsuc p)))

0≤o→≤-·o : 0 ≤ o → m ≤ n → m ℤ.· o ≤ n ℤ.· o
0≤o→≤-·o (pos≤pos p) = ≤-·o

<-·o : m < n → m ℤ.· pos (suc k) < n ℤ.· pos (suc k)
<-·o = recompute< ∘ proof _ _ _ where
  proof : ∀ m n k → m < n → m ℤ.· pos (suc k) < n ℤ.· pos (suc k)
  proof (pos zero)       (pos (suc n))    k (pos<pos p)       = zero-<possuc
  proof (pos (suc m))    (pos (suc n))    k (pos<pos p)       =
    <-o+ {o = pos (suc k)} (proof (pos m) (pos n) k (pos<pos p))
  proof (negsuc m)       (pos n)          k  negsuc<pos       = negsuc<pos
  proof (negsuc (suc m)) (negsuc zero)    k (negsuc<negsuc p) =
    pos<pos→negsuc>negsuc
      (subst (_< pos k ℤ.+ pos (suc m ℕ.· suc k)) (sym (ℤ.+IdR (pos k))) <SumLeftPosSuc)
  proof (negsuc (suc m)) (negsuc (suc n)) k (negsuc<negsuc p) =
    subst2 _<_
      (sym (predℤ· (negsuc m) (pos (suc k)))) (sym (predℤ· (negsuc n) (pos (suc k))))
      (<-o+ {o = negsuc k} (proof (negsuc m) (negsuc n) k (negsuc<negsuc p)))

0<o→<-·o : 0 < o → m < n → m ℤ.· o < n ℤ.· o
0<o→<-·o {pos (suc k)} (pos<pos p) = <-·o

<-weaken : m < n → m ≤ n
<-weaken = <suc→≤ ∘ flip isTrans< <-sucℤ

isIrrefl< : ¬ m < m
isIrrefl< = recompute¬< $ proof _ where
  proof : ∀ m → ¬ m < m
  proof (pos (suc m))    (pos<pos p)       = proof (pos m)    (pos<pos p)
  proof (negsuc (suc m)) (negsuc<negsuc p) = proof (negsuc m) (negsuc<negsuc p)

pos≤0→≡0 : pos k ≤ 0 → pos k ≡ 0
pos≤0→≡0 {zero} (pos≤pos x) = refl

¬m+posk<m : ¬ m ℤ.+ pos k < m
¬m+posk<m {m} {k} = recompute¬< $ ¬-pos<-zero ∘ <-o+-cancel {m} ∘ subst (m ℤ.+ pos k <_) (sym (ℤ.+IdR m))

≤<-trans : o ≤ m → m < n → o < n
≤<-trans p = suc≤→< ∘ isTrans≤ (suc-≤-suc p) ∘ <→suc≤

<≤-trans : o < m → m ≤ n → o < n
<≤-trans = (suc≤→< ∘_) ∘ isTrans≤ ∘ <→suc≤

isAsym< : m < n → ¬ n ≤ m
isAsym< = recompute¬≤ ∘ proof _ _ where
  proof : ∀ m n → m < n → ¬ n ≤ m
  proof (pos (suc m))    (pos (suc n))    (pos<pos p)       (pos≤pos q) =
    proof (pos m) (pos n) (pos<pos p) (pos≤pos q)
  proof (negsuc (suc m)) (negsuc (suc n)) (negsuc<negsuc p) (negsuc≤negsuc q) =
    proof (negsuc m) (negsuc n) (negsuc<negsuc p) (negsuc≤negsuc q)

isAsym'< : ¬ m < n → n ≤ m
isAsym'< = recompute≤ ∘ proof _ _ where
  proof : ∀ m n → ¬ m < n → n ≤ m
  proof (pos m)          (pos zero)       ¬p = zero-≤pos
  proof (pos zero)       (pos (suc n))    ¬p = ⊥.rec (¬p zero-<possuc)
  proof (pos (suc m))    (pos (suc n))    ¬p =
    suc-≤-suc (proof (pos m) (pos n) (¬p ∘ suc-<-suc))
  proof (pos m)          (negsuc n)       ¬p = negsuc≤pos
  proof (negsuc m)       (pos n)          ¬p = ⊥.rec (¬p negsuc<pos)
  proof (negsuc zero)    (negsuc n)       ¬p = negsuc≤negsuc tt
  proof (negsuc (suc m)) (negsuc zero)    ¬p = ⊥.rec (¬p (negsuc<negsuc tt))
  proof (negsuc (suc m)) (negsuc (suc n)) ¬p =
    pred-≤-pred (proof (negsuc m) (negsuc n) (¬p ∘ pred-<-pred))

<-+pos-trans : m ℤ.+ pos k < n → m < n
<-+pos-trans = ≤<-trans ≤SumLeftPos

<-pos+-trans : pos k ℤ.+ m < n → m < n
<-pos+-trans = ≤<-trans ≤SumRightPos

<-+-≤ : m < n → o ≤ s → m ℤ.+ o < n ℤ.+ s
<-+-≤ {n = n} p = <≤-trans (<-+o p) ∘ ≤-o+ {o = n}

-Dist≤ : m ≤ n → (- n) ≤ (- m)
-Dist≤ {pos zero}    {pos zero}    (pos≤pos p)       = pos≤pos tt
-Dist≤ {pos zero}    {pos (suc n)} (pos≤pos p)       = negsuc≤pos
-Dist≤ {pos (suc m)} {pos (suc n)} (pos≤pos p)       = negsuc≤negsuc p
-Dist≤ {negsuc m}    {pos zero}     negsuc≤pos       = pos≤pos tt
-Dist≤ {negsuc m}    {pos (suc n)}  negsuc≤pos       = negsuc≤pos
-Dist≤ {negsuc m}    {negsuc n}    (negsuc≤negsuc p) = pos≤pos p

-Dist< : m < n → (- n) < (- m)
-Dist< {pos zero}    {pos (suc n)} (pos<pos p)       = negsuc<pos
-Dist< {pos (suc m)} {pos (suc n)} (pos<pos p)       = negsuc<negsuc p
-Dist< {negsuc m}    {pos zero}     negsuc<pos       = pos<pos tt
-Dist< {negsuc m}    {pos (suc n)}  negsuc<pos       = negsuc<pos
-Dist< {negsuc m}    {negsuc n}    (negsuc<negsuc p) = pos<pos p

-pos≤ : m - (pos k) ≤ m
-pos≤ {m} {k} = recompute≤ $ subst (m - pos k ≤_) (ℤ.+IdR m) (≤-o+ {o = m} (-Dist≤ zero-≤pos))

≤→0≤Δ : m ≤ n → 0 ≤ n ℤ.- m
≤→0≤Δ {m} {n} = recompute≤ ∘ subst (_≤ n ℤ.- m) (ℤ.-Cancel m) ∘ ≤-+o

<→0<Δ : m < n → 0 < n ℤ.- m
<→0<Δ {m} {n} = recompute< ∘ subst (_< n ℤ.- m) (ℤ.-Cancel m) ∘ <-+o

0≤Δ→≤ : 0 ≤ n ℤ.- m → m ≤ n
0≤Δ→≤ {n} {m} = recompute≤ ∘ subst2 _≤_ (ℤ.+IdL m) (ℤ.minusPlus m n) ∘ ≤-+o

0<Δ→< : 0 < n ℤ.- m → m < n
0<Δ→< {n} {m} = recompute< ∘ subst2 _<_ (ℤ.+IdL m) (ℤ.minusPlus m n) ∘ <-+o

0≤→abs≡id : 0 ≤ n → pos (abs n) ≡ n
0≤→abs≡id {pos n} _ = refl

0<→abs≡id : 0 < n → pos (abs n) ≡ n
0<→abs≡id {pos n} _ = refl

·suc≤0 : m ℤ.· (pos (suc k)) ≤ 0 → m ≤ 0
·suc≤0 {pos zero} (pos≤pos p) = pos≤pos tt
·suc≤0 {negsuc n}  _          = negsuc≤pos

·suc<0 : m ℤ.· (pos (suc k)) < 0 → m < 0
·suc<0 {pos n}    (pos<pos ())
·suc<0 {negsuc n}  _          = negsuc<pos

0≤·suc-cancel : 0 ≤ m ℤ.· pos (suc k) → 0 ≤ m
0≤·suc-cancel {pos n} _ = zero-≤pos

0<·suc-cancel : 0 < m ℤ.· pos (suc k) → 0 < m
0<·suc-cancel {pos (suc n)} (pos<pos p) = zero-<possuc

0≤suc·-cancel : 0 ≤ pos (suc k) ℤ.· m → 0 ≤ m
0≤suc·-cancel {m = pos n} _ = zero-≤pos

0<suc·-cancel : 0 < pos (suc k) ℤ.· m → 0 < m
0<suc·-cancel {k} {pos zero}    p = subst (0 <_) (ℤ.·AnnihilR (pos (suc k))) p
0<suc·-cancel {k} {pos (suc n)} _ = zero-<possuc

≤-·o-cancel : m ℤ.· pos (suc k) ≤ n ℤ.· pos (suc k) → m ≤ n
≤-·o-cancel {m} {n = n} = 0≤Δ→≤ ∘ 0≤·suc-cancel
  ∘ subst (0 ≤_) (cong (n ℤ.· _ ℤ.+_) (ℤ.-DistL· m _) ∙ sym (ℤ.·DistL+ n (ℤ.- m) _))
  ∘ ≤→0≤Δ

<-·o-cancel : m ℤ.· pos (suc k) < n ℤ.· pos (suc k) → m < n
<-·o-cancel {m} {n = n} = 0<Δ→< ∘ 0<·suc-cancel
  ∘ subst (0 <_) (cong (n ℤ.· _ ℤ.+_) (ℤ.-DistL· m _) ∙ sym (ℤ.·DistL+ n (ℤ.- m) _))
  ∘ <→0<Δ

0<o→≤-·o-cancel : 0 < o → m ℤ.· o ≤ n ℤ.· o → m ≤ n
0<o→≤-·o-cancel {pos (suc k)} (pos<pos p) = ≤-·o-cancel

0<o→<-·o-cancel : 0 < o → m ℤ.· o < n ℤ.· o → m < n
0<o→<-·o-cancel {pos (suc k)} (pos<pos p) = <-·o-cancel

≤-o·-cancel : (pos (suc k)) ℤ.· m ≤ (pos (suc k)) ℤ.· n → m ≤ n
≤-o·-cancel {m = m} {n} = ≤-·o-cancel ∘ subst2 _≤_ (ℤ.·Comm _ m) (ℤ.·Comm _ n)

<-o·-cancel : (pos (suc k)) ℤ.· m < (pos (suc k)) ℤ.· n → m < n
<-o·-cancel {m = m} {n} = <-·o-cancel ∘ subst2 _<_ (ℤ.·Comm _ m) (ℤ.·Comm _ n)

0<o→≤-o·-cancel : 0 < o → o ℤ.· m ≤ o ℤ.· n → m ≤ n
0<o→≤-o·-cancel {pos (suc k)} (pos<pos p) = ≤-o·-cancel

0<o→<-o·-cancel : 0 < o → o ℤ.· m < o ℤ.· n → m < n
0<o→<-o·-cancel {pos (suc k)} (pos<pos p) = <-o·-cancel

≤max : m ≤ ℤ.max m n
≤max {pos zero}       {pos n}          = zero-≤pos
≤max {pos (suc m)}    {pos zero}       = isRefl≤
≤max {pos (suc m)}    {pos (suc n)} with m ℕ.<ᵇ n UsingEq
... | false , p = isRefl≤
... | true  , p = <-weaken (pos<pos (subst Bool→Type (sym p) tt))
≤max {pos m}          {negsuc n}       = isRefl≤
≤max {negsuc m}       {pos n}          = negsuc≤pos
≤max {negsuc zero}    {negsuc n}       = isRefl≤
≤max {negsuc (suc m)} {negsuc zero}    = negsuc≤negsuc tt
≤max {negsuc (suc m)} {negsuc (suc n)} with m ℕ.<ᵇ n UsingEq
... | false , p = isAsym'< (¬>ℕ→¬negsuc<negsuc (subst Bool→Type p))
... | true  , p = isRefl≤

-- this proof will not normalize quickly when m and n are the same large number
≤→max : m ≤ n → ℤ.max m n ≡ n
≤→max {pos zero}       {pos n}           p                = refl
≤→max {pos (suc m)}    {pos (suc n)}    (pos≤pos p) with m ℕ.<ᵇ n UsingEq
... | false , q = isAntisym≤ (pos≤pos p) (isAsym'< (¬<ℕ→¬pos<pos (subst Bool→Type q)) )
... | true  , q = refl
≤→max {negsuc m}       {pos n}           _                = refl
≤→max {negsuc zero}    {negsuc zero}    (negsuc≤negsuc p) = refl
≤→max {negsuc (suc m)} {negsuc zero}    (negsuc≤negsuc p) = refl
≤→max {negsuc (suc m)} {negsuc (suc n)} (negsuc≤negsuc p) with m ℕ.<ᵇ n UsingEq
... | false , q = refl
... | true  , q = isAntisym≤ (negsuc≤negsuc p)
                             (<-weaken (negsuc<negsuc (subst Bool→Type (sym q) tt)))

min≤ : ℤ.min m n ≤ m
min≤ {pos zero}       {pos n}          = zero-≤pos
min≤ {pos (suc m)}    {pos zero}       = zero-≤pos
min≤ {pos (suc m)}    {pos (suc n)} with m ℕ.<ᵇ n UsingEq
... | false , p = isAsym'< (¬<ℕ→¬pos<pos (subst Bool→Type p))
... | true  , p = isRefl≤
min≤ {pos m}          {negsuc n}       = negsuc≤pos
min≤ {negsuc m}       {pos n}          = isRefl≤
min≤ {negsuc zero}    {negsuc n}       = negsuc≤negsuc tt
min≤ {negsuc (suc m)} {negsuc zero}    = isRefl≤
min≤ {negsuc (suc m)} {negsuc (suc n)} with m ℕ.<ᵇ n UsingEq
... | false , p = isRefl≤
... | true  , p = <-weaken (negsuc<negsuc (subst Bool→Type (sym p) tt))

-- this proof will not normalize quickly when m and n are the same large number
≤→min : m ≤ n → ℤ.min m n ≡ m
≤→min {pos zero}       {pos n}           _                = refl
≤→min {pos (suc m)}    {pos (suc n)}    (pos≤pos p) with m ℕ.<ᵇ n UsingEq
... | false , q = isAntisym≤ (isAsym'< (¬<ℕ→¬pos<pos (subst Bool→Type q))) (pos≤pos p)
... | true  , q = refl
≤→min {negsuc m}       {pos n}           _                = refl
≤→min {negsuc zero}    {negsuc zero}    (negsuc≤negsuc p) = refl
≤→min {negsuc (suc m)} {negsuc zero}    (negsuc≤negsuc p) = refl
≤→min {negsuc (suc m)} {negsuc (suc n)} (negsuc≤negsuc p) with m ℕ.<ᵇ n UsingEq
... | false , q = refl
... | true  , q = isAntisym≤ (<-weaken (negsuc<negsuc (subst Bool→Type (sym q) tt)))
                             (negsuc≤negsuc p)

≤MonotoneMin : m ≤ n → o ≤ s → ℤ.min m o ≤ ℤ.min n s
≤MonotoneMin {m} {n} {o} {s} p q = recompute≤ $
  subst (_≤ ℤ.min n s) (
      sym (minAssoc n s (ℤ.min m o))
    ∙ cong (ℤ.min n) (
        minAssoc s m o ∙ cong (flip ℤ.min o) (ℤ.minComm s m) ∙ sym (minAssoc m s o))
    ∙ minAssoc n m (ℤ.min s o)
    ∙ cong₂ ℤ.min (ℤ.minComm n m ∙ ≤→min p)
      (ℤ.minComm s o ∙ ≤→min q))
    min≤

≤MonotoneMax : m ≤ n → o ≤ s → ℤ.max m o ≤ ℤ.max n s
≤MonotoneMax {m} {n} {o} {s} p q = recompute≤ $
  subst (ℤ.max m o ≤_) (
      sym (maxAssoc m o (ℤ.max n s)) ∙
      cong (ℤ.max m) (
        maxAssoc o n s
      ∙ cong (flip ℤ.max s) (ℤ.maxComm o n)
      ∙ sym (maxAssoc n o s)) ∙ maxAssoc m n (ℤ.max o s)
      ∙ cong₂ ℤ.max (≤→max p) (≤→max q))
    ≤max

0<+ : ∀ m n → 0 < m ℤ.+ n → (0 < m) ⊎ (0 < n)
0<+ (pos zero)    (pos (suc n)) (pos<pos p) = inr zero-<possuc
0<+ (pos (suc m)) (pos zero)    (pos<pos p) = inl zero-<possuc
0<+ (pos (suc m)) (pos (suc n)) (pos<pos p) = inr zero-<possuc -- alternative : inl zero-<possuc
0<+ (pos (suc m)) (negsuc n)     _          = inl zero-<possuc
0<+ (negsuc m)    (pos (suc n))  _          = inr zero-<possuc

Σℕ→≤ : Σ[ k ∈ ℕ ] m ℤ.+ pos k ≡ n → m ≤ n
Σℕ→≤ = recompute≤ ∘ uncurry λ _ → flip (subst (_ ≤_)) ≤SumLeftPos

Σℕ→< : Σ[ k ∈ ℕ ] m ℤ.+ pos (suc k) ≡ n → m < n
Σℕ→< = recompute< ∘ uncurry λ _ → flip (subst (_ <_)) <SumLeftPosSuc

-- the first component will normalize quickly, but not the path itself
≤→Σℕ : m ≤ n → Σ[ k ∈ ℕ ] m ℤ.+ pos k ≡ n
≤→Σℕ {m} {n} p .fst = abs (n - m)
≤→Σℕ {m} {n} p .snd =
  m ℤ.+ pos (abs (n - m)) ≡⟨ cong (m ℤ.+_) (0≤→abs≡id (≤→0≤Δ p)) ⟩
  m ℤ.+ (n - m)           ≡⟨ ℤ.+Comm m (n - m) ⟩
  (n - m) ℤ.+ m           ≡⟨ ℤ.minusPlus m n ⟩
  n                       ∎

-- the first component will normalize quickly, but not the path itself
<→Σℕ : m < n → Σ[ k ∈ ℕ ] m ℤ.+ pos (suc k) ≡ n
<→Σℕ {m} = map-snd (sym (+sucℤ m _) ∙∙ sucℤ+ m _ ∙∙_) ∘ ≤→Σℕ ∘ <→suc≤

data Trichotomy m n : Type where
  lt : m < n → Trichotomy m n
  eq : m ≡ n → Trichotomy m n
  gt : n < m → Trichotomy m n

Trichotomy-suc : Trichotomy m n → Trichotomy (sucℤ m) (sucℤ n)
Trichotomy-suc (lt m<n) = lt (suc-<-suc m<n)
Trichotomy-suc (eq m≡n) = eq (cong sucℤ m≡n)
Trichotomy-suc (gt n<m) = gt (suc-<-suc n<m)

Trichotomy-pred : Trichotomy (sucℤ m) (sucℤ n) → Trichotomy m n
Trichotomy-pred (lt m<n) = lt (pred-<-pred m<n)
Trichotomy-pred (eq m≡n) = eq (sym (predSuc _) ∙ cong predℤ m≡n ∙ predSuc _)
Trichotomy-pred (gt n<m) = gt (pred-<-pred n<m)

-- this proof will decide quickly among the cases `lt`, `gt`, `eq`
-- however, the path for the proof of the `eq` case will normalize slowly
_≟_ : ∀ m n → Trichotomy m n
pos m    ≟ pos n with m ℕ.≟ n
... | ℕ.lt p = lt $ recompute< $ pos<pos {m} {n} (ℕ.<→<ᵗ p)
... | ℕ.eq p = eq (cong pos p)
... | ℕ.gt p = gt $ recompute< $ pos<pos {n} {m} (ℕ.<→<ᵗ p)
pos m    ≟ negsuc n = gt negsuc<pos
negsuc m ≟ pos n    = lt negsuc<pos
negsuc m ≟ negsuc n with m ℕ.≟ n
... | ℕ.lt p = gt $ recompute< $ negsuc<negsuc {n} {m} (ℕ.<→<ᵗ p)
... | ℕ.eq p = eq (cong negsuc p)
... | ℕ.gt p = lt $ recompute< $ negsuc<negsuc {m} {n} (ℕ.<→<ᵗ p)

-- alternative proof
_≟'_ : ∀ m n → Trichotomy m n
pos zero       ≟' pos zero       = eq refl
pos zero       ≟' pos (suc n)    = lt zero-<possuc
pos (suc m)    ≟' pos zero       = gt zero-<possuc
pos (suc m)    ≟' pos (suc n)    = Trichotomy-suc (pos m ≟' pos n)
pos m          ≟' negsuc n       = gt negsuc<pos
negsuc m       ≟' pos n          = lt negsuc<pos
negsuc zero    ≟' negsuc zero    = eq refl
negsuc zero    ≟' negsuc (suc n) = gt (negsuc<negsuc tt)
negsuc (suc m) ≟' negsuc zero    = lt (negsuc<negsuc tt)
negsuc (suc m) ≟' negsuc (suc n) = Trichotomy-pred (negsuc m ≟' negsuc n)

-- raw comparisons, without the proof terms
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

  test₁' : compare' -4294967296 -4294967296 ≡ EQ
  test₁' = refl

  test₂' : compare' -4294967296 -4295967296 ≡ GT
  test₂' = refl

  -}
