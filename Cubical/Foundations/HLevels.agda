{-

Basic theory about h-levels/n-types:

- Basic properties of isContr, isProp and isSet (definitions are in Core/Prelude)

- Hedberg's theorem can be found in Cubical/Relation/Nullary/DecidableEq

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.HLevels where

open import Cubical.Core.Everything

open import Cubical.Foundations.FunExtEquiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat.Base
open import Cubical.Data.Empty
open import Cubical.Data.Sum
open import Cubical.Data.Unit

open import Cubical.Relation.Nullary

private
  variable
    ℓ ℓ' : Level
    A : Set ℓ
    B : A → Set ℓ'

hProp : Set (ℓ-suc ℓ)
hProp {ℓ} = Σ (Set ℓ) isProp

isOfHLevel : ℕ → Set ℓ → Set ℓ
isOfHLevel 0 A = isContr A
isOfHLevel 1 A = isProp A
isOfHLevel (suc n) A = (x y : A) → isOfHLevel n (x ≡ y)

HLevel : ℕ → Set (ℓ-suc ℓ)
HLevel {ℓ} n = Σ[ A ∈ Set ℓ ] (isOfHLevel n A)

isContr→isProp : isContr A → isProp A
isContr→isProp (x , p) a b i =
  hcomp (λ j → λ { (i = i0) → p a j
                 ; (i = i1) → p b j }) x

isProp→isSet : isProp A → isSet A
isProp→isSet h a b p q j i =
  hcomp (λ k → λ { (i = i0) → h a a k
                 ; (i = i1) → h a b k
                 ; (j = i0) → h a (p i) k
                 ; (j = i1) → h a (q i) k }) a 

inhProp→isContr : A → isProp A → isContr A
inhProp→isContr x h = x , h x

isPropIsContr : isProp (isContr A)
isPropIsContr z0 z1 j =
  ( z0 .snd (z1 .fst) j
  , λ x i → hcomp (λ k → λ { (i = i0) → z0 .snd (z1 .fst) j
                           ; (i = i1) → z0 .snd x (j ∨ k)
                           ; (j = i0) → z0 .snd x (i ∧ k)
                           ; (j = i1) → z1 .snd x i })
                  (z0 .snd (z1 .snd x i) j))

isPropIsProp : isProp (isProp A)
isPropIsProp f g i a b = isProp→isSet f a b (f a b) (g a b) i

isPropIsPiContrPath : isProp (∀ (x y : A) → isContr (x ≡ y))
isPropIsPiContrPath p q =
  funExt λ x → funExt λ y → isPropIsContr (p x y) (q x y)

-- A retract of a contractible type is contractible
retractIsContr
  : ∀{B : Set ℓ}
  → (f : A → B) (g : B → A)
  → (h : (x : A) → g (f x) ≡ x)
  → (v : isContr B) → isContr A
retractIsContr f g h (b , p) = (g b , λ x → (cong g (p (f x))) ∙ (h x))

isContrSigma
  : isContr A
  → ((x : A) → isContr (B x))
  → isContr (Σ[ x ∈ A ] B x)
isContrSigma {A = A} {B = B} (a , p) q =
  let h : (x : A) (y : B x) → (q x) .fst ≡ y
      h x y = (q x) .snd y
  in (( a , q a .fst)
     , ( λ x i → p (x .fst) i
       , h (p (x .fst) i) (transp (λ j → B (p (x .fst) (i ∨ ~ j))) i (x .snd)) i))

isContrPath : ∀ {ℓ} {A : Set ℓ} → isContr A → (x y : A) → isContr (x ≡ y)
isContrPath cA x y = inhProp→isContr (pA x y) (sA x y)
  where
  pA = isContr→isProp cA
  sA = isProp→isSet pA

lemProp : (A → isProp A) → isProp A
lemProp h a = h a a

-- The type isProp is equivalent to that its path space is contractible.
isProp≡PathIsContr : isProp A ≡ (∀ (x y : A) → isContr (x ≡ y))
isProp≡PathIsContr = isoToPath (iso isProp→PathIsContr PathIsContr→isProp
  (λ _ → isPropIsPiContrPath _ _) (λ _ → isPropIsProp _ _))
  where
    isProp→PathIsContr : isProp A → (∀ (x y : A) → isContr (x ≡ y))
    isProp→PathIsContr Aprop x y = isContrPath (inhProp→isContr x Aprop) x y

    PathIsContr→isProp : (∀ (x y : A) → isContr (x ≡ y)) → isProp A
    PathIsContr→isProp cA x y = cA x y .fst
    
-- Π preserves propositionality in the following sense:
propPi : (h : (x : A) → isProp (B x)) → isProp ((x : A) → B x)
propPi h f0 f1 i x = h x (f0 x) (f1 x) i

isProp→PathP
  : ((x : A) → isProp (B x)) → {a0 a1 : A}
  → (p : a0 ≡ a1) (b0 : B a0) (b1 : B a1)
  → PathP (λ i → B (p i)) b0 b1
isProp→PathP {B = B} P p b0 b1 =
  toPathP {A = λ i → B (p i)} {b0} {b1} (P _ _ _)

subtypeEquality
  : ((x : A) → isProp (B x)) → {u v : Σ[ a ∈ A ] B a}
  → (p : u .fst ≡ v .fst) → u ≡ v
subtypeEquality {B = B} pB {u} {v} p i =
  p i , isProp→PathP pB p (u .snd) (v .snd) i

isPropSigma : isProp A → ((x : A) → isProp (B x)) → isProp (Σ[ x ∈ A ] B x)
isPropSigma pA pB t u = subtypeEquality pB (pA (t .fst) (u .fst))

hLevelPi
  : ∀ n
  → ((x : A) → isOfHLevel n (B x))
  → isOfHLevel n ((x : A) → B x)
hLevelPi 0 h = (λ x → fst (h x)) , λ f i y → snd (h y) (f y) i
hLevelPi {B = B} 1 h f g i x = (h x) (f x) (g x) i
hLevelPi (suc (suc n)) h f g =
  subst (isOfHLevel (suc n)) funExtPath (hLevelPi (suc n) λ x → h x (f x) (g x))

isSetPi : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'}
  → ((x : A) → isSet (B x))
  → isSet ((x : A) → B x)
isSetPi Bset = hLevelPi 2 (λ a → Bset a)

isSet→isSet' : ∀ {ℓ} {A : Set ℓ} → isSet A → isSet' A
isSet→isSet' {A = A} Aset {x} {y} {z} {w} p q r s =
  J (λ (z : A) (r : x ≡ z) → ∀ {w : A} (s : y ≡ w) (p : x ≡ y) (q : z ≡ w) → PathP (λ i → Path A (r i) (s i) ) p q) helper r s p q
  where
    helper : ∀ {w : A} (s : y ≡ w) (p : x ≡ y) (q : x ≡ w) → PathP (λ i → Path A x (s i)) p q
    helper {w} s p q = J (λ (w : A) (s : y ≡ w) → ∀ p q → PathP (λ i → Path A x (s i)) p q) (λ p q → Aset x y p q) s p q 

isSet'→isSet : ∀ {ℓ} {A : Set ℓ} → isSet' A → isSet A
isSet'→isSet {A = A} Aset' x y p q = Aset' p q refl refl

hLevelSuc : (n : ℕ) (A : Set ℓ) → isOfHLevel n A → isOfHLevel (suc n) A
hLevelSuc 0 A = isContr→isProp
hLevelSuc 1 A = isProp→isSet
hLevelSuc (suc (suc n)) A h a b = hLevelSuc (suc n) (a ≡ b) (h a b)

hLevelLift : ∀ {ℓ} {A : Set ℓ} {n : ℕ} (m : ℕ) (hA : isOfHLevel n A) → isOfHLevel (m + n) A
hLevelLift zero hA = hA
hLevelLift {A = A} (suc m) hA = hLevelSuc _ A (hLevelLift m hA)

isPropIsOfHLevel : (n : ℕ) (A : Set ℓ) → isProp (isOfHLevel n A)
isPropIsOfHLevel 0 A = isPropIsContr
isPropIsOfHLevel 1 A = isPropIsProp
isPropIsOfHLevel (suc (suc n)) A f g i a b =
  isPropIsOfHLevel (suc n) (a ≡ b) (f a b) (g a b) i

isPropIsSet : isProp (isSet A)
isPropIsSet {A = A} = isPropIsOfHLevel 2 A
