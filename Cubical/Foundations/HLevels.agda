{-

Basic theory about h-levels/n-types:

- Basic properties of isContr, isProp and isSet (definitions are in Core/Prelude)

- Hedberg's theorem can be found in Cubical/Relation/Nullary/DecidableEq

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.HLevels where

open import Cubical.Core.Everything

open import Cubical.Foundations.FunExtEquiv

open import Cubical.Data.Nat.Base
open import Cubical.Data.Empty
open import Cubical.Data.Sum

open import Cubical.Relation.Nullary

hProp : {ℓ : Level} → Set (ℓ-suc ℓ)
hProp {ℓ} = Σ (Set ℓ) isProp

isOfHLevel : ∀ {ℓ} → ℕ → Set ℓ → Set ℓ
isOfHLevel zero A = isContr A
isOfHLevel (suc n) A = (x y : A) → isOfHLevel n (x ≡ y)

HLevel : ∀ {ℓ} → ℕ → Set _
HLevel {ℓ} n = Σ[ A ∈ Set ℓ ] (isOfHLevel n A)

isContr→isProp : ∀ {ℓ} {A : Set ℓ} → isContr A → isProp A
isContr→isProp (x , p) a b i =
  hcomp (λ j → λ { (i = i0) → p a j
                 ; (i = i1) → p b j }) x

isProp→isSet : ∀ {ℓ} {A : Set ℓ} → isProp A → isSet A
isProp→isSet h a b p q j i =
  hcomp (λ k → λ { (i = i0) → h a a k
                 ; (i = i1) → h a b k
                 ; (j = i0) → h a (p i) k
                 ; (j = i1) → h a (q i) k }) a 

inhProp→isContr : ∀ {ℓ} {A : Set ℓ} → A → isProp A → isContr A
inhProp→isContr x h = x , h x

isProp→IsOfHLevel1 : ∀ {ℓ} {A : Set ℓ} → isProp A → isOfHLevel 1 A
isProp→IsOfHLevel1 h x y = inhProp→isContr (h x y) (isProp→isSet h x y)

isOfHLevel1→isProp : ∀ {ℓ} {A : Set ℓ} → isOfHLevel 1 A → isProp A
isOfHLevel1→isProp h x y = fst (h x y)

isSet→isOfHLevel2 : ∀ {ℓ} {A : Set ℓ} → isSet A → isOfHLevel 2 A
isSet→isOfHLevel2 h x y = isProp→IsOfHLevel1 (h x y)

isOfHLevel2→isSet : ∀ {ℓ} {A : Set ℓ} → isOfHLevel 2 A → isSet A
isOfHLevel2→isSet h x y = isOfHLevel1→isProp (h x y)

isPropIsContr : ∀ {ℓ} {A : Set ℓ} → isProp (isContr A)
isPropIsContr z0 z1 j =
  ( z0 .snd (z1 .fst) j
  , λ x i → hcomp (λ k → λ { (i = i0) → z0 .snd (z1 .fst) j
                           ; (i = i1) → z0 .snd x (j ∨ k)
                           ; (j = i0) → z0 .snd x (i ∧ k)
                           ; (j = i1) → z1 .snd x i })
                  (z0 .snd (z1 .snd x i) j))

isPropIsProp : ∀ {ℓ} {A : Set ℓ} → isProp (isProp A)
isPropIsProp f g i a b = isProp→isSet f a b (f a b) (g a b) i

isPropIsSet : ∀ {ℓ} {A : Set ℓ} → isProp (isSet A)
isPropIsSet f g i a b = isPropIsProp (f a b) (g a b) i

-- A retract of a contractible type is contractible
retractIsContr : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (g : B → A)
                 (h : (x : A) → g (f x) ≡ x) (v : isContr B) → isContr A
retractIsContr f g h (b , p) = (g b , λ x → compPath (cong g (p (f x))) (h x))

isContrSigma : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} →
               isContr A → ((x : A) → isContr (B x)) →
               isContr (Σ[ x ∈ A ] B x)
isContrSigma {A = A} {B = B} (a , p) q =
  let h : (x : A) (y : B x) → (q x) .fst ≡ y
      h x y = (q x) .snd y
  in (( a , q a .fst)
     , ( λ x i → p (x .fst) i
       , h (p (x .fst) i) (transp (λ j → B (p (x .fst) (i ∨ ~ j))) i (x .snd)) i))

isContrPath : ∀ {ℓ} {A : Set ℓ} → isContr A → (x y : A) → isContr (x ≡ y)
isContrPath cA = isProp→IsOfHLevel1 (isContr→isProp cA)

lemProp : ∀ {ℓ} {A : Set ℓ} → (A → isProp A) → isProp A
lemProp h a = h a a

module _ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} where
  -- Π preserves propositionality in the following sense:
  propPi : (h : (x : A) → isProp (B x)) → isProp ((x : A) → B x)
  propPi h f0 f1 i x = h x (f0 x) (f1 x) i

  isProp→PathP : ((x : A) → isProp (B x)) → {a0 a1 : A}
                 (p : a0 ≡ a1) (b0 : B a0) (b1 : B a1) → PathP (λ i → B (p i)) b0 b1
  isProp→PathP P p b0 b1 i = P (p i) (transp (λ j → B (p (i ∧ j))) (~ i) b0)
                                     (transp (λ j → B (p (i ∨ ~ j))) i b1) i

  subtypeEquality : ((x : A) → isProp (B x)) → (u v : Σ[ a ∈ A ] B a)
                    (p : u .fst ≡ v .fst) → u ≡ v
  subtypeEquality pB u v p i = (p i) , isProp→PathP pB p (u .snd) (v .snd) i

  isPropSigma : isProp A → ((x : A) → isProp (B x)) → isProp (Σ[ x ∈ A ] B x)
  isPropSigma pA pB t u = subtypeEquality pB t u (pA (t .fst) (u .fst))

hLevelPi : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} n
         → ((x : A) → isOfHLevel n (B x))
         → isOfHLevel n ((x : A) → B x)
hLevelPi 0 h = (λ x → fst (h x)) , λ f i y → snd (h y) (f y) i
hLevelPi (suc n) h f g = subst (isOfHLevel n) funExtPath sub-lemma
  where
  sub-lemma : isOfHLevel n (∀ x → f x ≡ g x)
  sub-lemma = hLevelPi n λ x → h x (f x) (g x)

isSetPi : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'}
  → ((x : A) → isSet (B x))
  → isSet ((x : A) → B x)
isSetPi Bset = isOfHLevel2→isSet (hLevelPi 2 (λ a → isSet→isOfHLevel2 (Bset a)))


isSet→isSet' : ∀ {ℓ} {A : Set ℓ} → isSet A → isSet' A
isSet→isSet' {A = A} Aset {x} {y} {z} {w} p q r s =
  J (λ (z : A) (r : x ≡ z) → ∀ {w : A} (s : y ≡ w) (p : x ≡ y) (q : z ≡ w) → PathP (λ i → Path A (r i) (s i) ) p q) helper r s p q
  where
    helper : ∀ {w : A} (s : y ≡ w) (p : x ≡ y) (q : x ≡ w) → PathP (λ i → Path A x (s i)) p q
    helper {w} s p q = J (λ (w : A) (s : y ≡ w) → ∀ p q → PathP (λ i → Path A x (s i)) p q) (λ p q → Aset x y p q) s p q 

isSet'→isSet : ∀ {ℓ} {A : Set ℓ} → isSet' A → isSet A
isSet'→isSet {A = A} Aset' x y p q = Aset' p q refl refl
