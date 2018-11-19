{-

Basic theory about NTypes:

- basic properties of isContr, isProp and isSet (definitions are in Core/Prelude)

- Hedberg's theorem: any type with decidable equality is a set

-}
{-# OPTIONS --cubical #-}
module Cubical.Basics.NTypes where

open import Cubical.Core.Primitives
open import Cubical.Core.Prelude
open import Cubical.Core.Glue

open import Cubical.Basics.Empty

isContr→isProp : ∀ {ℓ} {A : Set ℓ} → isContr A → isProp A
isContr→isProp h a b i =
  hcomp (λ j → λ { (i = i0) → h .snd a j
                 ; (i = i1) → h .snd b j })
        (h .fst)

isProp→isSet : ∀ {ℓ} {A : Set ℓ} → isProp A → isSet A
isProp→isSet h a b p q j i =
  hcomp (λ k → λ { (i = i0) → h a a k
                 ; (i = i1) → h a b k
                 ; (j = i0) → h a (p i) k
                 ; (j = i1) → h a (q i) k }) a 

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


-- Proof of Hedberg's theorem:
-- TODO: upstream
data _⊎_ {ℓ ℓ'} (P : Set ℓ) (Q : Set ℓ') : Set (ℓ-max ℓ ℓ') where
  inl : P → P ⊎ Q
  inr : Q → P ⊎ Q

stable : ∀ {ℓ} → Set ℓ → Set ℓ
stable A = ¬ ¬ A → A

dec : ∀ {ℓ} → Set ℓ → Set ℓ
dec A = A ⊎ (¬ A)

discrete : ∀ {ℓ} → Set ℓ → Set ℓ
discrete A = (x y : A) → dec (x ≡ y)

dec→stable : ∀ {ℓ} (A : Set ℓ) → dec A → stable A
dec→stable A (inl x) = λ _ → x
dec→stable A (inr x) = λ f → ⊥-elim (f x)

dNot : ∀ {l} → (A : Set l) → (a : A) → ¬ ¬ A
dNot A a p = p a

lem : ∀ {ℓ} {A : Set ℓ} {a b : A} (f : (x : A) → a ≡ x → a ≡ x) (p : a ≡ b) → PathP (λ i → a ≡ p i) (f a refl) (f b p)
lem {a = a} f p = J (λ y q → PathP (λ i → a ≡ q i) (f a refl) (f y q)) refl p

stable-path→isSet : ∀ {ℓ} {A : Set ℓ} → (st : ∀ (a b : A) → stable (a ≡ b)) → isSet A
stable-path→isSet {A = A} st a b p q j i =
  let f : (x : A) → a ≡ x → a ≡ x
      f x p = st a x (dNot _ p)
      fIsConst : (x : A) → (p q : a ≡ x) → f x p ≡ f x q
      fIsConst = λ x p q i → st a x (isProp¬ _ (dNot _ p) (dNot _ q) i)
  in hcomp (λ k → λ { (i = i0) → f a refl k
                    ; (i = i1) → fIsConst b p q j k
                    ; (j = i0) → lem f p i k
                    ; (j = i1) → lem f q i k }) a
  
-- Hedberg's theorem
discrete→isSet : ∀ {ℓ} {A : Set ℓ} → discrete A → isSet A
discrete→isSet d = stable-path→isSet (λ x y → dec→stable (x ≡ y) (d x y))
