{-

Proof of some groupoid laws for equality

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.Groupoid where

open import Cubical.Core.Primitives
open import Cubical.Core.Prelude

-- shortcut for the composition

_⋆_ : {ℓ : Level} → {A : Set ℓ} → {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
x≡y ⋆ y≡z = compPath x≡y y≡z

infixl 30 _⋆_

-- simultaneaous composition on both sides of a path

doubleCompPath-filler : {ℓ : Level} {A : Set ℓ} {w x y z : A} → w ≡ x → x ≡ y → y ≡ z →
                        I → I → A
doubleCompPath-filler p q r i =
  hfill (λ t → λ { (i = i0) → p (~ t)
                 ; (i = i1) → r t })
        (inc (q i))

doubleCompPath : {ℓ : Level} {A : Set ℓ} {w x y z : A} → w ≡ x → x ≡ y → y ≡ z → w ≡ z
doubleCompPath p q r i = doubleCompPath-filler p q r i i1

_⋆⋆_⋆⋆_ : {ℓ : Level} {A : Set ℓ} {w x y z : A} → w ≡ x → x ≡ y → y ≡ z → w ≡ z
p ⋆⋆ q ⋆⋆ r = doubleCompPath p q r

-- some exchange law for doubleCompPath and refl

rhombus-filler : {ℓ : Level} {A : Set ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → I → I → A
rhombus-filler p q i j =
  hcomp (λ t → λ { (i = i0) → p (~ t ∨ j)
                 ; (i = i1) → q (t ∧ j)
                 ; (j = i0) → p (~ t ∨ i)
                 ; (j = i1) → q (t ∧ i) })
        (p i1)

leftright : {ℓ : Level} {A : Set ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) →
            (refl ⋆⋆ p ⋆⋆ q) ≡ (p ⋆⋆ q ⋆⋆ refl)
leftright p q i j =
  hcomp (λ t → λ { (j = i0) → p (i ∧ (~ t))
                 ; (j = i1) → q (t ∨ i) })
        (rhombus-filler p q i j)

-- equating doubleCompPath and a succession of two compPath

split-leftright : {ℓ : Level} {A : Set ℓ} {w x y z : A} (p : w ≡ x) (q : x ≡ y) (r : y ≡ z) →
                  (p ⋆⋆ q ⋆⋆ r) ≡ (refl ⋆⋆ (p ⋆⋆ q ⋆⋆ refl) ⋆⋆ r)
split-leftright p q r i j =
  hcomp (λ t → λ { (j = i0) → p (~ i ∧ ~ t)
                 ; (j = i1) → r t })
        (doubleCompPath-filler p q refl j i)

split-leftright' : {ℓ : Level} {A : Set ℓ} {w x y z : A} (p : w ≡ x) (q : x ≡ y) (r : y ≡ z) →
                  (p ⋆⋆ q ⋆⋆ r) ≡ (p ⋆⋆ (refl ⋆⋆ q ⋆⋆ r) ⋆⋆ refl)
split-leftright' p q r i j =
  hcomp (λ t → λ { (j = i0) → p (~ t)
                 ; (j = i1) → r (i ∨ t) })
        (doubleCompPath-filler refl q r j i)

doubleCompPath-elim : {ℓ : Level} {A : Set ℓ} {w x y z : A} (p : w ≡ x) (q : x ≡ y)
                      (r : y ≡ z) → (p ⋆⋆ q ⋆⋆ r) ≡ (p ⋆ q) ⋆ r
doubleCompPath-elim p q r = (split-leftright p q r) ⋆ (λ i → (leftright p q (~ i)) ⋆ r)

doubleCompPath-elim' : {ℓ : Level} {A : Set ℓ} {w x y z : A} (p : w ≡ x) (q : x ≡ y)
                       (r : y ≡ z) → (p ⋆⋆ q ⋆⋆ r) ≡ p ⋆ (q ⋆ r)
doubleCompPath-elim' p q r = (split-leftright' p q r) ⋆ (sym (leftright p (q ⋆ r)))

-- deducing associativity for compPath

compPath-assoc : {ℓ : Level} {A : Set ℓ} {w x y z : A} (p : w ≡ x) (q : x ≡ y) (r : y ≡ z) →
                 (p ⋆ q) ⋆ r ≡ p ⋆ (q ⋆ r)
compPath-assoc p q r = (sym (doubleCompPath-elim p q r)) ⋆ (doubleCompPath-elim' p q r)

-- refl is the identity element

compPath-refl-r : {ℓ : Level} {A : Set ℓ} {x y : A} (p : x ≡ y) → p ⋆ refl ≡ p
compPath-refl-r p i j =
  hfill (λ t → λ { (j = i0) → p i0 ; (j = i1) → p i1 }) (inc (p j)) (~ i)

compPath-refl-l : {ℓ : Level} {A : Set ℓ} {x y : A} (p : x ≡ y) → refl ⋆ p ≡ p
compPath-refl-l p = (leftright refl p) ⋆ (compPath-refl-r p)

-- sym is an inverse

compPath-inv-r : {ℓ : Level} {A : Set ℓ} {x y : A} (p : x ≡ y) → p ⋆ (sym p) ≡ refl
compPath-inv-r p i j =
  hcomp (λ t → λ { (i = i1) → p i0
                 ; (j = i0) → p i0
                 ; (j = i1) → p (~ i ∧ ~ t) })
        (p (~ i ∧ j))

compPath-inv-l : {ℓ : Level} {A : Set ℓ} {x y : A} (p : x ≡ y) → (sym p) ⋆ p ≡ refl
compPath-inv-l p = compPath-inv-r (sym p)
