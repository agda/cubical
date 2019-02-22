{-

This file proves the higher groupoid structure of types

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.GroupoidLaws where

open import Cubical.Core.Primitives
open import Cubical.Core.Prelude

private
  variable
    ℓ : Level
    A : Set ℓ

-- some useful notation

_·_ :  {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
x≡y · y≡z = compPath x≡y y≡z 

infixr 30 _·_

_⁻¹ : {x y : A} → (x ≡ y) → (y ≡ x)
x≡y ⁻¹ = sym x≡y

𝟭 : {x : A} → x ≡ x
𝟭 = refl

-- homogeneous groupoid laws

symInvo : {x y : A} (p : x ≡ y) →
     Path (Path A x y) p ((p ⁻¹)⁻¹)
symInvo p = 𝟭

rUnit : {x y : A} (p : x ≡ y) →
  Path (Path A x y) p (p · 𝟭)
rUnit p j i = compPath-filler p 𝟭 j i

lUnit : {x y : A} (p : x ≡ y) →
  Path (Path A x y) p (𝟭 · p)
lUnit {x = x} p k i =
  hcomp (λ j → λ { (i = i0) → x
                  ; (i = i1) → p (~ k ∨ j )
                  ; (k = i0) → p i
               -- ; (k = i1) → compPath-filler 𝟭 p j i
                  }) (p (~ k ∧ i ))

symRefl : {x : A} →
  Path (Path A x x) 𝟭 (𝟭 ⁻¹)
symRefl i = 𝟭 

compPathRefl : {x : A} →
  Path (Path A x x) 𝟭 (𝟭 · 𝟭)
compPathRefl = rUnit 𝟭

rCancel : ∀ {x y : A} (p : x ≡ y) →
   Path (Path A x x) (p · (p ⁻¹)) 𝟭
rCancel {x = x} p j i =
  hcomp (λ k → λ { (i = i0) → x
                  ; (i = i1) → p (~ k ∧ ~ j)
               -- ; (j = i0) → hfill (λ w → λ { (i = i0) → x; (i = i1) → p (~ w) }) (inc (p i)) k
                  ; (j = i1) → x
                  }) (p (i ∧ ~ j))

lCancel : {x y : A} (p : x ≡ y) →
   Path (Path A y y) 𝟭 ((p ⁻¹) · p)
lCancel p i = rCancel (p ⁻¹) (~ i)

3outof4 : (α : I → I → A) → (p : α i1 i0 ≡ α i1 i1) → (β : PathP (λ j → Path A (α j i0) (α j i1)) (λ i → α i0 i) p) →
  Path (Path A (α i1 i0) (α i1 i1)) (λ i → α i1 i) p
3outof4 α p β j i =
  hcomp (λ k → λ { (i = i0) → α k i0
                  ; (i = i1) → α k i1
                  ; (j = i0) → α k i
                  ; (j = i1) → β k i
                  }) (α i0 i)

preassoc : {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) →
  PathP (λ j → Path A x ((q · r) j)) p ((p · q) · r)
preassoc {x = x} p q r k i =
  hcomp (λ j → λ { (i = i0) → x
                  ; (i = i1) → compPath-filler q r j k
                  ; (k = i0) → p i
               -- ; (k = i1) → compPath-filler (p · q) r j i
                  }) (compPath-filler p q k i)

assoc : {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) →
  Path (Path A x w) (p · q · r) ((p · q) · r)
assoc p q r = 3outof4 (compPath-filler p (q · r)) ((p · q) · r) (preassoc p q r)

-- TODO: heterogeneous groupoid operations and laws

