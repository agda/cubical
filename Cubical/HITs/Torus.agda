{- 

Definition of the torus as a HIT together with a proof that it is
equivalent to two circles

-}
{-# OPTIONS --cubical #-}
module Cubical.HITs.Torus where

open import Cubical.Core.Primitives
open import Cubical.Core.Prelude

open import Cubical.HITs.Circle

data Torus : Set where
  point : Torus
  line1 : point ≡ point
  line2 : point ≡ point
  square : PathP (λ i → line1 i ≡ line1 i) line2 line2

t2c : Torus → S¹ × S¹
t2c point = ( base , base )
t2c (line1 x) = ( loop x , base )
t2c (line2 x) = ( base , loop x)
t2c (square x y) = ( loop x , loop y)

c2t : S¹ × S¹ → Torus
c2t (base , base) = point
c2t (loop i , base) = line1 i
c2t (base , loop j) = line2 j
c2t (loop i , loop j) = square i j

t2c-c2t : ∀ (t : Torus) → c2t (t2c t) ≡ t
t2c-c2t point = refl
t2c-c2t (line1 x) = refl
t2c-c2t (line2 x) = refl
t2c-c2t (square i x) = refl

c2t-t2c : ∀ (p : S¹ × S¹) → t2c (c2t p) ≡ p
c2t-t2c (base   , base)   = refl
c2t-t2c (base   , loop j) = refl
c2t-t2c (loop i , base)   = refl
c2t-t2c (loop i , loop j) = refl


 




























{-
refl : ∀ {A : Type} (x : A) → x ≡ x
refl x = λ _ → x

ap : ∀ {A B : Type} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
ap f p = λ i → f (p i)

funext : ∀ {A B : Type} (f g : A → B) (h : ∀ (x : A) → f x ≡ g x) → f ≡ g
funext f g h = λ i x → h x i

sym : ∀ {A : Type} {x y : A} → x ≡ y → y ≡ x
sym p = λ i → p (~ i)

data S¹ : Type where
  base : S¹
  loop : base ≡ base

-- Square : ∀ {l} {A : Type} {a0 a1 b0 b1 : A} → (u : a0 ≡ a1) (v : b0 ≡ b1)
--                                (r0 : a0 ≡ b0) (r1 : a1 ≡ b1) → Type
-- Square u v r0 r1 = PathP (\ (i : I) → r0 i ≡ r1 i) u v

data Torus : Type where
  point : Torus
  line1 : point ≡ point
  line2 : point ≡ point
  square : PathP (λ (i : I) → line1 i ≡ line1 i) line2 line2

t2c : Torus → S¹ × S¹
t2c point = base , base
t2c (line1 i) = loop i , base
t2c (line2 i) = base , loop i
t2c (square i j) = loop i , loop j

c2t : S¹ × S¹ → Torus
c2t (base   , base)   = point
c2t (base   , loop j) = line2 j
c2t (loop i , base)   = line1 i
c2t (loop i , loop j) = square i j

t2c-c2t : ∀ (t : Torus) → c2t (t2c t) ≡ t
t2c-c2t point        = refl point
t2c-c2t (line1 i)    = refl (line1 i)
t2c-c2t (line2 j)    = refl _
t2c-c2t (square i j) = refl _

c2t-t2c : ∀ (p : S¹ × S¹) → t2c (c2t p) ≡ p
c2t-t2c (base   , base)   = refl _
c2t-t2c (base   , loop j) = refl _
c2t-t2c (loop i , base)   = refl _
c2t-t2c (loop i , loop j) = refl _
-}
