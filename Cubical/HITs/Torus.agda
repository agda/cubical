{- 

Definition of the torus as a HIT together with a proof that it is
equivalent to two circles

-}
{-# OPTIONS --cubical #-}
module Cubical.HITs.Torus where

open import Cubical.Core.Primitives
open import Cubical.Core.Prelude

open import Cubical.Basics.IsoToEquiv
open import Cubical.Basics.Int

open import Cubical.HITs.Circle

data Torus : Set where
  point : Torus
  line1 : point ≡ point
  line2 : point ≡ point
  square : PathP (λ i → line1 i ≡ line1 i) line2 line2

t2c : Torus → S¹ × S¹
t2c point        = ( base , base )
t2c (line1 i)    = ( loop i , base )
t2c (line2 j)    = ( base , loop j)
t2c (square i j) = ( loop i , loop j)

c2t : S¹ × S¹ → Torus
c2t (base   , base)   = point
c2t (loop i , base)   = line1 i
c2t (base   , loop j) = line2 j
c2t (loop i , loop j) = square i j

c2t-t2c : ∀ (t : Torus) → c2t (t2c t) ≡ t
c2t-t2c point        = refl
c2t-t2c (line1 _)    = refl
c2t-t2c (line2 _)    = refl
c2t-t2c (square _ _) = refl

t2c-c2t : ∀ (p : S¹ × S¹) → t2c (c2t p) ≡ p
t2c-c2t (base   , base)   = refl
t2c-c2t (base   , loop _) = refl
t2c-c2t (loop _ , base)   = refl
t2c-c2t (loop _ , loop _) = refl

Torus≡S¹×S¹ : Torus ≡ S¹ × S¹
Torus≡S¹×S¹ = isoToPath t2c c2t t2c-c2t c2t-t2c

ΩTorus : Set
ΩTorus = point ≡ point

ΩTorus≡Int×Int : ΩTorus ≡ Int × Int
ΩTorus≡Int×Int = {!!}
