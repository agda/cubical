{-# OPTIONS --safe #-}
module Cubical.Algebra.CommRing.QuotientRing where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.SetQuotients hiding (_/_)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Ideal
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.QuotientRing renaming (_/_ to _/Ring_) hiding (asRing)

private
  variable
    ℓ : Level

_/_ : (R : CommRing ℓ) → (I : IdealsIn R) → CommRing ℓ
R / I =
  fst asRing , commringstr _ _ _ _ _
                 (iscommring (RingStr.isRing (snd asRing))
                             (elimProp2 (λ _ _ → squash/ _ _)
                                        commEq))
   where
       asRing = (CommRing→Ring R) /Ring (CommIdeal→Ideal I)
       _·/_ : fst asRing → fst asRing → fst asRing
       _·/_ = RingStr._·_ (snd asRing)
       commEq : (x y : fst R) → ([ x ] ·/ [ y ]) ≡ ([ y ] ·/ [ x ])
       commEq x y i = [ CommRingStr.·Comm (snd R) x y i ]

[_]/ : {R : CommRing ℓ} {I : IdealsIn R} → (a : fst R) → fst (R / I)
[ a ]/ = [ a ]
