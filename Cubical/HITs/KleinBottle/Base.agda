{-

Definition of the Klein bottle as a HIT

-}
{-# OPTIONS --safe #-}
module Cubical.HITs.KleinBottle.Base where

open import Cubical.Core.Everything

data KleinBottle : Type where
  point : KleinBottle
  line1 : point ≡ point
  line2 : point ≡ point
  square : PathP (λ i → line1 (~ i) ≡ line1 i) line2 line2
