{-

This module converts between the path equality
and the inductively define equality types.

- _≡c_ stands for "c"ubical equality.
- _≡p_ stands for "p"ropositional equality.

TODO: reconsider naming scheme.
-}
{-# OPTIONS --cubical --safe #-}

module Cubical.Data.Equality where

open import Cubical.Foundations.Prelude
  renaming ( _≡_ to _≡c_ ; refl to reflc )
  public
open import Agda.Builtin.Equality
  renaming ( _≡_ to _≡p_ ; refl to reflp )
  public

open import Cubical.Foundations.Isomorphism

private
 variable
  ℓ : Level
  A : Set ℓ
  x y z : A

ptoc : x ≡p y → x ≡c y
ptoc reflp = reflc

ctop : x ≡c y → x ≡p y
ctop p = transport (cong (λ u → _ ≡p u) p) reflp

ptoc-ctop : (p : x ≡c y) → ptoc (ctop p) ≡c p
ptoc-ctop p =
  J (λ _ h → ptoc (ctop h) ≡c h) (cong ptoc (transportRefl reflp)) p

ctop-ptoc : (p : x ≡p y) → ctop (ptoc p) ≡c p
ctop-ptoc {x = x} reflp = transportRefl reflp

p≅c : {x y : A} → Iso (x ≡c y) (x ≡p y)
p≅c = iso ctop ptoc ctop-ptoc ptoc-ctop

p-c : {x y : A} → (x ≡c y) ≡c (x ≡p y)
p-c = isoToPath p≅c

p=c : {x y : A} → (x ≡c y) ≡p (x ≡p y)
p=c = ctop p-c
