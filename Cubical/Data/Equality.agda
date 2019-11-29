{- Cubical Agda with K

This file defines:

ptoc : x ≡p y → x ≡c y
ctop : x ≡c y → x ≡p y

and proves:

ptoc-ctop : (p : x ≡c y) → ptoc (ctop p) ≡c p

These definitions and lemmas are proved without Axiom K.

-}

{-# OPTIONS --cubical --safe #-}

module Cubical.Data.Equality where

open import Cubical.Foundations.Prelude
  renaming ( _≡_ to _≡c_ ; refl to reflc )
  public
open import Agda.Builtin.Equality
  renaming ( _≡_ to _≡p_ ; refl to reflp )
  public

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

