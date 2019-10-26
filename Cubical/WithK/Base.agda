{- Cubical Agda with K

This file defines:

ptoc : x ≡p y → x ≡c y
ctop : x ≡c y → x ≡p y

and proves:

p-c : (x ≡c y) ≡c (x ≡p y)
p=c : (x ≡c y) ≡p (x ≡p y)

The above proofs are based on two incompatible flags of Agda.

-}

{-# OPTIONS --cubical --with-K #-}

module Cubical.WithK.Base where

open import Cubical.Foundations.Prelude
  renaming ( _≡_ to _≡c_ ; refl to reflc )
  public
open import Agda.Builtin.Equality
  renaming ( _≡_ to _≡p_ ; refl to reflp )
  public

open import Cubical.Foundations.Isomorphism

variable
  ℓ : Level
  A : Set ℓ
  x y z : A

ptoc : x ≡p y → x ≡c y
ptoc reflp = reflc

ctop : x ≡c y → x ≡p y
ctop p = transport (cong (λ u → _ ≡p u) p) reflp

tr : (u : A) → transport reflc u ≡c u
tr {A = A} u i = transp (λ _ → A) i u

ptoc-ctop : (p : x ≡c y) → ptoc (ctop p) ≡c p
ptoc-ctop p =
  J (λ _ h → ptoc (ctop h) ≡c h) (cong ptoc (transportRefl reflp)) p

uip : (prf : x ≡p x) → prf ≡c reflp
uip reflp i = reflp

ctop-ptoc : (p : x ≡p y) → ctop (ptoc p) ≡c p
ctop-ptoc {x = x} reflp = uip (transport (λ i → x ≡p x) reflp)

p-c : {x y : A} → (x ≡c y) ≡c (x ≡p y)
p-c = isoToPath (iso ctop ptoc ctop-ptoc ptoc-ctop)

p=c : {x y : A} → (x ≡c y) ≡p (x ≡p y)
p=c = ctop p-c

transport-uip : (prf : A ≡p A) → transport (ptoc prf) x ≡c x
transport-uip {x = x} prf =
  cong (λ m → transport (ptoc m) x) (uip prf) ∙ transportRefl x
