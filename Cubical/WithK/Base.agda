{- Cubical Agda with K

This file proves:

ctop-ptoc : (p : x ≡p y) → ctop (ptoc p) ≡c p
p-c : (x ≡c y) ≡c (x ≡p y)
p=c : (x ≡c y) ≡p (x ≡p y)

The above proofs are based on two incompatible flags of Agda.

-}

{-# OPTIONS --cubical --with-K #-}

module Cubical.WithK.Base where

open import Cubical.Data.Equality
open import Cubical.Foundations.Isomorphism


private
 variable
  ℓ : Level
  A : Set ℓ
  x y : A

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
