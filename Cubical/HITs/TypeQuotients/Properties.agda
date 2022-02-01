{-

Type quotients:

-}

{-# OPTIONS --safe #-}
module Cubical.HITs.TypeQuotients.Properties where

open import Cubical.HITs.TypeQuotients.Base

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.HITs.PropositionalTruncation as PropTrunc using (∥_∥ ; ∣_∣ ; squash)
open import Cubical.HITs.SetTruncation as SetTrunc using (∥_∥₂ ; ∣_∣₂ ; squash₂
                                                              ; isSetSetTrunc)

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    R : A → A → Type ℓ'
    B : A /ₜ R → Type ℓ''
    C : A /ₜ R → A /ₜ R → Type ℓ''


elim : (f : (a : A) → (B [ a ]))
     → ((a b : A) (r : R a b) → PathP (λ i → B (eq/ a b r i)) (f a) (f b))
    ------------------------------------------------------------------------
     → (x : A /ₜ R) → B x
elim f feq [ a ] = f a
elim f feq (eq/ a b r i) = feq a b r i

rec : {X : Type ℓ''}
    → (f : A → X)
    → (∀ (a b : A) → R a b → f a ≡ f b)
   -------------------------------------
    → A /ₜ R → X
rec f feq [ a ] = f a
rec f feq (eq/ a b r i) = feq a b r i

elimProp : ((x : A /ₜ R ) → isProp (B x))
         → ((a : A) → B ( [ a ]))
        ---------------------------------
         → (x : A /ₜ R) → B x
elimProp Bprop f [ a ] = f a
elimProp Bprop f (eq/ a b r i) = isOfHLevel→isOfHLevelDep 1 Bprop (f a) (f b) (eq/ a b r) i

elimProp2 : ((x y : A /ₜ R ) → isProp (C x y))
          → ((a b : A) → C [ a ] [ b ])
         --------------------------------------
          → (x y : A /ₜ R) → C x y
elimProp2 Cprop f = elimProp (λ x → isPropΠ (λ y → Cprop x y))
                             (λ x → elimProp (λ y → Cprop [ x ] y) (f x))
