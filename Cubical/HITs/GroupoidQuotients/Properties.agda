{-

Groupoid quotients:

-}

{-# OPTIONS --cubical --no-import-sorts #-}
module Cubical.HITs.GroupoidQuotients.Properties where

open import Cubical.HITs.GroupoidQuotients.Base

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Functions.Surjection

open import Cubical.Data.Sigma

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary.Base

open import Cubical.HITs.PropositionalTruncation as PropTrunc using (∥_∥₁; ∣_∣₁; squash₁)
open import Cubical.HITs.SetTruncation as SetTrunc using (∥_∥₂; ∣_∣₂; squash₂)

-- Type quotients

private
  variable
    ℓA ℓR ℓ : Level
    A : Type ℓA
    R : A → A → Type ℓR

elimSet : (Rt : BinaryRelation.isTrans R)
     → {B : A // Rt → Type ℓ}
     → ((x : A // Rt) → isSet (B x))
     → (f : (a : A) → B [ a ])
     → ({a b : A} (r : R a b) → PathP (λ i → B (eq// r i)) (f a) (f b))
     → (x : A // Rt)
     → B x
elimSet Rt Bset f feq [ a ] = f a
elimSet Rt Bset f feq (eq// r i) = feq r i
elimSet Rt Bset f feq (comp// {a} {b} {c} r s i j) =
  isSet→SquareP (λ i j → Bset (comp// r s i j))
    (λ j → feq r j) (λ j → feq (Rt a b c r s) j)
    (λ i → f a) (λ i → feq s i) i j
elimSet Rt Bset f feq (squash// x y p q r s i j k) =
  isOfHLevel→isOfHLevelDep 3 (λ x → isSet→isGroupoid (Bset x))
    _ _ _ _ (λ j k → g (r j k)) (λ j k → g (s j k)) (squash// x y p q r s) i j k
  where
    g = elimSet Rt Bset f feq

elimProp : (Rt : BinaryRelation.isTrans R)
         → {B : A // Rt → Type ℓ}
         → ((x : A // Rt) → isProp (B x))
         → ((a : A) → B [ a ])
         → (x : A // Rt)
         → B x
elimProp Rt Brop f x =
  elimSet Rt (λ x → isProp→isSet (Brop x)) f (λ r → isProp→PathP (λ i → Brop (eq// r i)) (f _) (f _)) x

elimProp2 : (Rt : BinaryRelation.isTrans R)
          → {C : A // Rt → A // Rt → Type ℓ}
         → ((x y : A // Rt) → isProp (C x y))
         → ((a b : A) → C [ a ] [ b ])
         → (x y : A // Rt)
         → C x y
elimProp2 Rt Cprop f = elimProp Rt (λ x → isPropΠ (λ y → Cprop x y))
                                   (λ x → elimProp Rt (λ y → Cprop [ x ] y) (f x))

isSurjective[] : (Rt : BinaryRelation.isTrans R)
               → isSurjection (λ a → [ a ])
isSurjective[] Rt = elimProp Rt (λ x → squash₁) (λ a → ∣ a , refl ∣₁)

elim : (Rt : BinaryRelation.isTrans R)
     → {B : A // Rt → Type ℓ}
     → ((x : A // Rt) → isGroupoid (B x))
     → (f : (a : A) → B [ a ])
     → (feq : {a b : A} (r : R a b) → PathP (λ i → B (eq// r i)) (f a) (f b))
     → ({a b c : A} (r : R a b) (s : R b c)
           → SquareP (λ i j → B (comp// r s i j))
           (feq r) (feq (Rt a b c r s)) (λ j → f a) (feq s))
     → (x : A // Rt)
     → B x
elim Rt Bgpd f feq fcomp [ a ] = f a
elim Rt Bgpd f feq fcomp (eq// r i) = feq r i
elim Rt Bgpd f feq fcomp (comp// r s i j) = fcomp r s i j
elim Rt Bgpd f feq fcomp (squash// x y p q r s i j k) =
  isOfHLevel→isOfHLevelDep 3 Bgpd
    _ _ _ _ (λ j k → g (r j k)) (λ j k → g (s j k)) (squash// x y p q r s) i j k
  where
    g = elim Rt Bgpd f feq fcomp

rec : (Rt : BinaryRelation.isTrans R)
    → {B : Type ℓ}
    → isGroupoid B
    → (f : A → B)
    → (feq : {a b : A} (r : R a b) → f a ≡ f b)
    → ({a b c : A} (r : R a b) (s : R b c)
          → Square (feq r) (feq (Rt a b c r s)) refl (feq s))
    → (x : A // Rt)
    → B
rec Rt Bgpd = elim Rt (λ _ → Bgpd)
