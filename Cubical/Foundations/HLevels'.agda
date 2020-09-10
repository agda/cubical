{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Foundations.HLevels' where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Loopspace
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Foundations.Structure

private
  variable
    ℓ : Level

isOfHLevel' : HLevel → Type ℓ → Type ℓ
isOfHLevel' 0 A = isOfHLevel 0 A
isOfHLevel' (suc n) A = (x y : A) → isOfHLevel' n (x ≡ y)

isOfHLevel'→ : {n : HLevel} {A : Type ℓ} (l : isOfHLevel' n A) → isOfHLevel n A
isOfHLevel'→ {n = 0} l = l
isOfHLevel'→ {n = 1} l a b = l a b .fst
isOfHLevel'→ {n = suc (suc _)} l a b = isOfHLevel'→ (l a b)

isOfHLevel→' : {n : HLevel} {A : Type ℓ} (l : isOfHLevel n A) → isOfHLevel' n A
isOfHLevel→' {n = 0} l = l
isOfHLevel→' {n = 1} l = isProp→isContrPath l
isOfHLevel→' {n = suc (suc _)} l = λ x y → isOfHLevel→' (l x y)

isPropIsOfHLevel' : (n : HLevel) {A : Type ℓ} → isProp (isOfHLevel' n A)
isPropIsOfHLevel' 0 = isPropIsOfHLevel 0
isPropIsOfHLevel' 1 p q = funExt (λ a → funExt (λ b → isPropIsContr (p a b) (q a b)))
isPropIsOfHLevel' (suc (suc n)) f g i a b = isPropIsOfHLevel' (suc n) (f a b) (g a b) i -- isPropIsOfHLevel (suc (suc n))

isOfHLevel≡' : (n : HLevel) {A : Type ℓ} → isOfHLevel n A ≡ isOfHLevel' n A
isOfHLevel≡' n = isoToPath (iso isOfHLevel→'
                                isOfHLevel'→
                                (λ p' → isPropIsOfHLevel' n _ p')
                                λ p → isPropIsOfHLevel n _ p)

HL→ = isOfHLevel→'
HL← = isOfHLevel'→

module _ {X : Type ℓ} where
  -- Lemma 7.2.8 in the HoTT book
  -- For n >= -1, if X being inhabited implies X is an n-type, then X is an n-type
  inh→ntype→ntype : {n : ℕ} (t : X → isOfHLevel (suc n) X) → isOfHLevel (suc n) X
  inh→ntype→ntype {n = 0} t = λ x y → t x x y
  inh→ntype→ntype {n = suc _} t = λ x y → t x x y

module _ {X : Type ℓ} where
  -- Theorem 7.2.7 in the HoTT book
  -- For n >= -1, X is an (n+1)-type if all its loop spaces are n-types
  truncSelfId→truncId : {n : ℕ} → ((x : X) → isOfHLevel (suc n) (x ≡ x)) → isOfHLevel (suc (suc n)) X
  truncSelfId→truncId {n = 0} t =
    λ x x' → inh→ntype→ntype {n = 0}
                              λ p → J (λ y q → isOfHLevel 1 (x ≡ y))
                                      (t x)
                                      p
  truncSelfId→truncId {n = suc m} t =
    λ x x' → inh→ntype→ntype {n = suc m}
                              λ p → J (λ y q → isOfHLevel (suc (suc m)) (x ≡ y))
                                      (t x)
                                      p

  EquivPresHLevel : {Y : Type ℓ} → {n : ℕ} → (X≃Y : X ≃ Y) → (hX : isOfHLevel n X) → isOfHLevel n Y
  EquivPresHLevel {Y} {n} X≃Y hX = subst (λ x → isOfHLevel n x) (ua X≃Y) hX
