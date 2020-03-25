{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Truncation.Connected.Base where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.NatMinusTwo.Base
open import Cubical.Data.Unit
open import Cubical.HITs.Truncation.Base

{- n-connected functions -}
is-_-Connected : ∀{ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (n : ℕ₋₂) (f : A → B) → Type (ℓ-max ℓ ℓ')
is-_-Connected {A = A} {B = B} n f = ((b : B) → isContr (∥ fiber f b ∥ n ))

{- n-connected types -}
is-_-ConnectedType : ∀ {ℓ} (n : ℕ₋₂) (A : Type ℓ) → Type ℓ
is- n -ConnectedType A = isContr (∥ A ∥ n)

is-_-ConnectedType2 : ∀ {ℓ} (n : ℕ₋₂) (A : Type ℓ) → Type ℓ
is- n -ConnectedType2 A = is- n -Connected (λ (x : A) → tt)

{- The first def implies the second -}
conTyp→conTyp2 : ∀ {ℓ} (n : ℕ₋₂) (A : Type ℓ) → is- n -ConnectedType A → is- n -ConnectedType2 A
conTyp→conTyp2 n A iscon tt = transport (λ i → isContr (∥ helper i ∥ n)) iscon
  where
  helper : A ≡ fiber (λ (x : A) → tt) tt
  helper = isoToPath (iso (λ x → x , refl) (λ x → fst x) (λ b i → (refl {x = fst b} i) , ((isOfHLevelSuc 1 (isPropUnit) tt tt (snd b) refl) i)) λ a → refl)

{- n-truncated types -}
is-_-Truncated : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
                 (n : ℕ₋₂) → (f : A → B) → Type (ℓ-max ℓ ℓ')
is-_-Truncated {A = A} {B = B} n f = (b : B) → isOfHLevel (2+ n) (fiber f b)

{- Induced function for induction principle of n-connected functions -}
indConFun : ∀{ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'}
             {k : ℕ₋₂}
             (f : A → B) →
             (P : (B → HLevel ℓ'' (2+ k))) →
             (((b : B) → fst (P b)) → (a : A) → fst (P (f a)))
indConFun  f P  = λ g a → g (f a)
