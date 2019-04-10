{-# OPTIONS --cubical --safe #-}

module Cubical.HITs.Modulo.Properties where

open import Cubical.Core.Everything

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin
open import Cubical.Data.Sigma

open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.HITs.Modulo.Base

private
  variable
    ℓ : Level
    k : ℕ

Modulo0≡ℕ : Modulo 0 ≡ ℕ
Modulo0≡ℕ = isoToPath lemma
 where
 open Iso
 lemma : Iso (Modulo 0) ℕ
 fun lemma (embed n) = n
 inv lemma = embed
 rightInv lemma n = refl
 leftInv lemma (embed n) = refl

isSetModulo0 : isSet (Modulo 0)
isSetModulo0 = subst isSet (sym Modulo0≡ℕ) isSetℕ

isContrModulo1 : isContr (Modulo 1)
isContrModulo1
  = value , λ
  { (embed n) → universal n
  ; (step n i) → universal-path n i
  }
  where
  value : Modulo 1
  value = embed 0

  universal : ∀ n → value ≡ embed n
  universal zero = refl
  universal (suc n) = universal n ∙ step n

  universal-path
   : ∀ n → PathP (λ i → value ≡ step n i) (universal n) (universal (suc n))
  universal-path n i j
    = compPath-filler (universal n) (step n) i j

steps : ∀ m o → embed {k = k} m ≡ embed (expand o k m)
steps m zero = refl
steps {k} m (suc o) = steps m o ∙ ztep (expand o k m)

steps≡
  : ∀ m n
  → PathP (λ i → embed {k} m ≡ ztep (expand n k m) i)
      (steps m n)
      (steps m (suc n))
steps≡ m n = λ i j → compPath-filler (steps m n) (ztep (expand n _ m)) i j

stepOver : ∀ m n o → expand o k m ≡ n → embed {k = k} m ≡ embed n
stepOver m n o p = steps m o ∙ cong embed p



