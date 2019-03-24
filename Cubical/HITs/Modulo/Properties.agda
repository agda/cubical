{-# OPTIONS --cubical --safe #-}

module Cubical.HITs.Modulo.Properties where

open import Cubical.Core.Everything

open import Cubical.Data.Nat
open import Cubical.Data.Fin

open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

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
 fun lemma (step n i) = n
 fun lemma (squash z n i j) = n
 inv lemma = embed
 rightInv lemma n = refl
 leftInv lemma (embed n) = refl
 leftInv lemma (step n i) j = squash _ n j i
 leftInv lemma (squash z n i j) k = squash z n (i ∧ k) j

Modulo0-isSet : isSet (Modulo 0)
Modulo0-isSet = subst isSet (sym Modulo0≡ℕ) isSetℕ

isContrModulo1 : isContr (Modulo 1)
isContrModulo1
  = value , λ
  { (embed n) → universal n
  ; (step n i) → universal-path n i
  ; (squash () n i j)
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

steps : ∀ m n → embed {k = k} m ≡ embed (n * k + m)
steps m zero = refl
steps {k} m (suc n)
  = steps m n ∙ step (n * k + m) ∙ cong embed (+-assoc k (n * k) m)

fembed : Fin k → Modulo k
fembed (n , n<k) = embed n

MReduction : (k : ℕ) → Modulo (suc k) → Set
MReduction k (embed n) = Reduction (suc k) n
MReduction k (step n i) = Reduction≡ (suc k) n (suc k + n) refl i

mreduce : (m : Modulo (suc k)) → MReduction k m
mreduce (embed n) = reduce _ n
mreduce {k} (step n i) = reduce≡ k n (suc k + n) refl i
