{-# OPTIONS --cubical --safe #-}

module Cubical.HITs.Modulo.FinEquiv where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude

open import Cubical.Data.Fin
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order

open import Cubical.HITs.Modulo.Base

module Reduction {k₀ : ℕ} where
  private
    k = suc k₀

  fembed : Fin k → Modulo k
  fembed = embed ∘ toℕ

  ModulusPath : ℕ → Set
  ModulusPath n =  Σ[ f ∈ Fin k ] fembed f ≡ embed n

  rbase : ∀ n (n<k : n < k) → ModulusPath n
  rbase n n<k = (n , n<k) , refl

  rstep : ∀ n → ModulusPath n → ModulusPath (k + n)
  rstep n (f , p) = f , p ∙ step n

  rstep≡
    : ∀ n (R : ModulusPath n)
    → PathP (λ i → fembed (fst R) ≡ step n i) (snd R) (snd (rstep n R))
  rstep≡ n (f , p) = λ i j → compPath-filler p (step n) i j

  modulusPath : ∀ n → ModulusPath n
  modulusPath = +induction k₀ ModulusPath rbase rstep

  lemma₁ : ∀ n → rstep n (modulusPath n) ≡ modulusPath (k + n)
  lemma₁ = sym ∘ +inductionStep k₀ ModulusPath rbase rstep

  modulusStep₁
    : ∀ n →  fst (modulusPath n) ≡ fst (modulusPath (k + n))
  modulusStep₁ = cong fst ∘ lemma₁

  modulusStep₂
    : ∀ n → PathP (λ i → fembed (modulusStep₁ n i) ≡ step n i)
              ((snd ∘ modulusPath) n)
              ((snd ∘ modulusPath) (k + n))
  modulusStep₂ n i j
    = hfill (λ ii → λ
            { (i = i0) → snd (modulusPath n) j
            ; (j = i0) → fembed (modulusStep₁ n (i ∧ ii))
            ; (i = i1) → snd (lemma₁ n ii) j
            ; (j = i1) → step n i
            })
        (inS (rstep≡ n (modulusPath n) i j))
        i1

  modulus : Modulo k → Fin k
  modulus (embed n) = fst (modulusPath n)
  modulus (step n i) = modulusStep₁ n i

  sect : section modulus fembed
  sect (r , r<k) = cong fst (+inductionBase k₀ ModulusPath rbase rstep r r<k)

  retr : retract modulus fembed
  retr (embed n) = snd (modulusPath n)
  retr (step n i) = modulusStep₂ n i

  Modulo≡Fin : Modulo k ≡ Fin k
  Modulo≡Fin = isoToPath (iso modulus fembed sect retr)

open Reduction using (fembed; modulus; Modulo≡Fin) public
