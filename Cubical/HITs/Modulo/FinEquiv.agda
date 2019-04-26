{-# OPTIONS --cubical --safe #-}

module Cubical.HITs.Modulo.FinEquiv where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude

open import Cubical.Data.Fin
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order

open import Cubical.HITs.Modulo.Base

-- For positive `k`, every `Modulo k` can be reduced to its
-- residue modulo `k`, given by a value of type `Fin k`. This
-- forms an equivalence between `Fin k` and `Modulo k`.
module Reduction {k₀ : ℕ} where
  private
    k = suc k₀

  fembed : Fin k → Modulo k
  fembed = embed ∘ toℕ

  ResiduePath : ℕ → Type₀
  ResiduePath n =  Σ[ f ∈ Fin k ] fembed f ≡ embed n

  rbase : ∀ n (n<k : n < k) → ResiduePath n
  rbase n n<k = (n , n<k) , refl

  rstep : ∀ n → ResiduePath n → ResiduePath (k + n)
  rstep n (f , p) = f , p ∙ step n

  rstep≡
    : ∀ n (R : ResiduePath n)
    → PathP (λ i → fembed (fst R) ≡ step n i) (snd R) (snd (rstep n R))
  rstep≡ n (f , p) = λ i j → compPath-filler p (step n) i j

  residuePath : ∀ n → ResiduePath n
  residuePath = +induction k₀ ResiduePath rbase rstep

  lemma₁ : ∀ n → rstep n (residuePath n) ≡ residuePath (k + n)
  lemma₁ = sym ∘ +inductionStep k₀ ResiduePath rbase rstep

  residueStep₁
    : ∀ n →  fst (residuePath n) ≡ fst (residuePath (k + n))
  residueStep₁ = cong fst ∘ lemma₁

  residueStep₂
    : ∀ n → PathP (λ i → fembed (residueStep₁ n i) ≡ step n i)
              ((snd ∘ residuePath) n)
              ((snd ∘ residuePath) (k + n))
  residueStep₂ n i j
    = hfill (λ ii → λ
            { (i = i0) → snd (residuePath n) j
            ; (j = i0) → fembed (residueStep₁ n (i ∧ ii))
            ; (i = i1) → snd (lemma₁ n ii) j
            ; (j = i1) → step n i
            })
        (inS (rstep≡ n (residuePath n) i j))
        i1

  residue : Modulo k → Fin k
  residue (embed n) = fst (residuePath n)
  residue (step n i) = residueStep₁ n i

  sect : section residue fembed
  sect (r , r<k) = cong fst (+inductionBase k₀ ResiduePath rbase rstep r r<k)

  retr : retract residue fembed
  retr (embed n) = snd (residuePath n)
  retr (step n i) = residueStep₂ n i

  Modulo≡Fin : Modulo k ≡ Fin k
  Modulo≡Fin = isoToPath (iso residue fembed sect retr)

open Reduction using (fembed; residue; Modulo≡Fin) public
