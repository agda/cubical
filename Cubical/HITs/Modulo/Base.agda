{-# OPTIONS --cubical #-}

module Cubical.HITs.Modulo.Base where

open import Cubical.Core.Everything

open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Empty
open import Cubical.Data.Fin as Fin
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Prod
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)

open import Cubical.Induction.WellFounded

open import Cubical.Relation.Nullary

NonZero : ℕ → Set
NonZero 0 = ⊥
NonZero _ = ⊤

Zero : ℕ → Set
Zero 0 = ⊤
Zero _ = ⊥

private
  variable
    ℓ : Level
    k : ℕ

assertZero : Zero k → 0 ≡ k
assertZero {zero} _ = refl
assertZero {suc _} ()

data Modulo (k : ℕ) : Set where
  embed : (n : ℕ) → Modulo k
  step : (n : ℕ) → embed n ≡ embed (k + n)
  squash
    : ∀(z : Zero k) n
    → PathP (λ i → embed n ≡ embed (assertZero z i + n)) refl (step n)

Square
  : (P : ∀ k → Modulo k → Set ℓ)
  → (e : ∀ k n → P k (embed n))
  → (st : ∀ k n → PathP (λ i → P k (step n i)) (e k n) (e k (k + n)))
  → ℕ → Set ℓ
Square P e st n
  = PathP (λ i → PathP (λ j → P 0 (squash _ n i j)) (e 0 n) (e 0 n)) refl (st 0 n)

elim
  : (P : ∀ k → Modulo k → Set ℓ)
  → (e : ∀ k n → P k (embed n))
  → (st : ∀ k n → PathP (λ i → P k (step n i)) (e k n) (e k (k + n)))
  → (sq : ∀ n → Square P e st n)
  → (m : Modulo k) → P k m
elim P e st sq (embed n) = e _ n
elim P e st sq (step n i) = st _ n i
elim {k = 0} P e st sq (squash z n i j) = sq n i j

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

swizzle : ∀{m n} → k + (m + n) ≡ m + (k + n)
swizzle {k} {m} {n} =
  k + (m + n) ≡⟨ +-assoc k m n ⟩
  (k + m) + n ≡⟨ cong (_+ n) (+-comm k m) ⟩
  (m + k) + n ≡⟨ sym (+-assoc m k n) ⟩
  m + (k + n) ∎

fembed : Fin k → Modulo k
fembed (n , n<k) = embed n

MReduction : (k : ℕ) → Modulo (suc k) → Set
MReduction k (embed n) = Reduction (suc k) n
MReduction k (step n i) = Reduction≡ {suc k} {n} i

mreduce : (m : Modulo (suc k)) → MReduction k m
mreduce (embed n) = reduce _ n
mreduce (step n i) = {!transport (λ j → Reduction⇒ refl (i ∧ j)) (reduce _ n)!}

