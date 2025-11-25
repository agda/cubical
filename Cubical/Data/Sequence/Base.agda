module Cubical.Data.Sequence.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat
open import Cubical.Data.Fin

private
  variable
    ℓ ℓ' ℓ'' : Level

record Sequence (ℓ : Level) : Type (ℓ-suc ℓ) where
  constructor sequence
  field
    obj : ℕ → Type ℓ
    map : {n : ℕ} → obj n → obj (1 + n)

record SequenceMap (C : Sequence ℓ) (D : Sequence ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor sequencemap
  field
    map : (n : ℕ) → Sequence.obj C n → Sequence.obj D n
    comm : (n : ℕ) (x : Sequence.obj C n)
      → Sequence.map D (map n x) ≡ map (suc n) (Sequence.map C x)

converges : ∀ {ℓ} → Sequence ℓ → (n : ℕ) → Type ℓ
converges seq n = (k : ℕ) → isEquiv (Sequence.map seq {n = k + n})

finiteSequence : (ℓ : Level) (m : ℕ) → Type (ℓ-suc ℓ)
finiteSequence ℓ m = Σ[ S ∈ Sequence ℓ ] converges S m

shiftSequence : ∀ {ℓ} → Sequence ℓ → (n : ℕ) → Sequence ℓ
Sequence.obj (shiftSequence seq n) m = Sequence.obj seq (m + n)
Sequence.map (shiftSequence seq n)  {n = k} x = Sequence.map seq x

-- Isomorphism of sequences
SequenceIso : (A : Sequence ℓ) (B : Sequence ℓ') → Type (ℓ-max ℓ ℓ')
SequenceIso A B =
  Σ[ is ∈ ((n : ℕ) → Iso (Sequence.obj A n) (Sequence.obj B n)) ]
     ((n : ℕ) (a : Sequence.obj A n)
       → Sequence.map B (Iso.fun (is n) a) ≡ Iso.fun (is (suc n))
                         (Sequence.map A a))

-- Equivalences of sequences
SequenceEquiv : (A : Sequence ℓ) (B : Sequence ℓ') → Type (ℓ-max ℓ ℓ')
SequenceEquiv A B =
  Σ[ e ∈ (SequenceMap A B) ]
     ((n : ℕ) → isEquiv (SequenceMap.map e n))

-- Iso to equiv
SequenceIso→SequenceEquiv : {A : Sequence ℓ} {B : Sequence ℓ'}
  → SequenceIso A B → SequenceEquiv A B
SequenceMap.map (fst (SequenceIso→SequenceEquiv (is , e))) x = Iso.fun (is x)
SequenceMap.comm (fst (SequenceIso→SequenceEquiv (is , e))) = e
snd (SequenceIso→SequenceEquiv (is , e)) n = isoToIsEquiv (is n)
