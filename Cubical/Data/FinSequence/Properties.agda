module Cubical.Data.FinSequence.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Fin.Inductive.Base
open import Cubical.Data.FinSequence.Base
open import Cubical.Data.Sequence


private
  variable
    ℓ ℓ' ℓ'' : Level

open Sequence
open FinSequence
open FinSequenceMap

idFinSequenceMap : (m : ℕ) (C : FinSequence m ℓ) → FinSequenceMap C C
fmap (idFinSequenceMap m C) p x = x
fcomm (idFinSequenceMap m C) p _ = refl

composeFinSequenceMap : (m : ℕ) {C : FinSequence m ℓ} {D : FinSequence m ℓ'}
  {E : FinSequence m ℓ''}
  (g : FinSequenceMap D E) (f : FinSequenceMap C D) → FinSequenceMap C E
fmap (composeFinSequenceMap m g f) n x = fmap g n (fmap f n x)
fcomm (composeFinSequenceMap m g f) n x =
    fcomm g n _
  ∙ cong (fmap g (fsuc n)) (fcomm f n x)

Sequence→FinSequence : (m : ℕ) → Sequence ℓ → FinSequence m ℓ
fobj (Sequence→FinSequence m C) x = obj C (fst x)
fmap (Sequence→FinSequence m C) x = map C x

SequenceMap→FinSequenceMap : (m : ℕ) (C D : Sequence ℓ)
  → SequenceMap C D
  → FinSequenceMap (Sequence→FinSequence m C) (Sequence→FinSequence m D)
fmap (SequenceMap→FinSequenceMap m C D ϕ) t = SequenceMap.map ϕ  (fst t)
fcomm (SequenceMap→FinSequenceMap m C D ϕ) t = SequenceMap.comm ϕ (fst t)
