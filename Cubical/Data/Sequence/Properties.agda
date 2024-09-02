{-# OPTIONS --safe #-}
module Cubical.Data.Sequence.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sequence.Base


private
  variable
    ℓ ℓ' ℓ'' : Level
idSequenceMap : (C : Sequence ℓ) → SequenceMap C C
SequenceMap.map (idSequenceMap C) n x = x
SequenceMap.comm (idSequenceMap C) n x = refl

composeSequenceMap : {C : Sequence ℓ} {D : Sequence ℓ'} {E : Sequence ℓ''}
  (g : SequenceMap D E) (f : SequenceMap C D) → SequenceMap C E
composeSequenceMap g f .SequenceMap.map n x = g .SequenceMap.map n (f .SequenceMap.map n x)
composeSequenceMap g f .SequenceMap.comm n x =
    g .SequenceMap.comm n _
  ∙ cong (g .SequenceMap.map (suc n)) (f .SequenceMap.comm n x)
