{-# OPTIONS --lossy-unification #-}
module Cubical.HITs.SequentialColimit.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat
open import Cubical.Data.Sequence
open import Cubical.Data.FinSequence
open import Cubical.Data.Fin.Inductive


private
  variable
    ℓ ℓ' : Level

open Sequence

data SeqColim (X : Sequence ℓ) : Type ℓ where
  incl : {n : ℕ} → X .obj n → SeqColim X
  push : {n : ℕ} (x : X .obj n) → incl x ≡ incl (X .map x)

data FinSeqColim (m : ℕ) (X : Sequence ℓ) : Type ℓ where
  fincl : (n : Fin (suc m)) → X .obj (fst n) → FinSeqColim m X
  fpush : (n : Fin m) (x : X .obj (fst n))
    → fincl (injectSuc n) x ≡ fincl (fsuc n) (X .map x)

FinSeqColim→Colim : (m : ℕ) {X : Sequence ℓ} → FinSeqColim m X → SeqColim X
FinSeqColim→Colim m (fincl n x) = incl x
FinSeqColim→Colim m (fpush n x i) = push x i

realiseSequenceMap : {C : Sequence ℓ} {D : Sequence ℓ'}
  → SequenceMap C D → SeqColim C → SeqColim D
realiseSequenceMap (sequencemap map comm) (incl x) = incl (map _ x)
realiseSequenceMap (sequencemap map comm) (push {n = n} x i) =
  (push (map n x) ∙ λ i → incl (comm n x i)) i

LiftSequence : ∀ {ℓA} (ℓ↑ : Level) (S : Sequence ℓA) →
  Sequence (ℓ-max ℓA ℓ↑)
obj (LiftSequence ℓ↑ S) n = Lift {j = ℓ↑} (obj S n)
map (LiftSequence ℓ↑ S) = liftFun (map S)
