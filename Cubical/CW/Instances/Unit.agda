{-
The unit type as a CW complex
-}
module Cubical.CW.Instances.Unit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Fin.Inductive
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Sequence.Base

open import Cubical.HITs.Pushout
open import Cubical.HITs.SequentialColimit
open import Cubical.HITs.PropositionalTruncation

open import Cubical.CW.Base

CWskelUnit* : ∀ {ℓ} → CWskel ℓ
fst CWskelUnit* zero = ⊥*
fst CWskelUnit* (suc n) = Unit*
fst (snd CWskelUnit*) zero = 1
fst (snd CWskelUnit*) (suc x) = 0
fst (snd (snd CWskelUnit*)) zero ()
fst (snd (snd CWskelUnit*)) (suc n) _ = tt*
snd (snd (snd (snd CWskelUnit*))) zero =
    compEquiv (compEquiv (compEquiv (invEquiv LiftEquiv)
    (isoToEquiv Iso-Unit-Fin1))
      (isoToEquiv (PushoutEmptyFam (λ()) λ()))) (symPushout _ _)
snd (snd (snd (snd CWskelUnit*))) (suc n) =
  isoToEquiv (PushoutEmptyFam (λ()) λ())

convergesCWskelUnit* : ∀ {ℓ} → converges (realiseSeq (CWskelUnit* {ℓ})) 1
convergesCWskelUnit* zero = idIsEquiv _
convergesCWskelUnit* (suc k) = idIsEquiv _

hasFinCWskelUnit* : ∀ {ℓ} → hasFinCWskel (Unit* {ℓ})
fst hasFinCWskelUnit* = 1
fst (fst (snd hasFinCWskelUnit*)) = CWskelUnit* .fst
fst (snd (fst (snd hasFinCWskelUnit*))) = CWskelUnit* .snd
snd (snd (fst (snd hasFinCWskelUnit*))) = convergesCWskelUnit*
fst (snd (snd hasFinCWskelUnit*)) = _
snd (snd (snd hasFinCWskelUnit*)) =
  converges→isEquivIncl {seq = realiseSeq CWskelUnit*} 1
    convergesCWskelUnit*

finCWUnit* : (ℓ : Level) → finCW ℓ
fst (finCWUnit* ℓ) = Unit*
snd (finCWUnit* ℓ) = ∣ hasFinCWskelUnit* ∣₁

finCWUnit : finCW ℓ-zero
fst finCWUnit = Unit
snd finCWUnit = subst isFinCW (sym (ua Unit≃Unit*)) ∣ hasFinCWskelUnit* ∣₁
