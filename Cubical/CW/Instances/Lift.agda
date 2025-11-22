{-
Universe lifts of CW complexes
-}
module Cubical.CW.Instances.Lift where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sequence

open import Cubical.HITs.Pushout
open import Cubical.HITs.SequentialColimit
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.CW.Base

private
  variable
    ℓA : Level

module _ (ℓ : Level) where
  CWskelLift : CWskel ℓA → CWskel (ℓ-max ℓA ℓ)
  fst (CWskelLift sk) n = Lift {j = ℓ} (fst sk n)
  fst (snd (CWskelLift sk)) = CWskel-fields.card sk
  fst (snd (snd (CWskelLift sk))) n (x , a) =
    lift (CWskel-fields.α sk n (x , a))
  fst (snd (snd (snd (CWskelLift sk)))) (lift x) =
    fst (snd (snd (snd sk))) x
  snd (snd (snd (snd (CWskelLift sk)))) n =
    compEquiv (invEquiv LiftEquiv)
      (compEquiv (CWskel-fields.e sk n)
        (pushoutEquiv _ _ _ _ (idEquiv _)
          LiftEquiv (idEquiv _) refl refl))

  hasCWskelLift : {A : Type ℓA} → hasCWskel A → hasCWskel (Lift {j = ℓ} A)
  fst (hasCWskelLift (sk , e)) = CWskelLift sk
  snd (hasCWskelLift (sk , e)) =
    compEquiv (invEquiv LiftEquiv)
      (compEquiv e
       (invEquiv (isoToEquiv (SeqColimLift {ℓ = ℓ} _))))

  CWLift : CW ℓA → CW (ℓ-max ℓA ℓ)
  fst (CWLift (A , sk)) = Lift {j = ℓ} A
  snd (CWLift (A , sk)) = PT.map hasCWskelLift sk

  finCWskelLift : ∀ {n} → finCWskel ℓA n → finCWskel (ℓ-max ℓA ℓ) n
  fst (finCWskelLift sk) = CWskelLift (finCWskel→CWskel _ sk) .fst
  fst (snd (finCWskelLift sk)) = CWskelLift (finCWskel→CWskel _ sk) .snd
  snd (snd (finCWskelLift sk)) k =
    compEquiv (invEquiv LiftEquiv)
      (compEquiv (_ , snd (snd sk) k) LiftEquiv) .snd

  hasFinCWskelLift : {A : Type ℓA}
    → hasFinCWskel A → hasFinCWskel (Lift {j = ℓ} A)
  fst (hasFinCWskelLift (dim , sk , e)) = dim
  fst (snd (hasFinCWskelLift (dim , sk , e))) = finCWskelLift sk
  snd (snd (hasFinCWskelLift c)) =
    hasCWskelLift (hasFinCWskel→hasCWskel _ c) .snd

  finCWLift : finCW ℓA → finCW (ℓ-max ℓA ℓ)
  fst (finCWLift (A , sk)) = Lift {j = ℓ} A
  snd (finCWLift (A , sk)) = PT.map hasFinCWskelLift sk
