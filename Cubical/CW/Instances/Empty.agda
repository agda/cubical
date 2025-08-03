{-
The empty type as a CW complex
-}
module Cubical.CW.Instances.Empty where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Fin.Inductive
open import Cubical.Data.Empty

open import Cubical.HITs.Pushout
open import Cubical.HITs.SequentialColimit
open import Cubical.HITs.PropositionalTruncation

open import Cubical.CW.Base

module _ (ℓ : Level) where
  finCWskel⊥* : finCWskel ℓ 0
  fst finCWskel⊥* _ = ⊥*
  fst (fst (snd finCWskel⊥*)) _ = 0
  fst (snd (fst (snd finCWskel⊥*))) _ (x , _) = lift (¬Fin0 x)
  fst (snd (snd (fst (snd finCWskel⊥*)))) ()
  snd (snd (snd (fst (snd finCWskel⊥*)))) n =
    uninhabEquiv (λ())
      λ x → invEq LiftEquiv
        ((Iso.inv (PushoutEmptyFam (λ x → ¬Fin0 (fst x)) ¬Fin0)) x)
  snd (snd finCWskel⊥*) _ = uninhabEquiv _ (λ{()}) .snd

  CWskel⊥* : CWskel ℓ
  CWskel⊥* = finCWskel→CWskel 0 finCWskel⊥*

  hasFinCWskel⊥* : hasFinCWskel ⊥*
  fst hasFinCWskel⊥* = 0
  fst (snd hasFinCWskel⊥*) = finCWskel⊥*
  snd (snd hasFinCWskel⊥*) =
    uninhabEquiv (λ{()}) λ{ (incl ()) ; (push () i)}

  hasCWskel⊥* : hasCWskel ⊥*
  fst hasCWskel⊥* = CWskel⊥*
  snd hasCWskel⊥* =
    uninhabEquiv (λ{()}) λ{ (incl ()) ; (push () i)}

  finCW⊥* : finCW ℓ
  fst finCW⊥* = ⊥*
  snd finCW⊥* = ∣ hasFinCWskel⊥* ∣₁

finCWskel⊥ : finCWskel ℓ-zero 0
fst finCWskel⊥ _ = ⊥
fst (fst (snd finCWskel⊥)) _ = 0
fst (snd (fst (snd finCWskel⊥))) _ (x , _) = ¬Fin0 x
fst (snd (snd (fst (snd finCWskel⊥)))) ()
snd (snd (snd (fst (snd finCWskel⊥)))) n =
  uninhabEquiv (λ())
    (Iso.inv (PushoutEmptyFam (λ x → ¬Fin0 (fst x)) ¬Fin0))
snd (snd finCWskel⊥) _ = uninhabEquiv _ (λ{()}) .snd

CWskel⊥ : CWskel ℓ-zero
CWskel⊥ = finCWskel→CWskel 0 finCWskel⊥

hasFinCWskel⊥ : hasFinCWskel ⊥
fst hasFinCWskel⊥ = 0
fst (snd hasFinCWskel⊥) = finCWskel⊥
snd (snd hasFinCWskel⊥) =
  uninhabEquiv (λ{()}) λ{ (incl ()) ; (push () i)}

hasCWskel⊥ : hasCWskel ⊥
fst hasCWskel⊥ = CWskel⊥
snd hasCWskel⊥ =
  uninhabEquiv (λ{()}) λ{ (incl ()) ; (push () i)}

finCW⊥ : finCW ℓ-zero
fst finCW⊥ = ⊥
snd finCW⊥ = ∣ hasFinCWskel⊥ ∣₁
