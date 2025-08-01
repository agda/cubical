
{-
  The stable version of the James splitting:
    ΣΩΣX ≃ ΣX ⋁ Σ(X ⋀ ΩΣX)
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.HITs.Susp
open import Cubical.HITs.Susp.SuspProduct
open import Cubical.HITs.Pushout
open import Cubical.HITs.Pushout.Flattening
open import Cubical.HITs.Wedge
open import Cubical.HITs.SmashProduct

open import Cubical.Homotopy.Loopspace

module Cubical.HITs.James.Stable {ℓ} (X∙@(X , x₀) : Pointed ℓ) where

module ContrPushout where
  Code : Pushout (terminal X) (terminal X) → Type ℓ
  Code x = inl _ ≡ x

  ΩΣX = Code (inl _)
  ΩΣX∙ : Pointed _
  ΩΣX∙ = ΩΣX , refl

  α : X × ΩΣX → ΩΣX
  α (x , p) = (p ∙ push x) ∙ sym (push x₀)

  open FlatteningLemma
    (terminal X) (terminal X)
    (Code ∘ inl) (Code ∘ inr)
    (pathToEquiv ∘ cong (inl tt ≡_) ∘ push)

  pushoutEq : Pushout Σf Σg ≃ Pushout snd α
  pushoutEq = pushoutEquiv _ _ _ _
    (idEquiv (X × ΩΣX)) (ΣUnit _)
    (ΣUnit _ ∙ₑ compPathrEquiv (sym (push x₀)))
    refl (funExt λ (x , p)
      → cong (_∙ sym (push x₀)) (substInPathsL (push x) p))

  Code≡E : ∀ x → Code x ≡ E x
  Code≡E (inl _) = refl
  Code≡E (inr _) = refl
  Code≡E (push a i) j = uaη (cong Code (push a)) (~ j) i

  isContrΣE : isContr (Σ _ E)
  isContrΣE = subst isContr (Σ-cong-snd Code≡E) (isContrSingl (inl tt))

  isContrPushout : isContr (Pushout snd α)
  isContrPushout = isOfHLevelRespectEquiv _ (flatten ∙ₑ pushoutEq) isContrΣE

open ContrPushout

LoopSuspSquare : commSquare
LoopSuspSquare = record
  { sp = 3span snd α
  ; P = Unit* {ℓ}
  ; comm = refl }

LoopSuspPushoutSquare : PushoutSquare
LoopSuspPushoutSquare = (LoopSuspSquare , isContr→≃Unit* isContrPushout .snd)

open PushoutPasteLeft LoopSuspPushoutSquare
  (λ _ → lift {j = ℓ} tt) _ _ (funExt merid)

cofib-snd-James : cofib (λ (r : X × ΩΣX) → snd r) ≃ Susp ΩΣX
cofib-snd-James = pushoutSwitchEquiv
  ∙ₑ pushoutEquiv snd _ snd _
    (idEquiv _) (idEquiv _) Unit≃Unit* refl refl
  ∙ₑ (_ , isPushoutRightSquare→isPushoutTotSquare
    (SuspPushoutSquare _ _ ΩΣX))

StableJames : Susp ΩΣX ≃ Susp∙ X ⋁ Susp∙ (X∙ ⋀ ΩΣX∙)
StableJames = invEquiv cofib-snd-James ∙ₑ cofib-snd X∙ (ΩΣX , refl)
