{-# OPTIONS --safe #-}

module Cubical.Modalities.Instances.DoubleNegation where

open import Cubical.Modalities.Modality

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_; const)
open import Cubical.Foundations.HLevels using (hProp; isProp→isContrPath)
open import Cubical.Foundations.Structure using (⟨_⟩)

open import Cubical.Data.Empty using (⊥*; isProp⊥*)
open import Cubical.Data.Sigma using (_×_; ΣPathP)


module GeneralizedDoubleNegation {ℓ : Level} (Y : hProp ℓ) where

  -- Generalized negation with respect to the proposition Y.
  ¬ : Type ℓ → Type ℓ
  ¬ A = A → ⟨ Y ⟩

  ¬¬ : Type ℓ → Type ℓ
  ¬¬ = ¬ ∘ ¬

  isStableProp : Type ℓ → Type ℓ
  isStableProp A = isProp A × (¬¬ A → A)

  module _ {A : Type ℓ} where

    η : A → ¬¬ A
    η a f = f a

    isPropIsStableProp : isProp (isStableProp A)
    isPropIsStableProp x y = ΣPathP (isPropIsProp _ _ , funExt (λ _ → fst x _ _))

    isContr→isStableProp : isContr A → isStableProp A
    isContr→isStableProp c = (isContr→isProp c) , const (fst c)

    isProp¬ : isProp (¬ A)
    isProp¬ x y = funExt (λ _ → snd Y _ _)

    tripleNegationReduction : ¬ (¬ (¬ A)) → ¬ A
    tripleNegationReduction f a = f (η a)

  module _ {A : Type ℓ} where
    isProp¬¬ : isProp (¬¬ A)
    isProp¬¬ = isProp¬

    isStableProp¬¬ : isStableProp (¬¬ A)
    isStableProp¬¬ = isProp¬¬ , tripleNegationReduction

  map¬¬ : {A B : Type ℓ} → (A → B) → ¬¬ A → ¬¬ B
  map¬¬ f = _∘ (_∘ f)

  modality : Modality ℓ
  Modality.isModal modality = isStableProp
  Modality.isPropIsModal modality = isPropIsStableProp
  Modality.◯ modality = ¬¬
  Modality.◯-isModal modality = isStableProp¬¬
  Modality.η modality = η
  Modality.◯-elim modality {A = A} {B = B} B-modal f x =
    snd (B-modal x) (map¬¬ (λ a → substB (f a)) x)
    where
      substB : {x y : ¬¬ A} → B x → B y
      substB {x} {y} = subst B (isProp¬¬ x y)
  Modality.◯-elim-β modality B-modal f a = fst (B-modal _) _ _
  Modality.◯-=-isModal modality x y =
    isContr→isStableProp (isProp→isContrPath isProp¬¬ _ _)

doubleNegationModality : {ℓ : Level} → Modality ℓ
doubleNegationModality = GeneralizedDoubleNegation.modality (⊥* , isProp⊥*)
