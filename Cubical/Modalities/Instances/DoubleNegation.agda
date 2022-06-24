{-# OPTIONS --safe #-}

module Cubical.Modalities.Instances.DoubleNegation where

open import Cubical.Modalities.Modality

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_; const)
open import Cubical.Foundations.HLevels using (isProp→isContrPath)

open import Cubical.Relation.Nullary.Base using (¬_; NonEmpty; Stable)

open import Cubical.Data.Empty using (isProp⊥)
open import Cubical.Data.Sigma using (_×_; ΣPathP)


module _ {ℓ : Level} where

  isStableProp : Type ℓ → Type ℓ
  isStableProp A = isProp A × Stable A

  module _ {A : Type ℓ} where
    η : A → NonEmpty A
    η a f = f a

    isPropIsStableProp : isProp (isStableProp A)
    isPropIsStableProp x y = ΣPathP (isPropIsProp _ _ , funExt (λ _ → fst x _ _))

    isContr→isStableProp : isContr A → isStableProp A
    isContr→isStableProp c = (isContr→isProp c) , const (fst c)

    isProp¬A : isProp (¬ A)
    isProp¬A x y = funExt (λ _ → isProp⊥ _ _)

    tripleNegationReduction : ¬ (¬ (¬ A)) → ¬ A
    tripleNegationReduction f a = f (η a)

  module _ {A : Type ℓ} where
    isPropNonEmpty : isProp (NonEmpty A)
    isPropNonEmpty = isProp¬A

    isStablePropNonEmpty : isStableProp (NonEmpty A)
    isStablePropNonEmpty = isPropNonEmpty , tripleNegationReduction

  mapNonEmpty : {A B : Type ℓ} → (A → B) → NonEmpty A → NonEmpty B
  mapNonEmpty f = _∘ (_∘ f)

  doubleNegationModality : Modality ℓ
  Modality.isModal doubleNegationModality = isStableProp
  Modality.isPropIsModal doubleNegationModality = isPropIsStableProp
  Modality.◯ doubleNegationModality = NonEmpty
  Modality.◯-isModal doubleNegationModality = isStablePropNonEmpty
  Modality.η doubleNegationModality = η
  Modality.◯-elim doubleNegationModality {A = A} {B = B} B-modal f x =
    snd (B-modal x) (mapNonEmpty (λ a → substB (f a)) x)
    where
      substB : {x y : NonEmpty A} → B x → B y
      substB {x} {y} = subst B (isPropNonEmpty x y)
  Modality.◯-elim-β doubleNegationModality B-modal f a = fst (B-modal _) _ _
  Modality.◯-=-isModal doubleNegationModality x y =
    isContr→isStableProp (isProp→isContrPath isPropNonEmpty _ _)
