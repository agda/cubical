
module Cubical.Modalities.Instances.Closed where

open import Cubical.Modalities.Modality

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hProp; isProp→; inhProp→isContr; isContr→isContrPath)
open import Cubical.Foundations.Structure using (⟨_⟩)

open import Cubical.Data.Unit

open import Cubical.HITs.Join

module _ {ℓ : Level} (X : hProp ℓ) where

  closedModality : Modality ℓ

  open Modality closedModality

  Modality.◯ closedModality A = join ⟨ X ⟩ A
  Modality.η closedModality = inr

  Modality.isModal closedModality A = ⟨ X ⟩ → isContr A
  Modality.isPropIsModal closedModality = isProp→ isPropIsContr

  Modality.◯-isModal closedModality {A = A} x =
    subst (λ t → isContr (join t A)) (sym ⟨X⟩≡Unit*) joinAnnihilL
    where
      ⟨X⟩≡Unit* : ⟨ X ⟩ ≡ Unit*
      ⟨X⟩≡Unit* = isContr→≡Unit* (inhProp→isContr x (snd X))

  Modality.◯-elim closedModality {B = B} B-modal f (inl x) = fst (B-modal (inl x) x)
  Modality.◯-elim closedModality {B = B} B-modal f (inr a) = f a
  Modality.◯-elim closedModality {B = B} B-modal f (push x a i) =
    isProp→PathP (λ i → isContr→isProp (B-modal (push x a i) x))
                 (B-modal (inl x) x .fst) (f a) i

  Modality.◯-elim-β closedModality {B = B} B-modal f a = refl

  Modality.◯-=-isModal closedModality a b x = isContr→isContrPath (◯-isModal x) a b
