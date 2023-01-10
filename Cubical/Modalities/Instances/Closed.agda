{-# OPTIONS --safe #-}

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

  Modality.◯-isModal closedModality {A = A} x
    = subst (λ t → isContr (join t A)) (sym ⟨X⟩≡Unit*) join-leftUnit
    where
      ⟨X⟩≡Unit* : ⟨ X ⟩ ≡ Unit*
      ⟨X⟩≡Unit* = isContr→≡Unit* (inhProp→isContr x (snd X))

  Modality.◯-elim closedModality {B = B} B-modal f (inl x) = fst (B-modal (inl x) x)
  Modality.◯-elim closedModality {B = B} B-modal f (inr a) = f a
  Modality.◯-elim closedModality {B = B} B-modal f (push x a i) =
     hcomp
       (λ where
         j (i = i0) → contr (transport (λ k → B (push x a (~ k))) (f a)) (~ j) -- Contractibilty
         j (i = i1) → f a)
       (transport-filler (sym (cong B (push x a))) (f a) (~ i))
    where
      contr : (y : B (inl x)) → fst (B-modal (inl x) x) ≡ y
      contr = snd (B-modal (inl x) x)

  Modality.◯-elim-β closedModality {B = B} B-modal f a = refl

  Modality.◯-=-isModal closedModality a b x = isContr→isContrPath (◯-isModal x) a b
