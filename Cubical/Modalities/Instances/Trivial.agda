{-# OPTIONS --safe #-}
module Cubical.Modalities.Instances.Trivial where

-- TODO: imports
open import Cubical.Modalities.Modality

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Unit


trivialModality : {ℓ : Level} → Modality ℓ
Modality.isModal trivialModality = isContr
Modality.isPropIsModal trivialModality = isPropIsContr
Modality.◯ trivialModality = const Unit*
Modality.◯-isModal trivialModality = isContrUnit*
Modality.η trivialModality = const tt*
Modality.◯-elim trivialModality B-modal _ tt* = fst (B-modal tt*)
Modality.◯-elim-β trivialModality B-modal _ _ = snd (B-modal tt*) _
Modality.◯-=-isModal trivialModality tt* tt* = refl , λ p → refl
