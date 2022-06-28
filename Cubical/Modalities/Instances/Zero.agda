{-# OPTIONS --safe #-}
module Cubical.Modalities.Instances.Zero where

open import Cubical.Modalities.Modality

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (const)

open import Cubical.Data.Unit using (Unit*; isContrUnit*; tt*)


zeroModality : {ℓ : Level} → Modality ℓ
Modality.isModal zeroModality = isContr
Modality.isPropIsModal zeroModality = isPropIsContr
Modality.◯ zeroModality = const Unit*
Modality.◯-isModal zeroModality = isContrUnit*
Modality.η zeroModality = const tt*
Modality.◯-elim zeroModality B-modal _ tt* = fst (B-modal tt*)
Modality.◯-elim-β zeroModality B-modal _ _ = snd (B-modal tt*) _
Modality.◯-=-isModal zeroModality tt* tt* = refl , λ p → refl
