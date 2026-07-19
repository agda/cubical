module Cubical.Modalities.Instances.Zero where

open import Cubical.Modalities.Modality

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (const)

open import Cubical.Data.Unit using (Unit*; isContrUnit*; tt*)


open Modality

zeroModality : {ℓ : Level} → Modality ℓ
isModal zeroModality = isContr
isPropIsModal zeroModality = isPropIsContr
◯ zeroModality = const Unit*
◯-isModal zeroModality = isContrUnit*
η zeroModality = const tt*
◯-elim zeroModality B-modal _ tt* = fst (B-modal tt*)
◯-elim-β zeroModality B-modal _ _ = snd (B-modal tt*) _
◯-=-isModal zeroModality tt* tt* = refl , λ p → refl
