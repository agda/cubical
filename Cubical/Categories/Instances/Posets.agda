{-# OPTIONS --safe #-}
module Cubical.Categories.Instances.Posets where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function as Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Relation.Binary.Order.Poset.Mappings

open import Cubical.Categories.Category

open Category hiding (_∘_)

PosetsCategory : ∀ ℓ ℓ' → Category (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
PosetsCategory ℓ ℓ' .ob = Poset ℓ ℓ'
PosetsCategory ℓ ℓ' .Hom[_,_] P Q = Σ[ f ∈ (⟨ P ⟩ → ⟨ Q ⟩) ] IsIsotone (str P) f (str Q)
PosetsCategory ℓ ℓ' .id = idfun _ , isisotone λ _ _ → idfun _
PosetsCategory ℓ ℓ' ._⋆_ (f , fMon) (g , gMon) = g ∘ f , IsIsotone-∘ _ _ _ _ _ fMon gMon
PosetsCategory ℓ ℓ' .⋆IdL _ = refl
PosetsCategory ℓ ℓ' .⋆IdR _ = refl
PosetsCategory ℓ ℓ' .⋆Assoc _ _ _ = refl
PosetsCategory ℓ ℓ' .isSetHom {x = P} {y = Q} = isSetΣSndProp (isSet→ Q.is-set) λ _ → isPropIsIsotone _ _ _
  where module Q = PosetStr (str Q)
