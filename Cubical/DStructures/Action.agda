{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Action where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma

open import Cubical.Structures.Group
open import Cubical.Structures.LeftAction

open import Cubical.DStructures.Base
open import Cubical.DStructures.Properties
open import Cubical.DStructures.Product
open import Cubical.DStructures.Type
open import Cubical.DStructures.Group

module Action (ℓ ℓ' : Level) where
  open Groups
  open Morphisms ℓ ℓ'

  private
    Las : ((G , H) : Group {ℓ} × Group {ℓ'}) → Type (ℓ-max ℓ ℓ')
    Las (G , H) = LeftActionStructure ⟨ G ⟩ ⟨ H ⟩

  G²Las = Σ[ GH ∈ G² ] Las GH
  G²Act = Σ[ ((G , H) , _α_) ∈ G²Las ] (IsGroupAction G H _α_)

  -- two groups with an action structure, i.e. a map ⟨ G ⟩ → ⟨ H ⟩ → ⟨ H ⟩
  SᴰActionStr : URGStrᴰ (URGStrGroup ℓ ×URG URGStrGroup ℓ')
                              (λ GH → Las GH)
                              (ℓ-max ℓ ℓ')
  SᴰActionStr =
    makeURGStrᴰ (λ {(G , H)} _α_ (eG , eH) _β_
                   → (g : ⟨ G ⟩) (h : ⟨ H ⟩)
                     → GroupEquiv.eq eH .fst (g α h) ≡ (GroupEquiv.eq eG .fst g) β (GroupEquiv.eq eH .fst h))
                (λ _ _ _ → refl)
                λ (G , H) _α_ → isOfHLevelRespectEquiv 0
                                                       -- (Σ[ _β_ ∈ Las (G , H) ] (_α_ ≡ _β_)
                                                       (Σ-cong-equiv-snd (λ _β_ → invEquiv funExt₂Equiv))
                                                       (isContrSingl _α_)

  SActionStr : URGStr G²Las (ℓ-max ℓ ℓ')
  SActionStr = ∫⟨ URGStrGroup ℓ ×URG URGStrGroup ℓ' ⟩ SᴰActionStr

  open ActionΣTheory

  SᴰAction : URGStrᴰ SActionStr
                     (λ ((G , H) , _α_) → IsGroupAction G H _α_)
                     ℓ-zero
  SᴰAction = Subtype→SubURGᴰ (λ ((G , H) , _α_) → IsGroupAction G H _α_ , isPropIsGroupAction G H _α_)
                             SActionStr

  SAction : URGStr G²Act (ℓ-max ℓ ℓ')
  SAction = ∫⟨ SActionStr ⟩ SᴰAction
