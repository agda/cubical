{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Action where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv

open import Cubical.Homotopy.Base

open import Cubical.Data.Sigma

open import Cubical.Relation.Binary
open BinaryRelation

open import Cubical.Structures.Group
open import Cubical.Structures.LeftAction

open import Cubical.DStructures.Base
open import Cubical.DStructures.Properties
open import Cubical.DStructures.Product
open import Cubical.DStructures.Combine
open import Cubical.DStructures.Type
open import Cubical.DStructures.Group

module _ (ℓ ℓ' : Level) where
  open Groups
  open Morphisms ℓ ℓ'

  Las : ((G , H) : Group {ℓ} × Group {ℓ'}) → Type (ℓ-max ℓ ℓ')
  Las (G , H) = LeftActionStructure ⟨ G ⟩ ⟨ H ⟩

  G²Las = Σ[ GH ∈ G² ] Las GH

  -- two groups with an action structure, i.e. a map ⟨ G ⟩ → ⟨ H ⟩ → ⟨ H ⟩
  SᴰActionStructure : URGStrᴰ (URGStrGroup ℓ ×URG URGStrGroup ℓ')
                              (λ GH → Las GH)
                              (ℓ-max ℓ ℓ')
  SᴰActionStructure =
    makeURGStrᴰ (λ {(G , H)} _α_ (eG , eH) _β_
                   → (g : ⟨ G ⟩) (h : ⟨ H ⟩)
                     → GroupEquiv.eq eH .fst (g α h) ≡ (GroupEquiv.eq eG .fst g) β (GroupEquiv.eq eH .fst h))
                (λ _ _ _ → refl)
                λ (G , H) _α_ → isOfHLevelRespectEquiv 0
                                                       -- (Σ[ _β_ ∈ Las (G , H) ] (_α_ ≡ _β_)
                                                       (Σ-cong-equiv-snd (λ _β_ → invEquiv funExt₂Equiv))
                                                       (isContrSingl _α_)

  SActionStructure : URGStr G²Las (ℓ-max ℓ ℓ')
  SActionStructure = ∫⟨ URGStrGroup ℓ ×URG URGStrGroup ℓ' ⟩ SᴰActionStructure

  SᴰAction : URGStrᴰ SActionStructure
                     (λ ((G , H) , _α_) → IsGroupAction G H _α_)
                     ℓ-zero
  SᴰAction = Subtype→SubURGᴰ (λ ((G , H) , _α_) → (IsGroupAction G H _α_) , {!!})
                             SActionStructure
