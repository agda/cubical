{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Structures.Strict2Group where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv

open import Cubical.Homotopy.Base

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Relation.Binary


open import Cubical.Algebra.Group
open import Cubical.Structures.LeftAction

open import Cubical.DStructures.Base
open import Cubical.DStructures.Meta.Properties

open import Cubical.DStructures.Structures.Constant
open import Cubical.DStructures.Structures.Type
open import Cubical.DStructures.Structures.Group
open import Cubical.DStructures.Structures.ReflGraph
open import Cubical.DStructures.Structures.VertComp

private
  variable
    ℓ ℓ' : Level

module _ (ℓ ℓ' : Level) where
  private
    ℓℓ' = ℓ-max ℓ ℓ'


  𝒮ᴰ-Strict2Group : URGStrᴰ (𝒮-ReflGraph ℓ ℓ')
                            VertComp
                            ℓ-zero
  𝒮ᴰ-Strict2Group = Subtype→Sub-𝒮ᴰ (λ 𝒢 → VertComp 𝒢 , isPropVertComp 𝒢)
                                   (𝒮-ReflGraph ℓ ℓ')

  Strict2Group : Type (ℓ-suc ℓℓ')
  Strict2Group = Σ[ 𝒢 ∈ ReflGraph ℓ ℓ' ] VertComp 𝒢


  record S2G : Type (ℓ-suc ℓℓ') where
    no-eta-equality
    field
      G₀ : Group {ℓ}
      G₁ : Group {ℓ'}
      σ : GroupHom G₁ G₀
      τ : GroupHom G₁ G₀
      ι : GroupHom G₀ G₁
      split-σ : isGroupSplitEpi ι σ
      split-τ : isGroupSplitEpi ι τ
      V : VertComp (((((G₀ , G₁) , ι , σ) , split-σ) , τ) , split-τ)

{-
  open S2G

  make-S2G : {G₀ : Group {ℓ}} {G₁ : Group {ℓ'}}
             → (σ τ : GroupHom G₁ G₀)
             → (ι : GroupHom G₀ G₁)
             → (split-σ : isGroupSplitEpi ι σ)
             → (split-τ : isGroupSplitEpi ι τ)
             → VertComp (((((G₀ , G₁) , ι , σ) , split-σ) , τ) , split-τ)
             → S2G
  make-S2G = {!!}



Group→S2G : Group {ℓ} → S2G ℓ ℓ
Group→S2G G .G₀ = G
Group→S2G G .G₁ = G
Group→S2G G .σ = idGroupHom G
Group→S2G G .τ = idGroupHom G
Group→S2G G .ι = idGroupHom G
Group→S2G G .split-σ = GroupMorphismExt (λ _ → refl)
Group→S2G G .split-τ = GroupMorphismExt (λ _ → refl)
Group→S2G G .V = {!!}
-}
