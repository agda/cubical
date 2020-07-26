{-# OPTIONS --cubical --no-import-sorts --safe --guardedness #-}
module Cubical.DStructures.Experiments where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

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
open import Cubical.DStructures.Isomorphism
open import Cubical.DStructures.Strict2Group
open import Cubical.DStructures.XModule

private
  variable
    ℓ ℓ' ℓ'' ℓ₁ ℓ₁' ℓ₁'' ℓ₂ ℓA ℓA' ℓ≅A ℓ≅A' ℓB ℓB' ℓ≅B ℓC ℓ≅C ℓ≅ᴰ ℓ≅ᴰ' : Level


{-
transport-𝒮ᴰ : {A : Type ℓ} {A' : Type ℓ} (p : A ≡ A')
                {𝒮-A : URGStr A ℓ≅A}
                {𝒮-A' : URGStr A' ℓ≅A}
                (p-𝒮 : PathP (λ i → URGStr (p i) ℓ≅A) 𝒮-A 𝒮-A')
                {B : A → Type ℓB} (𝒮ᴰ-A\B : URGStrᴰ 𝒮-A B ℓ≅B)
                → URGStrᴰ 𝒮-A'
                          (λ a' → B (transport (sym p) a'))
                          ℓ≅B
transport-𝒮ᴰ p p-𝒮 = {!make-𝒮ᴰ!}
-}

{-
module _ (ℓ ℓ' : Level) where
  open MorphismTree ℓ ℓ'

  𝒮ᴰ-G\GFB : URGStrᴰ (𝒮-group ℓ)
                     (λ G → Σ[ H ∈ Group {ℓ'} ] GroupHom G H × GroupHom H G)
                     (ℓ-max ℓ ℓ')
  𝒮ᴰ-G\GFB = splitTotal-𝒮ᴰ (𝒮-group ℓ)
                           (𝒮ᴰ-const (𝒮-group ℓ) (𝒮-group ℓ'))
                           𝒮ᴰ-G²\FB

  𝒮-G\GFB = ∫⟨ 𝒮-group ℓ ⟩ 𝒮ᴰ-G\GFB

  𝒮ᴰ-G\GFBSplit : URGStrᴰ (𝒮-group ℓ)
                          (λ G → Σ[ (H , f , b) ∈ Σ[ H ∈ Group {ℓ'} ] GroupHom G H × GroupHom H G ] isGroupHomRet f b)
                          (ℓ-max ℓ ℓ')
  𝒮ᴰ-G\GFBSplit = splitTotal-𝒮ᴰ (𝒮-group ℓ)
                                𝒮ᴰ-G\GFB
                                (transport-𝒮ᴰ (ua e) {!!} 𝒮ᴰ-G²FB\Split)
                                where
                                  GGFB = Σ[ G ∈ Group {ℓ} ] Σ[ H ∈ Group {ℓ'} ] GroupHom G H × GroupHom H G
                                  e : G²FB ≃ GGFB
                                  e = compEquiv Σ-assoc-≃ {!!}
-}

module _ {ℓ : Level} (G₀ : Group {ℓ}) (ℓ' : Level) where
  private
    ℓℓ' = ℓ-max ℓ ℓ'

  SplitExt : Type (ℓ-suc ℓℓ')
  SplitExt = Σ[ G₁ ∈ Group {ℓℓ'} ] Σ[ ι ∈ GroupHom G₀ G₁ ] Σ[ τ ∈ GroupHom G₁ G₀ ] isGroupHomRet τ ι

  GroupAct : Type (ℓ-suc ℓℓ')
  GroupAct = Σ[ G₁ ∈ Group {ℓℓ'} ] Σ[ _α_ ∈ LeftActionStructure ⟨ G₀ ⟩ ⟨ G₁ ⟩ ] (IsGroupAction G₀ G₁ _α_)

  SplitExt→GroupAct : SplitExt → GroupAct
  SplitExt→GroupAct (G₁ , ι , τ , isSplit) = ker-τ , _α_ , isAct
    where
      ker-τ : Group {ℓℓ'}
      ker-τ = {!!}
      _α_ : LeftActionStructure ⟨ G₀ ⟩ ⟨ ker-τ ⟩
      _α_ = {!!}
      isAct : IsGroupAction G₀ ker-τ _α_
      isAct = {!!}

  GroupAct→SplitExt : GroupAct → SplitExt
  GroupAct→SplitExt (G₁ , _α_ , isAct) = G₁⋊G₀ , ι , τ , isSplit
    where
      G₁⋊G₀ : Group {ℓℓ'}
      G₁⋊G₀ = {!!}
      ι : GroupHom G₀ G₁⋊G₀
      ι = {!!}
      τ : GroupHom G₁⋊G₀ G₀
      τ = {!!}
      isSplit : isGroupHomRet τ ι
      isSplit = {!!}


module _ (ℓ ℓ' : Level) where
  private
    ℓℓ' = ℓ-max ℓ ℓ'

  ReflexiveGraph = Σ[ (G₀ , G₁ , ι , τ , split-τ) ∈ (Σ[ G₀ ∈ Group {ℓ} ] SplitExt G₀ ℓ') ] Σ[ σ ∈ GroupHom G₁ G₀ ] isGroupHomRet σ ι

  PreCrossedModule = Σ[ (G₀ , G₁ , _α_ , isAct) ∈ (Σ[ G₀ ∈ Group {ℓ} ] GroupAct G₀ ℓ') ] (Σ[ φ ∈ GroupHom G₁ G₀ ] isEquivariant _α_ φ)


module _ where

{-
  record Hierarchy {A : Type ℓ} (𝒮-A : URGStr A ℓ) : Type (ℓ-suc ℓ) where
    coinductive
    field
      B : A → Type ℓ
      𝒮ᴰ-B : URGStrᴰ 𝒮-A B ℓ
      ℋ : Hierarchy {A = Σ A B} (∫⟨ 𝒮-A ⟩ 𝒮ᴰ-B)
-}

{-
  open import Cubical.Data.Maybe
  record Hierarchy {A : Type ℓ} (𝒮-A : URGStr A ℓ) : Type (ℓ-suc ℓ) where
    coinductive
    field
      B : A → Type ℓ
      𝒮ᴰ-B : URGStrᴰ 𝒮-A B ℓ
      ℋ : Maybe (Hierarchy {A = Σ A B} (∫⟨ 𝒮-A ⟩ 𝒮ᴰ-B))
-}
