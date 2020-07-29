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

module Semidirect where
  semidirectProd : (G : Group {ℓ}) (H : Group {ℓ'}) (Act : GroupAction H G)
                   → Group {ℓ-max ℓ ℓ'}
  semidirectProd G H Act = makeGroup-left {A = sd-carrier} sd-0 _+sd_ -sd_ sd-set sd-assoc sd-lId sd-lCancel
    where
      open ActionNotationα Act
      open ActionLemmas Act
      open GroupNotationG G
      open GroupNotationH H

      -- sd stands for semidirect
      sd-carrier = ⟨ G ⟩ × ⟨ H ⟩
      sd-0 = 0ᴳ , 0ᴴ

      module _ ((g , h) : sd-carrier) where
        -sd_ = (-ᴴ h) α (-ᴳ g) , -ᴴ h

        _+sd_ = λ (g' , h') → g +ᴳ (h α g') , h +ᴴ h'

      abstract
        sd-set = isSetΣ setᴳ (λ _ → setᴴ)
        sd-lId = λ ((g , h) : sd-carrier) → ΣPathP (lIdᴳ (0ᴴ α g) ∙ (α-id g) , lIdᴴ h)
        sd-lCancel = λ ((g , h) : sd-carrier) → ΣPathP ((sym (α-hom (-ᴴ h) (-ᴳ g) g) ∙∙ cong ((-ᴴ h) α_) (lCancelᴳ g) ∙∙ actOnUnit (-ᴴ h)) , lCancelᴴ h)


        sd-assoc = λ (a , x) (b , y) (c , z) → ΣPathP ((a +ᴳ (x α (b  +ᴳ (y α c)))
                                    ≡⟨ cong (a +ᴳ_) (α-hom x b (y α c)) ⟩
                                a +ᴳ ((x α b) +ᴳ (x α (y α c)))
                                    ≡⟨ assocᴳ a (x α b) (x α (y α c)) ⟩
                                (a +ᴳ (x α b)) +ᴳ (x α (y α c))
                                    ≡⟨ cong ((a +ᴳ (x α b)) +ᴳ_) (sym (α-assoc x y c)) ⟩
                                (a +ᴳ (x α b)) +ᴳ ((x +ᴴ y) α c) ∎) , assocᴴ x y z)

  syntax semidirectProd N H α = N ⋊⟨ α ⟩ H

  module Projections {N : Group {ℓ}} {H : Group {ℓ'}} (α : GroupAction H N) where
    π₁ : ⟨ N ⋊⟨ α ⟩ H ⟩ → ⟨ N ⟩
    π₁ = fst

    ι₁ : GroupHom N (N ⋊⟨ α ⟩ H)
    ι₁ = grouphom (λ n → n , Group.0g H) λ n n' → ΣPathP {!!}

    π₂ : GroupHom (N ⋊⟨ α ⟩ H) H
    π₂ = grouphom snd λ _ _ → refl

    ι₂ : GroupHom H (N ⋊⟨ α ⟩ H)
    ι₂ = grouphom (λ h → Group.0g N , h) λ h h' → ΣPathP ({!!} , refl)

    π₂-hasSec : isGroupHomRet ι₂ π₂
    π₂-hasSec = GroupMorphismExt (λ _ → refl)


module _ {ℓ : Level} (G₀ : Group {ℓ}) (ℓ' : Level) where
  private
    ℓℓ' = ℓ-max ℓ ℓ'

  SplitExt : Type (ℓ-suc ℓℓ')
  SplitExt = Σ[ G₁ ∈ Group {ℓℓ'} ] Σ[ ι ∈ GroupHom G₀ G₁ ] Σ[ σ ∈ GroupHom G₁ G₀ ] isGroupHomRet ι σ

  GroupAct : Type (ℓ-suc ℓℓ')
  GroupAct = Σ[ G₁ ∈ Group {ℓℓ'} ] Σ[ _α_ ∈ LeftActionStructure ⟨ G₀ ⟩ ⟨ G₁ ⟩ ] (IsGroupAction G₀ G₁ _α_)

  SplitExt→GroupAct : SplitExt → GroupAct
  SplitExt→GroupAct (G₁ , ι , σ , isSplit) = ker-σ , _α_ , isAct
    where
      open Kernel
      ker-σ : Group {ℓℓ'}
      ker-σ = ker σ
      _α_ : LeftActionStructure ⟨ G₀ ⟩ ⟨ ker-σ ⟩
      _α_ = {!!}
      isAct : IsGroupAction G₀ ker-σ _α_
      isAct = {!!}

  GroupAct→SplitExt : GroupAct → SplitExt
  GroupAct→SplitExt (G₁ , _α_ , isAct) = G₁⋊G₀ , ι₂ α , π₂ α , π₂-hasSec α
    where
      open Semidirect
      open Projections
      α = groupaction _α_ isAct
      G₁⋊G₀ : Group {ℓℓ'}
      G₁⋊G₀ = G₁ ⋊⟨ α ⟩ G₀

module _ (ℓ ℓ' : Level) where
  private
    ℓℓ' = ℓ-max ℓ ℓ'

  ReflexiveGraph = Σ[ (G₀ , G₁ , ι , σ , split-σ) ∈ (Σ[ G₀ ∈ Group {ℓ} ] SplitExt G₀ ℓ') ] Σ[ τ ∈ GroupHom G₁ G₀ ] isGroupHomRet ι τ

  PreCrossedModule = Σ[ (G₀ , G₁ , _α_ , isAct) ∈ (Σ[ G₀ ∈ Group {ℓ} ] GroupAct G₀ ℓ') ] (Σ[ φ ∈ GroupHom G₁ G₀ ] isEquivariant _α_ φ)
{-
module _ where
  open import Cubical.Data.Maybe
  record Hierarchy {A : Type ℓ} (𝒮-A : URGStr A ℓ) : Type (ℓ-suc ℓ) where
    coinductive
    field
      B : A → Type ℓ
      𝒮ᴰ-B : URGStrᴰ 𝒮-A B ℓ
      ℋ : Maybe (Hierarchy {A = Σ A B} (∫⟨ 𝒮-A ⟩ 𝒮ᴰ-B))
-}
