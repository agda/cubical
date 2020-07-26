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

module Kernel where
  ker : {G : Group {ℓ}} {H : Group {ℓ'}} (f : GroupHom G H) → Group {ℓ-max ℓ ℓ'}
  ker {G = G} {H = H} f* =
    makeGroup-left {A = Σ[ g ∈ ⟨ G ⟩ ] f g ≡ 0ᴴ }
                   (0ᴳ , {!!})
                   (λ (g , p) (g' , p') → g +ᴳ g , {!!})
                   (λ (g , p) → -ᴳ g , {!!})
                   {!!}
                   {!!}
                   {!!}
                   {!!}
    where
      f = GroupHom.fun f*
      f-hom = GroupHom.isHom f*

      open Group
      0ᴴ = H .0g
      0ᴳ = G .0g
      _+ᴴ_ = H ._+_
      _+ᴳ_ = G ._+_
      -ᴳ_ = G .-_

module Semidirect where

  semidirectProduct : (N : Group {ℓ}) (H : Group {ℓ'}) (Act : GroupAction H N)
                      → Group {ℓ-max ℓ ℓ'}
  semidirectProduct N H Act
    = makeGroup-left {A = N .Carrier × H .Carrier} -- carrier
                     -- identity
                     (N .0g , H .0g)
                     -- _+_
                     (λ (n , h) (n' , h') → n +N (h α n') , h +H h')
                     -- -_
                     (λ (n , h) → (-H h) α (-N n) , -H h)
                     -- set
                     (isSetΣ (N .is-set) λ _ → H .is-set)
                     -- assoc
                     (λ (a , x) (b , y) (c , z)
                       → ΣPathP ({!_∙∙_∙∙_!} , H .assoc x y z))
                     -- lUnit
                     (λ (n , h) → ΣPathP (lUnitN ((H .0g) α n) ∙ α-id n , lUnitH h))
                     -- lCancel
                     λ (n , h) → ΣPathP ((sym (α-hom (-H h) (-N n) n) ∙∙ cong ((-H h) α_) (lCancelN n) ∙∙ {!actg1≡1!}) ,  lCancelH h)
                     where
                       open GroupAction Act
                       open Group
                       _+N_ = N ._+_
                       _+H_ = H ._+_
                       -N_ = N .-_
                       -H_ = H .-_
                       lUnitH = IsGroup.lid (H .isGroup)
                       lUnitN = IsGroup.lid (N .isGroup)
                       lCancelH = IsGroup.invl (H .isGroup)
                       lCancelN = IsGroup.invl (N .isGroup)
                       α-id = IsGroupAction.identity isGroupAction
                       α-hom = IsGroupAction.isHom isGroupAction

  syntax semidirectProduct N H α = N ⋊⟨ α ⟩ H

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
