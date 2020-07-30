{-# OPTIONS --cubical --no-import-sorts --safe #-}
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

open import Cubical.Structures.Subtype
open import Cubical.Structures.Group
open import Cubical.Structures.LeftAction
open import Cubical.Structures.Group.Semidirect

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
      open GroupNotation₀ G₀
      open GroupNotation₁ G₁
      open GroupHom
      open MorphismLemmas
      open IsGroupAction
      open GroupLemmas

      ker-σ : Group {ℓℓ'}
      ker-σ = ker σ

      _+ₖ_ = ker-σ ._+_

      _α_ : LeftActionStructure ⟨ G₀ ⟩ ⟨ ker-σ ⟩
      _α_ g (h , p) = (ig +₁ h) +₁ (-₁ ig) , q
        where
          ig = ι .fun g
          s = σ .fun
          abstract
            q = s ((ig +₁ h) +₁ (-₁ ig))
                  ≡⟨ σ .isHom (ig +₁ h) (-₁ ig) ⟩
                (s (ig +₁ h)) +₀ s (-₁ ig)
                   ≡⟨ cong (s (ig +₁ h) +₀_) (mapInv σ ig) ⟩
                (s (ig +₁ h)) +₀ (-₀ (s ig))
                   ≡⟨ cong (_+₀ -₀ (s ig)) (σ .isHom ig h) ⟩
                ((s ig) +₀ (s h)) +₀ (-₀ (s ig))
                    ≡⟨ cong (λ z → ((s ig) +₀ z) +₀ (-₀ (s ig))) p ⟩
                ((s ig) +₀ 0₀) +₀ (-₀ (s ig))
                    ≡⟨ cong (_+₀ -₀ (s ig)) (rId₀ (s ig)) ⟩
                (s ig) +₀ (-₀ (s ig))
                   ≡⟨ rCancel₀ (s ig) ⟩
                0₀ ∎

      isAct : IsGroupAction G₀ ker-σ _α_
      abstract
        -- (g α (ker-σ Group.+ h) h') ≡ (ker-σ Group.+ (g α h)) (g α h')
        isAct .isHom g (h , p) (h' , p') = subtypeWitnessIrrelevance (sg-typeProp σ) q
          where
            ig = ι .fun g
            -ig = -₁ ig
            s = σ .fun
            abstract
              q = fst (g α ((h , p) +ₖ (h' , p')))
                      ≡⟨ refl ⟩
                  (ig +₁ (h +₁ h')) +₁ (-₁ ig)
                      ≡⟨ cong (λ z → (ig +₁ (z +₁ h')) +₁ (-₁ ig)) ((sym (rId₁ h)) ∙ (cong (h +₁_) (sym (lCancel₁ ig)))) ⟩
                  (ig +₁ ((h +₁ (-ig +₁ ig)) +₁ h')) +₁ -ig
                      ≡⟨ cong (λ z → (ig +₁ (z +₁ h')) +₁ -ig) (assoc₁ h -ig ig) ⟩
                  (ig +₁ (((h +₁ -ig) +₁ ig) +₁ h')) +₁ -ig
                      ≡⟨ cong (λ z → (ig +₁ z) +₁ -ig) (sym (assoc₁ (h +₁ -ig) ig h')) ⟩
                  (ig +₁ ((h +₁ -ig) +₁ (ig +₁ h'))) +₁ -ig
                      ≡⟨ cong (_+₁ -ig) (assoc₁ ig (h +₁ -ig) (ig +₁ h')) ⟩
                  ((ig +₁ (h +₁ -ig)) +₁ (ig +₁ h')) +₁ -ig
                      ≡⟨ cong (λ z → (z +₁ (ig +₁ h')) +₁ -ig) (assoc₁ ig h -ig) ⟩
                  (((ig +₁ h) +₁ -ig) +₁ (ig +₁ h')) +₁ -ig
                      ≡⟨ sym (assoc₁ ((ig +₁ h) +₁ -ig) (ig +₁ h') -ig) ⟩
                  ((ig +₁ h) +₁ -ig) +₁ ((ig +₁ h') +₁ -ig)
                      ≡⟨ refl ⟩
                  fst ((g α (h , p)) +ₖ (g α (h' , p'))) ∎
        isAct .identity (h , p) = subtypeWitnessIrrelevance (sg-typeProp σ) q
          where
            abstract
              q = fst (0₀ α (h , p))
                    ≡⟨ cong (λ z → (z +₁ h) +₁ (-₁ z)) (mapId ι) ⟩
                  (0₁ +₁ h) +₁ (-₁ 0₁)
                    ≡⟨ (cong ((0₁ +₁ h) +₁_) (invId G₁)) ∙∙ rId₁ (0₁ +₁ h) ∙∙ lId₁ h ⟩
                  h ∎
        -- (g +₀ g') α h ≡ g α (g' α h)
        isAct .assoc g g' (h , p) = subtypeWitnessIrrelevance (sg-typeProp σ) q
          where
            ig = ι .fun g
            ig' = ι .fun g'
            -ig = -₁ ig
            -ig' = -₁ ig'
            abstract
              q = (ι .fun (g +₀ g') +₁ h) +₁ (-₁ (ι .fun (g +₀ g')))
                     ≡⟨ cong (λ z → (z +₁ h) +₁ (-₁ z)) (ι .isHom g g') ⟩
                  ((ig +₁ ig') +₁ h) +₁ (-₁ (ig +₁ ig'))
                     ≡⟨ cong (((ig +₁ ig') +₁ h) +₁_) (invDistr G₁ ig ig') ⟩
                  ((ig +₁ ig') +₁ h) +₁ (-ig' +₁ -ig)
                    ≡⟨ cong (_+₁ (-ig' +₁ -ig)) (sym (assoc₁ ig ig' h)) ⟩
                  (ig +₁ (ig' +₁ h)) +₁ (-ig' +₁ -ig)
                    ≡⟨ assoc₁ (ig +₁ (ig' +₁ h)) -ig' -ig ⟩
                  ((ig +₁ (ig' +₁ h)) +₁ -ig') +₁ -ig
                    ≡⟨ cong (_+₁ -ig) (sym (assoc₁ ig (ig' +₁ h) -ig')) ⟩
                  fst (g α (g' α (h , p))) ∎

  GroupAct→SplitExt : GroupAct → SplitExt
  GroupAct→SplitExt (G₁ , _α_ , isAct) = G₁⋊G₀ , ι₂ α , π₂ α , π₂-hasSec α
    where
      α = groupaction _α_ isAct
      G₁⋊G₀ : Group {ℓℓ'}
      G₁⋊G₀ = G₁ ⋊⟨ α ⟩ G₀

module _ (ℓ ℓ' : Level) where
  private
    ℓℓ' = ℓ-max ℓ ℓ'

  ReflexiveGraph = Σ[ (G₀ , G₁ , ι , σ , split-σ) ∈ (Σ[ G₀ ∈ Group {ℓ} ] SplitExt G₀ ℓ') ] Σ[ τ ∈ GroupHom G₁ G₀ ] isGroupHomRet ι τ

  PreCrossedModule = Σ[ (G₀ , G₁ , _α_ , isAct) ∈ (Σ[ G₀ ∈ Group {ℓ} ] GroupAct G₀ ℓ') ] (Σ[ φ ∈ GroupHom G₁ G₀ ] isEquivariant _α_ φ)



-- Older Experiments --

{-
-- needs --guardedness flag

module _ where
  open import Cubical.Data.Maybe
  record Hierarchy {A : Type ℓ} (𝒮-A : URGStr A ℓ) : Type (ℓ-suc ℓ) where
    coinductive
    field
      B : A → Type ℓ
      𝒮ᴰ-B : URGStrᴰ 𝒮-A B ℓ
      ℋ : Maybe (Hierarchy {A = Σ A B} (∫⟨ 𝒮-A ⟩ 𝒮ᴰ-B))
-}
