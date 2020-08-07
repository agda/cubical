
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Equivalences.PreXModReflGraph where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Functions.FunExtEquiv

open import Cubical.Homotopy.Base

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Relation.Binary
open BinaryRelation

open import Cubical.Structures.Subtype
open import Cubical.Structures.Group
open import Cubical.Structures.LeftAction
open import Cubical.Structures.Group.Semidirect

open import Cubical.DStructures.Base
open import Cubical.DStructures.Meta.Properties
open import Cubical.DStructures.Meta.Combine
open import Cubical.DStructures.Meta.Isomorphism
open import Cubical.DStructures.Structures.Constant
open import Cubical.DStructures.Structures.Type
open import Cubical.DStructures.Structures.Group
open import Cubical.DStructures.Structures.Action
open import Cubical.DStructures.Structures.XModule
open import Cubical.DStructures.Equivalences.GroupSplitEpiAction


private
  variable
    ℓ ℓ' ℓ'' ℓ₁ ℓ₁' ℓ₁'' ℓ₂ ℓA ℓA' ℓ≅A ℓ≅A' ℓB ℓB' ℓ≅B ℓC ℓ≅C ℓ≅ᴰ ℓ≅ᴰ' ℓ≅B' : Level

open Kernel
open GroupHom -- such .fun!
open GroupLemmas
open MorphismLemmas
open ActionLemmas

module _ (ℓ ℓ' : Level) where
  private
    ℓℓ' = ℓ-max ℓ ℓ'

    ℱ : Iso (Action ℓ ℓℓ') (SplitEpi ℓ ℓℓ')
    ℱ = IsoActionSplitEpi ℓ ℓℓ'
    F = Iso.fun ℱ

  -- reassociate
  𝒮ᴰ-ReflGraph' : URGStrᴰ (𝒮-SplitEpi ℓ ℓℓ')
                         (λ (((G₀ , G₁) , (ι , σ)) , split-σ) → Σ[ τ ∈ GroupHom G₁ G₀ ] isGroupSplitEpi ι τ)
                         ℓℓ'
  𝒮ᴰ-ReflGraph' = splitTotal-𝒮ᴰ (𝒮-SplitEpi ℓ ℓℓ') (𝒮ᴰ-G²FBSplit\B ℓ ℓℓ') (𝒮ᴰ-ReflGraph ℓ ℓℓ')

  𝒮ᴰ-PreXModule' : URGStrᴰ (𝒮-Action ℓ ℓℓ')
                       (λ (((G₀ , G₁) , _α_) , isAct) → Σ[ φ ∈ GroupHom G₁ G₀ ] (isEquivariant _α_ φ))
                       ℓℓ'
  𝒮ᴰ-PreXModule' = splitTotal-𝒮ᴰ (𝒮-Action ℓ ℓℓ') (𝒮ᴰ-Action\PreXModuleStr ℓ ℓℓ') (𝒮ᴰ-PreXModule ℓ ℓℓ')

  𝒢 : 𝒮ᴰ-♭iso F 𝒮ᴰ-PreXModule' 𝒮ᴰ-ReflGraph'
  RelIso.fun (𝒢 (((G₀ , G₁) , _α_) , isAct)) (φ , isEqui) .fst = τ
    where
      open GroupNotation₀ G₀
      open GroupNotation₁ G₁
      𝒻 = GroupHom.fun φ
      τ = grouphom (λ (h , g) → GroupHom.fun φ h +₀ g) q
          where
            abstract
              q = λ (h , g) (h' , g') → 𝒻 (h +₁ (g α h')) +₀ (g +₀ g')
                                          ≡⟨ cong (_+₀ (g +₀ g')) (φ .isHom h (g α h')) ⟩
                                        (𝒻 h +₀ 𝒻 (g α h')) +₀ (g +₀ g')
                                          ≡⟨ cong (λ z → (𝒻 h +₀ z) +₀ (g +₀ g')) (isEqui g h') ⟩
                                        (𝒻 h +₀ ((g +₀ (𝒻 h')) +₀ (-₀ g))) +₀ (g +₀ g')
                                          ≡⟨ cong (λ z → (𝒻 h +₀ z) +₀ (g +₀ g') ) (sym (assoc₀ g (𝒻 h') (-₀ g))) ⟩
                                        (𝒻 h +₀ (g +₀ (𝒻 h' +₀ (-₀ g)))) +₀ (g +₀ g')
                                          ≡⟨ cong (_+₀ (g +₀ g')) (assoc₀ (𝒻 h) g (𝒻 h' +₀ (-₀ g))) ⟩
                                        ((𝒻 h +₀ g) +₀ (𝒻 h' +₀ (-₀ g))) +₀ (g +₀ g')
                                          ≡⟨ sym (assoc₀ (𝒻 h +₀ g) (𝒻 h' +₀ (-₀ g)) (g +₀ g')) ⟩
                                        (𝒻 h +₀ g) +₀ ((𝒻 h' +₀ (-₀ g)) +₀ (g +₀ g'))
                                          ≡⟨ cong ((𝒻 h +₀ g) +₀_)
                                                  (sym (assoc₀ (𝒻 h') (-₀ g) (g +₀ g'))
                                                  ∙ (cong (𝒻 h' +₀_)
                                                          (assoc₀ (-₀ g) g g'
                                                          ∙∙ cong (_+₀ g') (lCancel₀ g)
                                                          ∙∙ lId₀ g')))⟩
                                        (𝒻 h +₀ g) +₀ (𝒻  h' +₀ g') ∎

  RelIso.fun (𝒢 (((G₀ , G₁) , _α_) , isAct)) (φ , isEqui) .snd = q
    where
      open GroupNotation₀ G₀
      open GroupNotation₁ G₁
      𝒻 = GroupHom.fun φ
      abstract
        q = GroupMorphismExt λ g → 𝒻 0₁ +₀ g
                                             ≡⟨ cong (_+₀ g) (mapId φ) ⟩
                                           0₀ +₀ g
                                             ≡⟨ lId₀ g ⟩
                                           g ∎
  RelIso.inv (𝒢 (((G₀ , G₁) , _α_) , isAct)) (τ , split-τ) = φ , isEqui
    where
      ℬ = F (((G₀ , G₁) , _α_) , isAct)
      A = groupaction _α_ isAct

      -- σ = snd (snd (fst ℬ))
      -- φ should be τ| ker σ
      -- but ker σ ≅ G₁ so we "restrict" τ to that
      -- by precomposing with the inclusion G₁ → G₁⋊G₀
      ι1 = ι₁ A

      φ : GroupHom G₁ G₀
      φ = compGroupHom ι1 τ

      abstract
        isEqui : isEquivariant _α_ φ
        isEqui g h = 𝒻 (g α h)
                       ≡⟨ refl ⟩
                     t (g α h , 0₀)
                       ≡⟨ cong t
                               (g α h , 0₀
                                 ≡⟨ ΣPathP (sym ((cong (_+₁ ((g +₀ 0₀) α 0₁)) (lId₁ (g α h)))
                                                ∙∙ cong ((g α h) +₁_) (actOnUnit A (g +₀ 0₀))
                                                ∙∙ rId₁ (g α h))
                                           , sym (cong (_+₀ (-₀ g)) (rId₀ g) ∙ rCancel₀ g)) ⟩
                               (0₁ +₁ (g α h)) +₁ ((g +₀ 0₀) α 0₁) , (g +₀ 0₀) +₀ (-₀ g)
                                 ≡⟨ refl ⟩
                               ((0₁ , g) +α (h , 0₀)) +α (0₁ , -₀ g) ∎) ⟩
                     t (((0₁ , g) +α (h , 0₀)) +α (0₁ , -₀ g))
                       ≡⟨ hom-homl τ (0₁ , g) (h , 0₀) (0₁ , -₀ g) ⟩
                     ((t (0₁ , g)) +₀ t (h , 0₀)) +₀ t (0₁ , -₀ g)
                       ≡⟨ cong (((t (0₁ , g)) +₀ t (h , 0₀)) +₀_) (funExt⁻ (cong fun split-τ) (-₀ g)) ⟩
                     ((t (0₁ , g)) +₀ t (h , 0₀)) +₀ (-₀ g)
                       ≡⟨ cong (λ z → (z +₀ t (h , 0₀)) +₀ (-₀ g)) (funExt⁻ (cong fun split-τ) g) ⟩
                     (g +₀ 𝒻 h) +₀ (-₀ g) ∎
          where
            𝒾 = ι1 .fun
            𝒻 = φ .fun
            t = τ .fun
            G₁⋊G₀ = G₁ ⋊⟨ A ⟩ G₀
            _+α_ =  Group._+_ G₁⋊G₀

            open GroupNotation₁ G₁
            open GroupNotation₀ G₀


  RelIso.leftInv (𝒢 (((G₀ , G₁) , _α_) , isAct)) (φ , isEqui) .fst = φ-≅
    where
      open GroupNotation₀ G₀

      abstract
        -- φ ≅ inv (fun φ) ≡ τ ∘ ι₁
        φ-≅ : (h : ⟨ G₁ ⟩) → φ .fun h +₀ 0₀ ≡ φ .fun h
        φ-≅ h = rId₀ (φ .fun h)

  RelIso.leftInv (𝒢 (((G₀ , G₁) , _α_) , isAct)) (φ , isEqui) .snd = isEqui-≅
    where
      abstract
        isEqui-≅ : Unit
        isEqui-≅ = tt

  RelIso.rightInv (𝒢 (((G₀ , G₁) , _α_) , isAct)) (τ , split-τ) .fst = τ-≅
    where
      A = groupaction _α_ isAct
      G₁⋊G₀ = G₁ ⋊⟨ A ⟩ G₀
      t = τ .fun
      open GroupNotation₀ G₀
      open GroupNotation₁ G₁

      abstract
        τ-≅ : ((h , g) : ⟨ G₁⋊G₀ ⟩) → t (h , 0₀) +₀ g ≡ t (h , g)
        τ-≅ (h , g) = t (h , 0₀) +₀ g
                        ≡⟨ cong (t (h , 0₀) +₀_) (sym (funExt⁻ (cong GroupHom.fun split-τ) g)) ⟩
                      t (h , 0₀) +₀ t (0₁ , g)
                        ≡⟨ sym (τ .isHom (h , 0₀) (0₁ , g)) ⟩
                      t (h +₁ (0₀ α 0₁) , 0₀ +₀ g)
                        ≡⟨ cong t (ΣPathP (cong (h +₁_) (actOnUnit A 0₀) ∙ rId₁ h , lId₀ g)) ⟩
                      t (h , g) ∎

  RelIso.rightInv (𝒢 (((G₀ , G₁) , _α_) , isAct)) (τ , split-τ) .snd = split-τ-≅
    where
      abstract
        split-τ-≅ : Unit
        split-τ-≅ = tt

  -- IsoPreXModuleReflGraph : Iso (PreXModule' ℓ ℓℓ') (ReflGraph' ℓ ℓℓ')
  -- IsoPreXModuleReflGraph = Iso→TotalIso {!!} {!!} {!!} {!!}








-- old stuff

{-
  module _ (((((G₀ , G₁) , (ι , σ)) , split-σ) , τ , split-τ) : ReflGraph) where
    𝒜 : Act
    𝒜 = RelIso.inv ℱ-RelIso (((G₀ , G₁) , (ι , σ)) , split-σ)
    _α_ =  snd (fst 𝒜)

    get-φ : GroupHom (snd (fst (fst 𝒜))) G₀
    get-φ = restrictToKer σ τ

    abstract
      get-isEquivariant : isEquivariant _α_ get-φ
      get-isEquivariant g (h , p) = 𝓉 ((𝒾 g +₁ h) +₁ (-₁ (𝒾 g)))
                                      ≡⟨ τ .isHom (𝒾 g +₁ h) (-₁ (𝒾 g)) ⟩
                                    𝓉 (𝒾 g +₁ h) +₀ (𝓉 (-₁ (𝒾 g)))
                                      ≡⟨ cong (_+₀ 𝓉 (-₁ (𝒾 g))) (τ .isHom (𝒾 g) h) ⟩
                                    (𝓉 (𝒾 g) +₀ 𝓉 h) +₀ 𝓉 (-₁ (𝒾 g))
                                      ≡⟨ cong ((𝓉 (𝒾 g) +₀ 𝓉 h) +₀_) (mapInv τ (𝒾 g)) ⟩
                                    (𝓉 (𝒾 g) +₀ 𝓉 h) +₀ (-₀ (𝓉 (𝒾 g)))
                                      ≡⟨ cong (λ z → (z +₀ 𝓉 h) +₀ (-₀ z)) (funExt⁻ (cong fun split-τ) g) ⟩
                                    (g +₀ (𝓉 h)) +₀ (-₀ g) ∎
        where
          𝒾 = ι .fun
          𝓉 = τ .fun
          open GroupNotation₁ G₁
          open GroupNotation₀ G₀
          open MorphismLemmas


  module _ (((((G₀ , G₁) , _α_) , isAct) , φ , isEqui) : PreXMod) where
    ℬ : SplitEpi
    ℬ = RelIso.fun ℱ-RelIso (((G₀ , G₁) , _α_) , isAct)

    open GroupNotation₀ G₀
    open GroupNotation₁ G₁
    open MorphismLemmas
    𝒻 = GroupHom.fun φ

    get-τ : GroupHom (snd (fst (fst ℬ))) G₀
    GroupHom.fun get-τ (h , g) = GroupHom.fun φ h +₀ g
    GroupHom.isHom get-τ (h , g) (h' , g') = q
      where
        abstract
          q = 𝒻 (h +₁ (g α h')) +₀ (g +₀ g')
                ≡⟨ cong (_+₀ (g +₀ g')) (φ .isHom h (g α h')) ⟩
              (𝒻 h +₀ 𝒻 (g α h')) +₀ (g +₀ g')
                ≡⟨ cong (λ z → (𝒻 h +₀ z) +₀ (g +₀ g')) (isEqui g h') ⟩
              (𝒻 h +₀ ((g +₀ (𝒻 h')) +₀ (-₀ g))) +₀ (g +₀ g')
                ≡⟨ cong (λ z → (𝒻 h +₀ z) +₀ (g +₀ g') ) (sym (assoc₀ g (𝒻 h') (-₀ g))) ⟩
              (𝒻 h +₀ (g +₀ (𝒻 h' +₀ (-₀ g)))) +₀ (g +₀ g')
                ≡⟨ cong (_+₀ (g +₀ g')) (assoc₀ (𝒻 h) g (𝒻 h' +₀ (-₀ g))) ⟩
              ((𝒻 h +₀ g) +₀ (𝒻 h' +₀ (-₀ g))) +₀ (g +₀ g')
                ≡⟨ sym (assoc₀ (𝒻 h +₀ g) (𝒻 h' +₀ (-₀ g)) (g +₀ g')) ⟩
              (𝒻 h +₀ g) +₀ ((𝒻 h' +₀ (-₀ g)) +₀ (g +₀ g'))
                ≡⟨ cong ((𝒻 h +₀ g) +₀_)
                        (sym (assoc₀ (𝒻 h') (-₀ g) (g +₀ g'))
                        ∙ (cong (𝒻 h' +₀_)
                          (assoc₀ (-₀ g) g g'
                          ∙∙ cong (_+₀ g') (lCancel₀ g)
                          ∙∙ lId₀ g')))⟩
              (𝒻 h +₀ g) +₀ (𝒻  h' +₀ g') ∎


    abstract
      get-split-τ : isGroupSplitEpi (fst (snd (fst ℬ))) get-τ
      get-split-τ = GroupMorphismExt λ g → 𝒻 0₁ +₀ g
                                             ≡⟨ cong (_+₀ g) (mapId φ) ⟩
                                           0₀ +₀ g
                                             ≡⟨ lId₀ g ⟩
                                           g ∎


-}
