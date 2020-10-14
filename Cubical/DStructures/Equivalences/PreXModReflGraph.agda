
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


open import Cubical.Structures.Subtype
open import Cubical.Algebra.Group
open import Cubical.Structures.LeftAction
open import Cubical.Algebra.Group.Semidirect

open import Cubical.DStructures.Base
open import Cubical.DStructures.Meta.Properties

open import Cubical.DStructures.Meta.Isomorphism
open import Cubical.DStructures.Structures.Constant
open import Cubical.DStructures.Structures.Type
open import Cubical.DStructures.Structures.Group
open import Cubical.DStructures.Structures.SplitEpi
open import Cubical.DStructures.Structures.ReflGraph
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

    F = Iso.fun (IsoActionSplitEpi ℓ ℓℓ')

  -- reassociate: Display B + isSplitEpi over SplitEpi
  ReflGraph' = Σ[ (((G₀ , G₁) , (ι , σ)) , split-σ) ∈ SplitEpi ℓ ℓℓ' ] Σ[ τ ∈ GroupHom G₁ G₀ ] isGroupSplitEpi ι τ

  𝒮ᴰ-ReflGraph' : URGStrᴰ (𝒮-SplitEpi ℓ ℓℓ')
                          (λ (((G₀ , G₁) , (ι , σ)) , split-σ) → Σ[ τ ∈ GroupHom G₁ G₀ ] isGroupSplitEpi ι τ)
                          ℓℓ'
  𝒮ᴰ-ReflGraph' = splitTotal-𝒮ᴰ (𝒮-SplitEpi ℓ ℓℓ') (𝒮ᴰ-G²FBSplit\B ℓ ℓℓ') (𝒮ᴰ-ReflGraph ℓ ℓℓ')

  -- reassociate: Display B + isEquivar over Action
  PreXModule' = Σ[ (((G₀ , H) , _α_) , isAct) ∈ Action ℓ ℓℓ' ] Σ[ φ ∈ GroupHom H G₀ ] (isEquivariant (((G₀ , H) , _α_) , isAct) φ)

  𝒮ᴰ-PreXModule' : URGStrᴰ (𝒮-Action ℓ ℓℓ')
                           (λ (((G₀ , H) , _α_) , isAct) → Σ[ φ ∈ GroupHom H G₀ ] (isEquivariant (((G₀ , H) , _α_) , isAct) φ))
                           ℓℓ'
  𝒮ᴰ-PreXModule' = splitTotal-𝒮ᴰ (𝒮-Action ℓ ℓℓ') (𝒮ᴰ-Action\PreXModuleStr ℓ ℓℓ') (𝒮ᴰ-PreXModule ℓ ℓℓ')

  -- Establish ♭-relational isomorphism of precrossed modules and reflexive graphs
  -- over the isomorphism of actions and split epis
  𝒮ᴰ-♭PIso-PreXModule'-ReflGraph' : 𝒮ᴰ-♭PIso F 𝒮ᴰ-PreXModule' 𝒮ᴰ-ReflGraph'
  RelIso.fun (𝒮ᴰ-♭PIso-PreXModule'-ReflGraph' (((G₀ , H) , _α_) , isAct)) (φ , isEqui) .fst = τ
    where
      -- notation
      open GroupNotation₀ G₀
      open GroupNotationᴴ H
      f = GroupHom.fun φ
      A = groupaction _α_ isAct
      H⋊G₀ : Group {ℓ-max ℓ ℓ'}
      H⋊G₀ = H ⋊⟨ A ⟩ G₀

      -- define the morphism τ
      τ : GroupHom H⋊G₀ G₀
      τ .fun (h , g) = f h +₀ g
      τ .isHom (h , g) (h' , g') = q
        where
          abstract
            q = f (h +ᴴ (g α h')) +₀ (g +₀ g')
                  ≡⟨ cong (_+₀ (g +₀ g')) (φ .isHom h (g α h')) ⟩
                (f h +₀ f (g α h')) +₀ (g +₀ g')
                  ≡⟨ cong (λ z → (f h +₀ z) +₀ (g +₀ g')) (isEqui g h') ⟩
                (f h +₀ ((g +₀ (f h')) -₀ g)) +₀ (g +₀ g')
                  ≡⟨ cong (λ z → (f h +₀ z) +₀ (g +₀ g') ) (sym (assoc₀ g (f h') (-₀ g))) ⟩
                (f h +₀ (g +₀ (f h' +₀ (-₀ g)))) +₀ (g +₀ g')
                  ≡⟨ cong (_+₀ (g +₀ g')) (assoc₀ (f h) g (f h' +₀ (-₀ g))) ⟩
                ((f h +₀ g) +₀ (f h' +₀ (-₀ g))) +₀ (g +₀ g')
                  ≡⟨ sym (assoc₀ (f h +₀ g) (f h' +₀ (-₀ g)) (g +₀ g')) ⟩
                (f h +₀ g) +₀ ((f h' +₀ (-₀ g)) +₀ (g +₀ g'))
                  ≡⟨ cong ((f h +₀ g) +₀_)
                          (sym (assoc₀ (f h') (-₀ g) (g +₀ g'))
                          ∙ (cong (f h' +₀_)
                                  (assoc₀ (-₀ g) g g'
                                  ∙∙ cong (_+₀ g') (lCancel₀ g)
                                  ∙∙ lId₀ g')))⟩
                (f h +₀ g) +₀ (f  h' +₀ g') ∎

  RelIso.fun (𝒮ᴰ-♭PIso-PreXModule'-ReflGraph' (((G₀ , H) , _α_) , isAct)) (φ , isEqui) .snd = q
    where
      -- notation
      open GroupNotation₀ G₀
      open GroupNotationᴴ H
      f = GroupHom.fun φ
      τ = RelIso.fun (𝒮ᴰ-♭PIso-PreXModule'-ReflGraph' (((G₀ , H) , _α_) , isAct)) (φ , isEqui) .fst
      ι = Iso.fun (IsoActionSplitEpi ℓ ℓℓ') (((G₀ , H) , _α_) , isAct) .fst .snd .fst

      -- prove that τ as constructed above is split
      abstract
        q : isGroupSplitEpi ι τ
        q = GroupMorphismExt λ g → f 0ᴴ +₀ g
                                             ≡⟨ cong (_+₀ g) (mapId φ) ⟩
                                           0₀ +₀ g
                                             ≡⟨ lId₀ g ⟩
                                           g ∎

  -- end of RelIso.fun (𝒮ᴰ-♭PIso-PreXModule'-ReflGraph' (((G₀ , H) , _α_) , isAct)) (φ , isEqui)


  RelIso.inv (𝒮ᴰ-♭PIso-PreXModule'-ReflGraph' (((G₀ , H) , _α_) , isAct)) (τ , split-τ) = φ , isEqui
    where
      -- notation
      ℬ = F (((G₀ , H) , _α_) , isAct)
      A = groupaction _α_ isAct

      -- σ = snd (snd (fst ℬ))
      -- φ should be τ| ker σ
      -- but ker σ ≅ H so we "restrict" τ to that
      -- by precomposing with the inclusion H → H⋊G₀
      ι1 = ι₁ A
      𝒾 = ι1 .fun

      t = τ .fun

      H⋊G₀ = H ⋊⟨ A ⟩ G₀
      _+α_ =  Group._+_ H⋊G₀

      open GroupNotationᴴ H
      open GroupNotation₀ G₀

      -- define φ
      φ : GroupHom H G₀
      φ = compGroupHom ι1 τ
      f = φ .fun

      -- prove equivariance
      abstract
        isEqui : isEquivariant (((G₀ , H) , _α_) , isAct) φ
        isEqui g h = f (g α h)
                       ≡⟨ refl ⟩
                     t (g α h , 0₀)
                       ≡⟨ cong t
                               (g α h , 0₀
                                 ≡⟨ ΣPathP (sym ((cong (_+ᴴ ((g +₀ 0₀) α 0ᴴ)) (lIdᴴ (g α h)))
                                                ∙∙ cong ((g α h) +ᴴ_) (actOnUnit A (g +₀ 0₀))
                                                ∙∙ rIdᴴ (g α h))
                                           , sym (cong (_+₀ (-₀ g)) (rId₀ g) ∙ rCancel₀ g)) ⟩
                               (0ᴴ +ᴴ (g α h)) +ᴴ ((g +₀ 0₀) α 0ᴴ) , (g +₀ 0₀) -₀ g
                                 ≡⟨ refl ⟩
                               ((0ᴴ , g) +α (h , 0₀)) +α (0ᴴ , -₀ g) ∎) ⟩
                     t (((0ᴴ , g) +α (h , 0₀)) +α (0ᴴ , -₀ g))
                       ≡⟨ hom-homl τ (0ᴴ , g) (h , 0₀) (0ᴴ , -₀ g) ⟩
                     ((t (0ᴴ , g)) +₀ t (h , 0₀)) +₀ t (0ᴴ , -₀ g)
                       ≡⟨ cong (((t (0ᴴ , g)) +₀ t (h , 0₀)) +₀_) (funExt⁻ (cong fun split-τ) (-₀ g)) ⟩
                     ((t (0ᴴ , g)) +₀ t (h , 0₀)) -₀ g
                       ≡⟨ cong (λ z → (z +₀ t (h , 0₀)) -₀ g) (funExt⁻ (cong fun split-τ) g) ⟩
                     (g +₀ f h) -₀ g ∎

  -- RelIso.inv (𝒮ᴰ-♭PIso-PreXModule'-ReflGraph' (((G₀ , H) , _α_) , isAct)) (τ , split-τ)

  RelIso.leftInv (𝒮ᴰ-♭PIso-PreXModule'-ReflGraph' (((G₀ , H) , _α_) , isAct)) (φ , isEqui) .fst = φ-≅
    where
      open GroupNotation₀ G₀

      abstract
        -- φ ≅ inv (fun φ) ≡ τ ∘ ι₁
        φ-≅ : (h : ⟨ H ⟩) → φ .fun h +₀ 0₀ ≡ φ .fun h
        φ-≅ h = rId₀ (φ .fun h)

  RelIso.leftInv (𝒮ᴰ-♭PIso-PreXModule'-ReflGraph' (((G₀ , H) , _α_) , isAct)) (φ , isEqui) .snd = isEqui-≅
    where
      abstract
        isEqui-≅ : Unit
        isEqui-≅ = tt

  -- end of RelIso.leftInv (𝒮ᴰ-♭PIso-PreXModule'-ReflGraph' (((G₀ , H) , _α_) , isAct)) (φ , isEqui)

  RelIso.rightInv (𝒮ᴰ-♭PIso-PreXModule'-ReflGraph' (((G₀ , H) , _α_) , isAct)) (τ , split-τ) .fst = τ-≅
    where
      A = groupaction _α_ isAct
      H⋊G₀ = H ⋊⟨ A ⟩ G₀
      t = τ .fun
      open GroupNotation₀ G₀
      open GroupNotationᴴ H

      abstract
        τ-≅ : ((h , g) : ⟨ H⋊G₀ ⟩) → t (h , 0₀) +₀ g ≡ t (h , g)
        τ-≅ (h , g) = t (h , 0₀) +₀ g
                        ≡⟨ cong (t (h , 0₀) +₀_) (sym (funExt⁻ (cong GroupHom.fun split-τ) g)) ⟩
                      t (h , 0₀) +₀ t (0ᴴ , g)
                        ≡⟨ sym (τ .isHom (h , 0₀) (0ᴴ , g)) ⟩
                      t (h +ᴴ (0₀ α 0ᴴ) , 0₀ +₀ g)
                        ≡⟨ cong t (ΣPathP (cong (h +ᴴ_) (actOnUnit A 0₀) ∙ rIdᴴ h , lId₀ g)) ⟩
                      t (h , g) ∎

  RelIso.rightInv (𝒮ᴰ-♭PIso-PreXModule'-ReflGraph' (((G₀ , H) , _α_) , isAct)) (τ , split-τ) .snd = split-τ-≅
    where
      abstract
        split-τ-≅ : Unit
        split-τ-≅ = tt

  -- end of RelIso.rightInv (𝒮ᴰ-♭PIso-PreXModule'-ReflGraph' (((G₀ , H) , _α_) , isAct)) (τ , split-τ)

  -- end of 𝒮ᴰ-♭PIso-PreXModule'-ReflGraph' : 𝒮ᴰ-♭PIso F 𝒮ᴰ-PreXModule' 𝒮ᴰ-ReflGraph'

  -- turn the ♭-relational isomorphism into a (normal) iso
  Iso-PreXModule-ReflGraph' : Iso PreXModule' ReflGraph'
  Iso-PreXModule-ReflGraph' = 𝒮ᴰ-♭PIso-Over→TotalIso (IsoActionSplitEpi ℓ ℓℓ') 𝒮ᴰ-PreXModule' 𝒮ᴰ-ReflGraph' 𝒮ᴰ-♭PIso-PreXModule'-ReflGraph'

  -- reassociate on both sides
  Iso-PreXModule-ReflGraph : Iso (PreXModule ℓ ℓℓ') (ReflGraph ℓ ℓℓ')
  Iso-PreXModule-ReflGraph = compIso (compIso Σ-assoc-Iso
                                            Iso-PreXModule-ReflGraph')
                                   (invIso Σ-assoc-Iso)
