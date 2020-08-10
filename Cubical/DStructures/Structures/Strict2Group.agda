{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Structures.Strict2Group where

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
open import Cubical.DStructures.Meta.Properties
open import Cubical.DStructures.Structures.Constant
open import Cubical.DStructures.Meta.Combine
open import Cubical.DStructures.Structures.Type
open import Cubical.DStructures.Structures.Group

module _ {ℓ ℓ' : Level} where
  private
    ℓℓ' = ℓ-max ℓ ℓ'

  module VertCompNotation (𝒢 : ReflGraph ℓ ℓ') where
      G₁ = snd (fst (fst (fst (fst 𝒢))))
      G₀ = fst (fst (fst (fst (fst 𝒢))))
      σ = snd (snd (fst (fst (fst 𝒢))))
      τ = snd (fst 𝒢)
      ι = fst (snd (fst (fst (fst 𝒢))))
      s = GroupHom.fun σ
      t = GroupHom.fun τ
      𝒾 = GroupHom.fun ι
      split-τ = snd 𝒢
      split-σ = snd (fst (fst 𝒢))

      σι-≡-fun = λ (g : ⟨ G₀ ⟩) → funExt⁻ (cong GroupHom.fun split-σ) g
      τι-≡-fun = λ (g : ⟨ G₀ ⟩) → funExt⁻ (cong GroupHom.fun split-τ) g

      open GroupNotation₁ G₁ public
      open GroupNotation₀ G₀ public
      open GroupHom public

      isComposable : (g f : ⟨ G₁ ⟩) → Type ℓ
      isComposable g f = s g ≡ t f

      +-c : (g f : ⟨ G₁ ⟩) (c : isComposable g f)
            (g' f' : ⟨ G₁ ⟩) (c' : isComposable g' f')
            → isComposable (g +₁ g') (f +₁ f')
      +-c g f c g' f' c' = σ .isHom g g'
                           ∙∙ cong (_+₀ s g') c
                           ∙∙ cong (t f +₀_) c'
                           ∙ sym (τ .isHom f f')


  -- type of composition operations on the reflexive graph 𝒢
  record VertComp (𝒢 : ReflGraph ℓ ℓ') : Type ℓℓ' where
    no-eta-equality
    constructor vertcomp
    open VertCompNotation 𝒢

    field
      ∘ : (g f : ⟨ G₁ ⟩) → (isComposable g f) → ⟨ G₁ ⟩

    syntax ∘ g f p = g ∘⟨ p ⟩ f

    field
      σ-∘ : (g f : ⟨ G₁ ⟩) (c : isComposable g f) → s (g ∘⟨ c ⟩ f) ≡ s f
      τ-∘ : (g f : ⟨ G₁ ⟩) (c : isComposable g f) → t (g ∘⟨ c ⟩ f) ≡ t g
      isHom-∘ : (g f : ⟨ G₁ ⟩) (c : isComposable g f)
                (g' f' : ⟨ G₁ ⟩) (c' : isComposable g' f')
                → (g +₁ g') ∘⟨ +-c g f c g' f' c' ⟩ (f +₁ f') ≡ (g ∘⟨ c ⟩ f) +₁ (g' ∘⟨ c' ⟩ f')
      assoc-∘ : (h g f : ⟨ G₁ ⟩) (c : isComposable h g) (c' : isComposable g f)
                → h ∘⟨ c ∙ sym (τ-∘ g f c') ⟩ (g ∘⟨ c' ⟩ f) ≡ (h ∘⟨ c ⟩ g) ∘⟨ σ-∘ h g c ∙ c' ⟩ f
      lid-∘ : (f : ⟨ G₁ ⟩) → 𝒾 (t f) ∘⟨ σι-≡-fun (t f) ⟩ f ≡ f
      rid-∘ : (g : ⟨ G₁ ⟩) → g ∘⟨ sym (τι-≡-fun (s g)) ⟩ 𝒾 (s g) ≡ g


  module _ (𝒢 : ReflGraph ℓ ℓ') where

    -- open VertCompNotation 𝒢
    -- open VertComp

    -- VertComp-≡ :
    -- VertComp-≡ = ?

    abstract
      isPropVertComp : isProp (VertComp 𝒢)
      isPropVertComp 𝒞 𝒞' = {!!}

  𝒮ᴰ-Strict2Group : URGStrᴰ (𝒮-ReflGraph ℓ ℓ')
                            VertComp
                            ℓ-zero
  𝒮ᴰ-Strict2Group = Subtype→Sub-𝒮ᴰ (λ 𝒢 → VertComp 𝒢 , isPropVertComp 𝒢)
                                   (𝒮-ReflGraph ℓ ℓ')

  Strict2Group : Type (ℓ-suc ℓℓ')
  Strict2Group = Σ[ 𝒢 ∈ ReflGraph ℓ ℓ' ] VertComp 𝒢
