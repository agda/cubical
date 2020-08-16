{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Structures.ReflGraph where

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

open GroupLemmas
open MorphismLemmas

private
  variable
    ℓ ℓ' : Level


module ReflGraphNotation (𝒢 : ReflGraph ℓ ℓ') where
    G₁ = snd (fst (fst (fst (fst 𝒢))))
    G₀ = fst (fst (fst (fst (fst 𝒢))))
    σ = snd (snd (fst (fst (fst 𝒢))))
    τ = snd (fst 𝒢)
    ι = fst (snd (fst (fst (fst 𝒢))))
    s = GroupHom.fun σ
    t = GroupHom.fun τ
    𝒾 = GroupHom.fun ι
    𝒾s = λ (g : ⟨ G₁ ⟩) → 𝒾 (s g)
    𝒾t = λ (g : ⟨ G₁ ⟩) → 𝒾 (t g)
    ι∘σ : GroupHom G₁ G₁
    ι∘σ = compGroupHom σ ι
    split-τ = snd 𝒢
    split-σ = snd (fst (fst 𝒢))

    σι-≡-fun = λ (g : ⟨ G₀ ⟩) → funExt⁻ (cong GroupHom.fun split-σ) g
    τι-≡-fun = λ (g : ⟨ G₀ ⟩) → funExt⁻ (cong GroupHom.fun split-τ) g

    open GroupNotation₁ G₁ public
    open GroupNotation₀ G₀ public
    open GroupHom public

    isComposable : (g f : ⟨ G₁ ⟩) → Type ℓ
    isComposable g f = s g ≡ t f

    isPropIsComposable : (g f : ⟨ G₁ ⟩) → isProp (isComposable g f)
    isPropIsComposable g f c c' = set₀ (s g) (t f) c c'

    -- lemmas
    abstract
      σ-g--isg : (g : ⟨ G₁ ⟩) → s (g -₁ 𝒾s g) ≡ 0₀
      σ-g--isg g = s (g -₁ 𝒾s g)
                    ≡⟨ σ .isHom g (-₁ 𝒾s g) ⟩
                  s g +₀ s (-₁ 𝒾s g)
                    ≡⟨ cong (s g +₀_)
                            (mapInv σ (𝒾s g)) ⟩
                  s g -₀ s (𝒾s g)
                    ≡⟨ cong (λ z → s g -₀ z)
                            (σι-≡-fun (s g)) ⟩
                  s g -₀ s g
                    ≡⟨ rCancel₀ (s g) ⟩
                  0₀ ∎

      isComp-g-isg : (g : ⟨ G₁ ⟩) → isComposable g (𝒾s g)
      isComp-g-isg g = sym (τι-≡-fun (s g))

      ισ-ι : (g : ⟨ G₀ ⟩) → 𝒾s (-₁ (𝒾 g)) ≡ -₁ (𝒾 g)
      ισ-ι g = mapInv ι∘σ (𝒾 g) ∙ cong (λ z → -₁ (𝒾 z)) (σι-≡-fun g)
