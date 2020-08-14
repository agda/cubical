{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Structures.PeifferGraph where

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
  module _ {G₀ : Group {ℓ}} {G₁ : Group {ℓ'}}
           (ι : GroupHom G₀ G₁) (σ : GroupHom G₁ G₀) (τ : GroupHom G₁ G₀) where
         open GroupNotation₁ G₁

         private
           𝒾 = GroupHom.fun ι
           s = GroupHom.fun σ
           t = GroupHom.fun τ
           is = λ (h : ⟨ G₁ ⟩) → 𝒾 (s h)
           -is = λ (h : ⟨ G₁ ⟩) → -₁ 𝒾 (s h)
           it = λ (h : ⟨ G₁ ⟩) → 𝒾 (t h)
           -it = λ (h : ⟨ G₁ ⟩) → -₁ 𝒾 (t h)

         isPeifferGraph : Type ℓ'
         isPeifferGraph = (a b : ⟨ G₁ ⟩) → (((is b) +₁ (a +₁ (-it a))) +₁ ((-is b) +₁ b)) +₁ (it a) ≡ b +₁ a

         isPropIsPeifferGraph : isProp isPeifferGraph
         isPropIsPeifferGraph = isPropΠ2 (λ a b → set₁ ((((is b) +₁ (a +₁ (-it a))) +₁ ((-is b) +₁ b)) +₁ (it a)) (b +₁ a))

         -- peiffer graph lemmas
         isPeifferGraph' : (a b : ⟨ G₁ ⟩)

module _ (ℓ ℓ' : Level) where
  private
    ℓℓ' = ℓ-max ℓ ℓ'

  𝒮ᴰ-ReflGraph\Peiffer : URGStrᴰ (𝒮-ReflGraph ℓ ℓℓ')
                           (λ (((((G , H) , f , b) , isRet) , b') , isRet') → isPeifferGraph f b b')
                           ℓ-zero
  𝒮ᴰ-ReflGraph\Peiffer = Subtype→Sub-𝒮ᴰ (λ (((((G , H) , f , b) , isRet) , b') , isRet')
                                           → isPeifferGraph f b b' , isPropIsPeifferGraph f b b')
                                        (𝒮-ReflGraph ℓ ℓℓ')

  PeifferGraph : Type (ℓ-suc ℓℓ')
  PeifferGraph = Σ[ (((((G₀ , G₁) , ι , σ) , split-σ) , τ) , split-τ) ∈ ReflGraph ℓ ℓℓ' ] isPeifferGraph ι σ τ 

  𝒮-PeifferGraph : URGStr PeifferGraph ℓℓ'
  𝒮-PeifferGraph = ∫⟨ 𝒮-ReflGraph ℓ ℓℓ' ⟩ 𝒮ᴰ-ReflGraph\Peiffer
