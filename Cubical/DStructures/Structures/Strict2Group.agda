
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
         -- isPeifferGraph = (g g' : ⟨ G₁ ⟩) → g +₁ g' ≡ ((𝒾 (s g') +₁ g') +₁ (-₁ (𝒾 (t g')))) +₁ (-₁ (𝒾 (s g)))
         isPeifferGraph = (a b : ⟨ G₁ ⟩) → (((is b) +₁ (a +₁ (-it a))) +₁ ((-is b) +₁ b)) +₁ (it a) ≡ b +₁ a
         -- isPeifferGraph = (g g' : ⟨ G₁ ⟩) → g +₁ g' ≡ ((((((id (src g')) ⋆₁ g') ⋆₁ (inv₁ (id (τ g')))) ⋆₁ (inv₁ (id (src g)))) ⋆₁ g) ⋆₁ (id (τ g')) )


         isPropIsPeifferGraph : isProp isPeifferGraph
         isPropIsPeifferGraph = isPropΠ2 (λ a b → set₁ ((((is b) +₁ (a +₁ (-it a))) +₁ ((-is b) +₁ b)) +₁ (it a)) (b +₁ a))


module _ (ℓ ℓ' : Level) where
  private
    ℓℓ' = ℓ-max ℓ ℓ'
  𝒮ᴰ-ReflGraph\Peiffer : URGStrᴰ (𝒮-ReflGraph ℓ ℓℓ')
                           (λ (((((G , H) , f , b) , isRet) , b') , isRet') → isPeifferGraph f b b')
                           ℓ-zero
  𝒮ᴰ-ReflGraph\Peiffer = Subtype→Sub-𝒮ᴰ (λ (((((G , H) , f , b) , isRet) , b') , isRet')
                                           → isPeifferGraph f b b' , isPropIsPeifferGraph f b b')
                                        (𝒮-ReflGraph ℓ ℓℓ')
