
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Strict2Group where

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
open import Cubical.DStructures.Properties
open import Cubical.DStructures.Product
open import Cubical.DStructures.Combine
open import Cubical.DStructures.Type
open import Cubical.DStructures.Group


module _ {ℓ ℓ' : Level} where

  module _ {G₀ : Group {ℓ}} {G₁ : Group {ℓ'}}
           {Id : GroupHom G₀ G₁} {Src : GroupHom G₁ G₀} {Tar : GroupHom G₁ G₀}
           (retSrc : isGroupHomRet Id Src) (retTar : isGroupHomRet Id Tar) where

         _⋆₁_ = Group._+_ G₁
         inv₁ = Group.-_ G₁
         id = GroupHom.fun Id
         src = GroupHom.fun Src
         tar = GroupHom.fun Tar
         set₁ = Group.is-set G₁

         isPeifferGraph : Type ℓ'
         isPeifferGraph = (g g' : ⟨ G₁ ⟩) → g ⋆₁ g' ≡ ((((((id (src g')) ⋆₁ g') ⋆₁ (inv₁ (id (tar g')))) ⋆₁ (inv₁ (id (src g)))) ⋆₁ g) ⋆₁ (id (tar g')) )

         isPropIsPeifferGraph : isProp isPeifferGraph
         isPropIsPeifferGraph = isPropΠ2 (λ g g' → set₁ (g ⋆₁ g')
                                                        (((((((id (src g')) ⋆₁ g') ⋆₁ (inv₁ (id (tar g')))) ⋆₁ (inv₁ (id (src g)))) ⋆₁ g) ⋆₁ (id (tar g')) )))


module _ (ℓ ℓ' : Level) where
  open MorphismTree ℓ ℓ'
  𝒮ᴰ-G²FBSplitBSplit\Peiffer : URGStrᴰ 𝒮-G²FBSplitBSplit
                           (λ (((((G , H) , f , b) , isRet) , b') , isRet') → isPeifferGraph isRet isRet')
                           ℓ-zero
  𝒮ᴰ-G²FBSplitBSplit\Peiffer = Subtype→Sub-𝒮ᴰ (λ (((((G , H) , f , b) , isRet) , b') , isRet')
                                      → isPeifferGraph isRet isRet' , isPropIsPeifferGraph isRet isRet')
                                   𝒮-G²FBSplitBSplit
