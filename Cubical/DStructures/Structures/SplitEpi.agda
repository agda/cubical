{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Structures.SplitEpi where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv

open import Cubical.Homotopy.Base

open import Cubical.Data.Sigma

open import Cubical.Relation.Binary

open import Cubical.Structures.Group
open import Cubical.Structures.LeftAction

open import Cubical.DStructures.Base
open import Cubical.DStructures.Meta.Properties
open import Cubical.DStructures.Meta.Combine
open import Cubical.DStructures.Structures.Type
open import Cubical.DStructures.Structures.Constant
open import Cubical.DStructures.Structures.Group

private
  variable
    ℓ ℓ' : Level

open URGStr

---------------------------------------------
-- URG structures on the type of split epis,
-- and displayed structures over that
--
--     B
--     |
--  isSplit
--     |
--   G²FB
---------------------------------------------

module _ (ℓ ℓ' : Level) where

  -- type of Split epimorphisms
  SplitEpi = Σ[ ((G , H) , f , b) ∈ G²FB ℓ ℓ' ] isGroupSplitEpi f b

  -- split epimorphisms + a map back
  SplitEpiB = Σ[ (((G , H) , f , b) , isRet) ∈ SplitEpi ] GroupHom H G

  -- split epimorphisms displayed over pairs of groups
  𝒮ᴰ-SplitEpi : URGStrᴰ (𝒮-G²FB ℓ ℓ')
                        (λ ((G , H) , (f , g)) → isGroupSplitEpi f g)
                        ℓ-zero
  𝒮ᴰ-SplitEpi =
    Subtype→Sub-𝒮ᴰ (λ ((G , H) , (f , g)) → isGroupSplitEpi f g , isPropIsGroupHomRet f g)
                   (𝒮-G²FB ℓ ℓ')

  -- URG structure on type of split epimorphisms
  𝒮-SplitEpi : URGStr SplitEpi (ℓ-max ℓ ℓ')
  𝒮-SplitEpi = ∫⟨ 𝒮-G²FB ℓ ℓ' ⟩ 𝒮ᴰ-SplitEpi

  -- morphisms back displayed over split epimorphisms,
  -- obtained by lifting the morphisms back over
  -- 𝒮-G² twice
  𝒮ᴰ-G²FBSplit\B : URGStrᴰ 𝒮-SplitEpi
                           (λ (((G , H) , _) , _) → GroupHom H G)
                           (ℓ-max ℓ ℓ')
  𝒮ᴰ-G²FBSplit\B =
    VerticalLift2-𝒮ᴰ (𝒮-group ℓ ×𝒮 𝒮-group ℓ')
                     (𝒮ᴰ-G²\B ℓ ℓ')
                     (𝒮ᴰ-G²\FB ℓ ℓ')
                     𝒮ᴰ-SplitEpi

  -- URG structure on split epis with an extra
  -- morphism back
  𝒮-SplitEpiB : URGStr SplitEpiB (ℓ-max ℓ ℓ')
  𝒮-SplitEpiB = ∫⟨ 𝒮-SplitEpi ⟩ 𝒮ᴰ-G²FBSplit\B

--------------------------------------------------
-- This module introduces convenient notation
-- when working with a single split epimorphism
---------------------------------------------------

module SplitEpiNotation {G₀ : Group {ℓ}} {G₁ : Group {ℓ'}}
                        (ι : GroupHom G₀ G₁) (σ : GroupHom G₁ G₀)
                        (split : isGroupSplitEpi ι σ) where
  open GroupNotation₀ G₀
  open GroupNotation₁ G₁
  ι∘σ : GroupHom G₁ G₁
  ι∘σ = compGroupHom σ ι
  s = GroupHom.fun σ
  -- i is reserved for an interval variable (i : I) so we use 𝒾 instead
  𝒾 = GroupHom.fun ι
  -i = λ (x : ⟨ G₀ ⟩) → -₁ (𝒾 x)
  s- = λ (x : ⟨ G₁ ⟩) → s (-₁ x)
  si = λ (x : ⟨ G₀ ⟩) → s (𝒾 x)
  is = λ (x : ⟨ G₁ ⟩) → 𝒾 (s x)
  -si = λ (x : ⟨ G₀ ⟩) → -₀ (si x)
  -is = λ (x : ⟨ G₁ ⟩) → -₁ (is x)
  si- = λ (x : ⟨ G₀ ⟩) → si (-₀ x)
  is- = λ (x : ⟨ G₁ ⟩) → is (-₁ x)
  s-i = λ (x : ⟨ G₀ ⟩) → s (-₁ (𝒾 x))
  isi = λ (x : ⟨ G₀ ⟩) → 𝒾 (s (𝒾 x))
