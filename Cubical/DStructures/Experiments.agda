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

open import Cubical.Structures.Group
open import Cubical.Structures.LeftAction

open import Cubical.DStructures.Base
open import Cubical.DStructures.Properties
open import Cubical.DStructures.Product
open import Cubical.DStructures.Combine
open import Cubical.DStructures.Type
open import Cubical.DStructures.Group

private
  variable
    ℓ ℓ' ℓ'' ℓ₁ ℓ₁' ℓ₁'' ℓ₂ ℓA ℓA' ℓ≅A ℓ≅A' ℓB ℓB' ℓ≅B ℓC ℓ≅C ℓ≅ᴰ ℓ≅ᴰ' : Level


transport-𝒮ᴰ : {A : Type ℓ} {A' : Type ℓ} (p : A ≡ A')
                {𝒮-A : URGStr A ℓ≅A}
                {𝒮-A' : URGStr A' ℓ≅A}
                (p-𝒮 : PathP (λ i → URGStr (p i) ℓ≅A) 𝒮-A 𝒮-A')
                {B : A → Type ℓB} (𝒮ᴰ-A\B : URGStrᴰ 𝒮-A B ℓ≅B)
                → URGStrᴰ 𝒮-A'
                          (λ a' → B (transport (sym p) a'))
                          ℓ≅B
transport-𝒮ᴰ p p-𝒮 = {!make-𝒮ᴰ!}


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
                                  e = {!!}

{-
  Sᴰ-G\GF : URGStrᴰ (URGStrGroup ℓ)
                    (λ G → Σ[ H ∈ Group {ℓ'} ] GroupHom G H)
                    (ℓ-max ℓ ℓ')
  Sᴰ-G\GF = splitTotalURGStrᴰ (URGStrGroup ℓ)
                               (URGStrConstᴰ (URGStrGroup ℓ)
                                             (URGStrGroup ℓ'))
                               Sᴰ-G²\F
-}



{-
  Sᴰ-G\GSecRet : URGStrᴰ (URGStrGroup ℓ)
                         {!!}
                         {!!}
  Sᴰ-G\GSecRet = splitTotalURGStrᴰ (URGStrGroup ℓ)
                                   {!!}
                                   {!!}
-}
