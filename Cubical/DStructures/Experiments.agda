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
-- open import Cubical.DStructures.Structures.Strict2Group
open import Cubical.DStructures.Structures.XModule
open import Cubical.DStructures.Equivalences.GroupSplitEpiAction


private
  variable
    ℓ ℓ' ℓ'' ℓ₁ ℓ₁' ℓ₁'' ℓ₂ ℓA ℓA' ℓ≅A ℓ≅A' ℓB ℓB' ℓ≅B ℓC ℓ≅C ℓ≅ᴰ ℓ≅ᴰ' ℓ≅B' : Level

open Kernel
open GroupHom -- such .fun!
open GroupLemmas
open MorphismLemmas
open MorphismTree

module _ {ℓ ℓ' : Level} where
  private
    ℓℓ' = ℓ-max ℓ ℓ'

  -- give more suitable names
  SplitEpi = G²SecRet ℓ ℓℓ'
  𝒮-SplitEpi = 𝒮-G²FBSplit ℓ ℓℓ'

  Act = G²Act ℓ ℓℓ'
  𝒮-Act = 𝒮-Action ℓ ℓℓ'

  ReflGraph = Σ[ (((G₀ , G₁) , (ι , σ)) , split-σ) ∈ SplitEpi ] Σ[ τ ∈ GroupHom G₁ G₀ ] isGroupSplitEpi ι τ
  -- this is on a different Σ type
  𝒮-ReflGraph = 𝒮-G²FBSplitBSplit ℓ ℓℓ'

  PreXMod = Σ[ (((G₀ , G₁) , _α_) , isAct) ∈ Act ] Σ[ φ ∈ GroupHom G₁ G₀ ] (isEquivariant _α_ φ)
  𝒮-PreXMod = 𝒮-PreXModule ℓ ℓℓ'

  ℱ-RelIso : 𝒮-iso 𝒮-Act 𝒮-SplitEpi
  ℱ-RelIso = 𝒮-Iso-GroupAct-SplitEpi ℓ ℓℓ'

  ℱ : Act ≃ SplitEpi
  ℱ = isoToEquiv (𝒮-iso→Iso 𝒮-Act 𝒮-SplitEpi ℱ-RelIso)

  ReflGraph→PreXMod : ReflGraph → PreXMod
  ReflGraph→PreXMod = {!!}

  PreXMod→ReflGraph : PreXMod → ReflGraph
  PreXMod→ReflGraph  = {!!}

 --  𝒢 : 𝒮-iso 𝒮-ReflGraph 𝒮-PreXMod
 --  𝒢 = RelFiberIsoOver→RelFiberIso ℱ {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!}

module _ where
  -- for a displayed structure, extract the relational family
  𝒮ᴰ-relFamily : {A : Type ℓA} {𝒮-A : URGStr A ℓ≅A}
                 {B : A → Type ℓB} (𝒮ᴰ-B : URGStrᴰ 𝒮-A B ℓ≅B)
                 → RelFamily A ℓB ℓ≅B
  𝒮ᴰ-relFamily {B = B} 𝒮ᴰ-B .fst = B
  𝒮ᴰ-relFamily {𝒮-A = 𝒮-A} {B = B} 𝒮ᴰ-B .snd {a = a} b b' = b ≅ᴰ⟨ ρ a ⟩ b'
    where
      open URGStr 𝒮-A
      open URGStrᴰ 𝒮ᴰ-B

  -- the type of isos between the relational family extracted
  -- from the displayed structure over A and the
  -- relational family pulled back from the one extracted
  -- from the displayed structure over A'
  𝒮ᴰ-iso : {A : Type ℓA} {𝒮-A : URGStr A ℓ≅A}
           {A' : Type ℓA'} {𝒮-A' : URGStr A' ℓ≅A'}
           (ℱ : A → A')
           {B : A → Type ℓB} (𝒮ᴰ-B : URGStrᴰ 𝒮-A B ℓ≅B)
           {B' : A' → Type ℓB'} (𝒮ᴰ-B' : URGStrᴰ 𝒮-A' B' ℓ≅B')
           → Type (ℓ-max ℓA (ℓ-max (ℓ-max ℓB ℓB') (ℓ-max ℓ≅B ℓ≅B')))
  𝒮ᴰ-iso ℱ 𝒮ᴰ-B 𝒮ᴰ-B'
    = ♭RelFiberIsoOver ℱ (𝒮ᴰ-relFamily 𝒮ᴰ-B) (𝒮ᴰ-relFamily 𝒮ᴰ-B')

  𝒮ᴰ-isoOver→𝒮-iso-1 : {A : Type ℓA} {𝒮-A : URGStr A ℓ≅A}
                      {A' : Type ℓA'} {𝒮-A' : URGStr A' ℓ≅A'}
                      (ℱ : 𝒮-iso 𝒮-A 𝒮-A')
                      {B : A → Type ℓB} (𝒮ᴰ-B : URGStrᴰ 𝒮-A B ℓ≅B)
                      {B' : A' → Type ℓB'} (𝒮ᴰ-B' : URGStrᴰ 𝒮-A' B' ℓ≅B')
                      (𝒢 : 𝒮ᴰ-iso (RelIso.fun ℱ) 𝒮ᴰ-B 𝒮ᴰ-B')
                      → 𝒮-iso (∫⟨ 𝒮-A ⟩ 𝒮ᴰ-B) (∫⟨ 𝒮-A' ⟩ 𝒮ᴰ-B')
  𝒮ᴰ-isoOver→𝒮-iso-1 {A = A} {A' = A'} ℱ 𝒮ᴰ-B 𝒮ᴰ-B' 𝒢 =
    reliso (λ (a , b) → f a , g a b)
           (λ (a' , b') → f- a' , {!g- a' b'!})
           {!!}
           {!!}
    where
      f = RelIso.fun ℱ
      f- = RelIso.inv ℱ
      g = λ (a : A) → RelIso.fun (𝒢 a)
      g- = λ (a' : A') → RelIso.inv (𝒢 (f- a'))

{-
module _ (ℓ ℓ' : Level) where
  private
    ℓℓ' = ℓ-max ℓ ℓ'

  ReflexiveGraph = Σ[ (G₀ , G₁ , ι , σ , split-σ) ∈ (Σ[ G₀ ∈ Group {ℓ} ] GroupSplitEpi G₀ ℓ') ] Σ[ τ ∈ GroupHom G₁ G₀ ] isGroupSplitEpi ι τ

  PreCrossedModule = Σ[ (G₀ , G₁ , _α_ , isAct) ∈ (Σ[ G₀ ∈ Group {ℓ} ] GroupAct G₀ ℓ') ] (Σ[ φ ∈ GroupHom G₁ G₀ ] isEquivariant _α_ φ)
-}


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
