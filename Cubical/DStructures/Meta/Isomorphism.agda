{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Meta.Isomorphism where

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
open import Cubical.DStructures.Meta.Properties
open import Cubical.DStructures.Structures.Constant
open import Cubical.DStructures.Meta.Combine
open import Cubical.DStructures.Structures.Type
open import Cubical.DStructures.Structures.Group

private
  variable
    ℓ ℓ' ℓ'' ℓ₁ ℓ₁' ℓ₁'' ℓ₂ ℓA ℓA' ℓ≅A ℓ≅A' ℓB ℓB' ℓ≅B ℓ≅B' ℓC ℓ≅C ℓ≅ᴰ ℓ≅ᴰ' : Level

module _ {A : Type ℓA} (𝒮-A : URGStr A ℓ≅A)
         {A' : Type ℓA'} (𝒮-A' : URGStr A' ℓ≅A') where

       𝒮-iso : Type (ℓ-max (ℓ-max ℓA ℓA') (ℓ-max ℓ≅A ℓ≅A'))
       𝒮-iso = RelIso (URGStr._≅_ 𝒮-A) (URGStr._≅_ 𝒮-A')

       𝒮-iso→Iso : 𝒮-iso → Iso A A'
       𝒮-iso→Iso f = RelIso→Iso (_≅_ 𝒮-A) (_≅_ 𝒮-A') (ρ 𝒮-A) (ρ 𝒮-A') (uni 𝒮-A) (uni 𝒮-A') f
         where
           open URGStr


module _ {A : Type ℓA} {_≅A_ : Rel A A ℓ≅A}
         {A' : Type ℓA'} {_≅A'_ : Rel A' A' ℓ≅A'}
         (ℱ : RelIso _≅A_ _≅A'_)
         (B : RelFamily A ℓB ℓ≅B) (ρ : isFiberwiseReflexive B) (uni : isFiberwiseUnivalent B ρ)
         (B' : RelFamily A' ℓB' ℓ≅B') (ρ' : isFiberwiseReflexive B') (uni' : isFiberwiseUnivalent B' ρ') where

         f = RelIso.fun ℱ
         ♭B' = ♭RelFamily B' f
         ΣB = Σ[ a ∈ A ] (B .fst a)
         ΣB' = Σ[ a ∈ A' ] (B' .fst a)
         _≅ΣB_ : Rel ΣB ΣB' ?
         _≅ΣB_ = ?

         RelFiberIsoOver→TotalFiberIso : (𝒢 : ♭RelFiberIsoOver f B B')
                                         → RelIso {!!} {!!}
         RelFiberIsoOver→TotalFiberIso 𝒢 = {!!}

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
                      (B≅B' : 𝒮ᴰ-iso (RelIso.fun ℱ) 𝒮ᴰ-B 𝒮ᴰ-B')
                      → 𝒮-iso (∫⟨ 𝒮-A ⟩ 𝒮ᴰ-B) (∫⟨ 𝒮-A' ⟩ 𝒮ᴰ-B')
  𝒮ᴰ-isoOver→𝒮-iso-1 = {!!}
