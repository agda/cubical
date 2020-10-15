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


open import Cubical.Algebra.Group
open import Cubical.Structures.LeftAction

open import Cubical.DStructures.Base
open import Cubical.DStructures.Meta.Properties
open import Cubical.DStructures.Structures.Constant

open import Cubical.DStructures.Structures.Type
open import Cubical.DStructures.Structures.Group

private
  variable
    ℓ ℓ' ℓ'' ℓ₁ ℓ₁' ℓ₁'' ℓ₂ ℓA ℓA' ℓ≅A ℓ≅A' ℓB ℓB' ℓ≅B ℓ≅B' ℓC ℓ≅C ℓ≅ᴰ ℓ≅ᴰ' : Level

open URGStr
open URGStrᴰ

----------------------------------------------
-- Pseudo-isomorphisms between URG structures
-- are relational isos of the underlying rel.
----------------------------------------------
𝒮-PIso : {A : Type ℓA} (𝒮-A : URGStr A ℓ≅A)
         {A' : Type ℓA'} (𝒮-A' : URGStr A' ℓ≅A')
         → Type (ℓ-max (ℓ-max ℓA ℓA') (ℓ-max ℓ≅A ℓ≅A'))
𝒮-PIso 𝒮-A 𝒮-A' = RelIso (URGStr._≅_ 𝒮-A) (URGStr._≅_ 𝒮-A')

----------------------------------------------
-- Since the relations are univalent,
-- a rel. iso induces an iso of the underlying
-- types.
----------------------------------------------
𝒮-PIso→Iso : {A : Type ℓA} (𝒮-A : URGStr A ℓ≅A)
             {A' : Type ℓA'} (𝒮-A' : URGStr A' ℓ≅A')
             (ℱ : 𝒮-PIso 𝒮-A 𝒮-A')
             → Iso A A'
𝒮-PIso→Iso 𝒮-A 𝒮-A' ℱ
  = RelIso→Iso (_≅_ 𝒮-A) (_≅_ 𝒮-A') (uni 𝒮-A) (uni 𝒮-A') ℱ

----------------------------------------------
-- From a DURG structure, extract the
-- relational family over the base type
----------------------------------------------
𝒮ᴰ→relFamily : {A : Type ℓA} {𝒮-A : URGStr A ℓ≅A}
               {B : A → Type ℓB} (𝒮ᴰ-B : URGStrᴰ 𝒮-A B ℓ≅B)
               → RelFamily A ℓB ℓ≅B
-- define the type family, just B
𝒮ᴰ→relFamily {B = B} 𝒮ᴰ-B .fst = B
-- the binary relation is the displayed relation over ρ a
𝒮ᴰ→relFamily {𝒮-A = 𝒮-A} {B = B} 𝒮ᴰ-B .snd {a = a} b b'
  = 𝒮ᴰ-B ._≅ᴰ⟨_⟩_ b (𝒮-A .ρ a) b'

--------------------------------------------------------------
-- the type of relational isos between a DURG structure
-- and the pulled back relational family of another
--
-- ℱ will in applications always be an isomorphism,
-- but that's not needed for this definition.
--------------------------------------------------------------
𝒮ᴰ-♭PIso : {A : Type ℓA} {𝒮-A : URGStr A ℓ≅A}
           {A' : Type ℓA'} {𝒮-A' : URGStr A' ℓ≅A'}
           (ℱ : A → A')
           {B : A → Type ℓB} (𝒮ᴰ-B : URGStrᴰ 𝒮-A B ℓ≅B)
           {B' : A' → Type ℓB'} (𝒮ᴰ-B' : URGStrᴰ 𝒮-A' B' ℓ≅B')
           → Type (ℓ-max ℓA (ℓ-max (ℓ-max ℓB ℓB') (ℓ-max ℓ≅B ℓ≅B')))
𝒮ᴰ-♭PIso ℱ 𝒮ᴰ-B 𝒮ᴰ-B'
  = ♭RelFiberIsoOver ℱ (𝒮ᴰ→relFamily 𝒮ᴰ-B) (𝒮ᴰ→relFamily 𝒮ᴰ-B')

---------------------------------------------------------
-- Given
-- - an isomorphism ℱ of underlying types A, A', and
-- - an 𝒮ᴰ-bPIso over ℱ
-- produce an iso of the underlying total spaces
---------------------------------------------------------
𝒮ᴰ-♭PIso-Over→TotalIso : {A : Type ℓA} {𝒮-A : URGStr A ℓ≅A}
                         {A' : Type ℓA'} {𝒮-A' : URGStr A' ℓ≅A'}
                         (ℱ : Iso A A')
                         {B : A → Type ℓB} (𝒮ᴰ-B : URGStrᴰ 𝒮-A B ℓ≅B)
                         {B' : A' → Type ℓB'} (𝒮ᴰ-B' : URGStrᴰ 𝒮-A' B' ℓ≅B')
                         (𝒢 : 𝒮ᴰ-♭PIso (Iso.fun ℱ) 𝒮ᴰ-B 𝒮ᴰ-B')
                         → Iso (Σ A B) (Σ A' B')
𝒮ᴰ-♭PIso-Over→TotalIso ℱ 𝒮ᴰ-B 𝒮ᴰ-B' 𝒢
  = RelFiberIsoOver→Iso ℱ
                        (𝒮ᴰ→relFamily 𝒮ᴰ-B) (𝒮ᴰ-B .uniᴰ)
                        (𝒮ᴰ→relFamily 𝒮ᴰ-B') (𝒮ᴰ-B' .uniᴰ)
                        𝒢

