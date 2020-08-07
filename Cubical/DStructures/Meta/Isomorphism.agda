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

open URGStr
open URGStrᴰ

𝒮-iso : {A : Type ℓA} (𝒮-A : URGStr A ℓ≅A)
        {A' : Type ℓA'} (𝒮-A' : URGStr A' ℓ≅A')
        → Type (ℓ-max (ℓ-max ℓA ℓA') (ℓ-max ℓ≅A ℓ≅A'))
𝒮-iso 𝒮-A 𝒮-A' = RelIso (URGStr._≅_ 𝒮-A) (URGStr._≅_ 𝒮-A')

𝒮-iso→Iso : {A : Type ℓA} (𝒮-A : URGStr A ℓ≅A)
            {A' : Type ℓA'} (𝒮-A' : URGStr A' ℓ≅A')
            (ℱ : 𝒮-iso 𝒮-A 𝒮-A')
            → Iso A A'
𝒮-iso→Iso 𝒮-A 𝒮-A' ℱ
  = RelIso→Iso (_≅_ 𝒮-A) (_≅_ 𝒮-A') (uni 𝒮-A) (uni 𝒮-A') ℱ

-- for a displayed structure, extract the relational family
𝒮ᴰ→relFamily : {A : Type ℓA} {𝒮-A : URGStr A ℓ≅A}
               {B : A → Type ℓB} (𝒮ᴰ-B : URGStrᴰ 𝒮-A B ℓ≅B)
               → RelFamily A ℓB ℓ≅B
𝒮ᴰ→relFamily {B = B} 𝒮ᴰ-B .fst = B
𝒮ᴰ→relFamily {𝒮-A = 𝒮-A} {B = B} 𝒮ᴰ-B .snd {a = a} b b' = 𝒮ᴰ-B ._≅ᴰ⟨_⟩_ b (𝒮-A .ρ a) b'

-- the type of isos between the relational family extracted
-- from the displayed structure over A and the
-- relational family pulled back from the one extracted
-- from the displayed structure over A'
𝒮ᴰ-♭iso : {A : Type ℓA} {𝒮-A : URGStr A ℓ≅A}
          {A' : Type ℓA'} {𝒮-A' : URGStr A' ℓ≅A'}
          (ℱ : A → A')
          {B : A → Type ℓB} (𝒮ᴰ-B : URGStrᴰ 𝒮-A B ℓ≅B)
          {B' : A' → Type ℓB'} (𝒮ᴰ-B' : URGStrᴰ 𝒮-A' B' ℓ≅B')
          → Type (ℓ-max ℓA (ℓ-max (ℓ-max ℓB ℓB') (ℓ-max ℓ≅B ℓ≅B')))
𝒮ᴰ-♭iso ℱ 𝒮ᴰ-B 𝒮ᴰ-B'
  = ♭RelFiberIsoOver ℱ (𝒮ᴰ→relFamily 𝒮ᴰ-B) (𝒮ᴰ→relFamily 𝒮ᴰ-B')

𝒮ᴰ-♭Iso→TotalIso : {A : Type ℓA} {𝒮-A : URGStr A ℓ≅A}
                   {A' : Type ℓA'} {𝒮-A' : URGStr A' ℓ≅A'}
                   (ℱ : 𝒮-iso 𝒮-A 𝒮-A')
                   {B : A → Type ℓB} (𝒮ᴰ-B : URGStrᴰ 𝒮-A B ℓ≅B)
                   {B' : A' → Type ℓB'} (𝒮ᴰ-B' : URGStrᴰ 𝒮-A' B' ℓ≅B')
                   (𝒢 : 𝒮ᴰ-♭iso (RelIso.fun ℱ) 𝒮ᴰ-B 𝒮ᴰ-B')
                   → Iso (Σ A B) (Σ A' B')
𝒮ᴰ-♭Iso→TotalIso {A = A} {𝒮-A = 𝒮-A} {A' = A'} {𝒮-A' = 𝒮-A'} ℱ 𝒮ᴰ-B 𝒮ᴰ-B' 𝒢
  = RelFiberIsoOver→Iso (𝒮-iso→Iso 𝒮-A 𝒮-A' ℱ)
                        (𝒮ᴰ→relFamily 𝒮ᴰ-B) (𝒮ᴰ-B .uniᴰ)
                        (𝒮ᴰ→relFamily 𝒮ᴰ-B') (𝒮ᴰ-B' .uniᴰ)
                        𝒢

Iso→TotalIso : {A : Type ℓA} {𝒮-A : URGStr A ℓ≅A}
                   {A' : Type ℓA'} {𝒮-A' : URGStr A' ℓ≅A'}
                   (ℱ : Iso A A')
                   {B : A → Type ℓB} (𝒮ᴰ-B : URGStrᴰ 𝒮-A B ℓ≅B)
                   {B' : A' → Type ℓB'} (𝒮ᴰ-B' : URGStrᴰ 𝒮-A' B' ℓ≅B')
                   (𝒢 : 𝒮ᴰ-♭iso (Iso.fun ℱ) 𝒮ᴰ-B 𝒮ᴰ-B')
                   → Iso (Σ A B) (Σ A' B')
Iso→TotalIso {A = A} {𝒮-A = 𝒮-A} {A' = A'} {𝒮-A' = 𝒮-A'} ℱ 𝒮ᴰ-B 𝒮ᴰ-B' 𝒢
  = RelFiberIsoOver→Iso ℱ
                        (𝒮ᴰ→relFamily 𝒮ᴰ-B) (𝒮ᴰ-B .uniᴰ)
                        (𝒮ᴰ→relFamily 𝒮ᴰ-B') (𝒮ᴰ-B' .uniᴰ)
                        𝒢

-- old stuff

  {-


  𝒮ᴰ-iso : {A : Type ℓA} {𝒮-A : URGStr A ℓ≅A}
           {A' : Type ℓA'} {𝒮-A' : URGStr A' ℓ≅A'}
           (ℱ : A → A')
           {B : A → Type ℓB} (𝒮ᴰ-B : URGStrᴰ 𝒮-A B ℓ≅B)
           {B' : A' → Type ℓB'} (𝒮ᴰ-B' : URGStrᴰ 𝒮-A' B' ℓ≅B')
           → Type (ℓ-max ℓA (ℓ-max (ℓ-max ℓB ℓB') (ℓ-max ℓ≅B ℓ≅B')))
  𝒮ᴰ-iso ℱ 𝒮ᴰ-B 𝒮ᴰ-B' = RelFiberIsoOver ℱ (𝒮ᴰ→relFamily 𝒮ᴰ-B) (𝒮ᴰ→relFamily 𝒮ᴰ-B')

  𝒮ᴰ-isoOver→𝒮-♭iso : {A : Type ℓA} {𝒮-A : URGStr A ℓ≅A}
                      {A' : Type ℓA'} {𝒮-A' : URGStr A' ℓ≅A'}
                      (ℱ : 𝒮-iso 𝒮-A 𝒮-A')
                      {B : A → Type ℓB} (𝒮ᴰ-B : URGStrᴰ 𝒮-A B ℓ≅B)
                      {B' : A' → Type ℓB'} (𝒮ᴰ-B' : URGStrᴰ 𝒮-A' B' ℓ≅B')
                      (𝒢 : 𝒮ᴰ-♭iso (RelIso.fun ℱ) 𝒮ᴰ-B 𝒮ᴰ-B')
                      → RelIso {A = Σ A B} (URGStr._≅_ (∫⟨ 𝒮-A ⟩ 𝒮ᴰ-B))
                               {A' = Σ[ a ∈ A ] B' (RelIso.fun ℱ a)}
                               λ (a , b) (a' , b') → Σ[ e ∈ URGStr._≅_ 𝒮-A' (RelIso.fun ℱ a) (RelIso.fun ℱ a') ] URGStrᴰ._≅ᴰ⟨_⟩_ 𝒮ᴰ-B' b e b'
  𝒮ᴰ-isoOver→𝒮-♭iso {A = A} {𝒮-A = 𝒮-A} {A' = A'} {𝒮-A' = 𝒮-A'} ℱ 𝒮ᴰ-B 𝒮ᴰ-B' 𝒢 =
    reliso (λ (a , b) → a , 𝒢 a .fun b)
           (λ (a , b') → a , 𝒢 a .inv b')
           (λ (a , b') → 𝒮-A' .ρ  (ℱ .fun a) , 𝒢 a .rightInv b')
           λ (a , b) → 𝒮-A .ρ a , 𝒢 a .leftInv b
    where
      open RelIso
      open URGStr

  𝒮ᴰ-♭iso→♭iso : {A : Type ℓA} {𝒮-A : URGStr A ℓ≅A}
                 {A' : Type ℓA'} {𝒮-A' : URGStr A' ℓ≅A'}
                 (ℱ : 𝒮-iso 𝒮-A 𝒮-A')
                 {B : A → Type ℓB} (𝒮ᴰ-B : URGStrᴰ 𝒮-A B ℓ≅B)
                 {B' : A' → Type ℓB'} (𝒮ᴰ-B' : URGStrᴰ 𝒮-A' B' ℓ≅B')
                 (𝒢 : 𝒮ᴰ-♭iso (RelIso.fun ℱ) 𝒮ᴰ-B 𝒮ᴰ-B')
                 (ℋ : RelIso {A = Σ A B} (URGStr._≅_ (∫⟨ 𝒮-A ⟩ 𝒮ᴰ-B))
                              {A' = Σ[ a ∈ A ] B' (RelIso.fun ℱ a)}
                              λ (a , b) (a' , b') → Σ[ e ∈ URGStr._≅_ 𝒮-A' (RelIso.fun ℱ a) (RelIso.fun ℱ a') ] URGStrᴰ._≅ᴰ⟨_⟩_ 𝒮ᴰ-B' b e b')
                 → Iso (Σ A B) (Σ[ a ∈ A ] B' (RelIso.fun ℱ a))
  𝒮ᴰ-♭iso→♭iso {A = A} {𝒮-A = 𝒮-A} {A' = A'} {𝒮-A' = 𝒮-A'} ℱ 𝒮ᴰ-B 𝒮ᴰ-B' 𝒢 ℋ =
    iso (ℋ .fun) (ℋ .inv)
        (λ (a , b') → {!!})
        λ (a , b) → {!!}
    where
      open RelIso
      open URGStr

  𝒮ᴰ-isoOver→TotalIso : {A : Type ℓA} {𝒮-A : URGStr A ℓ≅A}
                        {A' : Type ℓA'} {𝒮-A' : URGStr A' ℓ≅A'}
                        (ℱ : 𝒮-iso 𝒮-A 𝒮-A')
                        {B : A → Type ℓB} (𝒮ᴰ-B : URGStrᴰ 𝒮-A B ℓ≅B)
                        {B' : A' → Type ℓB'} (𝒮ᴰ-B' : URGStrᴰ 𝒮-A' B' ℓ≅B')
                        (𝒢 : 𝒮ᴰ-♭iso (RelIso.fun ℱ) 𝒮ᴰ-B 𝒮ᴰ-B')
                        → Iso (Σ A B) (Σ A' B')
  𝒮ᴰ-isoOver→TotalIso {A = A} {𝒮-A = 𝒮-A} {A' = A'} {𝒮-A' = 𝒮-A'} ℱ 𝒮ᴰ-B 𝒮ᴰ-B' 𝒢
    = compIso (𝒮ᴰ-♭iso→♭iso ℱ 𝒮ᴰ-B 𝒮ᴰ-B' 𝒢 (𝒮ᴰ-isoOver→𝒮-♭iso ℱ 𝒮ᴰ-B 𝒮ᴰ-B' 𝒢))
              (Σ-cong-iso-fst (𝒮-iso→Iso 𝒮-A 𝒮-A' ℱ))
    where
      open RelIso
      open URGStr
  -}
