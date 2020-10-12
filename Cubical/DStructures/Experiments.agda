{-# OPTIONS --cubical --no-import-sorts --safe --guardedness #-}
module Cubical.DStructures.Experiments where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path

open import Cubical.Functions.FunExtEquiv

open import Cubical.Homotopy.Base

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Maybe

open import Cubical.Relation.Binary


open import Cubical.Structures.Subtype
open import Cubical.Algebra.Group
open import Cubical.Structures.LeftAction
open import Cubical.Algebra.Group.Semidirect

-- this file also serves as Everything.agda
open import Cubical.DStructures.Base
open import Cubical.DStructures.Meta.Properties
open import Cubical.DStructures.Meta.Combine
open import Cubical.DStructures.Meta.Isomorphism
open import Cubical.DStructures.Structures.Constant
open import Cubical.DStructures.Structures.Category
open import Cubical.DStructures.Structures.Type
open import Cubical.DStructures.Structures.Group
open import Cubical.DStructures.Structures.Action
open import Cubical.DStructures.Structures.Strict2Group
open import Cubical.DStructures.Structures.ReflGraph
open import Cubical.DStructures.Structures.PeifferGraph
open import Cubical.DStructures.Structures.VertComp
open import Cubical.DStructures.Structures.SplitEpi
open import Cubical.DStructures.Structures.Type
open import Cubical.DStructures.Structures.Universe
open import Cubical.DStructures.Structures.XModule
open import Cubical.DStructures.Equivalences.GroupSplitEpiAction
open import Cubical.DStructures.Equivalences.PreXModReflGraph
open import Cubical.DStructures.Equivalences.XModPeifferGraph
open import Cubical.DStructures.Equivalences.PeifferGraphS2G


private
  variable
    ℓ ℓ' ℓ'' ℓ₁ ℓ₁' ℓ₁'' ℓ₂ ℓA ℓA' ℓ≅A ℓ≅A' ℓB ℓB' ℓ≅B ℓC ℓ≅C ℓ≅ᴰ ℓ≅ᴰ' ℓ≅B' : Level

open Kernel
open GroupHom -- such .fun!
open GroupLemmas
open MorphismLemmas




{-

module _ {C : Type ℓ} where
  dispTypeIso : Iso (C → Type ℓ) (Σ[ X ∈ Type ℓ ] (X → C))
  Iso.fun dispTypeIso D .fst = Σ[ c ∈ C ] D c
  Iso.fun dispTypeIso D .snd = fst
  Iso.inv dispTypeIso (X , F) c = Σ[ x ∈ X ] F x ≡ c
  Iso.leftInv dispTypeIso D = funExt (λ c → ua (e c))
    where
      module _ (c : C) where
        x : isContr (Σ[ c' ∈ C ] (c ≡ c'))
        x = isContrSingl c
        e =
          Σ[ (c' , d) ∈ (Σ[ c' ∈ C ] D c') ] c' ≡ c
            ≃⟨ Σ-assoc-≃ ⟩
          Σ[ c' ∈ C ] (D c') × (c' ≡ c)
            ≃⟨ Σ-cong-equiv-snd (λ _ → Σ-swap-≃) ⟩
          Σ[ c' ∈ C ] (c' ≡ c) × (D c')
            ≃⟨ invEquiv Σ-assoc-≃ ⟩
          Σ[ (c' , _) ∈ Σ[ c' ∈ C ] (c' ≡ c) ] D c'
            ≃⟨ Σ-cong-equiv-fst (Σ-cong-equiv-snd (λ c' → isoToEquiv (iso sym sym (λ _ → refl) (λ _ → refl)))) ⟩
          Σ[ (c' , _) ∈ Σ[ c' ∈ C ] (c ≡ c') ] D c'
            ≃⟨ Σ-contractFst (isContrSingl c) ⟩
          D c ■

  Iso.rightInv dispTypeIso (X , F) = ΣPathP (p₁ , p₂)
    where
      p₁' =
        Σ[ c ∈ C ] (Σ[ x ∈ X ] F x ≡ c)
           ≃⟨ invEquiv Σ-assoc-≃ ⟩
        Σ[ (c , x) ∈ C × X ] (F x ≡ c)
           ≃⟨ Σ-cong-equiv-fst Σ-swap-≃ ⟩
        Σ[ (x , c) ∈ X × C ] (F x ≡ c)
           ≃⟨ Σ-assoc-≃ ⟩
        Σ[ x ∈ X ] Σ[ c ∈ C ] (F x ≡ c)
           ≃⟨ Σ-contractSnd (λ x → isContrSingl (F x)) ⟩
        X ■
      p₁ : (Σ[ c ∈ C ] (Σ[ x ∈ X ] F x ≡ c)) ≡ X
      p₁ = ua p₁'

      p₂ : PathP (λ i → p₁ i → C) fst F
      p₂ = funExtDep p₂'
        where
          module _ {(c , x , p) : Σ[ c ∈ C ] (Σ[ x ∈ X ] F x ≡ c)} {y : X} (q : PathP (λ i → p₁ i) (c , x , p) y) where
            p₂' : c ≡ F y
            p₂' = sym p ∙ cong F p₂''
              where
                p₂'' =
                  x
                    ≡⟨ sym (uaβ p₁' (c , x , p)) ⟩
                  transp (λ i → p₁ i) i0 (c , x , p)
                    ≡⟨ fromPathP q ⟩
                  y ∎

-}

{-

record Hom-𝒮 {A : Type ℓA} {ℓ≅A : Level} (𝒮-A : URGStr A ℓ≅A)
             {B : Type ℓB} {ℓ≅B : Level} (𝒮-B : URGStr B ℓ≅B)
             : Type (ℓ-max (ℓ-max ℓA ℓB) (ℓ-max ℓ≅A ℓ≅B)) where
  constructor hom-𝒮
  open URGStr
  field
    fun : A → B
    fun-≅ : {a a' : A} → (p : _≅_ 𝒮-A a a') → _≅_ 𝒮-B (fun a) (fun a')
    fun-ρ : {a : A} → fun-≅ (ρ 𝒮-A a) ≡ ρ 𝒮-B (fun a)

∫𝒮ᴰ-π₁ : {A : Type ℓA} {𝒮-A : URGStr A ℓ≅A}
         {B : A → Type ℓB} (𝒮ᴰ-B : URGStrᴰ 𝒮-A B ℓ≅B)
         → Hom-𝒮 (∫⟨ 𝒮-A ⟩ 𝒮ᴰ-B) 𝒮-A
Hom-𝒮.fun (∫𝒮ᴰ-π₁ 𝒮ᴰ-B) = fst
Hom-𝒮.fun-≅ (∫𝒮ᴰ-π₁ 𝒮ᴰ-B) = fst
Hom-𝒮.fun-ρ (∫𝒮ᴰ-π₁ 𝒮ᴰ-B) = refl

module _ {ℓ : Level} {A : Type ℓ} (𝒮-A : URGStr A ℓ) where
  𝒮ᴰ-toHom : Iso (Σ[ B ∈ (A → Type ℓ) ] (URGStrᴰ 𝒮-A B ℓ)) (Σ[ B ∈ (Type ℓ) ] Σ[ 𝒮-B ∈ (URGStr B ℓ) ] (Hom-𝒮 𝒮-B 𝒮-A))
  Iso.fun 𝒮ᴰ-toHom (B , 𝒮ᴰ-B) = (Σ[ a ∈ A ] B a) , {!!} , {!!}
  Iso.inv 𝒮ᴰ-toHom (B , 𝒮ᴰ-B , F) = (λ a → Σ[ b ∈ B ] F .fun b ≡ a) , {!!}
    where
      open Hom-𝒮
  Iso.leftInv 𝒮ᴰ-toHom (B , 𝒮ᴰ-B) = ΣPathP ((funExt (λ a → {!!})) , {!!})
  Iso.rightInv 𝒮ᴰ-toHom (B , 𝒮ᴰ-B , F) = {!!}
-}


 


-- Older Experiments --

-- needs --guardedness flag

module _ where
  record Hierarchy {A : Type ℓ} (𝒮-A : URGStr A ℓ) : Type (ℓ-suc ℓ) where
    coinductive
    field
      B : A → Type ℓ
      𝒮ᴰ-B : URGStrᴰ 𝒮-A B ℓ
      ℋ : Maybe (Hierarchy {A = Σ A B} (∫⟨ 𝒮-A ⟩ 𝒮ᴰ-B))
