{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Combine where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Relation.Binary
open BinaryRelation

open import Cubical.DStructures.Base
open import Cubical.DStructures.Properties

private
  variable
    ℓ ℓ' ℓ'' ℓ₁ ℓ₁' ℓ₁'' ℓ₂ ℓA ℓ≅A ℓB ℓ≅B ℓC ℓ≅C ℓ≅ᴰ : Level

-- combine two structures StrB and StrC over StrA to a structure StrB × StrC over A
combineURGStrᴰ : {A : Type ℓA} {StrA : URGStr A ℓ≅A}
                 {B : A → Type ℓB} {C : A → Type ℓC}
                 (StrBᴰ : URGStrᴰ StrA B ℓ≅B)
                 (StrCᴰ : URGStrᴰ StrA C ℓ≅C)
                 → URGStrᴰ StrA (λ a → B a × C a) (ℓ-max ℓ≅B ℓ≅C)
combineURGStrᴰ {ℓ≅B = ℓ≅B} {ℓ≅C = ℓ≅C} {A = A} {StrA = StrA} {B = B} {C = C} StrBᴰ StrCᴰ =
  makeURGStrᴰ (λ a → B a × C a)
              (ℓ-max ℓ≅B ℓ≅C)
              -- equality in the combined structure is defined componentwise
              (λ (b , c) p (b' , c') → b B≅ᴰ⟨ p ⟩ b' × c C≅ᴰ⟨ p ⟩ c')
              -- reflexivity follows from B and C reflexivity
              (λ (b , c) → Bρᴰ b , Cρᴰ c)
              -- so does univalence
              contrTot
  where
    ρ = URGStr.ρ StrA
    _B≅ᴰ⟨_⟩_ = URGStrᴰ._≅ᴰ⟨_⟩_ StrBᴰ
    _C≅ᴰ⟨_⟩_ = URGStrᴰ._≅ᴰ⟨_⟩_ StrCᴰ
    Bρᴰ = URGStrᴰ.ρᴰ StrBᴰ
    Cρᴰ = URGStrᴰ.ρᴰ StrCᴰ
    Buniᴰ = URGStrᴰ.uniᴰ StrBᴰ
    Cuniᴰ = URGStrᴰ.uniᴰ StrCᴰ
    contrTot : (a : A) ((b , c) : B a × C a) → isContr (Σ[ (b' , c') ∈ B a × C a ] (b B≅ᴰ⟨ ρ a ⟩ b' × c C≅ᴰ⟨ ρ a ⟩ c') )
    contrTot = λ (a : A) ((b , c) : B a × C a)
      → isOfHLevelRespectEquiv 0
                               (Σ[ b' ∈ B a ] (b B≅ᴰ⟨ ρ a ⟩ b')
                                 ≃⟨ invEquiv (Σ-contractSnd (λ _ → isUnivalent→contrTotalSpace (_C≅ᴰ⟨ ρ a ⟩_) Cρᴰ Cuniᴰ c)) ⟩
                               (Σ[ b' ∈ B a ] (b B≅ᴰ⟨ ρ a ⟩ b')) × (Σ[ c' ∈ C a ] (c C≅ᴰ⟨ ρ a ⟩ c'))
                                 ≃⟨ Σ-assoc-≃ ⟩
                               (Σ[ b' ∈ B a ] Σ[ _ ∈ b B≅ᴰ⟨ ρ a ⟩ b' ] Σ[ c' ∈ C a ] (c C≅ᴰ⟨ ρ a ⟩ c'))
                                 ≃⟨ Σ-cong-equiv-snd (λ b' → compEquiv (invEquiv Σ-assoc-≃) (compEquiv (Σ-cong-equiv-fst Σ-swap-≃) Σ-assoc-≃)) ⟩
                               (Σ[ b' ∈ B a ] Σ[ c' ∈ C a ] Σ[ _ ∈ b B≅ᴰ⟨ ρ a ⟩ b' ] (c C≅ᴰ⟨ ρ a ⟩ c'))
                                 ≃⟨ invEquiv Σ-assoc-≃ ⟩
                               (Σ[ (b' , c') ∈ B a × C a ] (b B≅ᴰ⟨ ρ a ⟩ b' × c C≅ᴰ⟨ ρ a ⟩ c') ) ■)
                               (isUnivalent→contrTotalSpace (_B≅ᴰ⟨ ρ a ⟩_) Bρᴰ Buniᴰ b)
