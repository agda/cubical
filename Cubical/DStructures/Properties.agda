{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma

open import Cubical.Relation.Binary
open BinaryRelation

open import Cubical.DStructures.Base

private
  variable
    ℓ ℓ' ℓ'' ℓ₁ ℓ₁' ℓ₁'' ℓ₂ ℓA ℓ≅A ℓB ℓ≅B ℓC ℓ≅C ℓ≅ᴰ : Level

-- the total space of a DURGS is a URGS
URGStrᴰ→URGStr : {A : Type ℓA} (StrA : URGStr A ℓ≅A)
                 (B : A → Type ℓB) (DispStrB : URGStrᴰ StrA B ℓ≅B)
                 → URGStr (Σ A B) (ℓ-max ℓ≅A ℓ≅B)
URGStrᴰ→URGStr {A = A} StrA B DispStrB
  = makeURGStr {_≅_ = _≅Σ_} ρΣ contrTotalΣ
  where
   -- import notation: ≅ for StrA and ≅ᴰ for StrBᴰ
   open URGStr StrA
   open URGStrᴰ DispStrB

   -- in the context of a fixed point (a , b)
   module _ ((a , b) : Σ A B) where
     -- the graph relation on the total space
     _≅Σ_ = λ ((a' , b') : Σ A B)
              → Σ[ e ∈ a ≅ a' ] (b ≅ᴰ⟨ e ⟩ b')
     -- reflexivity for that relation
     ρΣ = ρ a , ρᴰ b
     -- contractability of the corresponding total space
     contrTotalA : isContr (Σ[ a' ∈ A ] (a ≅ a'))
     contrTotalA = isUnivalent→contrTotalSpace _≅_ ρ uni a
     contrTotalA' : isContr (Σ[ a' ∈ A ] (a ≅ a'))
     contrTotalA' = (a , ρ a) , λ z → sym (snd contrTotalA (a , ρ a)) ∙ snd contrTotalA z
     contrTotalB : isContr (Σ[ b' ∈ B a ] (b ≅ᴰ⟨ ρ a ⟩ b'))
     contrTotalB = isUnivalent→contrTotalSpace (_≅ᴰ⟨ ρ a ⟩_) ρᴰ uniᴰ b

     contrTotalΣ
       = isOfHLevelRespectEquiv 0
                                (Rel→TotalSpace (_≅ᴰ⟨ ρ a ⟩_) b
                                  ≃⟨ idEquiv (Rel→TotalSpace (_≅ᴰ⟨ ρ a ⟩_) b) ⟩
                                Σ[ b' ∈ B a ] (b ≅ᴰ⟨ ρ a ⟩ b')
                                  ≃⟨ invEquiv (Σ-contractFst contrTotalA') ⟩
                                Σ[ (a' , e) ∈ (Σ[ a' ∈ A ] (a ≅ a')) ] Σ[ b' ∈ B a' ] (b ≅ᴰ⟨ e ⟩ b')
                                  ≃⟨ Σ-assoc-≃ ⟩
                                Σ[ a' ∈ A ] Σ[ e ∈ (a ≅ a') ] Σ[ b' ∈ B a' ] (b ≅ᴰ⟨ e ⟩ b')
                                  ≃⟨ Σ-cong-equiv-snd (λ a' → invEquiv Σ-assoc-≃) ⟩
                                Σ[ a' ∈ A ] Σ[ (e , b') ∈ (a ≅ a') × B a' ] (b ≅ᴰ⟨ e ⟩ b')
                                  ≃⟨ Σ-cong-equiv-snd (λ a' → Σ-cong-equiv-fst Σ-swap-≃) ⟩
                                Σ[ a' ∈ A ] Σ[ (b' , e) ∈ (B a' × (a ≅ a')) ] (b ≅ᴰ⟨ e ⟩ b')
                                  ≃⟨ Σ-cong-equiv-snd (λ a' → Σ-assoc-≃) ⟩
                                Σ[ a' ∈ A ] Σ[ b' ∈ B a' ] Σ[ e ∈ (a ≅ a') ] (b ≅ᴰ⟨ e ⟩ b')
                                  ≃⟨ invEquiv Σ-assoc-≃ ⟩
                                Σ[ (a' , b') ∈ Σ A B ] Σ[ e ∈ (a ≅ a') ] (b ≅ᴰ⟨ e ⟩ b') ■)
                                contrTotalB

-- integral notation like in the disp cats paper
∫⟨_⟩_ : {A : Type ℓA} (StrA : URGStr A ℓ≅A)
                 {B : A → Type ℓB} (DispStrB : URGStrᴰ StrA B ℓ≅B)
                 → URGStr (Σ A B) (ℓ-max ℓ≅A ℓ≅B)
∫⟨_⟩_ StrA {B} DispStrB = URGStrᴰ→URGStr StrA B DispStrB

-- associativity for towers
module Assoc {ℓA ℓB ℓC ℓ≅A ℓ≅B ℓ≅C : Level}
             {A : Type ℓ} {B : A → Type ℓB} {C : {a : A} → B a → Type ℓC}
             (StrA : URGStr A ℓ≅A) where

  ℓ≅ABC = ℓ-max (ℓ-max ℓ≅A ℓ≅B) ℓ≅C
  ℓ≅AB = ℓ-max ℓ≅A ℓ≅B
  ℓ≅BC = ℓ-max ℓ≅B ℓ≅C

  StrCᴰB/A = Σ[ StrB/A ∈ URGStr (Σ A B) ℓ≅AB ] URGStrᴰ StrB/A (λ (a , b) → C b) ℓ≅C
  StrCBᴰ/A = Σ[ StrA ∈ URGStr A ℓ≅A ] URGStrᴰ StrA (λ a → Σ[ b ∈ B a ] C b) ℓ≅BC
  StrC/BA = URGStr (Σ[ a ∈ A ] Σ[ b ∈ B a ] C b) ℓ≅ABC
  StrCB/A = URGStr (Σ[ (a , b) ∈ Σ[ a ∈ A ] B a ] C b) ℓ≅ABC

  f : StrCᴰB/A → StrCB/A
  f (StrB/A , StrCᴰ) = ∫⟨ StrB/A ⟩ StrCᴰ

  g : StrCBᴰ/A → StrC/BA
  g (StrA , StrCBᴰ) = ∫⟨ StrA ⟩ StrCBᴰ

  URGΣAssoc : StrCB/A ≡ StrC/BA
  URGΣAssoc = cong (λ z → URGStr z ℓ≅ABC) (isoToPath Σ-assoc-Iso)

module Combine where
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
