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
open import Cubical.DStructures.Product

private
  variable
    ℓ ℓ' ℓ'' ℓ₁ ℓ₁' ℓ₁'' ℓ₂ ℓA ℓ≅A ℓB ℓ≅B ℓC ℓ≅C ℓ≅ᴰ ℓD ℓ≅D : Level

-- combine two structures StrB and StrC over StrA to a structure StrB × StrC over A
combine-𝒮ᴰ : {A : Type ℓA} {StrA : URGStr A ℓ≅A}
                 {B : A → Type ℓB} {C : A → Type ℓC}
                 (StrBᴰ : URGStrᴰ StrA B ℓ≅B)
                 (StrCᴰ : URGStrᴰ StrA C ℓ≅C)
                 → URGStrᴰ StrA (λ a → B a × C a) (ℓ-max ℓ≅B ℓ≅C)
combine-𝒮ᴰ {ℓ≅B = ℓ≅B} {ℓ≅C = ℓ≅C} {A = A} {StrA = StrA} {B = B} {C = C} StrBᴰ StrCᴰ =
  make-𝒮ᴰ -- equality in the combined structure is defined componentwise
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



-- context: structure on A, B and C displayed over A
-- then B can be lifted to be displayed over ∫⟨ StrA ⟩ StrCᴰ
VerticalLift-𝒮ᴰ : {A : Type ℓA} {StrA : URGStr A ℓ≅A}
        {B : A → Type ℓB}
        (StrBᴰ : URGStrᴰ StrA B ℓ≅B)
        {C : A → Type ℓC}
        (StrCᴰ : URGStrᴰ StrA C ℓ≅C)
        → URGStrᴰ (∫⟨ StrA ⟩ StrCᴰ) (λ (a , _) → B a) ℓ≅B
VerticalLift-𝒮ᴰ {ℓ≅B = ℓ≅B} {B = B} StrBᴰ StrCᴰ =
  urgstrᴰ (λ b (pA , _) b' → b ≅ᴰ⟨ pA ⟩ b')
          ρᴰ
          uniᴰ
  where open URGStrᴰ StrBᴰ

-- context: StrA on A, B and C displayed over StrA,
--          D displayed over ∫⟨ StrA ⟩ StrBᴰ
-- then D can be lifted to be displayed over ∫⟨ StrA ⟩ "B × C"
HorizontalLift-𝒮ᴰ : {A : Type ℓA} {StrA : URGStr A ℓ≅A}
                 {B : A → Type ℓB} (StrBᴰ : URGStrᴰ StrA B ℓ≅B)
                 {C : A → Type ℓC} (StrCᴰ : URGStrᴰ StrA C ℓ≅C)
                 {D : (Σ A B) → Type ℓD} (StrDᴰ : URGStrᴰ (∫⟨ StrA ⟩ StrBᴰ) D ℓ≅D)
                 → URGStrᴰ (∫⟨ StrA ⟩ combine-𝒮ᴰ StrBᴰ StrCᴰ)
                           (λ (a , b , _) → D (a , b)) ℓ≅D
HorizontalLift-𝒮ᴰ {ℓ≅D = ℓ≅D} StrBᴰ StrCᴰ {D} StrDᴰ =
  urgstrᴰ (λ d (p , q , r) d' → d ≅ᴰ⟨ p , q ⟩ d')
          ρᴰ
          uniᴰ
    where open URGStrᴰ StrDᴰ



-- context: StrA on A, StrBᴰ / A, StrCᴰ / ∫⟨StrA⟩ StrBᴰ
-- then StrCᴰ can be rebased to StrA
splitTotal-𝒮ᴰ : {A : Type ℓA} (StrA : URGStr A ℓ≅A)
                    {B : A → Type ℓB} (StrBᴰ : URGStrᴰ StrA B ℓ≅B)
                    {C : Σ A B → Type ℓC} (StrCᴰ : URGStrᴰ (∫⟨ StrA ⟩ StrBᴰ) C ℓ≅C)
                    → URGStrᴰ StrA
                              (λ a → Σ[ b ∈ B a ] C (a , b))
                              (ℓ-max ℓ≅B ℓ≅C)
splitTotal-𝒮ᴰ {A = A} StrA {B} StrBᴰ {C} StrCᴰ
  = make-𝒮ᴰ (λ (b , c) eA (b' , c') → Σ[ eB ∈ b B≅ᴰ⟨ eA ⟩ b' ] c ≅ᴰ⟨ eA , eB ⟩ c')
                (λ (b , c) → Bρᴰ b , ρᴰ c)
                λ a (b , c) → isOfHLevelRespectEquiv 0
                                                     (Σ[ c' ∈ C (a , b) ] c ≅ᴰ⟨ ρ a , Bρᴰ b ⟩ c'
                                                       ≃⟨ invEquiv (Σ-contractFst (contrTotalB' a b)) ⟩
                                                     Σ[ (b' , eB) ∈ Σ[ b' ∈ B a ] b B≅ᴰ⟨ ρ a ⟩ b' ] (Σ[ c' ∈ C (a , b') ] (c ≅ᴰ⟨ ρ a , eB ⟩ c'))
                                                       ≃⟨ compEquiv Σ-assoc-≃
                                                                    (compEquiv (Σ-cong-equiv-snd (λ b' → compEquiv (invEquiv Σ-assoc-≃)
                                                                                                                   (compEquiv (Σ-cong-equiv-fst Σ-swap-≃)
                                                                                                                              Σ-assoc-≃)))
                                                                               (invEquiv Σ-assoc-≃)) ⟩
                                                     Σ[ (b' , c') ∈ Σ[ b' ∈ B a ] C (a , b') ] (Σ[ eB ∈ b B≅ᴰ⟨ ρ a ⟩ b' ] (c ≅ᴰ⟨ ρ a , eB ⟩ c')) ■)
                                                     (contrTotalC a b c)

  where
    open URGStrᴰ StrCᴰ
    open URGStr StrA
    _B≅ᴰ⟨_⟩_ = URGStrᴰ._≅ᴰ⟨_⟩_ StrBᴰ
    Bρᴰ = URGStrᴰ.ρᴰ StrBᴰ
    Buniᴰ = URGStrᴰ.uniᴰ StrBᴰ

    module _ (a : A) (b : B a) where
      contrTotalB : isContr (Σ[ b' ∈ B a ] b B≅ᴰ⟨ ρ a ⟩ b')
      contrTotalB = isUnivalent→contrTotalSpace (_B≅ᴰ⟨ ρ a ⟩_) Bρᴰ Buniᴰ b

      contrTotalB' : isContr (Σ[ b' ∈ B a ] b B≅ᴰ⟨ ρ a ⟩ b')
      contrTotalB' = (b , Bρᴰ b) , λ z → sym (snd contrTotalB (b , Bρᴰ b)) ∙ snd contrTotalB z

      contrTotalC : (c : C (a , b)) → isContr (Σ[ c' ∈ C (a , b) ] c ≅ᴰ⟨ ρ a , Bρᴰ b ⟩ c')
      contrTotalC = isUnivalent→contrTotalSpace (λ c₁ c₂ → c₁ ≅ᴰ⟨ ρ a , Bρᴰ b ⟩ c₂) ρᴰ uniᴰ

{-
  this is obsolete as it is a special case of splitTotalURGStrᴰ

-- context: StrA on A, StrB on B and C family over A × B
-- then StrA and StrB induce ×URG-structure on A × B
-- and any C displayed over StrA × StrB can be transformed
-- to be displayed over StrA
-- TODO: Separate definition of fiberwise total space
splitProductURGStrᴰ : {ℓ≅C : Level}
                      {A : Type ℓA} {StrA : URGStr A ℓ≅A}
                      {B : Type ℓB} {StrB : URGStr B ℓ≅B}
                      {C : A × B → Type ℓC}
                      (StrCᴰ/B×A : URGStrᴰ (StrA ×URG StrB) C ℓ≅C)
                      → URGStrᴰ StrA (λ a → Σ[ b ∈ B ] C (a , b)) (ℓ-max ℓ≅B ℓ≅C)
splitProductURGStrᴰ {A = A} {StrA = StrA} {B = B} {StrB = StrB} {C = C} StrCᴰ/B×A
  = makeURGStrᴰ (λ (b , c) eA (b' , c') → Σ[ eB ∈ b B≅ b' ] (c ≅ᴰ⟨ eA , eB ⟩ c') )
                (λ (b , c) → Bρ b , ρᴰ c)
                λ a (b , c) → isOfHLevelRespectEquiv 0
                                                     (Σ[ c' ∈ C (a , b) ] (c ≅ᴰ⟨ Aρ a , Bρ b  ⟩ c')
                                                        ≃⟨ invEquiv (Σ-contractFst (contrTotalB' a b)) ⟩
                                                     Σ[ (b' , eB) ∈ (Σ[ b' ∈ B ] b B≅ b') ] Σ[ c' ∈ C (a , b') ] (c ≅ᴰ⟨ Aρ a , eB  ⟩ c')
                                                       ≃⟨ Σ-assoc-≃ ⟩
                                                     Σ[ b' ∈ B ] Σ[ eB ∈ b B≅ b' ] Σ[ c' ∈ C (a , b') ] (c ≅ᴰ⟨ Aρ a , eB  ⟩ c')
                                                       ≃⟨ Σ-cong-equiv-snd (λ b' → compEquiv (invEquiv Σ-assoc-≃) (compEquiv (Σ-cong-equiv-fst Σ-swap-≃) Σ-assoc-≃)) ⟩
                                                     Σ[ b' ∈ B ] Σ[ c' ∈ C (a , b') ] Σ[ eB ∈ b B≅ b' ] (c ≅ᴰ⟨ Aρ a , eB  ⟩ c')
                                                       ≃⟨ invEquiv Σ-assoc-≃ ⟩
                                                     Σ[ (b' , c') ∈ (Σ[ b' ∈ B ] C (a , b')) ] Σ[ eB ∈ b B≅ b' ] (c ≅ᴰ⟨ Aρ a , eB  ⟩ c') ■)
                                                     (isUnivalent→contrTotalSpace (λ c c' → c ≅ᴰ⟨ Aρ a , Bρ b ⟩ c') ρᴰ uniᴰ c)
  where
    open URGStrᴰ StrCᴰ/B×A
    _B≅_ = URGStr._≅_ StrB
    Bρ = URGStr.ρ StrB
    Buni = URGStr.uni StrB
    Aρ = URGStr.ρ StrA

    module _ (a : A) (b : B) where
      contrTotalB : isContr (Σ[ b' ∈ B ] b B≅ b')
      contrTotalB = isUnivalent→contrTotalSpace _B≅_ Bρ Buni b

      contrTotalB' : isContr (Σ[ b' ∈ B ] b B≅ b')
      contrTotalB' = (b , Bρ b) , λ z → sym (snd contrTotalB (b , Bρ b)) ∙ snd contrTotalB z

-}
