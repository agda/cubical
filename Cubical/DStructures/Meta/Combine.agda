{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Meta.Combine where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Relation.Binary


open import Cubical.DStructures.Base
open import Cubical.DStructures.Meta.Properties
open import Cubical.DStructures.Structures.Constant

private
  variable
    ℓ ℓ' ℓ'' ℓ₁ ℓ₁' ℓ₁'' ℓ₂ ℓA ℓ≅A ℓB ℓ≅B ℓC ℓ≅C ℓ≅ᴰ ℓD ℓ≅D ℓ≅X ℓX : Level

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
      → isContrRespectEquiv
                               (Σ[ b' ∈ B a ] (b B≅ᴰ⟨ ρ a ⟩ b')
                                 ≃⟨ invEquiv (Σ-contractSnd (λ _ → isUnivalent→contrRelSingl (_C≅ᴰ⟨ ρ a ⟩_) Cρᴰ Cuniᴰ c)) ⟩
                               (Σ[ b' ∈ B a ] (b B≅ᴰ⟨ ρ a ⟩ b')) × (Σ[ c' ∈ C a ] (c C≅ᴰ⟨ ρ a ⟩ c'))
                                 ≃⟨ Σ-assoc-≃ ⟩
                               (Σ[ b' ∈ B a ] Σ[ _ ∈ b B≅ᴰ⟨ ρ a ⟩ b' ] Σ[ c' ∈ C a ] (c C≅ᴰ⟨ ρ a ⟩ c'))
                                 ≃⟨ Σ-cong-equiv-snd (λ b' → compEquiv (invEquiv Σ-assoc-≃) (compEquiv (Σ-cong-equiv-fst Σ-swap-≃) Σ-assoc-≃)) ⟩
                               (Σ[ b' ∈ B a ] Σ[ c' ∈ C a ] Σ[ _ ∈ b B≅ᴰ⟨ ρ a ⟩ b' ] (c C≅ᴰ⟨ ρ a ⟩ c'))
                                 ≃⟨ invEquiv Σ-assoc-≃ ⟩
                               (Σ[ (b' , c') ∈ B a × C a ] (b B≅ᴰ⟨ ρ a ⟩ b' × c C≅ᴰ⟨ ρ a ⟩ c') ) ■)
                               (isUnivalent→contrRelSingl (_B≅ᴰ⟨ ρ a ⟩_) Bρᴰ Buniᴰ b)



-- context: structure on A, B and C displayed over A
-- then B can be lifted to be displayed over ∫⟨ StrA ⟩ StrCᴰ
VerticalLift-𝒮ᴰ : {A : Type ℓA} (StrA : URGStr A ℓ≅A)
        {B : A → Type ℓB}
        (StrBᴰ : URGStrᴰ StrA B ℓ≅B)
        {C : A → Type ℓC}
        (StrCᴰ : URGStrᴰ StrA C ℓ≅C)
        → URGStrᴰ (∫⟨ StrA ⟩ StrCᴰ) (λ (a , _) → B a) ℓ≅B
VerticalLift-𝒮ᴰ {ℓ≅B = ℓ≅B} StrA {B = B} StrBᴰ StrCᴰ =
  urgstrᴰ (λ b (pA , _) b' → b ≅ᴰ⟨ pA ⟩ b')
          ρᴰ
          uniᴰ
  where open URGStrᴰ StrBᴰ

VerticalLift2-𝒮ᴰ : {A : Type ℓA} (𝒮-A : URGStr A ℓ≅A)
                   {X : A → Type ℓX} (𝒮ᴰ-X : URGStrᴰ 𝒮-A X ℓ≅X)
                   {B : A → Type ℓB} (𝒮ᴰ-B : URGStrᴰ 𝒮-A B ℓ≅B)
                   {C : Σ A B → Type ℓC} (𝒮ᴰ-C : URGStrᴰ (∫⟨ 𝒮-A ⟩ 𝒮ᴰ-B) C ℓ≅C)
                   → URGStrᴰ (∫⟨ ∫⟨ 𝒮-A ⟩ 𝒮ᴰ-B ⟩ 𝒮ᴰ-C)
                             (λ ((a , b) , c) → X a)
                             ℓ≅X
VerticalLift2-𝒮ᴰ 𝒮-A 𝒮ᴰ-X 𝒮ᴰ-B 𝒮ᴰ-C =
  VerticalLift-𝒮ᴰ (∫⟨ 𝒮-A ⟩ 𝒮ᴰ-B)
                  (VerticalLift-𝒮ᴰ 𝒮-A 𝒮ᴰ-X 𝒮ᴰ-B)
                  𝒮ᴰ-C

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
                q

  where
    open URGStrᴰ StrCᴰ
    open URGStr StrA
    _B≅ᴰ⟨_⟩_ = URGStrᴰ._≅ᴰ⟨_⟩_ StrBᴰ
    Bρᴰ = URGStrᴰ.ρᴰ StrBᴰ
    Buniᴰ = URGStrᴰ.uniᴰ StrBᴰ

    module _ (a : A) (b : B a) where
      abstract
        contrTotalB : isContr (Σ[ b' ∈ B a ] b B≅ᴰ⟨ ρ a ⟩ b')
        contrTotalB = isUnivalent→contrRelSingl (_B≅ᴰ⟨ ρ a ⟩_) Bρᴰ Buniᴰ b

        contrTotalB' : isContr (Σ[ b' ∈ B a ] b B≅ᴰ⟨ ρ a ⟩ b')
        contrTotalB' = (b , Bρᴰ b) , λ z → sym (snd contrTotalB (b , Bρᴰ b)) ∙ snd contrTotalB z

        contrTotalC : (c : C (a , b)) → isContr (Σ[ c' ∈ C (a , b) ] c ≅ᴰ⟨ ρ a , Bρᴰ b ⟩ c')
        contrTotalC = isUnivalent→contrRelSingl (λ c₁ c₂ → c₁ ≅ᴰ⟨ ρ a , Bρᴰ b ⟩ c₂) ρᴰ uniᴰ

    abstract
      q = λ a (b , c) → isContrRespectEquiv
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


SplitTotal-𝒮ᴰ→RelFamily : {ℓ≅A ℓ≅B ℓ≅C : Level}
                          {A : Type ℓA} (𝒮-A : URGStr A ℓ≅A)
                          {B : A → Type ℓB} (𝒮ᴰ-B : URGStrᴰ 𝒮-A B ℓ≅B)
                          {C : Σ A B → Type ℓC} (𝒮ᴰ-C : URGStrᴰ (∫⟨ 𝒮-A ⟩ 𝒮ᴰ-B) C ℓ≅C)
                          → Σ[ _≅_ ∈ Rel A A ℓ≅A ]
                               ({a a' : A} ((b , c) : Σ[ b ∈ B a ] C (a , b)) (e : a ≅ a') ((b' , c') : (Σ[ b' ∈ B a' ] C (a' , b'))) → Type (ℓ-max ℓ≅B ℓ≅C))
SplitTotal-𝒮ᴰ→RelFamily 𝒮-A {B = B} 𝒮ᴰ-B {C = C} 𝒮ᴰ-C .fst = _≅_
  where
    open URGStr 𝒮-A
SplitTotal-𝒮ᴰ→RelFamily 𝒮-A {B = B} 𝒮ᴰ-B {C = C} 𝒮ᴰ-C .snd (b , c) e (b' , c') = Σ[ eB ∈ b B≅ᴰ⟨ e ⟩ b' ] (c ≅ᴰ⟨ e , eB ⟩ c')
  where
    open URGStr 𝒮-A
    _B≅ᴰ⟨_⟩_ = URGStrᴰ._≅ᴰ⟨_⟩_ 𝒮ᴰ-B
    open URGStrᴰ 𝒮ᴰ-C

SplitTotal-𝒮ᴰ→RelFamily' : {ℓ≅A ℓ≅B ℓ≅C : Level}
                          {A : Type ℓA} (𝒮-A : URGStr A ℓ≅A)
                          {B : A → Type ℓB} (𝒮ᴰ-B : URGStrᴰ 𝒮-A B ℓ≅B)
                          {C : Σ A B → Type ℓC} (𝒮ᴰ-C : URGStrᴰ (∫⟨ 𝒮-A ⟩ 𝒮ᴰ-B) C ℓ≅C)
                          → RelFamily A (ℓ-max ℓB ℓC) (ℓ-max ℓ≅B ℓ≅C)
SplitTotal-𝒮ᴰ→RelFamily' 𝒮-A {B = B} 𝒮ᴰ-B {C = C} 𝒮ᴰ-C .fst a = Σ[ b ∈ B a ] C (a , b)
SplitTotal-𝒮ᴰ→RelFamily' 𝒮-A {B = B} 𝒮ᴰ-B {C = C} 𝒮ᴰ-C .snd {a = a} (b , c) (b' , c') = Σ[ p ∈ b B≅ᴰ⟨ ρ a ⟩ b' ] (c C≅ᴰ⟨ ρ a , p ⟩ c')
  where
    open URGStr 𝒮-A
    _B≅ᴰ⟨_⟩_ = URGStrᴰ._≅ᴰ⟨_⟩_ 𝒮ᴰ-B
    _C≅ᴰ⟨_⟩_ = URGStrᴰ._≅ᴰ⟨_⟩_ 𝒮ᴰ-C









-- old stuff

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
                λ a (b , c) → isContrRespectEquiv
                                                     (Σ[ c' ∈ C (a , b) ] (c ≅ᴰ⟨ Aρ a , Bρ b  ⟩ c')
                                                        ≃⟨ invEquiv (Σ-contractFst (contrTotalB' a b)) ⟩
                                                     Σ[ (b' , eB) ∈ (Σ[ b' ∈ B ] b B≅ b') ] Σ[ c' ∈ C (a , b') ] (c ≅ᴰ⟨ Aρ a , eB  ⟩ c')
                                                       ≃⟨ Σ-assoc-≃ ⟩
                                                     Σ[ b' ∈ B ] Σ[ eB ∈ b B≅ b' ] Σ[ c' ∈ C (a , b') ] (c ≅ᴰ⟨ Aρ a , eB  ⟩ c')
                                                       ≃⟨ Σ-cong-equiv-snd (λ b' → compEquiv (invEquiv Σ-assoc-≃) (compEquiv (Σ-cong-equiv-fst Σ-swap-≃) Σ-assoc-≃)) ⟩
                                                     Σ[ b' ∈ B ] Σ[ c' ∈ C (a , b') ] Σ[ eB ∈ b B≅ b' ] (c ≅ᴰ⟨ Aρ a , eB  ⟩ c')
                                                       ≃⟨ invEquiv Σ-assoc-≃ ⟩
                                                     Σ[ (b' , c') ∈ (Σ[ b' ∈ B ] C (a , b')) ] Σ[ eB ∈ b B≅ b' ] (c ≅ᴰ⟨ Aρ a , eB  ⟩ c') ■)
                                                     (isUnivalent→contrRelSingl (λ c c' → c ≅ᴰ⟨ Aρ a , Bρ b ⟩ c') ρᴰ uniᴰ c)
  where
    open URGStrᴰ StrCᴰ/B×A
    _B≅_ = URGStr._≅_ StrB
    Bρ = URGStr.ρ StrB
    Buni = URGStr.uni StrB
    Aρ = URGStr.ρ StrA

    module _ (a : A) (b : B) where
      contrTotalB : isContr (Σ[ b' ∈ B ] b B≅ b')
      contrTotalB = isUnivalent→contrRelSingl _B≅_ Bρ Buni b

      contrTotalB' : isContr (Σ[ b' ∈ B ] b B≅ b')
      contrTotalB' = (b , Bρ b) , λ z → sym (snd contrTotalB (b , Bρ b)) ∙ snd contrTotalB z

-}
