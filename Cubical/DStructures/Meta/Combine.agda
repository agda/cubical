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

-- combine two structures 𝒮-B and 𝒮-C over 𝒮-A to a structure 𝒮-B × 𝒮-C over A
combine-𝒮ᴰ : {A : Type ℓA} {𝒮-A : URGStr A ℓ≅A}
                 {B : A → Type ℓB} {C : A → Type ℓC}
                 (𝒮ᴰ-B : URGStrᴰ 𝒮-A B ℓ≅B)
                 (𝒮ᴰ-C : URGStrᴰ 𝒮-A C ℓ≅C)
                 → URGStrᴰ 𝒮-A (λ a → B a × C a) (ℓ-max ℓ≅B ℓ≅C)
combine-𝒮ᴰ {ℓ≅B = ℓ≅B} {ℓ≅C = ℓ≅C} {A = A} {𝒮-A = 𝒮-A} {B = B} {C = C} 𝒮ᴰ-B 𝒮ᴰ-C =
  make-𝒮ᴰ -- equality in the combined structure is defined componentwise
              (λ (b , c) p (b' , c') → b B≅ᴰ⟨ p ⟩ b' × c C≅ᴰ⟨ p ⟩ c')
              -- reflexivity follows from B and C reflexivity
              (λ (b , c) → Bρᴰ b , Cρᴰ c)
              -- so does univalence
              contrTot
  where
    ρ = URGStr.ρ 𝒮-A
    _B≅ᴰ⟨_⟩_ = URGStrᴰ._≅ᴰ⟨_⟩_ 𝒮ᴰ-B
    _C≅ᴰ⟨_⟩_ = URGStrᴰ._≅ᴰ⟨_⟩_ 𝒮ᴰ-C
    Bρᴰ = URGStrᴰ.ρᴰ 𝒮ᴰ-B
    Cρᴰ = URGStrᴰ.ρᴰ 𝒮ᴰ-C
    Buniᴰ = URGStrᴰ.uniᴰ 𝒮ᴰ-B
    Cuniᴰ = URGStrᴰ.uniᴰ 𝒮ᴰ-C
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
-- then B can be lifted to be displayed over ∫⟨ 𝒮-A ⟩ 𝒮ᴰ-C
VerticalLift-𝒮ᴰ : {A : Type ℓA} (𝒮-A : URGStr A ℓ≅A)
        {B : A → Type ℓB}
        (𝒮ᴰ-B : URGStrᴰ 𝒮-A B ℓ≅B)
        {C : A → Type ℓC}
        (𝒮ᴰ-C : URGStrᴰ 𝒮-A C ℓ≅C)
        → URGStrᴰ (∫⟨ 𝒮-A ⟩ 𝒮ᴰ-C) (λ (a , _) → B a) ℓ≅B
VerticalLift-𝒮ᴰ {ℓ≅B = ℓ≅B} 𝒮-A {B = B} 𝒮ᴰ-B 𝒮ᴰ-C =
  urgstrᴰ (λ b (pA , _) b' → b ≅ᴰ⟨ pA ⟩ b')
          ρᴰ
          uniᴰ
  where open URGStrᴰ 𝒮ᴰ-B

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

-- context: 𝒮-A on A, B and C displayed over 𝒮-A,
--          D displayed over ∫⟨ 𝒮-A ⟩ 𝒮ᴰ-B
-- then D can be lifted to be displayed over ∫⟨ 𝒮-A ⟩ "B × C"
HorizontalLift-𝒮ᴰ : {A : Type ℓA} {𝒮-A : URGStr A ℓ≅A}
                 {B : A → Type ℓB} (𝒮ᴰ-B : URGStrᴰ 𝒮-A B ℓ≅B)
                 {C : A → Type ℓC} (𝒮ᴰ-C : URGStrᴰ 𝒮-A C ℓ≅C)
                 {D : (Σ A B) → Type ℓD} (StrDᴰ : URGStrᴰ (∫⟨ 𝒮-A ⟩ 𝒮ᴰ-B) D ℓ≅D)
                 → URGStrᴰ (∫⟨ 𝒮-A ⟩ combine-𝒮ᴰ 𝒮ᴰ-B 𝒮ᴰ-C)
                           (λ (a , b , _) → D (a , b)) ℓ≅D
HorizontalLift-𝒮ᴰ {ℓ≅D = ℓ≅D} 𝒮ᴰ-B 𝒮ᴰ-C {D} StrDᴰ =
  urgstrᴰ (λ d (p , q , r) d' → d ≅ᴰ⟨ p , q ⟩ d')
          ρᴰ
          uniᴰ
    where open URGStrᴰ StrDᴰ


-- context: 𝒮-A on A, 𝒮ᴰ-B / A, 𝒮ᴰ-C / ∫⟨𝒮-A⟩ 𝒮ᴰ-B
-- then 𝒮ᴰ-C can be rebased to 𝒮-A
splitTotal-𝒮ᴰ : {A : Type ℓA} (𝒮-A : URGStr A ℓ≅A)
                    {B : A → Type ℓB} (𝒮ᴰ-B : URGStrᴰ 𝒮-A B ℓ≅B)
                    {C : Σ A B → Type ℓC} (𝒮ᴰ-C : URGStrᴰ (∫⟨ 𝒮-A ⟩ 𝒮ᴰ-B) C ℓ≅C)
                    → URGStrᴰ 𝒮-A
                              (λ a → Σ[ b ∈ B a ] C (a , b))
                              (ℓ-max ℓ≅B ℓ≅C)
splitTotal-𝒮ᴰ {A = A} 𝒮-A {B} 𝒮ᴰ-B {C} 𝒮ᴰ-C
  = make-𝒮ᴰ (λ (b , c) eA (b' , c') → Σ[ eB ∈ b B≅ᴰ⟨ eA ⟩ b' ] c ≅ᴰ⟨ eA , eB ⟩ c')
                (λ (b , c) → Bρᴰ b , ρᴰ c)
                q

  where
    open URGStrᴰ 𝒮ᴰ-C
    open URGStr 𝒮-A
    _B≅ᴰ⟨_⟩_ = URGStrᴰ._≅ᴰ⟨_⟩_ 𝒮ᴰ-B
    Bρᴰ = URGStrᴰ.ρᴰ 𝒮ᴰ-B
    Buniᴰ = URGStrᴰ.uniᴰ 𝒮ᴰ-B

    module _ (a : A) (b : B a) where
      abstract
        contrTotalB : isContr (Σ[ b' ∈ B a ] b B≅ᴰ⟨ ρ a ⟩ b')
        contrTotalB = isUnivalent→contrRelSingl (_B≅ᴰ⟨ ρ a ⟩_) Bρᴰ Buniᴰ b

        contrTotalC : (c : C (a , b)) → isContr (Σ[ c' ∈ C (a , b) ] c ≅ᴰ⟨ ρ a , Bρᴰ b ⟩ c')
        contrTotalC = isUnivalent→contrRelSingl (λ c₁ c₂ → c₁ ≅ᴰ⟨ ρ a , Bρᴰ b ⟩ c₂) ρᴰ uniᴰ

    abstract
      q = λ a (b , c) → isContrRespectEquiv (Σ[ c' ∈ C (a , b) ] c ≅ᴰ⟨ ρ a , Bρᴰ b ⟩ c'
                                                       ≃⟨ invEquiv (Σ-contractFst-recenter (contrTotalB a b) (b , Bρᴰ b)) ⟩
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

-- context: 𝒮-A on A, 𝒮-B on B and C family over A × B
-- then 𝒮-A and 𝒮-B induce ×URG-structure on A × B
-- and any C displayed over 𝒮-A × 𝒮-B can be transformed
-- to be displayed over 𝒮-A
-- TODO: Separate definition of fiberwise total space
splitProductURGStrᴰ : {ℓ≅C : Level}
                      {A : Type ℓA} {𝒮-A : URGStr A ℓ≅A}
                      {B : Type ℓB} {𝒮-B : URGStr B ℓ≅B}
                      {C : A × B → Type ℓC}
                      (𝒮ᴰ-C/B×A : URGStrᴰ (𝒮-A ×URG 𝒮-B) C ℓ≅C)
                      → URGStrᴰ 𝒮-A (λ a → Σ[ b ∈ B ] C (a , b)) (ℓ-max ℓ≅B ℓ≅C)
splitProductURGStrᴰ {A = A} {𝒮-A = 𝒮-A} {B = B} {𝒮-B = 𝒮-B} {C = C} 𝒮ᴰ-C/B×A
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
    open URGStrᴰ 𝒮ᴰ-C/B×A
    _B≅_ = URGStr._≅_ 𝒮-B
    Bρ = URGStr.ρ 𝒮-B
    Buni = URGStr.uni 𝒮-B
    Aρ = URGStr.ρ 𝒮-A

    module _ (a : A) (b : B) where
      contrTotalB : isContr (Σ[ b' ∈ B ] b B≅ b')
      contrTotalB = isUnivalent→contrRelSingl _B≅_ Bρ Buni b

      contrTotalB' : isContr (Σ[ b' ∈ B ] b B≅ b')
      contrTotalB' = (b , Bρ b) , λ z → sym (snd contrTotalB (b , Bρ b)) ∙ snd contrTotalB z

-}
