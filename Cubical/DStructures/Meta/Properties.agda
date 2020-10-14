{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Meta.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.Sigma

open import Cubical.Relation.Binary

open import Cubical.DStructures.Base

private
  variable
    ℓ ℓ' ℓ'' ℓ₁ ℓ₁' ℓ₁'' ℓ₂ ℓA ℓA' ℓ≅A ℓ≅A' ℓB ℓB' ℓ≅B ℓC ℓ≅C ℓ≅ᴰ ℓ≅ᴰ' ℓX ℓ≅X ℓD ℓ≅D : Level

-- the total space of a DURGS is a URGS
𝒮ᴰ→𝒮 : {A : Type ℓA} (𝒮-A : URGStr A ℓ≅A)
        {B : A → Type ℓB} (𝒮ᴰ-B : URGStrᴰ 𝒮-A B ℓ≅B)
        → URGStr (Σ A B) (ℓ-max ℓ≅A ℓ≅B)
𝒮ᴰ→𝒮 {A = A} 𝒮-A {B = B} 𝒮ᴰ-B
  = make-𝒮 {_≅_ = _≅Σ_} ρΣ contrTotalΣ
  where
   open URGStr 𝒮-A
   open URGStrᴰ 𝒮ᴰ-B

   -- in the context of a fixed point (a , b)
   module _ ((a , b) : Σ A B) where
     -- the graph relation on the total space
     _≅Σ_ = λ ((a' , b') : Σ A B)
              → Σ[ e ∈ a ≅ a' ] (b ≅ᴰ⟨ e ⟩ b')
     -- reflexivity for that relation
     ρΣ = ρ a , ρᴰ b
     -- contractability of the corresponding total space
     contrTotalA : isContr (Σ[ a' ∈ A ] (a ≅ a'))
     contrTotalA = isUnivalent→contrRelSingl _≅_ ρ uni a
     contrTotalB : isContr (Σ[ b' ∈ B a ] (b ≅ᴰ⟨ ρ a ⟩ b'))
     contrTotalB = isUnivalent→contrRelSingl (_≅ᴰ⟨ ρ a ⟩_) ρᴰ uniᴰ b

     contrTotalΣ
       = isContrRespectEquiv (relSinglAt (_≅ᴰ⟨ ρ a ⟩_) b
                                  ≃⟨ idEquiv (relSinglAt (_≅ᴰ⟨ ρ a ⟩_) b) ⟩
                                Σ[ b' ∈ B a ] (b ≅ᴰ⟨ ρ a ⟩ b')
                                  -- ≃⟨ invEquiv (Σ-contractFst contrTotalA') ⟩
                                  ≃⟨ invEquiv (Σ-contractFst-recenter contrTotalA (a , ρ a)) ⟩
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
∫⟨_⟩_ : {A : Type ℓA} (𝒮-A : URGStr A ℓ≅A)
       {B : A → Type ℓB} (𝒮ᴰ-B : URGStrᴰ 𝒮-A B ℓ≅B)
       → URGStr (Σ A B) (ℓ-max ℓ≅A ℓ≅B)
∫⟨_⟩_ 𝒮-A {B} DispStrB .URGStr._≅_ = 𝒮ᴰ→𝒮 𝒮-A DispStrB .URGStr._≅_
∫⟨_⟩_ 𝒮-A {B} DispStrB .URGStr.ρ = 𝒮ᴰ→𝒮 𝒮-A DispStrB .URGStr.ρ
∫⟨_⟩_ 𝒮-A {B} DispStrB .URGStr.uni = 𝒮ᴰ→𝒮 𝒮-A DispStrB .URGStr.uni


-- transport URG structures along an equivalence
𝒮-transport : {A : Type ℓA} {A' : Type ℓA'}
               (e : A ≃ A') (StrA : URGStr A ℓ≅A)
               → URGStr A' ℓ≅A
𝒮-transport {A = A} {A' = A'} e StrA =
  make-𝒮 {_≅_ = λ a a' → e- a ≅ e- a'}
             (λ a → ρ (e- a))
             λ a → isContrRespectEquiv (Σ[ x ∈ A ] e- a ≅ x
                                           ≃⟨ Σ-cong-equiv-snd (λ x → pathToEquiv (cong (e- a ≅_)
                                                                                        (sym (Iso.leftInv (equivToIso e)
                                                                                                           x)))) ⟩
                                       Σ[ x ∈ A ] e- a ≅ e- (e* x)
                                          ≃⟨ Σ-cong-equiv-fst e ⟩
                                       Σ[ a' ∈ A' ] e- a ≅ e- a' ■)
                                         (𝒮→cTS StrA (e- a))
                                       where
                                         open URGStr StrA
                                         e⁻¹ = invEquiv e
                                         e- = equivFun e⁻¹
                                         e* = equivFun e


-- obtain a path from a relation
𝒮-≅→≡ : {A : Type ℓA} (𝒮-A : URGStr A ℓ≅A)
          {a a' : A} (p : URGStr._≅_ 𝒮-A a a')
          → a ≡ a'
𝒮-≅→≡ 𝒮-A {a} {a'} p = equivFun (invEquiv (isUnivalent→isUnivalent' _≅_ ρ uni a a')) p
  where
    open URGStr 𝒮-A


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

-- pullback in the (∞,1)-topos of DURGs,
-- combine two DURGs over the same URG to one
combine-𝒮ᴰ : {A : Type ℓA} {𝒮-A : URGStr A ℓ≅A}
             {B : A → Type ℓB} {C : A → Type ℓC}
             (𝒮ᴰ-B : URGStrᴰ 𝒮-A B ℓ≅B)
             (𝒮ᴰ-C : URGStrᴰ 𝒮-A C ℓ≅C)
             → URGStrᴰ 𝒮-A (λ a → B a × C a) (ℓ-max ℓ≅B ℓ≅C)
combine-𝒮ᴰ {𝒮-A = 𝒮-A} 𝒮ᴰ-B 𝒮ᴰ-C = splitTotal-𝒮ᴰ 𝒮-A 𝒮ᴰ-B (VerticalLift-𝒮ᴰ 𝒮-A 𝒮ᴰ-C 𝒮ᴰ-B)







-- old stuff, not sure if relevant

-- extract the relational family from a DURG
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



-- combine two structures 𝒮-B and 𝒮-C over 𝒮-A to a structure 𝒮-B × 𝒮-C over A, direct proof
combine'-𝒮ᴰ : {A : Type ℓA} {𝒮-A : URGStr A ℓ≅A}
                 {B : A → Type ℓB} {C : A → Type ℓC}
                 (𝒮ᴰ-B : URGStrᴰ 𝒮-A B ℓ≅B)
                 (𝒮ᴰ-C : URGStrᴰ 𝒮-A C ℓ≅C)
                 → URGStrᴰ 𝒮-A (λ a → B a × C a) (ℓ-max ℓ≅B ℓ≅C)
combine'-𝒮ᴰ {ℓ≅B = ℓ≅B} {ℓ≅C = ℓ≅C} {A = A} {𝒮-A = 𝒮-A} {B = B} {C = C} 𝒮ᴰ-B 𝒮ᴰ-C =
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
      → isContrRespectEquiv (Σ[ b' ∈ B a ] (b B≅ᴰ⟨ ρ a ⟩ b')
                                 ≃⟨ invEquiv (Σ-contractSnd (λ _ → isUnivalent→contrRelSingl (_C≅ᴰ⟨ ρ a ⟩_) Cρᴰ Cuniᴰ c)) ⟩
                               (Σ[ b' ∈ B a ] (b B≅ᴰ⟨ ρ a ⟩ b')) × (Σ[ c' ∈ C a ] (c C≅ᴰ⟨ ρ a ⟩ c'))
                                 ≃⟨ Σ-assoc-≃ ⟩
                               (Σ[ b' ∈ B a ] Σ[ _ ∈ b B≅ᴰ⟨ ρ a ⟩ b' ] Σ[ c' ∈ C a ] (c C≅ᴰ⟨ ρ a ⟩ c'))
                                 ≃⟨ Σ-cong-equiv-snd (λ b' → compEquiv (invEquiv Σ-assoc-≃) (compEquiv (Σ-cong-equiv-fst Σ-swap-≃) Σ-assoc-≃)) ⟩
                               (Σ[ b' ∈ B a ] Σ[ c' ∈ C a ] Σ[ _ ∈ b B≅ᴰ⟨ ρ a ⟩ b' ] (c C≅ᴰ⟨ ρ a ⟩ c'))
                                 ≃⟨ invEquiv Σ-assoc-≃ ⟩
                               (Σ[ (b' , c') ∈ B a × C a ] (b B≅ᴰ⟨ ρ a ⟩ b' × c C≅ᴰ⟨ ρ a ⟩ c') ) ■)
                               (isUnivalent→contrRelSingl (_B≅ᴰ⟨ ρ a ⟩_) Bρᴰ Buniᴰ b)
