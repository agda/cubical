
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Structures.Type where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.Univalence

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Relation.Binary


open import Cubical.DStructures.Base
open import Cubical.DStructures.Meta.Properties

private
  variable
    ℓ ℓ' ℓ'' ℓ₁ ℓ₁' ℓ₁'' ℓ₂ ℓA ℓ≅A ℓB ℓ≅B ℓ≅ᴰ ℓP : Level

-- a type is a URGStr with the relation given by its identity type
𝒮-type : (A : Type ℓ) → URGStr A ℓ
𝒮-type A = make-𝒮 {_≅_ = _≡_} (λ _ → refl) isContrSingl

-- subtypes are displayed structures
𝒮ᴰ-subtype : {A : Type ℓ} (P : A → hProp ℓ')
             → URGStrᴰ (𝒮-type A)
                       (λ a → P a .fst)
                       ℓ-zero
𝒮ᴰ-subtype P
  = make-𝒮ᴰ (λ _ _ _ → Unit)
            (λ _ → tt)
            λ a p → isContrRespectEquiv (invEquiv (Σ-contractSnd (λ _ → isContrUnit)))
                                        (inhProp→isContr p (P a .snd))

-- a subtype induces a URG structure on itself
Subtype→Sub-𝒮ᴰ : {A : Type ℓA} (P : A → hProp ℓP)
                (StrA : URGStr A ℓ≅A)
                → URGStrᴰ StrA (λ a → P a .fst) ℓ-zero
Subtype→Sub-𝒮ᴰ P StrA =
  make-𝒮ᴰ (λ _ _ _ → Unit)
              (λ _ → tt)
              (λ a p → isContrRespectEquiv
                                              (invEquiv (Σ-contractSnd (λ _ → isContrUnit)))
                                              (inhProp→isContr p (P a .snd)))


module _ {A : Type ℓA} (𝒮 : URGStr A ℓA) where
  open URGStr
  𝒮' = 𝒮-type A

  ≅-≡ : _≅_ 𝒮' ≡ _≅_ 𝒮
  ≅-≡ = funExt₂ (λ a a' → ua (isUnivalent→isUnivalent' (_≅_ 𝒮) (ρ 𝒮) (uni 𝒮) a a'))

  ρ-≡ : PathP (λ i → isRefl (≅-≡ i)) (ρ 𝒮') (ρ 𝒮)
  ρ-≡ = funExt (λ a → toPathP (p a))
    where
      -- p : (a : A) → transp (λ i → ≅-≡ i a a) i0 refl ≡ (ρ 𝒮 a)
      module _ (a : A) where
        p : transport (λ i → ≅-≡ i a a) refl ≡ (ρ 𝒮 a)
        p a = uaβ {!!} refl
        p2 : transport (λ i → ≅-≡ i a a) refl ≡ {!!}
        p2 a = transportRefl {!!}


      q₁ : (a : A) → ≡→R (_≅_ 𝒮) (ρ 𝒮) refl ≡ subst ((_≅_ 𝒮) a) refl (ρ 𝒮 a)
      q₁ a = refl
      q₂ : (a : A) → subst (λ a' → (_≅_ 𝒮) a a') refl (ρ 𝒮 a) ≡ ρ 𝒮 a
      q₂ a = transportRefl (ρ 𝒮 a)

  uni-≡ : PathP (λ i → isUnivalent (≅-≡ i) (ρ-≡ i)) (uni 𝒮') (uni 𝒮)
  uni-≡ = isProp→PathP (λ i → isPropΠ2 (λ a a' → isPropIsEquiv (≡→R (≅-≡ i) (ρ-≡ i)))) (uni 𝒮') (uni 𝒮)


{-


module Sigma {ℓA ℓB ℓ≅A ℓ≅B} {A : Type ℓA} {B : A → Type ℓB} where
  ℓ≅AB = ℓ-max ℓ≅A ℓ≅B

  -- structures on Σ A B
  URGStrΣ = URGStr (Σ A B) ℓ≅AB
  -- structures on A with a displayed structure on top
  ΣURGStrᴰ = Σ[ StrA ∈ URGStr A ℓ≅A ] (URGStrᴰ StrA (λ a → B a) ℓ≅B)

  Σ∫ : ΣURGStrᴰ → URGStrΣ
  Σ∫ (StrA , StrBᴰ) = ∫⟨ StrA ⟩ StrBᴰ

module Sigma' {ℓA ℓB ℓ≅B} {A : Type ℓA} {B : A → Type ℓA} where
  open Sigma {ℓ≅A = ℓA} {ℓ≅B = ℓA} {A = A} {B = B}
  -- inverse to Σ∫
  ΣΔ : URGStrΣ → ΣURGStrᴰ
  fst (ΣΔ StrBA) = URGStrType A
  snd (ΣΔ StrBA) = makeURGStrᴰ B
                               ℓA
                               (λ {a} {a'} b p b' → (a , b) ≅ (a' , b'))
                               (λ b → ρ (_ , b))
                               λ a b → isContrRespectEquiv
                                                              (Σ[ b' ∈ B a ] b ≡ b'
                                                                ≃⟨ Σ-cong-equiv-snd (λ b' → compEquiv {!!}
                                                                                                      ((≡→R _≅_ ρ) , (uni (a , b) (a , b')))) ⟩
                                                              Σ[ b' ∈ B a ] (a , b) ≅ (a , b') ■)
                                                              (isContrSingl b)
                               where
                                 open URGStr StrBA

-}
