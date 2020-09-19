
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


𝒮ᴰ-type : {A : Type ℓA} (B : A → Type ℓB)
          → URGStrᴰ (𝒮-type A) B ℓB
𝒮ᴰ-type {A = A} B = make-𝒮ᴰ (λ b p b' → PathP (λ i → B (p i)) b b')
                    (λ _ → refl)
                    λ _ b → isContrSingl b


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
      p : (a : A) → transport (λ i → ≅-≡ i a a) refl ≡ (ρ 𝒮 a)
      p a = uaβ (isUnivalent→isUnivalent' (_≅_ 𝒮) (ρ 𝒮) (uni 𝒮) a a) refl ∙ transportRefl (ρ 𝒮 a)

      u : (a : A) → (transport (λ i → ≅-≡ i a a) refl) ≡ (subst (λ a' → (_≅_ 𝒮) a a') refl (ρ 𝒮 a))
      u a =  uaβ (isUnivalent→isUnivalent' (_≅_ 𝒮) (ρ 𝒮) (uni 𝒮) a a) refl 

{-
      q₁ : (a : A) → ≡→R (_≅_ 𝒮) (ρ 𝒮) refl ≡ subst ((_≅_ 𝒮) a) refl (ρ 𝒮 a)
      q₁ a = refl
      q₂ : (a : A) → subst (λ a' → (_≅_ 𝒮) a a') refl (ρ 𝒮 a) ≡ ρ 𝒮 a
      q₂ a = transportRefl (ρ 𝒮 a)
-}

  uni-≡ : PathP (λ i → isUnivalent (≅-≡ i) (ρ-≡ i)) (uni 𝒮') (uni 𝒮)
  uni-≡ = isProp→PathP (λ i → isPropΠ2 (λ a a' → isPropIsEquiv (≡→R (≅-≡ i) (ρ-≡ i)))) (uni 𝒮') (uni 𝒮)

𝒮-uniqueness : (A : Type ℓA) → isContr (URGStr A ℓA)
𝒮-uniqueness A .fst = 𝒮-type A
𝒮-uniqueness A .snd 𝒮 = sym (η-URGStr (𝒮-type A)) ∙∙ (λ i → p i) ∙∙ η-URGStr 𝒮
  where
    p = λ (i : I) → urgstr (≅-≡ 𝒮 i) (ρ-≡ 𝒮 i) (uni-≡ 𝒮 i)

