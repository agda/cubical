{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.Sigma

open import Cubical.Relation.Binary
open BinaryRelation

open import Cubical.DStructures.Base

private
  variable
    ℓ ℓ' ℓ'' ℓ₁ ℓ₁' ℓ₁'' ℓ₂ ℓA ℓA' ℓ≅A ℓ≅A' ℓB ℓB' ℓ≅B ℓC ℓ≅C ℓ≅ᴰ ℓ≅ᴰ' : Level

-- the total space of a DURGS is a URGS
𝒮ᴰ→𝒮 : {A : Type ℓA} (StrA : URGStr A ℓ≅A)
                 (B : A → Type ℓB) (DispStrB : URGStrᴰ StrA B ℓ≅B)
                 → URGStr (Σ A B) (ℓ-max ℓ≅A ℓ≅B)
𝒮ᴰ→𝒮 {A = A} StrA B DispStrB
  = make-𝒮 {_≅_ = _≅Σ_} ρΣ contrTotalΣ
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
∫⟨_⟩_ StrA {B} DispStrB = 𝒮ᴰ→𝒮 StrA B DispStrB

-- associativity for towers
module Assoc {ℓA ℓB ℓC ℓ≅A ℓ≅B ℓ≅C : Level}
             {A : Type ℓ} {B : A → Type ℓB} {C : {a : A} → B a → Type ℓC} where

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


𝒮-transport : {A : Type ℓA} {A' : Type ℓA'}
               (e : A ≃ A') (StrA : URGStr A ℓ≅A)
               → URGStr A' ℓ≅A
𝒮-transport {A = A} {A' = A'} e StrA =
  make-𝒮 {_≅_ = λ a a' → e- a ≅ e- a'}
             (λ a → ρ (e- a))
             λ a → isOfHLevelRespectEquiv 0
                                          (Σ[ x ∈ A ] e- a ≅ x
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



cong-𝒮 : {A : Type ℓ} {B : Type ℓ}
      (p : A ≡ B)
      → URGStr A ℓ' ≡ URGStr B ℓ'
cong-𝒮 {ℓ' = ℓ'} p = cong (λ X → URGStr X ℓ') p
-- transport of displayed structures along equivalences
{-
URGᴰtransp : {A : Type ℓA} {A' : Type ℓA'}
    {B : A → Type ℓB}
    (e : A ≃ A')
    (StrA : URGStr A ℓ≅A)
    (StrABᴰ : URGStrᴰ StrA B ℓ≅ᴰ)
    → URGStrᴰ {!!} {!!} {!!}
URGᴰtransp e StrA StrABᴰ =
  makeURGStrᴰ {!!} {!!} {!!} {!!} {!!}
-}

{-
𝒮-transport' : {A : Type ℓA} {A' : Type ℓA}
               (p : A ≡ A') (𝒮-A : URGStr A ℓ≅A)
               → URGStr A' ℓ≅A
𝒮-transport' {ℓ≅A = ℓ≅A} p 𝒮-A = subst (λ X → URGStr X ℓ≅A) p 𝒮-A

𝒮ᴰ-transport : {A : Type ℓA} {A' : Type ℓA}
               (p : A ≡ A') {𝒮-A : URGStr A ℓ≅A}
               {B : A → Type ℓB}
               (𝒮ᴰ-A\B : URGStrᴰ 𝒮-A B ℓ≅B)
               → URGStrᴰ (𝒮-transport' p 𝒮-A)
                         (λ a' → B (transport (sym p) a'))
                         ℓ≅B
𝒮ᴰ-transport e 𝒮ᴰ-A\B = {!!}
-}
