-- Displayed SIP
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.DispSIP where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path
open import Cubical.Foundations.SIP
open import Cubical.Data.Sigma

open import Cubical.Relation.Binary
open BinaryRelation

private
  variable
    ℓ ℓ' ℓ'' ℓ₁ ℓ₁' ℓ₂ : Level

-- a univalent reflexive graph structure on a type
record URGStr (A : Type ℓ) (ℓ₁ : Level) : Type (ℓ-max ℓ (ℓ-suc ℓ₁)) where
  constructor urgstr
  field
    _≅_ : Rel A A ℓ₁
    ρ : isRefl _≅_
    uni : isUnivalent _≅_ ρ

-- wrapper to create instances of URGStr
makeURGStr : {A : Type ℓ} {_≅_ : Rel A A ℓ₁}
             (ρ : isRefl _≅_) (contrTotal : contrTotalSpace _≅_)
             → URGStr A ℓ₁
makeURGStr {A = A} {_≅_ = _≅_}
           ρ contrTotal
           = urgstr _≅_
                    ρ
                    λ a a' → contrTotalSpace→isUnivalent _≅_ ρ contrTotal a a'

-- a displayed univalent reflexive graph structure over a URGStr on a type
record URGStrᴰ {A : Type ℓ} (StrA : URGStr A ℓ₁)
                  (B : A → Type ℓ') (ℓ₁' : Level) : Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓ₁) (ℓ-suc ℓ₁')) where
  open URGStr StrA

  field
    _≅ᴰ⟨_⟩_ : {a a' : A} → B a → a ≅ a' → B a' → Type ℓ₁'
    ρᴰ : {a : A} → isRefl _≅ᴰ⟨ ρ a ⟩_
    uniᴰ : {a : A} → isUnivalent _≅ᴰ⟨ ρ a ⟩_ ρᴰ

-- the total space of a DURGS is a URGS
URGStrᴰ→URGStr : {A : Type ℓ} (StrA : URGStr A ℓ₁)
                 (B : A → Type ℓ') (DispStrB : URGStrᴰ StrA B ℓ₁')
                 → URGStr (Σ A B) (ℓ-max ℓ₁ ℓ₁')
URGStrᴰ→URGStr {A = A} StrA B DispStrB
  = makeURGStr {_≅_ = _≅Σ_} ρΣ contrTotalΣ
  where
   -- import notation: ≅ for StrA and ≅ᴰ for StrBᴰ
   open URGStr StrA
   open URGStrᴰ DispStrB

   -- in the context of a fixed point (a , b)
   module _ (x : Σ A B) where
     a = fst x
     b = snd x
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
{- Stuff to do:
 * a family of props has a canonical URGStrᴰ with DRel = Unit?
 * get URGStr from univalent bi-category
 * (Bonus: (A : Type ℓ) → isContr (URGStr A ℓ))
 * functoriality for free for e : (a : A) → B a → B' a
 * such e is a fiberwise equiv if it has inverse wrt⟨⟩ ≅ and ≅'⟨⟩
-}

module Examples {ℓ ℓ' : Level} where
  -- Universes and equivalences form a URGStr
  UGRStrUniverse : URGStr (Type ℓ) ℓ
  UGRStrUniverse
    = makeURGStr {_≅_ = _≃_}
                 idEquiv
                 λ A → isOfHLevelRespectEquiv 0
                                              (Σ-cong-equiv-snd (λ A' → isoToEquiv (iso invEquiv
                                                                                        invEquiv
                                                                                        (λ e → equivEq (invEquiv (invEquiv e)) e (funExt (λ x → refl)))
                                                                                        λ e → equivEq (invEquiv (invEquiv e)) e (funExt (λ x → refl)))))
                                              (EquivContr A)

  -- every univalent 1-precategory gives a URGStr
  open import Cubical.Categories.Category renaming (isUnivalent to isUnivalentCat)
  Cat→URG : (𝒞 : Precategory ℓ ℓ') → (uni : isUnivalentCat 𝒞) → URGStr (𝒞 .ob) ℓ'
  Cat→URG 𝒞 uni
    = urgstr (CatIso {𝒞 = 𝒞}) idCatIso λ x y → isUnivalentCat.univ uni x y
