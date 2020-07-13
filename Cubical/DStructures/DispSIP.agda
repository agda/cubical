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
    ℓ ℓ' ℓ'' ℓ₁ ℓ₁' ℓ₁'' ℓ₂ ℓA ℓ≅A ℓB ℓ≅B ℓ≅ᴰ : Level

-- a univalent reflexive graph structure on a type
record URGStr (A : Type ℓA) (ℓ≅A : Level) : Type (ℓ-max ℓA (ℓ-suc ℓ≅A)) where
  constructor urgstr
  field
    _≅_ : Rel A A ℓ≅A
    ρ : isRefl _≅_
    uni : isUnivalent _≅_ ρ

-- wrapper to create instances of URGStr
makeURGStr : {A : Type ℓA} {_≅_ : Rel A A ℓ≅A}
             (ρ : isRefl _≅_) (contrTotal : contrTotalSpace _≅_)
             → URGStr A ℓ≅A
makeURGStr {A = A} {_≅_ = _≅_}
           ρ contrTotal
           = urgstr _≅_
                    ρ
                    λ a a' → contrTotalSpace→isUnivalent _≅_ ρ contrTotal a a'

-- a displayed univalent reflexive graph structure over a URGStr on a type
record URGStrᴰ {A : Type ℓA} (StrA : URGStr A ℓ≅A)
                  (B : A → Type ℓB) (ℓ≅ᴰ : Level) : Type (ℓ-max (ℓ-max (ℓ-max ℓA ℓB) ℓ≅A) (ℓ-suc ℓ≅ᴰ)) where
  constructor urgstrᴰ
  open URGStr StrA

  field
    _≅ᴰ⟨_⟩_ : {a a' : A} → B a → a ≅ a' → B a' → Type ℓ≅ᴰ
    ρᴰ : {a : A} → isRefl _≅ᴰ⟨ ρ a ⟩_
    uniᴰ : {a : A} → isUnivalent _≅ᴰ⟨ ρ a ⟩_ ρᴰ

-- wrapper to create instances of URGStrᴰ
module _ {A : Type ℓ} {StrA : URGStr A ℓ₁}
         (B : A → Type ℓ') (ℓ₁' : Level)
         where
           open URGStr StrA

           makeURGStrᴰ : {B : A → Type ℓ'} {ℓ₁' : Level}
                         (_≅ᴰ⟨_⟩_ : {a a' : A} → B a → a ≅ a' → B a' → Type ℓ₁')
                         (ρᴰ : {a : A} → isRefl _≅ᴰ⟨ ρ a ⟩_)
                         (contrTotal : (a : A) → contrTotalSpace _≅ᴰ⟨ ρ a ⟩_)
                         → URGStrᴰ StrA B ℓ₁'
           makeURGStrᴰ _≅ᴰ⟨_⟩_ ρᴰ contrTotal
             = urgstrᴰ _≅ᴰ⟨_⟩_
                       ρᴰ
                       λ {a : A} b b' → contrTotalSpace→isUnivalent (_≅ᴰ⟨ ρ a ⟩_)
                                                                    (ρᴰ {a})
                                                                    (contrTotal a)
                                                                    b b'


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
{- Stuff to do:
 * get URGStr from univalent bi-category
 * (Bonus: (A : Type ℓ) → isContr (URGStr A ℓ))
 * functoriality for free for e : (a : A) → B a → B' a
-}

module Fiberwise {ℓB ℓC ℓ≅B ℓ≅C : Level} {A : Type ℓ} {B : A → Type ℓB} {C : A → Type ℓC} where

  -- this belongs in Relation/Binary
  -- the notion of a fiberwise isomorphism with respect to a binary relation
  record FiberRelIso (_≅B_ : {a : A} → Rel (B a) (B a) ℓ≅B)
                  (_≅C_ : {a : A} → Rel (C a) (C a) ℓ≅C) : Type (ℓ-max (ℓ-max ℓ (ℓ-max ℓB ℓC)) (ℓ-max ℓ≅B ℓ≅C)) where
    constructor fiberRelIso
    field
      fun : {a : A} → B a → C a
      inv : {a : A} → C a → B a
      sec : {a : A} → (c : C a) → fun (inv c) ≅C c
      ret : {a : A} → (b : B a) → inv (fun b) ≅B b

  module _ {StrA : URGStr A ℓ} {StrBᴰ : URGStrᴰ StrA B ℓ≅B} {StrCᴰ : URGStrᴰ StrA C ℓ≅C} where
    -- maybe put this into separate module that exports useful notation
    module _ where
      ρ = URGStr.ρ StrA
      ρB = URGStrᴰ.ρᴰ StrBᴰ
      ρC = URGStrᴰ.ρᴰ StrCᴰ

      _≅B_ : {a : A} → Rel (B a) (B a) ℓ≅B
      _≅B_ {a} b b' = URGStrᴰ._≅ᴰ⟨_⟩_ StrBᴰ b (ρ a) b'
      _≅C_ : {a : A} → Rel (C a) (C a) ℓ≅C
      _≅C_ {a} c c' = URGStrᴰ._≅ᴰ⟨_⟩_ StrCᴰ c (ρ a) c'

      -- combine univalence map and proof that it is an equivalence
      -- to be able to invert it
      uniB : {a : A} (b b' : B a) → (b ≡ b') ≃ (b ≅B b')
      uniB b b' = ≡→R _≅B_ ρB , URGStrᴰ.uniᴰ StrBᴰ b b'

      uniC : {a : A} (c c' : C a) → (c ≡ c') ≃ (c ≅C c')
      uniC c c' = ≡→R _≅C_ ρC , URGStrᴰ.uniᴰ StrCᴰ c c'

    -- use univalence of the graph structure to show that
    -- fiberwise relational isos are fiberwise isos
    DispFiberIso→FiberEquiv : ((fiberRelIso F G FG GF) : FiberRelIso _≅B_ _≅C_)
                              → (a : A)
                              → Iso (B a) (C a)
    DispFiberIso→FiberEquiv (fiberRelIso F G FG GF) a
      = iso (F {a})
            (G {a})
            (λ c → (invEquiv (uniC (F (G c)) c)) .fst (FG c))
            λ b → (invEquiv (uniB (G (F b)) b)) .fst (GF b)

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

  -- a type is a URGStr with the relation given by its identity type
  URGStrType : (A : Type ℓ) → URGStr A ℓ
  URGStrType A = makeURGStr {_≅_ = _≡_} (λ _ → refl) isContrSingl

  -- subtypes are displayed structures
  open import Cubical.Data.Unit
  URGStrᴰSubtype : {A : Type ℓ} (P : A → hProp ℓ') → URGStrᴰ (URGStrType A) (λ a → P a .fst) ℓ-zero
  URGStrᴰSubtype P
    = makeURGStrᴰ (λ a → P a .fst)
                  ℓ-zero
                  (λ _ _ _ → Unit)
                  (λ _ → tt)
                  λ a p → isOfHLevelRespectEquiv 0
                                                 (invEquiv (Σ-contractSnd (λ _ → isContrUnit)))
                                                 (inhProp→isContr p (P a .snd))

{-
  Next steps:
  - URGStr on Groups
  - Two arms going up:
  -+ 1. SectRetr over G, RGGp over that, Peiffer over that, Str2Gp over/equiv to that
  -+ 2. GpAction over G, PreXMod over that, XMod over that
-}
