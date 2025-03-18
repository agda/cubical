{-# OPTIONS --safe #-}

-- The category of elements of a functor to Set

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
import      Cubical.Categories.Constructions.Slice.Base as Slice
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Isomorphism
import      Cubical.Categories.Morphism as Morphism


module Cubical.Categories.Constructions.Elements where

-- some issues
-- * always need to specify objects during composition because can't infer isSet
open Category
open Functor

module Covariant {ℓ ℓ'} {C : Category ℓ ℓ'} where
    getIsSet : ∀ {ℓS} (F : Functor C (SET ℓS)) → (c : C .ob) → isSet (fst (F ⟅ c ⟆))
    getIsSet F c = snd (F ⟅ c ⟆)

    Element : ∀ {ℓS} (F : Functor C (SET ℓS)) → Type (ℓ-max ℓ ℓS)
    Element F = Σ[ c ∈ C .ob ] fst (F ⟅ c ⟆)

    infix 50 ∫_
    ∫_ : ∀ {ℓS} → Functor C (SET ℓS) → Category (ℓ-max ℓ ℓS) (ℓ-max ℓ' ℓS)
    -- objects are (c , x) pairs where c ∈ C and x ∈ F c
    (∫ F) .ob = Element F
    -- morphisms are f : c → c' which take x to x'
    (∫ F) .Hom[_,_] (c , x) (c' , x')  = fiber (λ (f : C [ c , c' ]) → (F ⟪ f ⟫) x) x'
    (∫ F) .id {x = (c , x)} = C .id , funExt⁻ (F .F-id) x
    (∫ F) ._⋆_ {c , x} {c₁ , x₁} {c₂ , x₂} (f , p) (g , q)
      = (f ⋆⟨ C ⟩ g) , ((F ⟪ f ⋆⟨ C ⟩ g ⟫) x
                ≡⟨ funExt⁻ (F .F-seq _ _) _ ⟩
                  (F ⟪ g ⟫) ((F ⟪ f ⟫) x)
                ≡⟨ cong (F ⟪ g ⟫) p ⟩
                  (F ⟪ g ⟫) x₁
                ≡⟨ q ⟩
                  x₂
                ∎)
    (∫ F) .⋆IdL o@{c , x} o1@{c' , x'} f'@(f , p) i
      = (cIdL i) , isOfHLevel→isOfHLevelDep 1 (λ a → isS' ((F ⟪ a ⟫) x) x') p' p cIdL i
        where
          isS = getIsSet F c
          isS' = getIsSet F c'
          cIdL = C .⋆IdL f

          -- proof from composition with id
          p' : (F ⟪ C .id ⋆⟨ C ⟩ f ⟫) x ≡ x'
          p' = snd ((∫ F) ._⋆_ ((∫ F) .id) f')
    (∫ F) .⋆IdR o@{c , x} o1@{c' , x'} f'@(f , p) i
        = (cIdR i) , isOfHLevel→isOfHLevelDep 1 (λ a → isS' ((F ⟪ a ⟫) x) x') p' p cIdR i
          where
            cIdR = C .⋆IdR f
            isS' = getIsSet F c'

            p' : (F ⟪ f ⋆⟨ C ⟩ C .id ⟫) x ≡ x'
            p' = snd ((∫ F) ._⋆_ f' ((∫ F) .id))
    (∫ F) .⋆Assoc o@{c , x} o1@{c₁ , x₁} o2@{c₂ , x₂} o3@{c₃ , x₃} f'@(f , p) g'@(g , q) h'@(h , r) i
      = (cAssoc i) , isOfHLevel→isOfHLevelDep 1 (λ a → isS₃ ((F ⟪ a ⟫) x) x₃) p1 p2 cAssoc i
        where
          cAssoc = C .⋆Assoc f g h
          isS₃ = getIsSet F c₃

          p1 : (F ⟪ (f ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ h ⟫) x ≡ x₃
          p1 = snd ((∫ F) ._⋆_ ((∫ F) ._⋆_ {o} {o1} {o2} f' g') h')

          p2 : (F ⟪ f ⋆⟨ C ⟩ (g ⋆⟨ C ⟩ h) ⟫) x ≡ x₃
          p2 = snd ((∫ F) ._⋆_ f' ((∫ F) ._⋆_ {o1} {o2} {o3} g' h'))
    (∫ F) .isSetHom {x} {y} = isSetΣSndProp (C .isSetHom) λ _ → (F ⟅ fst y ⟆) .snd _ _

    ElementHom≡ : ∀ {ℓS} (F : Functor C (SET ℓS)) → {c,f c',f' : Element F}
      → {χ1,ef1 χ2,ef2 : (∫ F) [ c,f , c',f' ]} → (fst χ1,ef1 ≡ fst χ2,ef2) → (χ1,ef1 ≡ χ2,ef2)
    ElementHom≡ F {c1 , f1} {c2 , f2} {χ1 , ef1} {χ2 , ef2} eχ = cong₂ _,_ eχ
      (fst (isOfHLevelPathP' 0 (snd (F ⟅ c2 ⟆) _ _) ef1 ef2))

    ForgetElements : ∀ {ℓS} → (F : Functor C (SET ℓS)) → Functor (∫ F) C
    F-ob (ForgetElements F) = fst
    F-hom (ForgetElements F) = fst
    F-id (ForgetElements F) = refl
    F-seq (ForgetElements F) _ _ = refl

    module _ (isUnivC : isUnivalent C) {ℓS} (F : Functor C (SET ℓS)) where
      open isUnivalent
      isUnivalent∫ : isUnivalent (∫ F)
      isUnivalent∫ .univ (c , f) (c' , f') = isIsoToIsEquiv
        ( isoToPath∫
        , (λ f≅f' → CatIso≡ _ _
            (Σ≡Prop (λ _ → (F ⟅ _ ⟆) .snd _ _)
              (cong fst
              (secEq (univEquiv isUnivC _ _) (F-Iso {F = ForgetElements F} f≅f')))))
        , λ f≡f' → ΣSquareSet (λ x → snd (F ⟅ x ⟆))
          ( cong (CatIsoToPath isUnivC) (F-pathToIso {F = ForgetElements F} f≡f')
          ∙ retEq (univEquiv isUnivC _ _) (cong fst f≡f'))) where

        isoToPath∫ : ∀ {c c' f f'}
                   → CatIso (∫ F) (c , f) (c' , f')
                   → (c , f) ≡ (c' , f')
        isoToPath∫ {f = f} f≅f' = ΣPathP
          ( CatIsoToPath isUnivC (F-Iso {F = ForgetElements F} f≅f')
          , toPathP ( (λ j → transport (λ i → fst
                      (F-isoToPath isUnivC isUnivalentSET F
                        (F-Iso {F = ForgetElements F} f≅f') (~ j) i)) f)
                    ∙ univSetβ (F-Iso {F = F ∘F ForgetElements F} f≅f') f
                    ∙ f≅f' .fst .snd))


module Contravariant {ℓ ℓ'} {C : Category ℓ ℓ'} where
    open Covariant {C = C ^op}

    -- same thing but for presheaves
    ∫ᴾ_ : ∀ {ℓS} → Functor (C ^op) (SET ℓS) → Category (ℓ-max ℓ ℓS) (ℓ-max ℓ' ℓS)
    ∫ᴾ F = (∫ F) ^op

    Elementᴾ : ∀ {ℓS} → Functor (C ^op) (SET ℓS) → Type (ℓ-max ℓ ℓS)
    Elementᴾ F = (∫ᴾ F) .ob

    -- helpful results

    module _ {ℓS} {F : Functor (C ^op) (SET ℓS)} where

      -- morphisms are equal as long as the morphisms in C are equal
      ∫ᴾhomEq : ∀ {o1 o1' o2 o2'} (f : (∫ᴾ F) [ o1 , o2 ]) (g : (∫ᴾ F) [ o1' , o2' ])
              → (p : o1 ≡ o1') (q : o2 ≡ o2')
              → (eqInC : PathP (λ i → C [ fst (p i) , fst (q i) ]) (fst f) (fst g))
              → PathP (λ i → (∫ᴾ F) [ p i , q i ]) f g
      ∫ᴾhomEq _ _ _ _ = ΣPathPProp (λ f → snd (F ⟅ _ ⟆) _ _)

      ∫ᴾhomEqSimpl : ∀ {o1 o2} (f g : (∫ᴾ F) [ o1 , o2 ])
                   → fst f ≡ fst g → f ≡ g
      ∫ᴾhomEqSimpl f g p = ∫ᴾhomEq f g refl refl p
