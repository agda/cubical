{-# OPTIONS --safe #-}

-- The Category of Elements

open import Cubical.Categories.Category

module Cubical.Categories.Constructions.Elements where

open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Functor
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

import Cubical.Categories.Morphism as Morphism
import Cubical.Categories.Constructions.Slice as Slice

-- some issues
-- * always need to specify objects during composition because can't infer isSet
open Category
open Functor

module Covariant {ℓ ℓ'} {C : Category ℓ ℓ'} where

    getIsSet : ∀ {ℓS} {C : Category ℓ ℓ'} (F : Functor C (SET ℓS)) → (c : C .ob) → isSet (fst (F ⟅ c ⟆))
    getIsSet F c = snd (F ⟅ c ⟆)

    infix 50 ∫_
    ∫_ : ∀ {ℓS} → Functor C (SET ℓS) → Category (ℓ-max ℓ ℓS) (ℓ-max ℓ' ℓS)
    -- objects are (c , x) pairs where c ∈ C and x ∈ F c
    (∫ F) .ob = Σ[ c ∈ C .ob ] fst (F ⟅ c ⟆)
    -- morphisms are f : c → c' which take x to x'
    (∫ F) .Hom[_,_] (c , x) (c' , x')  = Σ[ f ∈ C [ c , c' ] ] x' ≡ (F ⟪ f ⟫) x
    (∫ F) .id {x = (c , x)} = C .id , sym (funExt⁻ (F .F-id) x ∙ refl)
    (∫ F) ._⋆_ {c , x} {c₁ , x₁} {c₂ , x₂} (f , p) (g , q)
      = (f ⋆⟨ C ⟩ g) , (x₂
                ≡⟨ q ⟩
                  (F ⟪ g ⟫) x₁         -- basically expanding out function composition
                ≡⟨ cong (F ⟪ g ⟫) p ⟩
                  (F ⟪ g ⟫) ((F ⟪ f ⟫) x)
                ≡⟨ funExt⁻ (sym (F .F-seq _ _)) _ ⟩
                  (F ⟪ f ⋆⟨ C ⟩ g ⟫) x
                ∎)
    (∫ F) .⋆IdL o@{c , x} o1@{c' , x'} f'@(f , p) i
      = (cIdL i) , isOfHLevel→isOfHLevelDep 1 (λ a → isS' x' ((F ⟪ a ⟫) x)) p' p cIdL i
        where
          isS = getIsSet F c
          isS' = getIsSet F c'
          cIdL = C .⋆IdL f

          -- proof from composition with id
          p' : x' ≡ (F ⟪ C .id ⋆⟨ C ⟩ f ⟫) x
          p' = snd ((∫ F) ._⋆_ ((∫ F) .id) f')
    (∫ F) .⋆IdR o@{c , x} o1@{c' , x'} f'@(f , p) i
        = (cIdR i) , isOfHLevel→isOfHLevelDep 1 (λ a → isS' x' ((F ⟪ a ⟫) x)) p' p cIdR i
          where
            cIdR = C .⋆IdR f
            isS' = getIsSet F c'

            p' : x' ≡ (F ⟪ f ⋆⟨ C ⟩ C .id ⟫) x
            p' = snd ((∫ F) ._⋆_ f' ((∫ F) .id))
    (∫ F) .⋆Assoc o@{c , x} o1@{c₁ , x₁} o2@{c₂ , x₂} o3@{c₃ , x₃} f'@(f , p) g'@(g , q) h'@(h , r) i
      = (cAssoc i) , isOfHLevel→isOfHLevelDep 1 (λ a → isS₃ x₃ ((F ⟪ a ⟫) x)) p1 p2 cAssoc i
        where
          cAssoc = C .⋆Assoc f g h
          isS₃ = getIsSet F c₃

          p1 : x₃ ≡ (F ⟪ (f ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ h ⟫) x
          p1 = snd ((∫ F) ._⋆_ ((∫ F) ._⋆_ {o} {o1} {o2} f' g') h')

          p2 : x₃ ≡ (F ⟪ f ⋆⟨ C ⟩ (g ⋆⟨ C ⟩ h) ⟫) x
          p2 = snd ((∫ F) ._⋆_ f' ((∫ F) ._⋆_ {o1} {o2} {o3} g' h'))
    (∫ F) .isSetHom {x} {y} = isSetΣSndProp (C .isSetHom) λ _ → (F ⟅ fst y ⟆) .snd _ _

    ForgetElements : ∀ {ℓS} → (F : Functor C (SET ℓS)) → Functor (∫ F) C
    F-ob (ForgetElements F) = fst
    F-hom (ForgetElements F) = fst
    F-id (ForgetElements F) = refl
    F-seq (ForgetElements F) _ _ = refl

module Contravariant {ℓ ℓ'} {C : Category ℓ ℓ'} where
    open Covariant {C = C ^op}

    -- same thing but for presheaves
    ∫ᴾ_ : ∀ {ℓS} → Functor (C ^op) (SET ℓS) → Category (ℓ-max ℓ ℓS) (ℓ-max ℓ' ℓS)
    ∫ᴾ F = (∫ F) ^op

    -- helpful results

    module _ {ℓS} {F : Functor (C ^op) (SET ℓS)} where

      -- morphisms are equal as long as the morphisms in C are equal
      ∫ᴾhomEq : ∀ {o1 o1' o2 o2'} (f : (∫ᴾ F) [ o1 , o2 ]) (g : (∫ᴾ F) [ o1' , o2' ])
              → (p : o1 ≡ o1') (q : o2 ≡ o2')
              → (eqInC : PathP (λ i → C [ fst (p i) , fst (q i) ]) (fst f) (fst g))
              → PathP (λ i → (∫ᴾ F) [ p i , q i ]) f g
      ∫ᴾhomEq _ _ _ _ = ΣPathPProp (λ f → snd (F ⟅ _ ⟆) _ _)
