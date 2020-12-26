{-# OPTIONS --cubical --no-import-sorts --safe #-}

-- The Category of Elements

module Cubical.Categories.Constructions.Elements where

open import Cubical.Categories.Category
open import Cubical.Categories.Sets
open import Cubical.Categories.Functor
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' : Level

-- some issues
-- * always need to specify objects during composition because can't infer isSet

module _ {C : Precategory ℓ ℓ'} where
  open Precategory
  open Functor

  infix 50 ∫_
  ∫_ : Functor C (SET ℓ) → Precategory ℓ (ℓ-max ℓ ℓ')
  -- objects are (c , x) pairs where c ∈ C and x ∈ F c
  (∫ F) .ob = Σ[ c ∈ C .ob ] fst (F .F-ob c) × isSet (fst (F .F-ob c))
  -- morphisms are f : c → c' which take x to x'
  (∫ F) .Hom[_,_] (c , x , _) (c' , x' , _) = Σ[ f ∈ C [ c , c' ] ] x' ≡ (F ⟪ f ⟫) x
  (∫ F) .id (c , x , _) = C .id c , sym (funExt⁻ (F .F-id) x ∙ refl)
  (∫ F) ._⋆_ {c , x , _} {c₁ , x₁ , _} {c₂ , x₂ , _} (f , p) (g , q)
    = (f ⋆⟨ C ⟩ g) , (x₂
              ≡⟨ q ⟩
                (F ⟪ g ⟫) x₁         -- basically expanding out function composition
              ≡⟨ cong (F ⟪ g ⟫) p ⟩
                (F ⟪ g ⟫) ((F ⟪ f ⟫) x)
              ≡⟨ funExt⁻ (sym (F .F-seq _ _)) _ ⟩
                (F ⟪ f ⋆⟨ C ⟩ g ⟫) x
              ∎)
  (∫ F) .⋆IdL o@{c , x , isS} o1@{c' , x' , isS'} f'@(f , p) i
    = (cIdL i) , isOfHLevel→isOfHLevelDep 1 (λ a → isS' x' ((F ⟪ a ⟫) x)) p' p cIdL i
      where
        cIdL = C .⋆IdL f

        -- proof from composition with id
        p' : x' ≡ (F ⟪ C .id c ⋆⟨ C ⟩ f ⟫) x
        p' = snd ((∫ F) ._⋆_ {o} {o} {o1} ((∫ F) .id o) f')
  (∫ F) .⋆IdR o@{c , x , isS} o1@{c' , x' , isS'} f'@(f , p) i
     = (cIdR i) , isOfHLevel→isOfHLevelDep 1 (λ a → isS' x' ((F ⟪ a ⟫) x)) p' p cIdR i
       where
         cIdR = C .⋆IdR f

         p' : x' ≡ (F ⟪ f ⋆⟨ C ⟩ C .id c' ⟫) x
         p' = snd ((∫ F) ._⋆_ {o} {o1} {o1} f' ((∫ F) .id o1))
  (∫ F) .⋆Assoc o@{c , x , isS} o1@{c₁ , x₁ , isS₁} o2@{c₂ , x₂ , isS₂} o3@{_ , x₃ , isS₃} f'@(f , p) g'@(g , q) h'@(h , r) i
    = (cAssoc i) , isOfHLevel→isOfHLevelDep 1 (λ a → isS₃ x₃ ((F ⟪ a ⟫) x)) p1 p2 cAssoc i
      where
        cAssoc = C .⋆Assoc f g h

        p1 : x₃ ≡ (F ⟪ (f ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ h ⟫) x
        p1 = snd ((∫ F) ._⋆_ {o} {o2} {o3} ((∫ F) ._⋆_ {o} {o1} {o2} f' g') h')

        p2 : x₃ ≡ (F ⟪ f ⋆⟨ C ⟩ (g ⋆⟨ C ⟩ h) ⟫) x
        p2 = snd ((∫ F) ._⋆_ {o} {o1} {o3} f' ((∫ F) ._⋆_ {o1} {o2} {o3} g' h'))
