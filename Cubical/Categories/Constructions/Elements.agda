{-# OPTIONS --cubical --no-import-sorts --safe #-}

-- The Category of Elements

module Cubical.Categories.Constructions.Elements where

open import Cubical.Categories.Category
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Sets
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaves
open import Cubical.Categories.Equivalence
open import Cubical.Categories.Constructions.Slice
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv using (fiber)
open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' : Level

-- some issues
-- * always need to specify objects during composition because can't infer isSet
open Precategory
open Functor


getIsSet : {C : Precategory ℓ ℓ'} (F : Functor C (SET ℓ)) → (c : C .ob) → isSet (fst (F ⟅ c ⟆))
getIsSet F c = snd (F ⟅ c ⟆)


module _ {C : Precategory ℓ ℓ'} where
  infix 50 ∫_
  ∫_ : Functor C (SET ℓ) → Precategory ℓ (ℓ-max ℓ ℓ')
  -- objects are (c , x) pairs where c ∈ C and x ∈ F c
  (∫ F) .ob = Σ[ c ∈ C .ob ] fst (F ⟅ c ⟆)
  -- morphisms are f : c → c' which take x to x'
  (∫ F) .Hom[_,_] (c , x) (c' , x')  = Σ[ f ∈ C [ c , c' ] ] x' ≡ (F ⟪ f ⟫) x
  (∫ F) .id (c , x) = C .id c , sym (funExt⁻ (F .F-id) x ∙ refl)
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
        p' : x' ≡ (F ⟪ C .id c ⋆⟨ C ⟩ f ⟫) x
        p' = snd ((∫ F) ._⋆_ ((∫ F) .id o) f')
  (∫ F) .⋆IdR o@{c , x} o1@{c' , x'} f'@(f , p) i
     = (cIdR i) , isOfHLevel→isOfHLevelDep 1 (λ a → isS' x' ((F ⟪ a ⟫) x)) p' p cIdR i
       where
         cIdR = C .⋆IdR f
         isS' = getIsSet F c'

         p' : x' ≡ (F ⟪ f ⋆⟨ C ⟩ C .id c' ⟫) x
         p' = snd ((∫ F) ._⋆_ f' ((∫ F) .id o1))
  (∫ F) .⋆Assoc o@{c , x} o1@{c₁ , x₁} o2@{c₂ , x₂} o3@{c₃ , x₃} f'@(f , p) g'@(g , q) h'@(h , r) i
    = (cAssoc i) , isOfHLevel→isOfHLevelDep 1 (λ a → isS₃ x₃ ((F ⟪ a ⟫) x)) p1 p2 cAssoc i
      where
        cAssoc = C .⋆Assoc f g h
        isS₃ = getIsSet F c₃

        p1 : x₃ ≡ (F ⟪ (f ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ h ⟫) x
        p1 = snd ((∫ F) ._⋆_ ((∫ F) ._⋆_ {o} {o1} {o2} f' g') h')

        p2 : x₃ ≡ (F ⟪ f ⋆⟨ C ⟩ (g ⋆⟨ C ⟩ h) ⟫) x
        p2 = snd ((∫ F) ._⋆_ f' ((∫ F) ._⋆_ {o1} {o2} {o3} g' h'))


  -- same thing but for presheaves
  ∫ᴾ_ : Functor (C ^op) (SET ℓ) → Precategory ℓ (ℓ-max ℓ ℓ')
  -- objects are (c , x) pairs where c ∈ C and x ∈ F c
  (∫ᴾ F) .ob = Σ[ c ∈ C .ob ] fst (F ⟅ c ⟆)
  -- morphisms are f : c → c' which take x to x'
  (∫ᴾ F) .Hom[_,_] (c , x) (c' , x')  = Σ[ f ∈ C [ c , c' ] ] x ≡ (F ⟪ f ⟫) x'
  (∫ᴾ F) .id (c , x) = C .id c , sym (funExt⁻ (F .F-id) x ∙ refl)
  (∫ᴾ F) ._⋆_ {c , x} {c₁ , x₁} {c₂ , x₂} (f , p) (g , q)
    = (f ⋆⟨ C ⟩ g) , (x
              ≡⟨ p ⟩
                (F ⟪ f ⟫) x₁         -- basically expanding out function composition
              ≡⟨ cong (F ⟪ f ⟫) q ⟩
                (F ⟪ f ⟫) ((F ⟪ g ⟫) x₂)
              ≡⟨ funExt⁻ (sym (F .F-seq _ _)) _ ⟩
                (F ⟪ f ⋆⟨ C ⟩ g ⟫) x₂
              ∎)
  (∫ᴾ F) .⋆IdL o@{c , x} o1@{c' , x'} f'@(f , p) i
    = (cIdL i) , isOfHLevel→isOfHLevelDep 1 (λ a → isS x ((F ⟪ a ⟫) x')) p' p cIdL i
      where
        isS = getIsSet F c
        isS' = getIsSet F c'
        cIdL = C .⋆IdL f

        -- proof from composition with id
        p' : x ≡ (F ⟪ C .id c ⋆⟨ C ⟩ f ⟫) x'
        p' = snd ((∫ᴾ F) ._⋆_ ((∫ᴾ F) .id o) f')
  (∫ᴾ F) .⋆IdR o@{c , x} o1@{c' , x'} f'@(f , p) i
     = (cIdR i) , isOfHLevel→isOfHLevelDep 1 (λ a → isS x ((F ⟪ a ⟫) x')) p' p cIdR i
       where
         cIdR = C .⋆IdR f
         isS = getIsSet F c

         p' : x ≡ (F ⟪ f ⋆⟨ C ⟩ C .id c' ⟫) x'
         p' = snd ((∫ᴾ F) ._⋆_ f' ((∫ᴾ F) .id o1))
  (∫ᴾ F) .⋆Assoc o@{c , x} o1@{c₁ , x₁} o2@{c₂ , x₂} o3@{c₃ , x₃} f'@(f , p) g'@(g , q) h'@(h , r) i
    = (cAssoc i) , isOfHLevel→isOfHLevelDep 1 (λ a → isS x ((F ⟪ a ⟫) x₃)) p1 p2 cAssoc i
      where
        cAssoc = C .⋆Assoc f g h
        isS = getIsSet F c

        p1 : x ≡ (F ⟪ (f ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ h ⟫) x₃
        p1 = snd ((∫ᴾ F) ._⋆_ ((∫ᴾ F) ._⋆_ {o} {o1} {o2} f' g') h')

        p2 : x ≡ (F ⟪ f ⋆⟨ C ⟩ (g ⋆⟨ C ⟩ h) ⟫) x₃
        p2 = snd ((∫ᴾ F) ._⋆_ f' ((∫ᴾ F) ._⋆_ {o1} {o2} {o3} g' h'))

  -- BIG THEOREM
  module _ (F : Functor (C ^op) (SET ℓ)) where
    open _≃ᶜ_
    open isEquivalence
    open NatTrans
    preshvSlice≃preshvElem : SliceCat (PreShv C) F ⦃ isC = isCatPreShv {C = C} ⦄ ≃ᶜ PreShv (∫ᴾ F)
    -- we take (c , x) to the fiber in A of ϕ over x
    preshvSlice≃preshvElem .func .F-ob (sliceob {A} ϕ) .F-ob (c , x)
      = (fiber (ϕ ⟦ c ⟧) x)
      , isOfHLevelΣ 2 (snd (A ⟅ c ⟆)) λ _ → isSet→isGroupoid (snd (F ⟅ c ⟆)) _ _
    -- for morhpisms, we just apply A ⟪ h ⟫ (plus equality proof)
    preshvSlice≃preshvElem .func .F-ob (sliceob {A} ϕ) .F-hom {d , y} {c , x} (h , com) (b , eq)
      = ((A ⟪ h ⟫) b)
      , ((ϕ ⟦ c ⟧) ((A ⟪ h ⟫) b)
      ≡[ i ]⟨ (ϕ .N-hom h) i b ⟩
        (F ⟪ h ⟫) ((ϕ ⟦ d ⟧) b)
      ≡[ i ]⟨ (F ⟪ h ⟫) (eq i) ⟩
        (F ⟪ h ⟫) y
      ≡⟨ sym com ⟩
        x
      ∎)
    -- functoriality follows from functoriality of A
    preshvSlice≃preshvElem .func .F-ob (sliceob {A} ϕ) .F-id {x = (c , x)}
      -- = funExt {!!}
      = funExt λ { (a , fibp)
                → ΣPathP (a≡ a
                          , isOfHLevel→isOfHLevelDep 1 (λ v → snd (F ⟅ c ⟆) ((ϕ ⟦ c ⟧) v) x) _ fibp (a≡ a)) }
        where
          a≡ : ∀ (a : fst (A ⟅ c ⟆)) → (A ⟪ C .id _ ⟫) a ≡ a
          a≡ = λ a → (A ⟪ C .id _ ⟫) a
                   ≡[ i ]⟨ A .F-id i a ⟩
                     a
                   ∎
    preshvSlice≃preshvElem .func .F-ob (sliceob {A} ϕ) .F-seq {x = (c , x)} {(d , y)} {(e , z)} (f' , eq1) (g' , eq2)
      = funExt λ { ( a , fibp )
                  → ΣPathP ( seq≡ a --(λ i → (A .F-seq f' g') i a)
                           , isOfHLevel→isOfHLevelDep 1 (λ v → snd (F ⟅ e ⟆) ((ϕ ⟦ e ⟧) v) z) _ _ (seq≡ a) )}
        where
          seq≡ = λ (a : fst (A ⟅ c ⟆)) → λ i → (A .F-seq f' g') i a
    preshvSlice≃preshvElem .func .F-hom = {!!}
    --   = record
    --   -- takes each element to its preimage under ϕ ⟦ c ⟧
    --   { F-ob = λ { (c , x) → 
    --   ; F-hom = λ { {d , y} {c , x} (h , com) (b , eq)
    --               → ((A ⟪ h ⟫) b)
    --               , ((ϕ ⟦ c ⟧) ((A ⟪ h ⟫) b)
    --               ≡[ i ]⟨ (ϕ .N-hom h) i b ⟩
    --                 (F ⟪ h ⟫) ((ϕ ⟦ d ⟧) b)
    --               ≡[ i ]⟨ (F ⟪ h ⟫) (eq i) ⟩
    --                 (F ⟪ h ⟫) y
    --               ≡⟨ sym com ⟩
    --                 x
    --               ∎)}
    --   ; F-id = λ { {x = (c , x)} → funExt λ {  (a , fibp)
    --                     → ΣPathP (((A ⟪ C .id _ ⟫) a
    --                              ≡[ i ]⟨ A .F-id i a ⟩
    --                                a
    --                              ∎)
    --                              , isOfHLevel→isOfHLevelDep 1 (λ v → snd (F ⟅ c ⟆) {!(ϕ ⟦ c ⟧) a!} x) _ fibp {!!}) } }
    --   ; F-seq = {!!} }
    preshvSlice≃preshvElem .isEquiv = {!!}
