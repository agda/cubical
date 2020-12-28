
{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Categories.Equivalence where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Morphism
open import Cubical.HITs.PropositionalTruncation.Base


open Precategory
open Functor

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

-- Definition

record IsEquivalence {C : Precategory ℓC ℓC'} {D : Precategory ℓD ℓD'}
                     (F : Functor C D) : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
  field
    G : Functor D C

    η : 𝟙⟨ C ⟩ ≅ᶜ G ∘F F
    ε : F ∘F G ≅ᶜ 𝟙⟨ D ⟩

record _≃ᶜ_ (C : Precategory ℓC ℓC') (D : Precategory ℓD ℓD') : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
  field
    F : Functor C D
    isEquiv : IsEquivalence F

open NatIso
open CatIso
open NatTrans

open IsEquivalence


-- Equivalence implies Full, Faithul, and Essentially Surjective

module _ {C : Precategory ℓC ℓC'} {D : Precategory ℓD ℓD'} where
  symEquiv : ∀ {F : Functor C D} → (e : IsEquivalence F) → IsEquivalence (e .G)
  symEquiv {F} record { G = G ; η = η ; ε = ε } = record { G = F ; η = symNatIso ε ; ε = symNatIso η }

  isEquiv→Faithful : ∀ {F : Functor C D} → IsEquivalence F → isFaithful F
  isEquiv→Faithful {F} record { G = G
                              ; η = η
                              ; ε = _ }
                   c c' f g p = f
                              ≡⟨ sqRL η ⟩
                                cIso .mor ⋆⟨ C ⟩ G ⟪ F ⟪ f ⟫ ⟫ ⋆⟨ C ⟩ c'Iso .inv
                              ≡⟨ cong (λ v → cIso .mor ⋆⟨ C ⟩ (G ⟪ v ⟫) ⋆⟨ C ⟩ c'Iso .inv) p ⟩
                                cIso .mor ⋆⟨ C ⟩ G ⟪ F ⟪ g ⟫ ⟫ ⋆⟨ C ⟩ c'Iso .inv
                              ≡⟨ sym (sqRL η) ⟩
                                g
                              ∎
    where

      -- isomorphism between c and GFc
      cIso = isIso→CatIso (η .iso c)
      -- isomorphism between c' and GFc'
      c'Iso = isIso→CatIso (η .iso c')

module _ {C : Precategory ℓC ℓC'} {D : Precategory ℓD ℓD'} where
  isEquiv→Full : ∀ {F : Functor C D} → IsEquivalence F → isFull F
  isEquiv→Full {F} eq@record { G = G
                             ; η = η
                             ; ε = _ }
               c c' g = ∣ h , isEquiv→Faithful (symEquiv eq) _ _ _ _ GFh≡Gg ∣ -- apply faithfulness of G
    where
      -- isomorphism between c and GFc
      cIso = isIso→CatIso (η .iso c)
      -- isomorphism between c' and GFc'
      c'Iso = isIso→CatIso (η .iso c')

      -- reverses
      cIso⁻ = symCatIso cIso
      c'Iso⁻ = symCatIso c'Iso

      h = cIso .mor ⋆⟨ C ⟩ G ⟪ g ⟫ ⋆⟨ C ⟩ c'Iso .inv

      -- we show that both `G ⟪ g ⟫` and `G ⟪ F ⟪ h ⟫ ⟫`
      -- are equal to the same thing
      -- namely : cIso .inv ⋆⟨ C ⟩ h ⋆⟨ C ⟩ c'Iso .mor
      Gg≡ηhη : G ⟪ g ⟫ ≡ cIso .inv ⋆⟨ C ⟩ h ⋆⟨ C ⟩ c'Iso .mor
      Gg≡ηhη = invMoveL cAreInv move-c' ∙ sym (C .⋆Assoc _ _ _)
        where
          cAreInv : areInv (cIso .mor) (cIso .inv)
          cAreInv = CatIso→areInv cIso

          c'AreInv : areInv (c'Iso .mor) (c'Iso .inv)
          c'AreInv = CatIso→areInv c'Iso

          move-c' : cIso .mor ⋆⟨ C ⟩ G ⟪ g ⟫ ≡ h ⋆⟨ C ⟩ c'Iso .mor
          move-c' = invMoveR (symAreInv c'AreInv) refl

      GFh≡Gg : G ⟪ F ⟪ h ⟫ ⟫ ≡ G ⟪ g ⟫
      GFh≡Gg = G ⟪ F ⟪ h ⟫ ⟫
             ≡⟨ sqLR η ⟩
               cIso .inv ⋆⟨ C ⟩ h ⋆⟨ C ⟩ c'Iso .mor
             ≡⟨ sym Gg≡ηhη ⟩
               G ⟪ g ⟫
             ∎

  isEquiv→Surj : ∀ {F : Functor C D} → IsEquivalence F → isEssentiallySurj F
  isEquiv→Surj isE d = (isE .G ⟅ d ⟆) , isIso→CatIso ((isE .ε .iso) d)
