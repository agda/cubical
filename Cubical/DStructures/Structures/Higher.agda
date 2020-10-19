{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Structures.Higher where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Univalence

open import Cubical.Functions.FunExtEquiv

open import Cubical.Homotopy.Base
open import Cubical.Homotopy.Connected

open import Cubical.Data.Sigma
open import Cubical.Data.Nat

open import Cubical.Relation.Binary

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Higher
open import Cubical.Algebra.Group.EilenbergMacLane1

open import Cubical.HITs.EilenbergMacLane1

open import Cubical.DStructures.Base
open import Cubical.DStructures.Meta.Properties

open import Cubical.DStructures.Meta.Isomorphism
open import Cubical.DStructures.Structures.Universe
open import Cubical.DStructures.Structures.Type
open import Cubical.DStructures.Structures.Group
open import Cubical.DStructures.Structures.Constant

private
  variable
    ℓ ℓ' : Level

𝒮ᴰ-connected : {ℓ : Level} (k : ℕ) → URGStrᴰ (𝒮-universe {ℓ}) (isConnected k) ℓ-zero
𝒮ᴰ-connected k =
  Subtype→Sub-𝒮ᴰ (λ A → isConnected k A , isPropIsContr)
                 𝒮-universe

𝒮ᴰ-truncated : {ℓ : Level} (n : ℕ) → URGStrᴰ (𝒮-universe {ℓ}) (isOfHLevel n) ℓ-zero
𝒮ᴰ-truncated n =
  Subtype→Sub-𝒮ᴰ (λ A → isOfHLevel n A , isPropIsOfHLevel n)
                 𝒮-universe

𝒮ᴰ-BGroup : (n k : ℕ)
            → URGStrᴰ (𝒮-universe {ℓ})
                      (λ A → A × (isConnected (k + 1) A) × (isOfHLevel (n + k + 2) A))
                      ℓ
𝒮ᴰ-BGroup n k =
  combine-𝒮ᴰ 𝒮ᴰ-pointed
             (combine-𝒮ᴰ (𝒮ᴰ-connected (k + 1))
                         (𝒮ᴰ-truncated (n + k + 2)))

𝒮-BGroup : (n k : ℕ) → URGStr (Σ[ A ∈ Type ℓ ] A × (isConnected (k + 1) A) × (isOfHLevel (n + k + 2) A)) ℓ
𝒮-BGroup n k = ∫⟨ 𝒮-universe ⟩ 𝒮ᴰ-BGroup n k

𝒮-1BGroup : URGStr 1BGroupΣ ℓ
𝒮-1BGroup = 𝒮-BGroup 0 1

𝒮-Iso-BGroup-Group : {ℓ : Level} → 𝒮-PIso (𝒮-group ℓ) 𝒮-1BGroup
RelIso.fun 𝒮-Iso-BGroup-Group G = EM₁ G , embase , EM₁Connected G , EM₁Groupoid G
RelIso.inv 𝒮-Iso-BGroup-Group = π₁-1BGroupΣ
RelIso.leftInv 𝒮-Iso-BGroup-Group = π₁EM₁≃
RelIso.rightInv 𝒮-Iso-BGroup-Group BG = basetype-≅ , basepoint-≅ , tt , tt
  where
    -- notation
    type = fst BG
    * = fst (snd BG)
    conn = fst (snd (snd BG))
    trunc = snd (snd (snd BG))
    BG' = (bgroup (type , *) conn trunc)

    π₁BG : Group
    π₁BG = π₁-1BGroupΣ BG

    EM₁π₁BG : 1BGroupΣ
    EM₁π₁BG = EM₁ π₁BG , embase , EM₁Connected π₁BG , EM₁Groupoid π₁BG

    -- equivalences
    basetype-≅ : EM₁ π₁BG ≃ type
    fst basetype-≅ = EM₁-functor-lInv-function π₁BG BG' (GroupEquiv.hom (π₁EM₁≃ π₁BG))
    snd basetype-≅ = EM₁-functor-lInv-onIso-isEquiv π₁BG BG' (π₁EM₁≃ π₁BG)

    basepoint-≅ : * ≡ *
    basepoint-≅ = refl


𝒮ᴰ-BGroupHom : (n k : ℕ) → URGStrᴰ (𝒮-BGroup {ℓ} n k ×𝒮 𝒮-BGroup {ℓ'} n k)
                                  (λ (BG , BH) → BGroupHomΣ BG BH)
                                  (ℓ-max ℓ ℓ')
𝒮ᴰ-BGroupHom n k =
  make-𝒮ᴰ
    (λ {(BG , BH)} {(BG' , BH')} f (((eᴳ , _) , eᴳ-pt , _), ((eᴴ , _) , eᴴ-pt , _)) f'
       → ((eᴴ , eᴴ-pt) ∘∙ f) ∙∼ (f' ∘∙ (eᴳ , eᴳ-pt)))
    (λ {(BG , BH)} f → q {(BG , BH)} f)
    contrSingl
    where
      module _ {(BG , BH) : BGroupΣ n k × BGroupΣ n k} (f : BGroupHomΣ BG BH) where
        q : (id∙ (baseΣ BH) ∘∙ f) ∙∼ (f ∘∙ id∙ (baseΣ BG))
        q = funExt∙⁻ (id∙ (baseΣ BH) ∘∙ f
                       ≡⟨ ∘∙-idʳ f ⟩
                     f
                       ≡⟨ sym (∘∙-idˡ f) ⟩
                     (f ∘∙ id∙ (baseΣ BG)) ∎)

      module _ ((BG , BH) : BGroupΣ n k × BGroupΣ n k) (f : BGroupHomΣ BG BH) where
        contrSingl : isContr (Σ[ f' ∈ BGroupHomΣ BG BH ] ((id∙ (baseΣ BH) ∘∙ f) ∙∼ (f' ∘∙ id∙ (baseΣ BG))))
        contrSingl =
                isContrRespectEquiv (Σ-cong-equiv-snd (λ f' → f ≡ f'
                                                                ≃⟨ invEquiv (funExt∙≃ f f') ⟩
                                                               f ∙∼ f'
                                                                ≃⟨ pathToEquiv (cong (_∙∼ f')
                                                                                     (sym (∘∙-idʳ f))
                                                                               ∙ cong ((id∙ (baseΣ BH) ∘∙ f) ∙∼_)
                                                                                      (sym (∘∙-idˡ f'))) ⟩
                                                              (id∙ (baseΣ BH) ∘∙ f) ∙∼ (f' ∘∙ id∙ (baseΣ BG)) ■))

                                    (isContrSingl f)
