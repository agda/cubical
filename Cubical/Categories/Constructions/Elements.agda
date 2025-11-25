-- The category of elements of a functor to Set
module Cubical.Categories.Constructions.Elements where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Isomorphism

open Category
open Functor

module Covariant {ℓ ℓ'} {C : Category ℓ ℓ'} where

  open Category C

  private
    getIsSet : ∀ {ℓS} (F : Functor C (SET ℓS)) → (c : C .ob) → isSet (fst (F ⟅ c ⟆))
    getIsSet F c = snd (F ⟅ c ⟆)

  Element : ∀ {ℓS} (F : Functor C (SET ℓS)) → Type (ℓ-max ℓ ℓS)
  Element F = Σ[ c ∈ C .ob ] fst (F ⟅ c ⟆)

  infix 50 ∫_

  ∫_ : ∀ {ℓS} → Functor C (SET ℓS) → Category (ℓ-max ℓ ℓS) (ℓ-max ℓ' ℓS)
  -- objects are (c , x) pairs where c ∈ C and x ∈ F c
  (∫ F) .ob = Element F
  -- morphisms are f : c → c' which take x to x'
  (∫ F) .Hom[_,_] (c , x) (c' , x') = fiber (λ (f : C [ c , c' ]) → F .F-hom f x) x'
  (∫ F) .id     .fst = id C
  (∫ F) .id {x} .snd = funExt⁻ (F .F-id) (x .snd)
  (∫ F) ._⋆_ (f , p) (g , q) .fst = f ⋆⟨ C ⟩ g
  (∫ F) ._⋆_ (f , p) (g , q) .snd = funExt⁻ (F .F-seq _ _) _ ∙∙ cong (F ⟪ g ⟫) p ∙∙ q
  (∫ F) .⋆IdL _ = Σ≡Prop (λ _ → getIsSet F _ _ _) (⋆IdL C _)
  (∫ F) .⋆IdR _ = Σ≡Prop (λ _ → getIsSet F _ _ _) (⋆IdR C _)
  (∫ F) .⋆Assoc _ _ _ = Σ≡Prop (λ _ → getIsSet F _ _ _) (⋆Assoc C _ _ _)
  (∫ F) .isSetHom {x} {y} = isSetΣSndProp (C .isSetHom) λ _ → (F ⟅ fst y ⟆) .snd _ _

  ElementHom≡ : ∀ {ℓS} (F : Functor C (SET ℓS)) → {x y : Element F}
              → {f g : (∫ F) [ x , y ]} → fst f ≡ fst g → f ≡ g
  ElementHom≡ F = Σ≡Prop (λ _ → getIsSet F _ _ _)

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
