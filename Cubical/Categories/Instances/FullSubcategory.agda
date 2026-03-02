module Cubical.Categories.Instances.FullSubcategory where
-- Full subcategory (not necessarily injective on objects)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism

open import Cubical.Functions.Embedding
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Functor renaming (𝟙⟨_⟩ to funcId)

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓP ℓQ ℓR : Level

module _ (C : Category ℓC ℓC') (P : Category.ob C → Type ℓP) where
  private
    module C = Category C
  open Category
  open Functor

  FullSubcategory : Category (ℓ-max ℓC ℓP) ℓC'
  ob FullSubcategory = Σ[ x ∈ C.ob ] P x
  Hom[_,_] FullSubcategory (x , p) (y , q) = C.Hom[ x , y ]
  id FullSubcategory = C.id
  _⋆_ FullSubcategory = C._⋆_
  ⋆IdL FullSubcategory = C.⋆IdL
  ⋆IdR FullSubcategory = C.⋆IdR
  ⋆Assoc FullSubcategory = C.⋆Assoc
  isSetHom FullSubcategory = C.isSetHom

  FullInclusion : Functor FullSubcategory C
  F-ob FullInclusion = fst
  F-hom FullInclusion = idfun _
  F-id FullInclusion = refl
  F-seq FullInclusion f g = refl

  isFullyFaithfulIncl : isFullyFaithful FullInclusion
  isFullyFaithfulIncl _ _ = idEquiv _ .snd

  module _ (x y : FullSubcategory .ob) where

    open isIso

    Incl-Iso = F-Iso {F = FullInclusion} {x = x} {y = y}

    Incl-Iso-inv : CatIso C (x .fst) (y .fst) → CatIso FullSubcategory x y
    Incl-Iso-inv f .fst = f .fst
    Incl-Iso-inv f .snd .inv = f .snd .inv
    Incl-Iso-inv f .snd .sec = f .snd .sec
    Incl-Iso-inv f .snd .ret = f .snd .ret

    Incl-Iso-sec : ∀ f → Incl-Iso (Incl-Iso-inv f) ≡ f
    Incl-Iso-sec f = CatIso≡ _ _ refl

    Incl-Iso-ret : ∀ f → Incl-Iso-inv (Incl-Iso f) ≡ f
    Incl-Iso-ret f = CatIso≡ _ _ refl

    Incl-Iso-Iso : Iso (CatIso FullSubcategory x y) (CatIso C (x .fst) (y .fst))
    Incl-Iso-Iso = iso Incl-Iso Incl-Iso-inv Incl-Iso-sec Incl-Iso-ret

    Incl-Iso≃ : CatIso FullSubcategory x y ≃ CatIso C (x .fst) (y .fst)
    Incl-Iso≃ = isoToEquiv Incl-Iso-Iso

    isEquivIncl-Iso : isEquiv Incl-Iso
    isEquivIncl-Iso = Incl-Iso≃ .snd


module _ (C : Category ℓC ℓC')
         (D : Category ℓD ℓD') (Q : Category.ob D → Type ℓQ) where
  private
    module C = Category C
    module D = Category D
  open Category
  open Functor

  ToFullSubcategory  : (F : Functor C D) → ((c : C.ob) → Q (F-ob F c)) → Functor C (FullSubcategory D Q)
  F-ob (ToFullSubcategory F f) c = F-ob F c , f c
  F-hom (ToFullSubcategory F f) = F-hom F
  F-id (ToFullSubcategory F f) = F-id F
  F-seq (ToFullSubcategory F f) = F-seq F

module _ (C : Category ℓC ℓC') (P : Category.ob C → Type ℓP)
         (D : Category ℓD ℓD') (Q : Category.ob D → Type ℓQ) where
  private
    module C = Category C
    module D = Category D
  open Category
  open Functor

  MapFullSubcategory : (F : Functor C D) → ((c : C.ob) → P c → Q (F-ob F c))
    → Functor (FullSubcategory C P) (FullSubcategory D Q)
  MapFullSubcategory F f = ToFullSubcategory (FullSubcategory C P) D Q
    (funcComp F (FullInclusion C P) )
    λ (c , p) → f c p

module _ (C : Category ℓC ℓC') (P : Category.ob C → Type ℓP) where
  private
    module C = Category C
  open Category
  open Functor

  MapFullSubcategory-id :
    MapFullSubcategory C P C P (funcId C) (λ c p → p) ≡ funcId (FullSubcategory C P)
  MapFullSubcategory-id = Functor≡
    (λ (c , p) → refl)
    (λ γ → refl)

module _ (C : Category ℓC ℓC') (P : Category.ob C → Type ℓP)
         (D : Category ℓD ℓD') (Q : Category.ob D → Type ℓQ)
         (E : Category ℓE ℓE') (R : Category.ob E → Type ℓR) where
  private
    module C = Category C
    module D = Category D
    module E = Category E
  open Category
  open Functor

  MapFullSubcategory-seq :
    (F : Functor C D) → (f : (c : C.ob) → P c → Q (F-ob F c)) →
    (G : Functor D E) → (g : (d : D.ob) → Q d → R (F-ob G d)) →
    MapFullSubcategory C P E R (funcComp G F) (λ c p → g (F-ob F c) (f c p)) ≡
    funcComp
      (MapFullSubcategory D Q E R G g)
      (MapFullSubcategory C P D Q F f)
  MapFullSubcategory-seq F f G g = Functor≡
    (λ (c , p) → refl)
    (λ γ → refl)


-- Full subcategory (injective on objects)

open Category

module _
  (C : Category ℓC ℓC')
  {P : C .ob → Type ℓP}(isPropP : (c : C .ob) → isProp (P c))
  where

  open Functor
  open isUnivalent


  -- Full subcategory (injective on objects) is injective on objects.

  isEmbdIncl-ob : isEmbedding (FullInclusion C P .F-ob)
  isEmbdIncl-ob _ _ = isEmbeddingFstΣProp isPropP


  -- Full subcategory (injective on objects) of univalent category is univalent.

  isUnivalentFullSub : isUnivalent C → isUnivalent (FullSubcategory C P)
  isUnivalentFullSub isUnivC .univ _ _ = isEquiv[equivFunA≃B∘f]→isEquiv[f] _ (Incl-Iso≃ C P _ _)
    (subst isEquiv (sym (F-pathToIso-∘ {F = FullInclusion C P}))
      (compEquiv (_ , isEmbdIncl-ob _ _) (_ , isUnivC .univ _ _) .snd))
