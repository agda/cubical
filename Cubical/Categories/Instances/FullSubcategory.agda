-- Full subcategory (not necessarily injective on objects)
module Cubical.Categories.Instances.FullSubcategory where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset

open import Cubical.Functions.Embedding
open import Cubical.Data.Sigma

open import Cubical.Categories.Category renaming (isIso to isCatIso)
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Functor renaming (𝟙⟨_⟩ to funcId)
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Equivalence.Base

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓP ℓQ ℓR : Level

open isCatIso

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

open Functor
ΣPropCat : (C : Category ℓC ℓC') (P : ℙ (ob C)) → Category ℓC ℓC'
ΣPropCat C P = FullSubcategory C (_∈ P)

forgetΣPropCat : (C : Category ℓC ℓC') (prop : ℙ (C .ob)) → Functor (ΣPropCat C prop) C
forgetΣPropCat C prop = FullInclusion C _

-- Functoriality on full subcategories defined by propositions
ΣPropCatFunc : {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
               {P : ℙ (ob C)} {Q : ℙ (ob D)} (F : Functor C D)
             → (∀ c → c ∈ P → F .F-ob c ∈ Q)
             → Functor (ΣPropCat C P) (ΣPropCat D Q)
ΣPropCatFunc = MapFullSubcategory _ _ _ _

-- equivalence on full subcategories defined by propositions
module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} (F : Functor C D) (invF : WeakInverse F) where
  open NatTrans
  open NatIso
  open WeakInverse
  open _≃ᶜ_

  private
    F⁻¹ = invF .invFunc
    ηᴱ = invF .η
    εᴱ = invF .ε

  ΣPropCatEquiv : {P : ℙ (ob C)} {Q : ℙ (ob D)}
                → (presF : ∀ c → c ∈ P → F .F-ob c ∈ Q)
                → (∀ d → d ∈ Q → F⁻¹ .F-ob d ∈ P)
                → WeakInverse (ΣPropCatFunc {P = P} {Q = Q} F presF)

  invFunc (ΣPropCatEquiv {P} {Q} _ presF⁻¹) = ΣPropCatFunc {P = Q} {Q = P} F⁻¹ presF⁻¹

  N-ob (trans (η (ΣPropCatEquiv _ _))) (x , _) = ηᴱ .trans .N-ob x
  N-hom (trans (η (ΣPropCatEquiv _ _))) f = ηᴱ .trans .N-hom f
  inv (nIso (η (ΣPropCatEquiv _ _)) (x , _)) = ηᴱ .nIso x .inv
  sec (nIso (η (ΣPropCatEquiv _ _)) (x , _)) = ηᴱ .nIso x .sec
  ret (nIso (η (ΣPropCatEquiv _ _)) (x , _)) = ηᴱ .nIso x .ret

  N-ob (trans (ε (ΣPropCatEquiv _ _))) (x , _) = εᴱ .trans .N-ob x
  N-hom (trans (ε (ΣPropCatEquiv _ _))) f = εᴱ .trans .N-hom f
  inv (nIso (ε (ΣPropCatEquiv _ _)) (x , _)) = εᴱ .nIso x .inv
  sec (nIso (ε (ΣPropCatEquiv _ _)) (x , _)) = εᴱ .nIso x .sec
  ret (nIso (ε (ΣPropCatEquiv _ _)) (x , _)) = εᴱ .nIso x .ret

isIsoΣPropCat : {C : Category ℓC ℓC'} {P : ℙ (ob C)}
                {x y : ob C} (p : x ∈ P) (q : y ∈ P)
                (f : C [ x , y ])
              → isCatIso C f → isCatIso (ΣPropCat C P) {x , p} {y , q} f
inv (isIsoΣPropCat p q f isIsoF) = isIsoF .inv
sec (isIsoΣPropCat p q f isIsoF) = isIsoF .sec
ret (isIsoΣPropCat p q f isIsoF) = isIsoF .ret
