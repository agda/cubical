{-# OPTIONS --safe #-}
module Cubical.Categories.Site.Sheaf where

-- Definition of sheaves on a site.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma

open import Cubical.Functions.Embedding

open import Cubical.Categories.Category
open import Cubical.Categories.Site.Cover
open import Cubical.Categories.Site.Sieve
open import Cubical.Categories.Site.Coverage
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.FullSubcategory
open import Cubical.Categories.Yoneda

module _
  {ℓ ℓ' : Level}
  {C : Category ℓ ℓ'}
  {ℓP : Level}
  (P : Presheaf C ℓP)
  where

  open Category C hiding (_∘_)

  module _
    {c : ob}
    {ℓ'' : Level}
    (cov : Cover C ℓ'' c)
    where

    FamilyOnCover : Type (ℓ-max ℓP ℓ'')
    FamilyOnCover = (i : ⟨ cov ⟩) → ⟨ P ⟅ patchObj cov i ⟆ ⟩

    isCompatibleFamily : FamilyOnCover → Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓP) ℓ'')
    isCompatibleFamily fam =
      (i : ⟨ cov ⟩) →
      (j : ⟨ cov ⟩) →
      (d : ob) →
      (f : Hom[ d , patchObj cov i ]) →
      (g : Hom[ d , patchObj cov j ]) →
      f ⋆ patchArr cov i ≡ g ⋆ patchArr cov j →
      (P ⟪ f ⟫) (fam i) ≡ (P ⟪ g ⟫) (fam j)

    isPropIsCompatibleFamily : (fam : FamilyOnCover) → isProp (isCompatibleFamily fam)
    isPropIsCompatibleFamily fam =
      isPropΠ6 λ _ _ d _ _ _ → str (P ⟅ d ⟆) _ _

    CompatibleFamily : Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓP) ℓ'')
    CompatibleFamily = Σ FamilyOnCover isCompatibleFamily

    isSetCompatibleFamily : isSet CompatibleFamily
    isSetCompatibleFamily =
      isSetΣSndProp
        (isSetΠ (λ i → str (P ⟅ patchObj cov i ⟆)))
        isPropIsCompatibleFamily

    CompatibleFamily≡ : (fam fam' : CompatibleFamily)
                      → (∀ i → fam .fst i ≡ fam' .fst i)
                      → fam ≡ fam'
    CompatibleFamily≡ fam fam' p = Σ≡Prop isPropIsCompatibleFamily (funExt p)

    elementToCompatibleFamily : ⟨ P ⟅ c ⟆ ⟩ → CompatibleFamily
    elementToCompatibleFamily x =
      (λ i → (P ⟪ patchArr cov i ⟫) x) ,
      λ i j d f g eq → cong (λ f → f x) (
        P ⟪ f ⟫ ∘ P ⟪ patchArr cov i ⟫  ≡⟨ sym (F-seq (patchArr cov i) f ) ⟩
        P ⟪ f ⋆ patchArr cov i ⟫        ≡⟨ cong (P ⟪_⟫) eq ⟩
        P ⟪ g ⋆ patchArr cov j ⟫        ≡⟨ F-seq (patchArr cov j) g ⟩
        P ⟪ g ⟫ ∘ P ⟪ patchArr cov j ⟫  ∎ )
      where
      open Functor P

    hasAmalgamationPropertyForCover : Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓP) ℓ'')
    hasAmalgamationPropertyForCover =
      isEquiv elementToCompatibleFamily

    isPropHasAmalgamationPropertyForCover : isProp hasAmalgamationPropertyForCover
    isPropHasAmalgamationPropertyForCover =
      isPropIsEquiv _

module _
  {ℓ ℓ' ℓcov ℓpat : Level}
  {C : Category ℓ ℓ'}
  (J : Coverage C ℓcov ℓpat)
  {ℓP : Level}
  (P : Presheaf C ℓP)
  where

  open Coverage J

  isSeparated : Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓcov) ℓpat) ℓP)
  isSeparated =
    (c : _) →
    (cov : ⟨ covers c ⟩) →
    (x : ⟨ P ⟅ c ⟆ ⟩) →
    (y : ⟨ P ⟅ c ⟆ ⟩) →
    ( (patch : _) →
      let f = patchArr (str (covers c) cov) patch
      in (P ⟪ f ⟫) x ≡ (P ⟪ f ⟫) y ) →
    x ≡ y

  isPropIsSeparated : isProp isSeparated
  isPropIsSeparated = isPropΠ5 (λ c _ _ _ _ → str (P ⟅ c ⟆) _ _)

  isSheaf : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓcov) ℓpat) ℓP)
  isSheaf =
    (c : _) →
    (cov : ⟨ covers c ⟩) →
    hasAmalgamationPropertyForCover P (str (covers c) cov)

  isPropIsSheaf : isProp isSheaf
  isPropIsSheaf = isPropΠ2 λ c cov → isPropHasAmalgamationPropertyForCover P (str (covers c) cov)

  isSheaf→isSeparated : isSheaf → isSeparated
  isSheaf→isSeparated isSheafP c cov x y locallyEqual =
    isEmbedding→Inj (isEquiv→isEmbedding (isSheafP c cov)) x y
      (Σ≡Prop
        (isPropIsCompatibleFamily {C = C} P _)
        (funExt locallyEqual))

module _
  {ℓ ℓ' ℓcov ℓpat : Level}
  {C : Category ℓ ℓ'}
  (J : Coverage C ℓcov ℓpat)
  (ℓF : Level)
  where

  Sheaf : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓcov) ℓpat) (ℓ-suc ℓF))
  Sheaf = Σ[ P ∈ Presheaf C ℓF ] isSheaf J P

  SheafCategory :
    Category
      (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓcov) ℓpat) (ℓ-suc ℓF))
      (ℓ-max (ℓ-max ℓ ℓ') ℓF)
  SheafCategory = FullSubcategory (PresheafCategory C ℓF) (isSheaf J)


module _
  {ℓ ℓ' ℓcov ℓpat : Level}
  {C : Category ℓ ℓ'}
  (J : Coverage C ℓcov ℓpat)
  where

  isSubcanonical : Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓcov) ℓpat)
  isSubcanonical = ∀ c → isSheaf J (yo c)

  isPropIsSubcanonical : isProp isSubcanonical
  isPropIsSubcanonical = isPropΠ λ c → isPropIsSheaf J (yo c)
