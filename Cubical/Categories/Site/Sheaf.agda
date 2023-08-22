{-# OPTIONS --safe #-}
module Cubical.Categories.Site.Sheaf where

-- Definition of sheaves on a site.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma

open import Cubical.Functions.Logic using (∀[]-syntax; ∀[∶]-syntax; _⇒_; _⇔_)
open import Cubical.Functions.Embedding

open import Cubical.Categories.Category
open import Cubical.Categories.Site.Cover
open import Cubical.Categories.Site.Sieve
open import Cubical.Categories.Site.Coverage
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.FullSubcategory

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

    isCompatibleFamily : FamilyOnCover → hProp (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓP) ℓ'')
    isCompatibleFamily fam =
      ∀[ i ] ∀[ j ] ∀[ d ] ∀[ f ∶ Hom[ d , _ ] ] ∀[ g ∶ Hom[ d , _ ] ]
      ((f ⋆ patchArr cov i ≡ g ⋆ patchArr cov j) , isSetHom _ _) ⇒
      (((P ⟪ f ⟫) (fam i) ≡ (P ⟪ g ⟫) (fam j)) , str (P ⟅ d ⟆) _ _ )

    CompatibleFamily : Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓP) ℓ'')
    CompatibleFamily = Σ FamilyOnCover (⟨_⟩ ∘ isCompatibleFamily)

    isSetCompatibleFamily : isSet CompatibleFamily
    isSetCompatibleFamily =
      isSetΣSndProp
        (isSetΠ (λ i → str (P ⟅ patchObj cov i ⟆)))
        (str ∘ isCompatibleFamily)

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

    amalgamationPropertyForCover : hProp (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓP) ℓ'')
    amalgamationPropertyForCover =
      isEquiv elementToCompatibleFamily ,
      isPropIsEquiv _

module _
  {ℓ ℓ' ℓcov ℓpat : Level}
  {C : Category ℓ ℓ'}
  (J : Coverage C ℓcov ℓpat)
  {ℓP : Level}
  (P : Presheaf C ℓP)
  where

  open Coverage J

  isSeparated :
    hProp (ℓ-max (ℓ-max (ℓ-max ℓ ℓcov) ℓpat) ℓP)
  isSeparated =
    ∀[ c ] ∀[ cov ∶ ⟨ covers c ⟩ ]
    ∀[ x ] ∀[ y ]
      (∀[ patch ]
        let f = patchArr (str (covers c) cov) patch in
        ((P ⟪ f ⟫) x ≡ (P ⟪ f ⟫) y) , str (P ⟅ _ ⟆) _ _)
      ⇒
      ((x ≡ y) , str (P ⟅ _ ⟆) _ _)

  amalgamationProperty :
    hProp (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓcov) ℓpat) ℓP)
  amalgamationProperty =
    ∀[ c ] ∀[ cov ∶ ⟨ covers c ⟩ ]
    amalgamationPropertyForCover P (str (covers c) cov)

  isSheaf : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓcov) ℓpat) ℓP)
  isSheaf = ⟨ amalgamationProperty ⟩

  isSheaf→isSeparated : isSheaf → ⟨ isSeparated ⟩
  isSheaf→isSeparated isSheafP c cov x y locallyEqual =
    isEmbedding→Inj (isEquiv→isEmbedding (isSheafP c cov)) x y
      (Σ≡Prop
        (str ∘ (isCompatibleFamily {C = C} P _))
        (funExt locallyEqual))

module _
  {ℓ ℓ' ℓcov ℓpat : Level}
  {C : Category ℓ ℓ'}
  (J : Coverage C ℓcov ℓpat)
  (ℓF : Level)
  where

  Sheaf : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓcov) ℓpat) (ℓ-suc ℓF))
  Sheaf = Σ (Presheaf C ℓF) (isSheaf J)

  SheafCategory :
    Category
      (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓcov) ℓpat) (ℓ-suc ℓF))
      (ℓ-max (ℓ-max ℓ ℓ') ℓF)
  SheafCategory = FullSubcategory (PresheafCategory C ℓF) (isSheaf J)
