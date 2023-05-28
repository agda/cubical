{-# OPTIONS --safe #-}
module Cubical.Categories.Site.Sheaf where

-- Definition of sheaves on a site.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv

open import Cubical.Functions.Logic using (∀[]-syntax; ∀[∶]-syntax; _⇒_; _⇔_)

open import Cubical.Categories.Category
open import Cubical.Categories.Site.Cover
open import Cubical.Categories.Site.Sieve
open import Cubical.Categories.Site.Coverage
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Functor

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
      ((f ⋆ patchArr cov i ≡ (g ⋆ patchArr cov j)) , isSetHom _ _) ⇒
      (((P ⟪ f ⟫) (fam i) ≡ (P ⟪ g ⟫) (fam j)) , str (P ⟅ d ⟆) _ _ )

    CompatibleFamilies : Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓP) ℓ'')
    CompatibleFamilies = Σ FamilyOnCover (⟨_⟩ ∘ isCompatibleFamily)

    elementToCompatibleFamily : ⟨ P ⟅ c ⟆ ⟩ → CompatibleFamilies
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
  where

  open Coverage J

  amalgamationProperty :
    {ℓP : Level} →
    (P : Presheaf C ℓP) →
    hProp (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓcov) ℓpat) ℓP)
  amalgamationProperty P =
    ∀[ c ] ∀[ cov ∶ ⟨ covers c ⟩ ]
    amalgamationPropertyForCover P (str (covers c) cov)

  Sheaf : (ℓF : Level) → Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓcov) ℓpat) (ℓ-suc ℓF))
  Sheaf ℓF = Σ (Presheaf C ℓF) (⟨_⟩ ∘ amalgamationProperty)
