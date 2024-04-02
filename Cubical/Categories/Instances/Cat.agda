-- The category of small categories
{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Cat where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Categories.Category.Path
open import Cubical.Relation.Binary.Properties

open import Cubical.Categories.Limits

open Category hiding (_∘_)
open Functor

module _ (ℓ ℓ' : Level) where
  Cat : Category (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
  ob Cat = Σ (Category ℓ ℓ') isSmall
  Hom[_,_] Cat X Y = Functor (fst X) (fst Y)
  id Cat = 𝟙⟨ _ ⟩
  _⋆_ Cat G H = H ∘F G
  ⋆IdL Cat _ = F-lUnit
  ⋆IdR Cat _ = F-rUnit
  ⋆Assoc Cat _ _ _ = F-assoc
  isSetHom Cat {y = _ , isSetObY} = isSetFunctor isSetObY


  -- isUnivalentCat : isUnivalent Cat
  -- isUnivalent.univ isUnivalentCat (C , isSmallC) (C' , isSmallC') =
  --   {!!}

  --  where
  --  w : Iso (CategoryPath C C') (CatIso Cat (C , isSmallC) (C' , isSmallC'))
  --  Iso.fun w = pathToIso ∘ Σ≡Prop (λ _ → isPropIsSet) ∘ CategoryPath.mk≡
  --  Iso.inv w (m , isiso inv sec ret) = ww
  --    where
  --     obIsom : Iso (C .ob) (C' .ob)
  --     Iso.fun obIsom = F-ob m
  --     Iso.inv obIsom = F-ob inv
  --     Iso.rightInv obIsom = cong F-ob sec ≡$_
  --     Iso.leftInv obIsom = cong F-ob ret ≡$_

  --     homIsom : (x y : C .ob) →
  --                 Iso (C .Hom[_,_] x y)
  --                 (C' .Hom[_,_] (fst (isoToEquiv obIsom) x)
  --                 (fst (isoToEquiv obIsom) y))
  --     Iso.fun (homIsom x y) = F-hom m
  --     Iso.inv (homIsom x y) f =
  --       subst2 (C [_,_]) (cong F-ob ret ≡$ x) ((cong F-ob ret ≡$ y))
  --         (F-hom inv f)

  --     Iso.rightInv (homIsom x y) b =
  --       -- cong (F-hom m)
  --       --   (fromPathP {A = (λ i → Hom[ C , F-ob (ret i) x ] (F-ob (ret i) y))}
  --       --    {!!}) ∙
  --         {!!} ∙
  --         λ i → (fromPathP (cong F-hom sec)) i b
  --       -- {!!} ∙ λ i → {!sec i .F-hom b!}
  --     Iso.leftInv (homIsom x y) a = {!!}

  --     open CategoryPath
  --     ww : CategoryPath C C'
  --     ob≡ ww = ua (isoToEquiv obIsom)
  --     Hom≡ ww = RelPathP _ λ x y → isoToEquiv $ homIsom x y
  --     id≡ ww = {!!}
  --     ⋆≡ ww = {!!}
  --  Iso.rightInv w = {!!}
  --  Iso.leftInv w = {!!}
