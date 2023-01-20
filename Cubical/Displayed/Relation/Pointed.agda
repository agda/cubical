{-

  Definition of something

-}
{-# OPTIONS --safe #-}
module Cubical.Displayed.Relation.Pointed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Total
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.SetQuotients as Quo
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Relation.ZigZag.Base
open import Cubical.Displayed.Relation
open import Cubical.Displayed.Relation.Sets

open DisplayedCat

Pointedᴰ : ∀ ℓ → DisplayedCat (SET ℓ) ℓ ℓ
Pointedᴰ ℓ .ob[_] A = A .fst
Pointedᴰ ℓ .Hom[_][_,_] f a b = f a ≡ b
Pointedᴰ ℓ .idᴰ = refl
Pointedᴰ ℓ ._⋆ᴰ_ p q = cong _ p ∙ q
Pointedᴰ ℓ .⋆IdLᴰ {y = A} _ = A .snd _ _ _ _
Pointedᴰ ℓ .⋆IdRᴰ {y = A} _ = A .snd _ _ _ _
Pointedᴰ ℓ .⋆Assocᴰ {w = A} _ _ _ = A .snd _ _ _ _
Pointedᴰ ℓ .isSetHomᴰ {y = A} = isProp→isSet (A .snd _ _)

ℛ-QER-Pointed : ∀ {ℓ ℓ'} → DRelCat (ℛ-Set-QER ℓ ℓ') (Pointedᴰ ℓ) ℓ' ℓ-zero
ℛ-QER-Pointed .ob[_] ((A , B) , (R , a , b)) = R .fst .fst a b
ℛ-QER-Pointed .Hom[_][_,_] _ _ _ = Unit
ℛ-QER-Pointed .idᴰ = _
ℛ-QER-Pointed ._⋆ᴰ_ _ _ = _
ℛ-QER-Pointed .⋆IdLᴰ _ = refl
ℛ-QER-Pointed .⋆IdRᴰ _ = refl
ℛ-QER-Pointed .⋆Assocᴰ _ _ _ = refl
ℛ-QER-Pointed .isSetHomᴰ = isSetUnit

ℛ-≃-Pointed : ∀ {ℓ} → DRelCat (ℛ-Set-≃ ℓ) (Pointedᴰ ℓ) ℓ ℓ-zero
ℛ-≃-Pointed .ob[_] ((A , B) , (e , a , b)) = e .fst a ≡ b
ℛ-≃-Pointed .Hom[_][_,_] _ _ _ = Unit
ℛ-≃-Pointed .idᴰ = _
ℛ-≃-Pointed ._⋆ᴰ_ _ _ = _
ℛ-≃-Pointed .⋆IdLᴰ _ = refl
ℛ-≃-Pointed .⋆IdRᴰ _ = refl
ℛ-≃-Pointed .⋆Assocᴰ _ _ _ = refl
ℛ-≃-Pointed .isSetHomᴰ = isSetUnit


-- module _ (ℓ ℓ' : Level) where

--   open DisplayedCat

--   ℛ-Set-QER : RelCat (SET ℓ) (ℓ-max ℓ (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
--   ℛ-Set-QER .ob[_] ((A₀ , _) , (A₁ , _)) = QuasiEquivRel A₀ A₁ ℓ'
--   ℛ-Set-QER .Hom[_][_,_] (f₀ , f₁) R S = ∀ a₀ a₁ → R .fst .fst a₀ a₁ → S .fst .fst (f₀ a₀) (f₁ a₁)
--   ℛ-Set-QER .idᴰ _ _ r = r
--   ℛ-Set-QER ._⋆ᴰ_ α β _ _ r = β _ _ (α _ _ r)
--   ℛ-Set-QER .⋆IdLᴰ _ = refl
--   ℛ-Set-QER .⋆IdRᴰ _ = refl
--   ℛ-Set-QER .⋆Assocᴰ _ _ _ = refl
--   ℛ-Set-QER .isSetHomᴰ {yᴰ = R} = isSetΠ3 λ _ _ _ → isProp→isSet (R .fst .snd _ _)

-- module _ (ℓ : Level) where

--   open DisplayedCat

--   ℛ-Set-≃ : RelCat (SET ℓ) ℓ ℓ
--   ℛ-Set-≃ .ob[_] ((A₀ , _) , (A₁ , _)) = A₀ ≃ A₁
--   ℛ-Set-≃ .Hom[_][_,_] (f₀ , f₁) e e' = ∀ a → e' .fst (f₀ a) ≡ f₁ (e .fst a)
--   ℛ-Set-≃ .idᴰ _ = refl
--   ℛ-Set-≃ ._⋆ᴰ_ {g = g} α β a = β _ ∙ cong (g .snd) (α a)
--   ℛ-Set-≃ .⋆IdLᴰ {y = A} _ = isProp→PathP (λ _ → isPropΠ λ _ → A .snd .snd _ _) _ _
--   ℛ-Set-≃ .⋆IdRᴰ {y = A} _ = isProp→PathP (λ _ → isPropΠ λ _ → A .snd .snd _ _) _ _
--   ℛ-Set-≃ .⋆Assocᴰ {w = A} _ _ _ = isProp→PathP (λ _ → isPropΠ λ _ → A .snd .snd _ _) _ _
--   ℛ-Set-≃ .isSetHomᴰ {y = A} = isSetΠ λ _ → isProp→isSet (A .snd .snd _ _)
