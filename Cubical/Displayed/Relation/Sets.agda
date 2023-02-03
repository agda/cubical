{-

  Definition of something

-}
{-# OPTIONS --safe #-}
module Cubical.Displayed.Relation.Sets where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.NaturalTransformation
open import Cubical.Data.Sigma
open import Cubical.HITs.SetQuotients as Quo
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Relation.ZigZag.Base

open import Cubical.Displayed.Relation.Base

module _ (ℓ ℓ' : Level) where

  open Categoryᴰ

  ℛ-Set-QER : RelCat (SET ℓ) (ℓ-max ℓ (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
  ℛ-Set-QER .ob[_] ((A₀ , _) , (A₁ , _)) = QuasiEquivRel A₀ A₁ ℓ'
  ℛ-Set-QER .Hom[_][_,_] (f₀ , f₁) R S = ∀ a₀ a₁ → R .fst .fst a₀ a₁ → S .fst .fst (f₀ a₀) (f₁ a₁)
  ℛ-Set-QER .idᴰ _ _ r = r
  ℛ-Set-QER ._⋆ᴰ_ α β _ _ r = β _ _ (α _ _ r)
  ℛ-Set-QER .⋆IdLᴰ _ = refl
  ℛ-Set-QER .⋆IdRᴰ _ = refl
  ℛ-Set-QER .⋆Assocᴰ _ _ _ = refl
  ℛ-Set-QER .isSetHomᴰ {yᴰ = R} = isSetΠ3 λ _ _ _ → isProp→isSet (R .fst .snd _ _)

module _ (ℓ : Level) where

  open Categoryᴰ

  ℛ-Set-≃ : RelCat (SET ℓ) ℓ ℓ
  ℛ-Set-≃ .ob[_] ((A₀ , _) , (A₁ , _)) = A₀ ≃ A₁
  ℛ-Set-≃ .Hom[_][_,_] (f₀ , f₁) e e' = ∀ a → e' .fst (f₀ a) ≡ f₁ (e .fst a)
  ℛ-Set-≃ .idᴰ _ = refl
  ℛ-Set-≃ ._⋆ᴰ_ {g = g} α β a = β _ ∙ cong (g .snd) (α a)
  ℛ-Set-≃ .⋆IdLᴰ {y = A} _ = isProp→PathP (λ _ → isPropΠ λ _ → A .snd .snd _ _) _ _
  ℛ-Set-≃ .⋆IdRᴰ {y = A} _ = isProp→PathP (λ _ → isPropΠ λ _ → A .snd .snd _ _) _ _
  ℛ-Set-≃ .⋆Assocᴰ {w = A} _ _ _ = isProp→PathP (λ _ → isPropΠ λ _ → A .snd .snd _ _) _ _
  ℛ-Set-≃ .isSetHomᴰ {y = A} = isSetΠ λ _ → isProp→isSet (A .snd .snd _ _)

module _  where

  open Functor

  ℛ-Set-QER→≃ : ∀ {ℓ} → RelCatFunctor (SET ℓ) (SET ℓ) (ℛ-Set-QER ℓ ℓ) (ℛ-Set-≃ ℓ)
  ℛ-Set-QER→≃ {ℓ} .F-ob ((A₀ , A₁) , R) =
    ((A₀ .fst / Rᴸ , squash/) , (A₁ .fst / Rᴿ , squash/)) , Thm
    where
    open QER→Equiv R
  ℛ-Set-QER→≃ .F-hom {x = (_ , R₀)} {y = (_ , R₁)} ((f₀ , f₁) , r) =
    ((fᴸ , fᴿ) , comm)
    where
    open QER→Equiv-Functorial R₀ R₁ f₀ f₁ r
  ℛ-Set-QER→≃ .F-id =
    Σ≡Prop
      (λ _ → isPropΠ λ _ → squash/ _ _)
      (ΣPathP
        ( funExt (Quo.elimProp (λ _ → squash/ _ _) $ λ _ → refl)
        , funExt (Quo.elimProp (λ _ → squash/ _ _) $ λ _ → refl)
        ))
  ℛ-Set-QER→≃ .F-seq _ _ =
    Σ≡Prop
      (λ _ → isPropΠ λ _ → squash/ _ _)
      (ΣPathP
        ( funExt (Quo.elimProp (λ _ → squash/ _ _) $ λ _ → refl)
        , funExt (Quo.elimProp (λ _ → squash/ _ _) $ λ _ → refl)
        ))

  ℛ-Set-≃→QER : ∀ {ℓ} → RelCatFunctor (SET ℓ) (SET ℓ) (ℛ-Set-≃ ℓ) (ℛ-Set-QER ℓ ℓ)
  ℛ-Set-≃→QER .F-ob ((A₀ , A₁) , e) = (A₀ , A₁) , ≃→QER (A₁ .snd) e
  ℛ-Set-≃→QER .F-hom ((f₀ , f₁) , h) = (f₀ , f₁) , λ a₀ a₁ p → h a₀ ∙ cong f₁ p
  ℛ-Set-≃→QER .F-id {x = (_ , A₁) , _} =
    Σ≡Prop (λ _ → isPropΠ3 λ _ _ _ → A₁ .snd _ _) refl
  ℛ-Set-≃→QER .F-seq {z = (_ , A₁) , _} _ _ =
    Σ≡Prop (λ _ → isPropΠ3 λ _ _ _ → A₁ .snd _ _) refl

  open UnitCounit._⊣_
  open NatTrans

  QER⊣≃ : ∀ {ℓ} → RelCatAdj (SET ℓ) (SET ℓ) (ℛ-Set-QER ℓ ℓ) (ℛ-Set-≃ ℓ) ℛ-Set-QER→≃ ℛ-Set-≃→QER
  QER⊣≃ .η .N-ob ((A₀ , A₁) , R) = ([_] , [_]) , λ _ _ r → QER→Equiv.relToFwd≡ R r
  QER⊣≃ .η .N-hom ((f₀ , f₁) , h) = Σ≡Prop (λ _ → isPropΠ3 λ _ _ _ → squash/ _ _) refl
  QER⊣≃ .ε .N-ob ((A₀ , A₁) , e) .fst .fst =
      Quo.rec (A₀ .snd) (λ a → a)
        (λ a a' → Prop.rec (A₀ .snd _ _) $ λ (_ , p , q) →
          sym (retEq e a) ∙ cong (invEq e) (p ∙ sym q) ∙ retEq e a')
  QER⊣≃ .ε .N-ob ((A₀ , A₁) , e) .fst .snd =
      Quo.rec (A₁ .snd) (λ a → a)
        (λ a a' → Prop.rec (A₁ .snd _ _) $ λ (_ , p , q) → sym p ∙ q)
  QER⊣≃ .ε .N-ob ((A₀ , A₁) , e) .snd =
      Quo.elimProp (λ _ → A₁ .snd _ _) $ λ _ → refl
  QER⊣≃ .ε .N-hom {y = (A₀ , A₁) , _} ((f₀ , f₁) , h) =
      Σ≡Prop (λ _ → isPropΠ λ _ → A₁ .snd _ _)
        (ΣPathP
          ( funExt (Quo.elimProp (λ _ → A₀ .snd _ _) $ λ _ → refl)
          , funExt (Quo.elimProp (λ _ → A₁ .snd _ _) $ λ _ → refl)
          ))
  QER⊣≃ .Δ₁ ((A₀ , A₁) , R) =
      Σ≡Prop (λ _ → isPropΠ λ _ → squash/ _ _)
        (ΣPathP
          ( funExt (Quo.elimProp (λ _ → squash/ _ _) $ λ _ → refl)
          , funExt (Quo.elimProp (λ _ → squash/ _ _) $ λ _ → refl)
          ))
  QER⊣≃ .Δ₂ ((A₀ , A₁) , e) =
      Σ≡Prop (λ _ → isPropΠ3 λ _ _ _ → A₁ .snd _ _) refl
