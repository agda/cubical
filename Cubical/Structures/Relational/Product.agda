{-

Product of structures S and T: X ↦ S X × T X

-}
{-# OPTIONS --safe #-}
module Cubical.Structures.Relational.Product where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.RelationalStructure
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Trunc
open import Cubical.HITs.SetQuotients

open import Cubical.Structures.Product

private
  variable
    ℓ ℓ₁ ℓ₁' ℓ₁'' ℓ₂ ℓ₂' ℓ₂'' : Level

-- Structured relations

ProductRelStr :
  {S₁ : Type ℓ → Type ℓ₁} (ρ₁ : StrRel S₁ ℓ₁')
  {S₂ : Type ℓ → Type ℓ₂} (ρ₂ : StrRel S₂ ℓ₂')
  → StrRel (ProductStructure S₁ S₂) (ℓ-max ℓ₁' ℓ₂')
ProductRelStr ρ₁ ρ₂ R (s₁ , s₂) (t₁ , t₂) =
  ρ₁ R s₁ t₁ × ρ₂ R s₂ t₂

productSuitableRel :
  {S₁ : Type ℓ → Type ℓ₁} {ρ₁ : StrRel S₁ ℓ₁'}
  {S₂ : Type ℓ → Type ℓ₂} {ρ₂ : StrRel S₂ ℓ₂'}
  → SuitableStrRel S₁ ρ₁ → SuitableStrRel S₂ ρ₂
  → SuitableStrRel (ProductStructure S₁ S₂) (ProductRelStr ρ₁ ρ₂)
productSuitableRel θ₁ θ₂ .quo (X , s₁ , s₂) R (r₁ , r₂) .fst .fst =
  θ₁ .quo (X , s₁) R r₁ .fst .fst , θ₂ .quo (X , s₂) R r₂ .fst .fst
productSuitableRel θ₁ θ₂ .quo (X , s₁ , s₂) R (r₁ , r₂) .fst .snd =
  θ₁ .quo (X , s₁) R r₁ .fst .snd , θ₂ .quo (X , s₂) R r₂ .fst .snd
productSuitableRel θ₁ θ₂ .quo (X , s₁ , s₂) R (r₁ , r₂) .snd ((q₁ , q₂) , (c₁ , c₂)) i .fst =
  θ₁ .quo (X , s₁) R r₁ .snd (q₁ , c₁) i .fst , θ₂ .quo (X , s₂) R r₂ .snd (q₂ , c₂) i .fst
productSuitableRel θ₁ θ₂ .quo (X , s₁ , s₂) R (r₁ , r₂) .snd ((q₁ , q₂) , (c₁ , c₂)) i .snd =
  θ₁ .quo (X , s₁) R r₁ .snd (q₁ , c₁) i .snd , θ₂ .quo (X , s₂) R r₂ .snd (q₂ , c₂) i .snd
productSuitableRel θ₁ θ₂ .symmetric R (r₁ , r₂) =
  θ₁ .symmetric R r₁ , θ₂ .symmetric R r₂
productSuitableRel θ₁ θ₂ .transitive R R' (r₁ , r₂) (r₁' , r₂') =
  θ₁ .transitive R R' r₁ r₁' , θ₂ .transitive R R' r₂ r₂'
productSuitableRel θ₁ θ₂ .set setX =
  isSet× (θ₁ .set setX) (θ₂ .set setX)
productSuitableRel θ₁ θ₂ .prop propR (s₁ , s₂) (t₁ , t₂) =
  isProp× (θ₁ .prop propR s₁ t₁) (θ₂ .prop propR s₂ t₂)

productRelMatchesEquiv :
  {S₁ : Type ℓ → Type ℓ₁} (ρ₁ : StrRel S₁ ℓ₁') {ι₁ : StrEquiv S₁ ℓ₁''}
  {S₂ : Type ℓ → Type ℓ₂} (ρ₂ : StrRel S₂ ℓ₂') {ι₂ : StrEquiv S₂ ℓ₂''}
  → StrRelMatchesEquiv ρ₁ ι₁ → StrRelMatchesEquiv ρ₂ ι₂
  → StrRelMatchesEquiv (ProductRelStr ρ₁ ρ₂) (ProductEquivStr ι₁ ι₂)
productRelMatchesEquiv ρ₁ ρ₂ μ₁ μ₂ A B e =
  Σ-cong-equiv (μ₁ _ _ e) (λ _ → μ₂ _ _ e)

productRelAction :
  {S₁ : Type ℓ → Type ℓ₁} {ρ₁ : StrRel S₁ ℓ₁'} (α₁ : StrRelAction ρ₁)
  {S₂ : Type ℓ → Type ℓ₂} {ρ₂ : StrRel S₂ ℓ₂'} (α₂ : StrRelAction ρ₂)
  → StrRelAction (ProductRelStr ρ₁ ρ₂)
productRelAction α₁ α₂ .actStr f (s₁ , s₂) = α₁ .actStr f s₁ , α₂ .actStr f s₂
productRelAction α₁ α₂ .actStrId (s₁ , s₂) = ΣPathP (α₁ .actStrId s₁ , α₂ .actStrId s₂)
productRelAction α₁ α₂ .actRel h _ _ (r₁ , r₂) = α₁ .actRel h _ _ r₁ , α₂ .actRel h _ _ r₂

productPositiveRel :
  {S₁ : Type ℓ → Type ℓ₁} {ρ₁ : StrRel S₁ ℓ₁'} {θ₁ : SuitableStrRel S₁ ρ₁}
  {S₂ : Type ℓ → Type ℓ₂} {ρ₂ : StrRel S₂ ℓ₂'} {θ₂ : SuitableStrRel S₂ ρ₂}
  → PositiveStrRel θ₁
  → PositiveStrRel θ₂
  → PositiveStrRel (productSuitableRel θ₁ θ₂)
productPositiveRel σ₁ σ₂ .act = productRelAction (σ₁ .act) (σ₂ .act)
productPositiveRel σ₁ σ₂ .reflexive (s₁ , s₂) = σ₁ .reflexive s₁ , σ₂ .reflexive s₂
productPositiveRel σ₁ σ₂ .detransitive R R' (rr'₁ , rr'₂) =
  Trunc.rec squash
    (λ {(s₁ , r₁ , r₁') →
      Trunc.rec squash
        (λ {(s₂ , r₂ , r₂') → ∣ (s₁ , s₂) , (r₁ , r₂) , (r₁' , r₂') ∣})
        (σ₂ .detransitive R R' rr'₂)})
    (σ₁ .detransitive R R' rr'₁)
productPositiveRel {S₁ = S₁} {ρ₁} {θ₁} {S₂} {ρ₂} {θ₂} σ₁ σ₂ .quo {X} R =
  subst isEquiv
    (funExt (elimProp (λ _ → productSuitableRel θ₁ θ₂ .set squash/ _ _) (λ _ → refl)))
    (compEquiv
      (isoToEquiv isom)
      (Σ-cong-equiv (_ , σ₁ .quo R) (λ _ → _ , σ₂ .quo R)) .snd)
  where
  fwd :
    ProductStructure S₁ S₂ X / ProductRelStr ρ₁ ρ₂ (R .fst .fst)
    → (S₁ X / ρ₁ (R .fst .fst)) × (S₂ X / ρ₂ (R .fst .fst))
  fwd [ s₁ , s₂ ] = [ s₁ ] , [ s₂ ]
  fwd (eq/ (s₁ , s₂) (t₁ , t₂) (r₁ , r₂) i) = eq/ s₁ t₁ r₁ i , eq/ s₂ t₂ r₂ i
  fwd (squash/ _ _ p q i j) =
    isSet× squash/ squash/ _ _ (cong fwd p) (cong fwd q) i j

  bwd[] : S₁ X → S₂ X / ρ₂ (R .fst .fst)
    → ProductStructure S₁ S₂ X / ProductRelStr ρ₁ ρ₂ (R .fst .fst)
  bwd[] s₁ [ s₂ ] = [ s₁ , s₂ ]
  bwd[] s₁ (eq/ s₂ t₂ r₂ i) =
    eq/ (s₁ , s₂) (s₁ , t₂) (posRelReflexive σ₁ R s₁ , r₂) i
  bwd[] s₁ (squash/ _ _ p q i j) =
    squash/ _ _ (λ j → bwd[] s₁ (p j)) (λ j → bwd[] s₁ (q j)) i j

  bwd : S₁ X / ρ₁ (R .fst .fst) → S₂ X / ρ₂ (R .fst .fst)
    → ProductStructure S₁ S₂ X / ProductRelStr ρ₁ ρ₂ (R .fst .fst)
  bwd [ s₁ ] u = bwd[] s₁ u
  bwd (eq/ s₁ t₁ r₁ i) u = path u i
    where
    path : ∀ u → bwd [ s₁ ] u ≡ bwd [ t₁ ] u
    path = elimProp (λ _ → squash/ _ _) (λ s₂ → eq/ (s₁ , s₂) (t₁ , s₂) (r₁ , posRelReflexive σ₂ R s₂))
  bwd (squash/ _ _ p q i j) =
    isSetΠ (λ _ → squash/) _ _ (cong bwd p) (cong bwd q) i j

  open Iso
  isom : Iso _ _
  isom .fun = fwd
  isom .inv = uncurry bwd
  isom .rightInv =
    uncurry
      (elimProp (λ _ → isPropΠ λ _ → isSet× squash/ squash/ _ _)
        (λ _ → elimProp (λ _ → isSet× squash/ squash/ _ _) (λ _ → refl)))
  isom .leftInv = elimProp (λ _ → squash/ _ _) (λ _ → refl)

productRelMatchesTransp :
  {S₁ : Type ℓ → Type ℓ₁} (ρ₁ : StrRel S₁ ℓ₁') (α₁ : EquivAction S₁)
  {S₂ : Type ℓ → Type ℓ₂} (ρ₂ : StrRel S₂ ℓ₂') (α₂ : EquivAction S₂)
  → StrRelMatchesEquiv ρ₁ (EquivAction→StrEquiv α₁)
  → StrRelMatchesEquiv ρ₂ (EquivAction→StrEquiv α₂)
  → StrRelMatchesEquiv (ProductRelStr ρ₁ ρ₂) (EquivAction→StrEquiv (productEquivAction α₁ α₂))
productRelMatchesTransp _ _ _ _ μ₁ μ₂ _ _ e =
  compEquiv (Σ-cong-equiv (μ₁ _ _ e) (λ _ → μ₂ _ _ e)) ΣPath≃PathΣ
