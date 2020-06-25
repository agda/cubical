{-

Index a structure S by the type variable: X ↦ X → S X

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.Relational.UnaryOp where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.RelationalStructure
open import Cubical.Foundations.Univalence
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.ZigZag.Base
open import Cubical.HITs.SetQuotients
open import Cubical.HITs.PropositionalTruncation as Trunc

open import Cubical.Structures.NAryOp

private
  variable
    ℓ ℓ₁ ℓ₁' : Level

-- Structured relations

preservesSetsUnaryFun : {S : Type ℓ → Type ℓ₁}
  → preservesSets S → preservesSets (NAryFunStructure 1 S)
preservesSetsUnaryFun p setX = isSetΠ λ _ → p setX

UnaryFunPropRel : {S : Type ℓ → Type ℓ₁} {ℓ₁' : Level}
  → StrRel S ℓ₁' → StrRel (NAryFunStructure 1 S) (ℓ-max ℓ ℓ₁')
UnaryFunPropRel ρ .rel R f g =
  ∀ {x y} → R x y → ρ .rel R (f x) (g y)
UnaryFunPropRel ρ .prop propR f g =
  isPropImplicitΠ λ x →
  isPropImplicitΠ λ y →
  isPropΠ λ _ → ρ .prop propR (f x) (g y)

open BinaryRelation
open isEquivRel
open isQuasiEquivRel
open SuitableStrRel

private
  composeWith[_] : {A : Type ℓ} (R : EquivPropRel A ℓ)
    → compPropRel (R .fst) (quotientPropRel (R .fst .fst)) .fst ≡ graphRel [_]
  composeWith[_] R =
    funExt₂ λ a t →
    hPropExt squash (squash/ _ _)
      (Trunc.rec (squash/ _ _) (λ {(b , r , p) → eq/ a b r ∙ p }))
      (λ p → ∣ a , R .snd .reflexive a , p ∣)

unaryFunSuitableRel : {S : Type ℓ → Type ℓ₁} (p : preservesSets S) {ρ : StrRel S ℓ₁'}
  → SuitableStrRel S ρ
  → SuitableStrRel (NAryFunStructure 1 S) (UnaryFunPropRel ρ)
unaryFunSuitableRel pres {ρ} θ .quo (X , f) R h .fst =
  f₀ ,
  λ {x} → J (λ y p → ρ .rel (graphRel [_]) (f x) (f₀ y)) (θ .quo (X , f x) R (href x) .fst .snd)
  where
  href = h ∘ R .snd .reflexive

  f₀ : _
  f₀ [ x ] = θ .quo (X , f x) R (href x) .fst .fst
  f₀ (eq/ x₀ x₁ r i) = path i
    where
    path : θ .quo (X , f x₀) R (href x₀) .fst .fst ≡ θ .quo (X , f x₁) R (href x₁) .fst .fst
    path =
      cong fst
        (θ .quo (X , f x₀) R (href x₀) .snd
          ( θ .quo (X , f x₁) R (href x₁) .fst .fst
          , subst
            (λ T → ρ .rel T (f x₀) (θ .quo (X , f x₁) R (href x₁) .fst .fst))
            (composeWith[_] R)
            (θ .transitive (R .fst) (quotientPropRel (R .fst .fst))
              (h r)
              (θ .quo (X , f x₁) R (href x₁) .fst .snd))
          ))
  f₀ (squash/ _ _ p q j i) =
    pres squash/ _ _ (cong f₀ p) (cong f₀ q) j i
unaryFunSuitableRel pres {ρ} θ .quo (X , f) R h .snd (f' , c) =
  Σ≡Prop
    (λ _ → isPropImplicitΠ λ _ → isPropImplicitΠ λ _ → isPropΠ λ _ →
      ρ .prop (λ _ _ → squash/ _ _) _ _)
    (funExt
      (elimProp (λ _ → pres squash/ _ _)
        (λ x → cong fst (θ .quo (X , f x) R (href x) .snd (f' [ x ] , c refl)))))
  where
  href = h ∘ R .snd .reflexive
unaryFunSuitableRel pres {ρ} θ .symmetric R h {x} {y} r = θ .symmetric R (h r)
unaryFunSuitableRel pres {ρ} θ .transitive R R' h h' {x} {z} =
  Trunc.rec
    (ρ .prop (λ _ _ → squash) _ _)
    (λ {(y , r , r') → θ .transitive R R' (h r) (h' r')})

unaryFunRelMatchesEquiv : {S : Type ℓ → Type ℓ₁}
  (ρ : StrRel S ℓ₁') {ι : StrEquiv S ℓ₁'}
  → StrRelMatchesEquiv ρ ι
  → StrRelMatchesEquiv (UnaryFunPropRel ρ) (UnaryFunEquivStr ι)
unaryFunRelMatchesEquiv ρ μ (X , f) (Y , g) e =
  compEquiv (isoToEquiv isom) (equivPi λ _ → μ _ _ e)
  where
  open Iso

  isom : Iso _ _
  isom .fun h x = h refl
  isom .inv k {x} = J (λ y _ → ρ .rel (graphRel (e .fst)) (f x) (g y)) (k x)
  isom .rightInv k i x = JRefl (λ y _ → ρ .rel (graphRel (e .fst)) (f x) (g y)) (k x) i
  isom .leftInv h =
    implicitFunExt λ {x} →
    implicitFunExt λ {y} →
    funExt λ p →
    J (λ y p →  isom .inv (isom .fun h) p ≡ h p)
      (funExt⁻ (isom .rightInv (isom .fun h)) x)
      p
