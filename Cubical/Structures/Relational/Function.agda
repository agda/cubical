{-

Index a structure T a positive structure S: X ↦ S X → T X

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.Relational.Function where

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

open import Cubical.Structures.Function

private
  variable
    ℓ ℓ₁ ℓ₁' ℓ₂ ℓ₂' : Level

-- Structured relations

preservesSetsFunction : {S : Type ℓ → Type ℓ₁} {T : Type ℓ → Type ℓ₂}
  → preservesSets S → preservesSets T
  → preservesSets (FunctionStructure S T)
preservesSetsFunction p₁ p₂ setX = isSetΠ λ _ → p₂ setX

FunctionRelStr : {S : Type ℓ → Type ℓ₁} {T : Type ℓ → Type ℓ₂}
  → StrRel S ℓ₁' → StrRel T ℓ₂' → StrRel (FunctionStructure S T) (ℓ-max ℓ₁ (ℓ-max ℓ₁' ℓ₂'))
FunctionRelStr ρ₁ ρ₂ R f g =
  ∀ {x y} → ρ₁ R x y → ρ₂ R (f x) (g y)

open BinaryRelation
open isEquivRel
open isQuasiEquivRel
open SuitableStrRel
open isPositiveStrRel

private
  composeWith[_] : {A : Type ℓ} (R : EquivPropRel A ℓ)
    → compPropRel (R .fst) (quotientPropRel (R .fst .fst)) .fst ≡ graphRel [_]
  composeWith[_] R =
    funExt₂ λ a t →
    hPropExt squash (squash/ _ _)
      (Trunc.rec (squash/ _ _) (λ {(b , r , p) → eq/ a b r ∙ p }))
      (λ p → ∣ a , R .snd .reflexive a , p ∣)

  [_]∙[_]⁻¹ : {A : Type ℓ} (R : EquivPropRel A ℓ)
    → compPropRel (quotientPropRel (R .fst .fst)) (invPropRel (quotientPropRel (R .fst .fst))) .fst
      ≡ R .fst .fst
  [_]∙[_]⁻¹ R =
    funExt₂ λ a b →
    hPropExt squash (R .fst .snd a b)
      (Trunc.rec (R .fst .snd a b)
        (λ {(c , p , q) → effective (R .fst .snd) (R .snd) a b (p ∙ sym q)}))
      (λ r → ∣ _ , eq/ a b r , refl ∣)

functionSuitableRel : {S : Type ℓ → Type ℓ₁} {T : Type ℓ → Type ℓ₂}
  (pres₁ : preservesSets S) (pres₂ : preservesSets T)
  {ρ₁ : StrRel S ℓ₁'} {ρ₂ : StrRel T ℓ₂'}
  (θ₁ : SuitableStrRel S ρ₁)
  → isPositiveStrRel pres₁ θ₁
  → SuitableStrRel T ρ₂
  → SuitableStrRel (FunctionStructure S T) (FunctionRelStr ρ₁ ρ₂)
functionSuitableRel {S = S} pres₁ pres₂ {ρ₁} {ρ₂} θ₁ σ θ₂ .quo (X , f) R h =
  final
  where
  href = h ∘ σ .reflexive R

  [f] : _
  [f] [ s ] = θ₂ .quo (X , f s) R (href s) .fst .fst
  [f] (eq/ s₀ s₁ r i) =
    cong fst
      (θ₂ .quo (X , f s₀) R (href s₀) .snd
        ( [f] [ s₁ ]
        , subst (λ R' → ρ₂ R' (f s₀) ([f] [ s₁ ]))
          (composePropRelWith[_] R)
          (θ₂ .transitive (R .fst) (quotientPropRel (R .fst .fst))
            (h r)
            (θ₂ .quo (X , f s₁) R (href s₁) .fst .snd))
        ))
      i
  [f] (squash/ _ _ p q j i) =
    pres₂ squash/ _ _ (cong [f] p) (cong [f] q) j i

  relLemma : (s : S X) (t : S X)
    → ρ₁ (graphRel [_]) s (funIsEq (σ .quo R) [ t ])
    → ρ₂ (graphRel [_]) (f s) ([f] [ t ])
  relLemma s t r =
    subst (λ R' → ρ₂ R' (f s) ([f] [ t ]))
      (composeWith[_] R)
      (θ₂ .transitive (R .fst) (quotientPropRel (R .fst .fst))
        (h r')
        (θ₂ .quo (X , f t) R (href t) .fst .snd))
    where
    r' : ρ₁ (R .fst .fst) s t
    r' =
      subst (λ R' → ρ₁ R' s t) ([_]∙[_]⁻¹ R)
        (θ₁ .transitive
          (quotientPropRel (R .fst .fst))
          (invPropRel (quotientPropRel (R .fst .fst)))
          r
          (θ₁ .symmetric (quotientPropRel (R .fst .fst))
            (θ₁ .quo (X , t) R (σ .reflexive R t) .fst .snd)))

  quoRelLemma : (s : S X) (t : S X / ρ₁ (R .fst .fst))
    → ρ₁ (graphRel [_]) s (funIsEq (σ .quo R) t)
    → ρ₂ (graphRel [_]) (f s) ([f] t)
  quoRelLemma s =
    elimProp (λ _ → isPropΠ λ _ → θ₂ .prop (λ _ _ → squash/ _ _) _ _)
      (relLemma s)

  final : Σ (Σ _ _) _
  final .fst .fst = [f] ∘ invIsEq (σ .quo R)
  final .fst .snd {s} {t} r =
    quoRelLemma s
      (invIsEq (σ .quo R) t)
      (subst (ρ₁ (graphRel [_]) s) (sym (secIsEq (σ .quo R) t)) r)
  final .snd (f' , c) =
    Σ≡Prop
      (λ _ → isPropImplicitΠ λ s →
        isPropImplicitΠ λ t →
        isPropΠ λ _ → θ₂ .prop (λ _ _ → squash/ _ _) _ _)
      (funExt λ s → contractorLemma (invIsEq (σ .quo R) s) ∙ cong f' (secIsEq (σ .quo R) s))
    where
    contractorLemma : (s : S X / ρ₁ (R .fst .fst))
      → [f] s ≡ f' (funIsEq (σ .quo R) s)
    contractorLemma =
      elimProp
        (λ _ → pres₂ squash/ _ _)
        (λ s →
          cong fst
            (θ₂ .quo (X , f s) R (href s) .snd
              ( f' (funIsEq (σ .quo R) [ s ])
              , c (θ₁ .quo (X , s) R (σ .reflexive R s) .fst .snd
              ))))
functionSuitableRel pres₁ pres₂ {ρ₁} {ρ₂} θ₁ σ θ₂ .symmetric R h r =
  θ₂ .symmetric R (h (θ₁ .symmetric (invPropRel R) r))
functionSuitableRel pres₁ pres₂ {ρ₁} {ρ₂} θ₁ σ θ₂ .transitive R R' h h' rr' =
  Trunc.rec
    (θ₂ .prop (λ _ _ → squash) _ _)
    (λ {(_ , r , r') → θ₂ .transitive R R' (h r) (h' r')})
    (σ .detransitive R R' rr')
functionSuitableRel pres₁ pres₂ {ρ₁} {ρ₂} θ₁ σ θ₂ .prop propR f g =
  isPropImplicitΠ λ _ →
  isPropImplicitΠ λ _ →
  isPropΠ λ _ →
  θ₂ .prop propR _ _
