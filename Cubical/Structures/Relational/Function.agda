{-

Index a structure T a positive structure S: X ↦ S X → T X

-}
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
    ℓ ℓ₁ ℓ₁' ℓ₁'' ℓ₂ ℓ₂' ℓ₂'' : Level

FunctionRelStr : {S : Type ℓ → Type ℓ₁} {T : Type ℓ → Type ℓ₂}
  → StrRel S ℓ₁' → StrRel T ℓ₂' → StrRel (FunctionStructure S T) (ℓ-max ℓ₁ (ℓ-max ℓ₁' ℓ₂'))
FunctionRelStr ρ₁ ρ₂ R f g =
  ∀ {x y} → ρ₁ R x y → ρ₂ R (f x) (g y)

open BinaryRelation
open isEquivRel

private
  composeWith[_] : {A : Type ℓ} (R : EquivPropRel A ℓ)
    → compPropRel (R .fst) (quotientPropRel (R .fst .fst)) .fst ≡ graphRel [_]
  composeWith[_] R =
    funExt₂ λ a t →
    hPropExt squash₁ (squash/ _ _)
      (Trunc.rec (squash/ _ _) (λ {(b , r , p) → eq/ a b r ∙ p }))
      (λ p → ∣ a , R .snd .reflexive a , p ∣₁)

  [_]∙[_]⁻¹ : {A : Type ℓ} (R : EquivPropRel A ℓ)
    → compPropRel (quotientPropRel (R .fst .fst)) (invPropRel (quotientPropRel (R .fst .fst))) .fst
      ≡ R .fst .fst
  [_]∙[_]⁻¹ R =
    funExt₂ λ a b →
    hPropExt squash₁ (R .fst .snd a b)
      (Trunc.rec (R .fst .snd a b)
        (λ {(c , p , q) → effective (R .fst .snd) (R .snd) a b (p ∙ sym q)}))
      (λ r → ∣ _ , eq/ a b r , refl ∣₁)

functionSuitableRel : {S : Type ℓ → Type ℓ₁} {T : Type ℓ → Type ℓ₂}
  {ρ₁ : StrRel S ℓ₁'} {ρ₂ : StrRel T ℓ₂'}
  (θ₁ : SuitableStrRel S ρ₁)
  → PositiveStrRel θ₁
  → SuitableStrRel T ρ₂
  → SuitableStrRel (FunctionStructure S T) (FunctionRelStr ρ₁ ρ₂)
functionSuitableRel {S = S} {T = T} {ρ₁ = ρ₁} {ρ₂} θ₁ σ₁ θ₂ .quo (X , f) R h =
  final
  where
  ref : (s : S X) → ρ₁ (R .fst .fst) s s
  ref = posRelReflexive σ₁ R

  [f] : S X / ρ₁ (R .fst .fst) → T (X / R .fst .fst)
  [f] [ s ] = θ₂ .quo (X , f s) R (h (ref s)) .fst .fst
  [f] (eq/ s₀ s₁ r i) =
    cong fst
      (θ₂ .quo (X , f s₀) R (h (ref s₀)) .snd
        ( [f] [ s₁ ]
        , subst (λ R' → ρ₂ R' (f s₀) ([f] [ s₁ ]))
          (composeWith[_] R)
          (θ₂ .transitive (R .fst) (quotientPropRel (R .fst .fst))
            (h r)
            (θ₂ .quo (X , f s₁) R (h (ref s₁)) .fst .snd))
        ))
      i
  [f] (squash/ _ _ p q j i) =
    θ₂ .set squash/ _ _ (cong [f] p) (cong [f] q) j i

  relLemma : (s : S X) (t : S X)
    → ρ₁ (graphRel [_]) s (funIsEq (σ₁ .quo R) [ t ])
    → ρ₂ (graphRel [_]) (f s) ([f] [ t ])
  relLemma s t r =
    subst (λ R' → ρ₂ R' (f s) ([f] [ t ]))
      (composeWith[_] R)
      (θ₂ .transitive (R .fst) (quotientPropRel (R .fst .fst))
        (h r')
        (θ₂ .quo (X , f t) R (h (ref t)) .fst .snd))
    where
    r' : ρ₁ (R .fst .fst) s t
    r' =
      subst (λ R' → ρ₁ R' s t) ([_]∙[_]⁻¹ R)
        (θ₁ .transitive
          (quotientPropRel (R .fst .fst))
          (invPropRel (quotientPropRel (R .fst .fst)))
          r
          (θ₁ .symmetric (quotientPropRel (R .fst .fst))
            (subst
              (λ t' → ρ₁ (graphRel [_]) t' (funIsEq (σ₁ .quo R) [ t ]))
              (σ₁ .act .actStrId t)
              (σ₁ .act .actRel eq/ t t (ref t)))))

  quoRelLemma : (s : S X) (t : S X / ρ₁ (R .fst .fst))
    → ρ₁ (graphRel [_]) s (funIsEq (σ₁ .quo R) t)
    → ρ₂ (graphRel [_]) (f s) ([f] t)
  quoRelLemma s =
    elimProp (λ _ → isPropΠ λ _ → θ₂ .prop (λ _ _ → squash/ _ _) _ _)
      (relLemma s)

  final : Σ (Σ _ _) _
  final .fst .fst = [f] ∘ invIsEq (σ₁ .quo R)
  final .fst .snd {s} {t} r =
    quoRelLemma s
      (invIsEq (σ₁ .quo R) t)
      (subst (ρ₁ (graphRel [_]) s) (sym (secIsEq (σ₁ .quo R) t)) r)
  final .snd (f' , c) =
    Σ≡Prop
      (λ _ → isPropImplicitΠ λ s →
        isPropImplicitΠ λ t →
        isPropΠ λ _ → θ₂ .prop (λ _ _ → squash/ _ _) _ _)
      (funExt λ s → contractorLemma (invIsEq (σ₁ .quo R) s) ∙ cong f' (secIsEq (σ₁ .quo R) s))
    where
    contractorLemma : (s : S X / ρ₁ (R .fst .fst))
      → [f] s ≡ f' (funIsEq (σ₁ .quo R) s)
    contractorLemma =
      elimProp
        (λ _ → θ₂ .set squash/ _ _)
        (λ s →
          cong fst
            (θ₂ .quo (X , f s) R (h (ref s)) .snd
              ( f' (funIsEq (σ₁ .quo R) [ s ])
              , c
                (subst
                  (λ s' → ρ₁ (graphRel [_]) s' (funIsEq (σ₁ .quo R) [ s ]))
                  (σ₁ .act .actStrId s)
                  (σ₁ .act .actRel eq/ s s (ref s)))
              )))
functionSuitableRel {ρ₁ = ρ₁} {ρ₂} θ₁ σ θ₂ .symmetric R h r =
  θ₂ .symmetric R (h (θ₁ .symmetric (invPropRel R) r))
functionSuitableRel {ρ₁ = ρ₁} {ρ₂} θ₁ σ θ₂ .transitive R R' h h' rr' =
  Trunc.rec
    (θ₂ .prop (λ _ _ → squash₁) _ _)
    (λ {(_ , r , r') → θ₂ .transitive R R' (h r) (h' r')})
    (σ .detransitive R R' rr')
functionSuitableRel {ρ₁ = ρ₁} {ρ₂} θ₁ σ θ₂ .set setX =
  isSetΠ λ _ → θ₂ .set setX
functionSuitableRel {ρ₁ = ρ₁} {ρ₂} θ₁ σ θ₂ .prop propR f g =
  isPropImplicitΠ λ _ →
  isPropImplicitΠ λ _ →
  isPropΠ λ _ →
  θ₂ .prop propR _ _

functionRelMatchesEquiv : {S : Type ℓ → Type ℓ₁} {T : Type ℓ → Type ℓ₂}
  (ρ₁ : StrRel S ℓ₁') {ι₁ : StrEquiv S ℓ₁''}
  (ρ₂ : StrRel T ℓ₂') {ι₂ : StrEquiv T ℓ₂''}
  → StrRelMatchesEquiv ρ₁ ι₁
  → StrRelMatchesEquiv ρ₂ ι₂
  → StrRelMatchesEquiv (FunctionRelStr ρ₁ ρ₂) (FunctionEquivStr ι₁ ι₂)
functionRelMatchesEquiv ρ₁ ρ₂ μ₁ μ₂ (X , f) (Y , g) e =
  equivImplicitΠCod (equivImplicitΠCod (equiv→ (μ₁ _ _ e) (μ₂ _ _ e)))

functionRelMatchesEquiv+ : {S : Type ℓ → Type ℓ₁} {T : Type ℓ → Type ℓ₂}
  (ρ₁ : StrRel S ℓ₁') (α₁ : EquivAction S)
  (ρ₂ : StrRel T ℓ₂') (ι₂ : StrEquiv T ℓ₂'')
  → StrRelMatchesEquiv ρ₁ (EquivAction→StrEquiv α₁)
  → StrRelMatchesEquiv ρ₂ ι₂
  → StrRelMatchesEquiv (FunctionRelStr ρ₁ ρ₂) (FunctionEquivStr+ α₁ ι₂)
functionRelMatchesEquiv+ ρ₁ α₁ ρ₂ ι₂ μ₁ μ₂ (X , f) (Y , g) e =
  compEquiv
    (functionRelMatchesEquiv ρ₁ ρ₂ μ₁ μ₂ (X , f) (Y , g) e)
    (isoToEquiv isom)
  where
  open Iso
  isom : Iso
    (FunctionEquivStr (EquivAction→StrEquiv α₁) ι₂ (X , f) (Y , g) e)
    (FunctionEquivStr+ α₁ ι₂ (X , f) (Y , g) e)
  isom .fun h s = h refl
  isom .inv k {x} = J (λ y _ → ι₂ (X , f x) (Y , g y) e) (k x)
  isom .rightInv k i x = JRefl (λ y _ → ι₂ (X , f x) (Y , g y) e) (k x) i
  isom .leftInv h =
    implicitFunExt λ {x} →
    implicitFunExt λ {y} →
    funExt λ p →
    J (λ y p → isom .inv (isom .fun h) p ≡ h p)
      (funExt⁻ (isom .rightInv (isom .fun h)) x)
      p
