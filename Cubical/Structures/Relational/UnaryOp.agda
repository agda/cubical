{-

Index a structure S by the type variable: X ↦ X → S X

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.Relational.UnaryOp where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.RelationalStructure
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma
open import Cubical.Relation.ZigZag.Base
open import Cubical.HITs.SetQuotients

open import Cubical.Structures.NAryOp

private
  variable
    ℓ ℓ₁ ℓ₁' : Level

-- Structured relations

UnaryFunSetStructure : SetStructure ℓ ℓ₁ → SetStructure ℓ (ℓ-max ℓ ℓ₁)
UnaryFunSetStructure S .struct X = X → S .struct X
UnaryFunSetStructure S .set setX = isSetΠ λ _ → S .set setX

UnaryFunPropRel : {S : Type ℓ → Type ℓ₁} {ℓ₁' : Level}
  → StrRel S ℓ₁' → StrRel (NAryFunStructure 1 S) (ℓ-max ℓ ℓ₁')
UnaryFunPropRel ρ .rel R f g =
  ∀ {x y} → R x y → ρ .rel R (f x) (g y)
UnaryFunPropRel ρ .prop propR f g =
  isPropImplicitΠ λ x →
  isPropImplicitΠ λ y →
  isPropΠ λ _ → ρ .prop propR (f x) (g y)

open isBisimulation
open BisimDescends
open isUnivalentRel

private
  quoᴸ-coherence : (S : SetStructure ℓ ℓ₁) (ρ : StrRel (S .struct) ℓ₁') (θ : isUnivalentRel S ρ)
    {X Y : Type ℓ} (R : Bisimulation X Y ℓ)
    {x₀ x₁ : S .struct X} {y₀ y₁ : S .struct Y}
    (code₀₀ : ρ .rel (R .fst) x₀ y₀)
    (code₁₁ : ρ .rel (R .fst) x₁ y₁)
    → ρ .rel (R .fst) x₀ y₁
    → θ .descends R .fst code₀₀ .quoᴸ  .fst ≡ θ .descends R .fst code₁₁ .quoᴸ .fst
  quoᴸ-coherence S ρ θ R {x₀} {x₁} {y₀} {y₁} code₀₀ code₁₁ code₀₁ =
    cong fst
      (θ .propQuo (bisim→EquivRel R)
        (θ .descends R .fst code₀₀ .quoᴸ)
        (θ .descends R .fst code₀₁ .quoᴸ))
    ∙ lem
      (symP (θ .descends R .fst code₀₁ .path))
      (symP (θ .descends R .fst code₁₁ .path))
      (cong fst
        (θ .propQuo (bisim→EquivRel (invBisim R))
          (θ .descends R .fst code₀₁ .quoᴿ)
          (θ .descends R .fst code₁₁ .quoᴿ)))
    where
    lem : {A : I → Type ℓ} {a₀ a₀' : A i0} {a₁ a₁' : A i1}
      → PathP A a₀ a₁
      → PathP A a₀' a₁'
      → a₀ ≡ a₀'
      → a₁ ≡ a₁'
    lem {A = A} p₀ p₁ q i =
      comp A (λ k → λ {(i = i0) → p₀ k; (i = i1) → p₁ k}) (q i)

  quoᴿ-coherence : (S : SetStructure ℓ ℓ₁) (ρ : StrRel (S .struct) ℓ₁') (θ : isUnivalentRel S ρ)
    {X Y : Type ℓ} (R : Bisimulation X Y ℓ)
    {x₀ x₁ : S .struct X} {y₀ y₁ : S .struct Y}
    (code₀₀ : ρ .rel (R .fst) x₀ y₀)
    (code₁₁ : ρ .rel (R .fst) x₁ y₁)
    → ρ .rel (R .fst) x₁ y₀
    → θ .descends R .fst code₀₀ .quoᴿ .fst ≡ θ .descends R .fst code₁₁ .quoᴿ .fst
  quoᴿ-coherence S ρ θ R {x₀} {x₁} {y₀} {y₁} code₀₀ code₁₁ code₁₀ =
    cong fst
      (θ .propQuo (bisim→EquivRel (invBisim R))
        (θ .descends R .fst code₀₀ .quoᴿ)
        (θ .descends R .fst code₁₀ .quoᴿ))
    ∙ lem
      (θ .descends R .fst code₁₀ .path)
      (θ .descends R .fst code₁₁ .path)
      (cong fst
        (θ .propQuo (bisim→EquivRel R)
          (θ .descends R .fst code₁₀ .quoᴸ)
          (θ .descends R .fst code₁₁ .quoᴸ)))
    where
    lem : {A : I → Type ℓ} {a₀ a₀' : A i0} {a₁ a₁' : A i1}
      → PathP A a₀ a₁
      → PathP A a₀' a₁'
      → a₀ ≡ a₀'
      → a₁ ≡ a₁'
    lem {A = A} p₀ p₁ q i =
      comp A (λ k → λ {(i = i0) → p₀ k; (i = i1) → p₁ k}) (q i)

unaryFunUnivalentRel : {S : SetStructure ℓ ℓ₁} {ρ : StrRel (S .struct) ℓ₁'}
  → isUnivalentRel S ρ
  → isUnivalentRel (UnaryFunSetStructure S) (UnaryFunPropRel ρ)
unaryFunUnivalentRel {S = S} {ρ} θ .propQuo R (t , c) (t' , c') =
  equivFun ΣPath≃PathΣ
    ( funExt
      (elimProp
        (λ _ → S .set squash/ _ _)
        (λ x → cong fst (θ .propQuo R (t [ x ] , c refl) (t' [ x ] , c' refl))))
    , isProp→PathP (λ _ → UnaryFunPropRel ρ .prop (λ _ _ → squash/ _ _) _ _) _ _
    )
unaryFunUnivalentRel {S = S} {ρ} θ .descends {X , f} {Y , g} (R , bis) .fst code .quoᴸ =
  f₀ , λ p → subst (λ y → ρ .rel _ _ (f₀ y)) p (θ .descends _ .fst _ .quoᴸ .snd)
  where
  f₀ : _
  f₀ [ x ] = θ .descends (R , bis) .fst (code (bis .fwdRel x)) .quoᴸ .fst
  f₀ (eq/ x₀ x₁ r i) =
    quoᴸ-coherence S ρ θ (R , bis)
      (code (bis .fwdRel x₀))
      (code (bis .fwdRel x₁))
      (code r)
      i
  f₀ (squash/ _ _ p q j i) =
    S .set squash/ _ _ (cong f₀ p) (cong f₀ q) j i
unaryFunUnivalentRel {S = S} {ρ} θ .descends (R , bis) .fst code .quoᴿ =
  g₀ , λ p → subst (λ y → ρ .rel _ _ (g₀ y)) p (θ .descends _ .fst _ .quoᴿ .snd)
  where
  g₀ : _
  g₀ [ y ] = θ .descends (R , bis) .fst (code (bis .bwdRel y)) .quoᴿ .fst
  g₀ (eq/ y₀ y₁ r i) =
    quoᴿ-coherence S ρ θ (R , bis)
      (code (bis .bwdRel y₀))
      (code (bis .bwdRel y₁))
      (code r)
      i
  g₀ (squash/ _ _ p q j i) =
    S .set squash/ _ _ (cong g₀ p) (cong g₀ q) j i
unaryFunUnivalentRel {S = S} {ρ} θ .descends (R , bis) .fst code .path =
  ua→
    (elimProp
      (λ _ → isOfHLevelPathP' 1 (S .set squash/) _ _)
      (λ x →
        θ .descends _ .fst (code (bis .fwdRel x)) .path
        ▷ quoᴿ-coherence S ρ θ (R , bis) _ _ (code (bis .bwdRel (bis .fwd x)))))
  where
  module E = Bisim→Equiv (R , bis)
unaryFunUnivalentRel {S = S} {ρ} θ .descends {A = X , f} {B = Y , g} (R , bis) .snd d {x} {y} r =
  θ .descends (R , bis) .snd dxy
  where
  dxy : BisimDescends (S .struct) ρ (X , f x) (Y , g y) (R , bis)
  dxy .quoᴸ = d .quoᴸ .fst [ x ] , d .quoᴸ .snd refl
  dxy .quoᴿ = d .quoᴿ .fst [ y ] , d .quoᴿ .snd refl
  dxy .path =
    ua→⁻ (d .path) [ x ]
    ▷ cong (d .quoᴿ .fst) (eq/ _ _ (bis .zigzag (bis .bwdRel y) r (bis .fwdRel x)))
