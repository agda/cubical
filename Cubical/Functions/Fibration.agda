{-# OPTIONS --safe #-}
module Cubical.Functions.Fibration where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isOfHLevel→isOfHLevelDep)
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Data.Sigma

private
  variable
    ℓ ℓb : Level
    B : Type ℓb

module FiberIso {ℓ} (p⁻¹ : B → Type ℓ) (x : B) where

  p : Σ B p⁻¹ → B
  p = fst

  fwd : fiber p x → p⁻¹ x
  fwd ((x' , y) , q) = subst (λ z → p⁻¹ z) q y

  bwd : p⁻¹ x → fiber p x
  bwd y = (x , y) , refl

  fwd-bwd : ∀ x → fwd (bwd x) ≡ x
  fwd-bwd y = transportRefl y

  bwd-fwd : ∀ x → bwd (fwd x) ≡ x
  bwd-fwd ((x' , y) , q) i = h (r i)
    where h : Σ[ s ∈ singl x ] p⁻¹ (s .fst) → fiber p x
          h ((x , p) , y) = (x , y) , sym p
          r : Path (Σ[ s ∈ singl x ] p⁻¹ (s .fst))
                   ((x  , refl ) , subst p⁻¹ q y)
                   ((x' , sym q) , y                            )
          r = ΣPathP (isContrSingl x .snd (x' , sym q)
                     , toPathP (transport⁻Transport (λ i → p⁻¹ (q i)) y))

  -- HoTT Lemma 4.8.1
  fiberEquiv : fiber p x ≃ p⁻¹ x
  fiberEquiv = isoToEquiv (iso fwd bwd fwd-bwd bwd-fwd)

open FiberIso using (fiberEquiv) public

module _ {ℓ} {E : Type ℓ} (p : E → B) where

  -- HoTT Lemma 4.8.2
  totalEquiv : E ≃ Σ B (fiber p)
  totalEquiv = isoToEquiv isom
    where isom : Iso E (Σ B (fiber p))
          Iso.fun isom x           = p x , x , refl
          Iso.inv isom (b , x , q) = x
          Iso.leftInv  isom x           i = x
          Iso.rightInv isom (b , x , q) i = q i , x , λ j → q (i ∧ j)

module _ (B : Type ℓb) (ℓ : Level) where
  private
    ℓ' = ℓ-max ℓb ℓ

  -- HoTT Theorem 4.8.3
  fibrationEquiv : (Σ[ E ∈ Type ℓ' ] (E → B)) ≃ (B → Type ℓ')
  fibrationEquiv = isoToEquiv isom
    where isom : Iso (Σ[ E ∈ Type ℓ' ] (E → B)) (B → Type ℓ')
          Iso.fun isom (E , p) = fiber p
          Iso.inv isom p⁻¹     = Σ B p⁻¹ , fst
          Iso.rightInv isom p⁻¹ i x = ua (fiberEquiv p⁻¹ x) i
          Iso.leftInv  isom (E , p) i = ua e (~ i) , fst ∘ ua-unglue e (~ i)
            where e = totalEquiv p


module ForSets {E : Type ℓ} {isSetB : isSet B} (f : E → B) where
  module _ {x x'} {px : x ≡ x'} {a' : fiber f x} {b' : fiber f x'} where
    -- fibers are equal when their representatives are equal
    fibersEqIfRepsEq : fst a' ≡ fst b'
                    → PathP (λ i → fiber f (px i)) a' b'
    fibersEqIfRepsEq p = ΣPathP (p ,
                                (isOfHLevel→isOfHLevelDep 1
                                                          (λ (v , w) → isSetB (f v) w)
                                                          (snd a') (snd b')
                                                          (λ i → (p i , px i))))
-- The path type in a fiber of f is equivalent to a fiber of (cong f)
open import Cubical.Foundations.Function

fiberPath : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A → B} {b : B} (h h' : fiber f b) →
             (Σ[ p ∈ (fst h ≡ fst h') ] (PathP (λ i → f (p i) ≡ b) (snd h) (snd h')))
           ≡ fiber (cong f) (h .snd ∙∙ refl ∙∙ sym (h' .snd))
fiberPath h h' = cong (Σ (h .fst ≡ h' .fst)) (funExt λ p → flipSquarePath ∙ PathP≡doubleCompPathʳ _ _ _ _)

fiber≡ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A → B} {b : B} (h h' : fiber f b)
  → (h ≡ h') ≡ fiber (cong f) (h .snd ∙∙ refl ∙∙ sym (h' .snd))
fiber≡ {f = f} {b = b} h h' =
  ΣPath≡PathΣ ⁻¹ ∙
  fiberPath h h'

fiberCong : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) {a₀ a₁ : A} (q : f a₀ ≡ f a₁)
  → fiber (cong f) q ≡ Path (fiber f (f a₁)) (a₀ , q) (a₁ , refl)
fiberCong f q =
  cong (fiber (cong f)) (cong sym (lUnit (sym q)))
  ∙ sym (fiber≡ (_ , q) (_ , refl))

FibrationStr : (B : Type ℓb) → Type ℓ → Type (ℓ-max ℓ ℓb)
FibrationStr B A = A → B

Fibration : (B : Type ℓb) → (ℓ : Level) → Type (ℓ-max ℓb (ℓ-suc ℓ))
Fibration {ℓb = ℓb} B ℓ = Σ[ A ∈ Type ℓ ] FibrationStr B A
