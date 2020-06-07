{-# OPTIONS --cubical --safe #-}
module Cubical.Functions.Fibration where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Data.Sigma

module FiberIso {ℓb} {B : Type ℓb} {ℓ} (p⁻¹ : B → Type ℓ) (x : B) where

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
                   ((x  , refl ) , subst (λ z → p⁻¹ z) q y)
                   ((x' , sym q) , y                            )
          r i = (contrSingl (sym q) i) , toPathP {A = λ i → p⁻¹ (q (~ i))}
                                         (transport⁻Transport (λ i → p⁻¹ (q i)) y) i

  -- HoTT Lemma 4.8.1
  fiberEquiv : fiber p x ≃ p⁻¹ x
  fiberEquiv = isoToEquiv (iso fwd bwd fwd-bwd bwd-fwd)

open FiberIso using (fiberEquiv) public

module _ {ℓb} {B : Type ℓb} {ℓ} {E : Type ℓ} (p : E → B) where

  -- HoTT Lemma 4.8.2
  totalEquiv : E ≃ Σ B (fiber p)
  totalEquiv = isoToEquiv isom
    where isom : Iso E (Σ B (fiber p))
          Iso.fun isom x           = p x , x , refl
          Iso.inv isom (b , x , q) = x
          Iso.leftInv  isom x           i = x
          Iso.rightInv isom (b , x , q) i = q i , x , λ j → q (i ∧ j)

module _ {ℓb} (B : Type ℓb) (ℓ : Level) where
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

-- The path type in a fiber of f is equivalent to a fiber of (cong f)
fiber≡ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A → B} {b : B} (h h' : fiber f b)
  → (h ≡ h') ≡ fiber (cong f) (h .snd ∙∙ refl ∙∙ sym (h' .snd))
fiber≡ {f = f} h h' =
  ΣPath≡PathΣ ⁻¹ ∙
  cong (Σ (h .fst ≡ h' .fst)) (funExt λ p → flipSquarePath ∙ PathP≡doubleCompPathʳ _ _ _ _)

