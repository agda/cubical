{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Functions.Fibration where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma

private
  variable
    ℓ : Level

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
                   ((x  , refl ) , subst p⁻¹ q y)
                   ((x' , sym q) , y                            )
          r = ΣPathP (isContrSingl x .snd (x' , sym q)
                     , toPathP (transport⁻Transport (λ i → p⁻¹ (q i)) y))

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

-- fibrant replacement
module _ {C : Type ℓ} where
  dispTypeIso : Iso (C → Type ℓ) (Σ[ X ∈ Type ℓ ] (X → C))
  Iso.fun dispTypeIso D .fst = Σ[ c ∈ C ] D c
  Iso.fun dispTypeIso D .snd = fst
  Iso.inv dispTypeIso (X , F) c = Σ[ x ∈ X ] F x ≡ c
  Iso.leftInv dispTypeIso D = funExt (λ c → ua (e c))
    where
      module _ (c : C) where
        x : isContr (Σ[ c' ∈ C ] (c ≡ c'))
        x = isContrSingl c
        e =
          Σ[ (c' , d) ∈ (Σ[ c' ∈ C ] D c') ] c' ≡ c
            ≃⟨ Σ-assoc-≃ ⟩
          Σ[ c' ∈ C ] (D c') × (c' ≡ c)
            ≃⟨ Σ-cong-equiv-snd (λ _ → Σ-swap-≃) ⟩
          Σ[ c' ∈ C ] (c' ≡ c) × (D c')
            ≃⟨ invEquiv Σ-assoc-≃ ⟩
          Σ[ (c' , _) ∈ Σ[ c' ∈ C ] (c' ≡ c) ] D c'
            ≃⟨ Σ-cong-equiv-fst (Σ-cong-equiv-snd (λ c' → isoToEquiv (iso sym sym (λ _ → refl) (λ _ → refl)))) ⟩
          Σ[ (c' , _) ∈ Σ[ c' ∈ C ] (c ≡ c') ] D c'
            ≃⟨ Σ-contractFst (isContrSingl c) ⟩
          D c ■

  Iso.rightInv dispTypeIso (X , F) = ΣPathP (p₁ , p₂)
    where
      p₁' =
        Σ[ c ∈ C ] (Σ[ x ∈ X ] F x ≡ c)
           ≃⟨ invEquiv Σ-assoc-≃ ⟩
        Σ[ (c , x) ∈ C × X ] (F x ≡ c)
           ≃⟨ Σ-cong-equiv-fst Σ-swap-≃ ⟩
        Σ[ (x , c) ∈ X × C ] (F x ≡ c)
           ≃⟨ Σ-assoc-≃ ⟩
        Σ[ x ∈ X ] Σ[ c ∈ C ] (F x ≡ c)
           ≃⟨ Σ-contractSnd (λ x → isContrSingl (F x)) ⟩
        X ■
      p₁ : (Σ[ c ∈ C ] (Σ[ x ∈ X ] F x ≡ c)) ≡ X
      p₁ = ua p₁'

      p₂ : PathP (λ i → p₁ i → C) fst F
      p₂ = funExtDep p₂'
        where
          module _ {(c , x , p) : Σ[ c ∈ C ] (Σ[ x ∈ X ] F x ≡ c)} {y : X} (q : PathP (λ i → p₁ i) (c , x , p) y) where
            p₂' : c ≡ F y
            p₂' = sym p ∙ cong F p₂''
              where
                p₂'' =
                  x
                    ≡⟨ sym (uaβ p₁' (c , x , p)) ⟩
                  transp (λ i → p₁ i) i0 (c , x , p)
                    ≡⟨ fromPathP q ⟩
                  y ∎
