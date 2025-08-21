{-# OPTIONS --safe #-}
module Cubical.Homotopy.Spectrum.Fiber where

open import Cubical.Data.Int
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Fiber
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence
open import Cubical.Homotopy.Group.LES
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Prespectrum
open import Cubical.Homotopy.Spectrum

private variable ℓ ℓ' : Level

open Spectrum
open GenericPrespectrum

module _ {X Y : Spectrum ℓ} (f : X →Sp Y) where
  FiberSpSpace : ℤ → Pointed ℓ
  FiberSpSpace n = fiber∙ (f .fst n)

  -- This is just EquivJ but the other way around
  EquivJ' : {ℓ ℓ' : Level} {A B : Type ℓ} (P : (B : Type ℓ) → (e : A ≃ B) → Type ℓ')
      → (r : P A (idEquiv A)) → (e : A ≃ B) → P B e
  EquivJ' {A = A} {B} P r e =
    let r' = subst (λ z → P A z) (sym pathToEquivRefl) r in
    let zz = J (λ B' p' → P B' (pathToEquiv p')) r' (ua e) in
    subst (λ z → P B z) (pathToEquiv-ua e) zz

  Equiv∙J' : {ℓ ℓ' : Level} {A : Pointed ℓ} (C : (B : Pointed ℓ) → A ≃∙ B → Type ℓ')
        → C A (idEquiv (fst A) , refl)
        → {B : _} (e : A ≃∙ B) → C B e
  Equiv∙J' {ℓ = ℓ} {ℓ'} {A} C ind {B} (e , e₀) = let
    ind2 =
      EquivJ'
      (λ B' e' → (a' : ⟨ A ⟩) → (b' : B')
        → (p' : e' .fst a' ≡ b')
        → (C' : (B'' : Pointed ℓ) → A .fst , a' ≃∙ B'' → Type ℓ')
        → C' (A .fst , a') ((idEquiv (A .fst)) , refl)
        → C' (B' , b') (e' , p'))
      (λ a' b' p' C' ind' → J (λ b'' p'' → C' (A .fst , b'') ((idEquiv (A .fst)) , p'')) ind' p')
    in ind2 e (A .snd) (B .snd) e₀ C ind

  FiberSpMap : (n : ℤ) → FiberSpSpace n ≃∙ Ω (FiberSpSpace (sucℤ n))
  FiberSpMap n = compEquiv∙ fib[fn]≡fib[Ωfn+1] Ωfib[fn+1]≡fib[Ωfn+1] where
    preEquivFiber : {ℓ : Level} {A B C : Pointed ℓ} (e : A ≃∙ B) (f : B →∙ C) → fiber∙ f ≃∙ fiber∙ (f ∘∙ ≃∙map e)
    preEquivFiber {A = A} {B} {C} e∙ @ (e , e₀) f∙ @ (f , f₀) =
      Equiv∙J' (λ B' e' → (f' : B' →∙ C) → fiber∙ f' ≃∙ fiber∙ (f' ∘∙ ≃∙map e')) reflCase e∙ f∙ where
        reflCase : (f' : (fst A , A .snd) →∙ C) → fiber∙ f' ≃∙ fiber∙ (f' ∘∙ ≃∙map (idEquiv (fst A) , refl))
        reflCase f' .fst = isoToEquiv (iso (idfun _) (idfun _) (λ _ → refl) (λ _ → refl))
        reflCase f' .snd = ΣPathP (refl , (lUnit _))

    postEquivFiber : {ℓ : Level} {A B C : Pointed ℓ} (f : A →∙ B) (e : B ≃∙ C) → fiber∙ f ≃∙ fiber∙ (≃∙map e ∘∙ f)
    postEquivFiber {A = A} {B} {C} f∙ @ (f , f₀) e∙ @ (e , e₀) =
      Equiv∙J (λ B' e' → (f' : A →∙ B') → fiber∙ f' ≃∙ fiber∙ (≃∙map e' ∘∙ f')) reflCase e∙ f∙ where
        reflCase : (f' : A →∙ C) → fiber∙ f' ≃∙ fiber∙ (≃∙map (idEquiv (fst C) , refl) ∘∙ f')
        reflCase f' .fst = isoToEquiv (iso (idfun _) (idfun _) (λ _ → refl) (λ _ → refl))
        reflCase f' .snd = ΣPathP (refl , rUnit (f' .snd))

    fib[fn]≡fib[Ωfn+1] : fiber∙ (f .fst n) ≃∙ fiber∙ (Ω→ (f .fst (sucℤ n)))
    fib[fn]≡fib[Ωfn+1] = compEquiv∙ seg1 (compEquiv∙ seg2 (invEquiv∙ seg3)) where
      seg1 : fiber∙ (f .fst n) ≃∙ fiber∙ (≃∙map (spectrumEquiv Y n) ∘∙ f .fst n)
      seg1 = postEquivFiber (f .fst n) (spectrumEquiv Y n)

      seg3 : fiber∙ (Ω→ (f .fst (sucℤ n))) ≃∙ fiber∙ (Ω→ (f .fst (sucℤ n)) ∘∙ ≃∙map (spectrumEquiv X n))
      seg3 = preEquivFiber (spectrumEquiv X n) (Ω→ (f .fst (sucℤ n)))

      pathToEquiv∙ : {A B : Pointed ℓ} → (A ≡ B) → A ≃∙ B
      pathToEquiv∙ p .fst = pathToEquiv (cong fst p)
      pathToEquiv∙ p .snd = fromPathP (cong snd p)

      seg2 : fiber∙ (≃∙map (spectrumEquiv Y n) ∘∙ f .fst n) ≃∙ fiber∙ (Ω→ (f .fst (sucℤ n)) ∘∙ ≃∙map (spectrumEquiv X n))
      seg2 = fiber∙-respects-∙∼ (f .snd n)

    Ωfib[fn+1]≡fib[Ωfn+1] : fiber∙ (Ω→ (f .fst (sucℤ n))) ≃∙ Ω (FiberSpSpace (sucℤ n))
    Ωfib[fn+1]≡fib[Ωfn+1] = invEquiv∙ ((isoToEquiv (ΩFibreIso (f .fst (sucℤ n)))) , ΩFibreIso∙ (f .fst (sucℤ n)))

  FiberSp : Spectrum ℓ
  FiberSp .prespectrum .space = FiberSpSpace
  FiberSp .prespectrum .map n = ≃∙map (FiberSpMap n)
  FiberSp .equiv n = FiberSpMap n .fst .snd
