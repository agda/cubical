module Cubical.Foundations.Pointed.Fiber where

open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv.Base
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Prelude

private variable ℓ ℓ' : Level

{- pointed version of fibers -}

fiber∙ : ∀ {A : Pointed ℓ} {B : Pointed ℓ'} (f : A →∙ B) → Pointed (ℓ-max ℓ ℓ')
fiber∙ {ℓ} {ℓ'} {A = A} {B} f .fst = fiber (f .fst) (B .snd)
fiber∙ {ℓ} {ℓ'} {A = A} {B} f .snd = (A .snd) , f .snd

fiber∙-respects-∙∼ : {A : Pointed ℓ} {B : Pointed ℓ'}
  → {f g : A →∙ B}
  → (h : f ∙∼ g)
  → fiber∙ f ≃∙ fiber∙ g
fiber∙-respects-∙∼ {A = A} {B} {f} {g} h = isoToEquiv (iso fwd bwd sec ret) , prf where
  fwd : fst (fiber∙ f) → fst (fiber∙ g)
  fwd (a , f[a]≡b₀) = a , (sym (h .fst a) ∙ f[a]≡b₀)

  bwd : fst (fiber∙ g) → fst (fiber∙ f)
  bwd (a , g[a]≡b₀) = a , h .fst a ∙ g[a]≡b₀

  sec : section fwd bwd
  sec (a , g[a]≡b₀) = ΣPathP (refl , (
    sym (h .fst a) ∙ h .fst a ∙ g[a]≡b₀ ≡⟨ assoc _ _ _ ⟩
    (sym (h .fst a) ∙ h .fst a) ∙ g[a]≡b₀ ≡⟨ cong (_∙ g[a]≡b₀) (lCancel _) ⟩
    refl ∙ g[a]≡b₀ ≡⟨ sym (lUnit _) ⟩
    g[a]≡b₀ ∎))

  ret : retract fwd bwd
  ret (a , f[a]≡b₀) = ΣPathP (refl , (
    h .fst a ∙ sym (h .fst a) ∙ f[a]≡b₀ ≡⟨ assoc _ _ _ ⟩
    (h .fst a ∙ sym (h .fst a)) ∙ f[a]≡b₀ ≡⟨ cong (_∙ f[a]≡b₀) (rCancel _) ⟩
    refl ∙ f[a]≡b₀ ≡⟨ sym (lUnit _) ⟩
    f[a]≡b₀ ∎))

  prf : fwd (A .snd , f .snd) ≡ (A .snd , g .snd)
  prf = ΣPathP (refl , (
    sym (h .fst (A .snd)) ∙ f .snd ≡⟨ cong (λ p → sym p ∙ f .snd) (h .snd) ⟩
    sym (f .snd ∙ sym (g .snd)) ∙ f .snd ≡⟨ cong (_∙ f .snd) (symDistr _ _) ⟩
    (sym (sym (g .snd)) ∙ sym (f .snd)) ∙ f .snd ≡⟨ sym (assoc _ _ _) ⟩
    sym (sym (g .snd)) ∙ sym (f .snd) ∙ f .snd ≡⟨ cong (sym (sym (g .snd)) ∙_) (lCancel _) ⟩
    sym (sym (g .snd)) ∙ refl ≡⟨ sym (rUnit _) ⟩
    sym (sym (g .snd)) ≡⟨ sym (symInvo _) ⟩
    g .snd ∎))

