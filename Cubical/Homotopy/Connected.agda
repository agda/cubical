{-# OPTIONS --cubical --safe #-}
module Cubical.Homotopy.Connected where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Univalence
open import Cubical.Functions.Fibration
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.HITs.Nullification
open import Cubical.HITs.Truncation as Trunc

isHLevelConnected : ∀ {ℓ} (n : ℕ) (A : Type ℓ) → Type ℓ
isHLevelConnected n A = isContr (hLevelTrunc n A)

isHLevelConnectedFun : ∀ {ℓ ℓ'} (n : ℕ) {A : Type ℓ} {B : Type ℓ'} (f : A → B) → Type (ℓ-max ℓ ℓ')
isHLevelConnectedFun n f = ∀ b → isHLevelConnected n (fiber f b)

isEquivPrecomposeConnected : ∀ {ℓ ℓ' ℓ''} (n : ℕ)
  {A : Type ℓ} {B : Type ℓ'} (P : B → HLevel ℓ'' n) (f : A → B)
  → isHLevelConnectedFun n f
  → isEquiv (λ(s : (b : B) → P b .fst) → s ∘ f)
isEquivPrecomposeConnected n {A} {B} P f fConn =
  isoToIsEquiv
    (iso (_∘ f)
      (λ t b → inv t b (fConn b .fst))
      (λ t → funExt λ a →
        cong (inv t (f a)) (fConn (f a) .snd ∣ a , refl ∣)
        ∙ substRefl {B = fst ∘ P} (t a))
      (λ s → funExt λ b →
        Trunc.elim
          {B = λ d → inv (s ∘ f) b d ≡ s b}
          (λ _ → isOfHLevelPath n (P b .snd) _ _)
          (λ {(a , p) i → transp (λ j → P (p (j ∨ i)) .fst) i (s (p i))})
          (fConn b .fst)))
  where
  inv : ((a : A) → P (f a) .fst) → (b : B) → hLevelTrunc n (fiber f b) → P b .fst
  inv t b =
    Trunc.rec
      (P b .snd)
      (λ {(a , p) → subst (fst ∘ P) p (t a)})

isOfHLevelPrecomposeConnected : ∀ {ℓ ℓ' ℓ''} (k : ℕ) (n : ℕ)
  {A : Type ℓ} {B : Type ℓ'} (P : B → HLevel ℓ'' (k + n)) (f : A → B)
  → isHLevelConnectedFun n f
  → isOfHLevelFun k (λ(s : (b : B) → P b .fst) → s ∘ f)
isOfHLevelPrecomposeConnected zero n P f fConn =
  isEquivPrecomposeConnected n P f fConn .equiv-proof
isOfHLevelPrecomposeConnected (suc k) n P f fConn t =
    isOfHLevelPath'⁻ k
      (λ {(s₀ , p₀) (s₁ , p₁) →
        subst (isOfHLevel k) (sym (fiber≡ (s₀ , p₀) (s₁ , p₁)))
          (isOfHLevelRetract k
            (λ {(q , α) → (funExt⁻ q) , (cong funExt⁻ α)})
            (λ {(h , β) → (funExt h) , (cong funExt β)})
            (λ _ → refl)
            (isOfHLevelPrecomposeConnected k n
              (λ b → (s₀ b ≡ s₁ b) , isOfHLevelPath' (k + n) (P b .snd) _ _)
              f fConn
              (funExt⁻ (p₀ ∙∙ refl ∙∙ sym p₁))))})

isHLevelConnectedPath : ∀ {ℓ} (n : ℕ) {A : Type ℓ}
  → isHLevelConnected (suc n) A
  → (a₀ a₁ : A) → isHLevelConnected n (a₀ ≡ a₁)
isHLevelConnectedPath n connA a₀ a₁ =
  subst isContr (PathIdTrunc _)
    (isContr→isContrPath connA _ _)

isHLevelConnectedRetract : ∀ {ℓ ℓ'} (n : ℕ)
  {A : Type ℓ} {B : Type ℓ'}
  (f : A → B) (g : B → A)
  (h : (x : A) → g (f x) ≡ x)
  → isHLevelConnected n B → isHLevelConnected n A
isHLevelConnectedRetract n f g h =
  isContrRetract
    (Trunc.map f)
    (Trunc.map g)
    (Trunc.elim
      (λ _ → isOfHLevelPath n (isOfHLevelTrunc n) _ _)
      (λ a → cong ∣_∣ (h a)))

isHLevelConnectedPoint : ∀ {ℓ} (n : ℕ) {A : Type ℓ}
  → isHLevelConnected (suc n) A
  → (a : A) → isHLevelConnectedFun n (λ(_ : Unit) → a)
isHLevelConnectedPoint n connA a₀ a =
  isHLevelConnectedRetract n
    snd (_ ,_) (λ _ → refl)
    (isHLevelConnectedPath n connA a₀ a)

