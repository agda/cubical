{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Data.Fin.Inductive.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Data.Fin.Inductive.Base

open import Cubical.Data.Nat
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Data.Fin.Base as FinOld
  hiding (Fin ; injectSuc ; fsuc ; fzero ; flast ; ¬Fin0 ; sumFinGen)
open import Cubical.Data.Fin.Properties as FinOldProps
  hiding (sumFinGen0 ; isSetFin ; sumFin-choose ; sumFinGenHom ; sumFinGenId)

open import Cubical.Relation.Nullary

open import Cubical.Algebra.AbGroup.Base using (move4)

fsuc-injectSuc : {m : ℕ} (n : Fin m)
  → injectSuc {n = suc m} (fsuc {n = m} n) ≡ fsuc (injectSuc n)
fsuc-injectSuc {m = suc m} (x , p) = refl


elimFin : ∀ {ℓ} {m : ℕ} {A : Fin (suc m) → Type ℓ}
                 (max : A flast)
                 (f : (x : Fin m) → A (injectSuc x))
              → (x : _) → A x
elimFin {m = zero} {A = A} max f (zero , p) = max
elimFin {m = suc m} {A = A} max f (zero , p) = f (zero , tt)
elimFin {m = suc zero} {A = A} max f (suc zero , p) = max
elimFin {m = suc (suc m)} {A = A} max f (suc x , p) =
  elimFin {m = suc m} {A = λ x → A (fsuc x)} max (λ t → f (fsuc t)) (x , p)

elimFin-alt : ∀ {ℓ} {m : ℕ} {A : Fin (suc m) → Type ℓ}
                 (max : A fzero)
                 (f : (x : Fin m) → A (fsuc x))
              → (x : _) → A x
elimFin-alt {m = zero} max f (zero , p) = max
elimFin-alt {m = suc m} max f (zero , p) = max
elimFin-alt {m = suc m} max f (suc x , p) = f (x , p)

elimFinβ : ∀ {ℓ} {m : ℕ} {A : Fin (suc m) → Type ℓ}
                 (max : A flast)
                 (f : (x : Fin m) → A (injectSuc x))
              → ((elimFin {A = A} max f flast ≡ max))
               × ((x : Fin m) → elimFin {A = A} max f (injectSuc x) ≡ f x)
elimFinβ {m = zero} {A = A} max f = refl , λ {()}
elimFinβ {m = suc zero} {A = A} max f = refl , λ {(zero , p) → refl}
elimFinβ {m = suc (suc m)} {A = A} max f =
  elimFinβ {m = (suc m)} {A = λ x → A (fsuc x)} max _ .fst
  , elimFin-alt {m = (suc m)} {A = λ x → elimFin max f (injectSuc {n = suc (suc m)} x) ≡ f x}
             refl
             (elimFinβ {m = (suc m)} {A = λ x → A (fsuc x)} max _ .snd)

¬Fin0 : ¬ Fin 0
¬Fin0 (x , ())

-- properties of finite sums
module _ {ℓ : Level} {A : Type ℓ} (_+A_ : A → A → A) (0A : A)
  (rUnit : (x : _) → x +A 0A ≡ x)
   where
  sumFinGen0 : (n : ℕ) (f : Fin n → A)
    → ((x : _) → f x ≡ 0A)
    → sumFinGen _+A_ 0A f
    ≡ 0A
  sumFinGen0 zero f ind = refl
  sumFinGen0 (suc n) f ind =
    cong₂ _+A_
      (ind flast)
      (sumFinGen0 n (f ∘ injectSuc) (λ x → ind (injectSuc x))) ∙ rUnit 0A

  module _ (comm : (x y : A) → x +A y ≡ y +A x) where
    private
      lUnitA : (x : _) → 0A +A x ≡ x
      lUnitA x = comm _ _ ∙ rUnit x

    sumFin-choose :
      {n : ℕ} (f : Fin n → A)
      → (a : A) (x : Fin n)
      → (f x ≡ a)
      → ((x' : Fin n) → ¬ (x' ≡ x) → f x' ≡ 0A)
      → sumFinGen {n = n} _+A_ 0A f ≡ a
    sumFin-choose {zero} f a x p t = ⊥.rec (¬Fin0 x)
    sumFin-choose {suc n} f a (x , q) p t with (n ≟ᵗ x)
    ... | lt x₁ = ⊥.rec (¬squeeze (q , x₁))
    ... | eq x₁ =
      cong (f flast +A_) (sumFinGen0 n _ λ h → t _
        λ q → ¬m<ᵗm (subst (_<ᵗ n) (cong fst q ∙ sym x₁) (snd h)))
      ∙ rUnit _ ∙ cong f (sym x=flast) ∙ p
      where
      x=flast : (x , q) ≡ flast
      x=flast = Σ≡Prop (λ _ → isProp<ᵗ) (sym x₁)
    ... | gt x₁ =
      cong₂ _+A_
         (t flast (λ p → ¬m<ᵗm (subst (_<ᵗ n) (sym (cong fst p)) x₁)))
         refl
      ∙ lUnitA _
      ∙ sumFin-choose {n = n} (f ∘ injectSuc) a (x , x₁)
          (cong f (Σ≡Prop (λ _ → isProp<ᵗ) refl) ∙ p)
          λ a r → t (injectSuc a) λ d → r (Σ≡Prop (λ _ → isProp<ᵗ)
          (cong fst d))

    module _ (assocA : (x y z : A) → x +A (y +A z) ≡ (x +A y) +A z) where
      sumFinGenHom : (n : ℕ) (f g : Fin n → A)
        → sumFinGen _+A_ 0A (λ x → f x +A g x)
         ≡ (sumFinGen _+A_ 0A f +A sumFinGen _+A_ 0A g)
      sumFinGenHom zero f g = sym (rUnit 0A)
      sumFinGenHom (suc n) f g =
          cong ((f flast +A g flast) +A_) (sumFinGenHom n (f ∘ injectSuc) (g ∘ injectSuc))
        ∙ move4 (f flast) (g flast)
                (sumFinGen _+A_ 0A (λ x → f (injectSuc x)))
                (sumFinGen _+A_ 0A (λ x → g (injectSuc x)))
                _+A_ assocA comm

sumFinGenId : ∀ {ℓ} {A : Type ℓ} {n : ℕ} (_+_ : A → A → A) (0A : A)
  (f g : Fin n → A) → f ≡ g → sumFinGen _+_ 0A f ≡ sumFinGen _+_ 0A g
sumFinGenId _+_ 0A f g p i = sumFinGen _+_ 0A (p i)

Iso-Fin-InductiveFin : (m : ℕ) → Iso (FinOld.Fin m) (Fin m)
Iso.fun (Iso-Fin-InductiveFin m) (x , p) = x , <→<ᵗ p
Iso.inv (Iso-Fin-InductiveFin m) (x , p) = x , <ᵗ→< p
Iso.rightInv (Iso-Fin-InductiveFin m) (x , p) =
  Σ≡Prop (λ w → isProp<ᵗ {n = w} {m}) refl
Iso.leftInv (Iso-Fin-InductiveFin m) _ = Σ≡Prop (λ _ → isProp≤) refl

isSetFin : {n : ℕ} → isSet (Fin n)
isSetFin {n = n} =
  isOfHLevelRetractFromIso 2 (invIso (Iso-Fin-InductiveFin n))
    FinOldProps.isSetFin
