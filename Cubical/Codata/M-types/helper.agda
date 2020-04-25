{-# OPTIONS --cubical --guardedness #-} --safe

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Function using (_∘_)

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path

open import Cubical.Functions.Embedding
open import Cubical.Functions.FunExtEquiv

module Cubical.Codata.M-types.helper where

module helper where

open Iso

refl-fun : ∀ {ℓ} {A : Set ℓ} (x : A) → x ≡ x
refl-fun x = refl {x = x}

-- Right
extent-r : ∀ {ℓ} {A B C : Set ℓ} {a b : A -> B} (f : C -> A) -> a ≡ b -> a ∘ f ≡ b ∘ f
extent-r = λ f x i → x i ∘ f

identity-f-r : ∀ {ℓ} {A B : Set ℓ} {k : A -> A} -> k ≡ idfun A -> ∀ (f : B -> A) -> k ∘ f ≡ f
identity-f-r {A = A} {k = k} p f = extent-r {a = k} {b = idfun A} f p

-- Left
extent-l : ∀ {ℓ} {A B C : Set ℓ} {a b : A -> B} (f : B -> C) -> a ≡ b -> f ∘ a ≡ f ∘ b
extent-l = λ f x i → f ∘ x i

identity-f-l : ∀ {ℓ} {A B : Set ℓ} {k : A -> A} -> k ≡ idfun A -> ∀ (f : A -> B) -> f ∘ k ≡ f
identity-f-l {A = A} {k = k} p f = extent-l {a = k} {b = idfun A} f p

-- General

-- Iso→monomorphism : -- TODO: Not used !
--   ∀ {ℓ} {A B C : Set ℓ}
--   → (isom : Iso A B)
--   --------------------
--   → {f g : C -> A}
--   → (fun isom ∘ f ≡ fun isom ∘ g)
--   → (f ≡ g)
-- Iso→monomorphism (iso a b right left) {f = f} {g = g} p =
--   (sym (identity-f-r (funExt left) f)) ∙ (λ k → b ∘ p k) ∙ (identity-f-r (funExt left) g)

iso→fun-Injection :
  ∀ {ℓ} {A B C : Set ℓ} (isom : Iso A B)
  → ∀ {f g : C -> A}
  → (x : C) → (Iso.fun isom (f x) ≡ Iso.fun isom (g x)) ≡ (f x ≡ g x)
iso→fun-Injection {A = A} {B} {C} isom {f = f} {g} =
  isEmbedding→Injection {A = A} {B} {C} (Iso.fun isom) (iso→isEmbedding {A = A} {B} isom) {f = f} {g = g}

abstract
  iso→Pi-fun-Injection :
    ∀ {ℓ} {A B C : Set ℓ} (isom : Iso A B)
    → ∀ {f g : C -> A}
    → Iso (∀ x → (fun isom) (f x) ≡ (fun isom) (g x)) (∀ x → f x ≡ g x)
  iso→Pi-fun-Injection {A = A} {B} {C} isom {f = f} {g} =
    pathToIso (cong (λ k → ∀ x → k x) (funExt (iso→fun-Injection isom {f = f} {g = g})))

iso→fun-Injection-Iso :
  ∀ {ℓ} {A B C : Set ℓ} (isom : Iso A B)
  → ∀ {f g : C -> A}
  → Iso (fun isom ∘ f ≡ fun isom ∘ g) (f ≡ g)
iso→fun-Injection-Iso {A = A} {B} {C} isom {f = f} {g} =
  (fun isom) ∘ f ≡ (fun isom) ∘ g
    Iso⟨ isoInv funExtIso ⟩
  (∀ x → (fun isom) (f x) ≡ (fun isom) (g x))
     Iso⟨ iso→Pi-fun-Injection isom ⟩
  (∀ x → f x ≡ g x)
     Iso⟨ funExtIso ⟩
  f ≡ g ∎Iso

iso→fun-Injection-Path :
  ∀ {ℓ} {A B C : Set ℓ} (isom : Iso A B)
  → ∀ {f g : C -> A}
  → (fun isom ∘ f ≡ fun isom ∘ g) ≡ (f ≡ g)
iso→fun-Injection-Path {A = A} {B} {C} isom {f = f} {g} =
  isoToPath (iso→fun-Injection-Iso isom)

iso→inv-Injection-Path :
  ∀ {ℓ} {A B C : Set ℓ} (isom : Iso A B) →
  ∀ {f g : C -> B} →
  -----------------------
  ((inv isom) ∘ f ≡ (inv isom) ∘ g) ≡ (f ≡ g)
iso→inv-Injection-Path {A = A} {B} {C} isom {f = f} {g} = iso→fun-Injection-Path (isoInv isom)


iso→fun-Injection-Iso-x :
    ∀ {ℓ} {A B : Set ℓ}
    → (isom : Iso A B)
    → ∀ {x y : A}
    → Iso ((fun isom) x ≡ (fun isom) y) (x ≡ y)
iso→fun-Injection-Iso-x isom {x} {y} =
    let tempx = λ {(lift tt) → x}
        tempy = λ {(lift tt) → y} in
    fun isom x ≡ fun isom y
      Iso⟨ iso (λ x₁ t → x₁)
               (λ x₁ → x₁ (lift tt))
               refl-fun
               refl-fun ⟩
    (∀ (t : Lift Unit) -> (((fun isom) ∘ tempx) t ≡ ((fun isom) ∘ tempy) t))
      Iso⟨ iso→Pi-fun-Injection isom ⟩
    (∀ (t : Lift Unit) -> tempx t ≡ tempy t)
      Iso⟨ iso (λ x₁ → x₁ (lift tt))
               (λ x₁ t → x₁)
               refl-fun
               refl-fun ⟩
    x ≡ y ∎Iso

iso→inv-Injection-Iso-x :
  ∀ {ℓ} {A B : Set ℓ}
  → (isom : Iso A B)
  → ∀ {x y : B}
  → Iso ((inv isom) x ≡ (inv isom) y) (x ≡ y)
iso→inv-Injection-Iso-x {A = A} {B = B} isom =
  iso→fun-Injection-Iso-x {A = B} {B = A} (isoInv isom)

iso→fun-Injection-Path-x :
  ∀ {ℓ} {A B : Set ℓ}
  → (isom : Iso A B)
  → ∀ {x y : A}
  → ((fun isom) x ≡ (fun isom) y) ≡ (x ≡ y)
iso→fun-Injection-Path-x isom {x} {y} =
  isoToPath (iso→fun-Injection-Iso-x isom)

iso→inv-Injection-Path-x :
  ∀ {ℓ} {A B : Set ℓ}
  → (isom : Iso A B)
  → ∀ {x y : B}
  → ((inv isom) x ≡ (inv isom) y) ≡ (x ≡ y)
iso→inv-Injection-Path-x isom =
  isoToPath (iso→inv-Injection-Iso-x isom)

-------------------------
-- Unit / × properties --
-------------------------

diagonal-unit : Unit ≡ Unit × Unit
diagonal-unit = isoToPath (iso (λ x → tt , tt) (λ x → tt) (λ {(tt , tt) i → tt , tt}) λ {tt i → tt})
