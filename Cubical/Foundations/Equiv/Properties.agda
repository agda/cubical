{-

A couple of general facts about equivalences:

- if f is an equivalence then (cong f) is an equivalence ([equivCong])
- if f is an equivalence then pre- and postcomposition with f are equivalences ([preCompEquiv], [postCompEquiv])
- if f is an equivalence then (Σ[ g ] section f g) and (Σ[ g ] retract f g) are contractible ([isContr-section], [isContr-retract])

(these are not in 'Equiv.agda' because they need Univalence.agda (which imports Equiv.agda))
-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.Equiv.Properties where

open import Cubical.Core.Everything

open import Cubical.Data.Sigma

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism

open import Cubical.Foundations.FunExtEquiv


isEquivCong : ∀ {ℓ} {A B : Type ℓ} {x y : A} (e : A ≃ B) → isEquiv (λ (p : x ≡ y) → (cong (fst e) p))
isEquivCong e = EquivJ (λ (B' A' : Type _) (e' : A' ≃ B') →
                         (x' y' : A') → isEquiv (λ (p : x' ≡ y') → cong (fst e') p))
                       (λ _ x' y' → idIsEquiv (x' ≡ y')) _ _ e _ _

congEquiv : ∀ {ℓ} {A B : Type ℓ} {x y : A} (e : A ≃ B) → (x ≡ y) ≃ (e .fst x ≡ e .fst y)
congEquiv e = ((λ (p : _ ≡ _) → cong (fst e) p) , isEquivCong e)

isEquivPreComp : ∀ {ℓ ℓ′} {A B : Type ℓ} {C : Type ℓ′} (e : A ≃ B)
  → isEquiv (λ (φ : B → C) → φ ∘ e .fst)
isEquivPreComp {A = A} {C = C} e = EquivJ
                  (λ (B A : Type _) (e' : A ≃ B) → isEquiv (λ (φ : B → C) → φ ∘ e' .fst))
                  (λ A → idIsEquiv (A → C)) _ _ e

isEquivPostComp : ∀ {ℓ ℓ′} {A B : Type ℓ} {C : Type ℓ′} (e : A ≃ B)
  → isEquiv (λ (φ : C → A) → e .fst ∘ φ)
isEquivPostComp {A = A} {C = C} e = EquivJ
                  (λ (B A : Type _) (e' : A ≃ B) →  isEquiv (λ (φ : C → A) → e' .fst ∘ φ))
                  (λ A → idIsEquiv (C → A)) _ _ e

preCompEquiv : ∀ {ℓ ℓ′} {A B : Type ℓ} {C : Type ℓ′} (e : A ≃ B)
             → (B → C) ≃ (A → C)
preCompEquiv e = (λ φ x → φ (fst e x)) , isEquivPreComp e

postCompEquiv : ∀ {ℓ ℓ′} {A B : Type ℓ} {C : Type ℓ′} (e : A ≃ B)
             → (C → A) ≃ (C → B)
postCompEquiv e = (λ φ x → fst e (φ x)) , isEquivPostComp e


isContr-section : ∀ {ℓ} {A B : Type ℓ} (e : A ≃ B) → isContr (Σ[ g ∈ (B → A) ] section (fst e) g)
fst (isContr-section e) = invEq e , retEq e
snd (isContr-section e) (f , ε) i = (λ b → fst (p b i)) , (λ b → snd (p b i))
  where p : ∀ b → (invEq e b , retEq e b) ≡ (f b , ε b)
        p b = snd (equiv-proof (snd e) b) (f b , ε b)

-- there is a (much slower) alternate proof that also works for retract

isContr-section' : ∀ {ℓ} {A B : Type ℓ} (e : A ≃ B) → isContr (Σ[ g ∈ (B → A) ] section (fst e) g)
isContr-section' {_} {A} {B} e = transport (λ i → isContr (Σ[ g ∈ (B → A) ] eq g i))
                                           (equiv-proof (isEquivPostComp e) (idfun _))
  where eq : ∀ (g : B → A) → ((fst e) ∘ g ≡ idfun _) ≡ (section (fst e) g)
        eq g = sym (funExtPath {f = (fst e) ∘ g} {g = idfun _})

isContr-retract : ∀ {ℓ} {A B : Type ℓ} (e : A ≃ B) → isContr (Σ[ g ∈ (B → A) ] retract (fst e) g)
isContr-retract {_} {A} {B} e = transport (λ i → isContr (Σ[ g ∈ (B → A) ] eq g i))
                                           (equiv-proof (isEquivPreComp e) (idfun _))
  where eq : ∀ (g : B → A) → (g ∘ (fst e) ≡ idfun _) ≡ (retract (fst e) g)
        eq g = sym (funExtPath {f = g ∘ (fst e)} {g = idfun _})

