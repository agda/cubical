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

open import Cubical.Functions.FunExtEquiv

private
  variable
    ℓ ℓ′ : Level
    A B : Type ℓ


isEquivCong : ∀ {ℓ} {A B : Type ℓ} {x y : A} (e : A ≃ B) → isEquiv (λ (p : x ≡ y) → (cong (fst e) p))
isEquivCong {B = B} e = EquivJ (λ (A' : Type _) (e' : A' ≃ B) →
                               (x' y' : A') → isEquiv (λ (p : x' ≡ y') → cong (fst e') p))
                               (λ x' y' → idIsEquiv (x' ≡ y')) e _ _

congEquiv : ∀ {ℓ} {A B : Type ℓ} {x y : A} (e : A ≃ B) → (x ≡ y) ≃ (e .fst x ≡ e .fst y)
congEquiv e = ((λ (p : _ ≡ _) → cong (fst e) p) , isEquivCong e)

isEquivPreComp : ∀ {ℓ ℓ′} {A B : Type ℓ} {C : Type ℓ′} (e : A ≃ B)
  → isEquiv (λ (φ : B → C) → φ ∘ e .fst)
isEquivPreComp {A = A} {B} {C} e = EquivJ
                  (λ (A : Type _) (e' : A ≃ B) → isEquiv (λ (φ : B → C) → φ ∘ e' .fst))
                  (idIsEquiv (B → C)) e

isEquivPostComp : ∀ {ℓ ℓ′} {A B : Type ℓ} {C : Type ℓ′} (e : A ≃ B)
  → isEquiv (λ (φ : C → A) → e .fst ∘ φ)
isEquivPostComp {A = A} {B} {C} e = EquivJ
                  (λ (A : Type _) (e' : A ≃ B) →  isEquiv (λ (φ : C → A) → e' .fst ∘ φ))
                  (idIsEquiv (C → B)) e

preCompEquiv : ∀ {ℓ ℓ′} {A B : Type ℓ} {C : Type ℓ′} (e : A ≃ B)
             → (B → C) ≃ (A → C)
preCompEquiv e = (λ φ x → φ (fst e x)) , isEquivPreComp e

postCompEquiv : ∀ {ℓ ℓ′} {A B : Type ℓ} {C : Type ℓ′} (e : A ≃ B)
             → (C → A) ≃ (C → B)
postCompEquiv e = (λ φ x → fst e (φ x)) , isEquivPostComp e


hasSection : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (A → B) → Type _
hasSection {A = A} {B} f = Σ[ g ∈ (B → A) ] section f g

hasRetract : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (A → B) → Type _
hasRetract {A = A} {B} f = Σ[ g ∈ (B → A) ] retract f g

isEquiv-hasSection : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B)
                    → isEquiv f
                    → hasSection f
isEquiv-hasSection f isEq = (λ b → equiv-proof isEq b .fst .fst) ,
                            λ b → equiv-proof isEq b .fst .snd

isContr-hasSection : ∀ {ℓ} {A B : Type ℓ} (e : A ≃ B) → isContr (hasSection (fst e))
fst (isContr-hasSection e) = invEq e , retEq e
snd (isContr-hasSection e) (f , ε) i = (λ b → fst (p b i)) , (λ b → snd (p b i))
  where p : ∀ b → (invEq e b , retEq e b) ≡ (f b , ε b)
        p b = snd (equiv-proof (snd e) b) (f b , ε b)

-- there is a (much slower) alternate proof that also works for retract

isContr-hasSection' : ∀ {ℓ} {A B : Type ℓ} (e : A ≃ B) → isContr (hasSection (fst e))
isContr-hasSection' {_} {A} {B} e = transport (λ i → isContr (Σ[ g ∈ (B → A) ] eq g i))
                                              (equiv-proof (isEquivPostComp e) (idfun _))
  where eq : ∀ (g : B → A) → ((fst e) ∘ g ≡ idfun _) ≡ (section (fst e) g)
        eq g = sym (funExtPath {f = (fst e) ∘ g} {g = idfun _})

isContr-hasRetract : ∀ {ℓ} {A B : Type ℓ} (e : A ≃ B) → isContr (hasRetract (fst e))
isContr-hasRetract {_} {A} {B} e = transport (λ i → isContr (Σ[ g ∈ (B → A) ] eq g i))
                                              (equiv-proof (isEquivPreComp e) (idfun _))
  where eq : ∀ (g : B → A) → (g ∘ (fst e) ≡ idfun _) ≡ (retract (fst e) g)
        eq g = sym (funExtPath {f = g ∘ (fst e)} {g = idfun _})


cong≃ : (F : Type ℓ → Type ℓ′) → (A ≃ B) → F A ≃ F B
cong≃ F e = pathToEquiv (cong F (ua e))

cong≃-char : (F : Type ℓ → Type ℓ′) {A B : Type ℓ} (e : A ≃ B) → ua (cong≃ F e) ≡ cong F (ua e)
cong≃-char F e = ua-pathToEquiv (cong F (ua e))

cong≃-idEquiv : (F : Type ℓ → Type ℓ′) (A : Type ℓ) → cong≃ F (idEquiv A) ≡ idEquiv (F A)
cong≃-idEquiv F A = cong≃ F (idEquiv A) ≡⟨ cong (λ p → pathToEquiv (cong F p)) uaIdEquiv  ⟩
                    pathToEquiv refl    ≡⟨ pathToEquivRefl ⟩
                    idEquiv (F A)       ∎
