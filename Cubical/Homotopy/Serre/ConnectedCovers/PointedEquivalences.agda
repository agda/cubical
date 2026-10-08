{-# OPTIONS --lossy-unification --safe #-}
module Cubical.Homotopy.Serre.ConnectedCovers.PointedEquivalences where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.HITs.Truncation renaming (elim to truncElim)

open import Cubical.Homotopy.Serre.ConnectedCovers.TruncationLevelFacts

open import Cubical.Homotopy.Serre.FiberOrCofiberSequences.Base

private
  variable
    ℓ : Level

AFamilyParametrised : (F : Pointed ℓ → Pointed ℓ)
  (f : (A : Pointed ℓ) → (A →∙ (F A)))
  → ({A* : Pointed ℓ} → typ A* → Type ℓ)
AFamilyParametrised F f {A* = A*} x = fst (f A*) x ≡ fst (f A*) (pt A*)

truncFam : (n : ℕ) → ({A* : Pointed ℓ} → typ A* → Type ℓ)
truncFam n {A* = A*} =
  AFamilyParametrised (hLevelTrunc∙ n) (λ A → trunc∙ n) {A* = A*}

ΣFamBaseChange : {A A' : Pointed ℓ} (F : Pointed ℓ → Pointed ℓ)
  (f : (A : Pointed ℓ) → (A →∙ (F A))) → (A ≃∙ A')
  → (Σ (typ A) (AFamilyParametrised F f {A* = A}) , (pt A , refl))
   ≃∙ (Σ (typ A') (AFamilyParametrised F f {A* = A'}) , (pt A' , refl))
ΣFamBaseChange {A' = A'} F f =
 Equiv∙J
 (λ A'' e'
 → (Σ (typ A'') (AFamilyParametrised F f {A* = A''}) , (pt A'' , refl))
 ≃∙ (Σ (typ A') (AFamilyParametrised F f {A* = A'}) , (pt A' , refl)))
 (idEquiv _ , refl)


ΣAssoc∙ : {A : Pointed ℓ} {B : typ A → Type ℓ}
  {C : (a : typ A) → B a → Type ℓ} (b' : B (pt A)) (c' : C (pt A) b')
  → (Σ (Σ (typ A) B) (λ (a , b) → C a b) , ((pt A) , b') , c')
  ≃∙ Σ (typ A) (λ a → Σ (B a) (C a)) , (pt A) , (b' , c')
fst (ΣAssoc∙ b' c') = Σ-assoc-≃
snd (ΣAssoc∙ b' c')= refl

trunc≡Equiv∙ : (A : Pointed ℓ) (n : ℕ)
  → ((trunc {X = A} (2 + n) (pt A) ≡ trunc (2 + n) (pt A)) , refl)
  ≃∙ hLevelTrunc∙ (suc n) ((pt A ≡ pt A) , refl)
fst (trunc≡Equiv∙ A n) = isoToEquiv (PathIdTruncIso (suc n))
snd (trunc≡Equiv∙ A n) = cong ∣_∣ (transportRefl refl)

ΣSwapNested : {A : Type ℓ} {B : Type ℓ} {C : A → B → Type ℓ}
  → (Σ A (λ a → Σ B (C a))) ≃ (Σ B (λ b → Σ A (λ a → C a b)))
ΣSwapNested =
  invEquiv Σ-assoc-≃
  ∙ₑ Σ-cong-equiv-fst Σ-swap-≃
  ∙ₑ Σ-assoc-≃

ΣSwap∙ : (A : Type ℓ) (B : Type ℓ) (C : A → B → Type ℓ) (a : A) (b : B)
  (c : C a b) → (Σ A (λ a → Σ B (C a)) , (a , (b , c)))
              ≃∙ (Σ B (λ b → Σ A (λ a → C a b)) , (b , (a , c)))
fst (ΣSwap∙ A B C a b c) =
  invEquiv (fst (ΣAssoc∙ b c))
  ∙ₑ Σ-cong-equiv-fst Σ-swap-≃
  ∙ₑ fst (ΣAssoc∙ a c)
snd (ΣSwap∙ A B C a b c) = refl


ΣContr∙ : (A : Type ℓ) (B : A → Type ℓ) (a : A) (b : B a)
  → ((a' : A) → isContr (B a'))
  → (Σ A B , (a , b)) ≃∙ (A , a)
fst (ΣContr∙ A B a b contrB) = Σ-contractSnd contrB
snd (ΣContr∙ A B a b contrB) = refl


ΣPtdFibEq : {A : Pointed ℓ} {B B' : (typ A) → Type ℓ} (b : B (pt A))
  (b' : B' (pt A))
  (e : (a : typ A) → B a ≃ B' a) → (fst (e (pt A)) b ≡ b')
  → (Σ (typ A) B , (pt A , b)) ≃∙ (Σ (typ A) B' , (pt A , b'))
fst (ΣPtdFibEq b b' e p) = Σ-cong-equiv-snd e
snd (ΣPtdFibEq b b' e p) = ΣPathP (refl , p)

Σ∙FibEq : {A : Pointed ℓ} {B B' : Σ[ P ∈ ((typ A) → Type ℓ) ] P (pt A)}
  → Σ[ e ∈ ((a : typ A) → (fst B) a ≃ (fst B') a) ]
      (fst (e (pt A))) (snd B) ≡ (snd B')
  → (Σ (typ A) (fst B) , (pt A , snd B))
     ≃∙ (Σ (typ A) (fst B') , (pt A , snd B'))
fst (Σ∙FibEq (e , p)) = Σ-cong-equiv-snd e
snd (Σ∙FibEq (e , p)) = ΣPathP (refl , p)

ΣΣ∙FibEq : {A : Pointed ℓ} {B : Σ[ P ∈ ((typ A) → Type ℓ) ] P (pt A)}
  {C C' : Σ[ P ∈ ((a : typ A) → (fst B) a → Type ℓ) ] P (pt A) (snd B)}
  → Σ[ e ∈ ((a : typ A) (b : (fst B) a) → (fst C) a b ≃ (fst C') a b) ]
      (fst (e (pt A) (snd B))) (snd C) ≡ (snd C')
  → Σ[ e ∈ ((a : typ A) → ((Σ[ b ∈ (fst B) a ] (fst C) a b)
                           ≃ (Σ[ b ∈ (fst B) a ] (fst C') a b))) ]
      (fst (e (pt A))) (snd B , snd C) ≡ (snd B , snd C')
fst (ΣΣ∙FibEq (e , p)) a = Σ-cong-equiv-snd (e a)
snd (ΣΣ∙FibEq (e , p)) = ΣPathP (refl , p)

Σ∙FibEqRfl : {A : Pointed ℓ} {B : Σ[ P ∈ ((typ A) → Type ℓ) ] P (pt A)}
  → Σ[ e ∈ ((a : typ A) → (fst B) a ≃ (fst B) a) ]
      (fst (e (pt A))) (snd B) ≡ (snd B)
fst Σ∙FibEqRfl a = idEquiv _
snd Σ∙FibEqRfl = refl

ΣΣ∙FibEqRfl : {A : Pointed ℓ} {B : Σ[ P ∈ ((typ A) → Type ℓ) ] P (pt A)}
  {C : Σ[ P ∈ ((a : typ A) → (fst B) a → Type ℓ) ] P (pt A) (snd B)}
  → Σ[ e ∈ ((a : typ A) (b : (fst B) a) → (fst C) a b ≃ (fst C) a b) ]
      (fst (e (pt A) (snd B))) (snd C) ≡ (snd C)
fst ΣΣ∙FibEqRfl a b = idEquiv _
snd ΣΣ∙FibEqRfl = refl

Σ∙FibEqComp : {A : Pointed ℓ} {B C D : Σ[ P ∈ ((typ A) → Type ℓ) ] P (pt A)}
  → Σ[ e ∈ ((a : typ A) → (fst B) a ≃ (fst C) a) ]
      (fst (e (pt A))) (snd B) ≡ (snd C)
  → Σ[ e ∈ ((a : typ A) → (fst C) a ≃ (fst D) a) ]
      (fst (e (pt A))) (snd C) ≡ (snd D)
  → Σ[ e ∈ ((a : typ A) → (fst B) a ≃ (fst D) a) ]
      (fst (e (pt A))) (snd B) ≡ (snd D)
fst (Σ∙FibEqComp (e , p) (f , q)) a = (e a) ∙ₑ (f a)
snd (Σ∙FibEqComp (e , p) (f , q)) = (cong (fst (f _)) p) ∙ q

ΣΣ∙FibEqComp : {A : Pointed ℓ} {B : Σ[ P ∈ ((typ A) → Type ℓ) ] P (pt A)}
  {C D E : Σ[ P ∈ ((a : typ A) → (fst B) a → Type ℓ) ] P (pt A) (snd B)}
  → Σ[ e ∈ ((a : typ A) (b : (fst B) a) → (fst C) a b ≃ (fst D) a b) ]
      (fst (e (pt A) (snd B))) (snd C) ≡ (snd D)
  → Σ[ e ∈ ((a : typ A) (b : (fst B) a) → (fst D) a b ≃ (fst E) a b) ]
      (fst (e (pt A) (snd B))) (snd D) ≡ (snd E)
  → Σ[ e ∈ ((a : typ A) (b : (fst B) a) → (fst C) a b ≃ (fst E) a b) ]
      (fst (e (pt A) (snd B))) (snd C) ≡ (snd E)
fst (ΣΣ∙FibEqComp (e , p) (f , q)) a b = (e a b) ∙ₑ (f a b)
snd (ΣΣ∙FibEqComp (e , p) (f , q)) = (cong (fst (f _ _)) p) ∙ q

_≃∙F⟨_⟩_ : {A : Pointed ℓ} (B : Σ[ P ∈ ((typ A) → Type ℓ) ] P (pt A))
  {C D : Σ[ P ∈ ((typ A) → Type ℓ) ] P (pt A)}
  → Σ[ e ∈ ((a : typ A) → (fst B) a ≃ (fst C) a) ]
      (fst (e (pt A))) (snd B) ≡ (snd C)
  → Σ[ e ∈ ((a : typ A) → (fst C) a ≃ (fst D) a) ]
      (fst (e (pt A))) (snd C) ≡ (snd D)
  → Σ[ e ∈ ((a : typ A) → (fst B) a ≃ (fst D) a) ]
      (fst (e (pt A))) (snd B) ≡ (snd D)
(B , b) ≃∙F⟨ (e , p) ⟩ (f , q) = Σ∙FibEqComp (e , p) (f , q)

_≃∙FF⟨_⟩_ : {A : Pointed ℓ} {B : Σ[ P ∈ ((typ A) → Type ℓ) ] P (pt A)}
  (C : Σ[ P ∈ ((a : typ A) → (fst B) a → Type ℓ) ] P (pt A) (snd B))
  {D E : Σ[ P ∈ ((a : typ A) → (fst B) a → Type ℓ) ] P (pt A) (snd B)}
  → Σ[ e ∈ ((a : typ A) (b : (fst B) a) → (fst C) a b ≃ (fst D) a b) ]
      (fst (e (pt A) (snd B))) (snd C) ≡ (snd D)
  → Σ[ e ∈ ((a : typ A) (b : (fst B) a) → (fst D) a b ≃ (fst E) a b) ]
      (fst (e (pt A) (snd B))) (snd D) ≡ (snd E)
  → Σ[ e ∈ ((a : typ A) (b : (fst B) a) → (fst C) a b ≃ (fst E) a b) ]
      (fst (e (pt A) (snd B))) (snd C) ≡ (snd E)
C ≃∙FF⟨ (e , p) ⟩ (f , q) = ΣΣ∙FibEqComp (e , p) (f , q)

_≃∙F∎ : {A : Pointed ℓ} (B : Σ[ P ∈ ((typ A) → Type ℓ) ] P (pt A))
  → Σ[ e ∈ ((a : typ A) → (fst B) a ≃ (fst B) a) ]
      (fst (e (pt A))) (snd B) ≡ (snd B)
(B , b) ≃∙F∎ = Σ∙FibEqRfl

_≃∙FF∎ : {A : Pointed ℓ} {B : Σ[ P ∈ ((typ A) → Type ℓ) ] P (pt A)}
  (C : Σ[ P ∈ ((a : typ A) → (fst B) a → Type ℓ) ] P (pt A) (snd B))
  → Σ[ e ∈ ((a : typ A) (b : (fst B) a) → (fst C) a b ≃ (fst C) a b) ]
      (fst (e (pt A) (snd B))) (snd C) ≡ (snd C)
(C , c) ≃∙FF∎ = ΣΣ∙FibEqRfl

hLevelCong≃∙F : {A : Pointed ℓ} (n : ℕ)
  (B B' : Σ[ P ∈ ((typ A) → Type ℓ) ] P (pt A))
  → Σ[ e ∈ ((a : typ A) → (fst B) a ≃ (fst B') a) ]
      (fst (e (pt A))) (snd B) ≡ (snd B')
  → Σ[ e ∈ ((a : typ A) → hLevelTrunc n ((fst B) a)
                            ≃ hLevelTrunc n ((fst B') a)) ]
      (fst (e (pt A))) (trunc {X = ((fst B) (pt A) , snd B)} n (snd B))
      ≡ trunc {X = ((fst B') (pt A) , snd B')} n (snd B')
fst (hLevelCong≃∙F zero B B' (e , p)) a = idEquiv _
snd (hLevelCong≃∙F zero B B' (e , p)) = refl
fst (hLevelCong≃∙F (suc n) B B' (e , p)) a =
  isoToEquiv (mapCompIso (equivToIso (e a)))
snd (hLevelCong≃∙F (suc n) B B' (e , p)) = cong ∣_∣ₕ p

ua∙' : (A B : Pointed ℓ) → A ≃∙ B → A ≡ B
ua∙' A B = Equiv∙J (λ A' e' → A' ≡ B) refl

ua∙* : (A B : Pointed ℓ) → A ≃∙ B → A ≡ B
ua∙* A B e = ua∙ (fst e) (snd e)

au∙ : (A B : Pointed ℓ) → A ≡ B → A ≃∙ B
au∙ A B = J (λ A' p' → A ≃∙ A') ((idEquiv (typ A)) , refl)
