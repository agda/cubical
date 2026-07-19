module Cubical.HITs.FreeAbGroup.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Fin.Inductive.Base
open import Cubical.Data.Fin.Inductive.Properties
open import Cubical.Data.Empty as ⊥

infixl 7 _·_
infix 20 _⁻¹

private variable
  ℓ ℓ' : Level
  A : Type ℓ

data FreeAbGroup (A : Type ℓ) : Type ℓ where
  ⟦_⟧       : A → FreeAbGroup A
  ε         : FreeAbGroup A
  _·_       : FreeAbGroup A → FreeAbGroup A → FreeAbGroup A
  _⁻¹       : FreeAbGroup A → FreeAbGroup A
  assoc     : ∀ x y z → x · (y · z) ≡ (x · y) · z
  comm      : ∀ x y   → x · y       ≡ y · x
  identityᵣ : ∀ x     → x · ε       ≡ x
  invᵣ      : ∀ x     → x · x ⁻¹    ≡ ε
  trunc     : isSet (FreeAbGroup A)

module Elim {B : FreeAbGroup A → Type ℓ'}
  (⟦_⟧*       : (x : A) → B ⟦ x ⟧)
  (ε*         : B ε)
  (_·*_       : ∀ {x y}   → B x → B y → B (x · y))
  (_⁻¹*       : ∀ {x}     → B x → B (x ⁻¹))
  (assoc*     : ∀ {x y z} → (xs : B x) (ys : B y) (zs : B z)
    → PathP (λ i → B (assoc x y z i)) (xs ·* (ys ·* zs)) ((xs ·* ys) ·* zs))
  (comm*      : ∀ {x y}   → (xs : B x) (ys : B y)
    → PathP (λ i → B (comm x y i)) (xs ·* ys) (ys ·* xs))
  (identityᵣ* : ∀ {x}     → (xs : B x)
    → PathP (λ i → B (identityᵣ x i)) (xs ·* ε*) xs)
  (invᵣ* : ∀ {x} → (xs : B x)
    → PathP (λ i → B (invᵣ x i)) (xs ·* (xs ⁻¹*)) ε*)
  (trunc*     : ∀ xs → isSet (B xs)) where

  f : (xs : FreeAbGroup A) → B xs
  f ⟦ x ⟧ = ⟦ x ⟧*
  f ε = ε*
  f (xs · ys) = f xs ·* f ys
  f (xs ⁻¹) = f xs ⁻¹*
  f (assoc xs ys zs i) = assoc* (f xs) (f ys) (f zs) i
  f (comm xs ys i) = comm* (f xs) (f ys) i
  f (identityᵣ xs i) = identityᵣ* (f xs) i
  f (invᵣ xs i) = invᵣ* (f xs) i
  f (trunc xs ys p q i j) = isOfHLevel→isOfHLevelDep 2 trunc*  (f xs) (f ys)
    (cong f p) (cong f q) (trunc xs ys p q) i j

module ElimProp {B : FreeAbGroup A → Type ℓ'}
  (BProp : {xs : FreeAbGroup A} → isProp (B xs))
  (⟦_⟧*       : (x : A) → B ⟦ x ⟧)
  (ε*         : B ε)
  (_·*_       : ∀ {x y}   → B x → B y → B (x · y))
  (_⁻¹*       : ∀ {x}     → B x → B (x ⁻¹)) where

  f : (xs : FreeAbGroup A) → B xs
  f = Elim.f ⟦_⟧* ε* _·*_ _⁻¹*
    (λ {x y z} xs ys zs → toPathP (BProp (transport (λ i → B (assoc x y z i)) (xs ·* (ys ·* zs))) ((xs ·* ys) ·* zs)))
    (λ {x y} xs ys → toPathP (BProp (transport (λ i → B (comm x y i)) (xs ·* ys)) (ys ·* xs)))
    (λ {x} xs → toPathP (BProp (transport (λ i → B (identityᵣ x i)) (xs ·* ε*)) xs))
    (λ {x} xs → toPathP (BProp (transport (λ i → B (invᵣ x i)) (xs ·* (xs ⁻¹*))) ε*))
    (λ _ → (isProp→isSet BProp))

module Rec {B : Type ℓ'} (BType : isSet B)
  (⟦_⟧*       : (x : A) → B)
  (ε*         : B)
  (_·*_       : B → B → B)
  (_⁻¹*       : B → B)
  (assoc*     : (x y z : B) → x ·* (y ·* z) ≡ (x ·* y) ·* z)
  (comm*      : (x y : B)   → x ·* y        ≡ y ·* x)
  (identityᵣ* : (x : B)     → x ·* ε*       ≡ x)
  (invᵣ*      : (x : B)     → x ·* (x ⁻¹*)  ≡ ε*)
  where

  f : FreeAbGroup A → B
  f = Elim.f ⟦_⟧* ε* _·*_ _⁻¹* assoc* comm* identityᵣ* invᵣ* (const BType)

isContr-Free⊥ : isContr (FreeAbGroup ⊥)
fst isContr-Free⊥ = ε
snd isContr-Free⊥ =
  ElimProp.f (trunc _ _)
    (λ {()})
    refl
    (λ p q → sym (identityᵣ ε) ∙ cong₂ _·_ p q)
    λ p → sym (invᵣ ε) ∙ comm _ _ ∙ identityᵣ (ε ⁻¹) ∙ cong _⁻¹ p

isContr-FreeFin0 : isContr (FreeAbGroup (Fin 0))
isContr-FreeFin0 = subst (isContr ∘ FreeAbGroup) (sym lem) isContr-Free⊥
  where
  lem : Fin 0 ≡ ⊥
  lem = isoToPath (iso ¬Fin0 (λ{()}) (λ{()}) λ p → ⊥.rec (¬Fin0 p))

Free↑ : (n : ℕ) → FreeAbGroup (Fin n) → FreeAbGroup (Fin (suc n))
Free↑ n ⟦ x ⟧ = ⟦ injectSuc x ⟧
Free↑ n ε = ε
Free↑ n (x · x₁) = Free↑ n x · Free↑ n x₁
Free↑ n (x ⁻¹) = (Free↑ n x) ⁻¹
Free↑ n (assoc x x₁ x₂ i) = assoc (Free↑ n x) (Free↑ n x₁) (Free↑ n x₂) i
Free↑ n (comm x x₁ i) = comm (Free↑ n x) (Free↑ n x₁) i
Free↑ n (identityᵣ x i) = identityᵣ (Free↑ n x) i
Free↑ n (invᵣ x i) = invᵣ (Free↑ n x) i
Free↑ n (trunc x x₁ x₂ y i i₁) =
  isSet→isSet' trunc
    (λ _ → Free↑ n x) (λ _ → Free↑ n x₁)
    (λ j → Free↑ n (x₂ j)) (λ j → Free↑ n (y j)) i₁ i

Free↑sumFinℤ : (n m : ℕ) (g : Fin m → FreeAbGroup (Fin n))
  → Free↑ n (sumFinGen {n = m} _·_ ε g) ≡ sumFinGen {n = m} _·_ ε (Free↑ n ∘ g)
Free↑sumFinℤ zero zero g = refl
Free↑sumFinℤ zero (suc m) g =
  cong (Free↑ zero (g flast) ·_) (Free↑sumFinℤ zero m (λ x → g (injectSuc x)))
Free↑sumFinℤ (suc n) zero g = refl
Free↑sumFinℤ (suc n) (suc m) g =
  cong (Free↑ (suc n) (g flast) ·_) (Free↑sumFinℤ (suc n) m (λ x → g (injectSuc x)))
