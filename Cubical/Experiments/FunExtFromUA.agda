{- Voevodsky's proof that univalence implies funext -}

{-# OPTIONS --cubical --safe #-}

module Cubical.Experiments.FunExtFromUA where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything

variable
 ℓ ℓ' : Level
_∼_ : {X : Type ℓ} {A : X → Type ℓ'} → (f g : (x : X) → A x) → Type (ℓ-max ℓ ℓ')
f ∼ g = ∀ x → f x ≡ g x

funext : ∀ ℓ ℓ' → Type (ℓ-suc(ℓ-max ℓ ℓ'))
funext ℓ ℓ' = {X : Type ℓ} {Y : Type ℓ'} {f g : X → Y} → f ∼ g → f ≡ g


elimEquivFun' : ∀ {ℓ} (P : (A B : Type ℓ) → (A → B) → Type ℓ)
              → (r : (B : Type ℓ) → P B B (λ x → x))
              → (A B : Type ℓ) → (e : A ≃ B) → P A B (e .fst)
elimEquivFun' P r A B = elimEquivFun B (λ A → P A B) (r B) A

pre-comp-is-equiv : (X Y : Type ℓ) (f : X → Y) (Z : Type ℓ)
                  → isEquiv f
                  → isEquiv (λ (g : Y → Z) → g ∘ f)
pre-comp-is-equiv {ℓ} X Y f Z e = elimEquivFun' P r X Y (f , e)
 where
  P : (X Y : Type ℓ) → (X → Y) → Type ℓ
  P X Y f = isEquiv (λ (g : Y → Z) → g ∘ f)
  r : (B : Type ℓ) → P B B (λ x → x)
  r B = idIsEquiv (B → Z)

leftCancellable : {X : Type ℓ} {Y : Type ℓ'} → (X → Y) → Type (ℓ-max ℓ ℓ')
leftCancellable f = ∀ {x x'} → f x ≡ f x' → x ≡ x'

equivLC : {X : Type ℓ} {Y : Type ℓ'} (f : X → Y) → isEquiv f → leftCancellable f
equivLC f e {x} {x'} p i = hcomp (λ j → \ {(i = i0) → secEq (f , e) x j ;
                                           (i = i1) → secEq (f , e) x' j})
                                 (invEq (f , e) (p i))

univalence-gives-funext : funext ℓ' ℓ
univalence-gives-funext {ℓ'} {ℓ} {X} {Y} {f₀} {f₁} = γ
 where
  Δ = Σ[ y₀ ∈ Y ] Σ[ y₁ ∈ Y ] y₀ ≡ y₁

  δ : Y → Δ
  δ y = (y , y , refl)

  π₀ π₁ : Δ → Y
  π₀ (y₀ , y₁ , p) = y₀
  π₁ (y₀ , y₁ , p) = y₁

  δ-is-equiv : isEquiv δ
  δ-is-equiv = isoToIsEquiv (iso δ π₀ ε η)
   where
    η : (y : Y) → π₀ (δ y) ≡ y
    η y = refl
    ε : (d : Δ) → δ (π₀ d) ≡ d
    ε (y₀ , y₁ , p) i = y₀ , p i , λ j → p (i ∧ j)

  φ : (Δ → Y) → (Y → Y)
  φ π = π ∘ δ

  e : isEquiv φ
  e = pre-comp-is-equiv Y Δ δ Y δ-is-equiv

  p : φ π₀ ≡ φ π₁
  p = refl

  q : π₀ ≡ π₁
  q = equivLC φ e p

  g : (h : f₀ ∼ f₁) (π : Δ → Y) (x : X) → Y
  g = λ h π x → π (f₀ x , f₁ x , h x)

  γ : f₀ ∼ f₁ → f₀ ≡ f₁
  γ h = cong (g h) q

  γ' : f₀ ∼ f₁ → f₀ ≡ f₁
  γ' h = f₀                              ≡⟨ refl ⟩
         (λ x → f₀ x)                    ≡⟨ refl ⟩
         (λ x → π₀ (f₀ x , f₁ x , h x))  ≡⟨ cong (g h) q ⟩
         (λ x → π₁ (f₀ x , f₁ x , h x))  ≡⟨ refl ⟩
         (λ x → f₁ x)                    ≡⟨ refl ⟩
         f₁                              ∎

{- Experiment testing univalence via funext -}

private

  data ℕ : Type₀ where
   zero : ℕ
   succ : ℕ → ℕ

  f g : ℕ → ℕ

  f n = n

  g zero = zero
  g (succ n) = succ (g n)

  h : (n : ℕ) → f n ≡ g n
  h zero = refl
  h (succ n) = cong succ (h n)

  p : f ≡ g
  p = univalence-gives-funext h

  five : ℕ
  five = succ (succ (succ (succ (succ zero))))

  a : Σ ℕ (λ n → f n ≡ five)
  a = five , refl

  b : Σ ℕ (λ n → g n ≡ five)
  b = subst (λ - → Σ ℕ (λ n → - n ≡ five)) p a

  c : fst b ≡ five
  c = refl

{- It works, fast. -}
