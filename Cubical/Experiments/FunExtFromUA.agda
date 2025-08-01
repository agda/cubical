{- Voevodsky's proof that univalence implies funext -}


module Cubical.Experiments.FunExtFromUA where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

variable
 ℓ ℓ' : Level
_∼_ : {X : Type ℓ} {A : X → Type ℓ'} → (f g : (x : X) → A x) → Type (ℓ-max ℓ ℓ')
f ∼ g = ∀ x → f x ≡ g x

funext : ∀ ℓ ℓ' → Type (ℓ-suc(ℓ-max ℓ ℓ'))
funext ℓ ℓ' = {X : Type ℓ} {Y : Type ℓ'} {f g : X → Y} → f ∼ g → f ≡ g


pre-comp-is-equiv : (X Y : Type ℓ) (f : X → Y) (Z : Type ℓ)
                  → isEquiv f
                  → isEquiv (λ (g : Y → Z) → g ∘ f)
pre-comp-is-equiv {ℓ} X Y f Z e = elimEquivFun P r (f , e)
 where
  P : (X : Type ℓ) → (X → Y) → Type ℓ
  P X f = isEquiv (λ (g : Y → Z) → g ∘ f)
  r : P Y (λ x → x)
  r = idIsEquiv (Y → Z)

leftCancellable : {X : Type ℓ} {Y : Type ℓ'} → (X → Y) → Type (ℓ-max ℓ ℓ')
leftCancellable f = ∀ {x x'} → f x ≡ f x' → x ≡ x'

equivLC : {X : Type ℓ} {Y : Type ℓ'} (f : X → Y) → isEquiv f → leftCancellable f
equivLC f e {x} {x'} p i = hcomp (λ j → \ {(i = i0) → retEq (f , e) x j ;
                                           (i = i1) → retEq (f , e) x' j})
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
