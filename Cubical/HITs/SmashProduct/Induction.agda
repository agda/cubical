{-

This file contains an induction principle for function defined over
iterated smash products. It concerns the map

⋀̃→⋀ : ⋀̃ Aᵢ → ⋀ᵢ Aᵢ

where ⋀̃ is defined as the pushout

Σi≤n (A₀ × ... × Aᵢ₋₁ × Aᵢ₊₁ × ... × Aₙ) ---→ (A₀ × ... × Aₙ)
               ↓                                ⌟  ↓
               1 ------------------------------→ ⋀̃ Aᵢ

Statement: Let f,g : ⋀ᵢ Aᵢ → B. If f ∘ ⋀̃→⋀ = g ∘ ⋀̃→⋀, then f = g.

-}

{-# OPTIONS --safe #-}


module Cubical.HITs.SmashProduct.Induction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Fin
open import Cubical.Data.Sum

open import Cubical.HITs.SmashProduct.Base
open import Cubical.HITs.Pushout

private
  variable
    ℓ ℓ' : Level

-- A `fat sum': Σi≤n (A₀ × ... × Aᵢ₋₁ × Aᵢ₊₁ × ... × Aₙ)
FS : (n : ℕ) → FinFamily (suc n) ℓ → Type ℓ
FS zero A = Unit*
FS (suc n) A =
     (FS n (predFinFamily A) × A flast)
   ⊎ prodFinFamily n (predFinFamily A)

FS→Prod : (n : ℕ) (A : FinFamily∙ (suc n) ℓ)
  → FS n (fst ∘ A) → prodFinFamily n (fst ∘ A)
FS→Prod zero A x = A fzero .snd
FS→Prod (suc n) A (inl x) =
  FS→Prod n (predFinFamily∙ A) (fst x) , snd x
FS→Prod (suc n) A (inr x) = x , A flast .snd

-- Definition of ⋀̃
⋀̃ : (n : ℕ) (A : FinFamily∙ (suc n) ℓ) → Type ℓ
⋀̃ n A = cofib (FS→Prod n A)

⋀̃∙ : (n : ℕ) (A : FinFamily∙ (suc n) ℓ)  → Pointed ℓ
⋀̃∙ n A = ⋀̃ n A , inl tt

-- (⋀̂[i≤n] Aᵢ) × Aₙ → ⋀̂[i≤n+1] Aᵢ
⋀̃↑ : (n : ℕ) (A : FinFamily∙ (suc (suc n)) ℓ) (y : A flast .fst)
  → ⋀̃ n (predFinFamily∙ A) → ⋀̃ (suc n) A
⋀̃↑ n A y (inl x) = inl x
⋀̃↑ n A y (inr x) = inr (x , y)
⋀̃↑ n A y (push a i) = push (inl (a , y)) i

-- For the obvious inclusion of cells ⋀̂ A → ⋀ A,
-- we need the following coherence
const≡prod→⋀^∘FS→Prod : (n : ℕ) (A : FinFamily∙ (suc n) ℓ)
  (a : FS n ((λ r → fst r) ∘ A))
  → ⋀^ n A .snd ≡ prod→⋀^ n A (FS→Prod n A a)
const≡prod→⋀^∘FS→Prod zero A a = refl
const≡prod→⋀^∘FS→Prod (suc n) A (inl x) =
    push (inr (snd x))
  ∙ λ i → inr (const≡prod→⋀^∘FS→Prod n
                (predFinFamily∙ A) (fst x) i , snd x)
const≡prod→⋀^∘FS→Prod (suc n) A (inr x) =
  push (inl (prod→⋀^ n (predFinFamily∙ A) x))

-- natural map ⋀̂ A → ⋀ A
⋀̃→⋀ : (n : ℕ) (A : FinFamily∙ (suc n) ℓ)
  → ⋀̃ n A → ⋀^ n A .fst
⋀̃→⋀ n A (inl x) = ⋀^ n A .snd
⋀̃→⋀ n A (inr x) = prod→⋀^ n A x
⋀̃→⋀ n A (push a i) = const≡prod→⋀^∘FS→Prod n A a i

-- pointed version
⋀̃→⋀∙ : (n : ℕ) (A : FinFamily∙ (suc n) ℓ)
  → ⋀̃∙ n A →∙ ⋀^ n A
fst (⋀̃→⋀∙ n A) = ⋀̃→⋀ n A
snd (⋀̃→⋀∙ n A) = refl

-- proof that it commutes with ⋀̃↑
⋀̃→⋀-⋀̃↑-comm : (n : ℕ)
  (A : FinFamily∙ (suc (suc n)) ℓ)
  (y : A flast .fst)
  (x : ⋀̃ n (predFinFamily∙ A))
  → ⋀̃→⋀ (suc n) A (⋀̃↑ n A y x)
   ≡ inr (⋀̃→⋀ n (predFinFamily∙ A) x , y)
⋀̃→⋀-⋀̃↑-comm n A a (inl x) = push (inr a)
⋀̃→⋀-⋀̃↑-comm n A a (inr x) = refl
⋀̃→⋀-⋀̃↑-comm n A a (push a₁ i) j =
  compPath-filler' (push (inr a))
    (λ i → inr (const≡prod→⋀^∘FS→Prod n (predFinFamily∙ A) a₁ i , a)) (~ j) i

-- Finally, the induction principle ⋀̃→⋀-ind...
⋀̃→⋀-ind : (n : ℕ) (A : FinFamily∙ (suc n) ℓ) {B : Type ℓ'}
  {f g : ⋀^ n A .fst → B}
  (ind : (x : ⋀̃ n A) → f (⋀̃→⋀ n A x) ≡ g (⋀̃→⋀ n A x))
 → f ≡ g
-- ...together with some computation rules (needed to strengthen the
-- inductive hypothesis in the proof), but should be useful in their
-- own right.
⋀̃→⋀-ind-coh : (n : ℕ) (A : FinFamily∙ (suc n) ℓ) {B : Type ℓ'}
  {f g : ⋀^ n A .fst → B}
  (ind : (x : ⋀̃ n A) → f (⋀̃→⋀ n A x) ≡ g (⋀̃→⋀ n A x))
  → (funExt⁻ (⋀̃→⋀-ind n A {f = f} {g = g} ind) (⋀^ n A .snd) ≡ ind (inl tt))
   × ((x : prodFinFamily∙ n A .fst)
     → funExt⁻ (⋀̃→⋀-ind n A {f = f} {g = g} ind) (⋀̃→⋀ n A (inr x))
      ≡ ind (inr x))
⋀̃→⋀-ind zero A ind = funExt (ind ∘ inr)
⋀̃→⋀-ind (suc n) A {B = B} {f = f} {g} ind =
  funExt (⋀-fun≡ f g (ind (inl tt))
    (λ x → h (snd x) (fst x))
    (λ x → transport (sym (PathP≡doubleCompPathʳ _ _ _ _))
      (funExt⁻ mainSquareAsCompPath-const x))
      λ x → (doubleCompPath-filler
            (sym (cong f (push (inr x))))
            (ind (inl tt))
            (cong g (push (inr x))))
        ▷ sym (h-coh x .fst))
  where
  f↓ g↓ : (y : typ (A flast)) → ⋀^ n (predFinFamily∙ A) .fst → B
  f↓ y = f ∘ inr ∘ (_, y)
  g↓ y = g ∘ inr ∘ (_, y)

  f↓≡g↓ : (y : typ (A flast)) (x : ⋀̃ n (predFinFamily∙ A))
     → f↓ y (⋀̃→⋀ n (predFinFamily∙ A) x)
      ≡ g↓ y (⋀̃→⋀ n (predFinFamily∙ A) x)
  f↓≡g↓ y x = cong f (sym (⋀̃→⋀-⋀̃↑-comm n A y x))
             ∙∙ ind (⋀̃↑ n A y x)
             ∙∙ cong g (⋀̃→⋀-⋀̃↑-comm n A y x)

  -- f and g agree on canonical points
  h : (y : typ (A flast)) (x : _) → f (inr (x , y)) ≡ g (inr (x , y))
  h y = funExt⁻ (⋀̃→⋀-ind n (predFinFamily∙ A) {f = f↓ y} {g↓ y} (f↓≡g↓ y))

  h-coh : (y : typ (A flast)) → _
  h-coh y = ⋀̃→⋀-ind-coh n (predFinFamily∙ A) {f = f↓ y} {g↓ y} (f↓≡g↓ y)

  -- coherence
  mainSquare : (x : prodFinFamily n (fst ∘ (predFinFamily∙ A)))
    → PathP (λ i → f (push (inl (prod→⋀^ n (predFinFamily∙ A) x)) i)
                   ≡ g (push (inl (prod→⋀^ n (predFinFamily∙ A) x)) i))
             (ind (inl tt))
             (h (A flast .snd) (prod→⋀^ n (predFinFamily∙ A) x))
  mainSquare x i j =
     hcomp (λ k →
      λ {(i = i0) → ind (push (inr x) (~ k)) j
       ; (i = i1) → ⋀̃→⋀-ind-coh n (predFinFamily∙ A)
                       {f = f↓ (A flast .snd)} {g↓ (A flast .snd)}
                       (f↓≡g↓ (A flast .snd)) .snd x (~ k) j
       ; (j = i0) → f (push (inl (prod→⋀^ n (predFinFamily∙ A) x)) (i ∨ ~ k))
       ; (j = i1) → g (push (inl (prod→⋀^ n (predFinFamily∙ A) x)) (i ∨ ~ k))})
        (rUnit (ind (inr (x , A flast .snd))) i j)

  mainSquareAsCompPath : ⋀^ n (predFinFamily∙ A) .fst → f (inl tt) ≡ g (inl tt)
  mainSquareAsCompPath x =
       cong f (push (inl x))
    ∙∙ h (snd (A flast)) x
    ∙∙ cong g (sym (push (inl x)))

  mainSquareAsCompPath-const : (λ _ → ind (inl tt)) ≡ mainSquareAsCompPath
  mainSquareAsCompPath-const = ⋀^→Homogeneous≡ n _ (isHomogeneousPath _ _)
    λ x → transport (PathP≡doubleCompPathʳ _ _ _ _) (mainSquare x)
fst (⋀̃→⋀-ind-coh zero A ind) = cong ind (sym (push tt*))
fst (⋀̃→⋀-ind-coh (suc n) A ind) = refl
snd (⋀̃→⋀-ind-coh zero A ind) x = refl
snd (⋀̃→⋀-ind-coh (suc n) A ind) x =
    ⋀̃→⋀-ind-coh n (predFinFamily∙ A) _ .snd (fst x)
  ∙ sym (rUnit _)

-- Pointed version
⋀̃→⋀-ind∙ : (n : ℕ) (A : FinFamily∙ (suc n) ℓ) {B : Pointed ℓ'}
  {f g : ⋀^ n A →∙ B}
 → f ∘∙ ⋀̃→⋀∙ n A ≡ (g ∘∙ ⋀̃→⋀∙ n A)
 → f ≡ g
-- ...together with some computation rules (needed to strengthen the
-- inductive hypothesis in the proof), but should be useful in their
-- own right.
fst (⋀̃→⋀-ind∙ n A {f = f} {g} ind i) =
  ⋀̃→⋀-ind n A {f = fst f} {g = fst g} (funExt⁻ (cong fst ind)) i
snd (⋀̃→⋀-ind∙ zero A ind i) j =
  ((λ j i → fst (ind i) (push tt* (~ j)))
  ◁ flipSquare (((lUnit _)
  ◁ cong snd ind
  ▷ (sym (lUnit _))))) j i
snd (⋀̃→⋀-ind∙ (suc n) A ind i) =
  ((lUnit _) ◁ cong snd ind ▷ (sym (lUnit _))) i
