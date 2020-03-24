{-# OPTIONS --cubical --guardedness #-} --safe

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Function using (_∘_)

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )
open import Cubical.Data.Sigma

open import Cubical.Foundations.Transport

open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

open import Cubical.Data.Sum

open import Cubical.M-types.helper
open import Cubical.M-types.Container

open import Cubical.M-types.Coalg.Base

module Cubical.M-types.M-type.Base where
--------------------------------
-- Limit of a Chain is Unique --
--------------------------------

-- Lemma 12
L-unique : ∀ {ℓ} -> {S : Container {ℓ}} -> L (shift-chain (sequence S)) ≡ L (sequence S)
L-unique {ℓ} {S = S} =
  isoToPath (
    iso (λ x → (λ {0 → lift tt ; (suc n) -> x .fst n}) , (λ { 0 → refl {x = lift tt} ; (suc n) → x .snd n }))
        (λ x → x .fst ∘ suc , x .snd ∘ suc)
        (λ {(b , c) → ΣPathP (funExt (λ { 0 → refl ; (suc n) → refl }) , λ {i 0 → refl ; i (suc n) → c (suc n)})})
        (λ a → ΣPathP (refl , refl)))

PX,Pπ : ∀ {ℓ} (S : Container {ℓ}) -> Chain
PX,Pπ {ℓ} S =
  (λ n → P₀ {S = S} (X (sequence S) n)) ,,
  (λ {n : ℕ} x → P₁ (λ z → z) (π (sequence S) {n = suc n} x ))

--------------
-- Lemma 10 --
--------------

projection : ∀ {ℓ} {S : Container {ℓ}} n -> M S -> X (sequence S) n
projection n (x , q) = x n

β : ∀ {ℓ} {S : Container {ℓ}} -> (n : ℕ) → ∀ x → π (sequence S) {n = n} (projection (suc n) x) ≡ projection n x
β n (x , q) = q n

lemma10 : ∀ {ℓ} {S : Container {ℓ}} (C,γ : Coalg₀ {S = S}) -> (C,γ .fst -> M S) ≡ Cone C,γ
lemma10 {S = S} C,γ@(C , γ) =
  isoToPath (iso (λ {f → (λ n z → projection n (f z)) , λ n i a → β n (f a) i})
                 (λ {(u , q) z → (λ n → u n z) , (λ n i → q n i z)})
                 (λ _ → refl)
                  λ _ → refl)

------------------------------------
-- Shifting M-type is an equality --
------------------------------------

swap-Σ-∀ :
  ∀ {ℓ} (X : ℕ -> Set ℓ)
    -> (A : Set ℓ)
    -> (B : A -> Set ℓ)
    -> (p : {n : ℕ} -> Σ A (λ a -> B a -> X (suc n)) -> Σ A (λ a -> B a -> X n) -> Set ℓ)
    -----------------------
    -> (Σ (∀ (n : ℕ) -> Σ A (λ a -> B a -> X n)) (λ w -> (n : ℕ) -> p (w (suc n)) (w n)))
    ≡ (Σ ((n : ℕ) → A) λ a → Σ ((n : ℕ) → B (a n) → X n) λ u → (n : ℕ) -> p (a (suc n) , u (suc n)) (a n , u n))
swap-Σ-∀ X A B p = isoToPath (iso (λ {(x , y) → (λ n → x n .fst) , (λ n → x n .snd) , y})
                                   (λ {(x , (y , z)) → (λ n → (x n) , y n) , z})
                                   (λ b → refl)
                                   (λ a → refl))

contr-⊤-iso : ∀ {i}{X : Set i} → isContr X → X ≡ Lift Unit
contr-⊤-iso hX = isoToPath (iso (λ _ → lift tt)
                                (λ _ → fst hX)
                                (λ {(lift tt) → refl})
                                λ a → snd hX a)

lemma11-helper : ∀ {ℓ} {S : Container {ℓ}} -> (χ : (x₀ : X (sequence S) 0)
              → isContr ( Σ ((n : ℕ) → X (sequence S) n) λ x
              → (x₀ ≡ x 0)
              × (∀ n → π (sequence S) (x (suc n)) ≡ x n) ) )  → M S ≡ X (sequence S) 0
lemma11-helper {ℓ} {S = S} χ =
  M S
    ≡⟨ sym (Σ-ap-iso₂ λ x → ∏-ap-iso refl λ n → refl) ⟩ -- sym not needed
  Σ ((n : ℕ) → X (sequence S) n) (λ x → (n : ℕ) → π (sequence S) (x (suc n)) ≡ x n)
    ≡⟨ sym (Σ-ap-iso₂ λ x → isoToPath (iso (λ x₁ → x₁ .snd) (λ x₁ → lift tt , x₁) (λ b → refl) λ a → refl)) ⟩
  Σ ((n : ℕ) → X (sequence S) n) (λ x → Σ (Lift Unit) λ _ → (n : ℕ) → π (sequence S) (x (suc n)) ≡ x n)
    ≡⟨ Σ-ap-iso₂ (λ x →
       Σ-ap-iso (isoToPath (iso (λ x₁ → (lift tt) , (λ i → lift tt)) (λ x₁ → lift tt) (λ {(a , b) → λ _ → (lift tt) , (λ _ → lift tt)}) λ a → refl)) λ _ → refl) ⟩
  Σ ((n : ℕ) → X (sequence S) n) (λ x →
  Σ (singl (x 0)) λ _ → (n : ℕ) → π (sequence S) (x (suc n)) ≡ x n)
    ≡⟨ isoToPath (iso (λ {(x , (z , p) , q) → z , x , p , q})
                      (λ {(lift tt , x , p , q) → x , ((lift tt) , p) , q})
                      (λ {(lift tt , x , p , q) → refl})
                      (λ {(x , (lift tt , p) , q) → refl})) ⟩
  Σ (X (sequence S) 0) (λ z →
  Σ ((n : ℕ) → X (sequence S) n) λ x →
  Σ (z ≡ x 0) λ _ →
    (n : ℕ) → π (sequence S) (x (suc n)) ≡ x n)
    ≡⟨ (Σ-ap-iso₂ λ z → let temp = χ z in contr-⊤-iso ((temp .fst .fst , proj₁ (temp .fst .snd) , proj₂ (temp .fst .snd)) , λ y → λ i → let temp' = temp .snd ((y .fst) , (y .snd .fst) , (y .snd .snd)) in (temp' i .fst) , proj₁ (temp' i .snd) , proj₂ (temp' i .snd))) ⟩
  (Σ (X (sequence S) 0) λ z → Lift Unit)
    ≡⟨ isoToPath (iso (λ _ → lift tt) (λ _ → lift tt , lift tt) (λ b → refl) λ a → refl) ⟩
  X (sequence S) 0 ∎

postulate
  lemma11 : ∀ {ℓ} {S : Container {ℓ}} -> M S ≡ X (sequence S) 0

α-iso-step-1-4 : ∀ {ℓ} {S : Container {ℓ}}
    -> let (A , B) = S in
    L (PX,Pπ S)
    ≡ (Σ (Σ ((n : ℕ) → A) (λ a → (n : ℕ) → a (suc n) ≡ a n)) λ a → Σ ((n : ℕ) → B (a .fst n) → X (sequence S) n) λ u → (n : ℕ) → PathP (λ x → B (a .snd n x) → X (sequence S) n) (π (sequence S) ∘ u (suc n)) (u n))
α-iso-step-1-4 {S = S@(A , B)} =
  isoToPath (iso
    (λ a →
      ((λ n → a .fst n .fst) , (λ n i → a .snd n i .fst)) ,
      ((λ n → a .fst n .snd) , (λ n x₁ → a .snd n x₁ .snd)))
    (λ a →
      (λ n → (a .fst .fst n) , (a .snd .fst n)) ,
      (λ n i → a .fst .snd n i , a .snd .snd n i))
    (λ b → refl)
    (λ a → refl))

postulate
  α-iso-step-5 : ∀ {ℓ} {S : Container {ℓ}}
    -> let (A , B) = S in
    (Σ (Σ ((n : ℕ) → A) (λ a → (n : ℕ) → a (suc n) ≡ a n)) λ a →
      Σ ((n : ℕ) → B (a .fst n) → X (sequence S) n) λ u →
        (n : ℕ) → PathP (λ x → B (a .snd n x) → X (sequence S) n) (π (sequence S) ∘ u (suc n)) (u n))
    ≡ Σ A (λ a → Σ ((n : ℕ) → B a → X (sequence S) n) λ u → (n : ℕ) → π (sequence S) ∘ (u (suc n)) ≡ u n)
  
α-iso-step-6 : ∀ {ℓ} {S : Container {ℓ}}
    -> let (A , B) = S in
    Σ A (λ a → Σ ((n : ℕ) → B a → X (sequence S) n) λ u → (n : ℕ) → π (sequence S) ∘ (u (suc n)) ≡ u n)
    ≡ Σ A (λ a → B a → M S)
α-iso-step-6 {S = S@(A , B)} = Σ-ap-iso₂ (λ a i → lemma10 (B a , (λ x → a , (λ x₁ → x₁))) (~ i))

-- TODO: Slow computations..
postulate
  α-iso' : ∀ {ℓ} {S : Container {ℓ}} -> L (PX,Pπ S) ≡ P₀ {S = S} (M S) -- L^P ≡ PL

-- Lemma 13
α-iso : ∀ {ℓ} {S : Container {ℓ}} -> L (PX,Pπ S) ≡ P₀ {S = S} (M S) -- L^P ≡ PL
α-iso {S = S@(A , B)} =
  α-iso-step-1-4 □ (α-iso-step-5 □ α-iso-step-6)

-----------------------------------------------------
-- Shifting the limit of a chain is an equivalence --
-----------------------------------------------------

abstract
  shift : ∀ {ℓ} {S : Container {ℓ}} -> P₀ {S = S} (M S) ≡ M S
  shift {S = S@(A , B)} = (sym α-iso) □ (L-unique {S = S}) -- lemma 13 & lemma 12

-- Transporting along shift

in-fun : ∀ {ℓ} {S : Container {ℓ}} -> P₀ (M S) -> M S
in-fun {S = S} = transport (shift {S = S})

out-fun : ∀ {ℓ} {S : Container {ℓ}} -> M S -> P₀ (M S)
out-fun {S = S} = transport (sym (shift {S = S}))

----------------------------------------
-- Property of functions into M-types --
----------------------------------------

lift-to-M : ∀ {ℓ} {A : Set ℓ} {S : Container {ℓ}}
  → (x : (n : ℕ) -> A → X (sequence S) n)
  → ((n : ℕ) → (a : A) →  π (sequence S) (x (suc n) a) ≡ x n a)
  ---------------
  → (A → M S)
lift-to-M x p a = (λ n → x n a) , λ n i → p n a i

lift-direct-M : ∀ {ℓ} {S : Container {ℓ}}
  → (x : (n : ℕ) → X (sequence S) n)
  → ((n : ℕ) →  π (sequence S) (x (suc n)) ≡ x n)
  ---------------
  → M S
lift-direct-M x p = x , p
