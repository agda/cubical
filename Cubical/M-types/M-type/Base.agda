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

open Iso

L-unique-iso : ∀ {ℓ} -> {S : Container {ℓ}} -> Iso (L (shift-chain (sequence S))) (L (sequence S))
fst (fun L-unique-iso (a , b)) 0 = lift tt
fst (fun L-unique-iso (a , b)) (suc n) = a n
snd (fun L-unique-iso (a , b)) 0 = refl {x = lift tt}
snd (fun L-unique-iso (a , b)) (suc n) = b n
fst (inv L-unique-iso x) = x .fst ∘ suc
snd (inv L-unique-iso x) = x .snd ∘ suc
fst (rightInv L-unique-iso (b , c) i) 0 = lift tt
fst (rightInv L-unique-iso (b , c) i) (suc n) = refl i
snd (rightInv L-unique-iso (b , c) i) 0 = refl
snd (rightInv L-unique-iso (b , c) i) (suc n) = c (suc n)
leftInv L-unique-iso = (λ a → ΣPathP (refl , refl))

-- Lemma 12
L-unique : ∀ {ℓ} -> {S : Container {ℓ}} -> L (shift-chain (sequence S)) ≡ L (sequence S)
L-unique {ℓ} {S = S} = isoToPath (L-unique-iso)

PX,Pπ : ∀ {ℓ} (S : Container {ℓ}) -> Chain
PX,Pπ {ℓ} S =
  (λ n → P₀ {S = S} (X (sequence S) n)) ,,
  (λ {n : ℕ} x → P₁ (λ z → z) (π (sequence S) {n = suc n} x ))

--------------
-- Lemma 10 --
--------------

projection : ∀ {ℓ} {S : Container {ℓ}} n -> M-type S -> X (sequence S) n
projection n (x , q) = x n

β : ∀ {ℓ} {S : Container {ℓ}} -> (n : ℕ) → ∀ x → π (sequence S) {n = n} (projection (suc n) x) ≡ projection n x
β n (x , q) = q n

lemma10 : ∀ {ℓ} {S : Container {ℓ}} (C,γ : Coalg₀ {S = S}) -> (C,γ .fst -> M-type S) ≡ Cone C,γ
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
              × (∀ n → π (sequence S) (x (suc n)) ≡ x n) ) )  → M-type S ≡ X (sequence S) 0
lemma11-helper {ℓ} {S = S} χ =
  M-type S
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
  lemma11 : ∀ {ℓ} {S : Container {ℓ}} -> M-type S ≡ X (sequence S) 0

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
  sym-α-iso-step-5-Iso : ∀ {ℓ} {S : Container {ℓ}}
    -> let (A , B) = S in
    Iso
      (Σ A (λ a → Σ ((n : ℕ) → B a → X (sequence S) n) λ u → (n : ℕ) → π (sequence S) ∘ (u (suc n)) ≡ u n))
      (Σ (Σ ((n : ℕ) → A) (λ a → (n : ℕ) → a (suc n) ≡ a n)) λ a →
        Σ ((n : ℕ) → B (a .fst n) → X (sequence S) n) λ u →
          (n : ℕ) → PathP (λ x → B (a .snd n x) → X (sequence S) n) (π (sequence S) ∘ u (suc n)) (u n))

α-iso-step-5 : ∀ {ℓ} {S : Container {ℓ}}
  -> let (A , B) = S in
  (Σ (Σ ((n : ℕ) → A) (λ a → (n : ℕ) → a (suc n) ≡ a n)) λ a →
     Σ ((n : ℕ) → B (a .fst n) → X (sequence S) n) λ u →
       (n : ℕ) → PathP (λ x → B (a .snd n x) → X (sequence S) n) (π (sequence S) ∘ u (suc n)) (u n))
  ≡ Σ A (λ a → Σ ((n : ℕ) → B a → X (sequence S) n) λ u → (n : ℕ) → π (sequence S) ∘ (u (suc n)) ≡ u n)
α-iso-step-5 = isoToPath (iso (inv sym-α-iso-step-5-Iso) (fun sym-α-iso-step-5-Iso) (leftInv sym-α-iso-step-5-Iso) (rightInv sym-α-iso-step-5-Iso))


sym-α-iso-step-6 : ∀ {ℓ} {S : Container {ℓ}}
    -> let (A , B) = S in
    Iso
      (Σ A (λ a → B a → M-type S))
      (Σ A (λ a → Σ ((n : ℕ) → B a → X (sequence S) n) λ u → (n : ℕ) → π (sequence S) ∘ (u (suc n)) ≡ u n))
fst (fun (sym-α-iso-step-6 {S = S@(A , B)}) (x , y')) = x
snd (fun (sym-α-iso-step-6 {S = S@(A , B)}) (x , y')) = transport (sym ((λ (a : A) → sym (lemma10 (B a , (λ x → a , (λ x₁ → x₁))))) x)) y'

fst (inv (sym-α-iso-step-6 {S = S@(A , B)}) (x , y)) = x
snd (inv (sym-α-iso-step-6 {S = S@(A , B)}) (x , y)) = transport ((λ (a : A) → sym (lemma10 (B a , (λ x → a , (λ x₁ → x₁))))) x) y

rightInv (sym-α-iso-step-6 {S = S@(A , B)}) (x , y') = ΣPathP (refl {x = x} , transport⁻Transport ((λ (a : A) → sym (lemma10 (B a , (λ x → a , (λ x₁ → x₁))))) x) y')

leftInv (sym-α-iso-step-6 {S = S@(A , B)}) (x , y) = ΣPathP (refl {x = x} , transportTransport⁻ ((λ (a : A) → sym (lemma10 (B a , (λ x → a , (λ x₁ → x₁))))) x) y)

α-iso-step-6 : ∀ {ℓ} {S : Container {ℓ}}
    -> let (A , B) = S in
    Σ A (λ a → Σ ((n : ℕ) → B a → X (sequence S) n) λ u → (n : ℕ) → π (sequence S) ∘ (u (suc n)) ≡ u n)
    ≡ Σ A (λ a → B a → M-type S)
α-iso-step-6 {S = S@(A , B)} = Σ-ap-iso₂ (λ a i → lemma10 (B a , (λ x → a , (λ x₁ → x₁))) (~ i))

-- Lemma 13
α-iso : ∀ {ℓ} {S : Container {ℓ}} -> L (PX,Pπ S) ≡ P₀ {S = S} (M-type S) -- L^P ≡ PL
α-iso {S = S@(A , B)} =
  α-iso-step-1-4 □ (α-iso-step-5 □ α-iso-step-6)

-----------------------------------------------------
-- Shifting the limit of a chain is an equivalence --
-----------------------------------------------------

comp-α-iso-step-1-4-Iso-Sym-L-unique-iso : ∀ {ℓ} {S : Container {ℓ}} -> let (A , B) = S in Iso (Σ (Σ ((n : ℕ) → A) (λ a → (n : ℕ) → a (suc n) ≡ a n)) λ a → Σ ((n : ℕ) → B (a .fst n) → X (sequence S) n) λ u → (n : ℕ) → PathP (λ x → B (a .snd n x) → X (sequence S) n) (π (sequence S) ∘ u (suc n)) (u n))  (L (sequence S))
fst (fun comp-α-iso-step-1-4-Iso-Sym-L-unique-iso (a , b)) 0 = lift tt
fst (fun comp-α-iso-step-1-4-Iso-Sym-L-unique-iso (a , b)) (suc n) = (a .fst n) , (b .fst n)
snd (fun comp-α-iso-step-1-4-Iso-Sym-L-unique-iso (a , b)) 0 = refl {x = lift tt}
snd (fun comp-α-iso-step-1-4-Iso-Sym-L-unique-iso (a , b)) (suc n) i = a .snd n i , b .snd n i
fst (fst (inv comp-α-iso-step-1-4-Iso-Sym-L-unique-iso x)) n = (x .fst) (suc n) .fst
snd (fst (inv comp-α-iso-step-1-4-Iso-Sym-L-unique-iso x)) n i = (x .snd) (suc n) i .fst
fst (snd (inv comp-α-iso-step-1-4-Iso-Sym-L-unique-iso x)) n = (x .fst) (suc n) .snd
snd (snd (inv comp-α-iso-step-1-4-Iso-Sym-L-unique-iso x)) n i = (x .snd) (suc n) i .snd
fst (rightInv comp-α-iso-step-1-4-Iso-Sym-L-unique-iso (b , c) i) 0 = lift tt
fst (rightInv comp-α-iso-step-1-4-Iso-Sym-L-unique-iso (b , c) i) (suc n) = refl i
snd (rightInv comp-α-iso-step-1-4-Iso-Sym-L-unique-iso (b , c) i) 0 = refl
snd (rightInv comp-α-iso-step-1-4-Iso-Sym-L-unique-iso (b , c) i) (suc n) = c (suc n)
leftInv comp-α-iso-step-1-4-Iso-Sym-L-unique-iso a = ΣPathP (refl , refl)

shift : ∀ {ℓ} {S : Container {ℓ}} -> P₀ {S = S} (M-type S) ≡ M-type S
shift {S = S@(A , B)} = isoToPath (compIso (sym-α-iso-step-6) (compIso (sym-α-iso-step-5-Iso {S = S}) (comp-α-iso-step-1-4-Iso-Sym-L-unique-iso {S = S}))) -- lemma 13 & lemma 12

-- Transporting along shift

in-fun : ∀ {ℓ} {S : Container {ℓ}} -> P₀ (M-type S) -> M-type S
in-fun {S = S} = transport (shift {S = S})

out-fun : ∀ {ℓ} {S : Container {ℓ}} -> M-type S -> P₀ (M-type S)
out-fun {S = S} = transport (sym (shift {S = S}))

----------------------------------------
-- Property of functions into M-types --
----------------------------------------

lift-to-M : ∀ {ℓ} {A : Set ℓ} {S : Container {ℓ}}
  → (x : (n : ℕ) -> A → X (sequence S) n)
  → ((n : ℕ) → (a : A) →  π (sequence S) (x (suc n) a) ≡ x n a)
  ---------------
  → (A → M-type S)
lift-to-M x p a = (λ n → x n a) , λ n i → p n a i

lift-direct-M : ∀ {ℓ} {S : Container {ℓ}}
  → (x : (n : ℕ) → X (sequence S) n)
  → ((n : ℕ) →  π (sequence S) (x (suc n)) ≡ x n)
  ---------------
  → M-type S
lift-direct-M x p = x , p
