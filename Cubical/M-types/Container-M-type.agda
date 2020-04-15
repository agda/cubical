{-# OPTIONS --cubical --guardedness #-} --safe

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Function using (_∘_)

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )
open import Cubical.Data.Sum
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.Foundations.Transport

open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

open import Cubical.M-types.helper
open import Cubical.M-types.Container

module Cubical.M-types.Container-M-type where
open Iso

---------------------------
-- Properties of M-types --
---------------------------

Container-product : ∀ {ℓ} (_ _ : Container {ℓ}) -> Container {ℓ}
Container-product (A , B) (C , D) = (A × C , λ x → B (proj₁ x) × D (proj₂ x) )

P-product :
  ∀ {ℓ} {A C : Set ℓ} {B : A -> Set ℓ} {D : C -> Set ℓ}
  -> ((n : ℕ) -> W (A , B) n) × ((n : ℕ) -> W (C , D) n)
  ------------------------
  -> (n : ℕ) -> W (Container-product (A , B) (C , D)) n
P-product (x , y) 0 = lift tt
P-product (x , y) (suc n) = ((x (suc n) .fst) , (y (suc n) .fst)) , λ _ → P-product (x , y) n

-- P-product-inv₁ :
--   ∀ {ℓ} {A C : Set ℓ} {B : A -> Set ℓ} {D : C -> Set ℓ}
--   -> ((n : ℕ) -> W (Container-product (A , B) (C , D)) n)
--   ------------------------
--   -> (n : ℕ) -> W (A , B) n
-- P-product-inv₁ x 0 = lift tt
-- P-product-inv₁ {D = D} x (suc n) = (proj₁ (x (suc n) .fst)) , (λ _ → P-product-inv₁ {D = D} x n)

-- P-product-inv₂ :
--   ∀ {ℓ} {A C : Set ℓ} {B : A -> Set ℓ} {D : C -> Set ℓ}
--   -> ((n : ℕ) -> W (Container-product (A , B) (C , D)) n)
--   ------------------------
--   -> (n : ℕ) -> W (C , D) n
-- P-product-inv₂ x 0 = lift tt
-- P-product-inv₂ {B = B} x (suc n) = (proj₂ (x (suc n) .fst)) , (λ _ → P-product-inv₂ {B = B} x n)

-- P-product-inv :
--   ∀ {ℓ} {A C : Set ℓ} {B : A -> Set ℓ} {D : C -> Set ℓ}
--   -> ((n : ℕ) -> W (Container-product (A , B) (C , D)) n)
--   ------------------------
--   -> ((n : ℕ) -> W (A , B) n) × ((n : ℕ) -> W (C , D) n)
-- P-product-inv {B = B} {D = D} x = (P-product-inv₁ {D = D} x) , (P-product-inv₂ {B = B} x)

Σ-prod-fun-Iso :
  ∀ {ℓ} {A C : Set ℓ} {B : A -> Set ℓ} {D : C -> Set ℓ}
  → (n : ℕ)
  → (x : A × C)
  → Iso ((B (proj₁ x) → W (A , B) n) × (D (proj₂ x) → W (C , D) n))
         (B (proj₁ x) × D (proj₂ x) → W (A , B) n × W (C , D) n)
fun (Σ-prod-fun-Iso n x) (bf , df) (b , d) = bf b , df d
inv (Σ-prod-fun-Iso {A = A} {C} {B} {D} n x) = Σ-prod-fun₂
  where
    postulate
      Σ-prod-fun₂ : (B (proj₁ x) × D (proj₂ x) → W (A , B) n × W (C , D) n) → (B (proj₁ x) → W (A , B) n) × (D (proj₂ x) → W (C , D) n)
rightInv (Σ-prod-fun-Iso n x) = Σ-prod-iso₁
  where
    postulate
      Σ-prod-iso₁ : section (fun (Σ-prod-fun-Iso n x)) (inv (Σ-prod-fun-Iso n x))
leftInv (Σ-prod-fun-Iso n x) = Σ-prod-iso₂
  where
    postulate
      Σ-prod-iso₂ : retract (fun (Σ-prod-fun-Iso n x)) (inv (Σ-prod-fun-Iso n x))

Σ-prod-fun :
  ∀ {ℓ} {A C : Set ℓ} {B : A -> Set ℓ} {D : C -> Set ℓ}
  → (n : ℕ)
  → (x : A × C)
  → (B (proj₁ x) → W (A , B) n) × (D (proj₂ x) → W (C , D) n)
  ≡ (B (proj₁ x) × D (proj₂ x) → W (A , B) n × W (C , D) n)
Σ-prod-fun {B = B} {D} n x = isoToPath (Σ-prod-fun-Iso n x)
  -- isoToPath (iso (Σ-prod-fun₁ n (a , c))
  --                (Σ-prod-fun₂ n (a , c))
  --                (Σ-prod-iso₁ n (a , c))
  --                (Σ-prod-iso₂ n (a , c)))

P-equality-helper-Iso :
    ∀ {ℓ} {A C : Set ℓ} {B : A -> Set ℓ} {D : C -> Set ℓ}
    -> (n : ℕ)
    ------------------------
    → Iso (Σ A (λ a → B a → W (A , B) n) × Σ C (λ c → D c → W (C , D) n))
          (Σ (A × C) (λ x → (B (proj₁ x) → W (A , B) n) × (D (proj₂ x) → W (C , D) n)))
P-equality-helper-Iso n =
  (iso (λ x → ((proj₁ x) .fst , (proj₂ x) .fst) , ((proj₁ x) .snd , (proj₂ x) .snd))
                   (λ x → (proj₁ (x .fst) , proj₁ (x .snd)) , ((proj₂ (x .fst)) , (proj₂ (x .snd))))
                   (λ { ((a , c) , b , d) → refl })
                   (λ { ((a , c) , b , d) → refl }))

P-equality-helper :
    ∀ {ℓ} {A C : Set ℓ} {B : A -> Set ℓ} {D : C -> Set ℓ}
    -> (n : ℕ)
    ------------------------
    -> Σ A (λ a → B a → W (A , B) n) × Σ C (λ c → D c → W (C , D) n)
    ≡ Σ (A × C) (λ x → (B (proj₁ x) → W (A , B) n) × (D (proj₂ x) → W (C , D) n))
P-equality-helper n = isoToPath (P-equality-helper-Iso n)

P-equality-Iso :
    ∀ {ℓ} {A C : Set ℓ} {B : A -> Set ℓ} {D : C -> Set ℓ}
    → (n : ℕ)
    ------------------------
    → Iso (W (A , B) n × W (C , D) n)
          (W (Container-product (A , B) (C , D)) n)
fun (P-equality-Iso 0) =  (λ _ → lift tt)
inv (P-equality-Iso 0) = (λ _ → lift tt , lift tt)
rightInv (P-equality-Iso 0) = (λ b i → lift tt)
leftInv (P-equality-Iso 0) = (λ {(_ , _) i → (lift tt) , (lift tt)})
P-equality-Iso {A = A} {C} {B} {D} (suc n) = compIso (P-equality-helper-Iso {A = A} {C} {B} {D} n) (compIso (Σ-ap-iso₂ (Σ-prod-fun-Iso n)) (pathToIso (cong (λ y → Σ (A × C) λ x → B (proj₁ x) × D (proj₂ x) → y) (isoToPath (P-equality-Iso n)))))

P-equality :
    ∀ {ℓ} {A C : Set ℓ} {B : A -> Set ℓ} {D : C -> Set ℓ}
    -> (n : ℕ)
    ------------------------
    -> (W (A , B) n × W (C , D) n)
    ≡ (W (Container-product (A , B) (C , D)) n)
P-equality n = isoToPath (P-equality-Iso n)

  -- (W (A , B) (suc n) × W (C , D) (suc n))
  --   ≡⟨ P-equality-helper {A = A} {C} {B} {D} n □ Σ-ap-iso₂ (Σ-prod-fun n) ⟩
  -- Σ (A × C) (λ x → B (proj₁ x) × D (proj₂ x) → (W (A , B) n × W (C , D) n))
  --   ≡⟨ cong (λ y → Σ (A × C) λ x → B (proj₁ x) × D (proj₂ x) → y) (P-equality n) ⟩
  -- Σ (A × C) (λ x → B (proj₁ x) × D (proj₂ x) → W (Container-product (A , B) (C , D)) n)
  --   ≡⟨ Σ-ap-iso₂ (λ x → refl) ⟩
  -- W (Container-product (A , B) (C , D)) (suc n) ∎

-- pathSigma≡sigmaPath


-- P-equality {ℓ} {A = A} {C} {B} {D} (suc n) =
--   (W (A , B) (suc n) × W (C , D) (suc n))
--     ≡⟨ P-equality-helper {A = A} {C} {B} {D} n □ (Σ-ap-iso₂(λ { (a , c) → Σ-prod-fun {A = A} {C = C} {B = B} {D = D} n (a , c) □ cong (λ x → B a × D c → x) (P-equality {B = B} {D = D} n) })) ⟩
--   W (Container-product (A , B) (C , D)) (suc n) ∎


postulate
  π-equality :
    ∀ {ℓ} {A C : Set ℓ} {B : A -> Set ℓ} {D : C -> Set ℓ}
    -> (x : (n : ℕ) -> W (Container-product (A , B) (C , D)) n)
    -> (n : ℕ)
    ------------------------
    -> πₙ (Container-product (A , B) (C , D)) (x (suc n))
    ≡ x n

  π-equality-2₁ :
    ∀ {ℓ} {A C : Set ℓ} {B : A -> Set ℓ} {D : C -> Set ℓ}
    -> (x : (n : ℕ) -> W (A , B) n × W (C , D) n)
    -> (n : ℕ)
    -----------------------
    -> πₙ (A , B) (proj₁ (x (suc n)))
    ≡ proj₁(x n)

  π-equality-2₂ :
    ∀ {ℓ} {A C : Set ℓ} {B : A -> Set ℓ} {D : C -> Set ℓ}
    -> (x : (n : ℕ) -> W (A , B) n × W (C , D) n)
    -> (n : ℕ)
    -----------------------
    -> πₙ (C , D) (proj₂ (x (suc n)))
    ≡ proj₂(x n)

M-product : ∀ {ℓ} S T -> M-type {ℓ = ℓ} S × M-type T -> M-type (Container-product S T)
M-product S T (x , y) = (λ n → transport (P-equality n) (x .fst n , y .fst n)) , π-equality {B = S .snd} {D = T .snd} (λ n -> transport (P-equality n) (x .fst n , y .fst n))

M-product-inv : ∀ {ℓ} S T -> M-type (Container-product S T) -> M-type {ℓ = ℓ} S × M-type T
M-product-inv S T (x , y) = ((λ n → proj₁ (transport (sym (P-equality {B = S .snd} {D = T .snd} n)) (x n))) ,
                                π-equality-2₁ {B = S .snd} {D = T .snd} (λ n → transport (λ i → P-equality {B = S .snd} {D = T .snd} n (~ i)) (x n))) ,
                             (λ n → proj₂ (transport (sym (P-equality {B = S .snd} {D = T .snd} n)) (x n))) ,
                                π-equality-2₂ {B = S .snd} {D = T .snd} (λ n → transport (λ i → P-equality {B = S .snd} {D = T .snd} n (~ i)) (x n))

postulate
  M-product-iso₁ : ∀ {ℓ} (S T : Container {ℓ}) b -> M-product S T (M-product-inv S T b) ≡ b
  M-product-iso₂ : ∀ {ℓ} (S T : Container {ℓ}) a -> M-product-inv S T (M-product S T a) ≡ a

M-product-equality : ∀ {ℓ} S T -> M-type {ℓ = ℓ} S × M-type T ≡ M-type (Container-product S T)
M-product-equality S T = isoToPath (iso (M-product S T) (M-product-inv S T) (M-product-iso₁ S T) (M-product-iso₂ S T))

---------------------------
-- Function into M-types --
---------------------------
