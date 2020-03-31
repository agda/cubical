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
open import Cubical.Foundations.Path

open import Cubical.Data.Sum

open import Cubical.M-types.helper
open import Cubical.M-types.Container

open import Cubical.M-types.Coalg.Base

module Cubical.M-types.M-type.Base where
--------------------------------
-- Limit of a Chain is Unique --
--------------------------------

open Iso

-- Lemma 12
L-unique-iso : ∀ {ℓ} -> {S : Container {ℓ}} -> Iso (L (shift-chain (sequence S))) (L (sequence S))
fun L-unique-iso (a , b) = (λ {0 → lift tt ; (suc n) → a n }) , λ { 0 → refl {x = lift tt} ; (suc n) → b n }
inv L-unique-iso x = x .fst ∘ suc , x .snd ∘ suc
fst (rightInv L-unique-iso (a , b) i) 0 = lift tt
fst (rightInv L-unique-iso (a , b) i) (suc n) = a (suc n)
snd (rightInv L-unique-iso (a , b) i) 0 = refl
snd (rightInv L-unique-iso (a , b) i) (suc n) = b (suc n)
leftInv L-unique-iso x = ΣPathP (refl , refl)

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

lemma10-Iso : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} -> Iso (C,γ .fst -> M-type S) (Cone C,γ)
fun (lemma10-Iso) f = (λ n z → projection n (f z)) , λ n i a → β n (f a) i
inv (lemma10-Iso) (u , q) z = (λ n → u n z) , λ n i → q n i z
rightInv (lemma10-Iso) = refl-fun
leftInv (lemma10-Iso) = refl-fun

lemma10 : ∀ {ℓ} {S : Container {ℓ}} (C,γ : Coalg₀ {S = S}) -> (C,γ .fst -> M-type S) ≡ Cone C,γ
lemma10 {S = S} C,γ@(C , γ) = isoToPath (lemma10-Iso {C,γ = C,γ})

------------------------------------
-- Shifting M-type is an equality --
------------------------------------

swap-Σ-∀-Iso :
  ∀ {ℓ} (X : ℕ -> Set ℓ)
    -> (A : Set ℓ)
    -> (B : A -> Set ℓ)
    -> (p : {n : ℕ} -> Σ A (λ a -> B a -> X (suc n)) -> Σ A (λ a -> B a -> X n) -> Set ℓ)
    -----------------------
    -> Iso (Σ (∀ (n : ℕ) -> Σ A (λ a -> B a -> X n)) (λ w -> (n : ℕ) -> p (w (suc n)) (w n)))
           (Σ ((n : ℕ) → A) λ a → Σ ((n : ℕ) → B (a n) → X n) λ u → (n : ℕ) -> p (a (suc n) , u (suc n)) (a n , u n))
fun (swap-Σ-∀-Iso X A B p) = (λ {(x , y) → (λ n → x n .fst) , (λ n → x n .snd) , y})
inv (swap-Σ-∀-Iso X A B p) = (λ {(x , (y , z)) → (λ n → (x n) , y n) , z})
rightInv (swap-Σ-∀-Iso X A B p) = refl-fun
leftInv (swap-Σ-∀-Iso X A B p) = refl-fun

swap-Σ-∀ :
  ∀ {ℓ} (X : ℕ -> Set ℓ)
    -> (A : Set ℓ)
    -> (B : A -> Set ℓ)
    -> (p : {n : ℕ} -> Σ A (λ a -> B a -> X (suc n)) -> Σ A (λ a -> B a -> X n) -> Set ℓ)
    -----------------------
    -> (Σ (∀ (n : ℕ) -> Σ A (λ a -> B a -> X n)) (λ w -> (n : ℕ) -> p (w (suc n)) (w n)))
    ≡ (Σ ((n : ℕ) → A) λ a → Σ ((n : ℕ) → B (a n) → X n) λ u → (n : ℕ) -> p (a (suc n) , u (suc n)) (a n , u n))
swap-Σ-∀ X A B p = isoToPath (swap-Σ-∀-Iso X A B p)

contr-⊤-iso-Iso : ∀ {i} {X : Set i} → (isContr X) → Iso X (Lift {ℓ-zero} {i} Unit)
fun (contr-⊤-iso-Iso hX) = (λ _ → lift tt)
inv (contr-⊤-iso-Iso hX) = (λ _ → fst hX)
rightInv (contr-⊤-iso-Iso hX) = (λ {(lift tt) → refl})
leftInv (contr-⊤-iso-Iso hX) = λ a → snd hX a

contr-⊤-iso : ∀ {i}{X : Set i} → isContr X → X ≡ Lift Unit
contr-⊤-iso = isoToPath ∘ contr-⊤-iso-Iso

limit-collapse : ∀ {ℓ} {S : Container {ℓ}} (X : ℕ → Set ℓ) (l : (n : ℕ) → X n → X (suc n)) → (x₀ : X 0) → ∀ (n : ℕ) → X n
limit-collapse X l x₀ 0 = x₀
limit-collapse {S = S} X l x₀ (suc n) = l n (limit-collapse {S = S} X l x₀ n)

lemma11-Iso :
  ∀ {ℓ} {S : Container {ℓ}} (X : ℕ → Set ℓ) (l : (n : ℕ) → X n → X (suc n))
  → Iso (Σ ((n : ℕ) → X n) (λ x → (n : ℕ) → x (suc n) ≡ l n (x n)))
         (X 0)
fun (lemma11-Iso X l) (x , y) = x 0
inv (lemma11-Iso {S = S} X l) x₀ = limit-collapse {S = S} X l x₀ , (λ n → refl {x = limit-collapse {S = S} X l x₀ (suc n)})
rightInv (lemma11-Iso X l) = refl-fun
leftInv (lemma11-Iso {S = S} X l) (x , y) i =
  let temp = χ-prop (x 0) (fst (inv (lemma11-Iso {S = S} X l) (fun (lemma11-Iso {S = S} X l) (x , y))) , refl , (λ n → refl {x = limit-collapse {S = S} X l (x 0) (suc n)})) (x , refl , y)
  in temp i .fst , proj₂ (temp i .snd)
  where
    leftInv1 :
      ∀ (x₀ : X 0)
      → (y : Σ ((n : ℕ) → X n) (λ x₁ → (x₀ ≡ x₁ 0) × ((n : ℕ) → x₁ (suc n) ≡ l n (x₁ n))))
      → (n : ℕ)
      → limit-collapse {S = S} X l x₀ n ≡ y .fst n
    leftInv1 x₀ y 0 = proj₁ (y .snd)
    leftInv1 x₀ y (suc n) = cong (l n) (leftInv1 x₀ y n) ∙ sym (proj₂ (y .snd) n)

    path-from-endpoint :
      ∀ {ℓ} {A : Set ℓ} {a b : A} (y : a ≡ b) (x : isProp (a ≡ b))
      → transport (λ i → y i0 ≡ y i) (refl {x = y i0}) ≡ y
    path-from-endpoint y x = x (transport (λ i → y i0 ≡ y i) (refl {x = y i0})) y

    postulate
      x₀-contr :
        ∀ (x₀ : X 0)
        → (y : Σ ((n : ℕ) → X n) (λ x₁ → (x₀ ≡ x₁ 0) × ((n : ℕ) → x₁ (suc n) ≡ l n (x₁ n))))
        → isContr (x₀  ≡ y .fst 0)

      xₙ-contr :
        ∀ (x₀ : X 0)
        → (y : Σ ((n : ℕ) → X n) (λ x₁ → (x₀ ≡ x₁ 0) × ((n : ℕ) → x₁ (suc n) ≡ l n (x₁ n))))
        → (n : ℕ)
        → isContr (fst y (suc n) ≡ l n (fst y n))

    x₀-path-from-endpoint :
        ∀ (x₀ : X 0)
        → (y : Σ ((n : ℕ) → X n) (λ x₁ → (x₀ ≡ x₁ 0) × ((n : ℕ) → x₁ (suc n) ≡ l n (x₁ n))))
        → transport (λ i → x₀ ≡ proj₁ (snd y) i) (refl {x = x₀}) ≡ proj₁ (snd y)
    x₀-path-from-endpoint x₀ y =
      transport (λ i → x₀ ≡ proj₁ (snd y) i) (refl {x = x₀})
        ≡⟨ refl ⟩
      (transport (λ i → (proj₁ (snd y)) i0 ≡ (proj₁ (snd y)) i) (refl {x = (proj₁ (snd y)) i0}))
        ≡⟨ path-from-endpoint (proj₁ (snd y)) (isContr→isProp (x₀-contr x₀ y)) ⟩
      proj₁ (snd y) ∎

    postulate
      extend-path-over-paths :
        ∀ (x₀ : X 0)
        → (y : Σ ((n : ℕ) → X n) (λ x₁ → (x₀ ≡ x₁ 0) × ((n : ℕ) → x₁ (suc n) ≡ l n (x₁ n))))
        → (n : ℕ)
        → transport (λ i₁ →
                    ((cong (l n) (leftInv1 x₀ y n)) ∙ (sym (proj₂ (y .snd) n))) i₁
                    ≡ (cong (l n) (leftInv1 x₀ y n)) i₁)
                (λ z → limit-collapse {S = S} X l x₀ (suc n))
        ≡ transport (λ i₁ → proj₂ (snd y) n i0 ≡ proj₂ (snd y) n i₁) (λ _ → proj₂ (snd y) n i0)

    xₙ-path-from-endpoint :
        ∀ (x₀ : X 0)
        → (y : Σ ((n : ℕ) → X n) (λ x₁ → (x₀ ≡ x₁ 0) × ((n : ℕ) → x₁ (suc n) ≡ l n (x₁ n))))
        → transport (λ i₁ → ((n : ℕ) → leftInv1 x₀ y (suc n)  i₁ ≡ l n (leftInv1 x₀ y n i₁))) (λ n _ → limit-collapse {S = S} X l x₀ (suc n))
        ≡ proj₂ (snd y)
    xₙ-path-from-endpoint x₀ y =
      funExt λ n →
        transport (λ i₁ → leftInv1 x₀ y (suc n) i₁ ≡ l n (leftInv1 x₀ y n i₁)) (λ _ → limit-collapse {S = S} X l x₀ (suc n))
          ≡⟨ refl ⟩
        transport (λ i₁ → (cong (l n) (leftInv1 x₀ y n) ∙ sym (proj₂ (y .snd) n)) i₁ ≡ l n (leftInv1 x₀ y n i₁)) (λ _ → limit-collapse {S = S} X l x₀ (suc n))
          ≡⟨ extend-path-over-paths x₀ y n ⟩
        transport (λ i₁ → proj₂ (snd y) n i0 ≡ proj₂ (snd y) n i₁) (λ _ → proj₂ (snd y) n i0)
          ≡⟨ path-from-endpoint (proj₂ (snd y) n) (isContr→isProp (xₙ-contr x₀ y n)) ⟩
        proj₂ (snd y) n ∎

    projection-equivalence :
      forall {i} {A B : Set i} (a : A × B) -> Cubical.Data.Prod._,_ (proj₁ a) (proj₂ a) ≡ a
    projection-equivalence (a , b) = refl

    leftInv2 :
        ∀ (x₀ : X 0)
        → (y : Σ ((n : ℕ) → X n) (λ x₁ → (x₀ ≡ x₁ 0) × ((n : ℕ) → x₁ (suc n) ≡ l n (x₁ n))))
        → PathP
          (λ i →
            (x₀ ≡ funExt (leftInv1 x₀ y) i 0) ×
            ((n : ℕ) → funExt (leftInv1 x₀ y) i (suc n) ≡ l n (funExt (leftInv1 x₀ y) i n)))
          ((λ _ → x₀) , (λ n _ → limit-collapse {S = S} X l x₀ (suc n))) (snd y)
    leftInv2 x₀ y =
      transport (sym (PathP≡Path (λ i → (x₀ ≡ funExt (leftInv1 x₀ y) i 0) × ((n : ℕ) → funExt (leftInv1 x₀ y) i (suc n) ≡ l n (funExt (leftInv1 x₀ y) i n)))
                                 ((λ _ → x₀) , (λ n _ → limit-collapse {S = S} X l x₀ (suc n)))
                                 (snd y)))
        (transport (λ i₁ → (x₀ ≡ funExt (leftInv1 x₀ y) i₁ 0) × ((n : ℕ) → funExt (leftInv1 x₀ y) i₁ (suc n) ≡ l n (funExt (leftInv1 x₀ y) i₁ n)))
           ((λ _ → x₀) , (λ n _ → limit-collapse {S = S} X l x₀ (suc n)))
          ≡⟨ refl ⟩
        (transport (λ i₁ → x₀ ≡ proj₁ (snd y) i₁) (λ _ → x₀) ,
         (transport (λ i₁ → ((n : ℕ) → leftInv1 x₀ y (suc n)  i₁ ≡ l n (leftInv1 x₀ y n i₁))) (λ n _ → limit-collapse {S = S} X l x₀ (suc n))))
          ≡⟨ (λ i₁ → x₀-path-from-endpoint x₀ y i₁ , xₙ-path-from-endpoint x₀ y i₁) ⟩
        (proj₁ (snd y) , proj₂ (snd y))
          ≡⟨ projection-equivalence (snd y) ⟩
        snd y ∎)

    χ : (x₀ : X 0) → isContr ( Σ ((n : ℕ) → X n) λ x → (x₀ ≡ x 0) × (∀ n → (x (suc n)) ≡ l n (x n)) )
    χ = λ x₀ → ((limit-collapse {S = S} X l x₀) , (refl , (λ n → refl))) , λ y₁ → ΣPathP (funExt (leftInv1 x₀ y₁) , leftInv2 x₀ y₁)

    χ-prop : (x₀ : X 0) → isProp ( Σ ((n : ℕ) → X n) λ x → (x₀ ≡ x 0) × (∀ n → (x (suc n)) ≡ l n (x n)) )
    χ-prop = isContr→isProp ∘ χ

-- Same as leftInv1'
lemma11-2-Iso : ∀ {ℓ} {S : Container {ℓ}} a p n → a n ≡ fun (lemma11-Iso {S = S} (λ _ → S .fst) (λ _ x₂ → x₂)) (a , p) -- = a 0
lemma11-2-Iso a p 0 = refl
lemma11-2-Iso {S = S} a p (suc n) = p n ∙ lemma11-2-Iso {S = S} a p n

α-iso-step-1-4-Iso : ∀ {ℓ} {S : Container {ℓ}}
    -> let (A , B) = S in
    Iso (L (PX,Pπ S))
        (Σ (Σ ((n : ℕ) → A) (λ a → (n : ℕ) → a (suc n) ≡ a n)) λ a → Σ ((n : ℕ) → B (a .fst n) → X (sequence S) n) λ u → (n : ℕ) → PathP (λ x → B (a .snd n x) → X (sequence S) n) (π (sequence S) ∘ u (suc n)) (u n))
fun (α-iso-step-1-4-Iso {S = S@(A , B)}) = (λ a → ((λ n → a .fst n .fst) , (λ n i → a .snd n i .fst)) , ((λ n → a .fst n .snd) , (λ n x₁ → a .snd n x₁ .snd)))
inv (α-iso-step-1-4-Iso {S = S@(A , B)}) = (λ a → (λ n → (a .fst .fst n) , (a .snd .fst n)) , (λ n i → a .fst .snd n i , a .snd .snd n i))
rightInv (α-iso-step-1-4-Iso {S = S@(A , B)}) = refl-fun
leftInv (α-iso-step-1-4-Iso {S = S@(A , B)}) = refl-fun

α-iso-step-5'-Iso : ∀ {ℓ} {S : Container {ℓ}}
    -> let (A , B) = S in
    Iso
      (Σ (Σ ((n : ℕ) → A) (λ a → (n : ℕ) → a (suc n) ≡ a n)) λ a →
        Σ ((n : ℕ) → B (a .fst n) → X (sequence S) n) λ u →
          (n : ℕ) → transport (λ x → B (a .snd n x) → X (sequence S) n) (π (sequence S) ∘ u (suc n)) ≡ (u n))
      (Σ A (λ a → Σ ((n : ℕ) → B a → X (sequence S) n) λ u → (n : ℕ) → π (sequence S) ∘ (u (suc n)) ≡ u n))
α-iso-step-5'-Iso {S = S@(A , B)} =
  (Σ (Σ ((n : ℕ) → A) (λ a → (n : ℕ) → a (suc n) ≡ a n)) λ a →
     Σ ((n : ℕ) → B (a .fst n) → W S n) λ u →
       (n : ℕ) → transport (λ x → B (a .snd n x) → W S n) (πₙ S ∘ u (suc n)) ≡ (u n))
    Iso⟨ Σ-ap-iso (lemma11-Iso {S = S} (λ _ → A) λ _ x → x) (λ {(a , p) →
       Σ-ap-iso (lemma11-temp (a , p)) (lemma11-temp-2-ext (a , p))}) ⟩
  (Σ A λ a → Σ ((n : ℕ) → B a → W S n) λ u →
     (n : ℕ) → transport (λ x → B a → W S n) (πₙ S ∘ u (suc n)) ≡ (u n))
    Iso⟨ Σ-ap-iso₂ (λ a → Σ-ap-iso₂ λ u →
         iso (λ x n → subst (λ k → k n ≡ u n) (funExt (λ n → transportRefl (πₙ S ∘ u (suc n)))) (x n))
             (λ x n → subst (λ k → k n ≡ u n) (sym (funExt (λ n → transportRefl (πₙ S ∘ u (suc n))))) (x n))
             (λ b i n → transportTransport⁻ (cong (λ k → k n ≡ u n) (funExt (λ n → transportRefl (πₙ S ∘ u (suc n))))) (b n) i)
             (λ b i n → transport⁻Transport (cong (λ k → k n ≡ u n) (funExt (λ n → transportRefl (πₙ S ∘ u (suc n))))) (b n) i)) ⟩
  Σ A (λ a → Σ ((n : ℕ) → B a → W S n) λ u →
     (n : ℕ) → πₙ S ∘ u (suc n) ≡ u n) ∎Iso
    where
      lemma11-temp-Path :
        (a : Σ ((n : ℕ) → A) (λ x → (n : ℕ) → x (suc n) ≡ x n))
        → ((n : ℕ) → B (a .fst n) → W (A , B) n)
        ≡ ((n : ℕ) → B (fun (lemma11-Iso {S = S} (λ _ → A) (λ _ x → x)) a) → W (A , B) n)
      lemma11-temp-Path a = cong (λ k → (n : ℕ) → k n) (funExt λ n → λ i → B (lemma11-2-Iso {S = S} (a .fst) (a .snd) n i) → W (A , B) n)

      -- postulate -- Too slow
      lemma11-temp :
        (a : Σ ((n : ℕ) → A) (λ x → (n : ℕ) → x (suc n) ≡ x n)) →
          Iso
            ((n : ℕ) → B (a .fst n) → W (A , B) n)
            ((n : ℕ) → B (fun (lemma11-Iso {S = S} (λ _ → A) (λ _ x → x)) a) → W (A , B) n)
      lemma11-temp = pathToIso ∘ lemma11-temp-Path
      -- fun (lemma11-temp a) x n x₁ = x n (subst B (sym (lemma11-2-Iso {S = S} (a .fst) (a .snd) n)) x₁)
      -- inv (lemma11-temp a) x n x₁ = x n (subst B (lemma11-2-Iso {S = S} (a .fst) (a .snd) n) x₁)
      -- rightInv (lemma11-temp a) b i n x = b n (transportTransport⁻ (cong B (lemma11-2-Iso {S = S} (a .fst) (a .snd) n)) x i)
      -- leftInv (lemma11-temp a) b i n x = b n (transport⁻Transport (cong B (lemma11-2-Iso {S = S} (a .fst) (a .snd) n)) x i)

      postulate
        lemma11-temp-2 :
          (a : Σ ((n : ℕ) → A) (λ x → (n : ℕ) → x (suc n) ≡ x n)) →
          (x : (n : ℕ) → B (a .fst n) → W (A , B) n) →
          (n : ℕ) →
          Iso
            (subst (λ x₁ → B x₁ → W (A , B) n)
                   (a .snd n)
                   (λ x₁ → πₙ (A , B) (x (suc n) x₁))
              ≡ x n)
            (subst (λ x₁ → B x₁ → W (A , B) n)
                   (\ _ -> fun (lemma11-Iso {S = S} (λ _ → A) (λ _ x₂ → x₂)) a)
                   (λ x₁ → πₙ (A , B) (fun (lemma11-temp a) x (suc n) x₁))
              ≡ fun (lemma11-temp a) x n)

      lemma11-temp-2-ext :
          (a : Σ ((n : ℕ) → A) (λ x → (n : ℕ) → x (suc n) ≡ x n)) →
          (x : (n : ℕ) → B (a .fst n) → W (A , B) n) →
          Iso
            ((n : ℕ) → transport (λ x₁ → B (snd a n x₁) → W (A , B) n) (λ x₁ → πₙ (A , B) (x (suc n) x₁)) ≡ x n)
            ((n : ℕ) → transport (λ x₁ → B (fun (lemma11-Iso {S = S} (λ _ → A) (λ _ x₂ → x₂)) (fst a , snd a)) → W (A , B) n)
                                 (λ x₁ → πₙ (A , B) (fun (lemma11-temp (fst a , snd a)) x (suc n) x₁)) ≡ fun (lemma11-temp (fst a , snd a)) x n)
      fun (lemma11-temp-2-ext (a , p) x) x₁ n = fun (lemma11-temp-2 (a , p) x n) (x₁ n)
      inv (lemma11-temp-2-ext (a , p) x) x₁ n = inv (lemma11-temp-2 (a , p) x n) (x₁ n)
      rightInv (lemma11-temp-2-ext (a , p) x) x₁ i n = rightInv (lemma11-temp-2 (a , p) x n) (x₁ n) i
      leftInv (lemma11-temp-2-ext (a , p) x) x₁ i n = leftInv (lemma11-temp-2 (a , p) x n) (x₁ n) i

sym-α-iso-step-5-Iso : ∀ {ℓ} {S : Container {ℓ}}
    -> let (A , B) = S in
    Iso
      (Σ A (λ a → Σ ((n : ℕ) → B a → X (sequence S) n) λ u → (n : ℕ) → π (sequence S) ∘ (u (suc n)) ≡ u n))
      (Σ (Σ ((n : ℕ) → A) (λ a → (n : ℕ) → a (suc n) ≡ a n)) λ a →
        Σ ((n : ℕ) → B (a .fst n) → X (sequence S) n) λ u →
          (n : ℕ) → PathP (λ x → B (a .snd n x) → X (sequence S) n) (π (sequence S) ∘ u (suc n)) (u n))
sym-α-iso-step-5-Iso {S = S@(A , B)} =
  Σ A (λ a → Σ ((n : ℕ) → B a → X (sequence S) n) λ u → (n : ℕ) → π (sequence S) ∘ u (suc n) ≡ u n)
    Iso⟨ sym-iso α-iso-step-5'-Iso ⟩
  (Σ (Σ ((n : ℕ) → A) (λ a → (n : ℕ) → a (suc n) ≡ a n)) λ a →
     Σ ((n : ℕ) → B (a .fst n) → X (sequence S) n) λ u →
       (n : ℕ) → transport (λ x → B (a .snd n x) → X (sequence S) n) (π (sequence S) ∘ u (suc n)) ≡ (u n))
    Iso⟨ iso (λ {((x , y) , (z , w)) → (x , y) , (z , λ n → transport⁻ (PathP≡Path (λ x → B (y n x) → X (sequence S) n) (πₙ S ∘ z (suc n)) (z n)) (w n))})
             (λ {((x , y) , (z , w)) → (x , y) , (z , λ n → transport (PathP≡Path (λ x → B (y n x) → X (sequence S) n) (πₙ S ∘ z (suc n)) (z n)) (w n))})
             (λ {((x , y) , (z , w)) → λ i → (x , y) , (z , (λ n → transport⁻Transport (PathP≡Path (λ x → B (y n x) → X (sequence S) n) (πₙ S ∘ z (suc n)) (z n)) (w n) i))})
             (λ {((x , y) , (z , w)) → λ i → (x , y) , (z , (λ n → transportTransport⁻ (PathP≡Path (λ x → B (y n x) → X (sequence S) n) (πₙ S ∘ z (suc n)) (z n)) (w n) i))}) ⟩
  (Σ (Σ ((n : ℕ) → A) (λ a → (n : ℕ) → a (suc n) ≡ a n)) (λ a →
     Σ ((n : ℕ) → B (a .fst n) → X (sequence S) n) λ u →
       (n : ℕ) → PathP (λ x → B (a .snd n x) → X (sequence S) n) (π (sequence S) ∘ u (suc n)) (u n))) ∎Iso

sym-α-iso-step-6 : ∀ {ℓ} {S : Container {ℓ}}
    -> let (A , B) = S in
    Iso (Σ A (λ a → B a → M-type S))
        (Σ A (λ a → Σ ((n : ℕ) → B a → X (sequence S) n) λ u → (n : ℕ) → π (sequence S) ∘ (u (suc n)) ≡ u n))
fun (sym-α-iso-step-6 {S = S@(A , B)}) (x , y') = x , transport (lemma10 (B x , λ _ → x , (λ x₁ → x₁))) y'
inv (sym-α-iso-step-6 {S = S@(A , B)}) (x , y) = x , transport (sym (lemma10 (B x , λ _ → x , (λ x₁ → x₁)))) y
rightInv (sym-α-iso-step-6 {S = S@(A , B)}) (x , y') = ΣPathP (refl {x = x} , transport⁻Transport (sym (lemma10 (B x , λ _ → x , (λ x₁ → x₁)))) y')
leftInv (sym-α-iso-step-6 {S = S@(A , B)}) (x , y) = ΣPathP (refl {x = x} , transportTransport⁻ (sym (lemma10 (B x , λ _ → x , (λ x₁ → x₁)))) y)

α-iso-step-6 : ∀ {ℓ} {S : Container {ℓ}}
    -> let (A , B) = S in
    Σ A (λ a → Σ ((n : ℕ) → B a → X (sequence S) n) λ u → (n : ℕ) → π (sequence S) ∘ (u (suc n)) ≡ u n)
    ≡ Σ A (λ a → B a → M-type S)
α-iso-step-6 {S = S@(A , B)} = Σ-ap₂ (λ a i → lemma10 (B a , (λ x → a , (λ x₁ → x₁))) (~ i))

-- Lemma 13
α-iso : ∀ {ℓ} {S : Container {ℓ}} -> L (PX,Pπ S) ≡ P₀ {S = S} (M-type S) -- L^P ≡ PL
α-iso {S = S@(A , B)} =
  isoToPath (compIso (α-iso-step-1-4-Iso) (compIso (sym-iso sym-α-iso-step-5-Iso) (sym-iso sym-α-iso-step-6)))

-----------------------------------------------------
-- Shifting the limit of a chain is an equivalence --
-----------------------------------------------------

comp-α-iso-step-1-4-Iso-Sym-L-unique-iso : ∀ {ℓ} {S : Container {ℓ}} -> let (A , B) = S in Iso (Σ (Σ ((n : ℕ) → A) (λ a → (n : ℕ) → a (suc n) ≡ a n)) λ a → Σ ((n : ℕ) → B (a .fst n) → X (sequence S) n) λ u → (n : ℕ) → PathP (λ x → B (a .snd n x) → X (sequence S) n) (π (sequence S) ∘ u (suc n)) (u n))  (L (sequence S))
fun comp-α-iso-step-1-4-Iso-Sym-L-unique-iso (a , b) = (λ { 0 → lift tt ; (suc n) → (a .fst n) , (b .fst n)}) , λ { 0 → refl {x = lift tt} ; (suc m) i → a .snd m i , b .snd m i }
inv comp-α-iso-step-1-4-Iso-Sym-L-unique-iso x = ((λ n → (x .fst) (suc n) .fst) , λ n i → (x .snd) (suc n) i .fst) , (λ n → (x .fst) (suc n) .snd) , λ n i → (x .snd) (suc n) i .snd
fst (rightInv comp-α-iso-step-1-4-Iso-Sym-L-unique-iso (b , c) i) 0 = lift tt
fst (rightInv comp-α-iso-step-1-4-Iso-Sym-L-unique-iso (b , c) i) (suc n) = refl i
snd (rightInv comp-α-iso-step-1-4-Iso-Sym-L-unique-iso (b , c) i) 0 = refl
snd (rightInv comp-α-iso-step-1-4-Iso-Sym-L-unique-iso (b , c) i) (suc n) = c (suc n)
leftInv comp-α-iso-step-1-4-Iso-Sym-L-unique-iso a = ΣPathP (refl , refl)

shift-iso : ∀ {ℓ} {S : Container {ℓ}} -> Iso (P₀ {S = S} (M-type S)) (M-type S)
shift-iso {S = S@(A , B)} = (compIso (sym-α-iso-step-6) (compIso (sym-α-iso-step-5-Iso {S = S}) (comp-α-iso-step-1-4-Iso-Sym-L-unique-iso {S = S})))

shift : ∀ {ℓ} {S : Container {ℓ}} -> P₀ {S = S} (M-type S) ≡ M-type S
shift {S = S@(A , B)} = isoToPath shift-iso -- lemma 13 & lemma 12

-- Transporting along shift

in-fun : ∀ {ℓ} {S : Container {ℓ}} -> P₀ (M-type S) -> M-type S
in-fun {S = S} = fun (shift-iso {S = S})

out-fun : ∀ {ℓ} {S : Container {ℓ}} -> M-type S -> P₀ (M-type S)
out-fun {S = S} = inv (shift-iso {S = S})

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
