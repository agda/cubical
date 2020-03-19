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
open import Cubical.Foundations.Equiv

open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path

module Cubical.M-types.helper where

identity-x : ∀ {ℓ} {A B : Set ℓ} (k : A -> A) -> k ≡ idfun A -> ∀ (x : A) -> k x ≡ x
identity-x {A = A} k = funExt⁻

-- Right
extent-r : ∀ {ℓ} {A B C : Set ℓ} {a b : A -> B} (f : C -> A) -> a ≡ b -> a ∘ f ≡ b ∘ f
extent-r = λ f x i → x i ∘ f

identity-f-r : ∀ {ℓ} {A B : Set ℓ} {k : A -> A} -> k ≡ idfun A -> ∀ (f : B -> A) -> k ∘ f ≡ f
identity-f-r {A = A} {k = k} p f = extent-r {a = k} {b = idfun A} f p

-- Left
extent-l : ∀ {ℓ} {A B C : Set ℓ} {a b : A -> B} (f : B -> C) -> a ≡ b -> f ∘ a ≡ f ∘ b
extent-l = λ f x i → f ∘ x i

identity-f-l : ∀ {ℓ} {A B : Set ℓ} {k : A -> A} -> k ≡ idfun A -> ∀ (f : A -> B) -> f ∘ k ≡ f
identity-f-l {A = A} {k = k} p f = extent-l {a = k} {b = idfun A} f p

-- General

≡-rel-a-monomorphism : ∀ {ℓ} {A B C : Set ℓ} (a : A -> B) (b : B -> A) -> a ∘ b ≡ idfun B -> b ∘ a ≡ idfun A -> {f g : C -> A} -> (a ∘ f ≡ a ∘ g) -> (f ≡ g)
≡-rel-a-monomorphism a b left right {f = f} {g = g} p = λ i →
  compPath-filler {x = f} {y = (b ∘ a ∘ f)} {z = g}
    (sym (identity-f-r right f))
    (λ j → compPath-filler {y = b ∘ a ∘ g}
      (λ k → b ∘ p k)
      (identity-f-r right g)
        j j)
      i i

postulate
  -- TODO: look into isInjectiveTransport

  ≡-rel-inj-iso-0 : ∀ {ℓ} {A B C : Set ℓ}
    (a : A -> B)
    (b : B -> A) ->
    (left : a ∘ b ≡ idfun B) ->
    (right : b ∘ a ≡ idfun A) ->
    {f g : C -> A} ->
    -------------------------------
    ∀ p -> ≡-rel-a-monomorphism a b left right {f = f} {g = g} (extent-l a p) ≡ p

  ≡-rel-inj-iso-1 : ∀ {ℓ} {A B C : Set ℓ}
    (a : A -> B)
    (b : B -> A) ->
    (left : a ∘ b ≡ idfun B) ->
    (right : b ∘ a ≡ idfun A) ->
    {f g : C -> A} ->
    -------------------------------
    ∀ p -> extent-l a (≡-rel-a-monomorphism a b left right {f = f} {g = g} p) ≡ p

≡-rel-a-inj : ∀ {ℓ} {A B C : Set ℓ} (a : A -> B) (b : B -> A) -> a ∘ b ≡ idfun B -> b ∘ a ≡ idfun A -> ∀ {f g : C -> A} -> (a ∘ f ≡ a ∘ g) ≡ (f ≡ g)
≡-rel-a-inj a b left right = ua (isoToEquiv (iso (≡-rel-a-monomorphism a b left right) (extent-l a) (≡-rel-inj-iso-0 a b left right) (≡-rel-inj-iso-1 a b left right)))

≡-rel-b-inj : ∀ {ℓ} {A B C : Set ℓ} (a : A -> B) (b : B -> A) -> a ∘ b ≡ idfun B -> b ∘ a ≡ idfun A -> ∀ {f g : C -> B} -> (b ∘ f ≡ b ∘ g) ≡ (f ≡ g)
≡-rel-b-inj a b left right = ua (isoToEquiv (iso (≡-rel-a-monomorphism b a right left) (extent-l b) (≡-rel-inj-iso-0 b a right left) (≡-rel-inj-iso-1 b a right left)))

-------------------------
-- Unit / × properties --
-------------------------

diagonal-unit : Unit ≡ Unit × Unit
diagonal-unit = isoToPath (iso (λ _ → tt , tt) (λ _ → tt) (λ {(tt , tt) i → tt , tt}) λ a i → tt)

------------------
-- Σ properties --
------------------

Σ-split-iso : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ} {a a' : A} {b : B a} {b' : B a'} → (Σ (a ≡ a') (λ q → PathP (λ i → B (q i)) b b')) ≡ ((a , b) ≡ (a' , b'))
Σ-split-iso = ua Σ≡

subst-hom : ∀ {i j} {X : Set i}(P : X → Set j){x y z : X}
          → (p : x ≡ y)(q : y ≡ z)(u : P x)
          → subst P q (subst P p u) ≡ subst P (p □ q) u
subst-hom {X = X} P {x = x} {y = y} {z = z} p q u = sym (substComposite-□ P p q u)

Σ-ap-iso₂ : ∀ {i j} {X : Set i}
          → {Y Y' : X → Set j}
          → ((x : X) → Y x ≡ Y' x)
          → Σ X Y ≡ Σ X Y'
Σ-ap-iso₂ {X = X} {Y} {Y'} isom =
  isoToPath (iso (λ { (x , y) → x , transport (isom x) y})
                 (λ { (x , y') → x , transport (sym (isom x)) y'})
                 (λ { (x , y) →  ΣPathP (refl , transportTransport⁻ (isom x) y)})
                 (λ { (x , y') → ΣPathP (refl , transport⁻Transport (isom x) y')}))

sym-refl : ∀ {ℓ} {X Y : Set ℓ} {f : X → Y} {g : Y → X} → (a : (∀ b → f (g b) ≡ b)) → ∀ b → (sym (a b) □ (a b)) ≡ λ _ → b
sym-refl a b =
  (sym (a b) □ (a b))
    ≡⟨ □≡∙ (sym (a b)) (a b) ⟩
  sym (a b) ∙ (a b)
    ≡⟨ lUnit (sym (a b) ∙ (a b)) ⟩
  refl ∙ sym (a b) ∙ (a b)
    ≡⟨ assoc refl (sym (a b)) (a b) ⟩
  (refl ∙ sym (a b)) ∙ (a b)
    ≡⟨ compPathr-cancel (a b) refl ⟩
  refl ∎

Σ-ap-iso₁ : ∀ {i} {X X' : Set i} {Y : X' → Set i}
          → (isom : X ≡ X')
          → Σ X (Y ∘ transport isom) ≡ Σ X' Y
Σ-ap-iso₁ {i} {X = X} {X'} {Y} isom =
  let f = transport isom in
  let g = transport⁻ isom in
  let K = transportTransport⁻ isom in
  let H = transport⁻Transport isom in
    isoToPath (iso (λ x → f (x .fst) , (x .snd))
                   (λ x → (g (x .fst)) , subst Y (sym (K (x .fst))) (x .snd))
                   (λ {(x , y) →
                     ΣPathP
                       {B = Y}
                       {x = f (g x) , subst Y (sym (K x)) y}
                       {y = x , y}
                         (K x ,
                         transport (sym (PathP≡Path (λ j → cong Y (K x) j) (subst Y (sym (K x)) y) y))
                         (subst Y (K x) (subst Y (sym (K x)) y)
                           ≡⟨ sym (substComposite-□ Y (sym (K x)) (K x) y) ⟩
                         subst Y ((sym (K x)) □ (K x)) y
                           ≡⟨ (cong (λ a → subst Y a y) (sym-refl {f = f} {g = g} K x)) ⟩
                         subst Y refl y
                           ≡⟨ substRefl {B = Y} y ⟩
                         y ∎))})
                   (λ {(x , y) →
                     ΣPathP
                       {B = Y ∘ transport isom}
                       {x = g (f x) , subst Y (sym (K (f x))) y}
                       {y = x , y}
                       (H x ,
                       transport (sym (PathP≡Path (λ j → Y (f (H x j))) (subst Y (sym (K (f x))) y) y))
                       (subst Y (cong f (H x)) (subst Y (sym (K (f x))) y)
                         ≡⟨ sym (substComposite-□ Y (sym (K (f x))) (λ j → f (H x j)) y) ⟩
                       subst Y (sym (K (f x)) □ (cong f (H x))) y
                         ≡⟨ cong (λ a → subst Y (sym (K (f x)) □ a) y) (lem x) ⟩
                       subst Y (sym (K (f x)) □ K (f x)) y
                         ≡⟨ cong (λ a → subst Y a y) (sym-refl {f = f} {g = g} K (f x)) ⟩
                       subst Y (refl) y
                         ≡⟨ substRefl {B = Y} y ⟩
                       y ∎))}))
    where
      postulate
        lem :  -- Vogt lemma
          let f = transport isom in
          let g = transport⁻ isom in
          let K = transportTransport⁻ isom in
          let H = transport⁻Transport isom in
            ∀ x → (cong f (H x)) ≡ K (f x)

Σ-ap-iso : ∀ {i} {X X' : Set i}
           {Y : X → Set i} {Y' : X' → Set i}
         → (isom : X ≡ X')
         → ((x : X) → Y x ≡ Y' (transport isom x))
         → Σ X Y ≡ Σ X' Y'
Σ-ap-iso {X = X} {X'} {Y} {Y'} isom isom' =
  (Σ-ap-iso₂ isom') □ Σ-ap-iso₁ isom

------------------
-- ∏ properties --
------------------

postulate
  ∏-ap-iso : ∀ {i j} {X X' : Set i}
               {Y : X → Set j}{Y' : X' → Set j}
             → (isom : X ≡ X')
             → ((x' : X') → Y (transport (sym isom) x') ≡ Y' x')
             → ((x : X) → Y x)
             ≡ ((x' : X') → Y' x')
