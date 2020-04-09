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
open import Cubical.Foundations.Embedding
open import Cubical.Foundations.FunExtEquiv

module Cubical.M-types.helper where

module helper where

refl-fun : ∀ {ℓ} {A : Set ℓ} (x : A) → x ≡ x
refl-fun x = refl {x = x}

----------------
-- Iso helper --
----------------

open Iso

refl-iso : ∀ {ℓ} {X : Set ℓ} → Iso X X
fun (refl-iso {X = X}) = idfun X
inv (refl-iso {X = X}) = idfun X
rightInv (refl-iso {X = X}) = refl-fun
leftInv (refl-iso {X = X}) = refl-fun

-- Helpful notation
_Iso⟨_⟩_ : ∀ {ℓ ℓ' ℓ''} {B : Set ℓ'} {C : Set ℓ''} (X : Set ℓ) → Iso X B → Iso B C → Iso X C
_ Iso⟨ f ⟩ g = compIso f g

_∎Iso : ∀ {ℓ} (X : Set ℓ) → Iso X X
X ∎Iso = refl-iso {X = X}

infixr  0 _Iso⟨_⟩_
infix   1 _∎Iso

sym-iso : ∀ {ℓ ℓ'} {X : Set ℓ} {Y : Set ℓ'} → Iso X Y → Iso Y X
fun (sym-iso isom) = inv isom
inv (sym-iso isom) = fun isom
rightInv (sym-iso isom) = leftInv isom
leftInv (sym-iso isom) = rightInv isom

funExt-iso :
  ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ} (f g : (x : A) → Set ℓ) →
  (∀ (x : A) → Iso (f x) (g x)) → Iso (∀ x → f x) (∀ x → g x)
fun (funExt-iso f g p) x y = fun (p y) (x y)
inv (funExt-iso f g p) x y = inv (p y) (x y)
rightInv (funExt-iso f g p) x i y = rightInv (p y) (x y) i
leftInv (funExt-iso f g p) x i y = leftInv (p y) (x y) i

------------------
-- Σ properties --
------------------

Σ-split-iso : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ} {a a' : A} {b : B a} {b' : B a'} → Iso (Σ (a ≡ a') (λ q → PathP (λ i → B (q i)) b b')) ((a , b) ≡ (a' , b'))
fun (Σ-split-iso) = ΣPathP
inv (Σ-split-iso) eq = (λ i → fst (eq i)) , (λ i → snd (eq i))
rightInv (Σ-split-iso) = refl-fun
leftInv (Σ-split-iso) = refl-fun

Σ-split : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ} {a a' : A} {b : B a} {b' : B a'} → (Σ (a ≡ a') (λ q → PathP (λ i → B (q i)) b b')) ≡ ((a , b) ≡ (a' , b'))
Σ-split = ua Σ≡

Σ-split-iso' : ∀ {ℓ} {A B : Set ℓ} {a a' : A} {b' b : B} → (Σ (a ≡ a') (λ q → b ≡ b')) ≡ ((a , b) ≡ (a' , b'))
Σ-split-iso' = ua Σ≡

Σ-ap-iso₂ : ∀ {i j} {X : Set i}
          → {Y Y' : X → Set j}
          → ((x : X) → Iso (Y x) (Y' x))
          → Iso (Σ X Y)
                 (Σ X Y')
fun (Σ-ap-iso₂ {X = X} {Y} {Y'} isom) (x , y) = x , fun (isom x) y
inv (Σ-ap-iso₂ {X = X} {Y} {Y'} isom) (x , y') = x , inv (isom x) y'
rightInv (Σ-ap-iso₂ {X = X} {Y} {Y'} isom) (x , y) = ΣPathP (refl , rightInv (isom x) y)
leftInv (Σ-ap-iso₂ {X = X} {Y} {Y'} isom) (x , y') = ΣPathP (refl , leftInv (isom x) y')

Σ-ap₂ : ∀ {i j} {X : Set i}
          → {Y Y' : X → Set j}
          → ((x : X) → Y x ≡ Y' x)
          → Σ X Y ≡ Σ X Y'
Σ-ap₂ {X = X} {Y} {Y'} isom = isoToPath (Σ-ap-iso₂ (pathToIso ∘ isom))

postulate
  naturality-1 : ∀ {ℓ} {A B : Set ℓ} (p : Iso A B) (x : A) → cong (fun p) (leftInv p x) ≡ rightInv p (fun p x)
  naturality-2 : ∀ {ℓ} {A B : Set ℓ} (p : Iso A B) (x : B) → cong (inv p) (rightInv p x) ≡ leftInv p (inv p x)
      -- fibers-total
      -- homotopyNatural : {f g : A → B} (H : ∀ a → f a ≡ g a) {x y : A} (p : x ≡ y) →
      -- Hfa≡fHa {!!} {!!} {!!}
      -- Vogt lemma -- law of excluded middle -- Hfa≡fHa (equiv)

Σ-ap-iso₁ : ∀ {i} {X X' : Set i} {Y : X' → Set i}
          → (isom : Iso X X')
          → Iso (Σ X (Y ∘ (fun isom)))
                 (Σ X' Y)
fun (Σ-ap-iso₁ {i} {X = X} {X'} {Y} isom) x = (fun isom) (x .fst) , x .snd
inv (Σ-ap-iso₁ {i} {X = X} {X'} {Y} isom) x = (inv isom) (x .fst) , subst Y (sym (rightInv isom (x .fst))) (x .snd)
rightInv (Σ-ap-iso₁ {i} {X = X} {X'} {Y} isom) (x , y) = ΣPathP (rightInv isom x ,
  transport
    (sym (PathP≡Path (λ j → cong Y (rightInv isom x) j) (subst Y (sym (rightInv isom x)) y) y))
    (subst Y (rightInv isom x) (subst Y (sym (rightInv isom x)) y)
      ≡⟨ sym (substComposite Y (sym (rightInv isom x)) (rightInv isom x) y) ⟩
    subst Y ((sym (rightInv isom x)) ∙ (rightInv isom x)) y
      ≡⟨ (cong (λ a → subst Y a y) (lCancel (rightInv isom x))) ⟩
    subst Y refl y
      ≡⟨ substRefl {B = Y} y ⟩
    y ∎))
leftInv (Σ-ap-iso₁ {i} {X = X} {X'} {Y} isom) (x , y) = ΣPathP (leftInv isom x ,
  transport
    (sym (PathP≡Path (λ j → Y (fun isom (leftInv isom x j))) (subst Y (sym ((rightInv isom) (fun isom x))) y) y))
    (subst Y (cong (fun isom) (leftInv isom x)) (subst Y (sym ((rightInv isom) (fun isom x))) y)
      ≡⟨ sym (substComposite Y (sym ((rightInv isom) (fun isom x))) (λ j → fun isom (leftInv isom x j)) y) ⟩
    subst Y (sym ((rightInv isom) (fun isom x)) ∙ (cong (fun isom) (leftInv isom x))) y
      ≡⟨ cong (λ a → subst Y (sym ((rightInv isom) (fun isom x)) ∙ a) y) (naturality-1 isom x) ⟩
    subst Y (sym ((rightInv isom) (fun isom x)) ∙ (rightInv isom) (fun isom x)) y
      ≡⟨ cong (λ a → subst Y a y) (lCancel (rightInv isom (fun isom x))) ⟩
    subst Y (refl) y
      ≡⟨ substRefl {B = Y} y ⟩
    y ∎))

Σ-ap₁ : ∀ {i} {X X' : Set i} {Y : X' → Set i}
          → (isom : X ≡ X')
          → Σ X (Y ∘ transport isom) ≡ Σ X' Y
Σ-ap₁ {i} {X = X} {X'} {Y} isom = isoToPath (Σ-ap-iso₁ (pathToIso isom))

Σ-ap-iso : ∀ {i} {X X' : Set i}
           {Y : X → Set i} {Y' : X' → Set i}
         → (isom : Iso X X')
         → ((x : X) → Iso (Y x) (Y' (fun isom x)))
         → Iso (Σ X Y)
                (Σ X' Y')
Σ-ap-iso {X = X} {X'} {Y} {Y'} isom isom' = compIso (Σ-ap-iso₂ isom') (Σ-ap-iso₁ isom)

Σ-ap :
  ∀ {i} {X X' : Set i} {Y : X → Set i} {Y' : X' → Set i}
  → (isom : X ≡ X')
  → ((x : X) → Y x ≡ Y' (transport isom x))
  ----------
  → (Σ X Y)
  ≡ (Σ X' Y')
Σ-ap  {X = X} {X'} {Y} {Y'} isom isom' = isoToPath (Σ-ap-iso (pathToIso isom) (pathToIso ∘ isom'))

Σ-ap' :
  ∀ {ℓ} {X X' : Set ℓ} {Y : X → Set ℓ} {Y' : X' → Set ℓ}
  → (isom : X ≡ X')
  → (PathP (λ i → isom i → Set _) Y Y')
  ----------
  → (Σ X Y)
  ≡ (Σ X' Y')
Σ-ap'  {ℓ} {X = X} {X'} {Y} {Y'} isom isom' = cong₂ (λ (a : Set ℓ) (b : a → Set ℓ) → Σ a λ x → b x) isom isom'

---

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

transport-iso :
  ∀ {ℓ} {X Y : Set ℓ}
  → (isom : Iso X Y)
  → transport (isoToPath isom) ≡ fun isom
transport-iso isom = funExt (transportRefl ∘ fun isom)

≡-to-embedding : ∀ {ℓ} {A B C : Set ℓ}
  → (isom : Iso A B)
  -------------------------------
  → isEmbedding (fun isom)
≡-to-embedding {A = A} {B} {C} isom = (isEquiv→isEmbedding (equivIsEquiv (isoToEquiv isom)))

funExtIso : ∀ {ℓ ℓ₁} {A : Type ℓ} {B : A → Type ℓ₁} {f g : (x : A) → B x} → Iso (∀ x → f x ≡ g x) (f ≡ g)
funExtIso = iso funExt funExt⁻ refl-fun refl-fun

≡-rel-a-inj' : ∀ {ℓ} {A B C : Set ℓ} (a : A -> B) (e : isEmbedding a) → ∀ {f g : C -> A} -> ∀ x → ((a (f x) ≡ a (g x)) ≡ (f x ≡ g x))
≡-rel-a-inj' a e {f = f} {g} x = sym (ua (cong a , e (f x) (g x)))

≡-rel-a-inj-Iso-helper-3 :
  ∀ {ℓ} {A B C : Set ℓ} (isom : Iso A B)
  → ∀ {f g : C -> A}
  → (x : C) → (fun isom (f x) ≡ fun isom (g x)) ≡ (f x ≡ g x)
≡-rel-a-inj-Iso-helper-3 {A = A} {B} {C} isom {f = f} {g} =
  ≡-rel-a-inj' {A = A} {B} {C} (fun isom) (≡-to-embedding {A = A} {B} {C} isom) {f = f} {g = g}

abstract
  pathCongFunExt :
    ∀ {ℓ} {A : Set ℓ} (a b : (x : A) → Set ℓ)
    → (∀ x → (a x) ≡ (b x))
    → Iso (∀ x → a x) (∀ x → b x)
  pathCongFunExt a b p =
    pathToIso (cong (λ k → ∀ x → k x) (funExt p))

≡-rel-a-inj-Iso-helper :
  ∀ {ℓ} {A B C : Set ℓ} (isom : Iso A B)
  → ∀ {f g : C -> A}
  → Iso (∀ x → (fun isom) (f x) ≡ (fun isom) (g x)) (∀ x → f x ≡ g x)
≡-rel-a-inj-Iso-helper {A = A} {B} {C} isom {f = f} {g} =
  pathCongFunExt (λ x → fun isom (f x) ≡ fun isom (g x)) (λ x → f x ≡ g x) (≡-rel-a-inj-Iso-helper-3 isom {f = f} {g = g})

≡-rel-a-inj-Iso :
  ∀ {ℓ} {A B C : Set ℓ} (isom : Iso A B)
  → ∀ {f g : C -> A}
  → Iso (fun isom ∘ f ≡ fun isom ∘ g) (f ≡ g)
≡-rel-a-inj-Iso {A = A} {B} {C} isom {f = f} {g} =
  (fun isom) ∘ f ≡ (fun isom) ∘ g
    Iso⟨ sym-iso funExtIso ⟩
  (∀ x → (fun isom) (f x) ≡ (fun isom) (g x))
     Iso⟨ ≡-rel-a-inj-Iso-helper isom ⟩
  (∀ x → f x ≡ g x)
     Iso⟨ funExtIso ⟩
  f ≡ g ∎Iso

≡-rel-a-inj :
  ∀ {ℓ} {A B C : Set ℓ} (isom : Iso A B)
  → ∀ {f g : C -> A}
  → (fun isom ∘ f ≡ fun isom ∘ g) ≡ (f ≡ g)
≡-rel-a-inj {A = A} {B} {C} isom {f = f} {g} = isoToPath (≡-rel-a-inj-Iso isom)

≡-rel-b-inj :
  ∀ {ℓ} {A B C : Set ℓ} (isom : Iso A B) →
  ∀ {f g : C -> B} →
  -----------------------
  ((inv isom) ∘ f ≡ (inv isom) ∘ g) ≡ (f ≡ g)
≡-rel-b-inj {A = A} {B} {C} isom {f = f} {g} =
  (inv isom) ∘ f ≡ (inv isom) ∘ g
    ≡⟨ sym funExtPath ⟩
  (∀ x → inv isom (f x) ≡ inv isom (g x))
    ≡⟨ (λ i → ∀ x → ≡-rel-a-inj' {A = B} {A} {C} (inv isom) (≡-to-embedding {A = B} {A} {C} (sym-iso isom)) {f = f} {g = g} x i) ⟩
  (∀ x → f x ≡ g x)
    ≡⟨ funExtPath ⟩
  f ≡ g ∎

≡-rel-a-inj-x-Iso :
  ∀ {ℓ} {A B : Set ℓ}
  → (isom : Iso A B)
  → ∀ {x y : A}
  → Iso ((fun isom) x ≡ (fun isom) y) (x ≡ y)
≡-rel-a-inj-x-Iso isom {x} {y} =
  let tempx = λ {(lift tt) → x}
      tempy = λ {(lift tt) → y} in
  fun isom x ≡ fun isom y
    Iso⟨ iso (λ x₁ t → x₁)
             (λ x₁ → x₁ (lift tt))
             refl-fun
             refl-fun ⟩
  (∀ (t : Lift Unit) -> (((fun isom) ∘ tempx) t ≡ ((fun isom) ∘ tempy) t))
    Iso⟨ ≡-rel-a-inj-Iso-helper isom ⟩
  (∀ (t : Lift Unit) -> tempx t ≡ tempy t)
     Iso⟨ iso (λ x₁ → x₁ (lift tt))
              (λ x₁ t → x₁)
              refl-fun
              refl-fun ⟩
  x ≡ y ∎Iso

≡-rel-b-inj-x-Iso :
  ∀ {ℓ} {A B : Set ℓ}
  → (isom : Iso A B)
  → ∀ {x y : B}
  → Iso ((inv isom) x ≡ (inv isom) y) (x ≡ y)
≡-rel-b-inj-x-Iso {A = A} {B = B} isom = ≡-rel-a-inj-x-Iso {A = B} {B = A} (sym-iso isom)

≡-rel-a-inj-x :
  ∀ {ℓ} {A B : Set ℓ}
  → (isom : Iso A B)
  → ∀ {x y : A}
  → ((fun isom) x ≡ (fun isom) y) ≡ (x ≡ y)
≡-rel-a-inj-x isom {x} {y} = isoToPath (≡-rel-a-inj-x-Iso isom)

≡-rel-b-inj-x :
  ∀ {ℓ} {A B : Set ℓ}
  → (isom : Iso A B)
  → ∀ {x y : B}
  → ((inv isom) x ≡ (inv isom) y) ≡ (x ≡ y)
≡-rel-b-inj-x isom = isoToPath (≡-rel-b-inj-x-Iso isom)

-------------------------
-- Unit / × properties --
-------------------------

diagonal-unit : Unit ≡ Unit × Unit
diagonal-unit = isoToPath (iso (λ x → tt , tt) (λ x → tt) (λ {(tt , tt) i → tt , tt}) λ {tt i → tt})
