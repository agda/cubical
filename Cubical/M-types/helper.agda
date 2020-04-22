{-# OPTIONS --cubical --guardedness #-} --safe

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Function using (_∘_)

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv.HalfAdjoint

open import Cubical.Functions.Embedding
open import Cubical.Functions.FunExtEquiv

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

isoInv : ∀ {ℓ ℓ'} {X : Set ℓ} {Y : Set ℓ'} → Iso X Y → Iso Y X
fun (isoInv isom) = inv isom
inv (isoInv isom) = fun isom
rightInv (isoInv isom) = leftInv isom
leftInv (isoInv isom) = rightInv isom

funExt-iso :
  ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ} (f g : (x : A) → Set ℓ) →
  (∀ (x : A) → Iso (f x) (g x)) → Iso (∀ x → f x) (∀ x → g x)
fun (funExt-iso f g p) x y = fun (p y) (x y)
inv (funExt-iso f g p) x y = inv (p y) (x y)
rightInv (funExt-iso f g p) x i y = rightInv (p y) (x y) i
leftInv (funExt-iso f g p) x i y = leftInv (p y) (x y) i

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

Iso→monomorphism : -- TODO: Not used !
  ∀ {ℓ} {A B C : Set ℓ}
  → (isom : Iso A B)
  --------------------
  → {f g : C -> A}
  → (fun isom ∘ f ≡ fun isom ∘ g)
  → (f ≡ g)
Iso→monomorphism (iso a b right left) {f = f} {g = g} p =
  (sym (identity-f-r (funExt left) f)) ∙ (λ k → b ∘ p k) ∙ (identity-f-r (funExt left) g)

-- abstract
Iso→isEmbedding : ∀ {ℓ} {A B : Set ℓ}
    → (isom : Iso A B)
    -------------------------------
    → isEmbedding (fun isom)
Iso→isEmbedding {A = A} {B} isom = (isEquiv→isEmbedding (equivIsEquiv (isoToEquiv isom)))

funExtIso : ∀ {ℓ ℓ₁} {A : Type ℓ} {B : A → Type ℓ₁} {f g : (x : A) → B x} → Iso (∀ x → f x ≡ g x) (f ≡ g)
funExtIso = iso funExt funExt⁻ refl-fun refl-fun

isEmbedding→Injection' :
  ∀ {ℓ} {A B C : Set ℓ}
  → (a : A -> B)
  → (e : isEmbedding a)
  ----------------------
  → ∀ {f g : C -> A} ->
  ∀ x → (a (f x) ≡ a (g x)) ≡ (f x ≡ g x)
isEmbedding→Injection' a e {f = f} {g} x = sym (ua (cong a , e (f x) (g x)))

Iso→fun-Injection :
  ∀ {ℓ} {A B C : Set ℓ} (isom : Iso A B)
  → ∀ {f g : C -> A}
  → (x : C) → (fun isom (f x) ≡ fun isom (g x)) ≡ (f x ≡ g x)
Iso→fun-Injection {A = A} {B} {C} isom {f = f} {g} =
  isEmbedding→Injection' {A = A} {B} {C} (fun isom) (Iso→isEmbedding {A = A} {B} isom) {f = f} {g = g}

pathCongFunExt :
  ∀ {ℓ} {A : Set ℓ} (a b : (x : A) → Set ℓ)
  → (∀ x → (a x) ≡ (b x))
  → Iso (∀ x → a x) (∀ x → b x)
pathCongFunExt a b p =
  pathToIso (cong (λ k → ∀ x → k x) (funExt p))

Iso→Pi-fun-Injection :
  ∀ {ℓ} {A B C : Set ℓ} (isom : Iso A B)
  → ∀ {f g : C -> A}
  → Iso (∀ x → (fun isom) (f x) ≡ (fun isom) (g x)) (∀ x → f x ≡ g x)
Iso→Pi-fun-Injection {A = A} {B} {C} isom {f = f} {g} =
  pathCongFunExt (λ x → fun isom (f x) ≡ fun isom (g x)) (λ x → f x ≡ g x) (Iso→fun-Injection isom {f = f} {g = g})

Iso→fun-Injection-Iso :
  ∀ {ℓ} {A B C : Set ℓ} (isom : Iso A B)
  → ∀ {f g : C -> A}
  → Iso (fun isom ∘ f ≡ fun isom ∘ g) (f ≡ g)
Iso→fun-Injection-Iso {A = A} {B} {C} isom {f = f} {g} =
  (fun isom) ∘ f ≡ (fun isom) ∘ g
    Iso⟨ isoInv funExtIso ⟩
  (∀ x → (fun isom) (f x) ≡ (fun isom) (g x))
     Iso⟨ Iso→Pi-fun-Injection isom ⟩
  (∀ x → f x ≡ g x)
     Iso⟨ funExtIso ⟩
  f ≡ g ∎Iso

Iso→fun-Injection-Path :
  ∀ {ℓ} {A B C : Set ℓ} (isom : Iso A B)
  → ∀ {f g : C -> A}
  → (fun isom ∘ f ≡ fun isom ∘ g) ≡ (f ≡ g)
Iso→fun-Injection-Path {A = A} {B} {C} isom {f = f} {g} =
  isoToPath (Iso→fun-Injection-Iso isom)

Iso→inv-Injection-Path :
  ∀ {ℓ} {A B C : Set ℓ} (isom : Iso A B) →
  ∀ {f g : C -> B} →
  -----------------------
  ((inv isom) ∘ f ≡ (inv isom) ∘ g) ≡ (f ≡ g)
Iso→inv-Injection-Path {A = A} {B} {C} isom {f = f} {g} = Iso→fun-Injection-Path (isoInv isom)

Iso→fun-Injection-Iso-x :
  ∀ {ℓ} {A B : Set ℓ}
  → (isom : Iso A B)
  → ∀ {x y : A}
  → Iso ((fun isom) x ≡ (fun isom) y) (x ≡ y)
Iso→fun-Injection-Iso-x isom {x} {y} =
  let tempx = λ {(lift tt) → x}
      tempy = λ {(lift tt) → y} in
  fun isom x ≡ fun isom y
    Iso⟨ iso (λ x₁ t → x₁)
             (λ x₁ → x₁ (lift tt))
             refl-fun
             refl-fun ⟩
  (∀ (t : Lift Unit) -> (((fun isom) ∘ tempx) t ≡ ((fun isom) ∘ tempy) t))
    Iso⟨ Iso→Pi-fun-Injection isom ⟩
  (∀ (t : Lift Unit) -> tempx t ≡ tempy t)
     Iso⟨ iso (λ x₁ → x₁ (lift tt))
              (λ x₁ t → x₁)
              refl-fun
              refl-fun ⟩
  x ≡ y ∎Iso

Iso→inv-Injection-Iso-x :
  ∀ {ℓ} {A B : Set ℓ}
  → (isom : Iso A B)
  → ∀ {x y : B}
  → Iso ((inv isom) x ≡ (inv isom) y) (x ≡ y)
Iso→inv-Injection-Iso-x {A = A} {B = B} isom =
  Iso→fun-Injection-Iso-x {A = B} {B = A} (isoInv isom)

Iso→fun-Injection-Path-x :
  ∀ {ℓ} {A B : Set ℓ}
  → (isom : Iso A B)
  → ∀ {x y : A}
  → ((fun isom) x ≡ (fun isom) y) ≡ (x ≡ y)
Iso→fun-Injection-Path-x isom {x} {y} =
  isoToPath (Iso→fun-Injection-Iso-x isom)

Iso→inv-Injection-Path-x :
  ∀ {ℓ} {A B : Set ℓ}
  → (isom : Iso A B)
  → ∀ {x y : B}
  → ((inv isom) x ≡ (inv isom) y) ≡ (x ≡ y)
Iso→inv-Injection-Path-x isom =
  isoToPath (Iso→inv-Injection-Iso-x isom)

-------------------------
-- Unit / × properties --
-------------------------

diagonal-unit : Unit ≡ Unit × Unit
diagonal-unit = isoToPath (iso (λ x → tt , tt) (λ x → tt) (λ {(tt , tt) i → tt , tt}) λ {tt i → tt})

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

open isHAEquiv

-- Theorem 4.2.3. of HoTT book (similar to iso→HAEquiv)
Iso→HAEquiv : ∀ {ℓ} {A B : Set ℓ} → Iso A B → HAEquiv A B
fst (Iso→HAEquiv (iso f g ε η)) = f
g (snd (Iso→HAEquiv (iso f g ε η))) = g
sec (snd (Iso→HAEquiv (iso f g ε η))) = η
ret (snd (Iso→HAEquiv (iso f g ε η))) b = sym (ε (f (g b))) ∙ (cong f (η (g b)) ∙ ε b)
com (snd (Iso→HAEquiv (iso f g ε η))) a =
  cong f (η a)
    ≡⟨ lUnit (cong f (η a)) ⟩
  refl ∙ cong f (η a)
    ≡⟨ cong (λ m → m ∙ cong f (η a)) (sym (lCancel (ε (f (g (f a)))))) ⟩
  (sym (ε (f (g (f a)))) ∙ ε (f (g (f a)))) ∙ cong f (η a)
    ≡⟨ sym (assoc (sym (ε (f (g (f a))))) (ε (f (g (f a)))) (cong f (η a))) ⟩
  sym (ε (f (g (f a)))) ∙ ε (f (g (f a))) ∙ cong f (η a)
    ≡⟨ cong (λ m → sym (ε (f (g (f a)))) ∙ m) (homotopyNatural (ε ∘ f) (η a)) ⟩
  sym (ε (f (g (f a)))) ∙ (cong (f ∘ g ∘ f) (η a)) ∙ ε (f a)
    ≡⟨ cong (λ m → sym (ε (f (g (f a)))) ∙ cong f m ∙ ε (f a)) (sym (Hfa≡fHa (λ x → g (f x)) η a)) ⟩
  sym (ε (f (g (f a)))) ∙ (cong f (η (g (f a)))) ∙ ε (f a) ∎

coherent : ∀ {ℓ} {A B : Set ℓ} (isom : Iso A B) → Set ℓ
coherent (iso f g H K) = ∀ x → cong f (K x) ≡ H (f x)

vogt : ∀ {ℓ} {X Y : Set ℓ} → (isom : Iso X Y) → Σ ((y : Y) → fun isom (inv isom y) ≡ y) λ iso' → coherent (iso (fun isom) (inv isom) iso' (leftInv isom))
vogt {X = X} isom@(iso f g ε η) = ε' , γ
  where
    ε' : ∀ y → f (g y) ≡ y
    ε' x = cong (f ∘ g) (sym (ε x)) ∙ cong f (η (g x)) ∙ ε x

    lem : ∀ (x : X)
      → cong f (η (g (f x))) ∙ ε (f x)
      ≡ cong (f ∘ g) (ε (f x)) ∙ cong f (η x)
    lem x =
      cong f (η (g (f x))) ∙ ε (f x)
        ≡⟨ lUnit (cong (f) (η (g (f x))) ∙ ε (f x)) ⟩
      refl ∙ cong f (η (g (f x))) ∙ ε (f x)
        ≡⟨ cong (λ a → a ∙ cong f (η (g (f x))) ∙ ε (f x)) (sym (rCancel (ε (f (g (f x)))))) ⟩
      (ε (f (g (f x))) ∙ sym (ε (f (g (f x))))) ∙ cong f (η (g (f x))) ∙ ε (f x)
        ≡⟨ sym (assoc (ε (f (g (f x)))) (sym (ε (f (g (f x))))) (cong f (η (g (f x))) ∙ ε (f x))) ⟩
      ε (f (g (f x))) ∙ sym (ε (f (g (f x)))) ∙ cong f (η (g (f x))) ∙ ε (f x)
        ≡⟨ cong (λ a → ε (f (g (f x))) ∙ a) (sym (isHAEquiv.com (Iso→HAEquiv isom .snd) x)) ⟩
      ε (f (g (f x))) ∙ cong f (η x)
        ≡⟨ cong (λ a → a ∙ cong f (η x)) (Hfa≡fHa (f ∘ g) ε (f x)) ⟩
      cong (f ∘ g) (ε (f x)) ∙ cong f (η x) ∎

    γ : coherent (iso f g ε' η)
    γ x = sym
      (ε' (f x)
        ≡⟨ refl ⟩
      cong (f ∘ g) (sym (ε (f x))) ∙ cong f (η (g (f x))) ∙ ε (f x)
        ≡⟨ cong (λ a → cong (f ∘ g) (sym (ε (f x))) ∙ a) (lem x) ⟩
      cong (f ∘ g) (sym (ε (f x))) ∙ cong (f ∘ g) (ε (f x)) ∙ cong f (η x)
        ≡⟨ refl ⟩
      sym (cong (f ∘ g) (ε (f x))) ∙ cong (f ∘ g) (ε (f x)) ∙ cong f (η x)
        ≡⟨ assoc (sym (cong (f ∘ g) (ε (f x)))) (cong (f ∘ g) (ε (f x))) (cong f (η x)) ⟩
      (sym (cong (f ∘ g) (ε (f x))) ∙ cong (f ∘ g) (ε (f x))) ∙ cong f (η x)
        ≡⟨ cong (λ a → a ∙ cong f (η x)) (lCancel (cong (f ∘ g) (ε (f x)))) ⟩
      refl ∙ cong f (η x)
        ≡⟨ sym (lUnit (cong f (η x))) ⟩
      cong f (η x) ∎)

Σ-ap-iso₁ : ∀ {i} {X X' : Set i} {Y : X' → Set i}
          → (isom : Iso X X')
          → Iso (Σ X (Y ∘ (fun isom)))
                 (Σ X' Y)
fun (Σ-ap-iso₁ {i} {X = X} {X'} {Y} isom) x = (fun isom) (x .fst) , x .snd
inv (Σ-ap-iso₁ {i} {X = X} {X'} {Y} isom) x = (inv isom) (x .fst) , subst Y (sym (ε' (x .fst))) (x .snd)
  where
    ε' = fst (vogt isom)
rightInv (Σ-ap-iso₁ {i} {X = X} {X'} {Y} isom) (x , y) = ΣPathP (ε' x ,
  transport
    (sym (PathP≡Path (λ j → cong Y (ε' x) j) (subst Y (sym (ε' x)) y) y))
    (subst Y (ε' x) (subst Y (sym (ε' x)) y)
      ≡⟨ sym (substComposite Y (sym (ε' x)) (ε' x) y) ⟩
    subst Y ((sym (ε' x)) ∙ (ε' x)) y
      ≡⟨ (cong (λ a → subst Y a y) (lCancel (ε' x))) ⟩
    subst Y refl y
      ≡⟨ substRefl {B = Y} y ⟩
    y ∎))
  where
    ε' = fst (vogt isom)
leftInv (Σ-ap-iso₁ {i} {X = X} {X'} {Y} isom@(iso f g ε η)) (x , y) = ΣPathP (η x ,
  transport
    (sym (PathP≡Path (λ j → cong Y (cong f (η x)) j) (subst Y (sym (ε' (f x))) y) y))
    (subst Y (cong f (η x)) (subst Y (sym (ε' (f x))) y)
      ≡⟨ sym (substComposite Y (sym (ε' (f x))) (cong f (η x)) y) ⟩
    subst Y (sym (ε' (f x)) ∙ (cong f (η x))) y
      ≡⟨ cong (λ a → subst Y a y) (lem x) ⟩
    subst Y (refl) y
      ≡⟨ substRefl {B = Y} y ⟩
    y ∎))
  where
    ε' = fst (vogt isom)
    γ = snd (vogt isom)

    lem : (x : X) → sym (ε' (f x)) ∙ cong f (η x) ≡ refl
    lem x = cong (λ a → sym (ε' (f x)) ∙ a) (γ x) ∙ lCancel (ε' (f x))

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
