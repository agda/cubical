{-# OPTIONS --safe --experimental-lossy-unification #-}

module Cubical.Homotopy.FibreDelooping where

open import Cubical.Core.Everything

open import Cubical.Data.Nat

open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Connected
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.HITs.SetTruncation
open import Cubical.HITs.Truncation hiding (elim2) renaming (rec to trRec)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Morphism
open import Cubical.Data.Sigma
open Iso

addSinglIso : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} (x : A)
  → Iso (B × singl x) B
fun (addSinglIso x) (b , _) = b
inv (addSinglIso x) b = b , (isContrSingl _ .fst)
rightInv (addSinglIso x) a = refl
leftInv (addSinglIso x) (b , _) =
  Σ≡Prop (λ _ → isContr→isProp (isContrSingl _)) refl

singlΣIso : {ℓ ℓ' : Level} {A : Type ℓ} {x : A} {B : singl x → Type ℓ'}
  → Iso (Σ (singl x) B) (B (x , refl))
fun (singlΣIso {B = B}) =
  uncurry (uncurry λ x p → transport (λ i → B ((p (~ i)) , λ j → p (~ i ∧ j))))
inv singlΣIso b = (_ , refl) , b
rightInv singlΣIso b = transportRefl b
leftInv (singlΣIso {x = x} {B = B}) =
  uncurry (uncurry (J> λ y → ΣPathP (refl , (transportRefl y))))

module _ {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} where
  F : {a x : A} {b y : B} (h : x ≡ a → y ≡ b)
    → (e : x ≡ a)
    → Ω (A , a) →∙ Ω (B , b)
  fst (F h e) p = sym (h e) ∙ h (e ∙ p)
  snd (F h e) = cong (sym (h e) ∙_) (cong h (sym (rUnit e)))
              ∙ lCancel (h e)

  C : {a : A} {b : B} (x : A) (y : B) (g : Ω (A , a) →∙ Ω (B , b))
    → Type _
  C {a = a} {b = b} x y g = Σ[ h ∈ (x ≡ a → y ≡ b) ] ((e : x ≡ a) → F h e ≡ g) 

  LT : {a : A} {b : B}
       (g : Ω (A , a) →∙ Ω (B , b)) → Type _
  LT g = (x : A) → Σ[ y ∈ B ] C x y g

  RT : {a : A} {b : B}
       (g : Ω (A , a) →∙ Ω (B , b)) → Type _
  RT {a = a} {b = b} g =
    Σ[ f ∈ (A → B) ]
      Σ[ f₀ ∈ (f a ≡ b) ] Ω→ (f , f₀) ≡ g

  LT-prelim : {a : A} {b : B}
       (g : Ω (A , a) →∙ Ω (B , b)) (f : A → B) → Type _
  LT-prelim {a = a} {b = b} g f = (x : A) → C x (f x) g

  RT-prelim : {a : A} {b : B}
       (g : Ω (A , a) →∙ Ω (B , b)) (f : A → B) → Type _
  RT-prelim {a = a} {b = b} g f =
    Σ[ h ∈ ((x : A) → x ≡ a → f x ≡ b) ]
      ((x : A) → (e : x ≡ a) → F (h x) e ≡ g)

  RT→LT1 : {a : A} {b : B}
       (g : Ω (A , a) →∙ Ω (B , b)) (f : A → B)
       → RT-prelim g f → LT-prelim g f
  fst (RT→LT1 g f (h , p) x) = h x
  snd (RT→LT1 g f (h , p) x) e = p x e

  LT1→RT : {a : A} {b : B}
       (g : Ω (A , a) →∙ Ω (B , b)) (f : A → B)
       → LT-prelim g f → RT-prelim g f
  fst (LT1→RT g f F) x e = F x .fst e
  snd (LT1→RT g f F) x e = F x .snd e

  F2 : {x : A} {b y : B} (h : x ≡ x → y ≡ b)
    → Ω (A , x) →∙ Ω (B , b)
  fst (F2 h) p = sym (h refl) ∙ h p
  snd (F2 h) = lCancel (h refl)

  Iso₁ : {a : A} {b : B}
       (g : Ω (A , a) →∙ Ω (B , b)) (f : A → B)
      →  Iso (LT-prelim g f)
              (RT-prelim g f)
  fun (Iso₁ {a = a} {b = b} g f) = LT1→RT g f
  inv (Iso₁ {a = a} {b = b} g f) =  RT→LT1 g f
  rightInv (Iso₁ {a = a} {b = b} g f) p = refl
  leftInv (Iso₁ {a = a} {b = b} g f) p = refl

  Fib2 : {a : A} {b : B}
       (g : Ω (A , a) →∙ Ω (B , b)) (f : A → B) → Type _
  Fib2 {a = a} {b = b} g f =
    Σ[ h ∈ ((x : A) → (x ≡ a) → f x ≡ b) ]
      F (h a) refl ≡ g

  IsContrIso : ∀ {ℓ ℓ'} {A : Type ℓ} {a : A} (B : (x : A) (e : x ≡ a) → Type ℓ')
    → Iso ((x : A) (e : x ≡ a) → B x e) (B a refl)
  fun (IsContrIso B) F = F _ refl
  inv (IsContrIso {a = a} B) r x e =
    J (λ x e → B x (sym e)) r (sym e)
  rightInv (IsContrIso B) r = transportRefl r
  leftInv (IsContrIso {a = a} B) F =
    funExt λ x → funExt λ p
      → J (λ x p → PathP (λ _ → B x (sym p))
      (inv (IsContrIso B) (fun (IsContrIso B) F) x (sym p)) (F x (sym p)))
        (transportRefl (F a refl))
        (sym p)

  Iso₂ : {a : A} {b : B}
       (g : Ω (A , a) →∙ Ω (B , b)) (f : A → B)
      →  Iso (RT-prelim g f) (Fib2 g f)
  Iso₂ g f =
    Σ-cong-iso-snd
      λ h → IsContrIso _

  lem : {x : A} {b y : B} (h : x ≡ x → y ≡ b)
    → F h refl ≡ F2 h
  lem h = →∙Homogeneous≡ (isHomogeneousPath _ _)
     (funExt λ p → cong (sym (h refl) ∙_) (cong h (sym (lUnit p))))


  Fib3 : {a : A} {b : B}
       (g : Ω (A , a) →∙ Ω (B , b)) (f : A → B) → Type _
  Fib3 {a = a} {b = b} g f =
    Σ[ h ∈ ((x : A) → (x ≡ a) → f x ≡ b) ]
      F2 (h a) ≡ g

  Iso₃ : {a : A} {b : B}
       (g : Ω (A , a) →∙ Ω (B , b)) (f : A → B)
       → Iso (Fib2 g f) (Fib3 g f)
  Iso₃ {a = a} {b = b} g f =
    pathToIso (cong (Σ ((x : A) → (x ≡ a) → f x ≡ b))
      (funExt λ h → cong (_≡ g) (lem (h a))))

  Fib3' : {a : A} {b : B}
       (g : Ω (A , a) →∙ Ω (B , b)) (f : A → B) → Type _
  Fib3' {a = a} {b = b} g f =
    Σ[ f₀ ∈ f a ≡ b ]
      F2 (λ p → cong f p ∙ f₀) ≡ g



  Iso₄ : {a : A} {b : B}
       (g : Ω (A , a) →∙ Ω (B , b)) (f : A → B)
       → Iso (Fib3 g f) (Fib3' g f)
  Iso₄ {a = a} {b = b} g f =
     (Σ-cong-iso {A = ((x : A) → (x ≡ a) → f x ≡ b)}
                        {A' = f a ≡ b}
                        {B = λ h → F2 (h a) ≡ g}
                        {B' = λ h → F2 (λ p → cong f p ∙ h) ≡ g}
      (IsContrIso _)
        λ h → pathToIso (cong (_≡ g) (s h)))
    where
    s : (h : (x : A) → x ≡ a → f x ≡ b) → (F2 (h a)) ≡ F2 (λ p → cong f p ∙ h a refl)
    s h = →∙Homogeneous≡ (isHomogeneousPath _ _)
           (funExt λ p → cong₂ _∙_ (cong sym (lUnit (h a refl))) (sym (l p)))
      where
      l : (p : a ≡ a) → cong f p ∙ h a refl ≡ h a p
      l p = (λ i → (λ j → f (p (j ∧ ~ i))) ∙ h (p (~ i)) λ j → (p (~ i ∨ j)))
          ∙ sym (lUnit (h a p))

  Iso₅ : {a : A} {b : B}
       (g : Ω (A , a) →∙ Ω (B , b)) (f : A → B)
       → Iso (Fib3' g f) (Σ[ f₀ ∈ f a ≡ b ] Ω→ (f , f₀) ≡ g)
  Iso₅ {a = a} {b = b} g f =
    pathToIso (cong (Σ (f a ≡ b))
      (funExt λ q → cong (_≡ g)
        (→∙Homogeneous≡ (isHomogeneousPath _ _)
          (funExt
            λ p → cong (_∙ cong f p ∙ q) (cong sym (sym (lUnit q)))
          ∙ sym (doubleCompPath≡compPath (sym q) (cong f p) q)))))

  AllT : {a : A} {b : B}
       (g : Ω (A , a) →∙ Ω (B , b)) (f : A → B)
       → Iso (LT-prelim g f)
              (Σ[ f₀ ∈ f a ≡ b ] Ω→ (f , f₀) ≡ g)
  AllT g f =
    compIso
      (Iso₁ g f)
      (compIso (Iso₂ g f)
        (compIso
          (Iso₃ g f)
          (compIso
            (Iso₄ g f)
            (Iso₅ g f))))

  AllL : {a : A} {b : B}
       (g : Ω (A , a) →∙ Ω (B , b))
       → Iso (LT g) (RT g)
  fst (fun (AllL g) F) = fst ∘ F
  snd (fun (AllL {a = a} g) F) = Iso.fun (AllT g (fst ∘ F)) (snd ∘ F)
  fst (inv (AllL g) (f , f₀ , p) x) = f x
  snd (inv (AllL g) (f , f₀ , p) x) = Iso.inv (AllT g f) (f₀ , p) x
  fst (rightInv (AllL g) (f , f₀ , p) i) = f
  snd (rightInv (AllL g) (f , f₀ , p) i) = Iso.rightInv (AllT g f) (f₀ , p) i
  leftInv (AllL g) F = funExt λ x
    → ΣPathP (refl , λ i → (Iso.leftInv (AllT g (fst ∘ F)) (λ x → snd (F x))) i x)

  Ω→-fib : {a : A} {b : B}
       (g : Ω (A , a) →∙ Ω (B , b))
       → Iso (LT g) (fiber Ω→ g)
  Ω→-fib {a = a} {b = b} g =
    compIso (AllL g)
      (invIso Σ-assoc-Iso)

  C'-base : {a : A} {b : B} (g : Ω (A , a) →∙ Ω (B , b)) →
    Iso (Σ[ y ∈ B ] C a y g)
        (Σ[ h ∈ Ω (A , a) →∙ Ω (B , b) ] ((e : a ≡ a) → F (fst h) e ≡ g))
  C'-base {a = a} {b = b} g =
    compIso
      (Σ-cong-iso-snd (λ y → compIso (Σ-cong-iso-snd λ h
        → compIso (invIso (addSinglIso {B = ((e : a ≡ a) → F h e ≡ g)} (h refl)))
                   (compIso Σ-swap-Iso
                     Σ-assoc-Iso))
            (compIso (invIso Σ-assoc-Iso)
              (compIso (Σ-cong-iso-fst Σ-swap-Iso)
                Σ-assoc-Iso))))
      (compIso
        (compIso (invIso Σ-assoc-Iso)
          (Σ-cong-iso-fst {B = λ s → Σ[ h ∈ (a ≡ a → fst s ≡ b) ]
                          (h refl ≡ sym (snd s)) × ((e : a ≡ a) → F h e ≡ g)}
                          (invIso singl≅signl')))
        (compIso
          singlΣIso
          (invIso Σ-assoc-Iso)))

  hId : {a : A} {b : B} (h : a ≡ a → b ≡ b) → F h refl ≡ (h , {!!})
  hId = {!!}
