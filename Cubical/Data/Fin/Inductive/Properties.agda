{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Data.Fin.Inductive.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Data.Fin.Inductive.Base

open import Cubical.Data.Nat
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Nat.Order as OrderOld
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Data.Fin.Base as FinOld
  hiding (Fin ; injectSuc ; fsuc ; fzero ; flast ; ¬Fin0 ; sumFinGen)
open import Cubical.Data.Fin.Properties as FinOldProps
  hiding (sumFinGen0 ; isSetFin ; sumFin-choose ; sumFinGenHom ; sumFinGenId)

open import Cubical.Relation.Nullary

open import Cubical.Algebra.AbGroup.Base using (move4)

Fin≡ : {m : ℕ} (a b : Fin m) → fst a ≡ fst b → a ≡ b
Fin≡ {m} (a , Ha) (b , Hb) H i =
  (H i , hcomp (λ j → λ { (i = i0) → Ha
                        ; (i = i1) → isProp<ᵗ {b}{m} (transp (λ j → H j <ᵗ m) i0 Ha) Hb j })
               (transp (λ j → H (i ∧ j) <ᵗ m) (~ i) Ha))

fsuc-injectSuc : {m : ℕ} (n : Fin m)
  → injectSuc {n = suc m} (fsuc {n = m} n) ≡ fsuc (injectSuc n)
fsuc-injectSuc {m = suc m} (x , p) = refl


elimFin : ∀ {ℓ} {m : ℕ} {A : Fin (suc m) → Type ℓ}
                 (max : A flast)
                 (f : (x : Fin m) → A (injectSuc x))
              → (x : _) → A x
elimFin {m = zero} {A = A} max f (zero , p) = max
elimFin {m = suc m} {A = A} max f (zero , p) = f (zero , tt)
elimFin {m = suc zero} {A = A} max f (suc zero , p) = max
elimFin {m = suc (suc m)} {A = A} max f (suc x , p) =
  elimFin {m = suc m} {A = λ x → A (fsuc x)} max (λ t → f (fsuc t)) (x , p)

elimFin-alt : ∀ {ℓ} {m : ℕ} {A : Fin (suc m) → Type ℓ}
                 (max : A fzero)
                 (f : (x : Fin m) → A (fsuc x))
              → (x : _) → A x
elimFin-alt {m = zero} max f (zero , p) = max
elimFin-alt {m = suc m} max f (zero , p) = max
elimFin-alt {m = suc m} max f (suc x , p) = f (x , p)

elimFinβ : ∀ {ℓ} {m : ℕ} {A : Fin (suc m) → Type ℓ}
                 (max : A flast)
                 (f : (x : Fin m) → A (injectSuc x))
              → ((elimFin {A = A} max f flast ≡ max))
               × ((x : Fin m) → elimFin {A = A} max f (injectSuc x) ≡ f x)
elimFinβ {m = zero} {A = A} max f = refl , λ {()}
elimFinβ {m = suc zero} {A = A} max f = refl , λ {(zero , p) → refl}
elimFinβ {m = suc (suc m)} {A = A} max f =
  elimFinβ {m = (suc m)} {A = λ x → A (fsuc x)} max _ .fst
  , elimFin-alt {m = (suc m)} {A = λ x → elimFin max f (injectSuc {n = suc (suc m)} x) ≡ f x}
             refl
             (elimFinβ {m = (suc m)} {A = λ x → A (fsuc x)} max _ .snd)

¬Fin0 : ¬ Fin 0
¬Fin0 (x , ())

-- properties of finite sums
module _ {ℓ : Level} {A : Type ℓ} (_+A_ : A → A → A) (0A : A)
  (rUnit : (x : _) → x +A 0A ≡ x)
   where
  sumFinGen0 : (n : ℕ) (f : Fin n → A)
    → ((x : _) → f x ≡ 0A)
    → sumFinGen _+A_ 0A f
    ≡ 0A
  sumFinGen0 zero f ind = refl
  sumFinGen0 (suc n) f ind =
    cong₂ _+A_
      (ind flast)
      (sumFinGen0 n (f ∘ injectSuc) (λ x → ind (injectSuc x))) ∙ rUnit 0A

  module _ (comm : (x y : A) → x +A y ≡ y +A x) where
    private
      lUnitA : (x : _) → 0A +A x ≡ x
      lUnitA x = comm _ _ ∙ rUnit x

    sumFin-choose :
      {n : ℕ} (f : Fin n → A)
      → (a : A) (x : Fin n)
      → (f x ≡ a)
      → ((x' : Fin n) → ¬ (x' ≡ x) → f x' ≡ 0A)
      → sumFinGen {n = n} _+A_ 0A f ≡ a
    sumFin-choose {zero} f a x p t = ⊥.rec (¬Fin0 x)
    sumFin-choose {suc n} f a (x , q) p t with (n ≟ᵗ x)
    ... | lt x₁ = ⊥.rec (¬squeeze (q , x₁))
    ... | eq x₁ =
      cong (f flast +A_) (sumFinGen0 n _ λ h → t _
        λ q → ¬m<ᵗm (subst (_<ᵗ n) (cong fst q ∙ sym x₁) (snd h)))
      ∙ rUnit _ ∙ cong f (sym x=flast) ∙ p
      where
      x=flast : (x , q) ≡ flast
      x=flast = Σ≡Prop (λ _ → isProp<ᵗ) (sym x₁)
    ... | gt x₁ =
      cong₂ _+A_
         (t flast (λ p → ¬m<ᵗm (subst (_<ᵗ n) (sym (cong fst p)) x₁)))
         refl
      ∙ lUnitA _
      ∙ sumFin-choose {n = n} (f ∘ injectSuc) a (x , x₁)
          (cong f (Σ≡Prop (λ _ → isProp<ᵗ) refl) ∙ p)
          λ a r → t (injectSuc a) λ d → r (Σ≡Prop (λ _ → isProp<ᵗ)
          (cong fst d))

    module _ (assocA : (x y z : A) → x +A (y +A z) ≡ (x +A y) +A z) where
      sumFinGenHom : (n : ℕ) (f g : Fin n → A)
        → sumFinGen _+A_ 0A (λ x → f x +A g x)
         ≡ (sumFinGen _+A_ 0A f +A sumFinGen _+A_ 0A g)
      sumFinGenHom zero f g = sym (rUnit 0A)
      sumFinGenHom (suc n) f g =
          cong ((f flast +A g flast) +A_) (sumFinGenHom n (f ∘ injectSuc) (g ∘ injectSuc))
        ∙ move4 (f flast) (g flast)
                (sumFinGen _+A_ 0A (λ x → f (injectSuc x)))
                (sumFinGen _+A_ 0A (λ x → g (injectSuc x)))
                _+A_ assocA comm

sumFinGenId : ∀ {ℓ} {A : Type ℓ} {n : ℕ} (_+_ : A → A → A) (0A : A)
  (f g : Fin n → A) → f ≡ g → sumFinGen _+_ 0A f ≡ sumFinGen _+_ 0A g
sumFinGenId _+_ 0A f g p i = sumFinGen _+_ 0A (p i)

Iso-Fin-InductiveFin : (m : ℕ) → Iso (FinOld.Fin m) (Fin m)
Iso.fun (Iso-Fin-InductiveFin m) (x , p) = x , <→<ᵗ p
Iso.inv (Iso-Fin-InductiveFin m) (x , p) = x , <ᵗ→< p
Iso.rightInv (Iso-Fin-InductiveFin m) (x , p) =
  Σ≡Prop (λ w → isProp<ᵗ {n = w} {m}) refl
Iso.leftInv (Iso-Fin-InductiveFin m) _ = Σ≡Prop (λ _ → OrderOld.isProp≤) refl

isSetFin : {n : ℕ} → isSet (Fin n)
isSetFin {n = n} =
  isOfHLevelRetractFromIso 2 (invIso (Iso-Fin-InductiveFin n))
    FinOldProps.isSetFin

isPropFin1 : isProp (Fin 1)
isPropFin1 (zero , tt) (zero , tt) = refl

DiscreteFin : ∀ {n} → Discrete (Fin n)
DiscreteFin x y with discreteℕ (fst x) (fst y)
... | yes p = yes (Σ≡Prop (λ _ → isProp<ᵗ) p)
... | no ¬p = no λ q → ¬p (cong fst q)

inhabitedFibres?Fin : ∀ {ℓ} {A : Type ℓ}
  (da : Discrete A) (n : ℕ) (f : Fin n → A)
  → inhabitedFibres? f
inhabitedFibres?Fin {A = A} da zero f y = inr λ x → ⊥.rec (¬Fin0 x)
inhabitedFibres?Fin {A = A} da (suc n) f y with da (f fzero) y
... | yes p = inl (fzero , p)
... | no ¬p with (inhabitedFibres?Fin da n (f ∘ fsuc) y)
... | inl q = inl ((fsuc (fst q)) , snd q)
... | inr q = inr (elimFin-alt ¬p q)

-- Decompositions in terms of ⊎ and ×
Iso-Fin1⊎Fin-FinSuc : {n : ℕ} → Iso (Fin 1 ⊎ Fin n) (Fin (suc n))
Iso.fun (Iso-Fin1⊎Fin-FinSuc {n = n}) = ⊎.rec (λ _ → flast) injectSuc
Iso.inv (Iso-Fin1⊎Fin-FinSuc {n = n}) = elimFin (inl flast) inr
Iso.rightInv (Iso-Fin1⊎Fin-FinSuc {n = n}) =
  elimFin (cong (⊎.rec (λ _ → flast) injectSuc)
                 (elimFinβ (inl flast) inr .fst))
              λ x → cong (⊎.rec (λ _ → flast) injectSuc)
                      (elimFinβ (inl flast) inr .snd x)
Iso.leftInv (Iso-Fin1⊎Fin-FinSuc {n = n}) (inl (zero , p)) =
  elimFinβ (inl flast) inr .fst
Iso.leftInv (Iso-Fin1⊎Fin-FinSuc {n = n}) (inr x) = elimFinβ (inl flast) inr .snd x

Iso-Fin⊎Fin-Fin+ : {n m : ℕ} → Iso (Fin n ⊎ Fin m) (Fin (n + m))
Iso.fun (Iso-Fin⊎Fin-Fin+ {n = zero} {m = m}) (inr x) = x
Iso.inv (Iso-Fin⊎Fin-Fin+ {n = zero} {m = m}) x = inr x
Iso.rightInv (Iso-Fin⊎Fin-Fin+ {n = zero} {m = m}) x = refl
Iso.leftInv (Iso-Fin⊎Fin-Fin+ {n = zero} {m = m}) (inr x) = refl
Iso-Fin⊎Fin-Fin+ {n = suc n} {m = m} =
  compIso (⊎Iso (invIso Iso-Fin1⊎Fin-FinSuc) idIso)
    (compIso ⊎-assoc-Iso
      (compIso (⊎Iso idIso (Iso-Fin⊎Fin-Fin+ {n = n} {m = m}))
        Iso-Fin1⊎Fin-FinSuc))

Iso-Unit-Fin1 : Iso Unit (Fin 1)
Iso.fun Iso-Unit-Fin1 tt = fzero
Iso.inv Iso-Unit-Fin1 (x , p) = tt
Iso.rightInv Iso-Unit-Fin1 (zero , p) = Σ≡Prop (λ _ → isProp<ᵗ) refl
Iso.leftInv Iso-Unit-Fin1 x = refl

Iso-Bool-Fin2 : Iso Bool (Fin 2)
Iso.fun Iso-Bool-Fin2 false = flast
Iso.fun Iso-Bool-Fin2 true = fzero
Iso.inv Iso-Bool-Fin2 (zero , p) = true
Iso.inv Iso-Bool-Fin2 (suc x , p) = false
Iso.rightInv Iso-Bool-Fin2 (zero , p) = refl
Iso.rightInv Iso-Bool-Fin2 (suc zero , p) =
  Σ≡Prop (λ _ → isProp<ᵗ) refl
Iso.leftInv Iso-Bool-Fin2 false = refl
Iso.leftInv Iso-Bool-Fin2 true = refl

Iso-Fin×Fin-Fin· : {n m : ℕ} → Iso (Fin n × Fin m) (Fin (n · m))
Iso-Fin×Fin-Fin· {n = zero} {m = m} =
  iso (λ {()}) (λ{()}) (λ{()}) (λ{()})
Iso-Fin×Fin-Fin· {n = suc n} {m = m} =
  compIso
    (compIso
      (compIso (Σ-cong-iso-fst (invIso Iso-Fin1⊎Fin-FinSuc))
        (compIso Σ-swap-Iso
          (compIso ×DistR⊎Iso
            (⊎Iso (compIso
              (Σ-cong-iso-snd (λ _ → invIso Iso-Unit-Fin1)) rUnit×Iso)
              Σ-swap-Iso))))
      (⊎Iso idIso Iso-Fin×Fin-Fin·))
    (Iso-Fin⊎Fin-Fin+ {n = m} {n · m})

Iso-Fin×Bool-Fin : {n : ℕ} → Iso (Fin n × Bool) (Fin (2 · n))
Iso-Fin×Bool-Fin =
  compIso (compIso Σ-swap-Iso
    (Σ-cong-iso-fst Iso-Bool-Fin2)) (Iso-Fin×Fin-Fin· {n = 2})

module _ {m : ℕ} where
  Fin→Unit⊎Fin : (x : Fin (suc m)) → Unit ⊎ Fin m
  Fin→Unit⊎Fin = elimFin (inl tt) inr

  Unit⊎Fin→Fin : Unit ⊎ Fin m → Fin (suc m)
  Unit⊎Fin→Fin (inl x) = flast
  Unit⊎Fin→Fin (inr x) = injectSuc x

  Iso-Fin-Unit⊎Fin : Iso (Fin (suc m)) (Unit ⊎ Fin m)
  Iso.fun Iso-Fin-Unit⊎Fin = Fin→Unit⊎Fin
  Iso.inv Iso-Fin-Unit⊎Fin = Unit⊎Fin→Fin
  Iso.rightInv Iso-Fin-Unit⊎Fin (inl x) = elimFinβ (inl tt) inr .fst
  Iso.rightInv Iso-Fin-Unit⊎Fin (inr x) = elimFinβ (inl tt) inr .snd x
  Iso.leftInv Iso-Fin-Unit⊎Fin =
    elimFin
      (cong Unit⊎Fin→Fin (elimFinβ (inl tt) inr .fst))
      λ x → (cong Unit⊎Fin→Fin (elimFinβ (inl tt) inr .snd x))

-- Swapping two elements in Fin n
module _ {n : ℕ} where
  swapFin : (x y : Fin n) → Fin n → Fin n
  swapFin (x , xp) (y , yp) (z , zp) with (discreteℕ z x) | (discreteℕ z y)
  ... | yes p | yes p₁ = z , zp
  ... | yes p | no ¬p = y , yp
  ... | no ¬p | yes p = x , xp
  ... | no ¬p | no ¬p₁ = (z , zp)

  swapFinβₗ : (x y : Fin n) → swapFin x y x ≡ y
  swapFinβₗ (x , xp) (y , yp) with (discreteℕ x x) | discreteℕ x y
  ... | yes p | yes p₁ = Σ≡Prop (λ _ → isProp<ᵗ) p₁
  ... | yes p | no ¬p = refl
  ... | no ¬p | q = ⊥.rec (¬p refl)

  swapFinβᵣ : (x y : Fin n) → swapFin x y y ≡ x
  swapFinβᵣ (x , xp) (y , yp) with (discreteℕ y y) | discreteℕ y x
  ... | yes p | yes p₁ = Σ≡Prop (λ _ → isProp<ᵗ) p₁
  ... | yes p | no ¬p = refl
  ... | no ¬p | q = ⊥.rec (¬p refl)

  swapFin² : (x y z : Fin n) → swapFin x y (swapFin x y z) ≡ z
  swapFin² (x , xp) (y , yp) (z , zp) with discreteℕ z x | discreteℕ z y
  ... | yes p | yes p₁ = help
    where
    help : swapFin (x , xp) (y , yp) (z , zp) ≡ (z , zp)
    help with discreteℕ z x | discreteℕ z y
    ... | yes p | yes p₁ = refl
    ... | yes p | no ¬p = ⊥.rec (¬p p₁)
    ... | no ¬p | r = ⊥.rec (¬p p)
  ... | yes p | no ¬q = help
    where
    help : swapFin (x , xp) (y , yp) (y , yp) ≡ (z , zp)
    help with discreteℕ y x | discreteℕ y y
    ... | yes p' | yes p₁ = Σ≡Prop (λ _ → isProp<ᵗ) (p' ∙ sym p)
    ... | no ¬p | yes p₁ = Σ≡Prop (λ _ → isProp<ᵗ)  (sym p)
    ... | p | no ¬p = ⊥.rec (¬p refl)
  ... | no ¬p | yes p = help
    where
    help : swapFin (x , xp) (y , yp) (x , xp) ≡ (z , zp)
    help with discreteℕ x y | discreteℕ x x
    ... | yes p₁ | yes _ = Σ≡Prop (λ _ → isProp<ᵗ) (p₁ ∙ sym p)
    ... | no ¬p | yes _ = Σ≡Prop (λ _ → isProp<ᵗ)  (sym p)
    ... | s | no ¬p = ⊥.rec (¬p refl)
  ... | no ¬p | no ¬q = help
    where
    help : swapFin (x , xp) (y , yp) (z , zp) ≡ (z , zp)
    help with discreteℕ z x | discreteℕ z y
    ... | yes p | yes p₁ = refl
    ... | yes p | no ¬b = ⊥.rec (¬p p)
    ... | no ¬a | yes b = ⊥.rec (¬q b)
    ... | no ¬a | no ¬b = refl

  swapFinIso : (x y : Fin n) → Iso (Fin n) (Fin n)
  Iso.fun (swapFinIso x y) = swapFin x y
  Iso.inv (swapFinIso x y) = swapFin x y
  Iso.rightInv (swapFinIso x y) = swapFin² x y
  Iso.leftInv (swapFinIso x y) = swapFin² x y

module _ {ℓ : Level} {n : ℕ} {A : Fin n → Type ℓ} (x₀ : Fin n)
  (pt : A x₀) (l : (x : Fin n) → ¬ x ≡ x₀ → A x) where
  private
    x = fst x₀
    p = snd x₀
  elimFinChoose : (x : _) → A x
  elimFinChoose (x' , q) with (discreteℕ x x')
  ... | yes p₁ = subst A (Σ≡Prop (λ _ → isProp<ᵗ) p₁) pt
  ... | no ¬p = l (x' , q) λ r → ¬p (sym (cong fst r))

  elimFinChooseβ : (elimFinChoose x₀ ≡ pt)
                × ((x : _) (q : ¬ x ≡ x₀) → elimFinChoose x ≡ l x q)
  fst elimFinChooseβ with (discreteℕ x x)
  ... | yes p₁ = (λ j → subst A (isSetFin x₀ x₀ (Σ≡Prop (λ z → isProp<ᵗ) p₁) refl j) pt)
                ∙ transportRefl pt
  ... | no ¬p = ⊥.rec (¬p refl)
  snd elimFinChooseβ (x' , q) with (discreteℕ x x')
  ... | yes p₁ = λ q → ⊥.rec (q (Σ≡Prop (λ _ → isProp<ᵗ) (sym p₁)))
  ... | no ¬p = λ s → cong (l (x' , q)) (isPropΠ (λ _ → isProp⊥) _ _)

containsTwoFin : {n : ℕ} (x : Fin (suc (suc n))) → Σ[ y ∈ Fin (suc (suc n)) ] ¬ x ≡ y
containsTwoFin (zero , p) = (1 , p) , λ q → snotz (sym (cong fst q))
containsTwoFin (suc x , p) = fzero , λ q → snotz (cong fst q)

≠flast→<ᵗflast : {n : ℕ} → (x : Fin (suc n)) → ¬ x ≡ flast → fst x <ᵗ n
≠flast→<ᵗflast = elimFin (λ p → ⊥.rec (p refl)) λ p _ → snd p

Fin≠Fin : {n m : ℕ} → ¬ (n ≡ m) → ¬ (Iso (Fin n) (Fin m))
Fin≠Fin {n = zero} {m = zero} p = ⊥.rec (p refl)
Fin≠Fin {n = zero} {m = suc m} p q = Iso.inv q fzero .snd
Fin≠Fin {n = suc n} {m = zero} p q = Iso.fun q fzero .snd
Fin≠Fin {n = suc n} {m = suc m} p q =
  Fin≠Fin {n = n} {m = m} (p ∘ cong suc)
    (Iso⊎→Iso idIso help λ {(zero , tt)
      → cong (Iso.inv Iso-Fin1⊎Fin-FinSuc) (swapFinβₗ (Iso.fun q flast) flast)
       ∙ elimFinβ (inl flast) inr .fst})
  where
  q^ : Iso (Fin (suc n)) (Fin (suc m))
  q^ = compIso q (swapFinIso (Iso.fun q flast) flast)

  help : Iso (Fin 1 ⊎ Fin n) (Fin 1 ⊎ Fin m)
  help = compIso Iso-Fin1⊎Fin-FinSuc (compIso q^ (invIso Iso-Fin1⊎Fin-FinSuc))
