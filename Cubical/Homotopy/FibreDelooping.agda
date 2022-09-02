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

addSignlIsoDep : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'}
  → (f : (x : A) → B x)
  → Iso A (Σ[ x ∈ A ] singl (f x))
fun (addSignlIsoDep f) a = a , isContrSingl _ .fst
inv (addSignlIsoDep f) = fst
rightInv (addSignlIsoDep f) _ = Σ≡Prop (λ _ → isContr→isProp (isContrSingl _)) refl
leftInv (addSignlIsoDep f) a = refl

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

  G : {a : A} {b : B} (h : Ω (A , a) →∙ Ω (B , b)) → F (fst h) refl ≡ h
  G h = →∙Homogeneous≡ (isHomogeneousPath _ _)
          (funExt λ x → cong₂ _∙_ (cong sym (snd h)) (cong (fst h) (sym (lUnit x)))
          ∙ sym (lUnit (fst h x)))

  R2 : {a : A} {b : B} (g : Ω (A , a) →∙ Ω (B , b)) →
    Iso (Σ[ h ∈ Ω (A , a) →∙ Ω (B , b) ] ((e : a ≡ a) → F (fst h) e ≡ g))
        (Σ[ w ∈ ((e : a ≡ a) → F (fst g) e ≡ g) ] w refl ≡ G g)
  R2 {a = a} {b = b} g =
    compIso (Σ-cong-iso-snd
      (λ h → compIso (compIso (addSignlIsoDep λ w → G h ⁻¹ ∙ w refl)
               idIso)
              (invIso Σ-assoc-Iso)))
      (compIso
        (invIso Σ-assoc-Iso)
        (compIso
          (Σ-cong-iso-fst
            (compIso (Σ-cong-iso-snd (λ h → Σ-swap-Iso))
              ((invIso Σ-assoc-Iso))))
          (compIso
            Σ-assoc-Iso
            (compIso
              (Σ-cong-iso-fst
                {B = λ h → Σ[ z ∈ ((e : (a ≡ a))
                           → F (fst (fst h)) e ≡ g) ] G (fst h) ⁻¹ ∙ z (λ _ → a)
                            ≡ sym (snd h)} (invIso singl≅signl'))
              (compIso
                singlΣIso
                (Σ-cong-iso-snd
                  λ h → compIso (congIso (equivToIso (compPathlEquiv (G g))))
                                 (equivToIso
                                    (compEquiv
                                      (compPathrEquiv
                                        (sym (rUnit (G g))))
                                      (compPathlEquiv
                                      (lUnit (h refl)
                                    ∙ cong (_∙ h refl)
                                        (sym (rCancel (G g)))
                                    ∙ sym (assoc _ _ _)))))))))))


  C₀ : {a : A} {b : B} (g : Ω (A , a) →∙ Ω (B , b)) →
    Iso  (Σ[ y ∈ B ] C a y g)
        (Σ[ w ∈ ((e : a ≡ a) → F (fst g) e ≡ g) ] w refl ≡ G g)
  C₀ g = compIso (C'-base g) (R2 g)
  
  pre-main : (n k : ℕ) {a : A} {b : B} (g : Ω (A , a) →∙ Ω (B , b))
    → isConnected (suc (suc n)) A
       → isOfHLevel (suc (suc (n + n + k))) B
       → isOfHLevel k ((Σ[ w ∈ ((e : a ≡ a) → F (fst g) e ≡ g) ] w refl ≡ G g))
  pre-main n k {a = a} {b = b} g conA hLevB =
    isOfHLevelPointedFib n k r
      λ q → subst (λ m → isOfHLevel m (F (fst g) q ≡ g))
                   (+-comm n k)
                   (isOfHLevelPath' (n + k) l _ _)
    where
    r : isConnected (suc n) (fst (Ω (A , a)))
    r = isConnectedPath (suc n) conA _ _

    l : isOfHLevel (suc (n + k)) (Ω (A , a) →∙ Ω (B , b))
    l = isOfHLevelPointedFib n (suc (n + k)) r {B = λ _ → b ≡ b}
          λ _ → subst (λ m → isOfHLevel m (b ≡ b))
                   (cong suc
                             (sym (+-assoc n n k)
                             ∙ cong (n +_) (+-comm n k)
                             ∙ +-assoc n k n))
                   (isOfHLevelPath' (suc (n + n + k)) hLevB _ _)

  main' : (n k : ℕ) {a : A} {b : B} (g : Ω (A , a) →∙ Ω (B , b))
    → isConnected (suc (suc n)) A
    → isOfHLevel (suc (suc (n + n + k))) B
    → (x : _) → isOfHLevel k (Σ[ y ∈ B ] C x y g)
  main' n k {a = a} {b = b} g conA hLevB =
    (invEq (_ , L)
          λ _ →
            isOfHLevelRetractFromIso k
              (C₀ g)
              (pre-main n k g conA hLevB))
    where
    L = elim.isEquivPrecompose (λ (x : Unit) → a) 1
         (λ x → isOfHLevel k (Σ-syntax B (λ y → C x y g))
              , isPropIsOfHLevel k)
         λ p → isConnectedSubtr 1 n
           (subst (λ m → isConnected m (fiber (λ (x : Unit) → a) p))
                  (+-comm 1 n)
                  (isConnectedPoint (suc n) conA a p))

  main : (n k : ℕ) {a : A} {b : B} (g : Ω (A , a) →∙ Ω (B , b))
    → isConnected (suc (suc n)) A
    → isOfHLevel (suc (suc (n + n + k))) B
    → isOfHLevel k (fiber Ω→ g)
  main n k {a = a} {b = b} g conA hLevB =
    isOfHLevelRetractFromIso k
      (invIso (Ω→-fib g))
      (isOfHLevelΠ k (
        (invEq (_ , L)
          λ _ →
            isOfHLevelRetractFromIso k
              (C₀ g)
              (pre-main n k g conA hLevB))))
    where
    L = elim.isEquivPrecompose (λ (x : Unit) → a) 1
         (λ x → isOfHLevel k (Σ-syntax B (λ y → C x y g))
              , isPropIsOfHLevel k)
         λ p → isConnectedSubtr 1 n
           (subst (λ m → isConnected m (fiber (λ (x : Unit) → a) p))
                  (+-comm 1 n)
                  (isConnectedPoint (suc n) conA a p))

open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.EilenbergMacLane.CupProduct


open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Group.Instances.IntMod
open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Semigroup.Base
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Semigroup

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Data.Fin.Arithmetic

open CommRingStr renaming (_+_ to _+R_)
open IsCommRing
open IsMonoid
open IsSemigroup
open IsRing
open AbGroupStr renaming (_+_ to _+G_)

open import Cubical.Data.Nat.Order

-- ℤ/2 lemmas
ℤ/2-elim : ∀ {ℓ} {A : Fin 2 → Type ℓ} → A 0 → A 1 → (x : _) → A x
ℤ/2-elim {A = A} a₀ a₁ (zero , p) = subst (λ p → A (zero , p)) (isProp≤ (0 .snd) p) a₀
ℤ/2-elim {A = A} a₀ a₁ (suc zero , p) = subst (λ p → A (1 , p)) (isProp≤ (1 .snd) p) a₁
ℤ/2-elim {A = A} a₀ a₁ (suc (suc x) , p) =
  ⊥.rec (snotz (cong (λ x → predℕ (predℕ x)) (+-comm (3 + x) (fst p) ∙ snd p)))

-Const-ℤ/2 : (x : fst (ℤGroup/ 2)) → -ₘ x ≡ x
-Const-ℤ/2 = ℤ/2-elim refl refl

ℤ/2CommRing : CommRing ℓ-zero
fst ℤ/2CommRing = fst (Group→AbGroup (ℤGroup/ 2) +ₘ-comm)
0r (snd ℤ/2CommRing) = fzero
1r (snd ℤ/2CommRing) = 1
_+R_ (snd ℤ/2CommRing) = _+ₘ_
CommRingStr._·_ (snd ℤ/2CommRing) = _·ₘ_
CommRingStr.- snd ℤ/2CommRing = -ₘ_
+IsAbGroup (isRing (isCommRing (snd ℤ/2CommRing))) =
  isAbGroup (Group→AbGroup (ℤGroup/ 2) +ₘ-comm .snd)
is-set (isSemigroup (·IsMonoid (isRing (isCommRing (snd ℤ/2CommRing))))) = isSetFin
IsSemigroup.·Assoc (isSemigroup (·IsMonoid (isRing (isCommRing (snd ℤ/2CommRing))))) =
  ℤ/2-elim (ℤ/2-elim (ℤ/2-elim refl refl) (ℤ/2-elim refl refl))
  (ℤ/2-elim (ℤ/2-elim refl refl) (ℤ/2-elim refl refl))
·IdR (·IsMonoid (isRing (isCommRing (snd ℤ/2CommRing)))) = ℤ/2-elim refl refl
·IdL (·IsMonoid (isRing (isCommRing (snd ℤ/2CommRing)))) = ℤ/2-elim refl refl
IsRing.·DistR+ (isRing (isCommRing (snd ℤ/2CommRing))) =
  ℤ/2-elim (λ y z → refl) (ℤ/2-elim (ℤ/2-elim refl refl) (ℤ/2-elim refl refl))
IsRing.·DistL+ (isRing (isCommRing (snd ℤ/2CommRing))) =
  ℤ/2-elim (ℤ/2-elim (ℤ/2-elim refl refl) (ℤ/2-elim refl refl))
  (ℤ/2-elim (ℤ/2-elim refl refl) (ℤ/2-elim refl refl))
IsCommRing.·Comm (isCommRing (snd ℤ/2CommRing)) =
  ℤ/2-elim (ℤ/2-elim refl refl) (ℤ/2-elim refl refl)

ℤ/2Ring : Ring ℓ-zero
ℤ/2Ring = CommRing→Ring ℤ/2CommRing

K : (n : ℕ) → Type
K n = EM (Ring→AbGroup ℤ/2Ring ) n

K∙ : (n : ℕ) → Pointed₀
K∙ n = EM∙ (Ring→AbGroup ℤ/2Ring ) n
open PlusBis
cup : (n m : ℕ) → K n → K m → K (n +' m) 
cup n m = _⌣ₖ_

SteenRInd : (n i : ℕ) → K∙ n →∙ K∙ (i +' n) → K∙ (suc n) →∙ K∙ (i +' (suc n))
SteenRInd n i ST = {!!}

open import Cubical.Data.Sum as ⊎
dic : (n m : ℕ) → (n ≤ m) ⊎ (n > m)
dic n m = l (n ≟ m)
  where
  l : Trichotomy n m → (n ≤ m) ⊎ (n > m)
  l (lt x) = inl (suc (fst x) , sym (+-suc (fst x) n) ∙ snd x)
  l (eq x) = inl (0 , x)
  l (gt x) = inr x

lemiSubst : {x y : ℕ} (p : x ≡ y) → subst K p (0ₖ x) ≡ 0ₖ y
lemiSubst {x = x} = J (λ y p → subst K p (0ₖ x) ≡ 0ₖ y) (transportRefl _)

lemiSubst' : {x y : ℕ} (p : x ≡ y) → subst (λ x → fst (Ω (K∙ x))) p refl ≡ refl
lemiSubst' {x = x} = J (λ y p → subst (λ x → fst (Ω (K∙ x))) p refl ≡ refl) (transportRefl _)

asd : (n : ℕ) (g : (Ω (K∙ (suc n)) →∙ Ω (K∙ (n +' (suc n)))))
  → (isProp (fiber Ω→ g))
  × ((x : _) → isProp (Σ[ y ∈ _ ] (C x y g)))
asd n g = main n 1 g (isConnectedEM (suc n))
         (subst (λ m → isOfHLevel m (K (n +' suc n)))
           lem'
           (hLevelEM (Ring→AbGroup ℤ/2Ring) (n +' suc n)))
       , main' n 1 g (isConnectedEM (suc n))
         (subst (λ m → isOfHLevel m (K (n +' suc n)))
           lem'
           (hLevelEM (Ring→AbGroup ℤ/2Ring) (n +' suc n)))
  where
  lem' : (2 + (n +' suc n)) ≡ suc (suc (n + n + 1))
  lem' = cong (suc ∘ suc) (+'≡+ n (suc n)
                        ∙ +-suc n n
                        ∙ +-comm 1 (n + n))
  H : (y : Ω (K∙ (suc n)) →∙ Ω (K∙ (n +' suc n)))
      → isProp (fiber Ω→ y)
  H y = main n 1 y (isConnectedEM (suc n))
         (subst (λ m → isOfHLevel m (K (n +' suc n)))
           lem'
           (hLevelEM (Ring→AbGroup ℤ/2Ring) (n +' suc n)))

+'-suc' : (n m : ℕ) → suc (n +' m) ≡ (n +' suc m)
+'-suc' n m = cong suc (+'-comm n m)
           ∙ +'-suc m n
           ∙ +'-comm (suc m) n

⌣-deloop : (n : ℕ)
  → (Ω (K∙ (suc n)) →∙ Ω (K∙ (n +' (suc n))))
fst (⌣-deloop n) x =
  subst (λ m → fst (Ω (K∙ m))) (+'-suc' n n)
       (EM→ΩEM+1 (n +' n) (cup n n (ΩEM+1→EM n x) (ΩEM+1→EM n x)))
snd (⌣-deloop n) =
  cong (subst (λ m → fst (Ω (K∙ m))) (+'-suc' n n))
       (cong (EM→ΩEM+1 (n +' n))
         (cong (λ x → cup n n x x) (ΩEM+1→EM-refl n) ∙ ⌣ₖ-0ₖ n n (0ₖ n))
         ∙ EM→ΩEM+1-0ₖ (n +' n))
     ∙ lemiSubst' (+'-suc' n n)

fib-deloop : (n : ℕ) → fiber Ω→ (⌣-deloop n)
fib-deloop n =
  Iso.fun (Ω→-fib (⌣-deloop n))
    (EM→Prop _ n (λ _ → asd n (⌣-deloop n) .snd _)
      (0ₖ (n +' suc n)
    , (⌣-deloop n .fst)
    , λ p → →∙Homogeneous≡ (isHomogeneousPath _ _)
             (funExt λ q → {!cong (subst (λ m → fst (Ω (K∙ m))) (+'-suc' n n)) ?!})))

eq' : (n i : ℕ) → (i < n)
  → (K∙ (suc n) →∙ K∙ (i +' (suc n))) ≃ ((Ω (K∙ (suc n)) →∙ Ω (K∙ (i +' (suc n)))))
fst (eq' n i p) = Ω→
snd (eq' zero i p) = ⊥.rec (snotz (+-comm (suc i) (fst p) ∙ snd p))
snd (eq' (suc n) i (x , p)) = record { equiv-proof = gr }
  where
  gr : (g : Ω (K∙ (suc (suc n))) →∙ Ω (K∙ (i +' suc (suc n))))
    → isContr (fiber Ω→ g)
  gr g = main (suc n) 0 g (isConnectedEM (suc (suc n)))
              (subst2 (λ m n → isOfHLevel m (K (i +' suc n)))
                      (cong suc
                        (cong suc
                           (cong (_+ x) (+'≡+ i (suc (x + suc i)))
                          ∙ (sym (+-assoc i (suc (x + suc i)) x)
                          ∙ cong (λ z → i + suc z)
                                 (sym (+-assoc x (suc i) x)
                               ∙ cong (x +_) (cong suc (+-comm i x) ∙ sym (+-suc x i)))
                          ∙ +-suc i (x + (x + suc i))
                          ∙ +-assoc (suc i) x (x + suc i)
                          ∙ cong (_+ (x + suc i))
                               (+-comm (suc i) x))
                          ∙ sym (+'≡+ (x + suc i) (x + suc i)))
                         ∙ (+'-suc (x + suc i) (x + suc i))
                         ∙ +'-comm (suc (x + suc i)) (x + suc i))
                     ∙ cong suc (cong₂ _+'_ p (cong suc p))
                     ∙ cong (suc ∘ suc ∘ suc) (+-comm 0 (n + suc n)))
                      p
                      (isOfHLevelPlus' {n = x} (2 + (i +' suc (x + suc i)))
                        (hLevelEM (Ring→AbGroup ℤ/2Ring) (i +' suc (x + suc i)))))

eq2 : (n i : ℕ)
  → ((Ω (K∙ (suc n)) →∙ Ω (K∙ (i +' (suc n)))))
   ≃ (K∙ n →∙ K∙ (i +' n))
eq2 n i = isoToEquiv (compIso (post∘∙equiv ((isoToEquiv (invIso (Iso-EM-ΩEM+1 n))) , ΩEM+1→EM-refl n))
                       (pre∘∙equiv
                         (compEquiv∙ ((substEquiv (λ x → fst (Ω (K∙ x)))
                           ((+'-comm i (suc n) ∙ sym (+'-suc n i)) ∙ cong suc (+'-comm n i)))
                           , lemiSubst' ((+'-comm i (suc n) ∙ sym (+'-suc n i)) ∙ cong suc (+'-comm n i)))
                       ((isoToEquiv (invIso (Iso-EM-ΩEM+1 (i +' n))))
                       , ΩEM+1→EM-refl (i +' n)))))

eq3 : (n i : ℕ) → (i < n)
  → (K∙ (suc n) →∙ K∙ (i +' (suc n)))
   ≃ (K∙ n →∙ K∙ (i +' n))
eq3 n i p = compEquiv (eq' n i p) (eq2 n i)

SteenR : (n i : ℕ) → (i ≤ n) ⊎ (i > n) → K∙ n →∙ K∙ (i +' n)
SteenR zero zero q = id∙ _
SteenR zero (suc i) q = (λ _ → 0ₖ (suc i)) , refl
SteenR (suc n) zero q = id∙ _
SteenR (suc n) (suc i) (inl (zero , q)) =
    (λ x → subst (λ m → K (m +' suc n)) (sym q)
            (cup (suc n) (suc n) x x))
  , cong (subst (λ m → K (m +' suc n)) (sym q)) (0ₖ-⌣ₖ (suc n) (suc n) (0ₖ (suc n)))
   ∙ lemiSubst _
SteenR (suc n) (suc i) (inl (suc zero , q)) =
    subst (λ m → K∙ (suc n) →∙ K∙ (m +' (suc n))) (sym (cong predℕ q))
      {!!}
SteenR (suc n) (suc i) (inl (suc (suc x) , q)) =
  invEq (eq3 n (suc i) (x , (+-suc x (suc i) ∙ cong predℕ q)))
    (SteenR n (suc i) (inl ((suc x) , (cong predℕ q))))
SteenR (suc n) (suc i) (inr x) = (λ _ → 0ₖ (suc (suc (i + n)))) , refl
