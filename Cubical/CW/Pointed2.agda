{-# OPTIONS --safe --lossy-unification #-}

-- This file contains definition of CW complexes and skeleta.

module Cubical.CW.Pointed2 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin.Inductive.Base
open import Cubical.Data.Sigma
open import Cubical.Data.Sequence
open import Cubical.Data.FinSequence

open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.Susp
open import Cubical.HITs.SequentialColimit
open import Cubical.HITs.SphereBouquet
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.Wedge

open import Cubical.Axiom.Choice

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup

open import Cubical.Relation.Nullary

open import Cubical.CW.Base

open Sequence

open import Cubical.Foundations.Equiv.HalfAdjoint

private
  variable
    ℓ ℓ' ℓ'' : Level

open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

liftFun : ∀ {ℓ ℓ' ℓ'' ℓ'''} {A : Type ℓ} {B : Type ℓ'}
  (f : A → B) → Lift {j = ℓ''} A → Lift {j = ℓ'''} B
liftFun f (lift a) = lift (f a)

module _ {ℓ ℓ' ℓ'' : Level} (ℓ''' : Level)
  {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} (f : A → B) (g : A → C) where
  PushoutLevel  : Level
  PushoutLevel = ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓ'' ℓ'''))

  PushoutLift : Type PushoutLevel
  PushoutLift = Pushout {A = Lift {j = ℓ-max ℓ' (ℓ-max ℓ'' ℓ''')} A}
                        {B = Lift {j = ℓ-max ℓ (ℓ-max ℓ'' ℓ''')} B}
                        {C = Lift {j = ℓ-max ℓ (ℓ-max ℓ' ℓ''')} C}
                        (liftFun f)
                        (liftFun g)

  PushoutLiftIso : Iso (Pushout f g) PushoutLift
  Iso.fun PushoutLiftIso (inl x) = inl (lift x)
  Iso.fun PushoutLiftIso (inr x) = inr (lift x)
  Iso.fun PushoutLiftIso (push a i) = push (lift a) i
  Iso.inv PushoutLiftIso (inl (lift x)) = inl x
  Iso.inv PushoutLiftIso (inr (lift x)) = inr x
  Iso.inv PushoutLiftIso (push (lift a) i) = push a i
  Iso.rightInv PushoutLiftIso (inl (lift x)) = refl
  Iso.rightInv PushoutLiftIso (inr (lift x)) = refl
  Iso.rightInv PushoutLiftIso (push (lift a) i) = refl
  Iso.leftInv PushoutLiftIso (inl x) = refl
  Iso.leftInv PushoutLiftIso (inr x) = refl
  Iso.leftInv PushoutLiftIso (push a i) = refl

open import Cubical.Foundations.Equiv


pushoutIso' : ∀ {ℓA₁ ℓB₁ ℓC₁ ℓA₂ ℓB₂ ℓC₂}
      {A₁ : Type ℓA₁} {B₁ : Type ℓB₁} {C₁ : Type ℓC₁}
      {A₂ : Type ℓA₂} {B₂ : Type ℓB₂} {C₂ : Type ℓC₂}
      (f₁ : A₁ → B₁) (g₁ : A₁ → C₁)
      (f₂ : A₂ → B₂) (g₂ : A₂ → C₂)
      (A≃ : A₁ ≃ A₂) (B≃ : B₁ ≃ B₂) (C≃ : C₁ ≃ C₂)
      (id1 : fst B≃ ∘ f₁ ≡ f₂ ∘ fst A≃)
      (id2 : fst C≃ ∘ g₁ ≡ g₂ ∘ fst A≃) →
      Iso (Pushout f₁ g₁) (Pushout f₂ g₂)
pushoutIso' {ℓA₁ = ℓA₁} {ℓB₁} {ℓC₁} {ℓA₂} {ℓB₂} {ℓC₂}
  f₁ g₁ f₂ g₂ A≃ B≃ C≃ id1 id2 =
    compIso (PushoutLiftIso ℓ* f₁ g₁)
      (compIso (pushoutIso _ _ _ _
        (Lift≃Lift A≃)
        (Lift≃Lift B≃)
        (Lift≃Lift C≃)
        (funExt (λ { (lift x) → cong lift (funExt⁻ id1 x)}))
        (funExt (λ { (lift x) → cong lift (funExt⁻ id2 x)})))
      (invIso (PushoutLiftIso ℓ* f₂ g₂)))
  where
  ℓ* = ℓ-max ℓA₁ (ℓ-max ℓA₂ (ℓ-max ℓB₁ (ℓ-max ℓB₂ (ℓ-max ℓC₁ ℓC₂)))) 


module _ {C : Type ℓ} {B : Type ℓ'} where
  PushoutAlongEquiv→ : {A : Type ℓ}
    (e : A ≃ C) (f : A → B) → Pushout (fst e) f → B
  PushoutAlongEquiv→ e f (inl x) = f (invEq e x)
  PushoutAlongEquiv→ e f (inr x) = x
  PushoutAlongEquiv→ e f (push a i) = f (retEq e a i)

  private
    PushoutAlongEquiv→Cancel : {A : Type ℓ} (e : A ≃ C) (f : A → B)
      → retract (PushoutAlongEquiv→ e f) inr
    PushoutAlongEquiv→Cancel =
      EquivJ (λ A e → (f : A → B)
                    → retract (PushoutAlongEquiv→ e f) inr)
            λ f → λ { (inl x) → sym (push x)
                      ; (inr x) → refl
                      ; (push a i) j → push a (~ j ∨ i)}

  PushoutAlongEquiv : {A : Type ℓ} (e : A ≃ C) (f : A → B)
    → Iso (Pushout (fst e) f) B
  Iso.fun (PushoutAlongEquiv e f) = PushoutAlongEquiv→ e f
  Iso.inv (PushoutAlongEquiv e f) = inr
  Iso.rightInv (PushoutAlongEquiv e f) x = refl
  Iso.leftInv (PushoutAlongEquiv e f) = PushoutAlongEquiv→Cancel e f


--- CW complexes ---
-- Definition of (the skeleton) of an arbitrary CW complex
-- New def: X 0 is empty and C (suc n) is pushout

open import Cubical.HITs.Pushout
module _ {ℓA ℓB ℓC : Level} {A : Type ℓA} {B : A → Pointed ℓB} (C : Pointed ℓC)
         (f : (⋁gen A B , inl tt) →∙ C) where

  private
    open 3x3-span
    inst : 3x3-span
    A00 inst = A
    A02 inst = Σ A (fst ∘ B)
    A04 inst = Σ A (fst ∘ B)
    A20 inst = A
    A22 inst = A
    A24 inst = Σ A (fst ∘ B)
    A40 inst = Unit
    A42 inst = Unit
    A44 inst = fst C
    f10 inst = idfun A
    f12 inst = λ x → x , snd (B x)
    f14 inst = idfun _
    f30 inst = λ _ → tt
    f32 inst = λ _ → tt
    f34 inst = fst f ∘ inr
    f01 inst = fst
    f21 inst = idfun A
    f41 inst = λ _ → tt
    f03 inst = idfun _
    f23 inst = λ x → x , snd (B x)
    f43 inst = λ _ → pt C
    H11 inst = λ _ → refl
    H13 inst = λ _ → refl
    H31 inst = λ _ → refl
    H33 inst = λ x → sym (snd f) ∙ cong (fst f) (push x)

  A0□Iso : Iso (A0□ inst) A
  A0□Iso = compIso (equivToIso (symPushout _ _))
                   (PushoutAlongEquiv (idEquiv _) fst)

  A2□Iso : Iso (A2□ inst) (Σ A (fst ∘ B))
  A2□Iso = PushoutAlongEquiv (idEquiv A) _

  A4□Iso : Iso (A4□ inst) (fst C)
  A4□Iso = PushoutAlongEquiv (idEquiv Unit) λ _ → pt C

  A○□Iso : Iso (A○□ inst) (Pushout (fst f ∘ inr) fst)
  A○□Iso = compIso (equivToIso (symPushout _ _))
                   (invIso (pushoutIso' _ _ _ _
                     (isoToEquiv (invIso A2□Iso))
                     (isoToEquiv (invIso A4□Iso))
                     (isoToEquiv (invIso A0□Iso))
                     refl
                     λ i x → push x i))
  
  

  A□0Iso : Iso (A□0 inst) Unit
  A□0Iso = isContr→Iso
    (inr tt , λ { (inl x) → sym (push x)
                ; (inr x) → refl
                ; (push a i) j → push a (i ∨ ~ j)})
    (tt , (λ _ → refl))

  A□2Iso : Iso (A□2 inst) (⋁gen A B)
  A□2Iso = equivToIso (symPushout _ _)


  A□4Iso : Iso (A□4 inst) (fst C)
  A□4Iso = PushoutAlongEquiv (idEquiv _) _

  open import Cubical.Foundations.GroupoidLaws
  A□○Iso : Iso (A□○ inst) (cofib (fst f))
  A□○Iso = invIso (pushoutIso' _ _ _ _
    (isoToEquiv (invIso A□2Iso))
    (isoToEquiv (invIso A□0Iso))
    (isoToEquiv (invIso A□4Iso))
    (funExt (λ { (inl x) → refl
                ; (inr x) → sym (push (fst x)) ∙ refl
                ; (push a i) j → (sym (push a) ∙ refl) (i ∧ j)}))
    (funExt λ { (inl x) i → inr (snd f i)
              ; (inr x) → sym (push x)
              ; (push a i) j
              → hcomp (λ k
              → (λ {(i = i0) → inr (compPath-filler' (sym (snd f))
                                      (cong (fst f) (push a)) j (~ k))
                   ; (i = i1) → push (a , snd (B a)) (~ j)
                   ; (j = i0) → inr (fst f (push a (~ k ∨ i)))}))
        (push (a , snd (B a)) (~ i ∨ ~ j))}))

  ⋁-cofib-Iso : Iso (Pushout (fst f ∘ inr) fst) (cofib (fst f))
  ⋁-cofib-Iso = compIso (compIso (invIso A○□Iso)
                                  (invIso (3x3-Iso inst)))
                                  A□○Iso



-- connected comp
open import Cubical.Homotopy.Connected
open import Cubical.CW.Properties
open import Cubical.HITs.Truncation as TR
open import Cubical.Foundations.HLevels

isConnectedCW→isConnectedSkel : (C : CWskel ℓ)
  → isConnected 2 (realise C)
  → (n : ℕ)
  → isConnected 2 (C .fst (suc (suc n)))
isConnectedCW→isConnectedSkel C c n =
  TR.rec (isOfHLevelSuc 1 isPropIsContr)
         (λ ⋆ → TR.rec (isProp→isOfHLevelSuc (suc n) isPropIsContr)
           (λ {(x , p) → ∣ x ∣
            , (TR.elim (λ _ → isOfHLevelPath 2 (isOfHLevelTrunc 2) _ _)
                (λ a → Iso.inv (PathIdTruncIso 1)
                  (TR.rec (isOfHLevelTrunc 1)
                    (λ q →
                      TR.rec (isOfHLevelPlus' 1 (isOfHLevelTrunc 1))
                    (∣_∣ₕ ∘ fst)
                    (isConnectedCong (suc n) _ (isConnected-CW↪∞  (suc (suc n)) C)
                       q .fst))
                    (Iso.fun (PathIdTruncIso 1)
                      (sym (c .snd ∣ incl x ∣) ∙ c .snd ∣ incl a ∣)))))})
           (isConnected-CW↪∞  (suc (suc n)) C ⋆ .fst))
         (c .fst)

open import Cubical.Data.Bool
open import Cubical.Data.Nat.Order.Inductive
-- open import Cubical.Data.Dec

open import Cubical.Relation.Nullary.Base
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Empty as ⊥

open import Cubical.Data.Fin.Inductive.Properties as Ind

FinSuc : {n : ℕ} → Iso (Fin 1 ⊎ Fin n) (Fin (suc n))
Iso.fun (FinSuc {n = n}) = ⊎.rec (λ _ → flast) injectSuc
Iso.inv (FinSuc {n = n}) = Ind.elimFin (inl flast) inr
Iso.rightInv (FinSuc {n = n}) =
  Ind.elimFin (cong (⊎.rec (λ _ → flast) injectSuc)
                 (Ind.elimFinβ (inl flast) inr .fst))
              λ x → cong (⊎.rec (λ _ → flast) injectSuc)
                      (Ind.elimFinβ (inl flast) inr .snd x)
Iso.leftInv (FinSuc {n = n}) (inl (zero , p)) =
  Ind.elimFinβ (inl flast) inr .fst
Iso.leftInv (FinSuc {n = n}) (inr x) = Ind.elimFinβ (inl flast) inr .snd x

Fin+ : {n m : ℕ} → Iso (Fin n ⊎ Fin m) (Fin (n +ℕ m))
Iso.fun (Fin+ {n = zero} {m = m}) (inr x) = x
Iso.inv (Fin+ {n = zero} {m = m}) x = inr x
Iso.rightInv (Fin+ {n = zero} {m = m}) x = refl
Iso.leftInv (Fin+ {n = zero} {m = m}) (inr x) = refl
Fin+ {n = suc n} {m = m} =
  compIso (⊎Iso (invIso FinSuc) idIso)
    (compIso ⊎-assoc-Iso
      (compIso (⊎Iso idIso (Fin+ {n = n} {m = m}))
        FinSuc))

Iso-Unit-Fin : Iso Unit (Fin 1)
Iso.fun Iso-Unit-Fin tt = fzero
Iso.inv Iso-Unit-Fin (x , p) = tt
Iso.rightInv Iso-Unit-Fin (zero , p) = Σ≡Prop (λ _ → isProp<ᵗ) refl
Iso.leftInv Iso-Unit-Fin x = refl

Iso-Bool-Fin : Iso (S₊ 0) (Fin 2)
Iso.fun Iso-Bool-Fin false = flast
Iso.fun Iso-Bool-Fin true = fzero
Iso.inv Iso-Bool-Fin (zero , p) = true
Iso.inv Iso-Bool-Fin (suc x , p) = false
Iso.rightInv Iso-Bool-Fin (zero , p) = refl
Iso.rightInv Iso-Bool-Fin (suc zero , p) =
  Σ≡Prop (λ _ → isProp<ᵗ) refl
Iso.leftInv Iso-Bool-Fin false = refl
Iso.leftInv Iso-Bool-Fin true = refl

Fin× : {n m : ℕ} → Iso (Fin n × Fin m) (Fin (n · m))
Fin× {n = zero} {m = m} =
  iso (λ {()}) (λ{()}) (λ{()}) (λ{()})
Fin× {n = suc n} {m = m} =
  compIso
    (compIso
      (compIso (Σ-cong-iso-fst (invIso FinSuc))
        (compIso Σ-swap-Iso
          (compIso ×DistR⊎Iso
            (⊎Iso (compIso
              (Σ-cong-iso-snd (λ _ → invIso Iso-Unit-Fin)) rUnit×Iso)
              Σ-swap-Iso))))
      (⊎Iso idIso Fin×))
    (Fin+ {n = m} {n · m})

DiscreteFin : ∀ {n} → Discrete (Fin n)
DiscreteFin x y with discreteℕ (fst x) (fst y)
... | yes p = yes (Σ≡Prop (λ _ → isProp<ᵗ) p)
... | no ¬p = no λ q → ¬p (cong fst q)


decIm : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) → Type (ℓ-max ℓ ℓ')
decIm {A = A} {B = B} f =
  (y : B) → (Σ[ x ∈ A ] f x ≡ y)
          ⊎ ((x : A) → ¬ f x ≡ y)

decImFin : ∀ {ℓ} {A : Type ℓ}
  (da : Discrete A) (n : ℕ) (f : Fin n → A)
  → decIm f
decImFin {A = A} da zero f y = inr λ x → ⊥.rec (¬Fin0 x)
decImFin {A = A} da (suc n) f y with da (f fzero) y
... | yes p = inl (fzero , p)
... | no ¬p with (decImFin da n (f ∘ fsuc) y)
... | inl q = inl ((fsuc (fst q)) , snd q)
... | inr q = inr (Ind.elimFin-alt ¬p q)

Bool×Fin≡Fin : {n : ℕ} → Iso (Fin n × S₊ 0) (Fin (2 · n))
Bool×Fin≡Fin =
  compIso (compIso Σ-swap-Iso
    (Σ-cong-iso-fst Iso-Bool-Fin)) (Fin× {n = 2})

decIm-S⁰×Fin : ∀ {ℓ} {A : Type ℓ}
  (da : Discrete A) (n : ℕ) (f : Fin n × S₊ 0 → A) → decIm f
decIm-S⁰×Fin {A = A} da n =
  subst (λ C → (f : C → A) → decIm f)
        (isoToPath (invIso Bool×Fin≡Fin))
        (decImFin da _)


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


pickDifferentFin : {n : ℕ} (x : Fin (suc (suc n))) → Σ[ y ∈ Fin (suc (suc n)) ] ¬ x ≡ y
pickDifferentFin (zero , p) = (1 , p) , λ q → snotz (sym (cong fst q))
pickDifferentFin (suc x , p) = fzero , λ q → snotz (cong fst q)

allConst? : ∀ {ℓ} {A : Type ℓ} {n : ℕ} (dis : Discrete A)
  → (t : Fin n → S₊ 0 → A)
  → ((x : Fin n) → t x ≡ λ _ → t x true)
   ⊎ (Σ[ x ∈ Fin n ] ¬ (t x true ≡ t x false))
allConst? {n = zero} dis t = inl λ {()}
allConst? {n = suc n} dis t
  with (dis (t fzero true) (t fzero false))
     | (allConst? {n = n} dis λ x p → t (fsuc x) p)
... | yes p | inl x =
  inl (Ind.elimFin-alt (funExt
        (λ { false → sym p ; true → refl})) x)
... | yes p | inr x = inr (_ , (snd x))
... | no ¬p | q = inr (_ , ¬p)


isSurj-α₀ : (n m : ℕ) (f : Fin n × S₊ 0 → Fin (suc (suc m)))
  → isConnected 2 (Pushout f fst)
  → (y : _) → Σ[ x ∈ _ ] f x ≡ y
isSurj-α₀ n m f c y with (decIm-S⁰×Fin DiscreteFin n f y)
... | inl x = x
isSurj-α₀ n m f c x₀ | inr q = ⊥.rec nope
  where
  pre-help : Fin (suc (suc m)) → Type
  pre-help = elimFinChoose x₀ ⊥ λ _ _ → Unit

  lem : (fa : _) (a : _) → f a ≡ fa → pre-help fa ≡ Unit
  lem = elimFinChoose x₀
        (λ s t → ⊥.rec (q _ t))
         λ s t b c → elimFinChooseβ x₀ ⊥ (λ _ _ → Unit) .snd s t

  help : Pushout f fst → Type
  help (inl x) = pre-help x
  help (inr x) = Unit
  help (push a i) = lem (f a) a refl i

  nope : ⊥
  nope = TR.rec isProp⊥
            (λ q → transport (elimFinChooseβ x₀ ⊥ (λ _ _ → Unit) .fst)
                     (subst help (sym q)
                       (transport (sym (elimFinChooseβ x₀ ⊥
                         (λ _ _ → Unit) .snd _
                           (pickDifferentFin x₀ .snd ∘ sym))) tt)))
            (Iso.fun (PathIdTruncIso 1)
              (isContr→isProp c
               ∣ inl x₀ ∣
               ∣ inl (pickDifferentFin x₀ .fst) ∣))

notAllLoops-α₀ : (n m : ℕ) (f : Fin n × S₊ 0 → Fin (suc (suc m)))
  → isConnected 2 (Pushout f fst)
  → Σ[ x ∈ Fin n ] (¬ f (x , true) ≡ f (x , false))
notAllLoops-α₀ n m f c with (allConst? DiscreteFin (λ x y → f (x , y)))
... | inr x = x
notAllLoops-α₀ n m f c | inl q =
  ⊥.rec (TR.rec isProp⊥ (λ p → subst T p tt)
           (Iso.fun(PathIdTruncIso 1)
             (isContr→isProp c
               ∣ inl flast ∣ ∣ inl fzero ∣)))
  where
  inrT : Fin n → Type
  inrT x with (DiscreteFin (f (x , true)) fzero)
  ... | yes p = ⊥
  ... | no ¬p = Unit

  inlT : Fin (suc (suc m)) → Type
  inlT (zero , p) = ⊥
  inlT (suc x , p) = Unit

  inlrT-pre : (a : _) → inlT (f (a , true)) ≡ inrT a
  inlrT-pre a with ((DiscreteFin (f (a , true)) fzero))
  ... | yes p = cong inlT p
  inlrT-pre s | no ¬p with (f (s , true))
  ... | zero , tt = ⊥.rec (¬p refl)
  ... | suc q , t = refl

  inlrT : (a : _) → inlT (f a) ≡ inrT (fst a)
  inlrT (b , false) = cong inlT (funExt⁻ (q b) false) ∙ inlrT-pre b
  inlrT (b , true) = inlrT-pre b

  T : Pushout f fst → Type
  T (inl x) = inlT x
  T (inr x) = inrT x
  T (push a i) = inlrT a i

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

  -- swapFinSwap : (x y z : Fin n) → swapFin x y z ≡ swapFin y x z
  -- swapFinSwap x y z with (discreteℕ (fst z) (fst x)) | discreteℕ (fst z) (fst y)
  -- ... | yes p | yes p₁ = Σ≡Prop (λ _ → isProp<ᵗ) (sym p₁ ∙ p)
  -- ... | yes p | no ¬p = {!help!}
  --   where
  --   help : y ≡ swapFin y x z
  --   help = {!!}
  -- ... | no ¬p | q = {!!}

  swapFin² : (x y z : Fin n) → swapFin x y (swapFin x y z) ≡ z
  swapFin² (x , xp) (y , yp) (z , zp) with discreteℕ z x | discreteℕ z y
  ... | yes p | yes p₁ = silly
    where
    silly : swapFin (x , xp) (y , yp) (z , zp) ≡ (z , zp)
    silly with discreteℕ z x | discreteℕ z y
    ... | yes p | yes p₁ = refl
    ... | yes p | no ¬p = ⊥.rec (¬p p₁)
    ... | no ¬p | r = ⊥.rec (¬p p)
  ... | yes p | no ¬q = silly
    where
    silly : swapFin (x , xp) (y , yp) (y , yp) ≡ (z , zp)
    silly with discreteℕ y x | discreteℕ y y
    ... | yes p' | yes p₁ = Σ≡Prop (λ _ → isProp<ᵗ) (p' ∙ sym p)
    ... | no ¬p | yes p₁ = Σ≡Prop (λ _ → isProp<ᵗ)  (sym p)
    ... | p | no ¬p = ⊥.rec (¬p refl)
  ... | no ¬p | yes p = silly
    where
    silly : swapFin (x , xp) (y , yp) (x , xp) ≡ (z , zp)
    silly with discreteℕ x y | discreteℕ x x
    ... | yes p₁ | yes _ = Σ≡Prop (λ _ → isProp<ᵗ) (p₁ ∙ sym p)
    ... | no ¬p | yes _ = Σ≡Prop (λ _ → isProp<ᵗ)  (sym p)
    ... | s | no ¬p = ⊥.rec (¬p refl)
  ... | no ¬p | no ¬q = silly
    where
    silly : swapFin (x , xp) (y , yp) (z , zp) ≡ (z , zp)
    silly with discreteℕ z x | discreteℕ z y
    ... | yes p | yes p₁ = refl
    ... | yes p | no ¬b = ⊥.rec (¬p p)
    ... | no ¬a | yes b = ⊥.rec (¬q b)
    ... | no ¬a | no ¬b = refl

  swapFinIso : (x y : Fin n) → Iso (Fin n) (Fin n)
  Iso.fun (swapFinIso x y) = swapFin x y
  Iso.inv (swapFinIso x y) = swapFin x y
  Iso.rightInv (swapFinIso x y) = swapFin² x y
  Iso.leftInv (swapFinIso x y) = swapFin² x y




PushoutPostcompEquivIso : ∀ {ℓ ℓ' ℓ'' ℓ'''}
  {A : Type ℓ} {B : Type ℓ'} {B' : Type ℓ''} {C : Type ℓ'''}
  (e2 : B' ≃ B)
  (f : A → B') (g : A → C)
  → Iso (Pushout (fst e2 ∘ f) g) (Pushout f g)
PushoutPostcompEquivIso {ℓ = ℓ} {ℓ'} {ℓ''} {ℓ'''}
  {A = A} {B} {B'} {C} e2 f g =
  compIso (PushoutLiftIso ℓ* _ _)
    (compIso (pushoutIso _ _ _ _ (idEquiv _)
      (compEquiv (invEquiv LiftEquiv)
        (compEquiv (invEquiv e2) LiftEquiv))
        (idEquiv _)
        (funExt (λ { (lift l) → cong lift (retEq e2 (f l))}))
        refl)
      (invIso (PushoutLiftIso ℓ* _ _)))
  where
  ℓ* = ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓ'' ℓ'''))

Pushout∘Equiv : ∀ {ℓ ℓ' ℓ''} {A A' : Type ℓ} {B B' : Type ℓ'} {C : Type ℓ''}
  (e1 : A ≃ A') (e2 : B' ≃ B)
  (f : A' → B') (g : A → C)
  → Iso (Pushout (fst e2 ∘ f ∘ fst e1) g) (Pushout f (g ∘ invEq e1))
Pushout∘Equiv {A = A} {A' = A'} {B} {B'} {C} =
  EquivJ (λ A e1 → (e2 : B' ≃ B) (f : A' → B') (g : A → C)
                 →  Iso (Pushout (fst e2 ∘ f ∘ fst e1) g)
                         (Pushout f (g ∘ invEq e1)))
   (EquivJ (λ B' e2 → (f : A' → B') (g : A' → C)
                 →  Iso (Pushout (fst e2 ∘ f) g)
                         (Pushout f g))
     λ f g → idIso)

module _ {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'}
  (f : A × Bool → Unit ⊎ B) (b₀ : B) where

  F : (Unit ⊎ A) × Bool → Unit ⊎ B
  F (inl tt , false) = inl tt
  F (inl tt , true) = inr b₀
  F (inr a , x) = f (a , x)

  g : Unit ⊎ B → B
  g (inl x) = b₀
  g (inr x) = x

  PF→P∘ₗ : (x : Unit ⊎ A) → Pushout (g ∘ f) fst
  PF→P∘ₗ (inl x) = inl b₀
  PF→P∘ₗ (inr x) = inr x

  theCoh : (a : _) → inl (g (F a)) ≡ PF→P∘ₗ (fst a)
  theCoh (inl x , false) = refl
  theCoh (inl x , true) = refl
  theCoh (inr x , false) = push (x , false)
  theCoh (inr x , true) = push (x , true)

  PF→P∘' : Pushout F fst → Pushout (g ∘ f) fst
  PF→P∘' (inl x) = inl (g x)
  PF→P∘' (inr x) = PF→P∘ₗ x
  PF→P∘' (push a i) = theCoh a i

  theCoh2 : (a : _) (b : _)
    → Path (Pushout F fst) (inl (inr (g (f (a , b))))) (inl (f (a , b)))
  theCoh2 a b with (f (a , b))
  theCoh2 a b | inl x = (push (inl tt , true)) ∙ sym (push (inl tt , false))
  ... | inr x = refl

  P∘'→PF : Pushout (g ∘ f) fst → Pushout F fst
  P∘'→PF (inl x) = inl (inr x)
  P∘'→PF (inr x) = inr (inr x)
  P∘'→PF (push (a , false) i) = (theCoh2 a false ∙ push (inr a , false)) i
  P∘'→PF (push (a , true) i) = (theCoh2 a true ∙ push (inr a , true)) i

  PFpushTₗ : (x : _) → P∘'→PF (PF→P∘' (inl x)) ≡ (inl x)
  PFpushTₗ (inl x) = push (inl tt , true) ∙ sym (push (inl tt , false))
  PFpushTₗ (inr x) = refl

  PFpushTᵣ : (x : _) → P∘'→PF (PF→P∘' (inr x)) ≡ (inr x)
  PFpushTᵣ (inl x) = push (inl tt , true)
  PFpushTᵣ (inr x) = refl

  pp1 : (x : A) → PFpushTₗ (f (x , false)) ≡ theCoh2 x false
  pp1 x with (f (x , false))
  ... | inl x₁ = refl
  ... | inr x₁ = refl

  pp2 : (x : A) → PFpushTₗ (f (x , true)) ≡ theCoh2 x true
  pp2 x with (f (x , true))
  ... | inl x₁ = refl
  ... | inr x₁ = refl

  open import Cubical.Foundations.Path
  open import Cubical.Foundations.GroupoidLaws
  

  PFpushT : (x : _) → P∘'→PF (PF→P∘' x) ≡ x 
  PFpushT (inl x) = PFpushTₗ x
  PFpushT (inr x) = PFpushTᵣ x
  PFpushT (push (inl x , false) i) j =
    compPath-filler (push (inl tt , true)) (sym (push (inl tt , false))) (~ i) j
  PFpushT (push (inr x , false) i) j =
    (pp1 x
    ◁ flipSquare
       (symP (compPath-filler'
         (theCoh2 x false) (push (inr x , false))))) i j
  PFpushT (push (inl x , true) i) j = push (inl x , true) (i ∧ j)
  PFpushT (push (inr x , true) i) j =
    (pp2 x
    ◁ flipSquare
       (symP (compPath-filler'
         (theCoh2 x true) (push (inr x , true))))) i j

  cong-PF→P∘' : (b : _) (a : _) → cong PF→P∘' (theCoh2 b a) ≡ refl
  cong-PF→P∘' b a with (f (b , a))
  ... | inl x = cong-∙ PF→P∘' (push (inl tt , true)) (sym (push (inl tt , false)))
              ∙ sym (rUnit refl)
  ... | inr x = refl

  PF→P∘'→PF : (x : _) → PF→P∘' (P∘'→PF x) ≡ x
  PF→P∘'→PF (inl x) = refl
  PF→P∘'→PF (inr x) = refl
  PF→P∘'→PF (push (b , false) i) j =
    (cong-∙ PF→P∘' (theCoh2 b false) (push (inr b , false))
    ∙ cong (_∙ push (b , false)) (cong-PF→P∘' b false)
    ∙ sym (lUnit _)) j i
  PF→P∘'→PF (push (b , true) i) j =
    (cong-∙ PF→P∘' (theCoh2 b true) (push (inr b , true))
    ∙ cong (_∙ push (b , true)) (cong-PF→P∘' b true)
    ∙ sym (lUnit _)) j i

  Is1 : Iso (Pushout F fst) (Pushout (g ∘ f) fst)
  Iso.fun Is1 = PF→P∘'
  Iso.inv Is1 = P∘'→PF
  Iso.rightInv Is1 = PF→P∘'→PF
  Iso.leftInv Is1 = PFpushT

FinPred : ∀ {m} → Fin (suc (suc m)) → Fin (suc m)
FinPred {m = m} (zero , p) = zero , p
FinPred {m = m} (suc x , p) = x , p

fone : ∀ {m} → Fin (suc (suc m))
fone {m} = suc zero , tt

module _ {m : ℕ} where
  Fin→Unit⊎Fin : (x : Fin (suc m)) → Unit ⊎ Fin m
  Fin→Unit⊎Fin = Ind.elimFin (inl tt) inr

  Unit⊎Fin→Fin : Unit ⊎ Fin m → Fin (suc m)
  Unit⊎Fin→Fin (inl x) = flast
  Unit⊎Fin→Fin (inr x) = injectSuc x

  Iso-Fin-Unit⊎Fin : Iso (Fin (suc m)) (Unit ⊎ Fin m)
  Iso.fun Iso-Fin-Unit⊎Fin = Fin→Unit⊎Fin
  Iso.inv Iso-Fin-Unit⊎Fin = Unit⊎Fin→Fin
  Iso.rightInv Iso-Fin-Unit⊎Fin (inl x) = Ind.elimFinβ (inl tt) inr .fst
  Iso.rightInv Iso-Fin-Unit⊎Fin (inr x) = Ind.elimFinβ (inl tt) inr .snd x
  Iso.leftInv Iso-Fin-Unit⊎Fin =
    Ind.elimFin
      (cong Unit⊎Fin→Fin (Ind.elimFinβ (inl tt) inr .fst))
      λ x → (cong Unit⊎Fin→Fin (Ind.elimFinβ (inl tt) inr .snd x))


≠flast→<ᵗflast : {n : ℕ} → (x : Fin (suc n)) → ¬ x ≡ flast → fst x <ᵗ n
≠flast→<ᵗflast = Ind.elimFin (λ p → ⊥.rec (p refl)) λ p _ → snd p

CW₁DataPre : (n m : ℕ) (f : Fin (suc (suc n)) × S₊ 0 → Fin (suc (suc m)))
  → f (flast , false) ≡ flast
  → (t : f (flast , true) .fst <ᵗ suc m)
  → Σ[ k ∈ ℕ ] Σ[ f' ∈ (Fin k × S₊ 0 → Fin (suc m)) ]
       Iso (Pushout f fst)
           (Pushout f' fst)
CW₁DataPre n m f p q = (suc n)
  , _
  , compIso (invIso (pushoutIso _ _ _ _
              (isoToEquiv (Σ-cong-iso-fst (invIso Iso-Fin-Unit⊎Fin)))
              (isoToEquiv (invIso Iso-Fin-Unit⊎Fin))
              (isoToEquiv (invIso Iso-Fin-Unit⊎Fin))
              (funExt (uncurry help))
              (funExt λ x → refl)))
     (Is1 {A = Fin (suc n)} {B = Fin (suc m)}
               (λ x → Fin→Unit⊎Fin (f ((injectSuc (fst x)) , (snd x))))
               (f (flast , true) .fst , q))
  where
  help : (y : Unit ⊎ Fin (suc n)) (x : Bool)
    → Unit⊎Fin→Fin
         (F (λ x₁ → Ind.elimFin (inl tt) inr (f (injectSuc (fst x₁) , snd x₁)))
         (f (flast , true) .fst , q) (y , x))
     ≡ f (Unit⊎Fin→Fin y , x)
  help (inl a) false = sym p
  help (inl b) true = Σ≡Prop (λ _ → isProp<ᵗ) refl
  help (inr a) false = Iso.leftInv Iso-Fin-Unit⊎Fin _
  help (inr a) true = Iso.leftInv Iso-Fin-Unit⊎Fin _

isPropFin1 : isProp (Fin 1)
isPropFin1 (zero , tt) (zero , tt) = refl

Iso⊎→Iso : ∀ {ℓ'''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {D : Type ℓ'''}
  → (f : Iso A C)
  → (e : Iso (A ⊎ B) (C ⊎ D))
   → ((a : A) → Iso.fun e (inl a) ≡ inl (Iso.fun f a))
   → Iso B D
Iso⊎→Iso {A = A} {B} {C} {D} f e p = Iso'
  where
  ⊥-fib : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → A ⊎ B → Type
  ⊥-fib (inl x) = ⊥
  ⊥-fib (inr x) = Unit

  module _ {ℓ ℓ' ℓ'' ℓ''' : Level}
         {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {D : Type ℓ'''}
         (f : Iso A C)
         (e : Iso (A ⊎ B) (C ⊎ D))
         (p : (a : A) → Iso.fun e (inl a) ≡ inl (Iso.fun f a)) where
    T : (b : B) → Type _
    T b = Σ[ d' ∈ C ⊎ D ] (Iso.fun e (inr b) ≡ d')

    T-elim : ∀ {ℓ} (b : B) {P : (x : T b) → Type ℓ}
           → ((d : D) (s : _) → P (inr d , s))
           → (x : _) → P x
    T-elim b ind (inl x , q) =
      ⊥.rec (subst ⊥-fib (sym (sym (Iso.leftInv e _)
          ∙ cong (Iso.inv e)
             (p _ ∙ cong inl (Iso.rightInv f x) ∙ sym q)
          ∙ Iso.leftInv e _)) tt)
    T-elim b ind (inr x , y) = ind x y

  e-pres-inr-help : (b : B) → T f e p b  → D
  e-pres-inr-help b = T-elim f e p b λ d _ → d

  p' : (a : C) → Iso.inv e (inl a) ≡ inl (Iso.inv f a)
  p' c = cong (Iso.inv e ∘ inl) (sym (Iso.rightInv f c))
      ∙∙ cong (Iso.inv e) (sym (p (Iso.inv f c)))
      ∙∙ Iso.leftInv e _

  e⁻-pres-inr-help : (d : D) → T (invIso f) (invIso e) p' d → B
  e⁻-pres-inr-help d = T-elim (invIso f) (invIso e) p' d λ b _ → b

  e-pres-inr : B → D
  e-pres-inr b = e-pres-inr-help b (_ , refl)

  e⁻-pres-inr : D → B
  e⁻-pres-inr d = e⁻-pres-inr-help d (_ , refl)

  lem1 : (b : B) (e : T f e p b) (d : _)
    → e⁻-pres-inr-help (e-pres-inr-help b e) d ≡ b
  lem1 b = T-elim f e p b λ d s
    → T-elim (invIso f) (invIso e) p' _
      λ b' s' → invEq (_ , isEmbedding-inr _ _)
        (sym s' ∙ cong (Iso.inv e) (sym s) ∙ Iso.leftInv e _)

  lem2 : (d : D) (e : T (invIso f) (invIso e) p' d ) (t : _)
    → e-pres-inr-help (e⁻-pres-inr-help d e) t ≡ d
  lem2 d = T-elim (invIso f) (invIso e) p' d
    λ b s → T-elim f e p _ λ d' s'
    → invEq (_ , isEmbedding-inr _ _)
         (sym s' ∙ cong (Iso.fun e) (sym s) ∙ Iso.rightInv e _)

  Iso' : Iso B D
  Iso.fun Iso' = e-pres-inr
  Iso.inv Iso' = e⁻-pres-inr
  Iso.rightInv Iso' x = lem2 x _ _
  Iso.leftInv Iso' x = lem1 x _ _

Fin≠Fin : {n m : ℕ} → ¬ (n ≡ m) → ¬ (Iso (Fin n) (Fin m))
Fin≠Fin {n = zero} {m = zero} p = ⊥.rec (p refl)
Fin≠Fin {n = zero} {m = suc m} p q = Iso.inv q fzero .snd
Fin≠Fin {n = suc n} {m = zero} p q = Iso.fun q fzero .snd
Fin≠Fin {n = suc n} {m = suc m} p q =
  Fin≠Fin {n = n} {m = m} (p ∘ cong suc)
    (Iso⊎→Iso idIso help λ {(zero , tt)
      → cong (Iso.inv FinSuc) (swapFinβₗ (Iso.fun q flast) flast)
       ∙ Ind.elimFinβ (inl flast) inr .fst})
  where
  q^ : Iso (Fin (suc n)) (Fin (suc m))
  q^ = compIso q (swapFinIso (Iso.fun q flast) flast)

  help : Iso (Fin 1 ⊎ Fin n) (Fin 1 ⊎ Fin m)
  help = compIso FinSuc (compIso q^ (invIso FinSuc))

CW₁Data₁ : (m : ℕ) (f : Fin 1 × S₊ 0 → Fin (suc (suc m)))
  → isConnected 2 (Pushout f fst)
  → Iso (Fin 1 × S₊ 0) (Fin (suc (suc m)))
CW₁Data₁ m f c = mainIso -- mainIso
  where
  f' : Bool → Fin (suc (suc m))
  f' = f ∘ (fzero ,_)

  f'-surj : (x : _) → Σ[ t ∈ Bool ] (f' t ≡ x)
  f'-surj x =
    isSurj-α₀ (suc zero) m f c x .fst .snd
    , cong f (ΣPathP (isPropFin1 _ _ , refl)) ∙ isSurj-α₀ (suc zero) m f c x .snd
  f-true≠f-false : (x : _) → f' true ≡ x →  ¬ f' true ≡ f' false
  f-true≠f-false (zero , q) p r = lem (f'-surj fone)
    where
    lem : Σ[ t ∈ Bool ] (f' t ≡ fone) → ⊥
    lem (false , s) = snotz (cong fst (sym s ∙ sym r ∙ p))
    lem (true , s) = snotz (cong fst (sym s ∙ p))
  f-true≠f-false (suc x , q) p r = lem (f'-surj fzero)
    where
    lem : Σ[ t ∈ Bool ] (f' t ≡ fzero) → ⊥
    lem (false , s) = snotz (cong fst (sym p ∙ r ∙ s))
    lem (true , s) = snotz (cong fst (sym p ∙ s))

  f-inj : (x y : _) → f x ≡ f y → x ≡ y
  f-inj ((zero , tt) , false) ((zero , tt) , false) p = refl
  f-inj ((zero , tt) , false) ((zero , tt) , true) p = ⊥.rec (f-true≠f-false _ refl (sym p))
  f-inj ((zero , tt) , true) ((zero , tt) , false) p = ⊥.rec (f-true≠f-false _ refl p)
  f-inj ((zero , tt) , true) ((zero , tt) , true) p = refl

  mainIso : Iso (Fin 1 × S₊ 0) (Fin (suc (suc m)))
  Iso.fun mainIso = f
  Iso.inv mainIso x = isSurj-α₀ (suc zero) m f c x .fst
  Iso.rightInv mainIso x = isSurj-α₀ 1 m f c x .snd
  Iso.leftInv mainIso ((zero , tt) , x) =
   (f-inj _ _ (isSurj-α₀ 1 m f c (f (fzero , x)) .snd))

CW₁Data : (n m : ℕ) (f : Fin n × S₊ 0 → Fin (suc (suc m)))
  → isConnected 2 (Pushout f fst)
  → Σ[ k ∈ ℕ ] Σ[ f' ∈ (Fin k × S₊ 0 → Fin (suc m)) ]
       Iso (Pushout f fst)
           (Pushout f' fst)
CW₁Data zero m f c = ⊥.rec (snd (notAllLoops-α₀ zero m f c .fst))
CW₁Data (suc zero) zero f c = 0 , ((λ ()) , compIso isoₗ (PushoutEmptyFam (snd ∘ fst) snd))
  where
  isoₗ : Iso (Pushout f fst) (Fin 1)
  isoₗ = PushoutAlongEquiv (isoToEquiv (CW₁Data₁ zero f c)) fst
CW₁Data (suc zero) (suc m) f c =
  ⊥.rec (Fin≠Fin (snotz ∘ sym ∘ cong (predℕ ∘ predℕ))
        mainIso)
  where
  mainIso : Iso (Fin 2) (Fin (3 +ℕ m))
  mainIso =
    compIso
      (compIso
        (invIso rUnit×Iso)
        (compIso
          (Σ-cong-iso
            (invIso Iso-Bool-Fin)
            (λ _ → isContr→Iso (tt , (λ _ → refl))
                                (inhProp→isContr fzero isPropFin1)))
            Σ-swap-Iso))
      (CW₁Data₁ (suc m) f c)
CW₁Data (suc (suc n)) m f c =
    main .fst , main .snd .fst
  , compIso correct (main .snd .snd)
  where
  t = notAllLoops-α₀ (suc (suc n)) m f c

  abstract
    x₀ : Fin (suc (suc n))
    x₀ = fst t

    xpath : ¬ (f (x₀ , true) ≡ f (x₀ , false))
    xpath = snd t

  Fin0-iso : Iso (Fin (suc (suc n)) × S₊ 0) (Fin (suc (suc n)) × S₊ 0)
  Fin0-iso = Σ-cong-iso-fst (swapFinIso flast x₀)

  FinIso2 : Iso (Fin (suc (suc m))) (Fin (suc (suc m)))
  FinIso2 = swapFinIso (f (x₀ , false)) flast

  f' : Fin (suc (suc n)) × S₊ 0 → Fin (suc (suc m))
  f' = Iso.fun FinIso2 ∘ f ∘ Iso.fun Fin0-iso

  f'≡ : f' (flast , false) ≡ flast
  f'≡ = cong (Iso.fun FinIso2 ∘ f)
          (cong (_, false) (swapFinβₗ flast x₀))
      ∙ swapFinβₗ (f (x₀ , false)) flast

  f'¬≡ : ¬ (f' (flast , true) ≡ flast)
  f'¬≡ p = xpath (cong f (ΣPathP (sym (swapFinβₗ flast x₀) , refl))
                ∙ sym (Iso.rightInv FinIso2 _)
                ∙ cong (Iso.inv FinIso2) (p ∙ sym f'≡)
                ∙ Iso.rightInv FinIso2 _
                ∙ cong f (ΣPathP (swapFinβₗ flast x₀ , refl)))

  f'< : fst (f' (flast , true)) <ᵗ suc m
  f'< = ≠flast→<ᵗflast _ f'¬≡

  main = CW₁DataPre _ _ f' f'≡ f'<

  Upath = isoToPath (swapFinIso x₀ fzero)

  correct : Iso (Pushout f fst) (Pushout f' fst)
  correct = pushoutIso _ _ _ _
    (isoToEquiv Fin0-iso) (isoToEquiv FinIso2) (isoToEquiv (swapFinIso flast x₀))
      (funExt (λ x → cong (FinIso2 .Iso.fun ∘ f) (sym (Iso.rightInv Fin0-iso x))))
      refl


CW₁Data' : (n m : ℕ) (f : Fin n × S₊ 0 → Fin m)
  → isConnected 2 (Pushout f fst)
  → Σ[ k ∈ ℕ ]
       Iso (Pushout f fst)
           (Pushout {A = Fin k × S₊ 0} {B = Fin 1} (λ _ → fzero) fst)
CW₁Data' zero zero f c = ⊥.rec (TR.rec (λ()) help (fst c))
  where
  help : ¬ Pushout f fst
  help = elimProp _ (λ _ → λ ()) snd snd
CW₁Data' (suc n) zero f c = ⊥.rec (f (fzero , true) .snd)
CW₁Data' n (suc zero) f c = n
  , pushoutIso _ _ _ _ (idEquiv _) (idEquiv _) (idEquiv _)
    (funExt (λ x → isPropFin1 _ _)) refl
CW₁Data' zero (suc (suc m)) f c =
  ⊥.rec (TR.rec (λ()) (snotz ∘ sym ∘ cong fst)
          (Iso.fun (PathIdTruncIso _)
            (isContr→isProp (subst (isConnected 2) (isoToPath help) c)
              ∣ fzero ∣ ∣ fone ∣)))
  where
  help : Iso (Pushout f fst) (Fin (suc (suc m)))
  help = invIso (PushoutEmptyFam (λ()) λ())
CW₁Data' (suc n) (suc (suc m)) f c
  with (CW₁Data' _ (suc m) (CW₁Data (suc n) m f c .snd .fst)
       (subst (isConnected 2)
         (isoToPath (CW₁Data (suc n) m f c .snd .snd)) c))
... | (k , e) = k , compIso (CW₁Data (suc n) m f c .snd .snd) e

yieldsConnectedCWskel : (A : ℕ → Type ℓ) (n : ℕ) → Type _
yieldsConnectedCWskel A k =
  Σ[ sk ∈ yieldsCWskel A ] ((sk .fst 0 ≡ 1) × ((n : ℕ) → n <ᵗ k → sk .fst (suc n) ≡ 0))

yieldsConnectedCWskel' : (A : ℕ → Type ℓ) (n : ℕ) → Type _
yieldsConnectedCWskel' A n = Σ[ sk ∈ yieldsCWskel A ] isConnected (2 +ℕ n) (realise (_ , sk))

connectedCWskel : (ℓ : Level) (n : ℕ) → Type (ℓ-suc ℓ)
connectedCWskel ℓ n = Σ[ X ∈ (ℕ → Type ℓ) ] (yieldsConnectedCWskel X n)

connectedCWskel' : (ℓ : Level) (n : ℕ) → Type (ℓ-suc ℓ)
connectedCWskel' ℓ n = Σ[ X ∈ (ℕ → Type ℓ) ] (yieldsConnectedCWskel' X n)

truncCWIso : (A : CWskel ℓ) (n : ℕ)
  → Iso (hLevelTrunc n (realise A)) (hLevelTrunc n (fst A n))
truncCWIso A n = invIso (connectedTruncIso n incl (isConnected-CW↪∞ n A))

isConnectedColim→isConnectedSkel :
  (A : CWskel ℓ) (n : ℕ)
  → isConnected n (realise A)
  → isConnected n (fst A n)
isConnectedColim→isConnectedSkel A n c =
  isOfHLevelRetractFromIso 0
    (invIso (truncCWIso A n)) c

module _ (A : ℕ → Type ℓ) (sk+c : yieldsConnectedCWskel' A 0) where
  private
    c = snd sk+c
    sk = fst sk+c
    c' = isConnectedColim→isConnectedSkel (_ , sk) 2 c

    module AC = CWskel-fields (_ , sk)

    e₁ : Iso (Pushout (fst (CW₁-discrete (_ , sk)) ∘ AC.α 1) fst) (A 2)
    e₁ = compIso (PushoutPostcompEquivIso (CW₁-discrete (A , sk)) (AC.α 1) fst)
                 (equivToIso (invEquiv (AC.e 1)))

    liftStr = CW₁Data' _ _ (fst (CW₁-discrete (_ , sk)) ∘ AC.α 1)
                (isConnectedRetractFromIso 2 e₁ c')

  collapse₁card : ℕ → ℕ
  collapse₁card zero = 1
  collapse₁card (suc zero) = fst liftStr
  collapse₁card (suc (suc x)) = AC.card (suc (suc x))

  collapse₁CWskel : ℕ → Type _
  collapse₁CWskel zero = Lift ⊥
  collapse₁CWskel (suc zero) = Lift (Fin 1)
  collapse₁CWskel (suc (suc n)) = A (suc (suc n))

  collapse₁α : (n : ℕ) → Fin (collapse₁card n) × S⁻ n → collapse₁CWskel n
  collapse₁α (suc zero) (x , p) = lift fzero
  collapse₁α (suc (suc n)) = AC.α (2 +ℕ n)

  connectedCWskel→ : yieldsConnectedCWskel collapse₁CWskel 0
  fst (fst connectedCWskel→) = collapse₁card
  fst (snd (fst connectedCWskel→)) = collapse₁α
  fst (snd (snd (fst connectedCWskel→))) = λ()
  snd (snd (snd (fst connectedCWskel→))) zero =
    isContr→Equiv (isOfHLevelLift 0 (inhProp→isContr fzero isPropFin1))
                       ((inr fzero)
                 , (λ { (inr x) j → inr (isPropFin1 fzero x j) }))
  snd (snd (snd (fst connectedCWskel→))) (suc zero) =
    compEquiv (invEquiv (isoToEquiv e₁))
      (compEquiv (isoToEquiv (snd liftStr))
      (isoToEquiv (pushoutIso' _ _ _ _
        (idEquiv _) LiftEquiv (idEquiv _)
        (funExt cohₗ) (funExt cohᵣ))))
    where
    -- Agda complains if these proofs are inlined...
    cohₗ : (x : _) → collapse₁α 1 x ≡ collapse₁α 1 x
    cohₗ (x , p) = refl

    cohᵣ : (x : Fin (fst liftStr) × Bool) → fst x ≡ fst x
    cohᵣ x = refl
  snd (snd (snd (fst connectedCWskel→))) (suc (suc n)) = AC.e (suc (suc n))
  snd connectedCWskel→ = refl , (λ _ → λ ())

  collapse₁Equiv : (n : ℕ)
    → realise (_ , sk) ≃ realise (_ , connectedCWskel→ .fst)
  collapse₁Equiv n =
    compEquiv
      (isoToEquiv (Iso-SeqColim→SeqColimShift _ 3))
      (compEquiv (pathToEquiv (cong SeqColim
        (cong₂ sequence (λ _ m → A (3 +ℕ m))
                        λ _ {z} → CW↪ (A , sk) (suc (suc (suc z))))))
        (invEquiv (isoToEquiv (Iso-SeqColim→SeqColimShift _ 3))))


connectedCWskel'→connectedCWskel : ∀ {ℓ}
  → Σ[ t ∈ connectedCWskel' ℓ 0 ]
       (Σ[ dim ∈ ℕ ]
         ((k : ℕ) → isEquiv (CW↪ (_ , snd t .fst) (k +ℕ dim))))
   → Σ[ t ∈ connectedCWskel ℓ 0 ]
        Σ[ dim ∈ ℕ ]
         ((k : ℕ) → isEquiv (CW↪ (_ , snd t .fst) (k +ℕ dim)))
fst (connectedCWskel'→connectedCWskel ((A , sk) , conv)) =
  _ , connectedCWskel→ A ((sk .fst) , (sk .snd)) .fst , refl , (λ _ → λ())
fst (snd (connectedCWskel'→connectedCWskel ((A , sk) , conv))) = suc (fst conv)
snd (snd (connectedCWskel'→connectedCWskel ((A , sk) , zero , T))) k =
  ⊥.rec (TR.rec (λ())
    (λ a → TR.rec (λ())
      (λ t → CW₀-empty (_ , fst sk) (invEq (_ , T 0) (t .fst)))
      (isConnected-CW↪∞ 1 (_ , fst sk) a .fst)) (sk .snd .fst))
snd (snd (connectedCWskel'→connectedCWskel ((A , sk) , (suc dim) , T))) k =
  transport (λ i → isEquiv (CW↪ (collapse₁CWskel A sk , connectedCWskel→ A sk .fst)
            (h i)))
            (transport (λ i → isEquiv (CW↪ (A , sk .fst) (suc (+-suc k dim i))))
            (T (suc k)))
  where
  h = cong suc (sym (+-suc k dim)) ∙ sym (+-suc k (suc dim))

yieldsGoodCWskel : {ℓ : Level} (A₊₂ : ℕ → Pointed ℓ) → Type _
yieldsGoodCWskel {ℓ = ℓ} A  =
  Σ[ f₊₁ ∈ (ℕ → ℕ) ]
   Σ[ fin ∈ (A 0) .fst ≃ Fin 1 ] 
    Σ[ α ∈ ((n : ℕ) → SphereBouquet∙ n (Fin (f₊₁ n)) →∙ A n) ]
           ((n : ℕ) → cofib (α n .fst) , inl tt ≃∙ A (suc n))

GoodCWskelSeq : {ℓ : Level} {A : ℕ → Pointed ℓ} → yieldsGoodCWskel A → Sequence ℓ
obj (GoodCWskelSeq {A = A} (f , fin , α , sq)) zero = Lift ⊥
obj (GoodCWskelSeq {A = A} (f , fin , α , sq)) (suc n) = fst (A n)
Sequence.map (GoodCWskelSeq {A = A} (f , fin , α , sq)) {n = suc n} x = fst (fst (sq n)) (inr x)

realiseGood∙ : {ℓ : Level} {A : ℕ → Pointed ℓ} → yieldsGoodCWskel A → Pointed ℓ
realiseGood∙ {A = A} S = SeqColim (GoodCWskelSeq S) , incl {n = 1} (snd (A 0))

yieldsFinGoodCWskel : {ℓ : Level} (dim : ℕ) (A₊₂ : ℕ → Pointed ℓ) → Type _
yieldsFinGoodCWskel {ℓ = ℓ} dim A  =
  Σ[ A ∈ yieldsGoodCWskel A ] converges (GoodCWskelSeq A) dim

GoodCWskel : (ℓ : Level) → Type (ℓ-suc ℓ)
GoodCWskel ℓ = Σ[ A ∈ (ℕ → Pointed ℓ) ] yieldsGoodCWskel A

FinGoodCWskel : (ℓ : Level) (dim : ℕ) → Type (ℓ-suc ℓ)
FinGoodCWskel ℓ dim = Σ[ A ∈ (ℕ → Pointed ℓ) ] yieldsFinGoodCWskel dim A

isGoodCWExpl : {ℓ : Level} (A : Pointed ℓ) → Type (ℓ-suc ℓ)
isGoodCWExpl {ℓ} A = Σ[ sk ∈ GoodCWskel ℓ ] realiseGood∙ (snd sk) ≃∙ A

isFinGoodCWExpl : {ℓ : Level} (A : Pointed ℓ) → Type (ℓ-suc ℓ)
isFinGoodCWExpl {ℓ} A =
  Σ[ dim ∈ ℕ ] Σ[ sk ∈ FinGoodCWskel ℓ dim ] realiseGood∙ (fst (snd sk)) ≃∙ A

isGoodCW : {ℓ : Level} (A : Pointed ℓ) → Type (ℓ-suc ℓ)
isGoodCW {ℓ} A = ∃[ sk ∈ GoodCWskel ℓ ] realiseGood∙ (snd sk) ≃∙ A

isFinGoodCW : {ℓ : Level} (A : Pointed ℓ) → Type (ℓ-suc ℓ)
isFinGoodCW {ℓ} A =
  ∃[ dim ∈ ℕ ] Σ[ sk ∈ FinGoodCWskel ℓ dim ] (realiseGood∙ (fst (snd sk)) ≃∙ A)

finGoodCW : (ℓ : Level) → Type (ℓ-suc ℓ)
finGoodCW ℓ = Σ[ A ∈ Pointed ℓ ] isFinGoodCW A 

ptCW : {ℓ : Level} {A : ℕ → Type ℓ} → yieldsCWskel A → A 1
  → (n : ℕ) → A (suc n)
ptCW sk a zero = a
ptCW sk a (suc n) = CW↪ (_ , sk) (suc n) (ptCW sk a n)

-- module TWOO {ℓ : Level} (A' : ℕ → Type ℓ) (pt0 : A' 1)
--   (dim : ℕ) (con : isConnected 2 (A' 2))
--   (C : yieldsFinCWskel dim A')
--   where

--   open CWskel-fields (_ , fst C)
--   e₀ : A' 1 ≃ Fin (card 0)
--   e₀ = CW₁-discrete (_ , fst C)

--   ptA : (n : ℕ) → A' (suc n)
--   ptA = ptCW (fst C) pt0

--   conA : (n : ℕ) → isConnected 2 (A' (suc n))
--   conA zero = isConnectedRetractFromIso 2 (equivToIso e₀)
--                 (subst (isConnected 2) (sym (cong Fin cA))
--                   (∣ flast ∣
--                   , TR.elim (λ _ → isOfHLevelPath 2
--                             (isOfHLevelTrunc 2) _ _)
--                       λ {(zero , tt) → refl}))
--   conA (suc n) =
--     isConnectedRetractFromIso 2
--       (equivToIso (e (suc n)))
--       (∣ inl (ptA n) ∣ₕ
--       , TR.elim (λ _ → isOfHLevelPath 2 (isOfHLevelTrunc 2) _ _)
--           (elimProp _ (λ _ → isOfHLevelTrunc 2 _ _)
--             (conA' (conA n))
--             λ c → conA' (conA n) _
--                  ∙ cong ∣_∣ₕ (push (c , ptSn n))))
--     where
--     conA' : (conA : isConnected 2 (A' (suc n))) (c : A' (suc n))
--       → Path (hLevelTrunc 2 (Pushout (α (suc n)) fst))
--               ∣ inl (ptA n) ∣ₕ ∣ inl c ∣ₕ
--     conA' conA c =
--       TR.rec (isOfHLevelTrunc 2 _ _)
--         (λ p i → ∣ inl (p i) ∣)
--         (Iso.fun (PathIdTruncIso _)
--           (isContr→isProp conA ∣ ptA n ∣ₕ ∣ c ∣ₕ))


--   private
--     funType = ((n : Fin (suc dim))
--                 → Σ[ h ∈ (SphereBouquet∙ (fst n) (Fin (card (suc (fst n))))
--                 →∙ (A' (suc (fst n)) , ptA (fst n))) ]
--                    ((x : _) → fst h (inr x) ≡ α (suc (fst n)) x))

--   mapMakerNil : ∥ funType ∥₁
--   mapMakerNil =
--     invEq propTrunc≃Trunc1 (invEq (_ , InductiveFinSatAC _ _ _)
--       λ n → TR.map
--         (λ pted → ((λ { (inl x) → ptA (fst n)
--                        ; (inr x) → α _ x
--                        ; (push a i) → pted a i})
--                   , refl)
--           , λ _ → refl) (help n))
--     where
--     help : (n : Fin (suc dim))
--       → hLevelTrunc 1 ((x : Fin (card (suc (fst n))))
--                      → (ptA (fst n) ≡ α (suc (fst n)) (x , ptSn (fst n))))
--     help n = invEq (_ , InductiveFinSatAC _ _ _)
--       λ m → Iso.fun (PathIdTruncIso _)
--               (isContr→isProp
--                 (conA (fst n)) ∣ (ptA (fst n)) ∣ₕ
--                                ∣ α (suc (fst n)) (m , ptSn (fst n)) ∣ₕ)
--   module _ (F : funType) where
--     funs : (n : ℕ) → SphereBouquet∙ n (Fin (card (suc n)))
--                    →∙ (A' (suc n) , ptA n)
--     funs n with (n ≟ᵗ dim)
--     ... | lt x = F (n , <ᵗ-trans-suc x) .fst
--     ... | eq x = F (n , subst (_<ᵗ suc dim) (sym x) <ᵗsucm) .fst
--     ... | gt x = const∙ _ _

--     funEqP1 : (n : ℕ) → (cofib (funs n .fst) , inl tt)
--                       ≃∙ Pushout (funs n .fst ∘ inr) (λ r → fst r) , inl (ptA n)
--     funEqP1 n = invEquiv (isoToEquiv (⋁-cofib-Iso _ (funs n))) , refl

--     funEq : (n : ℕ) → Pushout (funs n .fst ∘ inr) fst , inl (ptA n)
--                      ≃∙ Pushout (fst (C .snd) (suc n)) fst , inl (ptA n)
--     funEq n = isoToEquiv (pushoutIso' _ _ _ _
--                   (idEquiv _)
--                   (idEquiv _)
--                   (idEquiv _)
--                   (funExt (uncurry (main n)))
--                   (λ i x → fst x))
--                 , λ _ → inl (ptA n)
--       where
--       main : (n : ℕ) (x : Fin (card (suc n))) (y : S₊ n)
--         → funs n .fst (inr (x , y)) ≡ fst (C .snd) (suc n) (x , y)
--       main n with (n ≟ᵗ dim)
--       ... | lt p = λ x y
--         → F (n , <ᵗ-trans-suc p) .snd (x , y)
--       ... | eq p = λ x y
--         → F (n , subst (_<ᵗ suc dim) (λ i → p (~ i)) <ᵗsucm) .snd (x , y)
--       ... | gt p = λ x
--         → ⊥.rec (¬Fin0 (subst Fin (ind (suc n) (<ᵗ-trans p <ᵗsucm)) x))

--   getGoodCWskelAux : ∥ yieldsGoodCWskel (λ n → A' (suc n) , ptA n) ∥₁
--   getGoodCWskelAux = PT.map help mapMakerNil
--     where
--     help : funType → yieldsGoodCWskel (λ n → A' (suc n) , ptA n)
--     fst (help F) = card ∘ suc
--     fst (snd (help F)) = compEquiv e₀ (pathToEquiv (cong Fin cA))
--     fst (snd (snd (help F))) n = funs F n
--     snd (snd (snd (help F))) n =
--       compEquiv∙ (compEquiv∙ (funEqP1 F n) (funEq F n))
--                  (invEquiv (e (suc n)) , refl)


module BS {ℓ : Level} (A' : ℕ → Type ℓ)
  (dim : ℕ)
  (C+eq : yieldsFinCWskel dim A')
  (cA : fst (fst C+eq) 0 ≡ 1)
  where
  C = fst C+eq
  ind = snd C+eq

  open CWskel-fields (_ , C)
  e₀ : A' 1 ≃ Fin (card 0)
  e₀ = CW₁-discrete (_ , C)


  ¬dim≡0 : ¬ (dim ≡ 0)
  ¬dim≡0 p = CW₀-empty (_ , C) (subst A' p
          (invEq (_ , ind 0) (subst A' (cong suc (sym p))
            (invEq e₀ (subst Fin (sym cA) fzero)))))

  pt0 : A' 1
  pt0 = invEq e₀ (subst Fin (sym cA) flast)

  ptA : (n : ℕ) → A' (suc n)
  ptA = ptCW C pt0

  conA : (n : ℕ) → isConnected 2 (A' (suc n))
  conA zero = isConnectedRetractFromIso 2 (equivToIso e₀)
                (subst (isConnected 2) (sym (cong Fin cA))
                  (∣ flast ∣
                  , TR.elim (λ _ → isOfHLevelPath 2
                            (isOfHLevelTrunc 2) _ _)
                      λ {(zero , tt) → refl}))
  conA (suc n) =
    isConnectedRetractFromIso 2
      (equivToIso (e (suc n)))
      (∣ inl (ptA n) ∣ₕ
      , TR.elim (λ _ → isOfHLevelPath 2 (isOfHLevelTrunc 2) _ _)
          (elimProp _ (λ _ → isOfHLevelTrunc 2 _ _)
            (conA' (conA n))
            λ c → conA' (conA n) _
                 ∙ cong ∣_∣ₕ (push (c , ptSn n))))
    where
    conA' : (conA : isConnected 2 (A' (suc n))) (c : A' (suc n))
      → Path (hLevelTrunc 2 (Pushout (α (suc n)) fst))
              ∣ inl (ptA n) ∣ₕ ∣ inl c ∣ₕ
    conA' conA c =
      TR.rec (isOfHLevelTrunc 2 _ _)
        (λ p i → ∣ inl (p i) ∣)
        (Iso.fun (PathIdTruncIso _)
          (isContr→isProp conA ∣ ptA n ∣ₕ ∣ c ∣ₕ))

  private
    funType = ((n : Fin dim)
                → Σ[ h ∈ (SphereBouquet∙ (fst n) (Fin (card (suc (fst n))))
                →∙ (A' (suc (fst n)) , ptA (fst n))) ]
                   ((x : _) → fst h (inr x) ≡ α (suc (fst n)) x))

  mapMakerNil : ∥ funType ∥₁
  mapMakerNil =
    invEq propTrunc≃Trunc1 (invEq (_ , InductiveFinSatAC _ _ _)
      λ n → TR.map
        (λ pted → ((λ { (inl x) → ptA (fst n)
                       ; (inr x) → α _ x
                       ; (push a i) → pted a i})
                  , refl)
          , λ _ → refl) (help n))
    where
    help : (n : Fin dim)
      → hLevelTrunc 1 ((x : Fin (card (suc (fst n))))
                     → (ptA (fst n) ≡ α (suc (fst n)) (x , ptSn (fst n))))
    help n = invEq (_ , InductiveFinSatAC _ _ _)
      λ m → Iso.fun (PathIdTruncIso _)
              (isContr→isProp
                (conA (fst n)) ∣ (ptA (fst n)) ∣ₕ  ∣ α (suc (fst n)) (m , ptSn (fst n)) ∣ₕ)

  module _ (F : funType) where
    card' : ℕ → ℕ
    card' n with (n ≟ᵗ dim)
    ... | lt x = card (suc n)
    ... | eq x = 0
    ... | gt x = 0

    funs : (n : ℕ) → SphereBouquet∙ n (Fin (card' n))
                   →∙ (A' (suc n) , ptA n)
    funs n with (n ≟ᵗ dim)
    ... | lt x = F (n , x) .fst
    ... | eq x = const∙ _ _
    ... | gt x = const∙ _ _

    funEqP1 : (n : ℕ) → (cofib (funs n .fst) , inl tt)
                      ≃∙ Pushout (funs n .fst ∘ inr) (λ r → fst r) , inl (ptA n)
    funEqP1 n = invEquiv (isoToEquiv (⋁-cofib-Iso _ (funs n))) , refl

    funEq : (n : ℕ) → Pushout (funs n .fst ∘ inr) fst , inl (ptA n)
                     ≃∙ Pushout (fst (C .snd) (suc n)) fst , inl (ptA n)
    funEq n with (n ≟ᵗ dim)
    ... | lt x = isoToEquiv (pushoutIso' _ _ _ _
                  (idEquiv _)
                  (idEquiv _)
                  (idEquiv _)
                  (funExt (uncurry λ x y → F (n , _) .snd (x , y)))
                  (λ i x → fst x))
                , λ _ → inl (ptA n)
    ... | eq x = (compEquiv (isoToEquiv (invIso (PushoutEmptyFam (λ()) λ())))
                   (compEquiv ((CW↪ (_ , C) (suc n))
                              , transport (λ i → isEquiv (CW↪ (A' , C)
                                    (suc (x (~ i)))))
                                      (ind 1)
                                      )
                              (e (suc n)))) , secEq (e (suc n)) _
    ... | gt x = (compEquiv (isoToEquiv (invIso (PushoutEmptyFam (λ()) λ())))
                   (compEquiv ((CW↪ (_ , C) (suc n))
                                , (transport (λ i → isEquiv (CW↪ (A' , C)
                                    (suc ((sym (+-suc (fst (<ᵗ→< x)) dim)
                                        ∙ (<ᵗ→< x .snd)) i))))
                                      (ind (suc (suc (fst (<ᵗ→< x)))))))
                              (e (suc n)))) , secEq (e (suc n)) _

    goodCWmk : yieldsGoodCWskel (λ n → A' (suc n) , ptA n)
    fst goodCWmk = card'
    fst (snd goodCWmk) = compEquiv e₀ (pathToEquiv (cong Fin cA))
    fst (snd (snd goodCWmk)) = funs
    snd (snd (snd goodCWmk)) n =
      compEquiv∙ (compEquiv∙ (funEqP1 n) (funEq n))
                  (invEquiv (e (suc n)) , refl)

    goodCWmk-converges : converges
      (sequence (obj (GoodCWskelSeq goodCWmk))
                (Sequence.map (GoodCWskelSeq goodCWmk)))
      dim
    goodCWmk-converges zero = help dim refl
      where
      help : (x : _) (p : dim ≡ x) → isEquiv (Sequence.map (GoodCWskelSeq goodCWmk) {x})
      help zero p = ⊥.rec (¬dim≡0 p)
      help (suc x) p with (x ≟ᵗ dim)
      ... | lt x₁ = transport (λ i → isEquiv λ z → CW↪ (A' , C) (p i) z) (ind zero)
      ... | eq x₁ = ⊥.rec (¬m<m (0 , sym (x₁ ∙ p)))
      ... | gt x₁ = ⊥.rec (¬m<ᵗm (subst (dim <ᵗ_) (sym p) (<ᵗ-trans x₁ <ᵗsucm)))
    goodCWmk-converges (suc k) with ((k +ℕ dim) ≟ᵗ dim)
    ... | lt x = ⊥.rec (¬squeeze (x , (<→<ᵗ (k , +-suc k dim))))
    ... | eq x = compEquiv (_ , ind _)
                  (compEquiv (e (suc (k +ℕ dim)))
                   (invEquiv (_ , snd (fst C+eq .snd .snd .snd (suc (k +ℕ dim)))))) .snd
    ... | gt x = compEquiv (_ , ind _)
                  (compEquiv (e (suc (k +ℕ dim)))
                   (invEquiv (_ , snd (fst C+eq .snd .snd .snd (suc (k +ℕ dim)))))) .snd
 
    funType→ : realiseGood∙ goodCWmk .fst ≃ A' (suc dim)
    funType→ = compEquiv (isoToEquiv (invIso
        (converges→ColimIso dim goodCWmk-converges)))
          (help dim refl)
      where
      help : (x : _) (p : dim ≡ x) → obj (GoodCWskelSeq goodCWmk) x ≃ A' (suc x)
      help zero p = ⊥.rec (¬dim≡0 p)
      help (suc x) p = subst (λ x → A' x ≃ A' (suc x)) p (_ , ind 0)

    merelyPointed : ∥ realiseGood∙ goodCWmk ≃∙ A' (suc dim) , ptA dim ∥₁
    merelyPointed = PT.map (λ idp → funType→ , idp) (help dim refl)
      where
      help : (x : ℕ) (p : dim ≡ x)
        → ∥ funType→ .fst (realiseGood∙ goodCWmk .snd) ≡ ptA dim ∥₁
      help zero p = ⊥.rec (¬dim≡0 p)
      help (suc x) p = invEq propTrunc≃Trunc1 (PathIdTruncIso 1 .Iso.fun
                        (isContr→isProp
                          (subst (isConnected 2 ∘ A') (sym (cong suc p))
                            (conA (suc x)))
                            ∣ (funType→ .fst (realiseGood∙ goodCWmk .snd)) ∣ₕ
                            ∣ ptA dim ∣ₕ))

  getGoodCWskel : ∃[ skel ∈ yieldsGoodCWskel (λ n → A' (suc n) , ptA n) ]
                     converges (GoodCWskelSeq skel) dim
  getGoodCWskel = PT.map (λ F → (goodCWmk F)
                       , (goodCWmk-converges F)) mapMakerNil

  getGoodCWskelAux : ∥ yieldsGoodCWskel (λ n → A' (suc n) , ptA n) ∥₁
  getGoodCWskelAux = PT.map help mapMakerNil
    where
    help : funType → yieldsGoodCWskel (λ n → A' (suc n) , ptA n)
    fst (help F) = card' F
    fst (snd (help F)) = compEquiv e₀ (pathToEquiv (cong Fin cA))
    fst (snd (snd (help F))) = funs F
    snd (snd (snd (help F))) n =
      compEquiv∙ (compEquiv∙ (funEqP1 F n) (funEq F n))
                  (invEquiv (e (suc n)) , refl)



    {-
    fst (help F) = card ∘ suc
    fst (snd (help F)) = compEquiv e₀ (pathToEquiv (cong Fin cA))
    fst (snd (snd (help F))) n = funs F n
    snd (snd (snd (help F))) n =
      compEquiv∙ (compEquiv∙ (funEqP1 F n) (funEq F n))
                 (invEquiv (e (suc n)) , refl)
-}

-- module _ {ℓ : Level} (A' : ℕ → Type ℓ)
--   (C : yieldsCWskel A')
--   (dim : ℕ) (ind : (n : ℕ) → dim <ᵗ n → fst C n ≡ 0)
--   (cA : fst C 0 ≡ 1)
--   where

--   open CWskel-fields (_ , C)
--   e₀ : A' 1 ≃ Fin (card 0)
--   e₀ = CW₁-discrete (_ , C)


--   pt0 : A' 1
--   pt0 = invEq e₀ (subst Fin (sym cA) flast)

--   ptA : (n : ℕ) → A' (suc n)
--   ptA = ptCW C pt0

--   conA : (n : ℕ) → isConnected 2 (A' (suc n))
--   conA zero = isConnectedRetractFromIso 2 (equivToIso e₀)
--                 (subst (isConnected 2) (sym (cong Fin cA))
--                   (∣ flast ∣
--                   , TR.elim (λ _ → isOfHLevelPath 2
--                             (isOfHLevelTrunc 2) _ _)
--                       λ {(zero , tt) → refl}))
--   conA (suc n) =
--     isConnectedRetractFromIso 2
--       (equivToIso (e (suc n)))
--       (∣ inl (ptA n) ∣ₕ
--       , TR.elim (λ _ → isOfHLevelPath 2 (isOfHLevelTrunc 2) _ _)
--           (elimProp _ (λ _ → isOfHLevelTrunc 2 _ _)
--             (conA' (conA n))
--             λ c → conA' (conA n) _
--                  ∙ cong ∣_∣ₕ (push (c , ptSn n))))
--     where
--     conA' : (conA : isConnected 2 (A' (suc n))) (c : A' (suc n))
--       → Path (hLevelTrunc 2 (Pushout (α (suc n)) fst))
--               ∣ inl (ptA n) ∣ₕ ∣ inl c ∣ₕ
--     conA' conA c =
--       TR.rec (isOfHLevelTrunc 2 _ _)
--         (λ p i → ∣ inl (p i) ∣)
--         (Iso.fun (PathIdTruncIso _)
--           (isContr→isProp conA ∣ ptA n ∣ₕ ∣ c ∣ₕ))


--   private
--     funType = ((n : Fin (suc dim))
--                 → Σ[ h ∈ (SphereBouquet∙ (fst n) (Fin (card (suc (fst n))))
--                 →∙ (A' (suc (fst n)) , ptA (fst n))) ]
--                    ((x : _) → fst h (inr x) ≡ α (suc (fst n)) x))

--   mapMakerNil : ∥ funType ∥₁
--   mapMakerNil =
--     invEq propTrunc≃Trunc1 (invEq (_ , InductiveFinSatAC _ _ _)
--       λ n → TR.map
--         (λ pted → ((λ { (inl x) → ptA (fst n)
--                        ; (inr x) → α _ x
--                        ; (push a i) → pted a i})
--                   , refl)
--           , λ _ → refl) (help n))
--     where
--     help : (n : Fin (suc dim))
--       → hLevelTrunc 1 ((x : Fin (card (suc (fst n))))
--                      → (ptA (fst n) ≡ α (suc (fst n)) (x , ptSn (fst n))))
--     help n = invEq (_ , InductiveFinSatAC _ _ _)
--       λ m → Iso.fun (PathIdTruncIso _)
--               (isContr→isProp
--                 (conA (fst n)) ∣ (ptA (fst n)) ∣ₕ  ∣ α (suc (fst n)) (m , ptSn (fst n)) ∣ₕ)
--   module _ (F : funType) where
--     funs : (n : ℕ) → SphereBouquet∙ n (Fin (card (suc n)))
--                    →∙ (A' (suc n) , ptA n)
--     funs n with (n ≟ᵗ dim)
--     ... | lt x = F (n , <ᵗ-trans-suc x) .fst
--     ... | eq x = F (n , subst (_<ᵗ suc dim) (sym x) <ᵗsucm) .fst
--     ... | gt x = const∙ _ _

--     funEqP1 : (n : ℕ) → (cofib (funs n .fst) , inl tt)
--                       ≃∙ Pushout (funs n .fst ∘ inr) (λ r → fst r) , inl (ptA n)
--     funEqP1 n = invEquiv (isoToEquiv (⋁-cofib-Iso _ (funs n))) , refl

--     funEq : (n : ℕ) → Pushout (funs n .fst ∘ inr) fst , inl (ptA n)
--                      ≃∙ Pushout (fst (C .snd) (suc n)) fst , inl (ptA n)
--     funEq n = isoToEquiv (pushoutIso' _ _ _ _
--                   (idEquiv _)
--                   (idEquiv _)
--                   (idEquiv _)
--                   (funExt (uncurry (main n)))
--                   (λ i x → fst x))
--                 , λ _ → inl (ptA n)
--       where
--       main : (n : ℕ) (x : Fin (card (suc n))) (y : S₊ n)
--         → funs n .fst (inr (x , y)) ≡ fst (C .snd) (suc n) (x , y)
--       main n with (n ≟ᵗ dim)
--       ... | lt p = λ x y
--         → F (n , <ᵗ-trans-suc p) .snd (x , y)
--       ... | eq p = λ x y
--         → F (n , subst (_<ᵗ suc dim) (λ i → p (~ i)) <ᵗsucm) .snd (x , y)
--       ... | gt p = λ x
--         → ⊥.rec (¬Fin0 (subst Fin (ind (suc n) (<ᵗ-trans p <ᵗsucm)) x))

--   getGoodCWskelAux : ∥ yieldsGoodCWskel (λ n → A' (suc n) , ptA n) ∥₁
--   getGoodCWskelAux = PT.map help mapMakerNil
--     where
--     help : funType → yieldsGoodCWskel (λ n → A' (suc n) , ptA n)
--     fst (help F) = card ∘ suc
--     fst (snd (help F)) = compEquiv e₀ (pathToEquiv (cong Fin cA))
--     fst (snd (snd (help F))) n = funs F n
--     snd (snd (snd (help F))) n =
--       compEquiv∙ (compEquiv∙ (funEqP1 F n) (funEq F n))
--                  (invEquiv (e (suc n)) , refl)



open import Cubical.CW.Subcomplex
finCW→GoodCW : ∀ {ℓ} (A : finCW ℓ) (a₀ : fst A)
  → isConnected 2 (fst A)
  → finGoodCW ℓ
fst (finCW→GoodCW A a₀ cA) = fst A , a₀
snd (finCW→GoodCW (A , cwA) a₀ cA) =
  PT.rec squash₁ (λ cw → PT.rec squash₁
    (λ {(sk , T) → ∣ suc (fst cw) , (_ , sk , T)
       , compEquiv
         (isoToEquiv
           (compIso (invIso (converges→ColimIso _ T))
           (compIso (eqv cw _ refl)
             (converges→ColimIso _ (cw .snd .fst .snd .snd)))))
         (invEquiv (cw .snd .snd)) , {!!} ∣₁})
    (main cw))
    cwA
  where
  module _ (cw : isFinCW A) where
    makeNice' = makeNiceFinCWskel {A = A} cw

    inst = connectedCWskel'→connectedCWskel
             (((snd makeNice' .fst .fst)
            , (snd makeNice' .fst .snd .fst
            , isConnectedRetractFromIso 2
                 (equivToIso (invEquiv (snd makeNice' .snd))) cA))
            , _ , snd makeNice' .fst .snd .snd)

    open BS
              (inst .fst .fst)
              (suc (fst cw))
              ((snd (inst .fst) .fst) , inst .snd .snd)
              refl

    main = BS.getGoodCWskel
              (inst .fst .fst)
              (suc (fst cw))
              ((snd (inst .fst) .fst) , inst .snd .snd)
              refl

    open import Cubical.Foundations.Transport
    eqv : (x : _) (p : fst cw ≡ x)
      → Iso (inst .fst .fst (suc x))
             (fst (finCWskel→CWskel (fst cw) (fst (cw .snd))) x)
    eqv zero p = ⊥.rec (TR.rec (λ()) (λ s →
      (CW₀-empty (_ , snd cw .fst .snd .fst)
        (invEq (_ , transport (λ i → isEquiv
                          (CW↪ (fst (snd cw .fst)
                               , fst (snd cw .fst .snd)) (p i)))
                 (snd cw .fst .snd .snd 0))
          (s .fst))))
            (isConnected-CW↪∞ 1
              (_ , snd cw .fst .snd .fst)
                (fst (snd cw .snd) a₀) .fst))
    eqv (suc x) p with (suc (suc x) ≟ᵗ fst cw)
    ... | lt x₁ = ⊥.rec (¬m<ᵗm (<ᵗ-trans (subst (suc (suc x) <ᵗ_) p x₁) <ᵗsucm))
    ... | eq x₁ = ⊥.rec (¬m<ᵗm (subst (suc x <ᵗ_) (x₁ ∙ p) <ᵗsucm))
    ... | gt x₁ = pathToIso (cong (fst (snd cw) .fst) p)
      
    {- compIso (equivToIso (invEquiv (complex≃subcomplex (_ , snd cw .fst .snd .fst) {!suc (cw .fst)!} (suc (fst cw) , {!fst cw!})))) {!(fst (finCWskel→CWskel (fst cw) (fst (cw .snd))) (fst cw))!}
-}
    {- BS.getGoodCWskel _ ? ? -- (snd inst .fst) (fst cw) -- (snd inst .fst) (fst cw)
                              ? -- FN
                              ? -- refl -- refl
                              -}

{-
    inst = connectedCWskel'→connectedCWskel
              ((snd cw .fst .fst)
             , ((snd cw .fst .snd .fst)
             , (isConnectedRetractFromIso 2
                 (equivToIso (invEquiv (snd cw .snd))) cA)))

    makeNice = makeNiceFinCWskel {A = A} ((cw .fst)
                , ((inst .fst , inst .snd .fst
                 , {!cw .snd .fst .snd .snd!})
                , compEquiv (snd cw .snd) {!!}))

    check : (n : ℕ) → fst cw <ᵗ n → fst (snd inst .fst) n ≡ 0
    check n p with (suc (fst cw) ≟ᵗ n)
    ... | lt x = {!makeNiceFinCWskel!}
    ... | eq x = {!x!}
    ... | gt x = {!!}

    main = getGoodCWskelAux _ (makeNice .snd .fst .snd .fst) (fst cw) -- (snd inst .fst) (fst cw)
                              {!makeNice .snd .fst!}
                              {!!} -- refl
                              -}

--     ecw = snd (snd cw)

--     FL : (n : ℕ) → fst cw <ᵗ n
--       → fst (makeNiceFinCWskel cw .snd .fst .snd .fst) n ≡ 0
--     FL n p = {!inst .snd .fst!}

--     FR : fst (makeNiceFinCWskel cw .snd .fst .snd .fst) 0 ≡ 1
--     FR with (0 ≟ᵗ fst cw)
--     ... | lt t = {!!}
--     ... | eq x = ⊥.rec {!!}

--     main : {!!}
--     main = getGoodCWskelAux _
--             (makeNiceFinCWskel cw .snd .fst .snd .fst) (fst cw)
--               FL FR
-- -- makeNiceFinCWElim

-- connectedGoodCWskel' : ∀ {ℓ} (Aₙ₊₂ : ℕ → Pointed ℓ) → {!!}
-- connectedGoodCWskel' = {!!}




-- GoodCWSeq→CWSeq : {ℓ : Level} (A₊₂ : ℕ → Pointed ℓ) → {!!}
-- GoodCWSeq→CWSeq A₊₂ = {!!}

-- isGoodCW→isCW : ∀ {ℓ} (A₊₂ : ℕ → Pointed ℓ) → yieldsGoodCWskel A₊₂ → {!!}
-- isGoodCW→isCW = {!!}

-- -- connectedCWskel→CWskel : connectedCWskel ℓ → CWskel ℓ
-- -- connectedCWskel→CWskel (A , sk , _) = A , sk

-- -- module _ (C' : connectedCWskel ℓ) (n : ℕ) (x₀ : fst C' 1)
-- --          (term : converges (realiseSeq (fst C' , snd C' .fst)) n) where
-- --   private
-- --     C = fst C'
-- --     Csk = connectedCWskel→CWskel C'

-- --     open CWskel-fields Csk

-- --     ptC : (n : ℕ) → C (suc n)
-- --     ptC zero = x₀
-- --     ptC (suc n) = CW↪ Csk (suc n) (ptC n)

-- --     C∙ : ℕ → Pointed _
-- --     C∙ n = C (suc n) , ptC n

-- --   improveFam : ∥ ((m : Fin (suc (suc n))) → ?) ∥₁
-- --   improveFam = {!!}

-- --   finConnectedCW : {!!}
-- --   finConnectedCW = {!!}




-- -- -- yieldsGoodCWSkel : (ℕ → Type ℓ) → Type ℓ
-- -- -- yieldsGoodCWSkel = ?

-- -- -- yieldsCWskel∙ : (ℕ → Type ℓ) → Type ℓ
-- -- -- yieldsCWskel∙ X =
-- -- --   Σ[ f ∈ (ℕ → ℕ) ]
-- -- --     Σ[ α ∈ ((n : ℕ) → ⋁gen (Fin (f (suc n))) (λ _ → S₊∙ n) → X n) ]
-- -- --       ((X zero ≃ Fin (f zero)) ×
-- -- --       (((n : ℕ) → X (suc n) ≃ cofib (α n))))

-- -- -- CWskel∙ : (ℓ : Level) → Type (ℓ-suc ℓ)
-- -- -- CWskel∙ ℓ = Σ[ X ∈ (ℕ → Type ℓ) ] (yieldsCWskel∙ X)

-- -- -- module CWskel∙-fields (C : CWskel∙ ℓ) where
-- -- --   card = C .snd .fst
-- -- --   A = Fin ∘ card
-- -- --   α = C .snd .snd .fst
-- -- --   e = C .snd .snd .snd .snd

-- -- --   ℤ[A_] : (n : ℕ) → AbGroup ℓ-zero
-- -- --   ℤ[A n ] = ℤ[Fin (snd C .fst n) ]

-- -- -- CWpt : ∀ {ℓ} → (C : CWskel∙ ℓ) → (n : ℕ) → Pointed ℓ
-- -- -- fst (CWpt (C , f) n) = C n
-- -- -- snd (CWpt (C , f) n) = f .snd .fst n (inl tt)

-- -- -- -- Technically, a CW complex should be the sequential colimit over the following maps
-- -- -- CW∙↪ : (T : CWskel∙ ℓ) → (n : ℕ) → fst T n → fst T (suc n)
-- -- -- CW∙↪ (X , f , α , e₀ , e₊) n x = invEq (e₊ n) (inr x)

-- -- -- ptCW : (T : CWskel∙ ℓ) → (n : ℕ) → fst T n
-- -- -- ptCW T zero = T .snd .snd .fst zero (inl tt)
-- -- -- ptCW T (suc n) = CW∙↪ T n (ptCW T n)

-- -- -- CW∙ : (T : CWskel∙ ℓ) → (n : ℕ) → Pointed ℓ
-- -- -- CW∙ T n = fst T n , ptCW T n

-- -- -- CW∙↪∙ : (T : CWskel∙ ℓ) → (n : ℕ) → CW∙ T n →∙ CW∙ T (suc n)
-- -- -- fst (CW∙↪∙ T n) = CW∙↪ T n
-- -- -- snd (CW∙↪∙ T n) = refl


-- -- -- -- But if it stabilises, no need for colimits.
-- -- -- yieldsFinCWskel∙ : (n : ℕ) (X : ℕ → Type ℓ) → Type ℓ
-- -- -- yieldsFinCWskel∙ n X =
-- -- --   Σ[ CWskel ∈ yieldsCWskel∙ X ] ((k : ℕ) → isEquiv (CW∙↪ (X , CWskel) (k +ℕ n)))

-- -- -- -- ... which should give us finite CW complexes.
-- -- -- finCWskel∙ : (ℓ : Level) → (n : ℕ) → Type (ℓ-suc ℓ)
-- -- -- finCWskel∙ ℓ n = Σ[ C ∈ (ℕ → Type ℓ) ] (yieldsFinCWskel∙ n C)

-- -- -- finCWskel→CWskel∙ : (n : ℕ) → finCWskel ℓ n → CWskel ℓ
-- -- -- finCWskel→CWskel∙ n C = fst C , fst (snd C)

-- -- -- realiseSeq∙ : CWskel∙ ℓ → Sequence ℓ
-- -- -- Sequence.obj (realiseSeq∙ (C , p)) = C
-- -- -- Sequence.map (realiseSeq∙ C) = CW∙↪ C _

-- -- -- realiseFinSeq∙ : (m : ℕ) → CWskel∙ ℓ → FinSequence m ℓ
-- -- -- realiseFinSeq∙ m C = Sequence→FinSequence m (realiseSeq∙ C)

-- -- -- -- realisation of CW complex from skeleton
-- -- -- realise∙ : CWskel∙ ℓ → Type ℓ
-- -- -- realise∙ C = SeqColim (realiseSeq∙ C)

-- -- -- realise∙∙ : CWskel∙ ℓ → Pointed ℓ
-- -- -- realise∙∙ C = SeqColim (realiseSeq∙ C) , incl {n = 0} (CW∙ C 0 .snd)
-- -- -- open import Cubical.Data.Empty as ⊥

-- -- -- CWskel∙→CWskel : (A : ℕ → Type ℓ) → ℕ → Type ℓ
-- -- -- CWskel∙→CWskel A zero = Lift ⊥
-- -- -- CWskel∙→CWskel A (suc n) = A n
-- -- -- open import Cubical.Foundations.Isomorphism


-- -- -- module _  (A : ℕ → Type ℓ)
-- -- --   (cwsk : yieldsCWskel∙ A) where

-- -- --   private
-- -- --     αs : (n : ℕ) → Fin (cwsk .fst n) × S⁻ n → CWskel∙→CWskel A n
-- -- --     αs (suc n) x = snd cwsk .fst n (inr x)

-- -- --     e0 : {!!}
-- -- --     e0 = {!!}

-- -- --     es-suc→ : (n : ℕ) → cofib (fst (snd cwsk) n) → Pushout (αs (suc n)) fst
-- -- --     es-suc→ n (inl x) = inl (snd cwsk .fst n (inl tt))
-- -- --     es-suc→ n (inr x) = inl x
-- -- --     es-suc→ n (push (inl x) i) = inl (fst (snd cwsk) n (inl x))
-- -- --     es-suc→ n (push (inr (a , b)) i) = ((({!!} ∙ λ i → inl {!snd cwsk .snd n!}) ∙ push (a , b)) ∙ {!!}) i --  ({!!} ∙ sym (push (a , b))) i
-- -- --     es-suc→ n (push (push a i₁) i) = {!!}

-- -- --     es-suc : (n : ℕ)
-- -- --       → Iso (cofib (fst (snd cwsk) n))
-- -- --              (Pushout (αs (suc n)) fst)
-- -- --     Iso.fun (es-suc n) = es-suc→ n
-- -- --     Iso.inv (es-suc n) = {!!}
-- -- --     Iso.rightInv (es-suc n) = {!!}
-- -- --     Iso.leftInv (es-suc n) = {!!}

-- -- --     es : (n : ℕ) → A n ≃ Pushout (αs n) (λ r → fst r)
-- -- --     es zero = {!!}
-- -- --     es (suc n) = compEquiv (snd cwsk .snd .snd n) (isoToEquiv (es-suc n))

-- -- --   yieldsCWskel∙→' : yieldsCWskel (CWskel∙→CWskel A)
-- -- --   fst yieldsCWskel∙→' = cwsk .fst
-- -- --   fst (snd yieldsCWskel∙→') = αs
-- -- --   fst (snd (snd yieldsCWskel∙→')) ()
-- -- --   snd (snd (snd yieldsCWskel∙→')) = {!!}

-- -- -- yieldsCWskel∙→ : (A : ℕ → Type ℓ)
-- -- --   → yieldsCWskel∙ A → yieldsCWskel (CWskel∙→CWskel A)
-- -- -- fst (yieldsCWskel∙→ A cwsk) = cwsk .fst
-- -- -- fst (snd (yieldsCWskel∙→ A cwsk)) (suc n) (x , p) = snd cwsk .fst n (inr (x , p))
-- -- -- fst (snd (snd (yieldsCWskel∙→ A cwsk))) ()
-- -- -- snd (snd (snd (yieldsCWskel∙→ A cwsk))) zero = {!!}
-- -- -- snd (snd (snd (yieldsCWskel∙→ A cwsk))) (suc n) =
-- -- --   compEquiv (cwsk .snd .snd .snd n)
-- -- --     (isoToEquiv {!(fst (snd (yieldsCWskel∙→ A cwsk)) (suc n))!}) -- theEq)
-- -- --   where
-- -- --   theEq→ : cofib (fst (cwsk .snd) n) → Pushout _ fst
-- -- --   theEq→ (inl x) = inl (cwsk .snd .fst n (inl tt))
-- -- --   theEq→ (inr x) = inl x
-- -- --   theEq→ (push (inl x) i) = inl (cwsk .snd .fst n (inl tt))
-- -- --   theEq→ (push (inr (a , b)) i) = ({!push ?!} ∙ push {!!} ∙ {!!}) i -- inl (cwsk .snd .fst n {!!})
-- -- --   theEq→ (push (push a i₁) i) = {!!}

-- -- --   theEq : Iso (cofib (fst (cwsk .snd) n)) (Pushout _ fst)
-- -- --   Iso.fun theEq = theEq→
-- -- --   Iso.inv theEq = {!!}
-- -- --   Iso.rightInv theEq x = {!!}
-- -- --   Iso.leftInv theEq x = {!!}


-- -- --  -- compEquiv {!!} {!!}


-- -- -- -- -- Finally: definition of CW complexes
-- -- -- -- isCW : (X : Type ℓ) → Type (ℓ-suc ℓ)
-- -- -- -- isCW {ℓ = ℓ} X = Σ[ X' ∈ CWskel ℓ ] X ≃ realise X'

-- -- -- -- CW : (ℓ : Level) → Type (ℓ-suc ℓ)
-- -- -- -- CW ℓ = Σ[ A ∈ Type ℓ ] ∥ isCW A ∥₁

-- -- -- -- CWexplicit : (ℓ : Level) → Type (ℓ-suc ℓ)
-- -- -- -- CWexplicit ℓ = Σ[ A ∈ Type ℓ ] (isCW A)

-- -- -- -- -- Finite CW complexes
-- -- -- -- isFinCW : (X : Type ℓ) → Type (ℓ-suc ℓ)
-- -- -- -- isFinCW {ℓ = ℓ} X =
-- -- -- --   Σ[ m ∈ ℕ ] (Σ[ X' ∈ finCWskel ℓ m ] X ≃ realise (finCWskel→CWskel m X'))

-- -- -- -- finCW : (ℓ : Level) → Type (ℓ-suc ℓ)
-- -- -- -- finCW ℓ = Σ[ A ∈ Type ℓ ] ∥ isFinCW A ∥₁

-- -- -- -- finCWexplicit : (ℓ : Level) → Type (ℓ-suc ℓ)
-- -- -- -- finCWexplicit ℓ = Σ[ A ∈ Type ℓ ] (isFinCW A)

-- -- -- -- isFinCW→isCW : (X : Type ℓ) → isFinCW X → isCW X
-- -- -- -- isFinCW→isCW X (n , X' , str) = (finCWskel→CWskel n X') , str

-- -- -- -- finCW→CW : finCW ℓ → CW ℓ
-- -- -- -- finCW→CW (X , p) = X , PT.map (isFinCW→isCW X) p


-- -- -- -- -- morphisms
-- -- -- -- _→ᶜʷ_ : CW ℓ → CW ℓ' → Type (ℓ-max ℓ ℓ')
-- -- -- -- C →ᶜʷ D = fst C → fst D

-- -- -- -- --the cofibre of the inclusion of X n into X (suc n)
-- -- -- -- cofibCW : ∀ {ℓ} (n : ℕ) (C : CWskel ℓ) → Type ℓ
-- -- -- -- cofibCW n C = cofib (CW↪ C n)

-- -- -- -- --...is basically a sphere bouquet
-- -- -- -- cofibCW≃bouquet : ∀ {ℓ} (n : ℕ) (C : CWskel ℓ)
-- -- -- --   → cofibCW n C ≃ SphereBouquet n (Fin (snd C .fst n))
-- -- -- -- cofibCW≃bouquet n C = Bouquet≃-gen n (snd C .fst n) (α n) e
-- -- -- --   where
-- -- -- --   s = Bouquet≃-gen
-- -- -- --   α = C .snd .snd .fst
-- -- -- --   e = C .snd .snd .snd .snd n

-- -- -- -- --sending X (suc n) into the cofibCW
-- -- -- -- to_cofibCW : (n : ℕ) (C : CWskel ℓ) → fst C (suc n) → cofibCW n C
-- -- -- -- to_cofibCW n C x = inr x

-- -- -- -- --the connecting map of the long exact sequence
-- -- -- -- δ-pre :  {A : Type ℓ} {B : Type ℓ'} (conn : A → B)
-- -- -- --   → cofib conn → Susp A
-- -- -- -- δ-pre conn (inl x) = north
-- -- -- -- δ-pre conn (inr x) = south
-- -- -- -- δ-pre conn (push a i) = merid a i

-- -- -- -- δ : (n : ℕ) (C : CWskel ℓ) → cofibCW n C → Susp (fst C n)
-- -- -- -- δ n C = δ-pre (CW↪ C n)

-- -- -- -- -- send the stage n to the realization (the same as incl, but with explicit args and type)
-- -- -- -- CW↪∞ : (C : CWskel ℓ) → (n : ℕ) → fst C n → realise C
-- -- -- -- CW↪∞ C n x = incl x

-- -- -- -- finCW↑ : (n m : ℕ) → (m ≥ n) → finCWskel ℓ n → finCWskel ℓ m
-- -- -- -- fst (finCW↑ m n p C) = fst C
-- -- -- -- fst (snd (finCW↑ m n p C)) = snd C .fst
-- -- -- -- snd (snd (finCW↑ m n p C)) k =
-- -- -- --   subst (λ r → isEquiv (CW↪ (fst C , snd C .fst) r))
-- -- -- --         (sym (+-assoc k (fst p) m) ∙ cong (k +ℕ_) (snd p))
-- -- -- --         (snd C .snd (k +ℕ fst p))
