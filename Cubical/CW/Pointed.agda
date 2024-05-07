{-# OPTIONS --safe --lossy-unification #-}

-- This file contains definition of CW complexes and skeleta.

module Cubical.CW.Pointed where

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
module _ {A : Type} {B : A → Pointed₀} (C : Pointed₀) (f : (⋁gen A B , inl tt) →∙ C) where
  

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
                   (invIso (pushoutIso _ _ _ _
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
  A□○Iso = invIso (pushoutIso _ _ _ _
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

Bool×Fin≡Fin : {n : ℕ} → Iso (S₊ 0 × Fin n) (Fin (2 · n))
Bool×Fin≡Fin = compIso (Σ-cong-iso-fst Iso-Bool-Fin) (Fin× {n = 2})

decIm-S⁰×Fin : ∀ {ℓ} {A : Type ℓ}
  (da : Discrete A) (n : ℕ) (f : S₊ 0 × Fin n → A) → decIm f
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

CW₁Data' : (n m : ℕ) (f : S₊ 0 × Fin n → Fin (suc (suc m)))
  → isConnected 2 (Pushout f snd)
  → Σ[ k ∈ ℕ ] Σ[ f' ∈ (S₊ 0 × Fin k → Fin (suc m)) ]
       Iso (Pushout f snd)
           (Pushout f' snd)
CW₁Data' zero m f c = ⊥.rec {!!}
CW₁Data' (suc zero) m f c = {!!}
CW₁Data' (suc (suc n)) m f c = {!!}


isSurj-α₀ : (n m : ℕ) (f : S₊ 0 × Fin n → Fin (suc (suc m)))
  → isConnected 2 (Pushout f snd)
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

  help : Pushout f snd → Type
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


notAllLoops-α₀ : (n m : ℕ) (f : S₊ 0 × Fin n → Fin (suc (suc m)))
  → isConnected 2 (Pushout f snd)
  → Σ[ x ∈ Fin n ] (¬ f (true , x) ≡ f (false , x))
notAllLoops-α₀ n m f c with (allConst? DiscreteFin (λ x y → f (y , x)))
... | inr x = x
notAllLoops-α₀ n m f c | inl q =
  ⊥.rec (TR.rec isProp⊥ (λ p → subst T p tt)
           (Iso.fun(PathIdTruncIso 1)
             (isContr→isProp c
               ∣ inl flast ∣ ∣ inl fzero ∣)))
  where
  inrT : Fin n → Type
  inrT x with (DiscreteFin (f (true , x)) fzero)
  ... | yes p = ⊥
  ... | no ¬p = Unit

  inlT : Fin (suc (suc m)) → Type
  inlT (zero , p) = ⊥
  inlT (suc x , p) = Unit

  inlrT-pre : (a : _) → inlT (f (true , a)) ≡ inrT a
  inlrT-pre a with ((DiscreteFin (f (true , a)) fzero))
  ... | yes p = cong inlT p
  inlrT-pre s | no ¬p with (f (true , s))
  ... | zero , tt = ⊥.rec (¬p refl)
  ... | suc q , t = refl

  inlrT : (a : _) → inlT (f a) ≡ inrT (snd a)
  inlrT (false , b) = cong inlT (funExt⁻ (q b) false) ∙ inlrT-pre b
  inlrT (true , b) = inlrT-pre b

  T : Pushout f snd → Type
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

module _ {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'}
  (f : Bool × A → Unit ⊎ B) (dB : Discrete B) (dA : Discrete A) (b₀ : B) where

  F : Bool × (Unit ⊎ A) → Unit ⊎ B
  F (false , inl tt) = inl tt
  F (true , inl tt) = inr b₀
  F (x , inr a) = f (x , a)

  g : Unit ⊎ B → B
  g (inl x) = b₀
  g (inr x) = x

  PF→P∘ₗ : (x : Unit ⊎ A) → Pushout (g ∘ f) snd
  PF→P∘ₗ (inl x) = inl b₀
  PF→P∘ₗ (inr x) = inr x

  theCoh : (a : _) → inl (g (F a)) ≡ PF→P∘ₗ (snd a)
  theCoh (false , inl x) = refl
  theCoh (true , inl x) = refl
  theCoh (false , inr x) = push (false , x)
  theCoh (true , inr x) = push (true , x)

  PF→P∘' : Pushout F snd → Pushout (g ∘ f) snd
  PF→P∘' (inl x) = inl (g x)
  PF→P∘' (inr x) = PF→P∘ₗ x
  PF→P∘' (push a i) = theCoh a i

  theCoh2 : (a : _) (b : _)
    → Path (Pushout F snd) (inl (inr (g (f (b , a))))) (inl (f (b , a)))
  theCoh2 a b with (f (b , a))
  theCoh2 a b | inl x = (push (true , inl tt)) ∙ sym (push (false , inl tt))
  ... | inr x = refl

  P∘'→PF : Pushout (g ∘ f) snd → Pushout F snd
  P∘'→PF (inl x) = inl (inr x)
  P∘'→PF (inr x) = inr (inr x)
  P∘'→PF (push (false , a) i) = (theCoh2 a false ∙ push (false , inr a)) i
  P∘'→PF (push (true , a) i) = (theCoh2 a true ∙ push (true , inr a)) i

  PFpushT : (x : _) → P∘'→PF (PF→P∘' x) ≡ x 
  PFpushT (inl (inl x)) = push (true , inl tt) ∙ sym (push (false , inl tt))
  PFpushT (inl (inr x)) = refl
  PFpushT (inr (inl x)) = push (true , inl tt)
  PFpushT (inr (inr x)) = refl
  PFpushT (push (false , inl x) i) j =
    compPath-filler (push (true , inl tt)) (sym (push (false , inl tt))) (~ i) j
  PFpushT (push (false , inr x) i) j = {!!}
  PFpushT (push (true , inl x) i) j = push (true , inl x) (i ∧ j)
  PFpushT (push (true , inr x) i) j = {!!}

  PF→P∘ : Pushout F snd → Pushout (g ∘ f) snd
  PF→P∘ (inl (inl x)) = inl b₀
  PF→P∘ (inl (inr x)) = inl x
  PF→P∘ (inr (inl x)) = inl b₀
  PF→P∘ (inr (inr x)) = inr x
  PF→P∘ (push (false , inl x) i) = inl b₀
  PF→P∘ (push (true , inl x) i) = inl b₀
  PF→P∘ (push (false , inr x) i) = {!!}
  PF→P∘ (push (true , inr x) i) = {!!}

  Is1 : Iso (Pushout F snd) (Pushout (g ∘ f) snd)
  Is1 = {!!}
  
  


TheF : {!!}
TheF = {!!}

FinPred : ∀ {m} → Fin (suc (suc m)) → Fin (suc m)
FinPred {m = m} (zero , p) = zero , p
FinPred {m = m} (suc x , p) = x , p

fone : ∀ {m} → Fin (suc (suc m))
fone {m} = suc zero , tt



CW₁DataPre : (n m : ℕ) (f : S₊ 0 × Fin (suc (suc n)) → Fin (suc (suc m)))
  → f (true , fzero) ≡ fzero
  → f (false , fzero) ≡ fone
  → Σ[ k ∈ ℕ ] Σ[ f' ∈ (S₊ 0 × Fin k → Fin (suc m)) ]
       Iso (Pushout f snd)
           (Pushout f' snd)
CW₁DataPre n m f p q = (suc n)
  , F↓
  , (compIso (subst (λ f → Iso (Pushout f snd)
                 (Pushout f* snd)) (funExt f*≡) idIso)
             {!!})
  where
  f* : S₊ 0 × Fin (suc (suc n)) → Fin (suc (suc m))
  f* (false , zero , b) = fone
  f* (true , zero , b) = fzero
  f* (x , suc a , b) = f (x , suc a , b)

  f↓ : S₊ 0 × Fin (suc (suc n)) → Fin (suc (suc m))
  f↓ (x , p) with DiscreteFin (f (x , p)) fzero
  ... | yes p₁ = fone
  ... | no ¬p = f (x , p)

  F↓ : Bool × Fin (suc n) → Fin (suc m)
  F↓ (x , p) = FinPred (f↓ (x , fsuc p))

  FinPred-lem : (b : _) (x : _) (p : _)
    → FinPred (f (b , suc x , p)) ≡ F↓ (b , x , p)
  FinPred-lem b x p with (DiscreteFin (f (b , fsuc (x , p))) fzero)
  ... | yes p₁ = cong FinPred p₁
  ... | no ¬p = refl

  FinPred-lem2 : (b : _) (x : _) (p : _) → FinPred (f* (b , suc x , p)) ≡ F↓ (b , FinPred (suc x , p))
  FinPred-lem2 false x r = FinPred-lem false x r
  FinPred-lem2 true x p = FinPred-lem true x p

  slask : (b : Bool)
    → Path (Pushout F↓ (λ r → snd r))
            (inl (FinPred (f* (b , zero , tt))))
            (inl (F↓ (b , zero , tt)))
  slask b with DiscreteFin (f (b , fsuc (0 , tt))) (0 , tt)
  slask false | yes p = refl
  slask true | yes p = refl
  slask false | no ¬p = {!!} ∙ {!!}
  slask true | no ¬p = {!¬p !}

  f*≡ : (x : _ ) → f* x ≡ f x
  f*≡ (false , zero , z) = sym q
  f*≡ (true , zero , z) = sym p
  f*≡ (false , suc y , z) = refl
  f*≡ (true , suc y , z) = refl

  pp : (b : Bool) (x : Fin (suc (suc n)))
    → Path (Pushout F↓ (λ r → snd r))
            (inl (FinPred (f* (b , x)))) (inr (FinPred x))
  pp b (zero , p) = ({!!} ∙ push (b , fzero))
  pp b (suc x , p) = (λ i → inl (FinPred-lem2 b x p i)) ∙ push (b , x , p)
  -- ((λ i → inl (FinPred-lem2 b x p i)) ∙ push (b , FinPred (x , p)))

  Pf*→ : Pushout f* snd → Pushout F↓ snd
  Pf*→ (inl x) = inl (FinPred x)
  Pf*→ (inr x) = inr (FinPred x)
  Pf*→ (push (b , zero , q) i) = {!!}
  Pf*→ (push (b , suc x' , q) i) = {!!}

  {-
  main : Iso _ _
  Iso.fun main (inl x) = inl (FinPred x)
  Iso.fun main (inr x) = inr (FinPred x)
  Iso.fun main (push (false , zero , s) i) = ({!!} ∙∙ push {!!} ∙∙ {!!}) i
  Iso.fun main (push (true , zero , s) i) = {!!}
  Iso.fun main (push (b , suc a , s) i) = push (b , a , s) i
  Iso.inv main x = {!!}
  Iso.rightInv main x = {!!}
  Iso.leftInv main x = {!!}
  -}

CW₁Data : (n m : ℕ) (f : S₊ 0 × Fin n → Fin (suc (suc m)))
  → isConnected 2 (Pushout f snd)
  → Σ[ k ∈ ℕ ] Σ[ f' ∈ (S₊ 0 × Fin k → Fin (suc m)) ]
       Iso (Pushout f snd)
           (Pushout f' snd)
CW₁Data zero m f c = ⊥.rec (snd (notAllLoops-α₀ zero m f c .fst))
CW₁Data (suc n) m f c = n , (λ x → {!xpath!}) , {!RetrFin!}
  -- n , {!!} , (compIso {!!} {!!})
  where
  t = notAllLoops-α₀ (suc n) m f c

  abstract
    x₀ : Fin (suc n)
    x₀ = fst t

    xpath : ¬ (f (true , x₀) ≡ f (false , x₀))
    xpath = snd t

  Fin0-iso : Iso (S₊ 0 × Fin (suc n)) (S₊ 0 × Fin (suc n))
  Fin0-iso = Σ-cong-iso-snd λ _ → swapFinIso x₀ fzero

  FinIso2 : Iso (Fin (suc (suc m))) (Fin (suc (suc m)))
  FinIso2 = {!!}

  Upath = isoToPath (swapFinIso x₀ fzero)

  f' : S₊ 0 × Fin (suc n) → Fin (suc (suc m))
  f' (x , zero , p) = f (x , x₀)
  f' (x , suc b , p) with (discreteℕ (suc b) (fst x₀))
  ... | yes q = f (x , fzero)
  ... | no ¬q = f (x , suc b , p)

  f'≡ : (x : _) → f (fst x , (swapFin x₀ fzero (snd x))) ≡ f' x
  f'≡ (x , zero , p) with (discreteℕ 0 (fst x₀))
  ... | yes p₁ = cong f (ΣPathP (refl , Σ≡Prop (λ _ → isProp<ᵗ) p₁))
  ... | no ¬p = cong f (ΣPathP (refl , Σ≡Prop (λ _ → isProp<ᵗ) refl))
  f'≡ (x , suc b , p) with (discreteℕ (suc b) (fst x₀))
  ... | yes p₁ = cong f (ΣPathP (refl , Σ≡Prop (λ _ → isProp<ᵗ) refl))
  ... | no ¬p = refl

  Pushout-f≡ : (Pushout f snd) ≡ (Pushout f' snd)
  Pushout-f≡ = (λ i → Pushout {A = S₊ 0 × Upath i} {B = Fin (suc (suc m))} {C = Upath i} (help i) snd)
             ∙ (λ i → Pushout (λ x → f'≡ x i) snd)
    where
    help : PathP (λ i → Bool × Upath i → Fin (suc (suc m)))
                 f
                 (f ∘ (λ a → fst a , (swapFin x₀ fzero (snd a))))
    help = toPathP (funExt λ p → transportRefl _
                   ∙ cong f (λ j → fst p , transp (λ j → Upath (~ j)) i0 (snd p))
                   ∙ cong f (cong (fst p ,_)
                       (cong (Iso.fun (swapFinIso x₀ fzero)) (transportRefl _))))


{-
  F : Σ[ x ∈ Fin n ] (¬ f (true , x) ≡ f (false , x))
  F with (allConst? DiscreteFin (λ x y → f (y , x)))
  ... | inr x = x
  ... | inl qs = {!!}
    where
    pre-help : Fin (suc (suc m)) → Type
    pre-help (zero , p) = ⊥
    pre-help (suc x , p) = Unit

    lem : (fa : _) (a : _) → f a ≡ fa → pre-help fa ≡ Unit
    lem (zero , q) (false , t) p = {!!}
    lem (zero , q) (true , t) p = {!!}
    lem (suc x , q) a p = refl

    help : Pushout f snd → Type
    help (inl x) = {!!} -- pre-help x
    help (inr x) = {!x!} -- Unit
    help (push a i) = {!!} -- lem (f a) a refl i
    -}

--   pre-help : Fin (suc (suc m)) → Type
--   pre-help (zero , p) = ⊥
--   pre-help (suc x , p) = Unit

--   lem : (fa : _) (a : _) → f a ≡ fa → pre-help fa ≡ Unit
--   lem (zero , q) a p =
--     ⊥.rec (x a (p ∙ Σ≡Prop (λ _ → isProp<ᵗ) refl))
--   lem (suc n , q) a p = refl

--   help : Pushout f snd → Type
--   help (inl x) = pre-help x
--   help (inr x) = Unit
--   help (push a i) = lem (f a) a refl i

--   Pf≅⊥ : ⊥
--   Pf≅⊥ = TR.rec isProp⊥
--                 (λ p → subst help (sym p) tt)
--                 (Iso.fun (PathIdTruncIso 1)
--                   (isContr→isProp c ∣ inl fzero ∣ ∣ inl flast ∣))

-- --   where
-- --   fSurj : (x : Fin _) → Σ[ r ∈ _ ] f r ≡ x
-- --   fSurj x = {! -- Fin→Surj? ? ? ? ?!}

-- --   ptt : Pushout f snd → Type
-- --   ptt (inl x) = Fin (suc (suc m))
-- --   ptt (inr x) = {!Fin n!}
-- --   ptt (push a i) = {!!}

-- --   module _ (s : {!!}) where



-- -- yieldsCWskel∙ : (ℕ → Type ℓ) → Type ℓ
-- -- yieldsCWskel∙ X =
-- --   Σ[ f ∈ (ℕ → ℕ) ]
-- --     Σ[ α ∈ ((n : ℕ) → ⋁gen (Fin (f (suc n))) (λ _ → S₊∙ n) → X n) ]
-- --       ((X zero ≃ Fin (f zero)) ×
-- --       (((n : ℕ) → X (suc n) ≃ cofib (α n))))

-- -- CWskel∙ : (ℓ : Level) → Type (ℓ-suc ℓ)
-- -- CWskel∙ ℓ = Σ[ X ∈ (ℕ → Type ℓ) ] (yieldsCWskel∙ X)

-- -- module CWskel∙-fields (C : CWskel∙ ℓ) where
-- --   card = C .snd .fst
-- --   A = Fin ∘ card
-- --   α = C .snd .snd .fst
-- --   e = C .snd .snd .snd .snd

-- --   ℤ[A_] : (n : ℕ) → AbGroup ℓ-zero
-- --   ℤ[A n ] = ℤ[Fin (snd C .fst n) ]

-- -- CWpt : ∀ {ℓ} → (C : CWskel∙ ℓ) → (n : ℕ) → Pointed ℓ
-- -- fst (CWpt (C , f) n) = C n
-- -- snd (CWpt (C , f) n) = f .snd .fst n (inl tt)

-- -- -- Technically, a CW complex should be the sequential colimit over the following maps
-- -- CW∙↪ : (T : CWskel∙ ℓ) → (n : ℕ) → fst T n → fst T (suc n)
-- -- CW∙↪ (X , f , α , e₀ , e₊) n x = invEq (e₊ n) (inr x)

-- -- ptCW : (T : CWskel∙ ℓ) → (n : ℕ) → fst T n
-- -- ptCW T zero = T .snd .snd .fst zero (inl tt)
-- -- ptCW T (suc n) = CW∙↪ T n (ptCW T n)

-- -- CW∙ : (T : CWskel∙ ℓ) → (n : ℕ) → Pointed ℓ
-- -- CW∙ T n = fst T n , ptCW T n

-- -- CW∙↪∙ : (T : CWskel∙ ℓ) → (n : ℕ) → CW∙ T n →∙ CW∙ T (suc n)
-- -- fst (CW∙↪∙ T n) = CW∙↪ T n
-- -- snd (CW∙↪∙ T n) = refl


-- -- -- But if it stabilises, no need for colimits.
-- -- yieldsFinCWskel∙ : (n : ℕ) (X : ℕ → Type ℓ) → Type ℓ
-- -- yieldsFinCWskel∙ n X =
-- --   Σ[ CWskel ∈ yieldsCWskel∙ X ] ((k : ℕ) → isEquiv (CW∙↪ (X , CWskel) (k +ℕ n)))

-- -- -- ... which should give us finite CW complexes.
-- -- finCWskel∙ : (ℓ : Level) → (n : ℕ) → Type (ℓ-suc ℓ)
-- -- finCWskel∙ ℓ n = Σ[ C ∈ (ℕ → Type ℓ) ] (yieldsFinCWskel∙ n C)

-- -- finCWskel→CWskel∙ : (n : ℕ) → finCWskel ℓ n → CWskel ℓ
-- -- finCWskel→CWskel∙ n C = fst C , fst (snd C)

-- -- realiseSeq∙ : CWskel∙ ℓ → Sequence ℓ
-- -- Sequence.obj (realiseSeq∙ (C , p)) = C
-- -- Sequence.map (realiseSeq∙ C) = CW∙↪ C _

-- -- realiseFinSeq∙ : (m : ℕ) → CWskel∙ ℓ → FinSequence m ℓ
-- -- realiseFinSeq∙ m C = Sequence→FinSequence m (realiseSeq∙ C)

-- -- -- realisation of CW complex from skeleton
-- -- realise∙ : CWskel∙ ℓ → Type ℓ
-- -- realise∙ C = SeqColim (realiseSeq∙ C)

-- -- realise∙∙ : CWskel∙ ℓ → Pointed ℓ
-- -- realise∙∙ C = SeqColim (realiseSeq∙ C) , incl {n = 0} (CW∙ C 0 .snd)
-- -- open import Cubical.Data.Empty as ⊥

-- -- CWskel∙→CWskel : (A : ℕ → Type ℓ) → ℕ → Type ℓ
-- -- CWskel∙→CWskel A zero = Lift ⊥
-- -- CWskel∙→CWskel A (suc n) = A n
-- -- open import Cubical.Foundations.Isomorphism


-- -- module _  (A : ℕ → Type ℓ)
-- --   (cwsk : yieldsCWskel∙ A) where

-- --   private
-- --     αs : (n : ℕ) → Fin (cwsk .fst n) × S⁻ n → CWskel∙→CWskel A n
-- --     αs (suc n) x = snd cwsk .fst n (inr x)

-- --     e0 : {!!}
-- --     e0 = {!!}

-- --     es-suc→ : (n : ℕ) → cofib (fst (snd cwsk) n) → Pushout (αs (suc n)) fst
-- --     es-suc→ n (inl x) = inl (snd cwsk .fst n (inl tt))
-- --     es-suc→ n (inr x) = inl x
-- --     es-suc→ n (push (inl x) i) = inl (fst (snd cwsk) n (inl x))
-- --     es-suc→ n (push (inr (a , b)) i) = ((({!!} ∙ λ i → inl {!snd cwsk .snd n!}) ∙ push (a , b)) ∙ {!!}) i --  ({!!} ∙ sym (push (a , b))) i
-- --     es-suc→ n (push (push a i₁) i) = {!!}

-- --     es-suc : (n : ℕ)
-- --       → Iso (cofib (fst (snd cwsk) n))
-- --              (Pushout (αs (suc n)) fst)
-- --     Iso.fun (es-suc n) = es-suc→ n
-- --     Iso.inv (es-suc n) = {!!}
-- --     Iso.rightInv (es-suc n) = {!!}
-- --     Iso.leftInv (es-suc n) = {!!}

-- --     es : (n : ℕ) → A n ≃ Pushout (αs n) (λ r → fst r)
-- --     es zero = {!!}
-- --     es (suc n) = compEquiv (snd cwsk .snd .snd n) (isoToEquiv (es-suc n))

-- --   yieldsCWskel∙→' : yieldsCWskel (CWskel∙→CWskel A)
-- --   fst yieldsCWskel∙→' = cwsk .fst
-- --   fst (snd yieldsCWskel∙→') = αs
-- --   fst (snd (snd yieldsCWskel∙→')) ()
-- --   snd (snd (snd yieldsCWskel∙→')) = {!!}

-- -- yieldsCWskel∙→ : (A : ℕ → Type ℓ)
-- --   → yieldsCWskel∙ A → yieldsCWskel (CWskel∙→CWskel A)
-- -- fst (yieldsCWskel∙→ A cwsk) = cwsk .fst
-- -- fst (snd (yieldsCWskel∙→ A cwsk)) (suc n) (x , p) = snd cwsk .fst n (inr (x , p))
-- -- fst (snd (snd (yieldsCWskel∙→ A cwsk))) ()
-- -- snd (snd (snd (yieldsCWskel∙→ A cwsk))) zero = {!!}
-- -- snd (snd (snd (yieldsCWskel∙→ A cwsk))) (suc n) =
-- --   compEquiv (cwsk .snd .snd .snd n)
-- --     (isoToEquiv {!(fst (snd (yieldsCWskel∙→ A cwsk)) (suc n))!}) -- theEq)
-- --   where
-- --   theEq→ : cofib (fst (cwsk .snd) n) → Pushout _ fst
-- --   theEq→ (inl x) = inl (cwsk .snd .fst n (inl tt))
-- --   theEq→ (inr x) = inl x
-- --   theEq→ (push (inl x) i) = inl (cwsk .snd .fst n (inl tt))
-- --   theEq→ (push (inr (a , b)) i) = ({!push ?!} ∙ push {!!} ∙ {!!}) i -- inl (cwsk .snd .fst n {!!})
-- --   theEq→ (push (push a i₁) i) = {!!}

-- --   theEq : Iso (cofib (fst (cwsk .snd) n)) (Pushout _ fst)
-- --   Iso.fun theEq = theEq→
-- --   Iso.inv theEq = {!!}
-- --   Iso.rightInv theEq x = {!!}
-- --   Iso.leftInv theEq x = {!!}


-- --  -- compEquiv {!!} {!!}


-- -- -- -- Finally: definition of CW complexes
-- -- -- isCW : (X : Type ℓ) → Type (ℓ-suc ℓ)
-- -- -- isCW {ℓ = ℓ} X = Σ[ X' ∈ CWskel ℓ ] X ≃ realise X'

-- -- -- CW : (ℓ : Level) → Type (ℓ-suc ℓ)
-- -- -- CW ℓ = Σ[ A ∈ Type ℓ ] ∥ isCW A ∥₁

-- -- -- CWexplicit : (ℓ : Level) → Type (ℓ-suc ℓ)
-- -- -- CWexplicit ℓ = Σ[ A ∈ Type ℓ ] (isCW A)

-- -- -- -- Finite CW complexes
-- -- -- isFinCW : (X : Type ℓ) → Type (ℓ-suc ℓ)
-- -- -- isFinCW {ℓ = ℓ} X =
-- -- --   Σ[ m ∈ ℕ ] (Σ[ X' ∈ finCWskel ℓ m ] X ≃ realise (finCWskel→CWskel m X'))

-- -- -- finCW : (ℓ : Level) → Type (ℓ-suc ℓ)
-- -- -- finCW ℓ = Σ[ A ∈ Type ℓ ] ∥ isFinCW A ∥₁

-- -- -- finCWexplicit : (ℓ : Level) → Type (ℓ-suc ℓ)
-- -- -- finCWexplicit ℓ = Σ[ A ∈ Type ℓ ] (isFinCW A)

-- -- -- isFinCW→isCW : (X : Type ℓ) → isFinCW X → isCW X
-- -- -- isFinCW→isCW X (n , X' , str) = (finCWskel→CWskel n X') , str

-- -- -- finCW→CW : finCW ℓ → CW ℓ
-- -- -- finCW→CW (X , p) = X , PT.map (isFinCW→isCW X) p


-- -- -- -- morphisms
-- -- -- _→ᶜʷ_ : CW ℓ → CW ℓ' → Type (ℓ-max ℓ ℓ')
-- -- -- C →ᶜʷ D = fst C → fst D

-- -- -- --the cofibre of the inclusion of X n into X (suc n)
-- -- -- cofibCW : ∀ {ℓ} (n : ℕ) (C : CWskel ℓ) → Type ℓ
-- -- -- cofibCW n C = cofib (CW↪ C n)

-- -- -- --...is basically a sphere bouquet
-- -- -- cofibCW≃bouquet : ∀ {ℓ} (n : ℕ) (C : CWskel ℓ)
-- -- --   → cofibCW n C ≃ SphereBouquet n (Fin (snd C .fst n))
-- -- -- cofibCW≃bouquet n C = Bouquet≃-gen n (snd C .fst n) (α n) e
-- -- --   where
-- -- --   s = Bouquet≃-gen
-- -- --   α = C .snd .snd .fst
-- -- --   e = C .snd .snd .snd .snd n

-- -- -- --sending X (suc n) into the cofibCW
-- -- -- to_cofibCW : (n : ℕ) (C : CWskel ℓ) → fst C (suc n) → cofibCW n C
-- -- -- to_cofibCW n C x = inr x

-- -- -- --the connecting map of the long exact sequence
-- -- -- δ-pre :  {A : Type ℓ} {B : Type ℓ'} (conn : A → B)
-- -- --   → cofib conn → Susp A
-- -- -- δ-pre conn (inl x) = north
-- -- -- δ-pre conn (inr x) = south
-- -- -- δ-pre conn (push a i) = merid a i

-- -- -- δ : (n : ℕ) (C : CWskel ℓ) → cofibCW n C → Susp (fst C n)
-- -- -- δ n C = δ-pre (CW↪ C n)

-- -- -- -- send the stage n to the realization (the same as incl, but with explicit args and type)
-- -- -- CW↪∞ : (C : CWskel ℓ) → (n : ℕ) → fst C n → realise C
-- -- -- CW↪∞ C n x = incl x

-- -- -- finCW↑ : (n m : ℕ) → (m ≥ n) → finCWskel ℓ n → finCWskel ℓ m
-- -- -- fst (finCW↑ m n p C) = fst C
-- -- -- fst (snd (finCW↑ m n p C)) = snd C .fst
-- -- -- snd (snd (finCW↑ m n p C)) k =
-- -- --   subst (λ r → isEquiv (CW↪ (fst C , snd C .fst) r))
-- -- --         (sym (+-assoc k (fst p) m) ∙ cong (k +ℕ_) (snd p))
-- -- --         (snd C .snd (k +ℕ fst p))
