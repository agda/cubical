{-# OPTIONS --safe #-}
module Cubical.Homotopy.Serre.ConnectedCovers.GeneralisingFreudenthal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.Algebra.AbGroup
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.HITs.Susp
open import Cubical.HITs.PropositionalTruncation renaming
                                                 (map to pMap; rec to pRec;
                                                  elim to pElim;
                                                  elim2 to pElim2;
                                                  rec2 to pRec2)
open import Cubical.HITs.SetTruncation renaming (map to sMap; rec to sRec;
                                                 elim to sElim;
                                                 elim2 to sElim2)
open import Cubical.HITs.Truncation renaming (elim to hTElim)

open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.EilenbergMacLane.Base renaming (elim2 to EMELim2)
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.Freudenthal
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.WhiteheadsLemma

open import Cubical.Homotopy.Serre.LastMinuteLemmas.SuspLemmas

private
  variable
    ℓ : Level

connConnMapIso : {A B : Type ℓ} (f : A → B)
  → (b : B) → Iso (fiber (sMap f) ∣ b ∣₂) (∥ Σ[ a ∈ A ] ∥ f a ≡ b ∥₁ ∥₂)
Iso.fun (connConnMapIso f b) =
  sigmaElim (λ _ → isSetSetTrunc)
            (λ a p → ∣ (a , Iso.fun PathIdTrunc₀Iso p) ∣₂)
Iso.inv (connConnMapIso f b) =
  sRec (isSetΣ isSetSetTrunc (λ x → isSetPathImplicit))
       λ p → ∣ fst p ∣₂ , (Iso.inv PathIdTrunc₀Iso (snd p))
Iso.sec (connConnMapIso f b) =
  sElim (λ _ → isSetPathImplicit)
         λ a → cong ∣_∣₂ (ΣPathP (refl , Iso.sec PathIdTrunc₀Iso (snd a)))
Iso.ret (connConnMapIso f b) =
  sigmaElim (λ x → isOfHLevelPath 2
                    (isSetΣ isSetSetTrunc (λ _ → isSetPathImplicit)) _ _)
            λ a p → ΣPathP (refl , (Iso.ret PathIdTrunc₀Iso p))

connConnMap''' : {A B : Type ℓ} (f : A → B)
  → (b : B) → fiber (sMap f) ∣ b ∣₂ ≃ ∥ Σ[ a ∈ A ] ∥ f a ≡ b ∥₁ ∥₂
connConnMap''' f b = isoToEquiv (connConnMapIso f b)

connConnMap≡ : {A B : Type ℓ} (f : A → B)
  → (b : B) → fiber (sMap f) ∣ b ∣₂ ≡ ∥ Σ[ a ∈ A ] ∥ f a ≡ b ∥₁ ∥₂
connConnMap≡ f b = ua (connConnMap''' f b)

Surjection→ContrSet : {A B : Type ℓ} (f : A → B)
                      → ((b : B) → ∥ Σ[ a ∈ A ] b ≡ f a ∥₁)
                      → isContr (∥ A ∥₂) → isContr (∥ B ∥₂)
Surjection→ContrSet f h =
  sigmaElim (λ _ → isProp→isSet isPropIsContr)
  (λ a p → ∣ f a ∣₂ , (sElim (λ _ → isSetPathImplicit)
                            λ b → Iso.inv PathIdTrunc₀Iso
                                   (pRec isPropPropTrunc
                                         (λ hb → pRec isPropPropTrunc
                                                 (λ q →
                                                   ∣ cong f q ∙ snd hb ⁻¹ ∣₁)
                                                 (Iso.fun PathIdTrunc₀Iso
                                                          (p ∣ (fst hb) ∣₂)))
                                         (h b))))

ΣConnTrunc' : {A : Type ℓ} {B : A → Type ℓ}
  → (p : Σ A (λ a → ∥ B a ∥₁)) → ∥ Σ[ q ∈ Σ A B ] (p ≡ (fst q , ∣ snd q ∣₁)) ∥₁
ΣConnTrunc' {A = A} {B = B} (a , b) =
  pElim (λ _ → isPropPropTrunc
                  {A = Σ[ q ∈ Σ A B ] ((a , b) ≡ (fst q , ∣ snd q ∣₁))})
        (λ x → ∣ (a , x) , (ΣPathP (refl , (isPropPropTrunc b ∣ x ∣₁))) ∣₁) b

ΣConnTrunc : {A : Type ℓ} {B : A → Type ℓ}
  → isConnected 2 (Σ A B)
  → isConnected 2 (Σ A (λ a → ∥ B a ∥₁))
ΣConnTrunc {A = A} {B = B} h =
  transport (λ i → isContr (propTrunc≡Trunc2 {A = Σ A (λ a → ∥ B a ∥₁)} i))
            (Surjection→ContrSet (λ p → (fst p , ∣ snd p ∣₁)) ΣConnTrunc'
                                  (transport
                                  (λ i → isContr (propTrunc≡Trunc2
                                                   {A = Σ A B}
                                                   (~ i)))
                                  h))


SetTruncConn : {A : Type ℓ} → isConnected 2 A
                            → isContr ∥ A ∥₂
SetTruncConn {A = A} hA =
  transport (λ i → isContr (propTrunc≡Trunc2 {A = A} (~ i))) hA

connConnMap : {A B : Type ℓ} (f : A → B)
           → isConnectedFun 2 f
           → isEquiv (sMap f)
equiv-proof (connConnMap f hf) =
  sElim (λ b → isProp→isSet isPropIsContr)
        λ b → transport (λ i → isContr (connConnMap≡ f b (~ i)))
                         (SetTruncConn (ΣConnTrunc (hf b)))


isConnSubtr' : (A : Type ℓ) (m n : ℕ) → isConnected (n + m) A
  → isConnected n A
isConnSubtr' A m n hA =
  isConnectedSubtr n m
  ( transport (λ i → isConnected ((+-comm n m) i) A) hA)

isConnFunSubtr' : (A B : Type ℓ) (f : A → B) (m n : ℕ)
  → isConnectedFun (n + m) f
  → isConnectedFun n f
isConnFunSubtr' A B f m n hf  =
  isConnectedFunSubtr n m f
  ( transport (λ i → isConnectedFun ((+-comm n m) i) f) hf)

-- Not sure where to find this
∘^ : {A : Type ℓ} → ℕ → (A → A) → A → A
∘^ zero f = f
∘^ (suc n) f = (∘^ n f) ∘ f

∘^' : {A : Type ℓ} → (A → A) → ℕ → A → A
∘^' f zero = f
∘^' f (suc n) = f ∘ (∘^' f n)

FromSuspToΩ=∘∙ : (A B : Pointed ℓ) (f : Susp∙ (typ A) →∙ B)
  → (fromSusp→toΩ f) ≡ (Ω→ f) ∘∙ (toSuspPointed A)
FromSuspToΩ=∘∙ A B f = refl

^Susp∙ : (n : ℕ) → Pointed ℓ → Pointed ℓ
^Susp∙ n A .fst = Susp^' n (typ A)
^Susp∙ zero A .snd = pt A
^Susp∙ (suc n) A .snd = north

Susp∙^Comm : (A : Pointed ℓ) (n : ℕ)
  → Susp∙^ (1 + n) A ≡ Susp∙ (typ (Susp∙^ n A))
Susp∙^Comm A zero = refl
Susp∙^Comm A (suc n) = Susp∙^Comm (Susp∙ (typ A)) n

Susp∙^Comm' : (A : Pointed ℓ) (n : ℕ)
  → Susp∙^ n A ≡ ^Susp∙ n A
Susp∙^Comm' A zero = refl
Susp∙^Comm' A (suc n) = Susp∙^Comm A n
                      ∙ cong (λ X → (Susp∙ (typ X))) (Susp∙^Comm' A n)

Loop^Susp^AdjunctionIso : (A B : Pointed ℓ) (n : ℕ)
  → Iso (Susp∙^ n A →∙ B) (A →∙ (Ω^ n) B)
Loop^Susp^AdjunctionIso A B zero = idIso
Loop^Susp^AdjunctionIso A B (suc n) =
  compIso
  ( Loop^Susp^AdjunctionIso (Susp∙ (typ A)) B n)
  ( invIso ΩSuspAdjointIso)

LoopSusp^AdjGambit : (A B : Pointed ℓ) (n : ℕ) (f : Susp∙^ (1 + n) A →∙ B)
  → Iso.fun (Loop^Susp^AdjunctionIso A B (1 + n)) f
  ≡ (Ω→ (Iso.fun (Loop^Susp^AdjunctionIso (Susp∙ (typ A)) B n) f))
    ∘∙ (toSuspPointed A)
LoopSusp^AdjGambit A B n f = refl

toSuspPointedω : (A : Pointed ℓ) (n : ℕ)
  → A →∙ (Ω^ (1 + n)) (Susp∙^ (1 + n) A)
toSuspPointedω A zero = toSuspPointed A
toSuspPointedω A (suc n) =
  Ω→ (toSuspPointedω (Susp∙ (typ A)) n) ∘∙ toSuspPointed A

SuspUnitIso : Iso (Susp Unit) Unit
Iso.fun SuspUnitIso north = tt
Iso.fun SuspUnitIso south = tt
Iso.fun SuspUnitIso (merid tt i) = tt
Iso.inv SuspUnitIso tt = north
Iso.sec SuspUnitIso tt = refl
Iso.ret SuspUnitIso north = refl
Iso.ret SuspUnitIso south = merid tt
Iso.ret SuspUnitIso (merid tt i) = λ j → merid tt (i ∧ j)

SuspUnitEquiv : (Susp Unit) ≃ Unit
SuspUnitEquiv = isoToEquiv SuspUnitIso

SuspUnit≡ : (Susp Unit) ≡ Unit
SuspUnit≡ = ua SuspUnitEquiv

SuspUnit≡∙ : Path (Pointed ℓ-zero) (Susp Unit , north) (Unit , tt)
SuspUnit≡∙ = ua∙ SuspUnitEquiv refl

SuspFunUnit' : (A : Type ℓ) (a : Susp A)
 → (transport (λ i → Susp A → SuspUnit≡ i) (suspFun (λ (a : A) → tt)) a)
  ≡ (λ (a : Susp A) → tt) a
SuspFunUnit' A a = isPropUnit _ _

SuspFunUnit : (A : Type ℓ)
  → PathP (λ i → (Susp A → SuspUnit≡ i))
           (suspFun (λ (a : A) → tt)) (λ (a : _) → tt)
SuspFunUnit A = toPathP (funExt (SuspFunUnit' A))

SuspUnitFun≡ : (A : Type ℓ)
  → Path (Σ[ X ∈ Pointed ℓ-zero ] (Susp A → (fst X)))
  ((Susp Unit , north) , suspFun (λ (a : A) → tt))
  ((Unit , tt) , (λ (a : Susp A) → tt))
SuspUnitFun≡ A = ΣPathP (SuspUnit≡∙ , (SuspFunUnit A))

ΠSuspUnit : (A : Susp Unit → Type ℓ) → ((b : Susp Unit) → A b) ≃ A north
ΠSuspUnit =
  transport (λ i → (A : fst (SuspUnit≡∙ (~ i)) → Type _)
                 → ((b : fst (SuspUnit≡∙ (~ i))) → A b)
                  ≃ A (snd (SuspUnit≡∙ (~ i))))
            ΠUnit

+∸' : (m n : ℕ) → (m < n) → m + (n ∸ m) ≡ n
+∸' m n (zero , p) =
  cong (λ l → (m + (l ∸ m))) (sym p)
  ∙ cong (m +_) (+∸ 1 m)
  ∙ +-comm m 1
  ∙ p
+∸' m n (suc k , p) =
  cong (λ l → (m + (l ∸ m))) (sym p)
  ∙ cong (λ l → (m + (suc l ∸ m))) (+-assoc k 1 m)
  ∙ cong (m +_) (+∸ (1 + k + 1) m)
  ∙ +-comm m (suc (k + 1))
  ∙ cong suc (sym (+-assoc k 1 m))
  ∙ p

2+2n∸ : (m n : ℕ) → (m ≤ n)
                  → (1 + (n + (1 + n) ∸ m)) ≡ ((1 + n) + (1 + n) ∸ m)
2+2n∸ m n (k , p) =
  ≤-∸-suc {m = m} {n = n + (1 + n)} (≤-trans (k , p) ≤SumLeft)

<2+2n : (m n : ℕ) → ((suc m) ≤ n)
                  → m < suc (n + suc n)
<2+2n m n p = <-trans p ≤SumLeft

2+n+2+n=2+n+1+n+1 : (n : ℕ) → (1 + (1 + n)) + (1 + (1 + n))
                             ≡ ((1 + (1 + n)) + (1 + n)) + 1
2+n+2+n=2+n+1+n+1 n = ((+-assoc (1 + (1 + n)) (1 + n) 1 ⁻¹)
                      ∙ cong (λ m → (suc (suc (n + (suc m))))) (+-comm n 1)) ⁻¹

toSuspPointedωConnected' : {A : Pointed ℓ} (m n : ℕ)
  → isConnected (2 + n) (typ A)
  → isConnectedFun ((1 + n) + (1 + n)) (fst (toSuspPointedω A m))
toSuspPointedωConnected' zero n hA = isConnectedσ n hA
toSuspPointedωConnected' {A = A} (suc m) n hA =
  isConnectedComp (fst (Ω→ (toSuspPointedω (Susp∙ (typ A)) m))) (toSusp A)
                  (suc (n + suc n)) (isConnectedΩ→ (suc (n + suc n))
                  (toSuspPointedω (Susp∙ (typ A)) m)
                  (isConnFunSubtr' _ _ _ 1 _
                   (transport (λ i → isConnectedFun (2+n+2+n=2+n+1+n+1 n i)
                              (fst (toSuspPointedω (Susp∙ (typ A)) m)))
                  (toSuspPointedωConnected' m (1 + n)
                    (isConnectedSusp (suc (suc n)) hA)))))
                  (isConnectedσ n hA)

LoopSusp^AdjGambit' : (A B : Pointed ℓ) (n : ℕ) (f : Susp∙^ (1 + n) A →∙ B)
  → Iso.fun (Loop^Susp^AdjunctionIso A B (1 + n)) f
  ≡  ((Ω^→ (1 + n)) f) ∘∙ toSuspPointedω A n
LoopSusp^AdjGambit' A B zero f = refl
LoopSusp^AdjGambit' A B (suc n) f =
  (cong (λ g → Ω→ g ∘∙ (toSuspPointed A))
        (LoopSusp^AdjGambit' (Susp∙ (typ A)) B n f))
  ∙ (cong (_∘∙ (toSuspPointed A)) (Ω→∘∙ (Ω^→ (1 + n) f)
                                         (toSuspPointedω (Susp∙ (typ A)) n)))
  ∙ ∘∙-assoc (Ω^→ (2 + n) f)
             (Ω→ (toSuspPointedω (Susp∙ (typ A)) n))
             (toSuspPointed A)

ToSusp∙^ : (A : Pointed ℓ) (n : ℕ)
  → A →∙ (Ω^ (1 + n)) (Susp∙^ (1 + n) A)
ToSusp∙^ A n =
  Iso.fun
  (Loop^Susp^AdjunctionIso A (Susp∙^ (1 + n) A) (1 + n))
  (id∙ (Susp∙^ (1 + n) A))

CharInv : (A B : Pointed ℓ)
  → (f : Susp∙ (typ A) →∙ B)
  → fst (Iso.inv (ΩSuspAdjointIso {A = A} {B = B}) f)
   ≡ (fst (Ω→ f)) ∘ toSusp A
CharInv A B f = refl

CharArg : (A B : Pointed ℓ)
  → (f : A →∙ Ω B)
  → (fst f) ≡ fst (Ω→ (Iso.fun ΩSuspAdjointIso f)) ∘ toSusp A
CharArg A B f = (cong fst (Iso.ret ΩSuspAdjointIso f)) ⁻¹
              ∙ CharInv A B (Iso.fun ΩSuspAdjointIso f)

hLevel→hLevelFib : (A B : Type ℓ) (n : ℕ) (f : A → B)
  → isOfHLevel n A → isOfHLevel n B
  → ∀ (b : B) → isOfHLevel n (fiber f b)
hLevel→hLevelFib A B n f hA hB b =
  isOfHLevelΣ n hA
  (λ a → isOfHLevelPath n hB (f a) b)

Connected→isSetFibersInh : (A B : Type ℓ) (f : A → B)
  → isConnectedFun 2 f
  → ∀ (b : B) → fiber (map {n = 2} f) ∣ b ∣ₕ
Connected→isSetFibersInh A B f cf b =
  rec
  (hLevel→hLevelFib
   (∥ A ∥ 2) (∥ B ∥ 2) 2
   (map {n = 2} f)
   (isOfHLevelTrunc 2) (isOfHLevelTrunc 2) ∣ b ∣ₕ)
  (λ a → ∣ fst a ∣ₕ , cong ∣_∣ (snd a)) (fst (cf b))

Connected→PropFiberAux : (A B : Type ℓ) (f : A → B) (b : B)
  → isContr (∥ fiber f b ∥ 2)
  → (p p' : fiber f b) → ∥ fst p ≡ fst p' ∥ 1
Connected→PropFiberAux A B f b (cfx , cfp) p p' =
  hTElim {A = p ≡ p'} {n = 1} {B = λ _ → ∥ fst p ≡ fst p' ∥ (suc zero)}
  (λ r → isOfHLevelTrunc 1) (λ r → ∣ fst (PathPΣ r) ∣)
  (transport (PathIdTrunc 1) (sym (cfp ∣ p ∣) ∙ cfp ∣ p' ∣))

Connected→isPropFstFiber : (A B : Type ℓ) (f : A → B)
  → isConnectedFun 2 f
  → ∀ (b : B) (a a' : ∥ A ∥ 2) → map f a ≡ ∣ b ∣ → map f a' ≡ ∣ b ∣
  → a ≡ a'
Connected→isPropFstFiber A B f cf b =
  elim2 (λ a a' → isOfHLevelΠ 2 λ p → isOfHLevelΠ 2 λ q
                → isOfHLevelPath 2 (isOfHLevelTrunc 2) a a')
        λ a a' → transport
                  (λ i → (PathIdTrunc {a = f a} {b = b} 1 (~ i))
                        → (PathIdTrunc {a = f a'} {b = b} 1 (~ i))
                        → (PathIdTrunc {a = a} {b = a'} 1 (~ i)))
                  (hTElim (λ p → isOfHLevelΠ 1 λ q → isOfHLevelTrunc 1)
                          λ p →
                          hTElim (λ q → isOfHLevelTrunc 1)
                          λ q → Connected→PropFiberAux A B f b
                                 (cf b) (a , p) (a' , q))

Connected→isPropFibersMap : (A B : Type ℓ) (f : A → B)
  → isConnectedFun 2 f
  → ∀ (b : B) → isProp (fiber (map {n = 2} f) ∣ b ∣ₕ)
Connected→isPropFibersMap A B f cf b (a , p) (a' , q) =
  ΣPathP (Connected→isPropFstFiber A B f cf b a a' p q ,
          (toPathP (isOfHLevelTrunc 2 _ _ _ _)))

Connected→FibersContr : (A B : Type ℓ) (f : A → B)
  → isConnectedFun 2 f
  → ∀ (b : B) → isContr (fiber (map {n = 2} f) ∣ b ∣ₕ)
Connected→FibersContr A B f cf b =
  inhProp→isContr (Connected→isSetFibersInh A B f cf b)
                   (Connected→isPropFibersMap A B f cf b)

Connected→mapEquiv : (A B : Type ℓ) (f : A → B)
  → isConnectedFun 2 f
  → ∀ (b : ∥ B ∥ 2) → isContr (fiber (map {n = 2} f) b)
Connected→mapEquiv A B f cf =
  hTElim
  (λ b → isOfHLevelSuc 1 isPropIsContr)
  (Connected→FibersContr A B f cf)

2n+4-1+n=3+n : (n : ℕ)
  → (1 + (suc n)) + (1 + (suc n)) ∸ (1 + n) ≡ 2 + (1 + n)
2n+4-1+n=3+n n =
  cong (λ k → suc k ∸ n) (+-comm n (suc (suc n)))
  ∙ (suc∸-fst (suc (suc (n + n))) n (suc n , cong suc (+-suc n n)) ⁻¹
  ∙ cong suc (sym (suc∸-fst (suc (n + n)) n (n , +-suc n n))
  ∙ cong suc ((suc∸-fst' (n + n) n (n , refl)) ⁻¹
  ∙ cong suc ((≤-+∸ {m = n} {n} {n} (0 , refl)) ⁻¹))))
  ∙ cong (3 + n +_) (n∸n n) ∙ +-assoc 3 n 0 ∙ cong (3 +_) (+-zero n)
  where
  lem : (n : ℕ) → suc n ∸ n ≡ 1
  lem zero = refl
  lem (suc n) = lem n

  suc∸-fst' : (n m : ℕ) → m ≤ n → suc (n ∸ m) ≡ (suc n) ∸ m
  suc∸-fst' n m (zero , q) =
    cong suc (cong (n ∸_) q)
    ∙ (cong suc (n∸n n) ∙ lem n ⁻¹)
    ∙ cong (suc n ∸_) (q ⁻¹)
  suc∸-fst' n m (suc p , q) = suc∸-fst n m (p , +-suc p m ∙ q)

LoopSuspIsoConnected : (A B : Pointed ℓ) (n : ℕ)
  → (f : A →∙ (Ω^ (1 + n)) B) → isEquiv (fst f)
  → isConnected 2 (typ A)
  → isConnectedFun 3
     (fst ((Ω^→ (1 + n))
     (Iso.inv (Loop^Susp^AdjunctionIso A B (1 + n)) f)))
LoopSuspIsoConnected A B zero f hf hA =
  isConnectedFunCancel (toSusp A) (fst (Ω→ (Iso.fun ΩSuspAdjointIso f))) 2
  (isConnectedσ 0 hA)
  (transport (λ i → isConnectedFun 3 (CharArg A B f i))
  (isEquiv→isConnected (fst f) hf 3))
LoopSuspIsoConnected A B (suc n) f hf hA =
  isConnectedFunCancel (fst (toSuspPointedω A (1 + n)))
  (fst (Ω^→ (2 + n) (Iso.inv (Loop^Susp^AdjunctionIso A B (2 + n)) f)))
  2
  (toSuspPointedωConnected' (1 + n) 0 hA)
  (isEquiv→isConnected
    (fst (((Ω^→ (2 + n)) (Iso.inv (Loop^Susp^AdjunctionIso A B (2 + n)) f))
    ∘∙ toSuspPointedω A (1 + n)))
    (transport
      ((λ i → isEquiv (fst
               (Iso.sec (Loop^Susp^AdjunctionIso A B (2 + n)) f (~ i))))
      ∙ (λ i → isEquiv
                 (fst (LoopSusp^AdjGambit' A B (1 + n)
                 (Iso.inv (Loop^Susp^AdjunctionIso A B (2 + n)) f) i)))) hf) 3)

LoopSuspIsoπFunEquiv : (A B : Pointed ℓ) (n : ℕ)
  → (f : A →∙ (Ω^ (1 + n)) B) → isEquiv (fst f)
  → isConnected 2 (typ A)
  → isEquiv (πFun (1 + n) (Iso.inv (Loop^Susp^AdjunctionIso A B (1 + n)) f))
LoopSuspIsoπFunEquiv A B n f hf hA =
  connConnMap
    (fst ((Ω^→ (2 + n)) (Iso.inv (Loop^Susp^AdjunctionIso A B (1 + n)) f)))
    (isConnectedΩ→ 2
     ((Ω^→ (1 + n)) (Iso.inv (Loop^Susp^AdjunctionIso A B (1 + n)) f))
     (LoopSuspIsoConnected A B n f hf hA))

LoopSuspIsoπFunEquiv' : (G : AbGroup ℓ) (X : Pointed ℓ) (n : ℕ)
  → (f : (EM∙ G 1) →∙ (Ω^ (1 + n)) X) → isEquiv (fst f)
  → isEquiv (πFun (1 + n)
             (fst (invEquiv
             (isoToEquiv (Loop^Susp^AdjunctionIso (EM∙ G 1) X (1 + n)))) f))
LoopSuspIsoπFunEquiv' G X n f hf =
    LoopSuspIsoπFunEquiv (EM∙ G 1) X n f hf (isConnectedEM {G' = G} 1)
