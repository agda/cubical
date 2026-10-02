{-# OPTIONS --lossy-unification --safe #-}
module Cubical.Homotopy.Serre.ConnectedCovers.UsefulLemmas where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism hiding (isIsoToIso)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path

open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.GroupPath
open import Cubical.Algebra.Group.Instances.Unit
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

open import Cubical.Data.Nat renaming (elim to natElim)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Cubical.HITs.EilenbergMacLane1 renaming (rec to recEM1)
open import Cubical.HITs.SetTruncation
              renaming (rec to recSetTrunc ; elim to elimSetTrunc ;
                        elim2 to elim2SetTrunc ; map to mapSetTrunc ;
                        rec2 to sRec2)
open import Cubical.HITs.Susp
open import Cubical.HITs.Truncation
              renaming (rec to recTrunc ; elim to elimTrunc)

open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.EilenbergMacLane.Base
              renaming (elim to elimEM)
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.Freudenthal
open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.WhiteheadsLemma

open import Cubical.Homotopy.Serre.HomotopyGroups

open import Cubical.Homotopy.Serre.FiberOrCofiberSequences.Base

private
  variable
    ℓ : Level

hTr : (A : Type ℓ) (n : ℕ) → A → ∥ A ∥ n
hTr A n a = ∣ a ∣ₕ

isSetGroup : (G : Group ℓ) → isSet (typ G)
isSetGroup G = GroupStr.is-set (snd G)

congSym : {A B : Type ℓ} {a b : A} (f : A → B) (p : a ≡ b)
       → (cong f p) ⁻¹ ≡ cong f (p ⁻¹)
congSym f = J (λ b p → (cong f p) ⁻¹ ≡ cong f (p ⁻¹))
              refl

-- not sure where to find this
isIso→isIsotransport∙ : {A B C : Pointed ℓ} {f : A →∙ B} (p : B ≡ C)
  → isIso (fst f) → isIso (fst (transport (λ i → A →∙ (p i)) f))
isIso→isIsotransport∙ {A = A} {f = f} =
  J (λ X p → isIso (fst f) → isIso (fst (transport (λ i → A →∙ (p i)) f)))
     λ hf → transport (λ i → isIso (fst (transportRefl f (~ i)))) hf

funExt⁻Dist : {A B : Type ℓ} {f g : A → B}
              (p : f ≡ g) {h : A → B} (q : g ≡ h) {a : A}
           → funExt⁻ (p ∙ q) a ≡ funExt⁻ p a ∙ funExt⁻ q a
funExt⁻Dist {A = A} {B = B} {f = f} =
  J
  (λ g p → {h : A → B} (q : g ≡ h) {a : A}
         → funExt⁻ (p ∙ q) a ≡ funExt⁻ p a ∙ funExt⁻ q a)
  (J
   (λ h q → {a : A}
          → funExt⁻ (refl ∙ q) a ≡ funExt⁻ {f = f} {g = f} refl a ∙ funExt⁻ q a)
   refl)

funExt⁻Cong : {A B C : Type ℓ} (k : B → C) {f g : A → B}
              (p : f ≡ g) {a : A}
           → funExt⁻ (cong (k ∘_) p) a ≡ cong k (funExt⁻ p a)
funExt⁻Cong {A = A} k {f = f} =
  J
  (λ g p → {a : A}
         → funExt⁻ (cong (k ∘_) p) a ≡ cong k (funExt⁻ p a))
  refl

funExt⁻Sym : {A B : Type ℓ} {f g : A → B}
             (p : g ≡ f) {a : A}
          → funExt⁻ (p ⁻¹) a ≡ (funExt⁻ p a) ⁻¹
funExt⁻Sym {A = A} =
  J
  (λ g p → {a : A}
         → funExt⁻ (p ⁻¹) a ≡ (funExt⁻ p a) ⁻¹)
  refl

ContrFunEq : {X Y : Type ℓ} → isContr Y → (f g : X → Y)
  → f ≡ g
ContrFunEq (y , hy) f g = funExt (λ x → hy (f x) ⁻¹ ∙ hy (g x))

isIso→isEquiv : {X Y : Type ℓ} (f : X → Y) → isIso f → isEquiv f
isIso→isEquiv f hf = isoToIsEquiv
                      (iso f (fst hf) (fst (snd hf)) (snd (snd hf)))

Iso→isIso : {X Y : Type ℓ} (ISO : Iso X Y) → isIso (Iso.fun ISO)
fst (Iso→isIso ISO) = Iso.inv ISO
fst (snd (Iso→isIso ISO)) = Iso.sec ISO
snd (snd (Iso→isIso ISO)) = Iso.ret ISO

isEquiv→isIso : {X Y : Type ℓ} (f : X → Y) → isEquiv f → isIso f
isEquiv→isIso f hf = Iso→isIso (equivToIso (f , hf))

--don't know where to find this
isIsoToIso : {X Y : Type ℓ} (f : X → Y) → isIso f → Iso X Y
Iso.fun (isIsoToIso f (invf , secf , retf)) = f
Iso.inv (isIsoToIso f (invf , secf , retf)) = invf
Iso.sec (isIsoToIso f (invf , secf , retf)) = secf
Iso.ret (isIsoToIso f (invf , secf , retf)) = retf

342-case1 : {X Y Z : Type ℓ} (f : X → Y) (g : Y → Z)
  → isIso f → isIso (g ∘ f) → isIso g
fst (342-case1 f g (invf , secf , retf) (invgf , secgf , retgf)) =
  f ∘ invgf
fst (snd (342-case1 f g (invf , secf , retf) (invgf , secgf , retgf))) z =
  secgf z
snd (snd (342-case1 f g (invf , secf , retf) (invgf , secgf , retgf))) y =
  cong (λ y' → f (invgf (g y'))) (secf y ⁻¹)
  ∙ cong (λ x → f x) (retgf (invf y))
  ∙ secf y

342-case2 : {X Y Z : Type ℓ} (f : X → Y) (g : Y → Z)
  → isIso (g ∘ f) → isIso g → isIso f
fst (342-case2 f g (invgf , secgf , retgf) (invg , secg , retg)) =
  invgf ∘ g
fst (snd (342-case2 f g (invgf , secgf , retgf) (invg , secg , retg))) y =
  retg (f (invgf (g y))) ⁻¹
  ∙ cong (λ z → invg z) (secgf (g y))
  ∙ retg y
snd (snd (342-case2 f g (invgf , secgf , retgf) (invg , secg , retg))) x =
  retgf x

342-case3 : {X Y Z : Type ℓ} (f : X → Y) (g : Y → Z)
  → isIso g → isIso f → isIso (g ∘ f)
fst (342-case3 f g (invg , secg , retg) (invf , secf , retf)) =
  invf ∘ invg
fst (snd (342-case3 f g (invg , secg , retg) (invf , secf , retf))) z =
  cong g (secf (invg z))
  ∙ secg z
snd (snd (342-case3 f g (invg , secg , retg) (invf , secf , retf))) x =
  cong invf (retg (f x))
  ∙ retf x

Ω→id∙ : {A : Pointed ℓ} → Ω→ (id∙ A) ≡ id∙ (Ω A)
Ω→id∙ = ΣPathP (funExt (J (λ a p → refl ∙∙ p ∙∙ refl ≡ p) (∙∙lCancel refl))
               , toPathP
                 (transportPathLemmaLeft
                  (J (λ a p → refl ∙∙ p ∙∙ refl ≡ p) (∙∙lCancel refl)
                  refl)
                  (∙∙lCancel refl)
                 ∙ cong (λ p → p ⁻¹ ∙ ∙∙lCancel refl)
                   (JRefl (λ a p → refl ∙∙ p ∙∙ refl ≡ p) (∙∙lCancel refl))
                 ∙ lCancel (∙∙lCancel refl)))

UnitUnitIsIso : (f : Unit* {ℓ} → Unit*) → isIso f
fst (UnitUnitIsIso f) = f
fst (snd (UnitUnitIsIso f)) (lift tt) = refl
snd (snd (UnitUnitIsIso f)) (lift tt) = refl

UnitUnitIso : (f : Unit* {ℓ} → Unit*) → Iso Unit* Unit*
Iso.fun (UnitUnitIso f) = f
Iso.inv (UnitUnitIso f) = fst (UnitUnitIsIso f)
Iso.sec (UnitUnitIso f) = fst (snd (UnitUnitIsIso f))
Iso.ret (UnitUnitIso f) = snd (snd (UnitUnitIsIso f))

UnitUnitIsEquiv : (f : Unit* {ℓ} → Unit*) → isEquiv f
UnitUnitIsEquiv f = isoToIsEquiv (UnitUnitIso f)

ContrContrIsEquiv : (A B : Type ℓ) → isContr A → isContr B → (f : A → B)
  → isEquiv f
ContrContrIsEquiv A B hA hB =
  transport
  (λ i → ((f : ((isContr→≡Unit* hA) (~ i)) → (isContr→≡Unit* hB) (~ i))
       → isEquiv f))
  UnitUnitIsEquiv

isIso→isIsoRecTrunc : {X Y : Type ℓ} (n : ℕ) (f : X → Y) (hY : isOfHLevel n Y)
  → isIso f → isIso (recTrunc hY f)
isIso→isIsoRecTrunc zero f hY hf =
  isEquiv→isIso _ (ContrContrIsEquiv _ _ isContrUnit* hY _)
fst (isIso→isIsoRecTrunc (suc n) f hY (finv , fsec , fret)) = ∣_∣ₕ ∘ finv
fst (snd (isIso→isIsoRecTrunc (suc n) f hY (finv , fsec , fret))) y =
  fsec y
snd (snd (isIso→isIsoRecTrunc (suc n) f hY (finv , fsec , fret))) =
  elimTrunc (λ _ → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _)
            λ x → cong ∣_∣ₕ (fret x)

isIso→isIsoMapSet : {X Y : Type ℓ} (f : X → Y)
   → isIso f → isIso (mapSetTrunc f)
fst (isIso→isIsoMapSet f (finv , fsec , fret)) = mapSetTrunc finv
fst (snd (isIso→isIsoMapSet f (finv , fsec , fret))) =
  elimSetTrunc
  (λ y → isSetPathImplicit)
  (λ y → cong ∣_∣₂ (fsec y))
snd (snd (isIso→isIsoMapSet f (finv , fsec , fret))) =
  elimSetTrunc
  (λ x → isSetPathImplicit)
  (λ x → cong ∣_∣₂ (fret x))

setMap∘ : {X Y Z : Type ℓ} (g : Y → Z) (f : X → Y)
  → mapSetTrunc (g ∘ f) ≡ (mapSetTrunc g) ∘ (mapSetTrunc f)
setMap∘ g f =
  funExt
  (elimSetTrunc
   (λ x → isSetPathImplicit)
   λ x → refl)

SetMapRecNeut : (X Y : Type ℓ) (n : ℕ) (f : X → Y)
  (hY : isOfHLevel n Y)
  → mapSetTrunc (recTrunc hY f) ∘ mapSetTrunc ∣_∣ₕ ≡ mapSetTrunc f
SetMapRecNeut X Y zero f hY = funExt (elimSetTrunc (λ _ → isSetPathImplicit)
                                     λ x → cong ∣_∣₂ (snd hY (f x)))
SetMapRecNeut X Y (suc n) f hY = funExt (elimSetTrunc (λ _ → isSetPathImplicit)
                                                       λ _ → refl)

isOfHLevelSetTrunc : {A : Type ℓ} (n : ℕ)
  → isOfHLevel (2 + n) ∥ A ∥₂
isOfHLevelSetTrunc zero = isSetSetTrunc
isOfHLevelSetTrunc (suc n) = isOfHLevelSuc (suc (suc n)) (isOfHLevelSetTrunc n)

iso∣-∣ₕ : {A : Type ℓ} (n : ℕ)
   → isIso (mapSetTrunc (∣_∣ₕ {A = A} {n = 2 + n}))
fst (iso∣-∣ₕ n) =
  recSetTrunc isSetSetTrunc (recTrunc (isOfHLevelSetTrunc n) ∣_∣₂)
fst (snd (iso∣-∣ₕ n)) =
  elimSetTrunc (λ _ → isSetPathImplicit)
  (elimTrunc (λ a → isOfHLevelPath (2 + n) (isOfHLevelSetTrunc n) _ _)
  λ a → refl)
snd (snd (iso∣-∣ₕ n)) =
  elimSetTrunc (λ _ → isSetPathImplicit) (λ _ → refl)

correction≡ : {A : Type ℓ} {a a' : A} (n : ℕ)
       → Path (∥ A ∥ (1 + n)) ∣ a ∣ ∣ a' ∣
       → hLevelTrunc n (a ≡ a')
correction≡ n = Iso.fun (PathIdTruncIso n)

correction≡Refl : {A : Type ℓ} {a : A} (n : ℕ)
   → ∣ refl {x = a} ∣ₕ ≡ correction≡ n refl
correction≡Refl zero = refl
correction≡Refl (suc n) = cong ∣_∣ₕ (transportRefl refl ⁻¹)

correction≡∙ : {A : Type ℓ} {a a' : A} (n : ℕ) (p : a ≡ a')
            → (Path (∥ A ∥ (1 + n)) ∣ a ∣ ∣ a' ∣ , cong ∣_∣ p)
            →∙ hLevelTrunc∙ n ((a ≡ a') , p)
correction≡∙ {A = A} {a = a} zero p =
  (correction≡ zero) , refl
correction≡∙ {A = A} {a = a} (suc n) =
  J (λ a' p →
       (Path (∥ A ∥ (2 + n)) ∣ a ∣ ∣ a' ∣ , cong ∣_∣ p)
       →∙ hLevelTrunc∙ (1 + n) ((a ≡ a') , p))
    ((correction≡ (suc n)) , (cong ∣_∣ (transportRefl refl)))

1+m+n≡ : (m n : ℕ) → (suc m) + n ≡ m + (suc n)
1+m+n≡ m n = cong suc (+-comm m n) ∙ +-comm (suc n) m

hLevelΩ^ : {B : Pointed ℓ} (m n : ℕ)
        → isOfHLevel (m + n) (typ B)
        → isOfHLevel n (typ ((Ω^ m) B))
hLevelΩ^ zero n hB = hB
hLevelΩ^ (suc zero) n hB = isOfHLevelPath' n hB _ _
hLevelΩ^ {B = B} (suc (suc m)) n hB =
 hLevelΩ^ 1 n (hLevelΩ^ (suc m) (suc n)
  (transport (λ i → isOfHLevel (suc (1+m+n≡ m n i)) (typ B)) hB))

recTrunc∙ : {A B : Pointed ℓ} (m : ℕ)
         → isOfHLevel m (typ B)
         → (A →∙ B)
         → (hLevelTrunc∙ m A →∙ B)
recTrunc∙ zero hB f = (recTrunc hB (fst f)) , snd hB _
recTrunc∙ (suc m) hB f = (recTrunc hB (fst f)) , snd f

hLevelTrunc→∙ : {A : Pointed ℓ} (m n : ℕ)
             → ((Ω^ (suc m)) (hLevelTrunc∙ ((suc m) + n) A))
             →∙ ((Ω^ (suc m)) (hLevelTrunc∙ (m + (suc n)) A))
hLevelTrunc→∙ {A = A} zero n = id∙ (Ω (hLevelTrunc∙ (suc n) A))
hLevelTrunc→∙ {A = A} (suc m) n =
  transport (λ i → (Ω^ (suc (suc m))) (hLevelTrunc∙ ((suc (suc m)) + n) A)
             →∙ ((Ω^ (suc (suc m))) (hLevelTrunc∙ (1+m+n≡ (suc m) n i) A)))
           (id∙ ((Ω^ (suc (suc m))) (hLevelTrunc∙ ((suc (suc m)) + n) A)))

isIsoHLevelTrunc→∙ : {A : Pointed ℓ} (m n : ℕ)
  → isIso (fst (hLevelTrunc→∙ {A = A} m n))
isIsoHLevelTrunc→∙ zero n = Iso→isIso idIso
isIsoHLevelTrunc→∙ {A = A} (suc m) n =
  isIso→isIsotransport∙
  {f = id∙ ((Ω^ (suc (suc m))) (hLevelTrunc∙ ((suc (suc m)) + n) A))}
  (λ i → ((Ω^ (suc (suc m))) (hLevelTrunc∙ (1+m+n≡ (suc m) n i) A)))
  (Iso→isIso idIso)

correction : {A : Pointed ℓ} (m n : ℕ)
          → (((Ω^ m) (hLevelTrunc∙ (m + n) A))
          →∙ hLevelTrunc∙ n ((Ω^ m) A))
correction {A = A} zero n = id∙ (hLevelTrunc∙ n A)
correction (suc zero) n = correction≡∙ n refl
correction {A = A} (suc (suc m)) n =
  (correction {A = (Ω^ (1 + m)) A} 1 n
  ∘∙ Ω→ (correction (suc m) (suc n)))
  ∘∙ hLevelTrunc→∙ (suc m) n

fstCorrection1EqCorrection≡ : {A : Pointed ℓ} (n : ℕ) {a' : typ A}
    (p : pt A ≡ a')
  → fst (correction≡∙ {A = typ A} n p)
   ≡ correction≡ {A = (typ A)} {a = (pt A)} {a' = a'} n
fstCorrection1EqCorrection≡ zero p = refl
fstCorrection1EqCorrection≡ {A = A} (suc n) =
  J (λ a' p → fst (correction≡∙ {A = typ A} (suc n) p)
             ≡ correction≡ {A = typ A} {a = pt A} {a' = a'} (suc n))
    (transportRefl (correction≡ (suc n)))

correctionEqCorrection : {A : Pointed ℓ} (m n : ℕ)
  → ((correction {A = (Ω^ m) A} 1 n
     ∘∙ Ω→ (correction {A = A} m (suc n)))
     ∘∙ hLevelTrunc→∙ {A = A} m n)
   ≡ correction (suc m) n
correctionEqCorrection {A = A} zero n =
  cong (λ p → (correction≡∙ n refl
                ∘∙ p)
                ∘∙ id∙ (Ω (hLevelTrunc∙ (suc n) A)))
        Ω→id∙
  ∙ ∘∙-idˡ _
  ∙ ∘∙-idˡ _
correctionEqCorrection (suc m) n = refl

isIsoCorrection : {A : Pointed ℓ} (m n : ℕ)
               → isIso (fst (correction {A = A} m n))
isIsoCorrection zero n = Iso→isIso idIso
isIsoCorrection {A = A} (suc zero) n =
  transport (λ i → isIso
                    (fstCorrection1EqCorrection≡ n {a' = pt A} refl (~ i)))
            (Iso→isIso (PathIdTruncIso n))
isIsoCorrection {A = A} (suc (suc m)) n =
  Iso→isIso (compIso
    (isIsoToIso (fst (hLevelTrunc→∙ (suc m) n))
                (isIsoHLevelTrunc→∙ (suc m) n))
    (compIso
      (isIsoToIso
        (fst (Ω→ (correction (suc m) (suc n))))
        (isEquiv→isIso (fst (Ω→ (correction (suc m) (suc n))))
          (isEquivΩ→ (correction (suc m) (suc n))
                      (isIso→isEquiv
                      (fst (correction (suc m) (suc n)))
                      (isIsoCorrection (suc m) (suc n))))))
      (isIsoToIso (fst (correction {A = (Ω^ (suc m)) A} 1 n))
                  (isIsoCorrection {A = (Ω^ (suc m)) A} 1 n))))

hLevelNatComm : {A : Type ℓ} (m n : ℕ)
             → isOfHLevel ((suc m) + n) A
             → isOfHLevel (m + (suc n)) A
hLevelNatComm {A = A} m n hA =
  transport (λ i → isOfHLevel (1+m+n≡ m n i) A) hA

Ω→NatComm' : {A B : Pointed ℓ} (f : A →∙ B) (m n : ℕ) {n' : ℕ} (p : n ≡ n')
              (hB : isOfHLevel n (typ B))
              → Ω→ (Ω^→ (suc m) (recTrunc∙ n hB f))
              ≡ (Ω→ (Ω^→ (suc m) (recTrunc∙ n'
                            (transport (λ i → isOfHLevel (p i) (typ B)) hB) f))
                 ∘∙ transport (λ i → (Ω^ (suc (suc m))) (hLevelTrunc∙ n A)
                         →∙ ((Ω^ (suc (suc m))) (hLevelTrunc∙ (p i) A)))
                     (id∙ ((Ω^ (suc (suc m))) (hLevelTrunc∙ n A))))
Ω→NatComm' {A = A} {B = B} f m n = J (λ n' p → (hB : isOfHLevel n (typ B))
                      → Ω→ (Ω^→ (suc m) (recTrunc∙ n hB f))
                      ≡ (Ω→ (Ω^→ (suc m) (recTrunc∙ n'
                           (transport (λ i → isOfHLevel (p i) (typ B)) hB) f))
                      ∘∙ transport
                      (λ i → (Ω^ (suc (suc m)))
                              (hLevelTrunc∙ n A)
                         →∙ ((Ω^ (suc (suc m)))
                              (hLevelTrunc∙ (p i) A)))
                     (id∙ ((Ω^ (suc (suc m))) (hLevelTrunc∙ n A)))))
                     λ hB → (∘∙-idˡ _) ⁻¹
                           ∙ λ i →
                        (Ω→ (Ω^→ (suc m) (recTrunc∙ n
                        (transportRefl hB (~ i)) f))
                     ∘∙ transportRefl
                     (id∙ ((Ω^ (suc (suc m))) (hLevelTrunc∙ n A))) (~ i))

AppNatSet : {n : ℕ} (p : n ≡ n) → refl ≡ p
AppNatSet p = isSetℕ _ _ refl p

Ω→NatComm''' : {A B : Pointed ℓ} (f : A →∙ B) (n : ℕ) (p : n ≡ n)
                (hB : isOfHLevel n (typ B))
                 → Ω→ (recTrunc∙ n hB f)
                  ≡ Ω→ (recTrunc∙ n
                        (transport (λ i → isOfHLevel (p i) (typ B)) hB) f)
Ω→NatComm''' {B = B} f n p hB =
  (cong (λ hB' → Ω→ (recTrunc∙ n hB' f)) (transportRefl hB)) ⁻¹
  ∙ cong
    (λ q → Ω→ (recTrunc∙ n
               (transport (λ i → isOfHLevel (q i) (typ B)) hB) f))
    (AppNatSet p)

Ω→NatComm'' : {A B : Pointed ℓ} (f : A →∙ B) (n : ℕ) (p : n ≡ n)
               (hB : isOfHLevel n (typ B))
               → Ω→ (recTrunc∙ n hB f)
               ≡ (Ω→ (recTrunc∙ n
                      (transport (λ i → isOfHLevel (p i) (typ B)) hB) f)
               ∘∙ id∙ (Ω (hLevelTrunc∙ n A)))
Ω→NatComm'' {A = A} {B = B} f n p hB =
  Ω→NatComm''' f n p hB ∙ ∘∙-idˡ _ ⁻¹


Ω→NatComm : {A B : Pointed ℓ} (f : A →∙ B) (m n : ℕ)
               (hB : isOfHLevel (suc m + n) (typ B))
            → Ω→ (Ω^→ m (recTrunc∙ ((suc m) + n) hB f))
             ≡ (Ω→ (Ω^→ m (recTrunc∙ (m + (suc n)) (hLevelNatComm m n hB) f))
               ∘∙ hLevelTrunc→∙ m n)
Ω→NatComm f zero n hB =
  Ω→NatComm'' f (suc n) (1+m+n≡ zero n) hB
Ω→NatComm f (suc m) n hB =
  Ω→NatComm' f m ((suc (suc m)) + n) (1+m+n≡ (suc m) n) hB

congRecFun : {A B : Type ℓ} {a : A} (n : ℕ) {b b' : B}
             (f : A → B) (hB : isOfHLevel (suc n) B) (a' : ∥ A ∥ (1 + n))
             (q : recTrunc hB f a' ≡ b') (p : f a ≡ b) (r : ∣ a ∣ ≡ a')
          → (b ≡ b')
congRecFun n f hB =
  elimTrunc (λ _ → isOfHLevelΠ (suc n)
             (λ _ → isOfHLevelΠ (suc n)
              λ _ → isOfHLevelΠ (suc n)
              λ _ → isOfHLevelPath (suc n) hB _ _))
              λ a' q p → (λ r → (p ⁻¹) ∙∙ cong (recTrunc hB f) r ∙∙ q)

congRecFunEq : {A B : Pointed ℓ} (n : ℕ)
               (f : A →∙ B) (hB : isOfHLevel (suc n) (typ B))
               → fst (Ω→ (recTrunc∙ (suc n) hB f))
               ≡ congRecFun n (fst f) hB (∣ (pt A) ∣ₕ) (snd f) (snd f)
congRecFunEq n f hB = refl

altCongRecFun : {A B : Type ℓ} {a : A} (n : ℕ) {b b' : B}
                (f : A → B) (hB : isOfHLevel (suc n) B) (a' : ∥ A ∥ (1 + n))
                (q : recTrunc hB f a' ≡ b') (p : f a ≡ b) (r : ∣ a ∣ ≡ a')
             → (b ≡ b')
altCongRecFun n f hB =
  elimTrunc (λ x → isOfHLevelΠ (suc n)
             λ _ → isOfHLevelΠ (suc n)
             λ _ → isOfHLevelΠ (suc n)
             λ _ → isOfHLevelPath (suc n) hB _ _)
            λ a' q p → recTrunc (isOfHLevelPath' n hB _ _)
                                 (λ r → p ⁻¹ ∙∙ cong f r ∙∙ q)
                      ∘ correction≡ n

altCongRecFunEq : {A B : Pointed ℓ} (n : ℕ) (f : A →∙ B)
                  (hB : isOfHLevel (suc n) (typ B))
                  → altCongRecFun n (fst f) hB ∣ (pt A) ∣ₕ (snd f) (snd f)
                   ≡ fst ((recTrunc∙ n (hLevelΩ^ 1 n hB) (Ω→ f))
                     ∘∙ correction 1 n)
altCongRecFunEq zero f hB = refl
altCongRecFunEq {A = A} (suc n) f hB =
  cong (recTrunc (hLevelΩ^ 1 (suc n) hB) (fst (Ω→ f)) ∘_)
       (fstCorrection1EqCorrection≡ (suc n) refl ⁻¹)

congRecFunComm'' : {A B : Type ℓ} {a : A} (n : ℕ) {b b' : B}
                   (f : A → B) (hB : isOfHLevel (suc n) B)
                   (q : f a ≡ b') (p : f a ≡ b)
                   → (congRecFun n f hB ∣ a ∣ q p refl)
                   ≡ (recTrunc (isOfHLevelPath' n hB b b')
                     (λ r → p ⁻¹ ∙∙ cong f r ∙∙ q) ∣ refl ∣ₕ)
congRecFunComm'' zero f hB q p =
  isContr→isProp (isProp→isContrPath hB _ _) _ _
congRecFunComm'' (suc n) f hB q p = refl

congRecFunComm' : {A B : Type ℓ} {a : A} (n : ℕ) {b b' : B}
                  (f : A → B) (hB : isOfHLevel (suc n) B) {a' : ∥ A ∥ (1 + n)}
                  (r : ∣ a ∣ₕ ≡ a') (q : recTrunc hB f a' ≡ b') (p : f a ≡ b)
               → congRecFun n f hB a' q p r ≡ altCongRecFun n f hB a' q p r
congRecFunComm' {a = a} n {b = b} {b' = b'} f hB =
  J (λ a' r → (q : recTrunc hB f a' ≡ b') (p : f a ≡ b)
            → congRecFun n f hB a' q p r ≡ altCongRecFun n f hB a' q p r)
    λ q p → congRecFunComm'' n f hB q p
             ∙ cong (recTrunc (isOfHLevelPath' n hB b b')
                              (λ r → p ⁻¹ ∙∙ cong f r ∙∙ q))
                    (correction≡Refl n)

congRecFunComm : {A B : Type ℓ} {a : A} (n : ℕ) {b b' : B}
                 (f : A → B) (hB : isOfHLevel (suc n) B) (a' : ∥ A ∥ (1 + n))
                 (q : recTrunc hB f a' ≡ b') (p : f a ≡ b)
              → congRecFun n f hB a' q p ≡ altCongRecFun n f hB a' q p
congRecFunComm n f hB a' q p =
  funExt (λ r → congRecFunComm' n f hB r q p)

IntermediateCorrectionId' : {A : Pointed ℓ} (n : ℕ)
        → Path ((Ω (hLevelTrunc∙ (suc (suc n)) A))
                 →∙ (hLevelTrunc∙ (suc n) (Ω A)))
              (correction 1 (suc n))
              (correction≡ (suc n) , cong ∣_∣ₕ (transportRefl refl))
IntermediateCorrectionId' {A = A} n = JRefl (λ a' p →
       (Path (∥ typ A ∥ (2 + n)) ∣ pt A ∣ ∣ a' ∣ , cong ∣_∣ p)
       →∙ hLevelTrunc∙ (1 + n) ((pt A ≡ a') , p))
       (correction≡ (suc n) , cong ∣_∣ₕ (transportRefl refl))

IntermediateCorrectionId : {A : Pointed ℓ} (n : ℕ)
        → Path ((Ω (hLevelTrunc∙ (suc (suc n)) A))
                 →∙ (hLevelTrunc∙ (suc n) (Ω A)))
                (correction≡ (suc n)
                 , cong ∣_∣ₕ (transportRefl (refl {x = pt A})))
                (fst (correction {A = A} 1 (suc n)) ,
                      funExt⁻ (transportRefl
                      (correction≡ {A = typ A} {a = pt A} {a' = pt A} (suc n)))
                      (pt (Ω (hLevelTrunc∙ (2 + n) A)))
             ∙ (cong ∣_∣ₕ (transportRefl refl)))
IntermediateCorrectionId {A = A} n =
                     ΣPathP (transportRefl (correction≡ (suc n)) ⁻¹ ,
                     toPathP
                     (transportPathLemmaLeft (funExt⁻
                     (transportRefl (correction≡ (suc n)))
                     (pt (Ω (hLevelTrunc∙ (2 + n) A))) ⁻¹)
                     (cong ∣_∣ₕ (transportRefl refl))
                     ∙ cong (_∙ cong ∣_∣ₕ (transportRefl refl))
                     (symInvo (funExt⁻ (transportRefl (correction≡ (suc n)))
                     (pt (Ω (hLevelTrunc∙ (2 + n) A)))))))

IntermediateCorrectionId'' : {A : Pointed ℓ} (n : ℕ)
           → Path ((Ω (hLevelTrunc∙ (suc (suc n)) A))
                 →∙ (hLevelTrunc∙ (suc n) (Ω A)))
           (correction 1 (suc n))
           (fst (correction {A = A} 1 (suc n)) ,
                      funExt⁻ (transportRefl
                      (correction≡ {A = typ A} {a = pt A} {a' = pt A} (suc n)))
                      (pt (Ω (hLevelTrunc∙ (2 + n) A)))
             ∙ (cong ∣_∣ₕ (transportRefl refl)))
IntermediateCorrectionId'' n =
  IntermediateCorrectionId' n ∙ IntermediateCorrectionId n

PathFunctionNeed : {A B : Pointed ℓ} (n : ℕ) (f : A →∙ B)
                   (hB : isOfHLevel (2 + n) (typ B))
              → (hTr (pt A ≡ pt A) (1 + n) (refl {x = pt (fst A , snd A)})  ≡ ∣ transport refl (refl {x = pt (fst A , snd A)}) ∣ₕ)
              →
  recTrunc (hLevelΩ^ 1 (suc n) hB) (fst (Ω→ f))
      (fst (correction≡∙ (suc n) (λ _ → pt (fst A , snd A)))
       (pt (Ω (hLevelTrunc∙ (2 + n) A))))
      ≡
      recTrunc (hLevelΩ^ 1 (suc n) hB) (fst (Ω→ f))
      ∣ (λ _ → pt (fst A , snd A)) ∣ₕ
PathFunctionNeed {A = A} n f hB = λ p → cong (recTrunc (hLevelΩ^ 1 (suc n) hB) (fst (Ω→ f)))
                       ( p
                       ∙ (funExt⁻ (fstCorrection1EqCorrection≡ (suc n) refl)
                                 (pt (Ω (hLevelTrunc∙ (2 + n) A))) ⁻¹)) ⁻¹

NeedPathEq : {A B : Pointed ℓ} (n : ℕ) (f : A →∙ B)
             (hB : isOfHLevel (2 + n) (typ B))
           → (funExt⁻ (congRecFunComm (suc n) (fst f) hB
                       (∣ pt A ∣ₕ) (snd f) (snd f)
                     ∙ altCongRecFunEq (suc n) f hB)
                     (pt (Ω (hLevelTrunc∙ (2 + n) A)))) ⁻¹
            ≡ cong (recTrunc (hLevelΩ^ 1 (suc n) hB) (fst (Ω→ f)))
                   (funExt⁻ (transportRefl
                      (correction≡ {A = typ A} {a = pt A} {a' = pt A} (suc n)))
                      (pt (Ω (hLevelTrunc∙ (2 + n) A)))
             ∙ (cong ∣_∣ₕ (transportRefl refl)))
NeedPathEq {A = A} {B = B} n f hB =
  (funExt⁻ (congRecFunComm (suc n) (fst f) hB
            (∣ pt A ∣ₕ) (snd f) (snd f)
           ∙ altCongRecFunEq (suc n) f hB)
           (pt (Ω (hLevelTrunc∙ (2 + n) A)))) ⁻¹
  ≡⟨ cong _⁻¹ (funExt⁻Dist (congRecFunComm (suc n) (fst f) hB
                            (∣ pt A ∣ₕ) (snd f) (snd f))
                          (altCongRecFunEq (suc n) f hB)
                          {a = (pt (Ω (hLevelTrunc∙ (2 + n) A)))}) ⟩
  ( funExt⁻ (congRecFunComm (suc n) (fst f) hB
             (∣ pt A ∣ₕ) (snd f) (snd f))
            (pt (Ω (hLevelTrunc∙ (2 + n) A)))
  ∙ funExt⁻ (altCongRecFunEq (suc n) f hB)
            (pt (Ω (hLevelTrunc∙ (2 + n) A)))) ⁻¹
  ≡⟨ refl ⟩
  ( congRecFunComm' (suc n) (fst f) hB
                    (pt (Ω (hLevelTrunc∙ (2 + n) A))) (snd f) (snd f)
  ∙ funExt⁻ (altCongRecFunEq (suc n) f hB)
            (pt (Ω (hLevelTrunc∙ (2 + n) A)))) ⁻¹
  ≡⟨ refl ⟩
  ( congRecFunComm' (suc n) (fst f) hB
                     (pt (Ω (hLevelTrunc∙ (2 + n) A))) (snd f) (snd f)
  ∙ funExt⁻ (cong (recTrunc (hLevelΩ^ 1 (suc n) hB) (fst (Ω→ f)) ∘_)
            (fstCorrection1EqCorrection≡ (suc n) refl ⁻¹))
           (pt (Ω (hLevelTrunc∙ (2 + n) A)))) ⁻¹
  ≡⟨ cong (λ p → (congRecFunComm' (suc n) (fst f) hB
            (pt (Ω (hLevelTrunc∙ (2 + n) A))) (snd f) (snd f) ∙ p) ⁻¹)
           (funExt⁻Cong (recTrunc (hLevelΩ^ 1 (suc n) hB) (fst (Ω→ f)))
                        (fstCorrection1EqCorrection≡ (suc n) refl ⁻¹)
                        {a = (pt (Ω (hLevelTrunc∙ (2 + n) A)))}) ⟩
  ( congRecFunComm' (suc n) (fst f) hB
                    (pt (Ω (hLevelTrunc∙ (2 + n) A))) (snd f) (snd f)
  ∙ cong (recTrunc (hLevelΩ^ 1 (suc n) hB) (fst (Ω→ f)))
    (funExt⁻ (fstCorrection1EqCorrection≡ (suc n) refl ⁻¹)
             (pt (Ω (hLevelTrunc∙ (2 + n) A))))) ⁻¹
  ≡⟨ cong (λ p → (p ∙
                   cong (recTrunc (hLevelΩ^ 1 (suc n) hB) (fst (Ω→ f)))
                   (funExt⁻ (fstCorrection1EqCorrection≡ (suc n) refl ⁻¹)
                   (pt (Ω (hLevelTrunc∙ (2 + n) A))))) ⁻¹)
           (funExt⁻
           (funExt⁻ (JRefl (λ a' r → (q : recTrunc hB (fst f) a' ≡ (snd B))
                                      (p : (fst f) (pt A) ≡ (pt B))
            → congRecFun (suc n) (fst f) hB a' q p r
            ≡ altCongRecFun (suc n) (fst f) hB a' q p r)
            (λ p q →
           refl ∙ cong (recTrunc (hLevelΩ^ 1 (suc n) hB)
                                 (λ s → q ⁻¹ ∙∙ cong (fst f) s ∙∙ p))
                       (correction≡Refl (suc n))))
           (snd f)) (snd f)) ⟩
  ( (refl ∙ cong (recTrunc (hLevelΩ^ 1 (suc n) hB) (fst (Ω→ f)))
                 (correction≡Refl (suc n)))
  ∙ cong (recTrunc (hLevelΩ^ 1 (suc n) hB) (fst (Ω→ f)))
    (funExt⁻ (fstCorrection1EqCorrection≡ (suc n) refl ⁻¹)
             (pt (Ω (hLevelTrunc∙ (2 + n) A))))) ⁻¹
  ≡⟨ cong (λ p → (p ∙
              cong (recTrunc (hLevelΩ^ 1 (suc n) hB) (fst (Ω→ f)))
              (funExt⁻ (fstCorrection1EqCorrection≡ (suc n) refl ⁻¹)
               (pt (Ω (hLevelTrunc∙ (2 + n) A))))) ⁻¹)
           ((lUnit (cong (recTrunc (hLevelΩ^ 1 (suc n) hB) (fst (Ω→ f)))
                         (correction≡Refl (suc n)))) ⁻¹) ⟩
  ( cong (recTrunc (hLevelΩ^ 1 (suc n) hB) (fst (Ω→ f)))
          (correction≡Refl (suc n))
  ∙ cong (recTrunc (hLevelΩ^ 1 (suc n) hB) (fst (Ω→ f)))
    (funExt⁻ (fstCorrection1EqCorrection≡ (suc n) refl ⁻¹)
             (pt (Ω (hLevelTrunc∙ (2 + n) A))))) ⁻¹
  ≡⟨ cong _⁻¹ ((cong-∙ (recTrunc (hLevelΩ^ 1 (suc n) hB) (fst (Ω→ f)))
                      (correction≡Refl (suc n))
                      (funExt⁻ (fstCorrection1EqCorrection≡ (suc n) refl ⁻¹)
                               (pt (Ω (hLevelTrunc∙ (2 + n) A))))) ⁻¹) ⟩
  (cong (recTrunc (hLevelΩ^ 1 (suc n) hB) (fst (Ω→ f)))
    ((correction≡Refl (suc n))
  ∙ (funExt⁻ (fstCorrection1EqCorrection≡ (suc n) refl ⁻¹)
             (pt (Ω (hLevelTrunc∙ (2 + n) A)))))) ⁻¹
  ≡⟨ congSym (recTrunc (hLevelΩ^ 1 (suc n) hB) (fst (Ω→ f)))
     (correction≡Refl (suc n)
     ∙ funExt⁻ (fstCorrection1EqCorrection≡ (suc n) refl ⁻¹)
               (pt (Ω (hLevelTrunc∙ (2 + n) A)))) ⟩
  cong (recTrunc (hLevelΩ^ 1 (suc n) hB) (fst (Ω→ f)))
  ((correction≡Refl (suc n)
  ∙ funExt⁻ (fstCorrection1EqCorrection≡ (suc n) refl ⁻¹)
            (pt (Ω (hLevelTrunc∙ (2 + n) A)))) ⁻¹)
  ≡⟨ refl ⟩
  PathFunctionNeed n f hB (cong ∣_∣ₕ (transportRefl refl ⁻¹))
  ≡⟨ cong (PathFunctionNeed n f hB) ((congSym ∣_∣ₕ (transportRefl refl)) ⁻¹) ⟩
  cong (recTrunc (hLevelΩ^ 1 (suc n) hB) (fst (Ω→ f)))
  (((cong ∣_∣ₕ (transportRefl refl)) ⁻¹
  ∙ (funExt⁻ (fstCorrection1EqCorrection≡ (suc n) refl)
             (pt (Ω (hLevelTrunc∙ (2 + n) A))) ⁻¹)) ⁻¹)
  ≡⟨ cong (cong (recTrunc (hLevelΩ^ 1 (suc n) hB) (fst (Ω→ f))))
          (symDistr ((cong ∣_∣ₕ (transportRefl refl)) ⁻¹)
          (funExt⁻ (fstCorrection1EqCorrection≡ (suc n) refl)
                   (pt (Ω (hLevelTrunc∙ (2 + n) A))) ⁻¹))
     ∙ cong (cong (recTrunc (hLevelΩ^ 1 (suc n) hB) (fst (Ω→ f))))
            ( cong (_∙ (cong ∣_∣ₕ (transportRefl refl))  ⁻¹ ⁻¹)
                   (symInvo (funExt⁻ (fstCorrection1EqCorrection≡ (suc n) refl)
                                     (pt (Ω (hLevelTrunc∙ (2 + n) A))))) ⁻¹
            ∙ cong (funExt⁻ (fstCorrection1EqCorrection≡ (suc n) refl)
                             (pt (Ω (hLevelTrunc∙ (2 + n) A))) ∙_)
                    (symInvo (cong ∣_∣ₕ (transportRefl refl)) ⁻¹)) ⟩
  cong (recTrunc (hLevelΩ^ 1 (suc n) hB) (fst (Ω→ f)))
  ( funExt⁻ (fstCorrection1EqCorrection≡ (suc n) refl)
            (pt (Ω (hLevelTrunc∙ (2 + n) A)))
  ∙ (cong ∣_∣ₕ (transportRefl refl)))
  ≡⟨ cong (λ p →
     cong (recTrunc (hLevelΩ^ 1 (suc n) hB) (fst (Ω→ f)))
     ( funExt⁻ p (pt (Ω (hLevelTrunc∙ (2 + n) A)))
     ∙ (cong ∣_∣ₕ (transportRefl refl))))
     (JRefl (λ a' p → fst (correction≡∙ {A = typ A} (suc n) p)
             ≡ correction≡ {A = typ A} {a = pt A} {a' = a'} (suc n))
            (transportRefl
            (correction≡ {A = typ A} {a = pt A} {a' = pt A} (suc n)))) ⟩
  cong (recTrunc (hLevelΩ^ 1 (suc n) hB) (fst (Ω→ f)))
  ( funExt⁻
       (transportRefl (correction≡ {A = typ A} {a = pt A} {a' = pt A} (suc n)))
       (pt (Ω (hLevelTrunc∙ (2 + n) A)))
  ∙ (cong ∣_∣ₕ (transportRefl refl))) ∎

recTrunc∘∙≡ : {A B : Pointed ℓ} (f : A →∙ B) (n : ℕ)
              (hB : isOfHLevel (suc (suc n)) (typ B))
           → Path (Ω (hLevelTrunc∙ (suc (suc n)) A) →∙ (Ω B))
             (( (recTrunc (hLevelΩ^ 1 (suc n) hB) (fst (Ω→ f)))
              ∘ (fst (correction {A = A} 1 (suc n)))
              , ( funExt⁻ ( congRecFunComm (suc n) (fst f) hB
                                           ∣ pt A ∣ (snd f) (snd f)
                          ∙ altCongRecFunEq (suc n) f hB)
                          (pt (Ω (hLevelTrunc∙ (suc (suc n)) A)))) ⁻¹
                ∙ (∙∙lCancel (snd f))))
            ((( recTrunc∙ (suc n) (hLevelΩ^ 1 (suc n) hB) (Ω→ f))
             ∘∙ ( fst (correction {A = A} 1 (suc n))
                , funExt⁻
                   ( transportRefl
                     (correction≡ {A = typ A} {a = pt A} {a' = pt A} (suc n)))
                   ( pt (Ω (hLevelTrunc∙ (2 + n) A)))
                   ∙ (cong ∣_∣ₕ (transportRefl refl)))))
recTrunc∘∙≡ f n hB =
  ΣPathP (refl , toPathP ( transportRefl _
                         ∙ cong (_∙ ∙∙lCancel (snd f)) (NeedPathEq n f hB)))

ΩRecComm : {A B : Pointed ℓ} (f : A →∙ B) (n : ℕ)
           (hB : isOfHLevel (suc n) (typ B))
        → (Ω→ (recTrunc∙ (suc n) hB f))
         ≡ (recTrunc∙ n (hLevelΩ^ 1 n hB) (Ω→ f)) ∘∙ correction 1 n
ΩRecComm f zero hB =
  ΣPathP (ContrFunEq (isProp→isContrPath hB _ _)  _ _
        , toPathP
          (((snd (isContr→isContrPath (isProp→isContrPath hB _ _) _ _)) _) ⁻¹
          ∙ snd (isContr→isContrPath (isProp→isContrPath hB _ _) _ _) _))
ΩRecComm {A = A} f (suc n) hB =
  (Ω→ (recTrunc∙ (suc (suc n)) hB f))
  ≡⟨ ΣPathP (((congRecFunComm (suc n) (fst f) hB _ (snd f) (snd f)
         ∙ altCongRecFunEq (suc n) f hB))
         , toPathP (transportPathLemmaLeft _ _)) ⟩
  ((recTrunc (hLevelΩ^ 1 (suc n) hB) (fst (Ω→ f)))
  ∘ (fst (correction {A = A} 1 (suc n))) ,
  (funExt⁻ (congRecFunComm (suc n) (fst f) hB _ (snd f) (snd f)
             ∙ altCongRecFunEq (suc n) f hB)
            (pt (Ω (hLevelTrunc∙ (suc (suc n)) A)))) ⁻¹
  ∙ (∙∙lCancel (snd f)))
  ≡⟨ recTrunc∘∙≡ f n hB ⟩
  ((recTrunc∙ (suc n) (hLevelΩ^ 1 (suc n) hB) (Ω→ f))
  ∘∙ (fst (correction {A = A} 1 (suc n)) ,
                      funExt⁻ (transportRefl
                      (correction≡ {A = typ A} {a = pt A} {a' = pt A} (suc n)))
                      (pt (Ω (hLevelTrunc∙ (2 + n) A)))
             ∙ (cong ∣_∣ₕ (transportRefl refl))))
  ≡⟨ cong ((recTrunc∙ (suc n) (hLevelΩ^ 1 (suc n) hB) (Ω→ f)) ∘∙_)
     (IntermediateCorrectionId'' n ⁻¹) ⟩
  (recTrunc∙ (suc n) (hLevelΩ^ 1 (suc n) hB) (Ω→ f))
  ∘∙ correction 1 (suc n) ∎

Ω^RecComm : {A B : Pointed ℓ} (f : A →∙ B) (m n : ℕ)
            (hB : isOfHLevel (m + n) (typ B))
         → ((Ω^→ m) (recTrunc∙ (m + n) hB f))
          ≡ (recTrunc∙ n (hLevelΩ^ m n hB) ((Ω^→ m) f)) ∘∙ correction m n
Ω^RecComm f zero n hB = ∘∙-idˡ _ ⁻¹
Ω^RecComm {A = A} f (suc m) n hB =
  Ω→ (Ω^→ m (recTrunc∙ ((suc m) + n) hB f))
   ≡⟨ Ω→NatComm f m n hB ⟩
  Ω→ (Ω^→ m (recTrunc∙ (m + (suc n)) (hLevelNatComm m n hB) f))
  ∘∙ hLevelTrunc→∙ m n
   ≡⟨ cong (λ t → Ω→ t ∘∙ hLevelTrunc→∙ m n)
           (Ω^RecComm f m (suc n) (hLevelNatComm m n hB)) ⟩
  Ω→ (recTrunc∙ (suc n) (hLevelΩ^ m (suc n) (hLevelNatComm m n hB))
                 ((Ω^→ m) f)
  ∘∙ correction m (suc n))
  ∘∙ hLevelTrunc→∙ m n
   ≡⟨ cong (_∘∙ hLevelTrunc→∙ m n)
           (Ω→∘∙ (recTrunc∙ (suc n) (hLevelΩ^ m (suc n) (hLevelNatComm m n hB))
                                     ((Ω^→ m) f))
                  (correction m (suc n))) ⟩
  (Ω→ (recTrunc∙ (suc n) (hLevelΩ^ m (suc n) (hLevelNatComm m n hB))
                  ((Ω^→ m) f))
  ∘∙ Ω→ (correction m (suc n)))
  ∘∙ hLevelTrunc→∙ m n
   ≡⟨ ∘∙-assoc (Ω→ (recTrunc∙ (suc n)
                    (hLevelΩ^ m (suc n) (hLevelNatComm m n hB))
                    ((Ω^→ m) f)))
               (Ω→ (correction m (suc n)))
               (hLevelTrunc→∙ m n) ⟩
  Ω→ (recTrunc∙ (suc n) (hLevelΩ^ m (suc n) (hLevelNatComm m n hB))
                 ((Ω^→ m) f))
  ∘∙ (Ω→ (correction m (suc n))
  ∘∙ hLevelTrunc→∙ m n)
   ≡⟨ cong (_∘∙ (Ω→ (correction m (suc n))
                 ∘∙ hLevelTrunc→∙ m n))
            (ΩRecComm ((Ω^→ m) f) n
                      (hLevelΩ^ m (suc n) (hLevelNatComm m n hB))) ⟩
  (recTrunc∙ n (hLevelΩ^ 1 n (hLevelΩ^ m (suc n) (hLevelNatComm m n hB)))
             (Ω→ ((Ω^→ m) f))
  ∘∙ correction 1 n)
  ∘∙ (Ω→ (correction m (suc n))
  ∘∙ hLevelTrunc→∙ m n)
   ≡⟨ ∘∙-assoc (recTrunc∙ n (hLevelΩ^ 1 n
                             (hLevelΩ^ m (suc n) (hLevelNatComm m n hB)))
                             ((Ω^→ (suc m)) f))
                (correction {A = (Ω^ m) A} 1 n)
                (Ω→ (correction m (suc n))
                ∘∙ hLevelTrunc→∙ m n) ⟩
  recTrunc∙ n (hLevelΩ^ 1 n (hLevelΩ^ m (suc n) (hLevelNatComm m n hB)))
            ((Ω^→ (suc m)) f)
  ∘∙ (correction {A = (Ω^ m) A} 1 n
  ∘∙ (Ω→ (correction m (suc n))
  ∘∙ hLevelTrunc→∙ m n))
   ≡⟨ cong ((recTrunc∙ n (hLevelΩ^ 1 n (hLevelΩ^ m (suc n)
                         (hLevelNatComm m n hB)))
                         ((Ω^→ (suc m)) f)) ∘∙_)
            ((∘∙-assoc (correction {A = (Ω^ m) A} 1 n)
                       (Ω→ (correction m (suc n)))
                       (hLevelTrunc→∙ m n)) ⁻¹) ⟩
  recTrunc∙ n (hLevelΩ^ 1 n (hLevelΩ^ m (suc n) (hLevelNatComm m n hB)))
            ((Ω^→ (suc m)) f)
  ∘∙ ((correction {A = (Ω^ m) A} 1 n
  ∘∙ Ω→ (correction m (suc n)))
  ∘∙ hLevelTrunc→∙ m n)
   ≡⟨ cong (λ H
            → recTrunc∙ n H ((Ω^→ (suc m)) f)
              ∘∙ ((correction {A = (Ω^ m) A} 1 n
              ∘∙ Ω→ (correction m (suc n)))
              ∘∙ hLevelTrunc→∙ m n))
            (isPropIsOfHLevel n _ _) ⟩
  (recTrunc∙ n (hLevelΩ^ (suc m) n hB) ((Ω^→ (suc m)) f)
  ∘∙ (((correction {A = (Ω^ m) A} 1 n
  ∘∙ Ω→ (correction m (suc n)))
  ∘∙ hLevelTrunc→∙ m n)))
   ≡⟨ cong (recTrunc∙ n (hLevelΩ^ (suc m) n hB) ((Ω^→ (suc m)) f) ∘∙_)
      (correctionEqCorrection m n) ⟩
  recTrunc∙ n (hLevelΩ^ (suc m) n hB) ((Ω^→ (suc m)) f)
  ∘∙ correction (suc m) n ∎

ΩRecPreConcl : {A B : Pointed ℓ} (f : A →∙ B) (m n : ℕ)
               (hB : isOfHLevel (m + n) (typ B))
            → isIso (fst ((Ω^→ m) f))
            → isIso (fst ((Ω^→ m) (recTrunc∙ (m + n) hB f)))
ΩRecPreConcl f zero zero hB hf =
  isEquiv→isIso (λ _ → fst hB) (ContrContrIsEquiv _ _ isContrUnit* hB _)
ΩRecPreConcl f zero (suc n) hB hf =
  isIso→isIsoRecTrunc (suc n) (fst f) hB hf
ΩRecPreConcl {A = A} f (suc m) zero hB hf =
  transport (λ i → isIso (fst (Ω^RecComm f (suc m) zero hB (~ i))))
  (342-case3 (fst (correction (suc m) zero))
             (recTrunc (hLevelΩ^ (suc m) zero hB) (fst ((Ω^→ (suc m)) f)))
             (isIso→isIsoRecTrunc zero (fst ((Ω^→ (suc m)) f))
                                        (hLevelΩ^ (suc m) zero hB)
                                        hf)
             (isIsoCorrection {A = A} (suc m) zero))
ΩRecPreConcl f (suc m) (suc n) hB hf =
  transport (λ i → isIso (fst (Ω^RecComm f (suc m) (suc n) hB (~ i))))
            (342-case3 (fst (correction (suc m) (suc n)))
                       (recTrunc (hLevelΩ^ (suc m) (suc n) hB)
                                  (fst ((Ω^→ (suc m)) f)))
                       (isIso→isIsoRecTrunc (suc n) (fst ((Ω^→ (suc m)) f))
                       (hLevelΩ^ (suc m) (suc n) hB)
                       hf)
                       (isIsoCorrection (suc m) (suc n)))

ΩRecConcl : {A B : Pointed ℓ} (f : A →∙ B) (m n : ℕ)
            (hB : isOfHLevel ((suc m) + (2 + n)) (typ B))
         → isIso (πFun m f)
         → isIso (πFun m (recTrunc∙ ((suc m) + (2 + n)) hB f))
ΩRecConcl {A = A} {B = B} f m n hB hf =
  transport
  (λ i → isIso (mapSetTrunc (fst (Ω^RecComm f (suc m) (2 + n) hB (~ i)))))
  (transport
  (λ i → isIso (setMap∘ (fst (recTrunc∙ (2 + n) (hLevelΩ^ (suc m) (2 + n) hB)
                           ((Ω^→ (suc m)) f)))
                           (fst (correction {A = A} (suc m) (2 + n))) (~ i)))
  (342-case3 (mapSetTrunc (fst (correction (suc m) (2 + n))))
             (mapSetTrunc (fst (recTrunc∙ (2 + n) (hLevelΩ^ (suc m) (2 + n) hB)
                                            ((Ω^→ (suc m)) f))))
             (342-case1
               (mapSetTrunc ∣_∣ₕ)
               (mapSetTrunc
                (fst (recTrunc∙ (2 + n) (hLevelΩ^ (suc m) (2 + n) hB)
                      ((Ω^→ (suc m)) f))))
               (iso∣-∣ₕ n)
               (transport
               (λ i → isIso
               (SetMapRecNeut (typ ((Ω^ (suc m)) A)) (typ ((Ω^ (suc m)) B))
               (2 + n) (fst ((Ω^→ (suc m)) f)) (hLevelΩ^ (suc m) (2 + n) hB)
               (~ i)))
               hf))
             (isIso→isIsoMapSet (fst (correction (suc m) (2 + n)))
                                 (isIsoCorrection (suc m) (2 + n)))))

4+n≡ : (n : ℕ) → (4 + n) ≡ (suc (suc n)) + (2 + 0)
4+n≡ n = cong (λ m → suc (suc m)) (+-comm 2 n)

SpΩRecConcl : {A B : Pointed ℓ} (f : A →∙ B) (n : ℕ)
              (hB : isOfHLevel (4 + n) (typ B))
           → isIso (πFun (1 + n) f)
           → isIso (πFun (1 + n) (recTrunc∙ (4 + n) hB f))
SpΩRecConcl {B = B} f n =
  transport (λ i → ((hB : isOfHLevel (4+n≡ n (~ i)) (typ B))
                 → isIso (πFun (suc n) f)
                 → isIso (πFun (suc n) (recTrunc∙ (4+n≡ n (~ i)) hB f))))
             (ΩRecConcl f (suc n) 0)
