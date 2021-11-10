{-# OPTIONS --safe #-}
{-
The goal of this file is to prove that the function
suspMapΩ : Ωⁿ A → Ωⁿ⁺¹ (Susp A), induced by
the Freudenthal function σ : A → ΩΣA, gets taken to
the canonical suspension map
suspMap : (Sⁿ →∙ A) → (Sⁿ⁺¹ →∙ Susp A)
given some suitable structure preserving equivalences
Ωⁿ A ≃ (Sⁿ →∙ A).

The idea is to fill the following diagram

          suspMapΩ
Ωⁿ A -------------------> Ωⁿ⁺¹ (Susp A)
 |                           |
 |                           |
 | ≃ eq₁                     | ≃ eq₂
 |                           |
 v           suspMap         v
 (Sⁿ →∙ A) -------------- > (Sⁿ⁺¹ →∙ Susp A)

(we choose eq₁ and eq₂ (intensionally) different for techinical reasons)

Many results in this file are technical. See the end for the main results.
-}
module Cubical.Homotopy.Group.SuspensionMapPathP where

open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Freudenthal
open import Cubical.Homotopy.Connected

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws renaming (assoc to ∙assoc)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport

open import Cubical.Functions.Morphism

open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.S1

open import Cubical.Data.Bool hiding (_≟_)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat

open import Cubical.Algebra.Group
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid

open Iso
open IsGroup
open IsSemigroup
open IsMonoid
open GroupStr

flipΩPath : {ℓ : Level} {A : Pointed ℓ} (n : ℕ)
                → ((Ω^ (suc n)) A) ≡ (Ω^ n) (Ω A)
flipΩPath {A = A} zero = refl
flipΩPath {A = A} (suc n) = cong Ω (flipΩPath {A = A} n)

flipΩIso : {ℓ : Level} {A : Pointed ℓ} (n : ℕ)
              → Iso (fst ((Ω^ (suc n)) A)) (fst ((Ω^ n) (Ω A)))
flipΩIso {A = A} n = pathToIso (cong fst (flipΩPath n))

flipΩIso⁻pres· : {ℓ : Level} {A : Pointed ℓ} (n : ℕ)
                      → (f g : fst ((Ω^ (suc n)) (Ω A)))
                      → inv (flipΩIso (suc n)) (f ∙ g)
                      ≡ (inv (flipΩIso (suc n)) f)
                      ∙ (inv (flipΩIso (suc n)) g)
flipΩIso⁻pres· {A = A} n f g i =
    transp (λ j → flipΩPath {A = A} n (~ i ∧ ~ j) .snd
                 ≡ flipΩPath n (~ i ∧ ~ j) .snd) i
                  (transp (λ j → flipΩPath {A = A} n (~ i ∨ ~ j) .snd
                 ≡ flipΩPath n (~ i ∨ ~ j) .snd) (~ i) f
                 ∙ transp (λ j → flipΩPath {A = A} n (~ i ∨ ~ j) .snd
                 ≡ flipΩPath n (~ i ∨ ~ j) .snd) (~ i) g)

flipΩIsopres· : {ℓ : Level} {A : Pointed ℓ} (n : ℕ)
                      → (f g : fst (Ω ((Ω^ (suc n)) A)))
                      → fun (flipΩIso (suc n)) (f ∙ g)
                      ≡ (fun (flipΩIso (suc n)) f)
                      ∙ (fun (flipΩIso (suc n)) g)
flipΩIsopres· n =
  morphLemmas.isMorphInv _∙_ _∙_
    (inv (flipΩIso (suc n)))
    (flipΩIso⁻pres· n)
    (fun (flipΩIso (suc n)))
    (Iso.leftInv (flipΩIso (suc n)))
    (Iso.rightInv (flipΩIso (suc n)))

flipΩrefl : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
  → fun (flipΩIso {A = A} (suc n)) refl ≡ refl
flipΩrefl {A = A} n j =
  transp (λ i₁ → fst (Ω (flipΩPath {A = A} n ((i₁ ∨ j)))))
         j (snd (Ω (flipΩPath n j)))


-- Solves some termination issues
private
  +nInd : ∀ {ℓ} {P : ℕ → Type ℓ}
        → P 0
        → P 1
        → ((n : ℕ) → P (suc n) → P (suc (suc n)))
        → (n : ℕ) → P n
  +nInd 0c 1c indc zero = 0c
  +nInd 0c 1c indc (suc zero) = 1c
  +nInd {P = P} 0c 1c indc (suc (suc n)) =
    indc n (+nInd {P = P} 0c 1c indc (suc n))

-- move to loop
Ω^→ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ)
  → (A →∙ B) → ((Ω^ n) A →∙ (Ω^ n) B)
Ω^→ zero f = f
Ω^→ (suc n) f = Ω→ (Ω^→ n f)

-- move to pointed
post∘∙ : ∀ {ℓX ℓ ℓ'} (X : Pointed ℓX) {A : Pointed ℓ} {B : Pointed ℓ'}
  → (A →∙ B) → ((X →∙ A ∙) →∙ (X →∙ B ∙))
post∘∙ X f .fst g = f ∘∙ g
post∘∙ X f .snd =
  ΣPathP
    ( (funExt λ _ → f .snd)
    , (sym (lUnit (f .snd)) ◁ λ i j → f .snd (i ∨ j))
    )

suspMap : ∀ {ℓ} {A : Pointed ℓ}(n : ℕ)
        → S₊∙ (suc n) →∙ A
        → S₊∙ (suc (suc n)) →∙ Susp∙ (typ A)
fst (suspMap n f) north = north
fst (suspMap n f) south = north
fst (suspMap {A = A} n f) (merid a i) =
  (merid (fst f a) ∙ sym (merid (pt A))) i
snd (suspMap n f) = refl

lMap : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ}
  → typ ((Ω^ n) A) → (S₊∙ n →∙ A)
lMapId : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ} (a : _)
  → lMap n {A = A} (pt ((Ω^ n) A)) .fst a ≡ pt A
lMapId2 : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ}
  → lMap n {A = A} (pt ((Ω^ n) A)) ≡ ((λ _ → pt A) , refl)
fst (lMap zero {A = A} a) false = a
fst (lMap zero {A = A} a) true = pt A
snd (lMap zero {A = A} a) = refl
fst (lMap (suc zero) {A = A} p) base = pt A
fst (lMap (suc zero) {A = A} p) (loop i) = p i
snd (lMap (suc zero) {A = A} p) = refl
fst (lMap (suc (suc n)) {A = A} p) north = pt A
fst (lMap (suc (suc n)) {A = A} p) south = pt A
fst (lMap (suc (suc n)) {A = A} p) (merid a i) =
     (sym (lMapId (suc n) a)
  ∙∙ (λ i → lMap (suc n) (p i) .fst a)
  ∙∙ lMapId (suc n) a) i
snd (lMap (suc (suc n)) {A = A} p) = refl
lMapId zero false = refl
lMapId zero true = refl
lMapId (suc zero) base = refl
lMapId (suc zero) (loop i) = refl
lMapId (suc (suc n)) north = refl
lMapId (suc (suc n)) south = refl
lMapId (suc (suc n)) {A = A} (merid a i) j =
   ∙∙lCancel (lMapId (suc n) {A = A} a) j i
lMapId2 zero {A = A} =
  ΣPathP ((funExt (λ { false → refl
                     ; true → refl}))
           , refl)
lMapId2 (suc zero) {A = A} =
  ΣPathP ((funExt (λ { base → refl
                    ; (loop i) → refl}))
          , refl)
lMapId2 (suc (suc n)) {A = A} =
  ΣPathP ((funExt (λ { north → refl
                     ; south → refl
                     ; (merid a i) j
                      → ∙∙lCancel (lMapId (suc n) {A = A} a) j i}))
          , refl)

lMap∙ : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ}
  → ((Ω^ n) A) →∙ (S₊∙ n →∙ A ∙)
lMap∙ n .fst = lMap n
lMap∙ n .snd = lMapId2 n

-- We define the following maps which will be used to
-- show that lMap is an equivalence
lMapSplit₁ : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
           → typ ((Ω^ (suc n)) A)
           → typ (Ω (S₊∙ n →∙ A ∙))
lMapSplit₁ n = Ω→ (lMap∙ n) .fst

ΩSphereMap : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
  → typ (Ω (S₊∙ n →∙ A ∙))
  → (S₊∙ (suc n) →∙ A)
fst (ΩSphereMap {A = A} zero p) base = p i0 .fst false
fst (ΩSphereMap {A = A} zero p) (loop i) = p i .fst false
snd (ΩSphereMap {A = A} zero p) = refl
fst (ΩSphereMap {A = A} (suc n) p) north = pt A
fst (ΩSphereMap {A = A} (suc n) p) south = pt A
fst (ΩSphereMap {A = A} (suc n) p) (merid a i) = p i .fst a
snd (ΩSphereMap {A = A} (suc n) p) = refl

SphereMapΩ : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
  → (S₊∙ (suc n) →∙ A)
  → typ (Ω (S₊∙ n →∙ A ∙))
SphereMapΩ {A = A} zero (f , p) =
  ΣPathP ((funExt λ { false → sym p ∙∙ cong f loop ∙∙ p
                    ; true → refl})
          , refl)
SphereMapΩ {A = A} (suc n) (f , p) =
  ΣPathP (funExt (λ x → sym p ∙∙ cong f (merid x ∙ sym (merid (ptSn _))) ∙∙ p)
        , flipSquare (cong (sym p ∙∙_∙∙ p)
                           (cong (cong f) (rCancel (merid (ptSn _))))
                   ∙ ∙∙lCancel p))

SphereMapΩIso : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
  → Iso (S₊∙ (suc n) →∙ A)
         (typ (Ω (S₊∙ n →∙ A ∙)))
fun (SphereMapΩIso {A = A} n) = SphereMapΩ n
inv (SphereMapΩIso {A = A} n) = ΩSphereMap n
fst (rightInv (SphereMapΩIso {A = A} zero) p k i) false =
  rUnit (funExt⁻ (cong fst p) false) (~ k) i
fst (rightInv (SphereMapΩIso {A = A} zero) p k i) true = snd (p i) (~ k)
snd (rightInv (SphereMapΩIso {A = A} zero) p k i) l = snd (p i) (~ k ∨ l)
fst (rightInv (SphereMapΩIso {A = A} (suc n)) p k i) x = help k i
  where
  help : cong (fst (ΩSphereMap {A = A} (suc n) p)) (merid x ∙ sym (merid (ptSn _))) ∙ refl
       ≡ funExt⁻ (cong fst p) x
  help = (cong (refl ∙∙_∙∙ refl) (cong-∙ (fst (ΩSphereMap {A = A} (suc n) p))
                                         (merid x) (sym (merid (ptSn _))))
        ∙ cong (refl ∙∙_∙∙ refl) (cong (funExt⁻ (cong fst p) x ∙_)
                                       (cong sym (flipSquare (cong snd p)))
                                       ∙ sym (rUnit _)))
        ∙ sym (rUnit _)
snd (rightInv (SphereMapΩIso {A = A} (suc n)) p k i) j =
  hcomp (λ r →
    λ { (i = i0) → pt A
      ; (i = i1) → pt A
      ; (j = i0) → ((wrap-refl (cong-∙ Ωp (merid (ptSn (suc n)))
                                           (sym (merid (ptSn _))))
                    ∙ wrap-refl (cong (p-refl ∙_)
                                  (cong sym (flipSquare (cong snd p)))
                    ∙ sym (rUnit _))) ∙ sym (rUnit _)) k i
       ; (j = i1) → rUnit (λ _ → pt A) (~ r ∧ ~ k) i
       ; (k = i0) → compPath-filler (wrap-refl (cong (cong Ωp)
                                                 (rCancel (merid (ptSn _)))))
                                     (sym (rUnit refl)) r j i
       ; (k = i1) → snd (p i) j})
   (hcomp (λ r →
     λ { (i = i0) → rUnit (λ _ → pt A) (~ k ∨ r) i
       ; (i = i1) → rUnit (λ _ → pt A) (~ k ∨ r) i
       ; (j = i0) → ((cong (λ x → rUnit x r)
                            (cong-∙ Ωp (merid (ptSn (suc n)))
                                       (sym (merid (ptSn _))))
                     ∙ cong (λ x → rUnit x r)
                            (cong (p-refl ∙_)
                                  (cong sym (flipSquare (cong snd p)))
                                ∙ sym (rUnit _)))
                     ∙ λ i → rUnit p-refl (~ i ∧ r)) k i
       ; (j = i1) → rUnit (λ _ → pt A) (~ k ∧ r) i
       ; (k = i0) → rUnit (cong Ωp (rCancel (merid (ptSn _)) j)) r i
       ; (k = i1) → snd (p i) j})
     (hcomp (λ r →
     λ { (i = i0) → pt A
       ; (i = i1) → pt A
       ; (j = i0) → ((rUnit (compPath-filler'
                             (cong-∙ Ωp (merid (ptSn (suc n)))
                                        (sym (merid (ptSn _))))
                       ((cong (p-refl ∙_)
                          (cong sym (flipSquare (cong snd p)))
                       ∙ sym (rUnit _))) r) r) k i)
       ; (j = i1) → pt A
       ; (k = i0) → help Ωp (merid (ptSn (suc n))) r j i
       ; (k = i1) → snd (p i) j})
      (lem p-refl (sym (flipSquare (cong snd p))) k j i)))
  where
  Ωp = (fst (ΩSphereMap {A = A} (suc n) p))
  wrap-refl : ∀ {ℓ} {A : Type ℓ} {x : A} {r s : x ≡ x} (p : r ≡ s) → _
  wrap-refl p = cong (refl ∙∙_∙∙ refl) p
  p-refl = funExt⁻ (cong fst p) (ptSn (suc n))

  cong-∙∙-filler : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {x y z w : A}
    (f : A → B) (p : w ≡ x) (q : x ≡ y) (r : y ≡ z) → I → I → I → B
  cong-∙∙-filler f p q r k j i =
    hfill (λ k → λ { (j = i0) → f (doubleCompPath-filler p q r k i)
                    ; (i = i0) → f (p (~ k))
                    ; (i = i1) → f (r k) })
          (inS (f (q i))) k

  lem : ∀ {ℓ} {A : Pointed ℓ} (p : Path (typ A) (pt A) (pt A)) (q : refl ≡ p)
    → PathP (λ i → (cong (p ∙_) (cong sym (sym q)) ∙ sym (rUnit p)) i ≡ refl)
             (rCancel p) (sym q)
  lem {A = A} p =
    J (λ p q →
         PathP (λ i → (cong (p ∙_) (cong sym (sym q)) ∙ sym (rUnit p)) i ≡ refl)
               (rCancel p) (sym q))
      (flipSquare (sym (lUnit (sym (rUnit refl)))
                 ◁ λ k i → rCancel (λ _ → pt A) (k ∨ i)))

  help : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {x y : A} (f : A → B) (p : x ≡ y)
       → PathP (λ k → cong-∙ f p (sym p) (~ k) ≡ refl)
                (rCancel (cong f p)) (cong (cong f) (rCancel p))
  help f p i j k =
    hcomp (λ r → λ { (i = i0) → rCancel-filler (cong f p) r j k
                    ; (i = i1) → f (rCancel-filler p r j k)
                    ; (j = i0) → cong-∙∙-filler f refl p (sym p) r (~ i) k
                    ; (j = i1) → f (p i0)
                    ; (k = i0) → f (p i0)
                    ; (k = i1) → f (p (~ r ∧ ~ j))})
          (f (p (~ j ∧ k)))

leftInv (SphereMapΩIso {A = A} zero) (f , p) =
  ΣPathP ((funExt (λ { base → sym p
                     ; (loop i) j
                       → doubleCompPath-filler (sym p) (cong f loop) p (~ j) i}))
          , λ i j → p (j ∨ ~ i))
leftInv (SphereMapΩIso {A = A} (suc n)) (f , p) =
  ΣPathP (funExt (λ { north → sym p
                    ; south → sym p ∙ cong f (merid (ptSn (suc n)))
                    ; (merid a i) j → help a j i})
         , λ i j → p (j ∨ ~ i))
  where
  help : (a : S₊ (suc n)) → PathP (λ i → p (~ i) ≡ (sym p ∙ cong f (merid (ptSn (suc n)))) i)
                                   (sym p ∙∙ cong f (merid a ∙ sym (merid (ptSn _))) ∙∙ p)
                                   (cong f (merid a))
  help a i j =
    hcomp (λ k →
      λ { (i = i0) → doubleCompPath-filler (sym p)
                        (cong f (merid a ∙ sym (merid (ptSn _)))) p k j
        ; (i = i1) → f (merid a j)
        ; (j = i0) → p (~ i ∧ k)
        ; (j = i1) → compPath-filler' (sym p)
                        (cong f (merid (ptSn (suc n)))) k i})
     (f (compPath-filler (merid a)
                         (sym (merid (ptSn _))) (~ i) j))

{-
In order to show that lMap is an equivalence, we show that it factors

        SphereMapΩ                 lMapSplit₁
Ωⁿ⁺¹A ----------------> Ω (Sⁿ →∙ A) -----------> (Sⁿ⁺¹ →∙ A)
-}


lMap-split : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) (p : typ ((Ω^ (suc n)) A))
    → lMap (suc n) p ≡ ΩSphereMap n (lMapSplit₁ n p)
lMap-split {A = A} zero p =
  ΣPathP ((funExt (λ { base → refl
                     ; (loop i) j → lem (~ j) i}))
         , refl)
  where
  lem : funExt⁻ (cong fst (lMapSplit₁ zero p)) false ≡ p
  lem = (λ i → funExt⁻ (cong-∙∙ fst (sym (lMapId2 zero))
                                     (cong (lMap zero) p)
                                     (lMapId2 zero) i) false)
    ∙ sym (rUnit _)
lMap-split {A = A} (suc n) p =
  ΣPathP ((funExt (λ { north → refl
                     ; south → refl
                     ; (merid a i) j → lem₂ a j i}))
          , refl)
  where
  lem : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) (a : S₊ (suc n))
    → lMapId (suc n) {A = A} a
    ≡ (λ i → fst (lMapId2 (suc n) {A = A} i) a)
  lem zero base = refl
  lem zero (loop i) = refl
  lem (suc n) north = refl
  lem (suc n) south = refl
  lem (suc n) (merid a i) = refl

  lem₂ : (a : S₊ (suc n))
     → ((λ i₁ → lMapId (suc n) {A = A} a (~ i₁))
     ∙∙ (λ i₁ → lMap (suc n) (p i₁) .fst a)
     ∙∙ lMapId (suc n) a)
     ≡ (λ i → lMapSplit₁ (suc n) p i .fst a)
  lem₂ a = cong (λ x → sym x
                 ∙∙ funExt⁻ (cong fst (λ i → lMap (suc n) (p i))) a
                 ∙∙ x)
             (lem n a)
     ∙∙ sym (cong-∙∙ (λ x → x a)
              (cong fst (λ i → lMapId2 (suc n) (~ i)))
              (cong fst (λ i → lMap (suc n) (p i)))
              (cong fst (lMapId2 (suc n))))
     ∙∙ (λ i → funExt⁻ (cong-∙∙ fst (sym (lMapId2 (suc n)))
                          (cong (lMap (suc n)) p)
                          (lMapId2 (suc n)) (~ i)) a)

isEquiv-lMap : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ}
  → isEquiv (lMap (suc n) {A = A})
isEquiv-lMap zero {A = A} =
  isoToIsEquiv (iso _ invFun sec λ p → sym (rUnit p))
  where
  invFun : S₊∙ 1 →∙ A → typ (Ω A)
  invFun (f , p) = sym p ∙∙ cong f loop ∙∙ p

  sec : section (lMap 1) invFun
  sec (f , p) =
    ΣPathP ((funExt (λ { base → sym p
                       ; (loop i) j → doubleCompPath-filler
                                        (sym p) (cong f loop) p (~ j) i}))
           , λ i j → p (~ i ∨ j))

isEquiv-lMap (suc n) =
  subst isEquiv (sym (funExt (lMap-split (suc n))))
    (snd (compEquiv
         ((lMapSplit₁ (suc n)) ,
              (isEquivΩ→ (lMap (suc n) , lMapId2 (suc n))
                           (isEquiv-lMap n)))
         (invEquiv (isoToEquiv (SphereMapΩIso (suc n))))))


-- The homogeneity assumption is not necessary but simplifying
module _ {ℓ ℓ'} (A : Pointed ℓ) (B : Pointed ℓ') (homogB : isHomogeneous B) (f : A →∙ B)
  where

  isNaturalΩSphereMap : (n : ℕ)
    → ∀ g → f ∘∙ ΩSphereMap n g ≡ ΩSphereMap n (Ω→ (post∘∙ (S₊∙ n) f) .fst g)
  isNaturalΩSphereMap 0 g =
    →∙Homogeneous≡ homogB (funExt lem)
    where
    lem : ∀ x → f .fst (ΩSphereMap 0 g .fst x) ≡ ΩSphereMap 0 (Ω→ (post∘∙ (S₊∙ 0) f) .fst g) .fst x
    lem base = f .snd
    lem (loop i) j =
      hfill
        (λ j → λ
          { (i = i0) → post∘∙ _ f .snd j
          ; (i = i1) → post∘∙ _ f .snd j
          })
        (inS (f ∘∙ g i))
        j .fst false
  isNaturalΩSphereMap (n@(suc _)) g =
    →∙Homogeneous≡ homogB (funExt lem)
    where
    lem : ∀ x → f .fst (ΩSphereMap n g .fst x) ≡ ΩSphereMap n (Ω→ (post∘∙ (S₊∙ n) f) .fst g) .fst x
    lem north = f .snd
    lem south = f .snd
    lem (merid a i) j =
      hfill
        (λ j → λ
          { (i = i0) → post∘∙ _ f .snd j
          ; (i = i1) → post∘∙ _ f .snd j
          })
        (inS (f ∘∙ g i))
        j .fst a

  mutual
    isNatural-lMap : ∀ n p → f ∘∙ lMap n p ≡ lMap n (Ω^→ n f .fst p)
    isNatural-lMap 0 p =
      →∙Homogeneous≡ homogB (funExt λ {true → f .snd; false → refl})
    isNatural-lMap (n@(suc n')) p =
      cong (f ∘∙_) (lMap-split n' p)
      ∙ isNaturalΩSphereMap n' (lMapSplit₁ n' p)
      ∙ cong (ΩSphereMap n') inner
      ∙ sym (lMap-split n' (Ω^→ n f .fst p))
      where
      inner : Ω→ (post∘∙ (S₊∙ n') f) .fst (Ω→ (lMap∙ n') .fst p) ≡ Ω→ (lMap∙ n') .fst (Ω^→ (suc n') f .fst p)
      inner =
        sym (Ω→∘ (post∘∙ (S₊∙ n') f) (lMap∙ n') p)
        ∙ cong (λ g∙ → Ω→ g∙ .fst p) (isNatural-lMap∙ n')
        ∙ Ω→∘ (lMap∙ n') (Ω^→ n' f) p

    isNatural-lMap∙ : ∀ n → post∘∙ (S₊∙ n) f ∘∙ (lMap∙ n) ≡ (lMap∙ n {A = B} ∘∙ Ω^→ n f)
    isNatural-lMap∙ n = →∙Homogeneous≡ (isHomogeneous→∙ homogB) (funExt (isNatural-lMap n))


σ : ∀ {ℓ} (A : Pointed ℓ) (a : typ A) → Path (Susp (typ A)) north north
σ A a = merid a ∙ sym (merid (pt A))

σ∙ : ∀ {ℓ} (A : Pointed ℓ) → A →∙ Ω (Susp∙ (typ A))
fst (σ∙ A) = σ A
snd (σ∙ A) = rCancel _


top□ : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
      → Ω^→ (suc n) (σ∙ A)
      ≡ (((Iso.fun (flipΩIso (suc n))) , flipΩrefl n)
        ∘∙ suspMapΩ∙ (suc n))
top□ {A = A} zero =
  →∙Homogeneous≡ (isHomogeneousPath _ _)
    (funExt λ p → sym (transportRefl _))
top□ {A = A} (suc n) =
    cong Ω→ (top□ {A = A} n)
  ∙ →∙Homogeneous≡
    (isHomogeneousPath _ _)
    (funExt λ x
      → Ω→∘ (fun (flipΩIso (suc n)) , flipΩrefl n) (suspMapΩ∙ (suc n)) x)

{-          suspMapΩ
 Ωⁿ A  --------------------> Ω¹⁺ⁿ (Susp A)
 |                           |
 | =                         | ≃ flipΩ
 |          Ωⁿ→ σ           v
Ωⁿ A -------------------> Ωⁿ (Ω (Susp A))
 |                           |
 |                           |
 | ≃ lMap                    | ≃ lMap
 |                           |
 v           post∘∙ . σ      v
 (Sⁿ →∙ A) -------------- > (Sⁿ →∙ Ω (Susp A))
 |                           |
 | =                         | ≃ botᵣ
 |                           |
 v            suspMap        v
 (Sⁿ →∙ A) -------------- > (Sⁿ⁺¹→∙ Susp A)
 -}


mid□ : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
         → (p : typ ((Ω^ (suc n)) A))
        → fst (post∘∙ (S₊∙ (suc n)) (σ∙ A)) (lMap (suc n) p)
        ≡ lMap (suc n) (fst (Ω^→ (suc n) (σ∙ A)) p)
mid□ {A = A} n p =
  funExt⁻
    (cong fst
      (isNatural-lMap∙
        A (Ω (Susp∙ (typ A)))
        (isHomogeneousPath _ _)
        (σ∙ A) (suc n))) p

botᵣ : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
  → (S₊∙ n →∙ Ω (Susp∙ (typ A)))
  → S₊∙ (suc n) →∙ Susp∙ (typ A)
fst (botᵣ zero (f , p)) base = north
fst (botᵣ zero (f , p)) (loop i) = f false i
snd (botᵣ zero (f , p)) = refl
fst (botᵣ (suc n) (f , p)) north = north
fst (botᵣ (suc n) (f , p)) south = north
fst (botᵣ (suc n) (f , p)) (merid a i) = f a i
snd (botᵣ (suc n) (f , p)) = refl


botᵣ⁻' : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
         → S₊∙ (suc n) →∙ Susp∙ (typ A) → (S₊ n → typ (Ω (Susp∙ (typ A))))
botᵣ⁻' zero f false =
  sym (snd f) ∙∙ cong (fst f) loop ∙∙ snd f
botᵣ⁻' zero f true = refl
botᵣ⁻' (suc n) f x =
     sym (snd f)
  ∙∙ cong (fst f) (merid x ∙ sym (merid (ptSn (suc n))))
  ∙∙ snd f

botᵣ⁻ : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
  → S₊∙ (suc n) →∙ Susp∙ (typ A)
  → (S₊∙ n →∙ Ω (Susp∙ (typ A)))
fst (botᵣ⁻ {A = A} n f) = botᵣ⁻' {A = A} n f
snd (botᵣ⁻ {A = A} zero f) = refl
snd (botᵣ⁻ {A = A} (suc n) f) =
  cong (sym (snd f) ∙∙_∙∙ snd f)
       (cong (cong (fst f)) (rCancel (merid (ptSn _))))
     ∙ ∙∙lCancel (snd f)

-- botᵣ is an Iso
botᵣIso : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
    → Iso (S₊∙ n →∙ Ω (Susp∙ (typ A)))
           (S₊∙ (suc n) →∙ Susp∙ (typ A))
botᵣIso {A = A} n = (iso (botᵣ {A = A} n) (botᵣ⁻ {A = A} n) (h n) (retr n))
  where
  h : (n : ℕ) → section (botᵣ {A = A} n) (botᵣ⁻ {A = A} n)
  h zero (f , p) =
    ΣPathP (funExt (λ { base → sym p
                      ; (loop i) j → doubleCompPath-filler
                                       (sym p) (cong f loop) p (~ j) i})
          , λ i j → p (~ i ∨ j))
  h (suc n) (f , p) =
    ΣPathP (funExt (λ { north → sym p
                      ; south → sym p ∙ cong f (merid (ptSn _))
                      ; (merid a i) j
                       → hcomp (λ k
                         → λ { (i = i0) → p (~ j ∧ k)
                              ; (i = i1) → compPath-filler'
                                           (sym p) (cong f (merid (ptSn _))) k j
                              ; (j = i1) → f (merid a i)})
                           (f (compPath-filler
                              (merid a) (sym (merid (ptSn _))) (~ j) i))})
         , λ i j → p (~ i ∨ j))

  retr : (n : ℕ) → retract (botᵣ {A = A} n) (botᵣ⁻ {A = A} n)
  retr zero (f , p) =
    ΣPathP ((funExt (λ { false → sym (rUnit _) ; true → sym p}))
       , λ i j → p (~ i ∨ j))
  retr (suc n) (f , p) =
    →∙Homogeneous≡ (isHomogeneousPath _ _)
                   (funExt λ x → (λ i
                     → rUnit (cong-∙ (fst ((botᵣ {A = A}(suc n) (f , p))))
                                      (merid x)
                                      (sym (merid (ptSn (suc n)))) i) (~ i))
                   ∙∙ (λ i → f x ∙ sym (p i) )
                   ∙∙ sym (rUnit (f x)))


bot□ : ∀ {ℓ} {A : Pointed ℓ}  (n : ℕ) (f : (S₊∙ (suc n) →∙ A))
      → suspMap n f ≡ botᵣ {A = A} (suc n) (post∘∙ (S₊∙ (suc n)) (σ∙ A) .fst f)
bot□ {A = A} n f =
  ΣPathP ((funExt (λ { north → refl
                     ; south → refl
                     ; (merid a i) → refl}))
         , refl)


IsoΩSphereMap : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
  → Iso (typ ((Ω^ n) A)) ((S₊∙ n →∙ A))
fun (IsoΩSphereMap zero) = lMap zero
inv (IsoΩSphereMap zero) f = fst f false
rightInv (IsoΩSphereMap zero) f =
  ΣPathP ((funExt (λ { false → refl
                     ; true → sym (snd f)}))
         , λ i j → snd f (~ i ∨ j))
leftInv (IsoΩSphereMap zero) p = refl
IsoΩSphereMap (suc n) = equivToIso (_ , isEquiv-lMap n)

IsoΩSphereMapᵣ : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
  → Iso (typ ((Ω^ (suc n)) (Susp∙ (typ A)))) ((S₊∙ (suc n) →∙ Susp∙ (typ A)))
IsoΩSphereMapᵣ {A = A} n =
  compIso (flipΩIso n)
    (compIso (IsoΩSphereMap n) (botᵣIso {A = A} n))

suspMapPathP : ∀ {ℓ} (A : Pointed ℓ) (n : ℕ)
               → (typ ((Ω^ (suc n)) A) → (typ ((Ω^ (suc (suc n))) (Susp∙ (typ A)))))
                ≡ ((S₊∙ (suc n) →∙ A) → S₊∙ (suc (suc n)) →∙ (Susp∙ (typ A)))
suspMapPathP A n i =
    isoToPath (IsoΩSphereMap {A = A} (suc n)) i
  → isoToPath (IsoΩSphereMapᵣ {A = A} (suc n)) i

Ωσ→suspMap : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
           → PathP (λ i → suspMapPathP A n i)
                    (suspMapΩ (suc n))
                    (suspMap n)
Ωσ→suspMap {A = A} n =
  toPathP (funExt (λ p →
       (λ i → transportRefl
                (Iso.fun (IsoΩSphereMapᵣ {A = A} (suc n))
                  (suspMapΩ {A = A} (suc n)
                    (Iso.inv (IsoΩSphereMap {A = A} (suc n))
                      (transportRefl p i)))) i)
    ∙∙ cong (botᵣ {A = A} (suc n))
            (cong (lMap (suc n) {A = Ω (Susp∙ (typ A)) })
                  ((sym (funExt⁻ (cong fst (top□ {A = A} n))
                     (invEq (lMap (suc n) , isEquiv-lMap n) p))))
           ∙ (sym (mid□ n (invEq (lMap (suc n) , isEquiv-lMap n) p))
             ∙ cong (σ∙ (fst A , snd A) ∘∙_)
                    (secEq (lMap (suc n) , isEquiv-lMap n) p)))
    ∙∙ sym (bot□ n p)))
