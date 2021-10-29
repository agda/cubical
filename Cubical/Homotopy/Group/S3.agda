{-# OPTIONS --safe #-}
{-
This file contains
1. The definition of πₙ as a truncated loop space
2. The definition of πₙ as a truncated function space (Sⁿ →∙ A)
3. A structure preserving equivalence Ωⁿ A ≃ (Sⁿ →∙ A)
4. A proof that the two constructions of homotopy groups are isomorphic
-}
module Cubical.Homotopy.Group.S3 where

open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Loopspace

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws renaming (assoc to ∙assoc)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Functions.Embedding
open import Cubical.Functions.Morphism
open import Cubical.Foundations.Pointed.Homogeneous

open import Cubical.HITs.SetTruncation
  renaming (rec to sRec ; rec2 to sRec2 ; elim to sElim
          ; elim2 to sElim2 ; elim3 to sElim3 ; map to sMap)
open import Cubical.HITs.PropositionalTruncation
  renaming (rec to pRec ; rec2 to pRec2 ; elim to pElim)
open import Cubical.HITs.Sn
open import Cubical.Data.Bool hiding (_≟_)
open import Cubical.HITs.Susp
open import Cubical.HITs.S1
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

open import Cubical.Homotopy.Freudenthal
open import Cubical.Homotopy.Connected
open import Cubical.Foundations.Equiv
open import Cubical.HITs.Truncation
  renaming (rec to trRec ; elim to trElim ; map to trMap)


open import Cubical.Data.Sum
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty

open import Cubical.Foundations.Equiv.HalfAdjoint

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

where lMap and eq₂ are structure preserving equivalences
(we choose them (intensionally) different for techinical reasons)
-}

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
{-
Ω (Ωⁿ A) -----------> Ω (Ωⁿ⁺¹ ΣA)
 |                  |
 |                  |
 |                  |
 v                  v
 Ω (Sⁿ →∙ A) ----> Ω (Sⁿ⁺¹ →∙ ΣA)
 |                  |
 |                  |
 |                  |
 v                  v
 (Sⁿ⁺¹ →∙ A) ----> Sⁿ⁺² →∙ Σ A 
-}

-- Move to loopspace
Ω-fun : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
      → (A →∙ B) → (Ω A →∙ Ω B)
fst (Ω-fun {A = A} {B = B} (f , p)) q = sym p ∙∙ cong f q ∙∙ p
snd (Ω-fun {A = A} {B = B} (f , p)) = ∙∙lCancel p

-- move to loop space
open import Cubical.Foundations.Equiv.HalfAdjoint
isEquivΩfun : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
           → (f : (A →∙ B))
           → isEquiv (fst f) → isEquiv (Ω-fun f .fst)
isEquivΩfun {B = (B , b)} =
  uncurry λ f →
    J (λ b y → isEquiv f → isEquiv (λ q → (λ i → y (~ i)) ∙∙ (λ i → f (q i)) ∙∙ y))
      λ eqf → subst isEquiv (funExt (rUnit ∘ cong f))
                     (isoToIsEquiv (congIso (equivToIso (f , eqf))))


-- We define the following maps which will be used to
-- show that lMap is an equivalence
lMapSplit₁ : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
           → typ ((Ω^ (suc n)) A)
           → typ (Ω (S₊∙ n →∙ A ∙))
lMapSplit₁ n = Ω-fun (lMap n , lMapId2 n) .fst

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
        , flipSquare (cong (sym p ∙∙_∙∙ p) (cong (cong f) (rCancel (merid (ptSn _))))
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
      (cool2 p-refl (sym (flipSquare (cong snd p))) k j i)))
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

  cool2 : ∀ {ℓ} {A : Pointed ℓ} (p : Path (typ A) (pt A) (pt A)) (q : refl ≡ p)
    → PathP (λ i → (cong (p ∙_) (cong sym (sym q)) ∙ sym (rUnit p)) i ≡ refl)
             (rCancel p) (sym q)
  cool2 {A = A} p =
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
              (isEquivΩfun (lMap (suc n) , lMapId2 (suc n))
                           (isEquiv-lMap n)))
         (invEquiv (isoToEquiv (SphereMapΩIso (suc n))))))

botMap : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ}
        → (S₊∙ n →∙ A)
        → S₊∙ n →∙ Ω (Susp∙ (typ A))
fst (botMap n {A = A} f) x = merid (fst f x) ∙ sym (merid (pt A))
snd (botMap n {A = A} f) = cong (_∙ merid (pt A) ⁻¹) (cong merid (snd f))
                         ∙ rCancel (merid (pt A))

rMap : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ}
    → typ ((Ω^ (suc n)) (Susp∙ (typ A)))
    → (S₊∙ n →∙ Ω (Susp∙ (typ A)))
rMap n = lMap n ∘ Iso.fun (flipΩIso n)

private
  rMap1 : ∀ {ℓ} {A : Pointed ℓ}
    → typ ((Ω^ (suc 1)) (Susp∙ (typ A)))
    → (S₊∙ 1 →∙ Ω (Susp∙ (typ A)))
  rMap1 = lMap 1

  rMap≡rMap1 : ∀ {ℓ} {A : Pointed ℓ} → rMap 1 {A = A} ≡ rMap1 {A = A}
  rMap≡rMap1 = funExt λ x → cong (lMap 1) (transportRefl x)

flipΩrefl : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
  → fun (flipΩIso {A = A} (suc n)) refl ≡ refl
flipΩrefl {A = A} n j =
  transp (λ i₁ → fst (Ω (flipΩPath {A = A} n ((i₁ ∨ j))))) j (snd (Ω (flipΩPath n j)))

cong-lMap-lem : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) (p : _)
  → cong (lMap (suc n) {A = Ω A}) (fun (flipΩIso (suc (suc n))) p)
   ≡ (cong (lMap (suc n)) (sym (flipΩrefl n))
        ∙∙ cong (lMap (suc n) ∘ fun (flipΩIso (suc n))) p
      ∙∙ cong (lMap (suc n)) (flipΩrefl n))
cong-lMap-lem {A = A} n p =
    (λ i → cong (lMap (suc n) {A = Ω A})
                 (fun (flipΩIso (suc (suc n))) (rUnit p i)))
  ∙∙ (λ i j → lMap (suc n) {A = Ω A}
      (transp (λ k → fst (flipΩPath {A = A} (suc (suc n)) (k ∨ i))) i
        (((λ j → transp (λ k → fst (Ω (flipΩPath {A = A} n ((k ∨ ~ j) ∧ i))))
                         (~ i ∨ ~ j)
                         (snd (Ω (flipΩPath n (~ j ∧ i)))))
        ∙∙ (λ j → transp (λ k → fst (flipΩPath {A = A} (suc n)
                          (k ∧ i))) (~ i) (p j))
        ∙∙ λ j → transp (λ k → fst (Ω (flipΩPath {A = A} n ((k ∨ j) ∧ i))))
                         (~ i ∨ j) (snd (Ω (flipΩPath n (j ∧ i)))))) j))
  ∙∙ cong-∙∙ (lMap (suc n))
             (sym (flipΩrefl n))
             (cong (fun (flipΩIso (suc n))) p)
             (flipΩrefl n)

botₗ : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
  → (S₊∙ n →∙ A) → S₊∙ (suc n) →∙ (Susp∙ (typ A))
fst (botₗ zero f) base = north
fst (botₗ {A = A} zero f) (loop i) = (merid (fst f false) ∙ sym (merid (pt A))) i
snd (botₗ zero f) = refl
botₗ (suc n) f = suspMap n f

botᵣ : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
  → (S₊∙ n →∙ Ω (Susp∙ (typ A))) → S₊∙ (suc n) →∙ Susp∙ (typ A)
fst (botᵣ zero (f , p)) base = north
fst (botᵣ zero (f , p)) (loop i) = f false i
snd (botᵣ zero (f , p)) = refl
fst (botᵣ (suc n) (f , p)) north = north
fst (botᵣ (suc n) (f , p)) south = north
fst (botᵣ (suc n) (f , p)) (merid a i) = f a i
snd (botᵣ (suc n) (f , p)) = refl

{-
The goal now is to fill the following diagram.

               suspMap
((Ω^ n) A) ------------>  Ω^ (1 + n) (Susp A)
      |                            |
      |                            |
 lMap | ≃                        ≃ |  rMap
      v                            v
(S₊∙ n →∙ A) ---------->  (S₊∙ n →∙ Ω (Susp A))
      \          botMap          /
        \                      /
          \                  /
     botₗ   \               / botᵣ
   (suspMap) \           /
               \       /
                 \   /
                   v
            (Sⁿ⁺¹ →∙ Susp A)

-}

-- The bottom part is trival▿
filler▿ : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) (x : (S₊∙ n →∙ A))
       → botₗ n x ≡ botᵣ {A = A} n (botMap n x)
filler▿ zero (f , p) =
  ΣPathP ((funExt (λ { base → refl ; (loop i) → refl})) , refl)
filler▿ (suc n) (f , p) =
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

Ω≡SphereMap : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → (typ ((Ω^ n) A)) ≡ ((S₊∙ n →∙ A))
Ω≡SphereMap n = isoToPath (IsoΩSphereMap n)

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
  cong (sym (snd f) ∙∙_∙∙ snd f) (cong (cong (fst f)) (rCancel (merid (ptSn _)))) ∙ ∙∙lCancel (snd f)

isEquiv-rMap : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → isEquiv (rMap n {A = A})
isEquiv-rMap zero =
  compEquiv (isoToEquiv (flipΩIso zero))
            (isoToEquiv (IsoΩSphereMap zero)) .snd
isEquiv-rMap (suc n) =
  compEquiv (isoToEquiv (flipΩIso (suc n)))
            (isoToEquiv (IsoΩSphereMap (suc n))) .snd

-- botᵣ is an Iso
botᵣIso : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
    → Iso (S₊∙ n →∙ Ω (Susp∙ (typ A)))
           (S₊∙ (suc n) →∙ Susp∙ (typ A))
botᵣIso {A = A} n = (iso (botᵣ {A = A} n) (botᵣ⁻ {A = A} n) (h n) (retr n))
  where
  h : (n : ℕ) → section (botᵣ {A = A} n) (botᵣ⁻ {A = A} n)
  h zero (f , p) =
    ΣPathP (funExt (λ { base → sym p
                      ; (loop i) j → doubleCompPath-filler (sym p) (cong f loop) p (~ j) i})
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
                           (f (compPath-filler (merid a) (sym (merid (ptSn _))) (~ j) i))})
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

IsoΩSphereMap' : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
  → Iso (typ ((Ω^ (suc n)) (Susp∙ (typ A))))
         (S₊∙ (suc n) →∙ Susp∙ (typ A))
IsoΩSphereMap' {A = A} n =
  compIso (equivToIso (_ , isEquiv-rMap {A = A} n))
    (botᵣIso {A = A} n)

Ω≡SphereMap' : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
            → (typ ((Ω^ (suc n)) (Susp∙ (typ A))))
             ≡ (S₊∙ (suc n) →∙ Susp∙ (typ A))
Ω≡SphereMap' {A = A} n = isoToPath (IsoΩSphereMap' {A = A} n)

filler-top□ : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ}
         →  rMap n {A = A} ∘ (suspMapΩ {A = A} n)
          ≡ botMap n ∘ lMap n {A = A}
filler-top□ {ℓ} =
  +nInd (λ {A} → funExt λ p → →∙Homogeneous≡ (isHomogeneousPath _ _)
                   (funExt λ { false → transportRefl _
                             ; true → sym (rCancel _)}))
        (λ {A} → funExt λ p → →∙Homogeneous≡ (isHomogeneousPath _ _)
                   (funExt λ x
                     → (λ i → ((rMap≡rMap1 {A = A} i) ∘ suspMapΩ 1) p .fst x)
                      ∙ sym (lem₁ p x)))
                 cool*
  where
  lem₁ : ∀ {ℓ} {A : Pointed ℓ} (p : _) (x : S¹)
       → (botMap 1 ∘ lMap 1) p .fst x
        ≡ (rMap1 {A = A} ∘ (suspMapΩ {A = A} 1)) p .fst x
  lem₁ {A = A} p base = rCancel (merid (pt A))
  lem₁ {A = A} p (loop i) j =
    doubleCompPath-filler
      (sym (rCancel (merid (pt A))))
      (cong (λ x → merid x ∙ sym (merid (pt A))) p)
      (rCancel (merid (pt A))) j i

  cool* : (n : ℕ) →
      ({A : Pointed ℓ} →
       rMap (suc n) {A = A} ∘ suspMapΩ (suc n) ≡
       botMap (suc n) ∘ lMap (suc n)) →
      {A : Pointed ℓ} →
      rMap (suc (suc n)) {A = A} ∘ suspMapΩ (suc (suc n)) ≡
      botMap (suc (suc n)) ∘ lMap (suc (suc n))
  cool* n ind {A} =
    funExt λ p → →∙Homogeneous≡ (isHomogeneousPath (Susp (typ A)) refl)
      (funExt
        λ { north → sym (rCancel (merid (pt A)))
          ; south → sym (rCancel (merid (pt A)))
          ; (merid a i) j
          → hcomp (λ k
            → λ {( i = i0) → rCancel (merid (pt A)) (~ j)
                 ; (i = i1) → rCancel (merid (pt A)) (~ j)
                 ; (j = i0) → main p a (~ k) i
                 ; (j = i1) → (botMap (suc (suc n)) ∘ lMap (suc (suc n))) p .fst
                                (merid a i)})
              (doubleCompPath-filler
                (sym (rCancel (merid (pt A))))
                (cong ((botMap (suc (suc n)) ∘ lMap (suc (suc n))) p .fst)
                      (merid a))
                (rCancel (merid (pt A))) (~ j) i)})
    where
    module _ (p : typ (Ω _)) (a : S₊ (suc n)) where
      abstract
        indHyp : Path ((a₁ : fst (Ω ((Ω^ n) A))) →
          Σ (fst (S₊∙ (suc n)) → fst (Ω (Susp∙ (typ A))))
          (λ f → f (snd (S₊∙ (suc n))) ≡ snd (Ω (Susp∙ (typ A)))))
                ((rMap (suc n) {A = A} ∘ (suspMapΩ {A = A} (suc n))))
                (botMap (suc n) ∘ lMap (suc n) {A = A})
        indHyp =
          funExt λ a → →∙Homogeneous≡ (isHomogeneousPath _ _)
            (funExt (λ x → funExt⁻ (cong fst (funExt⁻ (ind {A = A}) a)) x))

      pathLem₁ : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ z)
               → p ∙ (q ∙ r ∙ sym q) ∙ sym p ≡ (p ∙ q) ∙ r ∙ sym (p ∙ q)
      pathLem₁ p q r =
          ∙assoc p (q ∙ r ∙ sym q) (sym p)
        ∙ cong (_∙ sym p) (∙assoc p q (r ∙ sym q))
        ∙ sym (∙assoc (p ∙ q) (r ∙ sym q) (sym p))
        ∙ cong ((p ∙ q) ∙_) (sym (∙assoc r (sym q) (sym p))
                          ∙ cong (r ∙_) (sym (symDistr p q)))

      pathLem₂ : ∀ {ℓ} {A : Type ℓ} {x y : A} (coh : x ≡ y) (p : x ≡ x)
        → p ≡ coh ∙ (sym coh ∙∙ p ∙∙ coh) ∙ sym coh
      pathLem₂ {x = x} =
        J (λ y coh → (p : x ≡ x) → p ≡ coh ∙ (sym coh ∙∙ p ∙∙ coh) ∙ sym coh)
           λ p → lUnit _ ∙ cong (refl ∙_) (rUnit _ ∙ cong (_∙ refl) (rUnit p))

      pathLem₃ : ∀ {ℓ} {A : Type ℓ} {x₀ x y z w : A}
                (p : x₀ ≡ x) (q : x ≡ y) (r : y ≡ z) (s : z ≡ w) (mid : w ≡ w)
                (coh : x₀ ≡ w)
              → isComm∙ (A , x₀)
              → (p ∙∙ q ∙∙ r
               ∙∙ s ∙∙ mid ∙∙ sym s
               ∙∙ sym r ∙∙ sym q ∙∙ sym p)
              ≡ (coh ∙∙ mid ∙∙ sym coh)
      pathLem₃ p q r s mid coh comm =
        doubleCompPath≡compPath p _ (sym p)
       ∙∙ cong (λ x → p ∙ x ∙ (sym p))
               (doubleCompPath≡compPath q _ (sym q)
               ∙ cong (λ x → q ∙ x ∙ (sym q))
                      (doubleCompPath≡compPath r _ (sym r)
                      ∙ cong (λ x → r ∙ x ∙ (sym r))
                        (doubleCompPath≡compPath s _ (sym s)
                         ∙ cong (λ x → s ∙ x ∙ sym s) (pathLem₂ (sym coh) mid)
                         ∙ pathLem₁ s (sym coh) (coh ∙∙ mid ∙∙ sym coh))
                         ∙ pathLem₁ r (s ∙ sym coh) (coh ∙∙ mid ∙∙ sym coh))
                         ∙ pathLem₁ q (r ∙ s ∙ sym coh) (coh ∙∙ mid ∙∙ sym coh))
       ∙∙ pathLem₁ p (q ∙ r ∙ s ∙ sym coh) (coh ∙∙ mid ∙∙ sym coh)
       ∙∙ cong ((p ∙ q ∙ r ∙ s ∙ sym coh) ∙_)
               (comm (coh ∙∙ mid ∙∙ sym coh) (sym (p ∙ q ∙ r ∙ s ∙ sym coh)))
       ∙∙ ∙assoc _ _ _
       ∙∙ cong (_∙ (coh ∙∙ mid ∙∙ sym coh)) (rCancel _)
       ∙∙ sym (lUnit _)

      pathLem₄ : ∀ {ℓ} {A : Type ℓ} {x y z : A}
                 (p : z ≡ x) (q : y ≡ z) (r : y ≡ y)
              → (sym (q ∙ p) ∙∙ r ∙∙ (q ∙ p))
              ≡ (sym p ∙∙ sym q ∙∙ r ∙∙ q ∙∙ p)
      pathLem₄ p q r =
           cong (λ x → x ∙∙ r ∙∙ (q ∙ p)) (symDistr q p)
        ∙∙ doubleCompPath≡compPath (sym p ∙ sym q) r (q ∙ p)
        ∙∙ (sym (∙assoc (sym p) (sym q) (r ∙ q ∙ p))
        ∙∙ cong (sym p ∙_) (∙assoc (sym q) r (q ∙ p)
                          ∙ ∙assoc (sym q ∙ r) q p)
        ∙∙ sym (doubleCompPath≡compPath (sym p) ((sym q ∙ r) ∙ q) p)
         ∙ cong (sym p ∙∙_∙∙ p)
            (sym (∙assoc (sym q) r q)
            ∙ sym (doubleCompPath≡compPath (sym q) r q)))

      cong-lMap : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) (x : _)
                   (p : refl ≡ x) (q : _ ≡ _) (a : S₊ (suc n))
                → (cong (lMap (suc n) {A = Ω A})
                         (fun (flipΩIso (suc (suc n))) (p ∙∙ q ∙∙ sym p)))
                ≡ (cong (lMap (suc n)) (sym (flipΩrefl n))
                  ∙∙ cong (lMap (suc n) ∘ fun (flipΩIso (suc n))) p
                  ∙∙ cong (lMap (suc n) ∘ fun (flipΩIso (suc n))) q
                  ∙∙ sym (cong (lMap (suc n) ∘ fun (flipΩIso (suc n))) p)
                  ∙∙ cong (lMap (suc n)) (flipΩrefl n))
      cong-lMap n x =
        J (λ x p → (q : x ≡ x)
        → S₊ (suc n)
        → cong (lMap (suc n))
        (fun (flipΩIso (suc (suc n))) (p ∙∙ q ∙∙ sym p))
        ≡
        (cong (lMap (suc n)) (sym (flipΩrefl n)) ∙∙
         cong (lMap (suc n) ∘ fun (flipΩIso (suc n))) p ∙∙
         cong (lMap (suc n) ∘ fun (flipΩIso (suc n))) q ∙∙
         sym (cong (lMap (suc n) ∘ fun (flipΩIso (suc n))) p)
         ∙∙ cong (lMap (suc n)) (flipΩrefl n)))
          λ q a → (λ j i → lMap (suc n)
                      (fun (flipΩIso (suc (suc n))) (rUnit q (~ j)) i))
                 ∙∙ cong-lMap-lem n q
                 ∙∙ cong (cong (lMap (suc n)) (sym (flipΩrefl n))
                         ∙∙_∙∙
                          cong (lMap (suc n)) (flipΩrefl n))
                     (rUnit (cong (lMap (suc n) ∘ fun (flipΩIso (suc n))) q))

      main : cong ((rMap (suc (suc n)) {A = A}
                   ∘ suspMapΩ (suc (suc n))) p .fst) (merid a)
              ≡ (sym (rCancel (merid (pt A)))
             ∙∙ (λ i → (botMap (suc (suc n)) ∘ lMap (suc (suc n)) {A = A})
                         p .fst (merid a i))
              ∙∙ rCancel _)
      main =  cong (sym (lMapId (suc n) a) ∙∙_∙∙ (lMapId (suc n) a))
                   (cong (cong (λ x → fst x a))
                     (cong-lMap _ _
                       (sym (∙∙lCancel (snd (suspMapΩ∙ n))))
                       (cong (suspMapΩ (suc n)) p) a))
           ∙∙ cong (sym (lMapId (suc n) a) ∙∙_∙∙ (lMapId (suc n) a))
                   ((cong-∙∙ (λ x → fst x a)
                     (cong (lMap (suc n)) (sym (flipΩrefl n)))
                         (cong (lMap (suc n) ∘ fun (flipΩIso (suc n)))
                               (sym (∙∙lCancel (snd (suspMapΩ∙ n))))
                       ∙∙ cong (lMap (suc n) ∘ fun (flipΩIso (suc n)))
                               (cong ((suspMapΩ∙ (suc n)) .fst) p)
                       ∙∙ cong (lMap (suc n) ∘ fun (flipΩIso (suc n)))
                               (∙∙lCancel (snd (suspMapΩ∙ n))))
                     (cong (lMap (suc n)) (flipΩrefl n))))
           ∙∙ cong (sym (lMapId (suc n) a) ∙∙_∙∙ (lMapId (suc n) a))
                    (cong (cong (λ x → fst x a)
                                (cong (lMap (suc n)) (sym (flipΩrefl n)))
                          ∙∙_∙∙
                          cong (λ x → fst x a)
                               (cong (lMap (suc n)) (flipΩrefl n)))
                          (cong-∙∙ (λ x → fst x a)
                           (cong (lMap (suc n) ∘ fun (flipΩIso (suc n)))
                                 (sym (∙∙lCancel (snd (suspMapΩ∙ n)))))
                           (cong (lMap (suc n) ∘ fun (flipΩIso (suc n)))
                                 (cong ((suspMapΩ∙ (suc n)) .fst) p))
                           (cong (lMap (suc n) ∘ fun (flipΩIso (suc n)))
                                 (∙∙lCancel (snd (suspMapΩ∙ n))))))
           ∙∙ cong (sym (lMapId (suc n) a) ∙∙_∙∙ (lMapId (suc n) a))
               (cong (cong (λ x → fst x a)
                           (cong (lMap (suc n)) (sym (flipΩrefl n)))
                     ∙∙_∙∙
                     cong (λ x → fst x a)
                          (cong (lMap (suc n)) (flipΩrefl n)))
                     (cong (cong (λ x → fst x a)
                            (cong (lMap (suc n) ∘ fun (flipΩIso (suc n)))
                             (sym (∙∙lCancel (snd (suspMapΩ∙ n)))))
                              ∙∙_∙∙
                            cong (λ x → fst x a)
                             (cong (lMap (suc n) ∘ fun (flipΩIso (suc n)))
                              (∙∙lCancel (snd (suspMapΩ∙ n)))))
                            ((λ i j → rMap (suc n) {A = A}
                                        (suspMapΩ∙ (suc n) .fst (p j)) .fst a)
                             ∙ rUnit _
                             ∙ λ i → (λ j → indHyp (i ∧ j)
                                             (snd (Ω ((Ω^ n) A))) .fst a)
                                   ∙∙ (λ j → indHyp i (p j) .fst a)
                                   ∙∙ λ j → indHyp (i ∧ ~ j)
                                             (snd (Ω ((Ω^ n) A))) .fst a)))
           ∙∙ pathLem₃
                (sym (lMapId (suc n) a))
                (λ i₁ → fst (lMap (suc n) (flipΩrefl n (~ i₁))) a)
                (λ i₁ → fst (lMap (suc n) (fun (flipΩIso (suc n))
                             (∙∙lCancel (snd (suspMapΩ∙ {A = A} n)) (~ i₁)))) a)
                (λ j₁ → indHyp j₁ (snd (Ω ((Ω^ n) A))) .fst a)
                (λ j₁ → (botMap (suc n) ∘ lMap (suc n)) (p j₁) .fst a)
                (sym (cong (_∙ sym (merid (pt A)))
                      (cong merid (lMapId (suc n) a)) ∙ rCancel _))
                (EH 0)
           ∙∙ pathLem₄ (rCancel (merid (pt A)))
                      (cong (_∙ sym (merid (pt A)))
                       (cong merid (lMapId (suc n) a)))
                      (λ j₁ → (botMap (suc n) ∘ lMap (suc n)) (p j₁) .fst a)
           ∙∙ cong (sym (rCancel (merid (pt A))) ∙∙_∙∙ rCancel (merid (pt A)))
                   (sym (cong-∙∙ (λ x → merid x ∙ sym (merid (pt A)))
                         (sym (lMapId (suc n) a))
                         (λ i → lMap (suc n) (p i) .fst a)
                         (lMapId (suc n) a)))

suspMap→TranspType : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
  → (typ (Ω ((Ω^ n) A)) → typ (Ω (Ω ((Ω^ n) (Susp∙ (typ A))))))
    ≡ ((S₊∙ (suc n) →∙ A) → (S₊∙ (suc (suc n)) →∙ Susp∙ (typ A)))
suspMap→TranspType {A = A} n i = 
  Ω≡SphereMap {A = A} (suc n) i → Ω≡SphereMap' {A = A} (suc n) i

suspMap→ : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
         → PathP (λ i → suspMap→TranspType {A = A} n i)
                 (suspMapΩ∙ (suc n) .fst)
                 (suspMap n)
suspMap→ {A = A} n =
  toPathP (funExt λ f →
      (λ j → transportRefl (botᵣ {A = A} (suc n)
                               (rMap (suc n) {A = A}
                                 (suspMapΩ∙ (suc n) .fst
                                   ((invEq (_ , isEquiv-lMap n) (transportRefl f j)))))) j)
    ∙∙ cong (botᵣ {A = A} (suc n))
            (funExt⁻ (filler-top□ (suc n)) (invEq (_ , isEquiv-lMap n) f))
    ∙∙ sym (filler▿ (suc n) (lMap (suc n) {A = A} (invEq (lMap (suc n) , isEquiv-lMap n) f)))
     ∙ cong (suspMap n) (secEq ((lMap (suc n) , isEquiv-lMap n)) f))

{-
We would like for the above dependent path to preserve composition
(in order to deduce properties of suspMap from the corresponding
ones of suspMapΩ). For this, we need that both Ω≡SphereMap and
Ω≡SphereMap' are structure preserving
-}

-- We define an alternative notion of composition (to ∙Π) on
-- Sⁿ →∙ Ω (Susp∙ (typ A)). It will be easier to work with
private
  invComp : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
          → S₊∙ n →∙ Ω (Susp∙ (typ A))
          → S₊∙ n →∙ Ω (Susp∙ (typ A))
          → S₊∙ n →∙ Ω (Susp∙ (typ A))
  fst (invComp n f g) x = (fst f x) ∙ (fst g x)
  snd (invComp n f g) = cong₂ _∙_ (snd f) (snd g) ∙ sym (rUnit refl)

  -- We prove that it agrees with ∙Π
  ∙Π≡invComp : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
          → (f g : S₊∙ (suc n) →∙ Ω (Susp∙ (typ A)))
          → ∙Π f g ≡ invComp {A = A} (suc n) f g
  ∙Π≡invComp zero f g =
    →∙Homogeneous≡ (isHomogeneousPath _ _)
      (funExt (λ { base → rUnit refl
                         ∙ sym (cong (_∙ fst g (snd (S₊∙ 1))) (snd f)
                              ∙ cong (refl ∙_) (snd g))
                 ; (loop i) j →
        hcomp (λ k →
          λ { (i = i0) → (rUnit refl
                          ∙ sym (cong (_∙ fst g (snd (S₊∙ 1))) (snd f)
                          ∙ cong (refl ∙_) (snd g))) j
            ; (i = i1) → (rUnit refl
                           ∙ sym (cong (_∙ fst g (snd (S₊∙ 1))) (snd f)
                           ∙ cong (refl ∙_) (snd g))) j
            ; (j = i0) → ((sym (snd f) ∙∙ cong (fst f) loop ∙∙ snd f)
                         ∙ (sym (snd g) ∙∙ cong (fst g) loop ∙∙ snd g)) i
            ; (j = i1) → cong₂Funct _∙_
                           (cong (fst f) loop) (cong (fst g) loop) (~ k) i})
         (hcomp (λ k →
           λ { (i = i0) → (rUnit refl
                           ∙ sym (cong (_∙ snd g (~ k)) (λ j → snd f (j ∨ ~ k))
                           ∙ cong (refl ∙_) (λ j → snd g (j ∨ ~ k)))) j
             ; (i = i1) → (rUnit refl
                           ∙ sym (cong (_∙ snd g (~ k)) (λ j → snd f (j ∨ ~ k))
                           ∙ cong (refl ∙_) (λ j → snd g (j ∨ ~ k)))) j
             ; (j = i0) → ((sym (snd f) ∙∙ cong (fst f) loop ∙∙ snd f)
                           ∙ (sym (snd g) ∙∙ cong (fst g) loop ∙∙ snd g)) i
             ; (j = i1) → (cong (_∙ snd g (~ k))
                              (doubleCompPath-filler (sym (snd f))
                                  (cong (fst f) loop)
                                               (snd f) (~ k)) ∙
                            cong ((snd f (~ k)) ∙_)
                              (doubleCompPath-filler (sym (snd g))
                                (cong (fst g) loop) (snd g) (~ k))) i})
           (hcomp (λ k →
             λ { (i = i0) → (rUnit (rUnit refl)
                            ∙ cong (rUnit refl ∙_) (cong sym (rUnit refl))) k j
               ; (i = i1) → (rUnit (rUnit refl)
                            ∙ cong (rUnit refl ∙_) (cong sym (rUnit refl))) k j
               ; (j = i0) → ((sym (snd f) ∙∙ cong (fst f) loop ∙∙ snd f)
                            ∙ (sym (snd g) ∙∙ cong (fst g) loop ∙∙ snd g)) i
               ; (j = i1) → (cong (_∙ refl)
                               ((sym (snd f) ∙∙ cong (fst f) loop ∙∙ snd f))
                            ∙ cong (refl ∙_)
                               (sym (snd g) ∙∙ cong (fst g) loop ∙∙ snd g)) i})
                ((cong (λ x → rUnit x j)
                       (sym (snd f) ∙∙ cong (fst f) loop ∙∙ snd f)
                ∙ cong (λ x → lUnit x j)
                       (sym (snd g) ∙∙ cong (fst g) loop ∙∙ snd g)) i)))}))
  ∙Π≡invComp {A = A} (suc n) f g =
    →∙Homogeneous≡ (isHomogeneousPath _ _)
      (funExt λ { north → rUnit refl
                         ∙ sym (cong (fst f north ∙_) (snd g)
                         ∙ cong (_∙ refl) (snd f))
                ; south → rUnit refl
                         ∙ sym (cong₂ _∙_
                               (cong (fst f) (sym (merid (ptSn _))) ∙ snd f)
                               (cong (fst g) (sym (merid (ptSn _))) ∙ snd g))
                ; (merid a i) j → p a i j})
    where
    module _ (a : S₊ (suc n)) where
      f-n = fst f north
      g-n = fst g north
      cong-f = (cong (fst f) (merid a ∙ sym (merid (ptSn _))))
      cong-g = (cong (fst g) (merid a ∙ sym (merid (ptSn _))))
      c-f = sym (snd f) ∙∙ cong-f ∙∙ snd f
      c-g = sym (snd g) ∙∙ cong-g ∙∙ snd g

      p : I → I → fst (Ω (Susp∙ (typ A)))
      p i j =
        hcomp (λ k →
          λ { (i = i0) → (rUnit (λ _ → snd (Susp∙ (typ A)))
                         ∙ sym ((cong (fst f north ∙_) (snd g)
                               ∙ cong (_∙ refl) (snd f)))) j
             ; (i = i1) → (rUnit refl
                    ∙  sym (cong₂ _∙_
                          (compPath-filler'
                            (cong (fst f) (sym (merid (ptSn _)))) (snd f) k)
                          (compPath-filler'
                            (cong (fst g) (sym (merid (ptSn _)))) (snd g) k))) j
             ; (j = i0) → (c-f ∙ c-g) i
             ; (j = i1) → fst f (compPath-filler
                                  (merid a)
                                  (sym (merid (ptSn _))) (~ k) i)
                         ∙ fst g (compPath-filler
                                  (merid a)
                                  (sym (merid (ptSn _))) (~ k) i)})
         (hcomp (λ k →
           λ {(i = i0) → (rUnit (λ _ → snd (Susp∙ (typ A)))
                        ∙ sym ((cong (fst f north ∙_) (snd g)
                             ∙ cong (_∙ refl) (snd f)))) j
            ; (i = i1) → (rUnit refl ∙ sym (cong₂ _∙_ (snd f) (snd g))) j
            ; (j = i0) → (c-f ∙ c-g) i
            ; (j = i1) → cong₂Funct _∙_ cong-f cong-g (~ k) i})
           (hcomp (λ k →
           λ {(i = i0) → (rUnit refl
                        ∙ sym (compPath-filler'
                               ((cong (fst f north ∙_) (snd g)))
                                (cong (_∙ refl) (snd f)) k)) j
            ; (i = i1) → (rUnit refl
                        ∙  sym (cong₂ _∙_ (λ i → snd f (i ∨ ~ k)) (snd g))) j
            ; (j = i0) → (c-f ∙ c-g) i
            ; (j = i1) → (cong (λ x → x ∙ snd g (~ k))
                           (doubleCompPath-filler refl
                            cong-f (snd f) (~ k))
                         ∙ cong ((snd f (~ k)) ∙_)
                              (doubleCompPath-filler
                                (sym (snd g)) cong-g refl (~ k))) i})
            (hcomp (λ k →
             λ {(i = i0) → compPath-filler
                            (rUnit (λ _ → snd (Susp∙ (typ A))))
                            (sym ((cong (_∙ refl) (snd f)))) k j
            ; (i = i1) → compPath-filler
                              (rUnit refl)
                              (sym (cong (refl ∙_) (snd g))) k j
            ; (j = i0) → (c-f ∙ c-g) i
            ; (j = i1) → (cong (_∙ refl)
                            ((λ j → snd f (~ j ∧ ~ k)) ∙∙ cong-f ∙∙ snd f)
                      ∙ cong (refl ∙_)
                         (sym (snd g) ∙∙ cong-g ∙∙ (λ j → snd g (j ∧ ~ k)))) i})
             (((cong (λ x → rUnit x j) c-f) ∙ (cong (λ x → lUnit x j) c-g)) i))))

  hom-botᵣ⁻ : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
    → (f g : S₊∙ (suc n) →∙ Susp∙ (typ A))
    → botᵣ⁻ {A = A} n (∙Π f g)
     ≡ invComp {A = A} n (botᵣ⁻ {A = A} n f) (botᵣ⁻ {A = A} n g)

-- We ge that 
hom-botᵣ⁻ zero f g =
  ΣPathP ((funExt (λ { false → sym (rUnit _)
                     ; true → (rUnit _)}))
                     , ((λ i j → rUnit refl (i ∧ ~ j))
                      ▷ lUnit (sym (rUnit refl))))
hom-botᵣ⁻ (suc n) f g =
  →∙Homogeneous≡ (isHomogeneousPath _ _)
    (funExt (λ x → (sym (rUnit (cong (fst (∙Π f g)) (merid x ∙ sym (merid (ptSn _))))))
                      ∙∙ cong-∙ (fst (∙Π f g)) (merid x) (sym (merid (ptSn _)))
                      ∙∙ cong (cong (fst (∙Π f g)) (merid x) ∙_) (cong sym lem)
                       ∙ sym (rUnit (cong (fst (∙Π f g)) (merid x)))))
  where
  lem : cong (fst (∙Π f g)) (merid (ptSn (suc n))) ≡ refl
  lem = (λ i → (sym (snd f) ∙∙ cong (fst f) (rCancel (merid (ptSn _)) i) ∙∙ snd f)
              ∙ (sym (snd g) ∙∙ cong (fst g) (rCancel (merid (ptSn _)) i) ∙∙ snd g))
      ∙ (λ i → ∙∙lCancel (snd f) i ∙ ∙∙lCancel (snd g) i)
       ∙ sym (rUnit refl)

-- We get that botᵣ⁻ (and hence botᵣ) is homomorphism
hom-botᵣ⁻' : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
  → (f g : S₊∙ (suc (suc n)) →∙ Susp∙ (typ A))
  → botᵣ⁻ {A = A} (suc n) (∙Π f g)
   ≡ ∙Π (botᵣ⁻ {A = A} (suc n) f) (botᵣ⁻ {A = A} (suc n) g)
hom-botᵣ⁻' {A = A} n f g =
    hom-botᵣ⁻ {A = A} (suc n) f g
  ∙ sym (∙Π≡invComp {A = A} _ (botᵣ⁻ {A = A} _ f) (botᵣ⁻ {A = A} _ g))

isHom-lMap : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ} (p q : _)
  → lMap (suc n) {A = A} (p ∙ q)
  ≡ ∙Π (lMap (suc n) p) (lMap (suc n) q)
isHom-lMap zero p q =
  ΣPathP ((funExt (λ { base → refl
                    ; (loop i) j → (rUnit p j ∙ rUnit q j) i}))
                    , refl)
isHom-lMap (suc n) {A = A} p q =
  ΣPathP ((funExt (λ { north → refl
                     ; south → refl
                     ; (merid a i) j → h a j i}))
          , refl)
  where
  doubleComp-lem : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) (q r : y ≡ y)
                 → (p ∙∙ q ∙∙ sym p) ∙ (p ∙∙ r ∙∙ sym p)
                  ≡ (p ∙∙ (q ∙ r) ∙∙ sym p) 
  doubleComp-lem p q r i j =
    hcomp (λ k → λ { (i = i0) → (doubleCompPath-filler p q (sym p) k
                                ∙ doubleCompPath-filler p r (sym p) k) j
                    ; (i = i1) → doubleCompPath-filler p (q ∙ r) (sym p) k j
                    ; (j = i0) → p (~ k)
                    ; (j = i1) → p (~ k)})
          ((q ∙ r) j)

  help2 : (p : typ ((Ω^ (suc (suc n))) A))
        → cong (fst (lMap (suc (suc n)) p)) (merid (ptSn _)) ≡ refl
  help2 p =
    cong (sym (lMapId (suc n) (ptSn _)) ∙∙_∙∙ lMapId (suc n) (ptSn _))
              (rUnit _ ∙ (λ j → (λ i → lMap (suc n) {A = A} refl .snd (i ∧ j))
                       ∙∙ (λ i → lMap (suc n) {A = A} (p i) .snd j)
                       ∙∙ λ i → lMap (suc n) {A = A} refl .snd (~ i ∧ j))
                       ∙ ∙∙lCancel _)
              ∙ ∙∙lCancel _

  h : (a : S₊ (suc n))
    → sym (lMapId (suc n) a)
        ∙∙ funExt⁻ (cong fst (cong (lMap (suc n)) (p ∙ q))) a
        ∙∙ lMapId (suc n) a
     ≡ cong (fst (∙Π (lMap (suc (suc n)) p) (lMap (suc (suc n)) q))) (merid a)
  h a = (cong (sym (lMapId (suc n) a) ∙∙_∙∙ (lMapId (suc n) a))
              (cong-∙ (λ x → lMap (suc n) x .fst a) p q)
       ∙ sym (doubleComp-lem (sym (lMapId (suc n) a)) _ _))
     ∙∙ cong₂ _∙_ (sym (cong (cong (fst (lMap (suc (suc n)) p)) (merid a) ∙_)
                       (cong sym (help2 p)) ∙ sym (rUnit _)))
                  (sym (cong (cong (fst (lMap (suc (suc n)) q)) (merid a) ∙_)
                       (cong sym (help2 q)) ∙ sym (rUnit _)))
     ∙∙ λ i → (rUnit (cong-∙ (fst (lMap (suc (suc n)) p))
                              (merid a) (sym (merid (ptSn _))) (~ i)) i)
             ∙ (rUnit (cong-∙ (fst (lMap (suc (suc n)) q))
                              (merid a) (sym (merid (ptSn _)))(~ i)) i)

hom-rMap : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
  → (p q : typ ((Ω^ (suc (suc n))) (Susp∙ (typ A))))
  → rMap (suc n) {A = A} (p ∙ q)
   ≡ ∙Π (rMap (suc n) {A = A} p) (rMap (suc n) {A = A} q)
hom-rMap {A = A} n p q =
  cong (lMap (suc n) {A = Ω (Susp∙ (typ A))})
    (morphLemmas.isMorphInv _∙_ _∙_
      (Iso.inv (flipΩIso (suc n))) (flipΩIsopres· n)
      (Iso.fun (flipΩIso (suc n)))
      (Iso.leftInv (flipΩIso (suc n))) (Iso.rightInv (flipΩIso (suc n)))
      p q)
  ∙ isHom-lMap _ (fun (flipΩIso (suc n)) p) (fun (flipΩIso (suc n)) q)

isHom-IsoΩSphereMap' : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
     (p q : typ (Ω ((Ω^ n) (Susp∙ (typ A)))))
  → Iso.fun (IsoΩSphereMap' {A = A} n) (p ∙ q)
   ≡ ∙Π {n = (suc n)} (Iso.fun (IsoΩSphereMap' {A = A} n) p)
                      (Iso.fun (IsoΩSphereMap' {A = A} n) q)
isHom-IsoΩSphereMap' {A = A} zero p q =
  (cong (botᵣ {A = A} 0)
    (cong ((lMap 0 {A = Ω (Susp∙ (typ A))}))
      (transportRefl (p ∙ q))))
  ∙ ΣPathP (funExt (λ { base → refl
                      ; (loop i) j
                      → lem j i})
           , refl)
  where
  lem : p ∙ q ≡ (cong (fst (fun (IsoΩSphereMap' {A = A} zero) p)) loop ∙ refl)
              ∙ (cong (fst (fun (IsoΩSphereMap' {A = A} zero) q)) loop ∙ refl)
  lem = cong₂ _∙_
         (sym (transportRefl p)
         ∙ rUnit (cong (fst (fun (IsoΩSphereMap' {A = A} zero) p)) loop))
         (sym (transportRefl q)
         ∙ rUnit (cong (fst (fun (IsoΩSphereMap' {A = A} zero) q)) loop))
isHom-IsoΩSphereMap' {A = A} (suc n) p q =
     cong (botᵣ {A = A} (suc n) ∘ lMap (suc n) {A = Ω (Susp∙ (typ A))})
          (morphLemmas.isMorphInv
            _∙_ _∙_
            (Iso.inv (flipΩIso (suc n)))
            (flipΩIsopres· n)
            (Iso.fun (flipΩIso (suc n)))
            (Iso.leftInv (flipΩIso (suc n)))
            (Iso.rightInv (flipΩIso (suc n))) p q)
  ∙ (cong (botᵣ {A = A} (suc n))
          (isHom-lMap _ {A = Ω (Susp∙ (typ A))}
            (fun (flipΩIso (suc n)) p) (fun (flipΩIso (suc n)) q))
   ∙ morphLemmas.isMorphInv ∙Π ∙Π (botᵣ⁻ {A = A} (suc n))
        (hom-botᵣ⁻' {A = A} n)
        (botᵣ {A = A} (suc n))
        (Iso.leftInv (botᵣIso {A = A} (suc n)))
        (Iso.rightInv (botᵣIso {A = A} (suc n)))
        (lMap (suc n) (fun (flipΩIso (suc n)) p))
        (lMap (suc n) (fun (flipΩIso (suc n)) q)))


suspMapΩ→hom : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) (p q : typ ((Ω^ (suc n)) A))
  → suspMapΩ∙ (suc n) .fst (p ∙ q)
   ≡ suspMapΩ∙ (suc n) .fst p ∙ suspMapΩ∙ (suc n) .fst q
suspMapΩ→hom {A = A} n p q =
     cong (sym (snd (suspMapΩ∙ {A = A} n)) ∙∙_∙∙ snd (suspMapΩ∙ {A = A} n))
          (cong-∙ (fst (suspMapΩ∙ {A = A} n)) p q)
   ∙ help (snd (suspMapΩ∙ {A = A} n)) _ _
  where
  help : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) (q s : x ≡ x)
    → sym p ∙∙ (q ∙ s) ∙∙ p
    ≡ (sym p ∙∙ q ∙∙ p) ∙ (sym p ∙∙ s ∙∙ p)
  help {x = x} =
    J (λ y p → (q s : x ≡ x)
    → sym p ∙∙ (q ∙ s) ∙∙ p
    ≡ (sym p ∙∙ q ∙∙ p ) ∙ (sym p ∙∙ s ∙∙ p))
       λ q s → sym (rUnit (q ∙ s))
             ∙ cong₂ _∙_ (rUnit q) (rUnit s)

private
  transpLemTyp : ∀ {ℓ} → {A1 A2 B1 B2 : Type ℓ}
               (AB1 : A1 ≡ B1) (AB2 : A2 ≡ B2)
            → (f : A1 → A2) (g : B1 → B2)
            → PathP (λ i → AB1 i → AB2 i) f g
            → Type ℓ
  transpLemTyp {ℓ} {A1} {A2} {B1} {B2} AB1 AB2 f g p =
       (+A1 : A1 → A1 → A1)
     → (+A2 : A2 → A2 → A2)
     → (+B1 : B1 → B1 → B1)
     → (+B2 : B2 → B2 → B2)
     → ((x y : A1) → transport AB1 (+A1 x y)
                    ≡ +B1 (transport AB1 x) (transport AB1 y))
     → ((x y : A2) → transport AB2 (+A2 x y)
                    ≡ +B2 (transport AB2 x) (transport AB2 y))
     → ((x y : A1) → f (+A1 x y) ≡ +A2 (f x) (f y))
     → ((x y : B1) → g (+B1 x y) ≡ +B2 (g x) (g y))

  transpLem : ∀ {ℓ} → {A1 A2 B1 B2 : Type ℓ} (AB1 : A1 ≡ B1) (AB2 : A2 ≡ B2)
            → (f : A1 → A2) (g : B1 → B2)
            → (eq : PathP (λ i → AB1 i → AB2 i) f g)
            → transpLemTyp AB1 AB2 f g eq
  transpLem {ℓ} {A1} {A2} {B1} {B2} =
    J (λ B1 AB1 → (AB2 : A2 ≡ B2)
            → (f : A1 → A2) (g : B1 → B2)
            → (eq : PathP (λ i → AB1 i → AB2 i) f g)
            → transpLemTyp AB1 AB2 f g eq)
      (J (λ B2 AB2 → (f : A1 → A2) (g : A1 → B2)
         → (eq : PathP (λ i → A1 → AB2 i) f g)
         → transpLemTyp refl AB2 f g eq)
      λ f g → J (λ g p → transpLemTyp refl refl f g p)
        λ +A1 +A2 +B1 +B2 trId1 trId2 fhom1
        → λ x y → cong f (cong₂ +B1 (sym (transportRefl x)) (sym (transportRefl y))
                        ∙∙ sym (trId1 x y)
                        ∙∙ transportRefl (+A1 x y))
                        ∙∙ fhom1 x y
                        ∙∙ ((sym (transportRefl _) ∙ (trId2 (f x) (f y)))
                         ∙ cong₂ +B2 (transportRefl (f x)) (transportRefl (f y))))

open import Cubical.Foundations.Univalence
suspMap→hom : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) (f g : S₊∙ (suc n) →∙ A)
  → suspMap n (∙Π f g) ≡ ∙Π (suspMap n f) (suspMap n g)
suspMap→hom {A = A} n =
  transpLem (Ω≡SphereMap {A = A} (suc n)) (Ω≡SphereMap' {A = A} (suc n))
   (suspMapΩ {A = A} (suc n)) (suspMap {A = A} n)
   (suspMap→ {A = A} n)
   _∙_ _∙_ ∙Π ∙Π
   (λ x y → uaβ (isoToEquiv (IsoΩSphereMap {A = A} (suc n))) (x ∙ y)
          ∙∙ isHom-lMap n x y
          ∙∙ cong₂ ∙Π
              (sym (uaβ (isoToEquiv (IsoΩSphereMap {A = A} (suc n))) x))
              (sym (uaβ (isoToEquiv (IsoΩSphereMap {A = A} (suc n))) y)))
   (λ x y → uaβ (isoToEquiv (IsoΩSphereMap' {A = A} (suc n))) (x ∙ y)
         ∙∙ isHom-IsoΩSphereMap' {A = A} (suc n) x y
         ∙∙ cong₂ ∙Π
              (sym (uaβ (isoToEquiv (IsoΩSphereMap' {A = A} (suc n))) x))
              (sym (uaβ (isoToEquiv (IsoΩSphereMap' {A = A} (suc n))) y)))
   (suspMapΩ→hom {A = A} n)

private
  isConnectedPres : ∀ {ℓ} {A : Pointed ℓ} (con n : ℕ)
                  → isConnectedFun con (suspMapΩ∙ {A = A} (suc n) .fst)
                  → isConnectedFun con (suspMap {A = A} n)
  isConnectedPres {A = A} con n hyp =
    transport (λ i → isConnectedFun con (suspMap→ {A = A} n i)) hyp

isConnectedSuspMap : (n m : ℕ)
  → isConnectedFun ((m + suc m) ∸ n) (suspMap {A = S₊∙ (suc m)} n)
isConnectedSuspMap n m =
  isConnectedPres _ _ (suspMapΩ-connected m (suc n) (sphereConnected (suc m)))

suspMapπ' : (n m : ℕ)
  → π' (suc n) (S₊∙ (suc m))
  → π' (suc (suc n)) (S₊∙ (suc (suc m)))
suspMapπ' n m = sMap (suspMap {A = S₊∙ (suc m)} n)

suspMapHom : (n m : ℕ)
  → GroupHom (π'Gr n (S₊∙ (suc m)))
              (π'Gr (suc n) (S₊∙ (suc (suc m))))
fst (suspMapHom n m) = suspMapπ' n m
snd (suspMapHom n m) =
  makeIsGroupHom (sElim2 (λ _ _ → isSetPathImplicit)
    λ f g → cong ∣_∣₂ (suspMap→hom n f g))

isSurjectiveSuspMap : (n : ℕ) → isSurjective (suspMapHom (2 + n) (suc n))
isSurjectiveSuspMap n =
  sElim (λ _ → isProp→isSet squash)
        λ f → trRec (subst (λ x → isOfHLevel x (isInIm (suspMapHom (2 + n) (suc n)) ∣ f ∣₂))
                      (sym (snd (lem n n)))
                      (isProp→isOfHLevelSuc {A = isInIm (suspMapHom (2 + n) (suc n)) ∣ f ∣₂}
                      (fst (lem n n)) squash))
                     (λ p → ∣ ∣ fst p ∣₂ , (cong ∣_∣₂ (snd p)) ∣)
               (fst (isConnectedSuspMap (2 + n) (suc n) f))
  where
  lem : (m n : ℕ) → Σ[ x ∈ ℕ ] ((m + suc (suc n) ∸ suc n) ≡ suc x)
  lem zero zero = 0 , refl
  lem (suc m) zero = suc m , +-comm m 2
  lem zero (suc n) = lem zero n
  lem (suc m) (suc n) = fst (lem (suc m) n) , (cong (_∸ (suc n)) (+-comm m (3 + n))
                     ∙∙ cong (_∸ n) (+-comm (suc (suc n)) m)
                     ∙∙ snd (lem (suc m) n))
