{-# OPTIONS --safe --experimental-lossy-unification #-}
{-
This file contians:
1. A proof that the equivalence Ωⁿ A ≃ (Sⁿ →∙ A)
is structure preserving

2. Using the above, the complete group structure on (Sⁿ →∙ A),
the alternative definition of homotopy groups

4. A proof that the dependent path in Homotopy.Group.SuspensionMapPathP
is structure preserving.

5. A group isomorphism of the different definitions of homotopy groups

6. Connectivity of the suspension map

7. Surjectivity of the suspension map π₂₊ₙ(S¹⁺ⁿ) → π₃₊ₙ(S²⁺ⁿ)
-}
module Cubical.Homotopy.Group.Properties where

open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Group.SuspensionMapPathP
open import Cubical.Homotopy.Group.SuspensionMapPathP
  using (IsoΩSphereMap) public
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
open import Cubical.Foundations.Univalence

open import Cubical.Functions.Morphism

open import Cubical.HITs.PropositionalTruncation
  renaming (rec to pRec ; rec2 to pRec2 ; elim to pElim)
open import Cubical.HITs.SetTruncation
  renaming (rec to sRec ; rec2 to sRec2 ; elim to sElim
          ; elim2 to sElim2 ; elim3 to sElim3 ; map to sMap)
open import Cubical.HITs.Truncation
  renaming (rec to trRec)
open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.Data.Bool
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

-- We finally arrive at the main result

IsoSphereMapΩ : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
     → Iso (S₊∙ n →∙ A) (fst ((Ω^ n) A))
IsoSphereMapΩ n = invIso (IsoΩSphereMap n)

SphereMap→Ω : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
           → (S₊∙ n →∙ A) → (fst ((Ω^ n) A))
SphereMap→Ω n = fun (IsoSphereMapΩ n)

Ω→SphereMap : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
           → (fst ((Ω^ n) A)) → (S₊∙ n →∙ A)
Ω→SphereMap n = inv (IsoSphereMapΩ n)

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

-- The iso is structure preserving
IsoSphereMapΩ-pres∙Π : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) (f g : S₊∙ (suc n) →∙ A)
             → SphereMap→Ω (suc n) (∙Π f g)
             ≡ SphereMap→Ω (suc n) f ∙ SphereMap→Ω (suc n) g
IsoSphereMapΩ-pres∙Π n =
  morphLemmas.isMorphInv _∙_ ∙Π (Ω→SphereMap (suc n))
    (isHom-lMap n)
    (SphereMap→Ω (suc n))
    (rightInv (IsoΩSphereMap (suc n)))
    (leftInv (IsoΩSphereMap (suc n)))

-- It is useful to define the ``Group Structure'' on (S₊∙ n →∙ A)
-- before doing it on π'. These will be the equivalents of the
-- usual groupoid laws on Ω A.
1Π : ∀ {ℓ} {A : Pointed ℓ} {n : ℕ} → (S₊∙ n →∙ A)
fst (1Π {A = A}) _ = pt A
snd (1Π {A = A}) = refl

∙Π-rUnit : ∀ {ℓ} {A : Pointed ℓ} {n : ℕ}
        → (f : S₊∙ (suc n) →∙ A)
        → ∙Π f 1Π ≡ f
fst (∙Π-rUnit {A = A} {n = zero} f i) base = snd f (~ i)
fst (∙Π-rUnit {A = A} {n = zero} f i) (loop j) = help i j
  where
  help : PathP (λ i → snd f (~ i) ≡ snd f (~ i))
               (((sym (snd f)) ∙∙ (cong (fst f) loop) ∙∙ snd f)
                 ∙ (refl ∙ refl))
               (cong (fst f) loop)
  help = (cong ((sym (snd f) ∙∙ cong (fst f) loop ∙∙ snd f) ∙_)
               (sym (rUnit refl)) ∙ sym (rUnit _))
        ◁ λ i j → doubleCompPath-filler (sym (snd f))
                     (cong (fst f) loop) (snd f) (~ i) j
snd (∙Π-rUnit {A = A} {n = zero} f i) j = snd f (~ i ∨ j)
fst (∙Π-rUnit {A = A} {n = suc n} f i) north = snd f (~ i)
fst (∙Π-rUnit {A = A} {n = suc n} f i) south =
  (sym (snd f) ∙ cong (fst f) (merid (ptSn (suc n)))) i
fst (∙Π-rUnit {A = A} {n = suc n} f i) (merid a j) = help i j
  where
  help : PathP (λ i → snd f (~ i)
             ≡ (sym (snd f) ∙ cong (fst f) (merid (ptSn (suc n)))) i)
               (((sym (snd f))
                 ∙∙ (cong (fst f) (merid a ∙ sym (merid (ptSn (suc n)))))
                 ∙∙ snd f)
                 ∙ (refl ∙ refl))
               (cong (fst f) (merid a))
  help = (cong (((sym (snd f))
                ∙∙ (cong (fst f) (merid a ∙ sym (merid (ptSn (suc n)))))
                ∙∙ snd f) ∙_)
              (sym (rUnit refl))
       ∙ sym (rUnit _))
       ◁ λ i j → hcomp (λ k →
         λ { (j = i0) → snd f (~ i ∧ k)
            ; (j = i1) → compPath-filler' (sym (snd f))
                           (cong (fst f) (merid (ptSn (suc n)))) k i
            ; (i = i0) → doubleCompPath-filler (sym (snd f))
                            (cong (fst f)
                            (merid a ∙ sym (merid (ptSn (suc n)))))
                            (snd f) k j
            ; (i = i1) → fst f (merid a j)})
            (fst f (compPath-filler (merid a)
                      (sym (merid (ptSn _))) (~ i) j))
snd (∙Π-rUnit {A = A} {n = suc n} f i) j = snd f (~ i ∨ j)

∙Π-lUnit : ∀ {ℓ} {A : Pointed ℓ} {n : ℕ}
        → (f : S₊∙ (suc n) →∙ A)
        → ∙Π 1Π f ≡ f
fst (∙Π-lUnit {n = zero} f i) base = snd f (~ i)
fst (∙Π-lUnit {n = zero} f i) (loop j) = s i j
  where
  s : PathP (λ i → snd f (~ i) ≡ snd f (~ i))
            ((refl ∙ refl) ∙ (sym (snd f) ∙∙ cong (fst f) loop ∙∙ snd f))
            (cong (fst f) loop)
  s = (cong (_∙ (sym (snd f) ∙∙ cong (fst f) loop ∙∙ snd f))
            (sym (rUnit refl)) ∙ sym (lUnit _))
          ◁ λ i j → doubleCompPath-filler (sym (snd f))
                      (cong (fst f) loop) (snd f) (~ i) j
snd (∙Π-lUnit {n = zero} f i) j = snd f (~ i ∨ j)
fst (∙Π-lUnit {n = suc n} f i) north = snd f (~ i)
fst (∙Π-lUnit {n = suc n} f i) south =
  (sym (snd f) ∙ cong (fst f) (merid (ptSn _))) i
fst (∙Π-lUnit {n = suc n} f i) (merid a j) = help i j
  where
  help : PathP (λ i → snd f (~ i)
             ≡ (sym (snd f) ∙ cong (fst f) (merid (ptSn (suc n)))) i)
               ((refl ∙ refl) ∙ ((sym (snd f))
                      ∙∙ (cong (fst f) (merid a ∙ sym (merid (ptSn (suc n)))))
                      ∙∙ snd f))
               (cong (fst f) (merid a))
  help =
    (cong (_∙ ((sym (snd f))
            ∙∙ (cong (fst f) (merid a ∙ sym (merid (ptSn (suc n)))))
            ∙∙ snd f))
           (sym (rUnit refl))
    ∙ sym (lUnit _))
    ◁ λ i j → hcomp (λ k →
      λ { (j = i0) → snd f (~ i ∧ k)
        ; (j = i1) → compPath-filler' (sym (snd f))
                       (cong (fst f) (merid (ptSn (suc n)))) k i
        ; (i = i0) → doubleCompPath-filler (sym (snd f))
                        (cong (fst f) (merid a ∙ sym (merid (ptSn (suc n)))))
                        (snd f) k j
        ; (i = i1) → fst f (merid a j)})
        (fst f (compPath-filler (merid a) (sym (merid (ptSn _))) (~ i) j))
snd (∙Π-lUnit {n = suc n} f i) j = snd f (~ i ∨ j)

∙Π-rCancel : ∀ {ℓ} {A : Pointed ℓ} {n : ℕ}
        → (f : S₊∙ (suc n) →∙ A)
        → ∙Π f (-Π f) ≡ 1Π
fst (∙Π-rCancel {A = A} {n = zero} f i) base = pt A
fst (∙Π-rCancel {A = A} {n = zero} f i) (loop j) =
  rCancel (sym (snd f) ∙∙ cong (fst f) loop ∙∙ snd f) i j
snd (∙Π-rCancel {A = A} {n = zero} f i) = refl
fst (∙Π-rCancel {A = A} {n = suc n} f i) north = pt A
fst (∙Π-rCancel {A = A} {n = suc n} f i) south = pt A
fst (∙Π-rCancel {A = A} {n = suc n} f i) (merid a i₁) = sl i i₁
  where
  pl = (sym (snd f)
     ∙∙ cong (fst f) (merid a ∙ sym (merid (ptSn _)))
     ∙∙ snd f)
  sl : pl
     ∙ ((sym (snd f)
      ∙∙ cong (fst (-Π f)) (merid a ∙ sym (merid (ptSn _)))
      ∙∙ snd f)) ≡ refl
  sl = cong (pl ∙_) (cong (sym (snd f) ∙∙_∙∙ (snd f))
        (cong-∙ (fst (-Π f)) (merid a) (sym (merid (ptSn _)))
        ∙∙ cong₂ _∙_ refl
                   (cong (cong (fst f)) (rCancel (merid (ptSn _))))
        ∙∙ sym (rUnit _)))
     ∙ rCancel pl
snd (∙Π-rCancel {A = A} {n = suc n} f i) = refl

∙Π-lCancel : ∀ {ℓ} {A : Pointed ℓ} {n : ℕ}
        → (f : S₊∙ (suc n) →∙ A)
        → ∙Π (-Π f) f ≡ 1Π
fst (∙Π-lCancel {A = A} {n = zero} f i) base = pt A
fst (∙Π-lCancel {A = A} {n = zero} f i) (loop j) =
  rCancel (sym (snd f) ∙∙ cong (fst f) (sym loop) ∙∙ snd f) i j
fst (∙Π-lCancel {A = A} {n = suc n} f i) north = pt A
fst (∙Π-lCancel {A = A} {n = suc n} f i) south = pt A
fst (∙Π-lCancel {A = A} {n = suc n} f i) (merid a j) = sl i j
  where
  pl = (sym (snd f)
     ∙∙ cong (fst f) (merid a ∙ sym (merid (ptSn _)))
     ∙∙ snd f)

  sl : (sym (snd f)
     ∙∙ cong (fst (-Π f)) (merid a ∙ sym (merid (ptSn _)))
     ∙∙ snd f) ∙ pl
     ≡ refl
  sl = cong (_∙ pl) (cong (sym (snd f) ∙∙_∙∙ (snd f))
        (cong-∙ (fst (-Π f)) (merid a) (sym (merid (ptSn _)))
        ∙∙ cong₂ _∙_ refl (cong (cong (fst f)) (rCancel (merid (ptSn _))))
        ∙∙ sym (rUnit _)))
     ∙ lCancel pl
snd (∙Π-lCancel {A = A} {n = zero} f i) = refl
snd (∙Π-lCancel {A = A} {n = suc n} f i) = refl

∙Π-assoc : ∀ {ℓ} {A : Pointed ℓ} {n : ℕ}
        → (f g h : S₊∙ (suc n) →∙ A)
        → ∙Π f (∙Π g h) ≡ ∙Π (∙Π f g) h
∙Π-assoc {n = n} f g h =
     sym (leftInv (IsoSphereMapΩ (suc n)) (∙Π f (∙Π g h)))
  ∙∙ cong (Ω→SphereMap (suc n)) (IsoSphereMapΩ-pres∙Π n f (∙Π g h)
                ∙∙ cong (SphereMap→Ω (suc n) f ∙_) (IsoSphereMapΩ-pres∙Π n g h)
                ∙∙ ∙assoc (SphereMap→Ω (suc n) f) (SphereMap→Ω (suc n) g) (SphereMap→Ω (suc n) h)
                ∙∙ cong (_∙ SphereMap→Ω (suc n) h) (sym (IsoSphereMapΩ-pres∙Π n f g))
                ∙∙ sym (IsoSphereMapΩ-pres∙Π n (∙Π f g) h))
  ∙∙ leftInv (IsoSphereMapΩ (suc n)) (∙Π (∙Π f g) h)

∙Π-comm : ∀ {ℓ} {A : Pointed ℓ} {n : ℕ}
        → (f g : S₊∙ (suc (suc n)) →∙ A)
        → ∙Π f g ≡ ∙Π g f
∙Π-comm {A = A} {n = n} f g =
     sym (leftInv (IsoSphereMapΩ (suc (suc n))) (∙Π f g))
  ∙∙ cong (Ω→SphereMap (suc (suc n))) (IsoSphereMapΩ-pres∙Π (suc n) f g
  ∙∙ EH _ _ _
  ∙∙ sym (IsoSphereMapΩ-pres∙Π (suc n) g f))
  ∙∙ leftInv (IsoSphereMapΩ (suc (suc n))) (∙Π g f)

{- π'' as a group -}
1π' : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ} → π' n A
1π' n {A = A} = ∣ 1Π ∣₂

·π' : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ} → π' (suc n) A → π' (suc n) A → π' (suc n) A
·π' n = sRec2 squash₂ λ p q → ∣ ∙Π p q ∣₂

-π' : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ} → π' (suc n) A → π' (suc n) A
-π' n = sMap -Π

π'-rUnit : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ} (x : π' (suc n) A)
        → (·π' n x (1π' (suc n))) ≡ x
π'-rUnit n = sElim (λ _ → isSetPathImplicit) λ p i → ∣ ∙Π-rUnit p i ∣₂

π'-lUnit : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ} (x : π' (suc n) A)
        → (·π' n (1π' (suc n)) x) ≡ x
π'-lUnit n = sElim (λ _ → isSetPathImplicit) λ p i → ∣ ∙Π-lUnit p i ∣₂

π'-rCancel : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ} (x : π' (suc n) A)
        → (·π' n x (-π' n x)) ≡ 1π' (suc n)
π'-rCancel n = sElim (λ _ → isSetPathImplicit) λ p i → ∣ ∙Π-rCancel p i ∣₂

π'-lCancel : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ} (x : π' (suc n) A)
        → (·π' n (-π' n x) x) ≡ 1π' (suc n)
π'-lCancel n = sElim (λ _ → isSetPathImplicit) λ p i → ∣ ∙Π-lCancel p i ∣₂

π'-assoc : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ} (x y z : π' (suc n) A)
        → ·π' n x (·π' n y z) ≡ ·π' n (·π' n x y) z
π'-assoc n = sElim3 (λ _ _ _ → isSetPathImplicit) λ p q r i → ∣ ∙Π-assoc p q r i ∣₂

π'-comm : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ} (x y : π' (suc (suc n)) A)
        → ·π' (suc n) x y ≡ ·π' (suc n) y x
π'-comm n = sElim2 (λ _ _ → isSetPathImplicit) λ p q i → ∣ ∙Π-comm p q i ∣₂

-- We finally get the group definition
π'Gr : ∀ {ℓ} (n : ℕ) (A : Pointed ℓ) → Group ℓ
fst (π'Gr n A) = π' (suc n) A
1g (snd (π'Gr n A)) = 1π' (suc n)
GroupStr._·_ (snd (π'Gr n A)) = ·π' n
inv (snd (π'Gr n A)) = -π' n
is-set (isSemigroup (isMonoid (isGroup (snd (π'Gr n A))))) = squash₂
assoc (isSemigroup (isMonoid (isGroup (snd (π'Gr n A))))) = π'-assoc n
identity (isMonoid (isGroup (snd (π'Gr n A)))) x = (π'-rUnit n x) , (π'-lUnit n x)
inverse (isGroup (snd (π'Gr n A))) x = (π'-rCancel n x) , (π'-lCancel n x)

-- and finally, the Iso
π'Gr≅πGr : ∀ {ℓ} (n : ℕ) (A : Pointed ℓ) → GroupIso (π'Gr n A) (πGr n A)
fst (π'Gr≅πGr n A) = setTruncIso (IsoSphereMapΩ (suc n))
snd (π'Gr≅πGr n A) =
  makeIsGroupHom (sElim2 (λ _ _ → isSetPathImplicit)
    λ p q i → ∣ IsoSphereMapΩ-pres∙Π n p q i ∣₂)

{-
In file X we gave a filler of the following square
          suspMapΩ
Ωⁿ A -------------------> Ωⁿ⁺¹ (Susp A)
 |                           |
 |                           |
 | ≃ eq₁                     | ≃ eq₂
 |                           |
 v           suspMap         v
 (Sⁿ →∙ A) -------------- > (Sⁿ⁺¹ →∙ Susp A)

We would like this to preserve composition
(in order to deduce properties of suspMap from the corresponding
ones of suspMapΩ). For this, we need that both equivalences
on the sides are structure preserving
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


hom-rMap : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
  → (p q : typ ((Ω^ (suc (suc n))) (Susp∙ (typ A))))
  → rMap (suc n) {A = A} (p ∙ q)
   ≡ ∙Π (rMap (suc n) {A = A} p) (rMap (suc n) {A = A} q)
hom-rMap {A = A} n p q =
  cong (lMap (suc n) {A = Ω (Susp∙ (typ A))})
    (morphLemmas.isMorphInv _∙_ _∙_
      (inv (flipΩIso (suc n))) (flipΩIsopres· n)
      (fun (flipΩIso (suc n)))
      (leftInv (flipΩIso (suc n))) (rightInv (flipΩIso (suc n)))
      p q)
  ∙ isHom-lMap _ (fun (flipΩIso (suc n)) p) (fun (flipΩIso (suc n)) q)

isHom-IsoΩSphereMap' : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
     (p q : typ (Ω ((Ω^ n) (Susp∙ (typ A)))))
  → fun (IsoΩSphereMap' {A = A} n) (p ∙ q)
   ≡ ∙Π {n = (suc n)} (fun (IsoΩSphereMap' {A = A} n) p)
                      (fun (IsoΩSphereMap' {A = A} n) q)
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
            (inv (flipΩIso (suc n)))
            (flipΩIsopres· n)
            (fun (flipΩIso (suc n)))
            (leftInv (flipΩIso (suc n)))
            (rightInv (flipΩIso (suc n))) p q)
  ∙ (cong (botᵣ {A = A} (suc n))
          (isHom-lMap _ {A = Ω (Susp∙ (typ A))}
            (fun (flipΩIso (suc n)) p) (fun (flipΩIso (suc n)) q))
   ∙ morphLemmas.isMorphInv ∙Π ∙Π (botᵣ⁻ {A = A} (suc n))
        (hom-botᵣ⁻' {A = A} n)
        (botᵣ {A = A} (suc n))
        (leftInv (botᵣIso {A = A} (suc n)))
        (rightInv (botᵣIso {A = A} (suc n)))
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
