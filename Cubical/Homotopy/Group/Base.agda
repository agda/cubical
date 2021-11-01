{-# OPTIONS --safe --experimental-lossy-unification #-}
{-
This file contains
1. The definition of πₙ as a truncated loop space
2. The definition of πₙ as a truncated function space (Sⁿ →∙ A)
3. A structure preserving equivalence Ωⁿ A ≃ (Sⁿ →∙ A)
4. A proof that the two constructions of homotopy groups are isomorphic
-}
module Cubical.Homotopy.Group.Base where

open import Cubical.Homotopy.Loopspace

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws renaming (assoc to ∙assoc)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport

open import Cubical.HITs.SetTruncation
  renaming (rec to sRec ; rec2 to sRec2 ; elim to sElim
          ; elim2 to sElim2 ; elim3 to sElim3 ; map to sMap)
open import Cubical.HITs.Sn
open import Cubical.Data.Bool
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


{- Homotopy group -}
π : ∀ {ℓ} (n : ℕ) (A : Pointed ℓ) → Type ℓ
π n A = ∥ typ ((Ω^ n) A) ∥₂

{- Alternative formulation. This will be given a group structure in
  the Properties file -}
π' : ∀ {ℓ} (n : ℕ) (A : Pointed ℓ) → Type ℓ
π' n A = ∥ S₊∙ n →∙ A ∥₂

{- π as a group -}
1π : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ} → π n A
1π zero {A = A} = ∣ pt A ∣₂
1π (suc n) = ∣ refl ∣₂

·π : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ} → π (suc n) A → π (suc n) A → π (suc n) A
·π n = sRec2 squash₂ λ p q → ∣ p ∙ q ∣₂

-π : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ} → π (suc n) A → π (suc n) A
-π n = sMap sym

π-rUnit : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ} (x : π (suc n) A)
        → (·π n x (1π (suc n))) ≡ x
π-rUnit n = sElim (λ _ → isSetPathImplicit) λ p i → ∣ rUnit p (~ i) ∣₂

π-lUnit : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ} (x : π (suc n) A)
        → (·π n (1π (suc n)) x) ≡ x
π-lUnit n = sElim (λ _ → isSetPathImplicit) λ p i → ∣ lUnit p (~ i) ∣₂

π-rCancel : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ} (x : π (suc n) A)
        → (·π n x (-π n x)) ≡ 1π (suc n)
π-rCancel n = sElim (λ _ → isSetPathImplicit) λ p i → ∣ rCancel p i ∣₂

π-lCancel : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ} (x : π (suc n) A)
        → (·π n (-π n x) x) ≡ 1π (suc n)
π-lCancel n = sElim (λ _ → isSetPathImplicit) λ p i → ∣ lCancel p i ∣₂

π-assoc : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ} (x y z : π (suc n) A)
        → ·π n x (·π n y z) ≡ ·π n (·π n x y) z
π-assoc n = sElim3 (λ _ _ _ → isSetPathImplicit) λ p q r i → ∣ ∙assoc p q r i ∣₂

π-comm : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ} (x y : π (suc (suc n)) A)
        → ·π (suc n) x y ≡ ·π (suc n) y x
π-comm n = sElim2 (λ _ _ → isSetPathImplicit) λ p q i → ∣ EH n p q i ∣₂

πGr : ∀ {ℓ} (n : ℕ) (A : Pointed ℓ) → Group ℓ
fst (πGr n A) = π (suc n) A
1g (snd (πGr n A)) = 1π (suc n)
GroupStr._·_ (snd (πGr n A)) = ·π n
inv (snd (πGr n A)) = -π n
is-set (isSemigroup (isMonoid (isGroup (snd (πGr n A))))) = squash₂
assoc (isSemigroup (isMonoid (isGroup (snd (πGr n A))))) = π-assoc n
identity (isMonoid (isGroup (snd (πGr n A)))) x = (π-rUnit n x) , (π-lUnit n x)
inverse (isGroup (snd (πGr n A))) x = (π-rCancel n x) , (π-lCancel n x)

-- We now define the group structure on π'.
-- We first define the corresponding structure on the untruncated
-- (S₊∙ n →∙ A). We first give multiplication and inversion and use this
-- to give a structure preserving equivalence (S₊∙ n →∙ A) ≃ Ωⁿ A.


∙Π : ∀ {ℓ} {A : Pointed ℓ} {n : ℕ}
  → (S₊∙ n →∙ A)
  → (S₊∙ n →∙ A)
  → (S₊∙ n →∙ A)
∙Π {A = A} {n = zero} p q = (λ _ → pt A) , refl
fst (∙Π {A = A} {n = suc zero} (f , p) (g , q)) base = pt A
fst (∙Π {A = A} {n = suc zero} (f , p) (g , q)) (loop j) =
  ((sym p ∙∙ cong f loop ∙∙ p) ∙ (sym q ∙∙ cong g loop ∙∙ q)) j
snd (∙Π {A = A} {n = suc zero} (f , p) (g , q)) = refl
fst (∙Π {A = A} {n = suc (suc n)} (f , p) (g , q)) north = pt A
fst (∙Π {A = A} {n = suc (suc n)} (f , p) (g , q)) south = pt A
fst (∙Π {A = A} {n = suc (suc n)} (f , p) (g , q)) (merid a j) =
   ((sym p ∙∙ cong f (merid a ∙ sym (merid (ptSn (suc n)))) ∙∙ p)
  ∙ (sym q ∙∙ cong g (merid a ∙ sym (merid (ptSn (suc n)))) ∙∙ q)) j
snd (∙Π {A = A} {n = suc (suc n)} (f , p) (g , q)) = refl

-Π : ∀ {ℓ} {A : Pointed ℓ} {n : ℕ}
  → (S₊∙ n →∙ A)
  → (S₊∙ n →∙ A)
-Π {n = zero} f = f
fst (-Π {A = A} {n = suc zero} f) base = fst f base
fst (-Π {A = A} {n = suc zero} f) (loop j) = fst f (loop (~ j))
snd (-Π {A = A} {n = suc zero} f) = snd f
fst (-Π {A = A} {n = suc (suc n)} f) north = fst f north
fst (-Π {A = A} {n = suc (suc n)} f) south = fst f north
fst (-Π {A = A} {n = suc (suc n)} f) (merid a j) =
 fst f ((merid a ∙ sym (merid (ptSn _))) (~ j))
snd (-Π {A = A} {n = suc (suc n)} f) = snd f



-- module _ {ℓ : Level} {A : Pointed ℓ} where
--   suspension→ : (n : ℕ) → (S₊∙ (suc n) →∙ Ω A) → (S₊∙ (suc (suc n)) →∙ A)
--   fst (suspension→ n f) north = pt A
--   fst (suspension→ n f) south = pt A
--   fst (suspension→ n f) (merid a i₁) = fst f a i₁
--   snd (suspension→ n f) = refl

--   suspension-pres∙ :
--     (n : ℕ) (f g : (S₊∙ (suc n) →∙ Ω A))
--     → suspension→ n (∙Π f g) ≡ ∙Π (suspension→ n f) (suspension→ n g)
--   suspension-pres∙ n f g = ΣPathP ((funExt main) , refl)
--     where
--     J2 : ∀ {ℓ ℓ'} {A : Type ℓ} {x : A}
--       → (P : (p q : x ≡ x) → (refl ≡ p) → (refl ≡ q) → Type ℓ')
--       → P refl refl refl refl
--       → (p q : x ≡ x) (P' : _) (Q : _) → P p q P' Q
--     J2 P b p q =
--       J (λ p P' → (Q₁ : refl ≡ q) → P p q P' Q₁)
--         (J (λ q Q → P refl q refl Q) b)

--     J4 : ∀ {ℓ ℓ'} {A : Type ℓ} {x : A}
--       → (P : (p q r s : x ≡ x)
--            → (refl ≡ p) → (p ≡ q) → (refl ≡ r) → (r ≡ s) → Type ℓ')
--       → P refl refl refl refl refl refl refl refl
--       → (p q r s : x ≡ x) (P' : _) (Q : _) (R : _) (S : _) → P p q r s P' Q R S
--     J4 P b p q r s =
--       J (λ p P' → (Q₁ : p ≡ q) (R : refl ≡ r) (S₁ : r ≡ s)
--                  → P p q r s P' Q₁ R S₁)
--         (J (λ q Q₁ → (R : refl ≡ r) (S₁ : r ≡ s)
--                  → P refl q r s refl Q₁ R S₁)
--           (J (λ r R → (S₁ : r ≡ s)
--                  → P refl refl r s refl refl R S₁)
--             (J (λ s S₁ → P refl refl refl s refl refl refl S₁)
--               b)))

--     looper-help : (n : ℕ) (f g : (S₊∙ (suc n) →∙ Ω A)) (a : _)
--                 → fst (∙Π f g) a ≡ fst f a ∙ fst g a
--     looper-help zero f g base =
--       rUnit refl ∙ cong₂ _∙_ (sym (snd f)) (sym (snd g))
--     looper-help zero f g (loop i) k =
--       lazy-fill _ _
--         (sym (snd f)) (sym (snd g))
--         (cong (fst f) loop) (cong (fst g) loop) k i
--       where
--       lazy-fill :
--         ∀ {ℓ} {A : Type ℓ} {x : A} (p q : x ≡ x)
--             (prefl : refl ≡ p) (qrefl : refl ≡ q) (fl : p ≡ p) (fr : q ≡ q)
--           → PathP (λ i → (rUnit (refl {x = x}) ∙ cong₂ _∙_ prefl qrefl) i
--                        ≡ (rUnit (refl {x = x}) ∙ cong₂ _∙_ prefl qrefl) i)
--                    ((prefl ∙∙ fl ∙∙ sym prefl) ∙ (qrefl ∙∙ fr ∙∙ sym qrefl))
--                    (cong₂ _∙_ fl fr)
--       lazy-fill {x = x} =
--         J2 (λ p q prefl qrefl → (fl : p ≡ p) (fr : q ≡ q)
--              → PathP (λ i → (rUnit (refl {x = x}) ∙ cong₂ _∙_ prefl qrefl) i
--                             ≡ (rUnit (refl {x = x}) ∙ cong₂ _∙_ prefl qrefl) i)
--                       ((prefl ∙∙ fl ∙∙ sym prefl) ∙ (qrefl ∙∙ fr ∙∙ sym qrefl))
--                       (cong₂ _∙_ fl fr))
--             λ fl fr → cong₂ _∙_ (sym (rUnit fl)) (sym (rUnit fr))
--                         ◁ flipSquare (sym (rUnit (rUnit refl))
--                         ◁ (flipSquare ((λ j → cong (λ x → rUnit x j) fl
--                                              ∙ cong (λ x → lUnit x j) fr)
--                                      ▷ sym (cong₂Funct _∙_ fl fr))
--                         ▷ (rUnit (rUnit refl))))
--     looper-help (suc n) f g north =
--       rUnit refl ∙ cong₂ _∙_ (sym (snd f)) (sym (snd g))
--     looper-help (suc n) f g south =
--          (rUnit refl ∙ cong₂ _∙_ (sym (snd f)) (sym (snd g)))
--         ∙ cong₂ _∙_ (cong (fst f) (merid (ptSn _)))
--                     (cong (fst g) (merid (ptSn _)))
--     looper-help (suc n) f g (merid a j) i = help i j
--       where
--       help :
--         PathP (λ i → (rUnit refl ∙ cong₂ _∙_ (sym (snd f)) (sym (snd g))) i
--                    ≡ ((rUnit refl ∙ cong₂ _∙_ (sym (snd f)) (sym (snd g)))
--                      ∙ cong₂ _∙_ (cong (fst f) (merid (ptSn _)))
--                                  (cong (fst g) (merid (ptSn _)))) i)
--                      (cong (fst (∙Π f g)) (merid a))
--                      (cong₂ _∙_ (cong (fst f) (merid a))
--                                 (cong (fst g) (merid a)))
--       help = (cong₂ _∙_ (cong (sym (snd f) ∙∙_∙∙ snd f)
--                               (cong-∙ (fst f)
--                                       (merid a) (sym (merid (ptSn _)))))
--                         ((cong (sym (snd g) ∙∙_∙∙ snd g)
--                                (cong-∙ (fst g)
--                                       (merid a) (sym (merid (ptSn _))))))
--            ◁ lazy-help _ _ _ _ (sym (snd f)) (cong (fst f) (merid (ptSn _)))
--                        (sym (snd g)) (cong (fst g) (merid (ptSn _)))
--                        (cong (fst f) (merid a)) (cong (fst g) (merid a)))
--         where
--         lazy-help :
--           ∀ {ℓ} {A : Type ℓ} {x : A}
--                 (p-north p-south q-north q-south : x ≡ x)
--                 (prefl : refl ≡ p-north) (p-merid : p-north ≡ p-south)
--                 (qrefl : refl ≡ q-north) (q-merid : q-north ≡ q-south)
--                 (fl : p-north ≡ p-south) (fr : q-north ≡ q-south)
--          → PathP (λ i → (rUnit refl ∙ cong₂ _∙_ prefl qrefl) i
--                        ≡ ((rUnit refl ∙ cong₂ _∙_ prefl qrefl)
--                           ∙ cong₂ _∙_ p-merid q-merid) i)
--                   ((prefl ∙∙ fl ∙ sym p-merid ∙∙ sym prefl)
--                   ∙ (qrefl ∙∙ fr ∙ sym q-merid ∙∙ sym qrefl))
--                   (cong₂ _∙_ fl fr)
--         lazy-help {x = x} =
--           J4 (λ p-north p-south q-north q-south prefl p-merid qrefl q-merid
--              → (fl : p-north ≡ p-south) (fr : q-north ≡ q-south) →
--             PathP (λ i₁ → (rUnit refl ∙ cong₂ _∙_ prefl qrefl) i₁ ≡
--                           ((rUnit refl ∙ cong₂ _∙_ prefl qrefl)
--                           ∙ cong₂ _∙_ p-merid q-merid) i₁)
--             ((prefl ∙∙ fl ∙ sym p-merid ∙∙ sym prefl) ∙
--              (qrefl ∙∙ fr ∙ sym q-merid ∙∙ sym qrefl))
--             (cong₂ _∙_ fl fr))
--             λ fl fr → (cong₂ _∙_ (sym (rUnit (fl ∙ refl)) ∙ sym (rUnit fl))
--                                   (sym (rUnit (fr ∙ refl)) ∙ sym (rUnit fr))
--                                   ◁ flipSquare ((sym (rUnit _)
--                                   ◁ flipSquare
--                                     ((λ j → cong (λ x → rUnit x j) fl
--                                            ∙ cong (λ x → lUnit x j) fr)
--                                   ▷ sym (cong₂Funct _∙_ fl fr)))
--                                   ▷ (rUnit _ ∙ rUnit _)))
--     main : (x : fst (S₊∙ (suc (suc n)))) →
--       fst (suspension→ n (∙Π f g)) x ≡
--       fst (∙Π (suspension→ n f) (suspension→ n g)) x
--     main north = refl
--     main south = refl
--     main (merid a i₁) j = help j i₁
--       where
--       help : fst (∙Π f g) a
--            ≡ cong (fst (∙Π (suspension→ n f) (suspension→ n g))) (merid a)
--       help = looper-help n f g a
--         ∙ cong₂ _∙_ (sym (cong-∙ (fst (suspension→ n f))
--                                  (merid a)
--                                  (sym (merid (ptSn _)))
--                        ∙∙ cong (fst f a ∙_) (cong sym (snd f))
--                        ∙∙ sym (rUnit _)))
--                     (sym (cong-∙ (fst (suspension→ n g))
--                                  (merid a)
--                                  (sym (merid (ptSn _)))
--                        ∙∙ cong (fst g a ∙_) (cong sym (snd g))
--                        ∙∙ sym (rUnit _)))
--         ∙ λ i → rUnit (cong (fst (suspension→ n f))
--                        (merid a ∙ sym (merid (ptSn _)))) i
--                ∙ rUnit (cong (fst (suspension→ n g))
--                        (merid a ∙ sym (merid (ptSn _)))) i

--   suspension←filler : (n : ℕ) → (S₊∙ (suc (suc n)) →∙ A)
--                     → I → I → I → fst A
--   suspension←filler n f i j k =
--     hfill (λ k → λ { (i = i0) → doubleCompPath-filler
--                                    (sym (snd f))
--                                    (cong (fst f) (merid (ptSn _)
--                                     ∙ sym (merid (ptSn _))))
--                                    (snd f) k j
--                    ; (i = i1) → snd f k
--                    ; (j = i0) → snd f k
--                    ; (j = i1) → snd f k})
--           (inS ((fst f) (rCancel' (merid (ptSn _)) i j)))
--           k

--   suspension← : (n : ℕ) → (S₊∙ (suc (suc n)) →∙ A) → (S₊∙ (suc n) →∙ Ω A)
--   fst (suspension← n f) a =
--     sym (snd f) ∙∙ cong (fst f) (merid a ∙ sym (merid (ptSn _))) ∙∙ snd f
--   snd (suspension← n f) i j = suspension←filler n f i j i1

--   suspensionIso : (n : ℕ) → Iso (S₊∙ (suc n) →∙ Ω A) (S₊∙ (suc (suc n)) →∙ A)
--   Iso.fun (suspensionIso n) f = suspension→ n f
--   Iso.inv (suspensionIso n) f = suspension← n f
--   Iso.rightInv (suspensionIso n) (f , p) =
--     ΣPathP (funExt help , λ i j → p (~ i ∨ j))
--     where
--     help : (x : _) → fst (suspension→ n (suspension← n (f , p))) x ≡ f x
--     help north = sym p
--     help south = sym p ∙ cong f (merid (ptSn _))
--     help (merid a j) i =
--       hcomp (λ k → λ { (i = i1) → f (merid a j)
--                       ; (j = i0) → p (~ i ∧ k)
--                       ; (j = i1) → compPath-filler' (sym p)
--                                      (cong f (merid (ptSn _))) k i})
--             (f (compPath-filler (merid a) (sym (merid (ptSn _))) (~ i) j))
--   Iso.leftInv (suspensionIso n) f =
--     ΣPathP (funExt lem , PathP-filler)
--     where

--     side₁ : (x : S₊ (suc n)) → I → I → I → fst A
--     side₁ x i j k =
--       hfill (λ k → λ { (i = i0) → suspension→ n f .fst
--                                      (compPath-filler' (merid x)
--                                        (sym (merid (ptSn _))) k j)
--                       ; (i = i1) → snd A
--                       ; (j = i0) → fst f x (i ∨ ~ k)
--                       ; (j = i1) → snd A})
--                    (inS (snd f i (~ j)))
--                    k

--     side₂ : (x : S₊ (suc n)) → I → I → I → fst A
--     side₂ x i j k =
--       hfill (λ k → λ { (i = i0) → doubleCompPath-filler
--                                       refl
--                                       (cong (suspension→ n f .fst)
--                                             (merid x ∙ sym (merid (ptSn _))))
--                                       refl k j
--                       ; (i = i1) → fst f x (j ∨ ~ k)
--                       ; (j = i0) → fst f x (i ∧ ~ k)
--                       ; (j = i1) → snd A})
--             (inS (side₁ x i j i1))
--             k

--     compPath-filler'' : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z)
--                      → I → I → I → A
--     compPath-filler'' {z = z} p q k j i =
--       hfill (λ k → λ { (i = i0) → p (~ j)
--                      ; (i = i1) → q k
--                      ; (j = i0) → q (i ∧ k) })
--             (inS (p (i ∨ ~ j)))
--             k

--     lem : (x : _) → fst (suspension← n (suspension→ n f)) x ≡ fst f x
--     lem x i j = side₂ x i j i1

--     sideCube : Cube (λ j k → snd f j (~ k))
--                                (λ j k → fst (suspension→ n f)
--                                           (rCancel' (merid (ptSn _)) j k))
--                     (λ r k → suspension→ n f .fst
--                                (compPath-filler' (merid (ptSn _))
--                                  (sym (merid (ptSn _))) r k))
--                     (λ _ _ → pt A)
--                     (λ r j → snd f j (~ r)) λ _ _ → pt A
--     sideCube r j k =
--       hcomp (λ i → λ {(r = i0) → snd f j (~ k ∨ ~ i)
--                      ; (r = i1) → fst (suspension→ n f)
--                                     (rCancel-filler' (merid (ptSn _)) (~ i) j k)
--                      ; (j = i0) → suspension→ n f .fst
--                                      (compPath-filler'' (merid (ptSn _))
--                                        (sym (merid (ptSn _))) i r k)
--                      ; (j = i1) → snd f (~ r) (~ i ∧ k)
--                      ; (k = i0) → snd f j (~ r)
--                      ; (k = i1) → snd f (~ r ∧ j) (~ i)})
--              (hcomp (λ i → λ {(r = i0) → pt A
--                      ; (r = i1) → snd f (~ i) k
--                      ; (j = i0) → snd f (~ i) (k ∨ ~ r)
--                      ; (j = i1) → snd f (~ r ∨ ~ i) k
--                      ; (k = i0) → snd f (j ∨ ~ i) (~ r)
--                      ; (k = i1) → pt A})
--                     (pt A))

--     PathP-filler : PathP _ _ _
--     PathP-filler i j k =
--       hcomp (λ r → λ {(i = i0) → suspension←filler n (suspension→ n f) j k r
--                      ; (i = i1) → snd f j (k ∨ ~ r)
--                      ; (j = i0) → side₂ (ptSn _) i k r
--                      ; (j = i1) → snd A
--                      ; (k = i0) → snd f j (i ∧ ~ r)
--                      ; (k = i1) → snd A})
--             (hcomp ((λ r → λ {(i = i0) → sideCube r j k
--                      ; (i = i1) → pt A
--                      ; (j = i0) → side₁ (ptSn _) i k r
--                      ; (j = i1) → pt A
--                      ; (k = i0) → snd f j (i ∨ ~ r)
--                      ; (k = i1) → pt A}))
--                    (snd f (i ∨ j) (~ k)))

--   suspension←-pres∙ : (n : ℕ) → (f g : S₊∙ (suc (suc n)) →∙ A)
--                          → suspension← n (∙Π f g)
--                          ≡ ∙Π (suspension← n f) (suspension← n g)
--   suspension←-pres∙ n f g =
--        sym (Iso.leftInv (suspensionIso n) (suspension← n (∙Π f g)))
--     ∙∙ cong (suspension← n)
--             (Iso.rightInv (suspensionIso n) (∙Π f g)
--             ∙∙ cong₂ ∙Π (sym (Iso.rightInv (suspensionIso n) f))
--                         (sym (Iso.rightInv (suspensionIso n) g))
--             ∙∙ sym (suspension-pres∙ _ (suspension← n f) (suspension← n g)))
--     ∙∙ (Iso.leftInv (suspensionIso n) (∙Π (suspension← n f) (suspension← n g)))

-- SphereMap→Ω : {ℓ : Level} {A : Pointed ℓ} (n : ℕ)
--   → (S₊∙ (suc n) →∙ A) → (fst ((Ω^ (suc n)) A))
-- SphereMap→Ω zero (f , p) = sym p ∙∙ cong f loop ∙∙ p
-- SphereMap→Ω {A = A} (suc n) (f , p) =
--   Iso.inv (flipΩIso _)
--     (SphereMap→Ω {A = Ω A} n (Iso.inv (suspensionIso _) (f , p)))

-- SphereMap→Ωpres∙ : {ℓ : Level} {A : Pointed ℓ} (n : ℕ)
--         → (p q : S₊∙ (suc n) →∙ A)
--         → SphereMap→Ω n (∙Π p q) ≡ SphereMap→Ω n p ∙ SphereMap→Ω n q
-- SphereMap→Ωpres∙ zero f g = sym (rUnit _)
-- SphereMap→Ωpres∙ (suc n) f g =
--   cong (Iso.inv (flipΩIso (suc n)))
--     (cong (SphereMap→Ω n) (suspension←-pres∙ n f g)
--   ∙ SphereMap→Ωpres∙ n (suspension← n f) (suspension← n g))
--   ∙ flipΩIsopres· n _ _

-- Ω→SphereMap : {ℓ : Level} {A : Pointed ℓ} (n : ℕ)
--   → (fst ((Ω^ (suc n)) A)) → (S₊∙ (suc n) →∙ A)
-- fst (Ω→SphereMap {A = A} zero f) base = pt A
-- fst (Ω→SphereMap {A = A} zero f) (loop i₁) = f i₁
-- snd (Ω→SphereMap {A = A} zero f) = refl
-- Ω→SphereMap {A = A} (suc n) f =
--   Iso.fun (suspensionIso _) (Ω→SphereMap n (Iso.fun (flipΩIso _) f))

-- Ω→SphereMap→Ω : {ℓ : Level} {A : Pointed ℓ} (n : ℕ)
--          → (x : fst ((Ω^ (suc n)) A))
--          → SphereMap→Ω n (Ω→SphereMap n x) ≡ x
-- Ω→SphereMap→Ω zero x = sym (rUnit _)
-- Ω→SphereMap→Ω (suc n) x =
--      cong (Iso.inv (flipΩIso (suc n)) ∘ SphereMap→Ω n)
--           (Iso.leftInv (suspensionIso _)
--           (Ω→SphereMap n (Iso.fun (flipΩIso (suc n)) x)))
--   ∙∙ cong (Iso.inv (flipΩIso (suc n)))
--           (Ω→SphereMap→Ω n (Iso.fun (flipΩIso (suc n)) x))
--   ∙∙ Iso.leftInv (flipΩIso (suc n)) x

-- SphereMap→Ω→SphereMap : {ℓ : Level} {A : Pointed ℓ} (n : ℕ)
--          → (x : (S₊∙ (suc n) →∙ A))
--          → Ω→SphereMap n (SphereMap→Ω n x) ≡ x
-- SphereMap→Ω→SphereMap zero (f , p) =
--   ΣPathP (funExt fstp , λ i j → p (~ i ∨ j))
--   where
--   fstp : (x : _) → _ ≡ f x
--   fstp base = sym p
--   fstp (loop i) j = doubleCompPath-filler (sym p) (cong f loop) p (~ j) i
-- SphereMap→Ω→SphereMap (suc n) f =
--      cong (Iso.fun (suspensionIso n) ∘ Ω→SphereMap n)
--                    (Iso.rightInv (flipΩIso (suc n))
--           (SphereMap→Ω n (Iso.inv (suspensionIso n) f)))
--   ∙∙ cong (Iso.fun (suspensionIso n))
--           (SphereMap→Ω→SphereMap n (Iso.inv (suspensionIso n) f))
--   ∙∙ Iso.rightInv (suspensionIso _) _
