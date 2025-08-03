{-# OPTIONS --lossy-unification #-}
module Cubical.Homotopy.Group.Base where

open import Cubical.Homotopy.Loopspace

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws renaming (assoc to ∙assoc)
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Structure

open import Cubical.Functions.Morphism

open import Cubical.HITs.SetTruncation
  renaming (rec to sRec ; rec2 to sRec2
          ; elim to sElim ; elim2 to sElim2 ; elim3 to sElim3
          ; map to sMap)
open import Cubical.HITs.Truncation
  renaming (rec to trRec ; elim to trElim ; elim2 to trElim2)
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp renaming (toSusp to σ)
open import Cubical.HITs.S1 renaming (_·_ to _*_)
open import Cubical.HITs.S3

open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Unit

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.GroupPath
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

-- πₙ₊₁
πGr : ∀ {ℓ} (n : ℕ) (A : Pointed ℓ) → Group ℓ
fst (πGr n A) = π (suc n) A
1g (snd (πGr n A)) = 1π (suc n)
GroupStr._·_ (snd (πGr n A)) = ·π n
inv (snd (πGr n A)) = -π n
is-set (isSemigroup (isMonoid (isGroup (snd (πGr n A))))) = squash₂
·Assoc (isSemigroup (isMonoid (isGroup (snd (πGr n A))))) = π-assoc n
·IdR (isMonoid (isGroup (snd (πGr n A)))) x = π-rUnit n x
·IdL (isMonoid (isGroup (snd (πGr n A)))) x = π-lUnit n x
·InvR (isGroup (snd (πGr n A))) x = π-rCancel n x
·InvL (isGroup (snd (πGr n A))) x = π-lCancel n x

-- Group operations on π'.
-- We define the corresponding structure on the untruncated
-- (S₊∙ n →∙ A).

∙Π : ∀ {ℓ} {A : Pointed ℓ} {n : ℕ}
  → (S₊∙ n →∙ A)
  → (S₊∙ n →∙ A)
  → (S₊∙ n →∙ A)
∙Π {A = A} {n = zero} p q = (λ _ → pt A) , refl
fst (∙Π {A = A} {n = suc zero} (f , p) (g , q)) base = pt A
fst (∙Π {A = A} {n = suc zero} (f , p) (g , q)) (loop j) =
  ((sym p ∙∙ cong f loop ∙∙ p) ∙ (sym q ∙∙ cong g loop ∙∙ q)) j
snd (∙Π {A = A} {n = suc zero} (f , p) (g , q)) = refl
∙Π {A = A} {n = suc (suc n)} = ·Susp (S₊∙ (suc n))

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


-- to prove that this gives a group structure on π', we first
-- prove that Ωⁿ A ≃ (Sⁿ →∙ A).
-- We use the following map
mutual
  Ω→SphereMap : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ}
   → typ ((Ω^ n) A) → (S₊∙ n →∙ A)
  fst (Ω→SphereMap zero a) false = a
  fst (Ω→SphereMap zero {A = A} a) true = pt A
  snd (Ω→SphereMap zero a) = refl
  fst (Ω→SphereMap (suc zero) {A = A} p) base = pt A
  fst (Ω→SphereMap (suc zero) p) (loop i) = p i
  snd (Ω→SphereMap (suc zero) p) = refl
  fst (Ω→SphereMap (suc (suc n)) {A = A} p) north = pt A
  fst (Ω→SphereMap (suc (suc n)) {A = A} p) south = pt A
  fst (Ω→SphereMap (suc (suc n)) p) (merid a i) =
    (sym (Ω→SphereMapId (suc n) a)
    ∙∙ (λ i → Ω→SphereMap (suc n) (p i) .fst a)
    ∙∙ Ω→SphereMapId (suc n) a) i
  snd (Ω→SphereMap (suc (suc n)) p) = refl

  Ω→SphereMapId : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ} (a : _)
    → Ω→SphereMap n {A = A} (pt ((Ω^ n) A)) .fst a ≡ pt A
  Ω→SphereMapId zero false = refl
  Ω→SphereMapId zero true = refl
  Ω→SphereMapId (suc zero) base = refl
  Ω→SphereMapId (suc zero) (loop i) = refl
  Ω→SphereMapId (suc (suc n)) north = refl
  Ω→SphereMapId (suc (suc n)) south = refl
  Ω→SphereMapId (suc (suc n)) {A = A} (merid a i) j =
    ∙∙lCancel (Ω→SphereMapId (suc n) {A = A} a) j i

Ω→SphereMapId2 : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ}
  → Ω→SphereMap n {A = A} (pt ((Ω^ n) A)) ≡ ((λ _ → pt A) , refl)
fst (Ω→SphereMapId2 n {A = A} i) a = funExt (Ω→SphereMapId n {A = A}) i a
snd (Ω→SphereMapId2 zero {A = A} i) = refl
snd (Ω→SphereMapId2 (suc zero) {A = A} i) = refl
snd (Ω→SphereMapId2 (suc (suc n)) {A = A} i) = refl

-- Pointed version
Ω→SphereMap∙ : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ}
  → ((Ω^ n) A) →∙ (S₊∙ n →∙ A ∙)
Ω→SphereMap∙ n .fst = Ω→SphereMap n
Ω→SphereMap∙ n .snd = Ω→SphereMapId2 n

-- We define the following maps which will be used to
-- show that Ω→SphereMap is an equivalence
Ω→SphereMapSplit₁ : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
           → typ ((Ω^ (suc n)) A)
           → typ (Ω (S₊∙ n →∙ A ∙))
Ω→SphereMapSplit₁ n = Ω→ (Ω→SphereMap∙ n) .fst

ΩSphereMap : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
  → typ (Ω (S₊∙ n →∙ A ∙))
  → (S₊∙ (suc n) →∙ A)
fst (ΩSphereMap {A = A} zero p) base = p i0 .fst false
fst (ΩSphereMap {A = A} zero p) (loop i) = p i .fst false
snd (ΩSphereMap {A = A} zero p) = refl
ΩSphereMap {A = A} (suc n) = fun IsoΩFunSuspFun

-- Functoriality
-- The homogeneity assumption is not necessary but simplifying
isNaturalΩSphereMap : ∀ {ℓ ℓ'} (A : Pointed ℓ) (B : Pointed ℓ')
  (homogB : isHomogeneous B) (f : A →∙ B) (n : ℕ)
  → ∀ g → f ∘∙ ΩSphereMap n g ≡ ΩSphereMap n (Ω→ (post∘∙ (S₊∙ n) f) .fst g)
isNaturalΩSphereMap A B homogB f 0 g =
  →∙Homogeneous≡ homogB (funExt lem)
  where
  lem : ∀ x → f .fst (ΩSphereMap 0 g .fst x)
            ≡ ΩSphereMap 0 (Ω→ (post∘∙ (S₊∙ 0) f) .fst g) .fst x
  lem base = f .snd
  lem (loop i) j =
    hfill
      (λ j → λ
        { (i = i0) → post∘∙ _ f .snd j
        ; (i = i1) → post∘∙ _ f .snd j
        })
      (inS (f ∘∙ g i))
      j .fst false
isNaturalΩSphereMap A B homogB f (n@(suc _)) g =
  →∙Homogeneous≡ homogB (funExt lem)
  where
  lem : ∀ x → f .fst (ΩSphereMap n g .fst x)
            ≡ ΩSphereMap n (Ω→ (post∘∙ (S₊∙ n) f) .fst g) .fst x
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

SphereMapΩ : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
  → (S₊∙ (suc n) →∙ A)
  → typ (Ω (S₊∙ n →∙ A ∙))
SphereMapΩ {A = A} zero (f , p) =
  ΣPathP ((funExt λ { false → sym p ∙∙ cong f loop ∙∙ p
                    ; true → refl})
          , refl)
SphereMapΩ {A = A} (suc n) = inv IsoΩFunSuspFun

SphereMapΩIso : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
  → Iso (S₊∙ (suc n) →∙ A)
         (typ (Ω (S₊∙ n →∙ A ∙)))
fun (SphereMapΩIso n) = SphereMapΩ n
inv (SphereMapΩIso n) = ΩSphereMap n
fst (rightInv (SphereMapΩIso zero) f i j) false = rUnit (λ j → fst (f j) false) (~ i) j
fst (rightInv (SphereMapΩIso {A = A} zero) f i j) true = snd (f j) (~ i)
snd (rightInv (SphereMapΩIso {A = A} zero) f i j) k = snd (f j) (~ i ∨ k)
rightInv (SphereMapΩIso (suc n)) = leftInv IsoΩFunSuspFun
leftInv (SphereMapΩIso zero) f =
  ΣPathP ((funExt (λ { base → sym (snd f)
                    ; (loop i) j → doubleCompPath-filler
                                     (sym (snd f))
                                     (cong (fst f) loop)
                                     (snd f) (~ j) i}))
        , λ i j → snd f (~ i ∨ j))
leftInv (SphereMapΩIso (suc n)) = rightInv IsoΩFunSuspFun

{-
In order to show that Ω→SphereMap is an equivalence, we show that it factors

             Ω→SphereMapSplit₁               ΩSphereMap
Ωⁿ⁺¹A ----------------> Ω (Sⁿ →∙ A) -----------> (Sⁿ⁺¹ →∙ A)
-}

Ω→SphereMap-split : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) (p : typ ((Ω^ (suc n)) A))
    → Ω→SphereMap (suc n) p ≡ ΩSphereMap n (Ω→SphereMapSplit₁ n p)
Ω→SphereMap-split {A = A} zero p =
  ΣPathP ((funExt (λ { base → refl
                     ; (loop i) j → lem (~ j) i}))
         , refl)
  where
  lem : funExt⁻ (cong fst (Ω→SphereMapSplit₁ zero p)) false ≡ p
  lem = (λ i → funExt⁻ (cong-∙∙ fst (sym (Ω→SphereMapId2 zero))
                                     (cong (Ω→SphereMap zero) p)
                                     (Ω→SphereMapId2 zero) i) false)
    ∙ sym (rUnit _)
Ω→SphereMap-split {A = A} (suc n) p =
  ΣPathP ((funExt (λ { north → refl
                     ; south → refl
                     ; (merid a i) j → lem₂ a j i}))
          , refl)
  where
  lem : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) (a : S₊ (suc n))
    → Ω→SphereMapId (suc n) {A = A} a
    ≡ (λ i → fst (Ω→SphereMapId2 (suc n) {A = A} i) a)
  lem zero base = refl
  lem zero (loop i) = refl
  lem (suc n) north = refl
  lem (suc n) south = refl
  lem (suc n) (merid a i) = refl

  lem₂ : (a : S₊ (suc n))
     → ((λ i₁ → Ω→SphereMapId (suc n) {A = A} a (~ i₁))
     ∙∙ (λ i₁ → Ω→SphereMap (suc n) (p i₁) .fst a)
     ∙∙ Ω→SphereMapId (suc n) a)
     ≡ (λ i → Ω→SphereMapSplit₁ (suc n) p i .fst a)
  lem₂ a = cong (λ x → sym x
                 ∙∙ funExt⁻ (cong fst (λ i → Ω→SphereMap (suc n) (p i))) a
                 ∙∙ x)
             (lem n a)
     ∙∙ sym (cong-∙∙ (λ x → x a)
              (cong fst (λ i → Ω→SphereMapId2 (suc n) (~ i)))
              (cong fst (λ i → Ω→SphereMap (suc n) (p i)))
              (cong fst (Ω→SphereMapId2 (suc n))))
     ∙∙ (λ i → funExt⁻ (cong-∙∙ fst (sym (Ω→SphereMapId2 (suc n)))
                          (cong (Ω→SphereMap (suc n)) p)
                          (Ω→SphereMapId2 (suc n)) (~ i)) a)

isEquiv-Ω→SphereMap₀ : ∀ {ℓ} {A : Pointed ℓ}
  → isEquiv (Ω→SphereMap 0 {A = A})
isEquiv-Ω→SphereMap₀ {A = A} =
  isoToIsEquiv
    (iso _ (λ f → fst f false)
         (λ f → ΣPathP ((funExt (λ { false → refl ; true → sym (snd f)}))
                       , λ i j → snd f (~ i ∨ j)))
         λ p → refl)

isEquiv-Ω→SphereMap : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ}
  → isEquiv (Ω→SphereMap n {A = A})
isEquiv-Ω→SphereMap zero {A = A} =
  (isoToIsEquiv
    (iso _ (λ f → fst f false)
           (λ f → ΣPathP ((funExt (λ { false → refl
                                      ; true → sym (snd f)}))
                          , λ i j → snd f (~ i ∨ j)))
            λ _ → refl))
isEquiv-Ω→SphereMap (suc zero) {A = A} =
  isoToIsEquiv (iso _ invFun sec λ p → sym (rUnit p))
  where
  invFun : S₊∙ 1 →∙ A → typ (Ω A)
  invFun (f , p) = sym p ∙∙ cong f loop ∙∙ p

  sec : section (Ω→SphereMap 1) invFun
  sec (f , p) =
    ΣPathP ((funExt (λ { base → sym p
                       ; (loop i) j → doubleCompPath-filler
                                        (sym p) (cong f loop) p (~ j) i}))
           , λ i j → p (~ i ∨ j))

isEquiv-Ω→SphereMap (suc (suc n)) =
  subst isEquiv (sym (funExt (Ω→SphereMap-split (suc n))))
    (snd (compEquiv
         ((Ω→SphereMapSplit₁ (suc n)) ,
              (isEquivΩ→ (Ω→SphereMap (suc n) , Ω→SphereMapId2 (suc n))
                           (isEquiv-Ω→SphereMap (suc n))))
         (invEquiv (isoToEquiv (SphereMapΩIso (suc n))))))

IsoΩSphereMap : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
  → Iso (typ ((Ω^ n) A)) (S₊∙ n →∙ A)
IsoΩSphereMap n = equivToIso (_ , isEquiv-Ω→SphereMap n)

IsoSphereMapΩ : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
     → Iso (S₊∙ n →∙ A) (fst ((Ω^ n) A))
IsoSphereMapΩ {A = A} n =
  invIso (IsoΩSphereMap n)

SphereMap→Ω : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
      → S₊∙ n →∙ A → fst ((Ω^ n) A)
SphereMap→Ω n = fun (IsoSphereMapΩ n)

isHom-Ω→SphereMap : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ} (p q : _)
  → Ω→SphereMap (suc n) {A = A} (p ∙ q)
  ≡ ∙Π (Ω→SphereMap (suc n) {A = A} p)
       (Ω→SphereMap (suc n) {A = A} q)
isHom-Ω→SphereMap zero {A = A} p q =
  ΣPathP ((funExt (λ { base → refl
                    ; (loop i) j → (rUnit p j ∙ rUnit q j) i}))
        , refl)
isHom-Ω→SphereMap (suc n) {A = A} p q =
  ΣPathP ((funExt (λ { north → refl
                     ; south → refl
                     ; (merid a i) j → main a j i}))
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

  lem : (p : typ ((Ω^ (suc (suc n))) A))
      → cong (fst (Ω→SphereMap (suc (suc n)) p)) (merid (ptSn _)) ≡ refl
  lem p =
    cong (sym (Ω→SphereMapId (suc n) (ptSn _)) ∙∙_∙∙ Ω→SphereMapId (suc n) (ptSn _))
              (rUnit _ ∙ (λ j → (λ i → Ω→SphereMap (suc n) {A = A} refl .snd (i ∧ j))
                       ∙∙ (λ i → Ω→SphereMap (suc n) {A = A} (p i) .snd j)
                       ∙∙ λ i → Ω→SphereMap (suc n) {A = A} refl .snd (~ i ∧ j))
                       ∙ ∙∙lCancel _)
              ∙ ∙∙lCancel _

  main : (a : S₊ (suc n))
    → sym (Ω→SphereMapId (suc n) a)
        ∙∙ funExt⁻ (cong fst (cong (Ω→SphereMap (suc n)) (p ∙ q))) a
        ∙∙ Ω→SphereMapId (suc n) a
     ≡ cong (fst (∙Π (Ω→SphereMap (suc (suc n)) p) (Ω→SphereMap (suc (suc n)) q))) (merid a)
  main a = (cong (sym (Ω→SphereMapId (suc n) a) ∙∙_∙∙ (Ω→SphereMapId (suc n) a))
              (cong-∙ (λ x → Ω→SphereMap (suc n) x .fst a) p q)
       ∙ sym (doubleComp-lem (sym (Ω→SphereMapId (suc n) a)) _ _))
     ∙∙ cong₂ _∙_ (sym (cong (cong (fst (Ω→SphereMap (suc (suc n)) p)) (merid a) ∙_)
                       (cong sym (lem p)) ∙ sym (rUnit _)))
                  (sym (cong (cong (fst (Ω→SphereMap (suc (suc n)) q)) (merid a) ∙_)
                       (cong sym (lem q)) ∙ sym (rUnit _)))
     ∙∙ λ i → (rUnit (cong-∙ (fst (Ω→SphereMap (suc (suc n)) p))
                              (merid a) (sym (merid (ptSn _))) (~ i)) i)
             ∙ (rUnit (cong-∙ (fst (Ω→SphereMap (suc (suc n)) q))
                              (merid a) (sym (merid (ptSn _)))(~ i)) i)


-- The iso is structure preserving
IsoSphereMapΩ-pres∙Π : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) (f g : S₊∙ (suc n) →∙ A)
             → SphereMap→Ω (suc n) (∙Π f g)
              ≡ SphereMap→Ω (suc n) f ∙ SphereMap→Ω (suc n) g
IsoSphereMapΩ-pres∙Π n =
  morphLemmas.isMorphInv _∙_ ∙Π (Ω→SphereMap (suc n))
    (isHom-Ω→SphereMap n)
    (SphereMap→Ω (suc n))
    (leftInv (IsoSphereMapΩ (suc n)))
    (rightInv (IsoSphereMapΩ (suc n)))

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
fst (∙Π-rCancel {A = A} {n = suc n} f i) (merid a i₁) = lem i i₁
  where
  pl = (sym (snd f)
     ∙∙ cong (fst f) (merid a ∙ sym (merid (ptSn _)))
     ∙∙ snd f)

  lem : pl
     ∙ ((sym (snd f)
      ∙∙ cong (fst (-Π f)) (merid a ∙ sym (merid (ptSn _)))
      ∙∙ snd f)) ≡ refl
  lem = cong (pl ∙_) (cong (sym (snd f) ∙∙_∙∙ (snd f))
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
fst (∙Π-lCancel {A = A} {n = suc n} f i) (merid a j) = lem i j
  where
  pl = (sym (snd f)
     ∙∙ cong (fst f) (merid a ∙ sym (merid (ptSn _)))
     ∙∙ snd f)

  lem : (sym (snd f)
     ∙∙ cong (fst (-Π f)) (merid a ∙ sym (merid (ptSn _)))
     ∙∙ snd f) ∙ pl
     ≡ refl
  lem = cong (_∙ pl) (cong (sym (snd f) ∙∙_∙∙ (snd f))
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
isGroup (snd (π'Gr n A)) = makeIsGroup squash₂
                                       (π'-assoc n)
                                       (π'-rUnit n) (π'-lUnit n)
                                       (π'-rCancel n) (π'-lCancel n)

-- and finally, the Iso
π'Gr≅πGr : ∀ {ℓ} (n : ℕ) (A : Pointed ℓ) → GroupIso (π'Gr n A) (πGr n A)
fst (π'Gr≅πGr n A) = setTruncIso (IsoSphereMapΩ (suc n))
snd (π'Gr≅πGr n A) =
  makeIsGroupHom (sElim2 (λ _ _ → isSetPathImplicit)
    λ p q i → ∣ IsoSphereMapΩ-pres∙Π n p q i ∣₂)

-- Proof that π'Gr preserves universe lifts
π'GrLiftIso : ∀ {ℓ} (ℓ' : Level) {A : Pointed ℓ} (n : ℕ)
  → GroupIso (π'Gr n (Lift∙ {j = ℓ'} A)) (π'Gr n A)
fun (fst (π'GrLiftIso ℓ' n)) =
  sMap λ f → (λ x → lower (fst f x))
            , (cong lower (snd f))
inv (fst (π'GrLiftIso ℓ' n)) =
  sMap λ f → (λ x → lift (fst f x))
            , (cong lift (snd f))
rightInv (fst (π'GrLiftIso ℓ' n)) =
  sElim (λ _ → isSetPathImplicit) λ f → refl
leftInv (fst (π'GrLiftIso ℓ' n)) =
  sElim (λ _ → isSetPathImplicit) λ f → refl
snd (π'GrLiftIso ℓ' zero) =
  makeIsGroupHom (sElim2 (λ _ _ → isSetPathImplicit)
    λ f g → cong ∣_∣₂ (ΣPathP ((funExt
     λ { base → refl
       ; (loop i) j → (cong-∙ lower (Ω→ f .fst loop) (Ω→ g .fst loop)
        ∙ cong₂ _∙_
          (cong-∙∙ lower (sym (snd f)) (cong (fst f) loop) (snd f))
          (cong-∙∙ lower (sym (snd g)) (cong (fst g) loop) (snd g))) j i})
       , refl)))
snd (π'GrLiftIso ℓ' {A = A} (suc n)) =
  makeIsGroupHom (sElim2 (λ _ _ → isSetPathImplicit)
    λ f g → cong ∣_∣₂ (ΣPathP ((funExt (
      λ { north → refl
        ; south → refl
        ; (merid a i) j
       → (cong-∙ lower (Ω→ f .fst (σS a)) (Ω→ g .fst (σS a))
        ∙ cong₂ _∙_
          (cong-∙∙ lower (sym (snd f)) (cong (fst f) (σS a)) (snd f))
          (cong-∙∙ lower (sym (snd g)) (cong (fst g) (σS a)) (snd g))) j i}))
      , refl)))

{- Proof of πₙ(ΩA) = πₙ₊₁(A) -}
Iso-πΩ-π : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
        → Iso (π n (Ω A)) (π (suc n) A)
Iso-πΩ-π {A = A} n = setTruncIso (invIso (flipΩIso n))

GrIso-πΩ-π : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
          → GroupIso (πGr n (Ω A)) (πGr (suc n) A)
fst (GrIso-πΩ-π n) = Iso-πΩ-π _
snd (GrIso-πΩ-π n) =
  makeIsGroupHom
    (sElim2 (λ _ _ → isSetPathImplicit)
     λ p q → cong ∣_∣₂ (flipΩIso⁻pres· n p q))


{- Proof that πₙ(A) ≅ πₙ(∥ A ∥ₙ) -}
isContrΩTrunc : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
  → isContr (typ ((Ω^ n) (hLevelTrunc∙ n A)))
isContrΩTrunc {A = A} zero = isContrUnit*
isContrΩTrunc {A = A} (suc n) =
  subst isContr main (isContrΩTrunc {A = Ω A} n)
  where
  lem₁ : (n : ℕ) → fun (PathIdTruncIso n) (λ _ → ∣ pt A ∣)
                ≡ snd (hLevelTrunc∙ n (Ω A))
  lem₁ zero = refl
  lem₁ (suc n) = transportRefl ∣ refl ∣

  lem₂ : hLevelTrunc∙ n (Ω A) ≡ (Ω (hLevelTrunc∙ (suc n) A))
  lem₂ = sym (ua∙ (isoToEquiv (PathIdTruncIso n))
          (lem₁ n))

  main : (typ ((Ω^ n) (hLevelTrunc∙ n (Ω A))))
       ≡ (typ ((Ω^ suc n) (hLevelTrunc∙ (suc n) A)))
  main = (λ i → typ ((Ω^ n) (lem₂ i)))
       ∙ sym (isoToPath (flipΩIso n))


mutual
  ΩTruncSwitchFun : ∀ {ℓ} {A : Pointed ℓ} (n m : ℕ) →
    (hLevelTrunc∙ (suc (suc m)) ((Ω^ n) A))
      →∙ ((Ω^ n) (hLevelTrunc∙ (suc n + suc m) A))
  ΩTruncSwitchFun {A = A} n m =
    ((λ x → transport
                (λ i → fst ((Ω^ n) (hLevelTrunc∙ (+-suc n (suc m) i) A)))
                (Iso.fun (ΩTruncSwitch {A = A} n (suc (suc m))) x))
       , cong (transport
                 (λ i → fst ((Ω^ n) (hLevelTrunc∙ (+-suc n (suc m) i) A))))
               (ΩTruncSwitch∙ n (suc (suc m)))
       ∙ λ j → transp
                (λ i → fst ((Ω^ n) (hLevelTrunc∙ (+-suc n (suc m) (i ∨ j)) A)))
                j (snd ((Ω^ n) (hLevelTrunc∙ (+-suc n (suc m) j) A))))

  ΩTruncSwitchLem :
    ∀ {ℓ} {A : Pointed ℓ} (n m : ℕ)
    → Iso
      (typ (Ω (hLevelTrunc∙ (suc (suc m)) ((Ω^ n) A))))
      (typ ((Ω^ suc n) (hLevelTrunc∙ (suc n + suc m) A)))
  ΩTruncSwitchLem {A = A} n m =
    (equivToIso
     (Ω→ (ΩTruncSwitchFun n m) .fst
    , isEquivΩ→ _ (compEquiv (isoToEquiv (ΩTruncSwitch {A = A} n (suc (suc m))))
       (pathToEquiv
         (λ i → typ ((Ω^ n) (hLevelTrunc∙ (+-suc n (suc m) i) A)))) .snd)))

  ΩTruncSwitch : ∀ {ℓ} {A : Pointed ℓ} (n m : ℕ)
    → Iso (hLevelTrunc m (fst ((Ω^ n) A)))
           (typ ((Ω^ n) (hLevelTrunc∙ (n + m) A)))
  ΩTruncSwitch {A = A} n zero =
    equivToIso
    (invEquiv
      (isContr→≃Unit*
        (subst isContr
          (λ i → (typ ((Ω^ n) (hLevelTrunc∙ (+-comm zero n i) A))))
        (isContrΩTrunc n))))
  ΩTruncSwitch {A = A} zero (suc m) = idIso
  ΩTruncSwitch {A = A} (suc n) (suc m) =
    compIso (invIso (PathIdTruncIso _))
      (ΩTruncSwitchLem n m)

  ΩTruncSwitch∙ : ∀ {ℓ} {A : Pointed ℓ} (n m : ℕ)
    → Iso.fun (ΩTruncSwitch {A = A} n m) (snd (hLevelTrunc∙ m ((Ω^ n) A)))
     ≡ pt ((Ω^ n) (hLevelTrunc∙ (n + m) A))
  ΩTruncSwitch∙ {A = A} n zero =
    isContr→isProp
    ((subst isContr
       (λ i → (typ ((Ω^ n) (hLevelTrunc∙ (+-comm zero n i) A))))
       (isContrΩTrunc n))) _ _
  ΩTruncSwitch∙ {A = A} zero (suc m) = refl
  ΩTruncSwitch∙ {A = A} (suc n) (suc m) = ∙∙lCancel _


ΩTruncSwitch-hom : ∀ {ℓ} {A : Pointed ℓ} (n m : ℕ) (p q : _)
        → Iso.fun (ΩTruncSwitch {A = A} (suc n) (suc m)) ∣ p ∙ q ∣
         ≡ Iso.fun (ΩTruncSwitch {A = A} (suc n) (suc m)) ∣ p ∣
         ∙ Iso.fun (ΩTruncSwitch {A = A} (suc n) (suc m)) ∣ q ∣
ΩTruncSwitch-hom {A = A} n m p q =
    cong (Iso.fun (ΩTruncSwitchLem {A = A} n m))
         (cong-∙ ∣_∣ₕ p q)
  ∙ Ω→pres∙ (ΩTruncSwitchFun n m) (cong ∣_∣ₕ p) (cong ∣_∣ₕ q)

2TruncΩIso : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
    → Iso (hLevelTrunc 2 (fst ((Ω^ n) A)))
           (typ ((Ω^ n) (hLevelTrunc∙ (2 + n) A)))
2TruncΩIso zero = idIso
2TruncΩIso {A = A} (suc n) =
  compIso
   (ΩTruncSwitch (suc n) 2)
   (pathToIso λ i → typ ((Ω^ suc n) (hLevelTrunc∙ (+-comm (suc n) 2 i) A)))

hLevΩ+ : ∀ {ℓ} {A : Pointed ℓ} (n m : ℕ)
      → isOfHLevel (m + n) (typ A) → isOfHLevel n (typ ((Ω^ m) A))
hLevΩ+ n zero p = p
hLevΩ+ {A = A} zero (suc zero) p = refl , λ _ → isProp→isSet p _ _ _ _
hLevΩ+ {A = A} zero (suc (suc zero)) p =
  refl , λ y → isOfHLevelSuc 2 p _ _ _ _ refl y
hLevΩ+ {A = A} zero (suc (suc (suc m))) p =
  transport
   (λ i → isContr (typ (Ω (ua∙
            (isoToEquiv (flipΩIso {A = A} (suc m))) (flipΩrefl m) (~ i)))))
    (hLevΩ+ {A = Ω A} zero (suc (suc m))
     (subst (λ x → isOfHLevel x (typ (Ω A)))
            (+-comm zero (suc (suc m)))
            (lem (pt A) (pt A))))
  where
  lem : isOfHLevel (3 + m) (typ A)
  lem = subst (λ x → isOfHLevel x (typ A))
              (λ i → suc (+-comm (2 + m) zero i)) p
hLevΩ+ {A = A} (suc n) (suc m) p =
  subst (isOfHLevel (suc n))
    (sym (ua (isoToEquiv (flipΩIso {A = A} m))))
    (hLevΩ+ {A = Ω A} (suc n) m
      (isOfHLevelPath' (m + suc n) p _ _))

isSetΩTrunc : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
  → (isSet (typ (Ω ((Ω^ n) (hLevelTrunc∙ (suc (suc (suc n))) A)))))
isSetΩTrunc {A = A} zero = isOfHLevelTrunc 3 _ _
isSetΩTrunc {A = A} (suc n) =
  hLevΩ+ 2 (suc (suc n))
    (transport
     (λ i → isOfHLevel (+-comm 2 (2 + n) i) (hLevelTrunc (4 + n) (typ A)))
      (isOfHLevelTrunc (suc (suc (suc (suc n))))))

πTruncIso : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
             → Iso (π n A) (π n (hLevelTrunc∙ (2 + n) A))
πTruncIso {A = A} zero =
  compIso (invIso (setTruncIdempotentIso squash₂))
                  (setTruncIso setTruncTrunc2Iso)
πTruncIso {A = A} (suc n) =
  compIso setTruncTrunc2Iso
    (compIso
     (2TruncΩIso (suc n))
     (invIso (setTruncIdempotentIso (isSetΩTrunc n))))

πTruncGroupIso : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
             → GroupIso (πGr n A) (πGr n (hLevelTrunc∙ (3 + n) A))
fst (πTruncGroupIso n) = πTruncIso (suc n)
snd (πTruncGroupIso {A = A} n) =
  makeIsGroupHom
    (sElim2 (λ _ _ → isSetPathImplicit)
      λ a b
      → cong (inv (setTruncIdempotentIso (isSetΩTrunc n)))
         (cong
          (transport
           (λ i → typ ((Ω^ suc n) (hLevelTrunc∙ (+-comm (suc n) 2 i) A))))
           (ΩTruncSwitch-hom n 1 a b)
        ∙ transpΩTruncSwitch
            (λ w → ((Ω^ n) (hLevelTrunc∙ w A))) (+-comm (suc n) 2) _ _))
  where
  transpΩTruncSwitch : ∀ {ℓ} (A : ℕ → Pointed ℓ) {n m : ℕ}
    (r : n ≡ m) (p q : typ (Ω (A n)))
    → subst (λ n → typ (Ω (A n))) r (p ∙ q)
     ≡ subst (λ n → typ (Ω (A n))) r p
     ∙ subst (λ n → typ (Ω (A n))) r q
  transpΩTruncSwitch A {n = n} =
    J (λ m r → (p q : typ (Ω (A n)))
              → subst (λ n → typ (Ω (A n))) r (p ∙ q)
               ≡ subst (λ n → typ (Ω (A n))) r p
               ∙ subst (λ n → typ (Ω (A n))) r q)
      λ p q → transportRefl _ ∙ cong₂ _∙_
                (sym (transportRefl p)) (sym (transportRefl q))

-- Often, we prefer thinking of Ωⁿ A as (Sⁿ →∙ A).
-- The goal of the following lemmas is to show that the maps
-- Ωⁿ A → Ωⁿ B and Ωⁿ (fib f) →∙ Ωⁿ A get sent to post composition
-- under the equivalence Ωⁿ A as (Sⁿ →∙ A). This also gives a proof
-- that post composition induces a homomorphism of homotopy groups.

-- The following lemmas is not pretty but very helpful
private
  bigLemma : ∀ {ℓ ℓ'} {A₁ B₁ C₁ : Type ℓ} {A₂ B₂ C₂ : Type ℓ'}
             (A₁→B₁ : A₁ ≃ B₁) (B₁→C₁ : B₁ ≃ C₁)
             (A₂→B₂ : A₂ ≃ B₂) (B₂→C₂ : B₂ ≃ C₂)
             (A₁→A₂ : A₁ → A₂)
             (B₁→B₂ : B₁ → B₂)
             (C₁→C₂ : C₁ → C₂)
          → (B₁→B₂ ∘ (fst A₁→B₁)) ≡ (fst A₂→B₂ ∘ A₁→A₂)
          → C₁→C₂ ∘ fst B₁→C₁ ≡ fst B₂→C₂ ∘ B₁→B₂
          → C₁→C₂ ∘ fst B₁→C₁ ∘ fst A₁→B₁
          ≡ fst B₂→C₂ ∘ fst A₂→B₂ ∘ A₁→A₂
  bigLemma {B₁ = B₁} {C₁ = C₁} {A₂ = A₂} {B₂ = B₂} {C₂ = C₂} =
    EquivJ
      (λ A₁ A₁→B₁ → (B₁→C₁ : B₁ ≃ C₁) (A₂→B₂ : A₂ ≃ B₂)
        (B₂→C₂ : B₂ ≃ C₂) (A₁→A₂ : A₁ → A₂) (B₁→B₂ : B₁ → B₂)
        (C₁→C₂ : C₁ → C₂) →
        B₁→B₂ ∘ fst A₁→B₁ ≡ fst A₂→B₂ ∘ A₁→A₂ →
        C₁→C₂ ∘ fst B₁→C₁ ≡ fst B₂→C₂ ∘ B₁→B₂ →
        C₁→C₂ ∘ fst B₁→C₁ ∘ fst A₁→B₁ ≡ fst B₂→C₂ ∘ fst A₂→B₂ ∘ A₁→A₂)
      (EquivJ (λ B₁ B₁→C₁ → (A₂→B₂ : A₂ ≃ B₂) (B₂→C₂ : B₂ ≃ C₂)
        (A₁→A₂ : B₁ → A₂) (B₁→B₂ : B₁ → B₂) (C₁→C₂ : C₁ → C₂) →
        (B₁→B₂) ≡ (fst A₂→B₂ ∘ A₁→A₂) →
        (C₁→C₂ ∘ (fst B₁→C₁)) ≡ (fst B₂→C₂ ∘ (B₁→B₂)) →
        (C₁→C₂ ∘ (fst B₁→C₁)) ≡ (fst B₂→C₂ ∘ (fst A₂→B₂ ∘ A₁→A₂)))
        (EquivJ (λ A₂ A₂→B₂ → (B₂→C₂ : B₂ ≃ C₂) (A₁→A₂ : C₁ → A₂)
          (B₁→B₂ : C₁ → B₂) (C₁→C₂ : C₁ → C₂) →
          B₁→B₂ ≡ (fst A₂→B₂ ∘ A₁→A₂) →
          (C₁→C₂) ≡ (fst B₂→C₂ ∘ B₁→B₂) →
          (C₁→C₂) ≡ fst B₂→C₂ ∘ (fst A₂→B₂ ∘ A₁→A₂))
          (EquivJ (λ B₂ B₂→C₂ → (A₁→A₂ B₁→B₂ : C₁ → B₂) (C₁→C₂ : C₁ → C₂) →
            B₁→B₂ ≡ A₁→A₂ →
            C₁→C₂ ≡ (fst B₂→C₂ ∘ B₁→B₂) →
            C₁→C₂ ≡ (fst B₂→C₂ ∘ A₁→A₂))
              λ _ _ _ p q → q ∙ p)))

{-
We want to show that the following square
commutes.

       Ωⁿ f
Ωⁿ A ----------→ Ωⁿ B
|                  |
|                  |
v         f∘_      v
(Sⁿ→∙A) ------> (Sⁿ→∙B)
-}

Ω^→≈post∘∙ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ)
  → (f : A →∙ B)
  → Path ((Ω^ (suc n)) A →∙ (S₊∙ (suc n) →∙ B ∙))
          (post∘∙ (S₊∙ (suc n)) f ∘∙ Ω→SphereMap∙ (suc n))
          (Ω→SphereMap∙ (suc n) ∘∙ Ω^→ (suc n) f)
Ω^→≈post∘∙ {A = A} {B = B} zero f =
    →∙Homogeneous≡
       (subst isHomogeneous
        (ua∙ (Ω→SphereMap 1 , (isEquiv-Ω→SphereMap 1))
             (Ω→SphereMap∙ 1 {A = B} .snd))
    (isHomogeneousPath _ _))
    (funExt λ p →
      ΣPathP ((funExt (λ { base → snd f
                        ; (loop i) j →
                          doubleCompPath-filler
                            (sym (snd f)) (cong (fst f) p) (snd f) j i}))
            , (sym (lUnit (snd f)) ◁ λ i j → snd f (i ∨ j))))
Ω^→≈post∘∙ {A = A} {B = B} (suc n) f =
  →∙Homogeneous≡
    (subst isHomogeneous
      (ua∙ (Ω→SphereMap (2 + n) , (isEquiv-Ω→SphereMap (2 + n)))
           (Ω→SphereMap∙ (2 + n) {A = B} .snd))
           (isHomogeneousPath _ _))
    ((funExt λ p
        → (λ i → post∘∙ (S₊∙ (2 + n)) f .fst (Ω→SphereMap-split (suc n) p i))
        ∙∙ funExt⁻
          (bigLemma
            (Ω→SphereMapSplit₁ (suc n)
            , isEquivΩ→ _ (isEquiv-Ω→SphereMap (suc n)))
            (ΩSphereMap (suc n) , isoToIsEquiv (invIso (SphereMapΩIso (suc n))))
            (Ω→SphereMapSplit₁ (suc n)
            , isEquivΩ→ _ (isEquiv-Ω→SphereMap (suc n)))
            (ΩSphereMap (suc n) , isoToIsEquiv (invIso (SphereMapΩIso (suc n))))
            (Ω^→ (2 + n) f .fst) (Ω→ (post∘∙ (S₊∙ (suc n)) f) .fst)
            (post∘∙ (S₊∙ (2 + n)) f .fst)
            (funExt topSquare)
            (sym (funExt (bottomSquare f))))
            p
        ∙∙ sym (Ω→SphereMap-split (suc n) (Ω^→ (2 + n) f .fst p))))
  where
  topSquare : (p : typ ((Ω^ (2 + n)) A))
    → Path (typ (Ω ((S₊∙ (suc n)) →∙ B ∙)))
        ((Ω→ (post∘∙ (S₊∙ (suc n)) f) .fst ∘ Ω→ (Ω→SphereMap∙ (suc n)) .fst) p)
        (((Ω→ (Ω→SphereMap∙ (suc n))) .fst ∘ (Ω^→ (suc (suc n)) f .fst)) p)
  topSquare p = sym (Ω→∘ (post∘∙ (S₊∙ (suc n)) f) (Ω→SphereMap∙ (suc n)) p)
              ∙ (λ i → Ω→ (Ω^→≈post∘∙ {A = A} {B = B} n f i) .fst p)
              ∙ Ω→∘ (Ω→SphereMap∙ (suc n)) (Ω^→ (suc n) f) p

  bottomSquare : (f : A →∙ B) (g : typ (Ω (S₊∙ (suc n) →∙ A ∙)))
    → Path (S₊∙ (2 + n) →∙ B)
            (ΩSphereMap (suc n) (Ω→ (post∘∙ (S₊∙ (suc n)) f) .fst g))
            ((post∘∙ (S₊∙ (2 + n)) f .fst ∘ ΩSphereMap (suc n)) g)
  bottomSquare =
    →∙J (λ b₀ f → (g : typ (Ω (S₊∙ (suc n) →∙ A ∙)))
            → Path (S₊∙ (suc (suc n)) →∙ (fst B , b₀))
            (ΩSphereMap (suc n) (Ω→ (post∘∙ (S₊∙ (suc n)) f) .fst g))
            ((post∘∙ (S₊∙ (suc (suc n))) f .fst ∘ ΩSphereMap (suc n)) g))
           λ f g → ΣPathP ((funExt (λ { north → refl
                                       ; south → refl
                                       ; (merid a i) j → lem f g a j i}))
                        , lUnit refl)
    where
    lem : (f : typ A → typ B) (g : typ (Ω (S₊∙ (suc n) →∙ A ∙)))
      → (a : S₊ (suc n))
      → cong (fst (ΩSphereMap (suc n)
               (Ω→ (post∘∙ (S₊∙ (suc n)) (f , refl)) .fst g)))
             (merid a)
        ≡ cong (fst ((f , refl) ∘∙ ΩSphereMap (suc n) g)) (merid a)
    lem f g a =
      (λ i → funExt⁻
        (cong-∙∙ fst (sym (snd (post∘∙ (S₊∙ (suc n)) (f , (λ _ → f (snd A))))))
                 (cong (fst (post∘∙ (S₊∙ (suc n)) (f , (λ _ → f (snd A))))) g)
                 (snd (post∘∙ (S₊∙ (suc n)) (f , (λ _ → f (snd A))))) i) a)
              ∙ sym (rUnit (λ i → f (fst (g i) a)))

{- We can use this to define prove that post composition induces a homomorphism
πₙ A → πₙ B-}

π'∘∙fun : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ) (f : A →∙ B)
        → π' (suc n) A → π' (suc n) B
π'∘∙fun n f = sMap (f ∘∙_)

GroupHomπ≅π'PathP : ∀ {ℓ ℓ'} (A : Pointed ℓ) (B : Pointed ℓ') (n m : ℕ)
  → GroupHom (πGr n A) (πGr m B) ≡ GroupHom (π'Gr n A) (π'Gr m B)
GroupHomπ≅π'PathP A B n m i =
  GroupHom (fst (GroupPath _ _) (GroupIso→GroupEquiv (π'Gr≅πGr n A)) (~ i))
           (fst (GroupPath _ _) (GroupIso→GroupEquiv (π'Gr≅πGr m B)) (~ i))

πFun : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ) (f : A →∙ B)
     → π (suc n) A → π (suc n) B
πFun n f = sMap (fst (Ω^→ (suc n) f))

πHom : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ) (f : A →∙ B)
     → GroupHom (πGr n A) (πGr n B)
fst (πHom n f) = πFun n f
snd (πHom n f) =
  makeIsGroupHom
    (sElim2 (λ _ _ → isSetPathImplicit)
      λ p q → cong ∣_∣₂ (Ω^→pres∙ f n p q))

π'∘∙Hom' : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ) (f : A →∙ B)
        → GroupHom (π'Gr n A) (π'Gr n B)
π'∘∙Hom' {A = A} {B = B} n f =
  transport (λ i → GroupHomπ≅π'PathP A B n n i)
            (πHom n f)

π'∘∙Hom'≡π'∘∙fun : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
  (n : ℕ) (f : A →∙ B) → π'∘∙Hom' n f .fst ≡ π'∘∙fun n f
π'∘∙Hom'≡π'∘∙fun n f =
  funExt (sElim (λ _ → isSetPathImplicit)
    λ g → cong ∣_∣₂
      ((λ i → inv (IsoSphereMapΩ (suc n))
          (transportRefl (Ω^→ (suc n) f .fst
            (transportRefl (fun (IsoSphereMapΩ (suc n)) g) i)) i))
     ∙ sym (funExt⁻ (cong fst (Ω^→≈post∘∙ n f))
                    (fun (IsoSphereMapΩ (suc n)) g))
     ∙ cong (f ∘∙_) (leftInv (IsoSphereMapΩ (suc n)) g)))

π'∘∙Hom : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ) (f : A →∙ B)
       → GroupHom (π'Gr n A) (π'Gr n B)
fst (π'∘∙Hom n f) = sMap (f ∘∙_)
snd (π'∘∙Hom {A = A} {B = B} n f) = isHom∘∙
  where
  abstract
    isHom∘∙ : IsGroupHom (π'Gr n A .snd) (fst (π'∘∙Hom n f)) (π'Gr n B .snd)
    isHom∘∙ =
      transport (λ i → IsGroupHom (π'Gr n A .snd)
                                   (π'∘∙Hom'≡π'∘∙fun n f i)
                                   (π'Gr n B .snd))
                (π'∘∙Hom' n f .snd)

GroupHomπ≅π'PathP-hom : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
  (n : ℕ) (f : A →∙ B)
  → PathP (λ i → GroupHomπ≅π'PathP A B n n i) (πHom n f) (π'∘∙Hom n f)
GroupHomπ≅π'PathP-hom {A = A} {B = B} n f =
  (λ j → transp (λ i → GroupHomπ≅π'PathP A B n n (i ∧ j)) (~ j)
                 (πHom n f))
  ▷ Σ≡Prop (λ _ → isPropIsGroupHom _ _) (π'∘∙Hom'≡π'∘∙fun n f)

-- post composition with an equivalence induces an
-- isomorphism of homotopy groups
π'eqFun : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ)
      → A ≃∙ B
      → (π' (suc n) A) → π' (suc n) B
π'eqFun n p = π'∘∙fun n (≃∙map p)

π'eqFun-idEquiv : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
              → π'eqFun n (idEquiv (fst A) , (λ _ → pt A))
               ≡ idfun _
π'eqFun-idEquiv n =
  funExt (sElim (λ _ → isSetPathImplicit)
    λ f → cong ∣_∣₂ (∘∙-idʳ f))

invEquiv∙idEquiv∙≡idEquiv : ∀ {ℓ} {A : Pointed ℓ}
  → invEquiv∙ (idEquiv (fst A) , (λ _ → pt A))
  ≡ (idEquiv (fst A) , refl)
invEquiv∙idEquiv∙≡idEquiv = ΣPathP ((Σ≡Prop (λ _ → isPropIsEquiv _) refl) , (sym (lUnit refl)))

π'eqFunIsEquiv :
  ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ)
      → (e : A ≃∙ B)
      → isEquiv (π'eqFun n e)
π'eqFunIsEquiv {ℓ = ℓ} {ℓ'} {A} {B} n e =
  subst isEquiv
    (funExt (sElim (λ _ → isSetPathImplicit)
             (λ f → cong ∣_∣₂
             (ΣPathP (refl
               , (cong-∙ lower (cong (lift ∘ (fst (fst e))) (snd f)) _))))))
    (πA≃πB .snd)
  where
  e' : Lift∙ {j = ℓ'} A ≃∙ Lift∙ {j = ℓ} B
  fst e' =
    compEquiv (invEquiv LiftEquiv) (compEquiv (fst e) LiftEquiv)
  snd e' = cong lift (snd e)

  main : ∀ {ℓ} {A B : Pointed ℓ} (n : ℕ)
      → (e : A ≃∙ B)
      → isEquiv (π'eqFun n e)
  main {B = B} n =
    Equiv∙J (λ A e → isEquiv (π'eqFun n e))
     (subst isEquiv (sym (π'eqFun-idEquiv n))
      (idIsEquiv (π' (suc n) B)))

  πA≃πB : π' (suc n) A ≃ π' (suc n) B
  πA≃πB =
    compEquiv (invEquiv (isoToEquiv (fst (π'GrLiftIso _ n))))
     (compEquiv (_ , main n e')
       (isoToEquiv (fst (π'GrLiftIso _ n))))

π'eqFunIsHom : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ)
      → (e : A ≃∙ B)
      → IsGroupHom (π'Gr n A .snd) (π'eqFun n e)
                    (π'Gr n B .snd)
π'eqFunIsHom {ℓ = ℓ} {ℓ'} {A} {B} n e =
  subst (λ ϕ → IsGroupHom (π'Gr n A .snd)
                         ϕ (π'Gr n B .snd))
        (funExt (sElim (λ _ → isSetPathImplicit)
          (λ f → cong ∣_∣₂ (ΣPathP
            (refl
           , cong-∙ lower (cong (lift ∘ (fst (fst e))) (snd f)) _)))))
        (compGroupHom
          (GroupIso→GroupHom (invGroupIso (π'GrLiftIso _ n)))
         (compGroupHom (_ , main n e')
          (GroupIso→GroupHom (π'GrLiftIso _ n))) .snd)
  where
  e' : Lift∙ {j = ℓ'} A ≃∙ Lift∙ {j = ℓ} B
  fst e' =
    compEquiv (invEquiv LiftEquiv) (compEquiv (fst e) LiftEquiv)
  snd e' = cong lift (snd e)

  main : ∀ {ℓ} {A B : Pointed ℓ} (n : ℕ)
      → (e : A ≃∙ B)
      → IsGroupHom (π'Gr n A .snd) (π'eqFun n e)
                    (π'Gr n B .snd)
  main {B = B} n =
    Equiv∙J (λ A e → IsGroupHom (π'Gr n A .snd) (π'eqFun n e) (π'Gr n B .snd))
    (subst (λ x → IsGroupHom (π'Gr n B .snd) x (π'Gr n B .snd))
      (sym (π'eqFun-idEquiv n))
      (makeIsGroupHom λ _ _ → refl))

π'GrIso : {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ)
  (e : A ≃∙ B) → GroupIso (π'Gr n A) (π'Gr n B)
fst (π'GrIso n e) = setTruncIso (pre∘∙equiv e)
snd (π'GrIso n e) = π'eqFunIsHom n e

π'Iso : ∀ {ℓ} {A : Pointed ℓ} {B : Pointed ℓ} (n : ℕ)
      → A ≃∙ B
      → GroupEquiv (π'Gr n A) (π'Gr n B)
π'Iso n e = GroupIso→GroupEquiv (π'GrIso n e)

πIso : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
        → (A ≃∙ B)
        → (n : ℕ)
        → GroupEquiv (πGr n A) (πGr n B)
fst (fst (πIso e n)) = fst (πHom n (≃∙map e))
snd (fst (πIso e n)) =
  isoToIsEquiv
    (setTruncIso
      (equivToIso (_ , isEquivΩ^→ (suc n) (≃∙map e) (snd (fst e)))))
snd (πIso e n) = snd (πHom n (≃∙map e))

hGroupoidπ₁ : ∀ {ℓ} (A : hGroupoid ℓ) → ⟨ A ⟩ → Group ℓ
fst (hGroupoidπ₁ A a) = a ≡ a
1g (snd (hGroupoidπ₁ A a)) = refl
GroupStr._·_ (snd (hGroupoidπ₁ A a)) = _∙_
inv (snd (hGroupoidπ₁ A a)) = sym
is-set (isSemigroup (isMonoid (isGroup (snd (hGroupoidπ₁ A a))))) = snd A a a
·Assoc (isSemigroup (isMonoid (isGroup (snd (hGroupoidπ₁ A a))))) = ∙assoc
·IdR (isMonoid (isGroup (snd (hGroupoidπ₁ A a)))) = sym ∘ rUnit
·IdL (isMonoid (isGroup (snd (hGroupoidπ₁ A a)))) = sym ∘ lUnit
·InvR (isGroup (snd (hGroupoidπ₁ A a))) = rCancel
·InvL (isGroup (snd (hGroupoidπ₁ A a))) = lCancel

-- Adjunction
sphereFunIso : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
  → Iso (S₊∙ n →∙ (Path (fst A) (pt A) (pt A) , refl)) (S₊∙ (suc n) →∙ A)
sphereFunIso zero = compIso IsoBool→∙ (invIso (IsoSphereMapΩ 1))
sphereFunIso (suc n) = ΩSuspAdjointIso

--
∙Π∘∙ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
  (n : ℕ) (f g : S₊∙ (suc n) →∙ A) (h : A →∙ B)
  → h ∘∙ ∙Π f g ≡ ∙Π (h ∘∙ f) (h ∘∙ g)
∙Π∘∙ {A = A} n f g h =
     cong (h ∘∙_) (cong₂ ∙Π (sym (Iso.rightInv (sphereFunIso n) f))
                            (sym (Iso.rightInv (sphereFunIso n) g)))
  ∙∙ lem2 n (Iso.inv (sphereFunIso n) f) (Iso.inv (sphereFunIso n) g)
  ∙∙ cong₂ (λ f g → ∙Π (h ∘∙ f) (h ∘∙ g))
           (Iso.rightInv (sphereFunIso n) f)
           (Iso.rightInv (sphereFunIso n) g)
  where
  lem : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) → Square p refl (refl ∙ p) refl
  lem p = lUnit p ◁ λ i j → (refl ∙ p) (i ∨ j)

  mainEq : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) (a : A) (b : B)
    (fp : f a ≡ b) (l1 l2 : a ≡ a)
    → Square (cong f ((l1 ∙ refl) ∙ (l2 ∙ refl)))
             ((sym (refl ∙ fp) ∙∙ cong f l1 ∙∙ (refl ∙ fp))
            ∙ (sym (refl ∙ fp) ∙∙ cong f l2 ∙∙ (refl ∙ fp)))
              fp fp
  mainEq f a = J> λ l1 l2 → cong-∙ f _ _
    ∙ cong₂ _∙_ (cong-∙ f l1 refl  ∙ cong₃ _∙∙_∙∙_ (rUnit refl) refl (rUnit refl))
                (cong-∙ f l2 refl ∙ cong₃ _∙∙_∙∙_ (rUnit refl) refl (rUnit refl))

  lem2 : (n : ℕ) (f g : S₊∙ n →∙ Ω A)
    → (h ∘∙ ∙Π (Iso.fun (sphereFunIso n) f) (Iso.fun (sphereFunIso n) g))
    ≡ ∙Π (h ∘∙ Iso.fun (sphereFunIso n) f) (h ∘∙ Iso.fun (sphereFunIso n) g)
  fst (lem2 zero f g i) base = snd h i
  fst (lem2 zero f g i) (loop i₁) =
    mainEq (fst h) _ _ (snd h) (fst f false) (fst g false) i i₁
  fst (lem2 (suc n) f g i) north = snd h i
  fst (lem2 (suc n) f g i) south = snd h i
  fst (lem2 (suc n) f g i) (merid a i₁) =
    mainEq (fst h) _ _ (snd h)
      (cong (Iso.fun (sphereFunIso (suc n)) f .fst) (σS a))
      (cong (Iso.fun (sphereFunIso (suc n)) g .fst) (σS a)) i i₁
  snd (lem2 zero f g i) j = lem (snd h) j i
  snd (lem2 (suc n) f g i) j = lem (snd h) j i
