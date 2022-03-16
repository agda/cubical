{-# OPTIONS --safe --experimental-lossy-unification #-}
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
assoc (isSemigroup (isMonoid (isGroup (snd (πGr n A))))) = π-assoc n
identity (isMonoid (isGroup (snd (πGr n A)))) x = (π-rUnit n x) , (π-lUnit n x)
inverse (isGroup (snd (πGr n A))) x = (π-rCancel n x) , (π-lCancel n x)

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
       (transportEquiv
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

GroupHomπ≅π'PathP : ∀ {ℓ ℓ'} (A : Pointed ℓ) (B : Pointed ℓ') (n : ℕ)
  → GroupHom (πGr n A) (πGr n B) ≡ GroupHom (π'Gr n A) (π'Gr n B)
GroupHomπ≅π'PathP A B n i =
  GroupHom (fst (GroupPath _ _) (GroupIso→GroupEquiv (π'Gr≅πGr n A)) (~ i))
           (fst (GroupPath _ _) (GroupIso→GroupEquiv (π'Gr≅πGr n B)) (~ i))

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
  transport (λ i → GroupHomπ≅π'PathP A B n i)
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

-- post composition with an equivalence induces an
-- isomorphism of homotopy groups
π'eqFun : ∀ {ℓ} {A : Pointed ℓ} {B : Pointed ℓ} (n : ℕ)
      → A ≃∙ B
      → (π' (suc n) A) → π' (suc n) B
π'eqFun n p = π'∘∙fun n (≃∙map p)

π'eqFun-idEquiv : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
              → π'eqFun n (idEquiv (fst A) , (λ _ → pt A))
               ≡ idfun _
π'eqFun-idEquiv n =
  funExt (sElim (λ _ → isSetPathImplicit)
    λ f → cong ∣_∣₂ (∘∙-idʳ f))

π'eqFunIsEquiv :
  ∀ {ℓ} {A : Pointed ℓ} {B : Pointed ℓ} (n : ℕ)
      → (e : A ≃∙ B)
      → isEquiv (π'eqFun n e)
π'eqFunIsEquiv {B = B} n =
  Equiv∙J (λ A e → isEquiv (π'eqFun n e))
    (subst isEquiv (sym (π'eqFun-idEquiv n))
      (idIsEquiv (π' (suc n) B)))

π'eqFunIsHom : ∀ {ℓ} {A B : Pointed ℓ}(n : ℕ)
      → (e : A ≃∙ B)
      → IsGroupHom (π'Gr n A .snd) (π'eqFun n e)
                    (π'Gr n B .snd)
π'eqFunIsHom {B = B} n =
  Equiv∙J (λ A e → IsGroupHom (π'Gr n A .snd) (π'eqFun n e) (π'Gr n B .snd))
    (subst (λ x → IsGroupHom (π'Gr n B .snd) x (π'Gr n B .snd))
      (sym (π'eqFun-idEquiv n))
      (makeIsGroupHom λ _ _ → refl))

π'Iso : ∀ {ℓ} {A : Pointed ℓ} {B : Pointed ℓ} (n : ℕ)
      → A ≃∙ B
      → GroupEquiv (π'Gr n A) (π'Gr n B)
fst (fst (π'Iso n e)) = π'eqFun n e
snd (fst (π'Iso n e)) = π'eqFunIsEquiv n e
snd (π'Iso n e) = π'eqFunIsHom n e

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


open import Cubical.HITs.Wedge
open import Cubical.HITs.Join hiding (joinS¹S¹→S³)
open import Cubical.HITs.Pushout


{-
Goal: join (Susp A) B
———— Boundary ——————————————————————————————————————————————
j = i0 ⊢ inl north
j = i1 ⊢ inl north
i = i0 ⊢ inl north
i = i1 ⊢ inl north
-}





{-
i = i0 ⊢ inl south
i = i1 ⊢ push north b k
k = i0 ⊢ suspJoinFiller (~ i) r i1 (pt A) b
k = i1 ⊢ push south b i
r = i0 ⊢ c1-filler b i k i1
r = i1 ⊢ c1-filler b i k i1
-}

HopfM : join S¹ S¹ → S₊ 2
HopfM (inl x) = north
HopfM (inr x) = north
HopfM (push a b i) = (merid (a * b) ∙ sym (merid base)) i

∨map : join S¹ S¹ → (S₊∙ 2) ⋁ (S₊∙ 2)
∨map (inl x) = inr north
∨map (inr x) = inl north
∨map (push a b i) = ((λ i → inr (σ (S₊∙ 1) b i)) ∙∙ sym (push tt) ∙∙ (λ i → inl (σ (S₊∙ 1) a i))) i


_+join_ : (f g : (join S¹ S¹ , inl base) →∙ S₊∙ 2)
       → (join S¹ S¹ , inl base) →∙ S₊∙ 2
fst (f +join g) (inl x) = fst f (inl x)
fst (f +join g) (inr x) = fst g (inr x)
fst (f +join g) (push a b i) =
  (cong (fst f) (push a b ∙ sym (push base b))
  ∙∙ snd f ∙ sym (snd g)
  ∙∙ cong (fst g) (push base base ∙∙ sym (push a base) ∙∙ push a b)) i
snd (f +join g) = snd f

{-
S¹ × S¹ →∙ Ω S²
-}

join-fill : I → I → I → I → join S¹ S¹
join-fill r i j k =
  hfill (λ r → λ { (i = i0) → push (loop r) (loop (j ∨ r)) k
                  ; (i = i1) → push base (loop (j ∨ r)) k --  (k ∧ ~ r)
                  ; (j = i0) → push (loop (i ∨ r)) (loop r) k
                  ; (j = i1) → push (loop (i ∨ r)) base k
                  ; (k = i0) → inl (loop (i ∨ r)) -- inl (loop (i ∨ r))
                  ; (k = i1) → inr (loop (j ∨ r))})
        (inS (push (loop i) (loop j) k))
        r

{-
S³→joinS¹S¹ : S³ → join S¹ S¹
S³→joinS¹S¹ base = inl base
S³→joinS¹S¹ (surf j k i) = border-contraction i j k i1
-}

S3→joinS¹S¹ : S₊ 3 → join S¹ S¹
S3→joinS¹S¹ north = inl base
S3→joinS¹S¹ south = inl base
S3→joinS¹S¹ (merid north i) = inl base
S3→joinS¹S¹ (merid south i) = inl base
S3→joinS¹S¹ (merid (merid base i₁) i) = inl base
S3→joinS¹S¹ (merid (merid (loop i) j) k) = border-contraction k i j i1

-- S3→joinS¹S¹ : ?
-- S3→joinS¹S¹ = ?

tt123 = joinS¹S¹→S³
{-
S3→j→S3 : (x : S₊ 3) → joinS¹S¹→S³ (S3→joinS¹S¹ x) ≡ x
S3→j→S3 north = refl
S3→j→S3 south = merid north
S3→j→S3 (merid north i) j = merid north (i ∧ j)
S3→j→S3 (merid south i) j =
  hcomp (λ k → λ {(i = i0) → north
                 ; (i = i1) → merid north j
                 ; (j = i0) → north
                 ; (j = i1) → merid (merid base k) i})
        (merid north (i ∧ j))
S3→j→S3 (merid (merid base j) i) k =
  {!!}
S3→j→S3 (merid (merid (loop i) j) k) l =
  {!j = i0 ⊢ merid north (i ∧ k)
j = i1 ⊢ hcomp
         (λ { k₁ (i = i0) → north
            ; k₁ (i = i1) → merid north k
            ; k₁ (k = i0) → north
            ; k₁ (k = i1) → merid (merid base k₁) i
            })
         (merid north (i ∧ k))
i = i0 ⊢ north
i = i1 ⊢ merid north k
k = i0 ⊢ north
k = i1 ⊢ merid (merid base j) i!}
{-
  hcomp (λ r → λ { (i = i0) → {!join-fill r i j k -- joinS¹S¹→S³ (join-fill i1 i i0 k) -- joinS¹S¹→S³ (join-fill r i i0 k)!}
                  ; (i = i1) → {!!} -- merid (merid base (l ∧ j)) k
                  ; (j = i0) → {!joinS¹S¹→S³ (join-fill r i i0 k)!} -- joinS¹S¹→S³ (join-fill r i i0 k)
                  ; (j = i1) → {!!} -- merid (merid base l) k -- merid (merid base l) k
                  ; (k = i0) → {!!} -- north -- joinS¹S¹→S³ (push (loop r) (loop r) (k ∧ i))
                  ; (k = i1) → {!!} -- south
                  ; (l = i0) → ? -- joinS¹S¹→S³ (join-fill r i j k)
                  ; (l = i1) → ?})
        {!!} -}
  where
  help : PathP (λ r → Cube {A = S₊ 3} {!!} (λ k l → merid (merid base l) k)
                            {!!} {!!}
                            (λ j k → joinS¹S¹→S³ (push (loop r) (loop (j ∨ r)) k))
                            {!!})
                            {!!} {!!}
  help = {!!}
{-
i = i0 ⊢ merid (merid base (l ∧ j)) k
i = i1 ⊢ merid (merid base (l ∧ j)) k
j = i0 ⊢ merid north k
j = i1 ⊢ merid (merid base l) k
k = i0 ⊢ north
k = i1 ⊢ south
l = i0 ⊢ joinS¹S¹→S³ (S3→joinS¹S¹ (merid (merid (loop i) j) k))
l = i1 ⊢ merid (merid (loop i) j) k
-}
  
  -- hcomp {!!}
     --    {!!}

-- open import Cubical.HITs.S3
-- open import Cubical.HITs.S2
σ₂ : (a b : S¹) → typ (Ω (S₊∙ 3))
σ₂ base b = refl
σ₂ (loop i) base = refl
σ₂ (loop i) (loop j) k = {!!}






_⌣ₛ_ : {n m : ℕ} → S₊ (suc n) → S₊ (suc m) → S₊ (suc (n + (suc m)))
_⌣ₛ_ {n = zero} {m = zero} = S¹×S¹→S²
_⌣ₛ_ {n = zero} {m = suc m} base y = north
_⌣ₛ_ {n = zero} {m = suc m} (loop i) y = (merid y ∙ sym (merid north)) i
_⌣ₛ_ {n = suc n} {m = m} north y = north
_⌣ₛ_ {n = suc n} {m = m} south y = south
_⌣ₛ_ {n = suc n} {m = m} (merid a i) y = merid (a ⌣ₛ y) i

joinIso : (n m : ℕ) → join (S₊ (suc n)) (S₊ (suc m)) → S₊ (suc (suc n + suc m))
joinIso zero zero = joinS¹S¹→S³
joinIso zero (suc m) = {!!}
joinIso (suc n) m x =
  suspFun (joinIso n m) (joinSusp→suspJoin {A = (S₊∙ (suc n))} {B = (S₊∙ (suc m))} x)

joinIso2 : (n m : ℕ) → join (S₊ (suc n)) (S₊ (suc m)) → S₊ (suc (suc n + suc m))
joinIso2 n m (inl x) = north
joinIso2 n m (inr x) = south
joinIso2 n m (push a b i) = merid (a ⌣ₛ b) i

joinIso2-ind : (n m : ℕ) (x : _)
  → suspFun (joinIso2 n m) (S.joinSusp {A = S₊∙ (suc n)} {B = S₊∙ (suc m)} x)
  ≡ joinIso2 (suc n) m x
joinIso2-ind n m (inl north) = refl
joinIso2-ind n m (inl south) = sym (merid north)
joinIso2-ind n m (inl (merid a i)) j = merid north (i ∧ ~ j)
joinIso2-ind n m (inr x) = (merid north)
joinIso2-ind n m (push north b i) j = merid north (i ∧ j)
joinIso2-ind n m (push south b i) j = {!merid north (~ i ∨ ~ j)!}
joinIso2-ind n m (push (merid a k) b i) j = {!!}

theEq : (n m : ℕ) (x : join (S₊ (suc n)) (S₊ (suc m))) → joinIso n m x ≡ joinIso2 n m x 
theEq zero m x = {!!}
theEq (suc n) m x =
  (λ i → suspFun (funExt (theEq n m) i) (S.joinSusp x) )
  ∙ joinIso2-ind n m x

isEquivPostComp : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : y ≡ z)
  → isEquiv (λ (q : x ≡ y) → q ∙ p)
isEquivPostComp {z = z} =
  J (λ z p → isEquiv (λ q → q ∙ p))
    (subst isEquiv (funExt rUnit) (idIsEquiv _))


TorusAct : S¹ → S¹ → (typ (Ω (S₊∙ 3))) ≃ (typ (Ω (S₊∙ 3)))
fst (TorusAct a b) p = p ∙ merid (S¹×S¹→S² a b) ∙ sym (merid north)
snd (TorusAct a b) = isEquivPostComp _


CC : join S¹ S¹ → Type
CC (inl x) = typ (Ω (S₊∙ 3))
CC (inr x) = typ (Ω (S₊∙ 3))
CC (push a b i) = ua (TorusAct a b) (~ i)


s2 : {!!}
s2 = {!!}

dec : (x : join S¹ S¹) → CC x → inl base ≡ x
dec (inl x) p = {!push base x ∙∙ ? ∙∙ ?!}
dec (inr x) p = {!!}
dec (push a b i) = {!!}
  where
  F : (x : S¹) → typ (Ω (S₊∙ 3)) → inl base ≡ inl x
  F x = {!!}
  
  G : (x : S¹) → typ (Ω (S₊∙ 3)) → inl base ≡ inr x
  G x = {!!}


  s : PathP (λ i → ua (TorusAct a b) (~ i) → Path (join S¹ S¹) (inl base) (push a b i)) (F a) (G b)
  s = toPathP (funExt (λ p → (λ j → transp (λ i → Path (join S¹ S¹) (inl base) (push a b (i ∨ j))) j
                             (compPath-filler (F a (transportRefl p j
                                                  ∙ merid (S¹×S¹→S² a b) ∙ sym (merid north))) (push a b) j))
                             ∙ {!!}))


{-
S3→joinS¹S¹ : S₊ 3 → join S¹ S¹
S3→joinS¹S¹ north = inl base
S3→joinS¹S¹ south = inr base
S3→joinS¹S¹ (merid north i) = push base base i
S3→joinS¹S¹ (merid south i) = push base base i
S3→joinS¹S¹ (merid (merid base i₁) i) = push base base i
S3→joinS¹S¹ (merid (merid (loop k) j) i) =
  {!hcomp ? push (loop i₂) (loop i₁) i!}

S3→joinS¹S¹→S³ : (x : _) → S3→joinS¹S¹ (joinS¹S¹→S³ x) ≡ x
S3→joinS¹S¹→S³ (inl x) = push base base ∙ sym (push x base)
S3→joinS¹S¹→S³ (inr x) = {!!}
S3→joinS¹S¹→S³ (push a b i) = {!!}
-}

-}

HopF : S₊∙ 3 →∙ S₊∙ 2
fst HopF x = HopfM (S3→joinS¹S¹ x)
snd HopF = refl

HopF2 : S₊∙ 3 →∙ S₊∙ 2
fst HopF2 x = fold⋁ (∨map (S3→joinS¹S¹ x))
snd HopF2 = refl

deJoin : (join S¹ S¹ , inl base) →∙ S₊∙ 2 → S₊∙ 3 →∙ S₊∙ 2
fst (deJoin f) x = fst f (Iso.inv (IsoSphereJoin 1 1) x)
snd (deJoin f) = snd f

joinify : S₊∙ 3 →∙ S₊∙ 2 → (join S¹ S¹ , inl base) →∙ S₊∙ 2
fst (joinify f) x = fst f (joinS¹S¹→S³ x)
snd (joinify f) = snd f



{-
IsoSphereJoin : (n m : ℕ)
  → Iso (join (S₊ n) (S₊ m)) (S₊ (suc (n + m)))
IsoSphereJoin zero m =
  compIso join-comm
    (compIso (invIso Susp-iso-joinBool)
             (invIso (IsoSucSphereSusp m)))
IsoSphereJoin (suc n) m =
  compIso (Iso→joinIso
            (compIso (pathToIso (cong S₊ (cong suc (+-comm zero n))))
                     (invIso (IsoSphereJoin n 0)))
            idIso)
          (compIso (equivToIso joinAssocDirect)
            (compIso (Iso→joinIso idIso
                      (compIso join-comm
                       (compIso (invIso Susp-iso-joinBool)
                                (invIso (IsoSucSphereSusp m)))))
                (compIso
                  (IsoSphereJoin n (suc m))
                    (pathToIso λ i → S₊ (suc (+-suc n m i))))))
-}

open import Cubical.Data.Bool renaming (Bool to BoolT)


joininfy-dejoin : (f : (join S¹ S¹ , inl base) →∙ S₊∙ 2) → joinify (deJoin f) ≡ f
joininfy-dejoin x = {!!}

dejoin-joinify : (f : S₊∙ 3 →∙ S₊∙ 2) → deJoin (joinify f) ≡ f
dejoin-joinify = {!!}

_+join≡_ : (f g : S₊∙ 3 →∙ S₊∙ 2)
         → joinify (∙Π f g) -- deJoin (f +join g)
         ≡ (joinify f +join joinify g) -- ∙Π (deJoin f) (deJoin g)
_+join≡_ f g =
  ΣPathP ((funExt (λ { (inl x) → sym (snd f)
                     ; (inr x) → sym (snd g) ∙ cong (fst g) (merid north)
                     ; (push a b i) j → h a b j i}))
        , λ i j → snd f (j ∨ ~ i))
  where
  S¹×S¹→S²rUnit : (a : S¹) → S¹×S¹→S² a base ≡ north
  S¹×S¹→S²rUnit base = refl
  S¹×S¹→S²rUnit (loop i) = refl

  l1 : (a b : S¹)
    → cong (fst (joinify g)) (push base base ∙∙ sym (push a base) ∙∙ push a b)
    ≡ cong (fst g) (merid (S¹×S¹→S² a b))
  l1 a b = cong-∙∙ (fst (joinify g))
       (push base base) (sym (push a base)) (push a b)
       ∙ cong (cong (fst g) (merid north) ∙∙_∙∙ cong (fst g) (merid (S¹×S¹→S² a b)))
              (cong (cong (fst g)) (cong sym (cong merid (S¹×S¹→S²rUnit a))))
       ∙  ((λ i → (cong (fst g) (λ j → merid north (j ∧ ~ i)))
       ∙∙ (cong (fst g) (λ j → merid north (~ j ∧ ~ i)))
       ∙∙ cong (fst g) (merid (S¹×S¹→S² a b)))
       ∙ sym (lUnit (cong (fst g) (merid (S¹×S¹→S² a b)))))

  l2 : ∀ {ℓ} {A : Type ℓ} {x y z w u : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) (s : w ≡ u)
    → (refl ∙∙ p ∙∙ q) ∙ (r ∙∙ s ∙∙ refl)
     ≡ (p ∙∙ (q ∙ r) ∙∙ s)
  l2 p q r s = (λ i → (p ∙ q) ∙ compPath≡compPath' r s (~ i))
           ∙∙ sym (∙assoc p q (r ∙ s))
           ∙∙ cong (p ∙_) (∙assoc q r s)
            ∙ sym (doubleCompPath≡compPath p (q ∙ r) s)

  pp : (a b : S¹)
    → Square ((refl ∙∙ cong (fst f) (merid (S¹×S¹→S² a b) ∙ (λ i₂ → merid north (~ i₂))) ∙∙ snd f)
             ∙ (sym (snd g) ∙∙ cong (fst g) (merid (S¹×S¹→S² a b) ∙ (λ i₂ → merid north (~ i₂))) ∙∙ refl))
             (((cong (fst f) (merid (S¹×S¹→S² a b)) ∙ sym (cong (fst f) (merid north)))
                                          ∙∙ (snd f ∙ sym (snd g))
               ∙∙ cong (fst g) (merid (S¹×S¹→S² a b))))
           (λ _ → fst f north)
           (cong (fst g) (merid north))
  pp a b = l2 (cong (fst f) (merid (S¹×S¹→S² a b) ∙ (λ i₂ → merid north (~ i₂))))
              (snd f) (sym (snd g)) (cong (fst g)
              (merid (S¹×S¹→S² a b) ∙ (λ i₂ → merid north (~ i₂))))
         ◁ p
    where
    p : PathP (λ i → fst f north ≡ cong (fst g) (merid north) i)
              ((λ i →
                  fst f ((merid (S¹×S¹→S² a b) ∙ (λ i₂ → merid north (~ i₂))) i))
               ∙∙ snd f ∙ (λ i → snd g (~ i)) ∙∙
               (λ i →
                  fst g ((merid (S¹×S¹→S² a b) ∙ (λ i₂ → merid north (~ i₂))) i)))
              ((cong (fst f) (merid (S¹×S¹→S² a b)) ∙
                sym (cong (fst f) (merid north)))
               ∙∙ snd f ∙ sym (snd g) ∙∙ cong (fst g) (merid (S¹×S¹→S² a b)))
    p i j =
      hcomp (λ k → λ { (i = i0) → (cong-∙ (fst f) (merid (S¹×S¹→S² a b)) (sym (merid north)) (~ k)
                                ∙∙ snd f ∙ (λ i₁ → snd g (~ i₁))
                                ∙∙ (λ i₁ → fst g (compPath-filler (merid (S¹×S¹→S² a b)) (λ i₂ → merid north (~ i₂)) k i₁))) j
                       ; (i = i1) → ((cong (fst f) (merid (S¹×S¹→S² a b)) ∙
                                      sym (cong (fst f) (merid north)))
                                     ∙∙ (snd f ∙ sym (snd g)) ∙∙ cong (fst g) (merid (S¹×S¹→S² a b)))
                                    j
                       ; (j = i0) → fst f north
                       ; (j = i1) → fst g (merid north (~ k ∨ i))})
            (((cong (fst f) (merid (S¹×S¹→S² a b)) ∙
                                      sym (cong (fst f) (merid north)))
                                     ∙∙ (snd f ∙ sym (snd g)) ∙∙ cong (fst g) (merid (S¹×S¹→S² a b)))
                                    j)

  h : (a b : S¹)
    → PathP (λ i → snd f (~ i) ≡ (sym (snd g) ∙ cong (fst g) (merid north)) i)
            ((sym (snd f) ∙∙ cong (fst f) (merid (S¹×S¹→S² a b) ∙ (λ i₂ → merid north (~ i₂))) ∙∙ snd f)
            ∙ (sym (snd g) ∙∙ cong (fst g) (merid (S¹×S¹→S² a b) ∙ (λ i₂ → merid north (~ i₂))) ∙∙ snd g))
            ((cong (fst (joinify f)) (push a b ∙ sym (push base b))
          ∙∙ snd f ∙ sym (snd g)
          ∙∙ cong (fst (joinify g)) (push base base ∙∙ sym (push a base) ∙∙ push a b)))
  h a b =
    ((λ i j → hcomp (λ k → λ {(i = i0) → (((λ j → snd f (~ j ∧ k)) ∙∙ cong (fst f) (merid (S¹×S¹→S² a b) ∙ (λ i₂ → merid north (~ i₂))) ∙∙ snd f)
                                         ∙ (sym (snd g) ∙∙ cong (fst g) (merid (S¹×S¹→S² a b) ∙ (λ i₂ → merid north (~ i₂))) ∙∙ λ j → snd g (j ∧ k))) j
                              ; (i = i1) → ((cong (fst f) (merid (S¹×S¹→S² a b)) ∙ sym (cong (fst f) (merid north)))
                                          ∙∙ snd f ∙ sym (snd g)
                                          ∙∙ cong (fst g) (merid (S¹×S¹→S² a b))) j
                              ; (j = i0) → snd f (~ i ∧ k)
                              ; (j = i1) → compPath-filler' (sym (snd g)) (cong (fst g) (merid north)) k i})
                     (pp a b i j))
    ▷ (λ i → (cong (fst f) (merid (S¹×S¹→S² a b)) ∙ sym (cong (fst f) (merid north)))
           ∙∙ snd f ∙ sym (snd g)
           ∙∙ cong (fst g) (merid (S¹×S¹→S² a b))))
    ▷ λ i →
      cong-∙ (fst (joinify f)) (push a b) (sym (push base b)) (~ i)
      ∙∙ snd f ∙ sym (snd g)
      ∙∙ l1 a b (~ i)

wedgeify : (f g : S₊∙ 3 →∙ S₊∙ 2) → S₊∙ 3 →∙ S₊∙ 2
fst (wedgeify f g) x = {! x!}
snd (wedgeify f g) = {!x!}

HopF' : (join S¹ S¹ , inl base) →∙ S₊∙ 2
fst HopF' = HopfM
snd HopF' = refl

HopF2' : (join S¹ S¹ , inl base) →∙ S₊∙ 2
fst HopF2' = fold⋁ ∘ ∨map
snd HopF2' = refl

homotHom : ∥ (join S¹ S¹ , inl base) →∙ (join S¹ S¹ , inl base) ∥₂ → ∥ (join S¹ S¹ , inl base) →∙ S₊∙ 2 ∥₂ 
homotHom = sMap λ f → HopfM ∘ fst f , cong HopfM (snd f)


-- wedge+ : ∣ HopF2 ∣₂ ≡ ·π' 2 ∣ HopF ∣₂ ∣ HopF ∣₂
-- wedge+ =
--   cong ∣_∣₂
--     ( {!id2!} ∙∙ cong deJoin ((id2 ∙ {!!}) ∙∙ cong (λ x → x +join x) (sym id1) ∙∙ sym (HopF +join≡ HopF)) ∙∙ dejoin-joinify (∙Π HopF HopF))


--   where
--   id1 : joinify HopF ≡ HopF'
--   id1 = ΣPathP (funExt (λ x → cong HopfM (S3→joinS¹S¹→S³ x)) , flipSquare (cong (cong HopfM) (rCancel (push base base))))

--   id2 : joinify HopF2 ≡ HopF2'
--   id2 = ΣPathP (funExt (λ x → cong (fold⋁ ∘ ∨map) (S3→joinS¹S¹→S³ x)) , flipSquare ((cong (cong (fold⋁ ∘ ∨map)) (rCancel (push base base)))))

--   main : (x : _) → fst HopF2' x ≡ fst (HopF' +join HopF') x
--   main (inl x) = σ (S₊∙ 1) x
--   main (inr x) = σ (S₊∙ 1) x
--   main (push a b i) = {!!}
--     where
--     s1 : cong (fst HopF2') (push a b) ≡ {!cong fold⋁ ?!}
--     s1 = cong-∙∙ fold⋁ (λ i → inr (σ (S₊∙ 1) b i)) (sym (push tt)) (λ i → inl (σ (S₊∙ 1) a i))
--        ∙∙ {!!}
--        ∙∙ {!!}

--     σ' : S¹ → typ (Ω (S₊∙ 2))
--     σ' base = refl
--     σ' (loop i) j = (sym (rCancel (merid base)) ∙∙ (cong (σ (S₊∙ 1)) loop) ∙∙ rCancel (merid base)) i j

--     σ'≡σ : (a : S¹) → σ (S₊∙ 1) a ≡ σ' a
--     σ'≡σ base = rCancel (merid base)
--     σ'≡σ (loop i) j k =
--       doubleCompPath-filler (sym (rCancel (merid base))) (cong (σ (S₊∙ 1)) loop) (rCancel (merid base)) j i k

--     σ'-sym : (a : S¹) → σ' (invLooper a) ≡ sym (σ' a)
--     σ'-sym base = refl
--     σ'-sym (loop i) j k = (sym≡cong-sym (λ i j → σ' (loop i) j)) j i k

--     σ-sym : (a : S¹) → σ (S₊∙ 1) (invLooper a) ≡ sym (σ (S₊∙ 1) a)
--     σ-sym a = σ'≡σ (invLooper a) ∙∙ σ'-sym a ∙∙ cong sym (sym (σ'≡σ a))

--     σ'-morph : (a : S¹) → σ' (a * a) ≡ σ' a ∙ σ' a
--     σ'-morph base = rUnit refl
--     σ'-morph (loop i) j = help3 i j
--       where
--       help : cong σ' (cong₂ _*_ loop loop) ≡ cong σ' loop ∙ cong σ' loop
--       help = cong (cong σ') (cong₂Funct _*_ loop loop)
--           ∙∙ cong (cong σ') (λ i → cong (λ x → rUnitS¹ x i) loop ∙ loop)
--           ∙∙ cong-∙ σ' loop loop

--       help2 : cong₂ _∙_ (cong σ' loop) (cong σ' loop)
--             ≡ cong (λ x → x ∙ refl) (cong σ' loop) ∙ cong (λ x → refl ∙ x) (cong σ' loop)
--       help2 = cong₂Funct _∙_ (cong σ' loop) (cong σ' loop)

--       help3 : Square (rUnit refl) (rUnit refl) (cong σ' (cong₂ _*_ loop loop)) (cong₂ _∙_ (cong σ' loop) (cong σ' loop))
--       help3 =
--         flipSquare (help
--           ◁ ((λ i → cong (λ x → rUnit x i) (cong σ' loop) ∙ cong (λ x → lUnit x i) (cong σ' loop))
--           ▷ sym help2))

--     σ-morph : (a : S¹) → σ (S₊∙ 1) (a * a) ≡ σ (S₊∙ 1) a ∙ σ (S₊∙ 1) a
--     σ-morph a = σ'≡σ (a * a) ∙∙ σ'-morph a ∙∙ cong (λ x → x ∙ x) (sym (σ'≡σ a))

--     σ'3 : (a : S¹) → σ' a ∙∙ σ' a ∙∙ σ' a ≡ σ' ((a * a) * a)
--     σ'3 base = sym (rUnit refl)
--     σ'3 (loop i) = {!!}
--       where
--       h : cong₂ (λ x y → x ∙∙ x ∙∙ y) (cong σ' loop) (cong σ' loop) ≡ {!!} -- cong (λ x → (x * x) * x) loop
--       h = cong₂Funct (λ x y → x ∙∙ x ∙∙ y) (cong σ' loop) (cong σ' loop)
--         ∙∙ {!cong (!} ∙∙ {!!}

--     σ'-comm : (a b : S¹) → σ' (a * b) ∙∙ (σ' (invLooper b) ∙ σ' (invLooper a)) ∙∙ σ' (a * b) ≡ σ' b ∙ σ' a
--     σ'-comm base b = {!!} -- sym (lUnit (σ' b)) ∙∙ refl ∙∙ rUnit (σ' b)
--     σ'-comm (loop i) b = {!!}

--     {-
--       (cong (fst f) (push a b ∙ sym (push base b))
--   ∙∙ snd f ∙ sym (snd g)
--   ∙∙ cong (fst g) (push base base ∙∙ sym (push a base) ∙∙ push a b)) i
--     -}

--     s3 : cong (fst (HopF' +join HopF')) (push a b)
--        ≡ (σ (S₊∙ 1) (a * b) ∙ sym (σ (S₊∙ 1) b))
--        ∙ (sym (σ (S₊∙ 1) a) ∙ σ (S₊∙ 1) (a * b))
--     s3 = (λ i → cong-∙ (fst HopF') (push a b) (sym (push base b)) i
--               ∙∙ rUnit refl (~ i)
--               ∙∙ cong-∙∙ (fst HopF') (push base base) (sym (push a base)) (push a b) i)
--       ∙∙ (λ i → (λ j → (σ (S₊∙ 1) (a * b) ∙ sym (σ (S₊∙ 1) b)) (~ i ∧ j))
--               ∙∙ ((λ j → (σ (S₊∙ 1) (a * b) ∙ sym (σ (S₊∙ 1) b)) (~ i ∨ j)))
--               ∙∙ (rCancel (merid base) i ∙∙ sym (σ (S₊∙ 1) (rUnitS¹ a i)) ∙∙ σ (S₊∙ 1) (a * b)))
--       ∙∙ refl


-- {- cong ∣_∣₂ (sym (dejoin-joinify {!!})
--                     ∙∙ {!!} -- cong deJoin
--                       ({!!}
--                        ∙ {!!}
--                       ∙∙ cong (λ x → x +join x) (sym id1)
--                       ∙∙ sym (HopF +join≡ HopF))
--                     ∙∙ dejoin-joinify (∙Π HopF HopF)) {- ((funExt (λ { north → refl
--                                      ; south → refl
--                                      ; (merid a i) j → help a j i})) -}
--                         --  , refl)) -}



-- --   where
-- --   maini : HopF2' ≡ (HopF' +join HopF')
-- --   maini = ΣPathP ((funExt (λ { (inl x) → refl
-- --                              ; (inr x) → refl
-- --                              ; (push a b i) j → h a b j i}))
-- --                 , refl)
-- --     where
-- --     rotLoop' : ∀ {ℓ} {A : Type ℓ} {x : A} (p : x ≡ x) → Square p p p p
-- --     rotLoop' p i j =
-- --       hcomp (λ k → λ { (i = i0) → p (j ∨ ~ k)
-- --                  ; (i = i1) → p (j ∧ k)
-- --                  ; (j = i0) → p (i ∨ ~ k)
-- --                  ; (j = i1) → p (i ∧ k)})
-- --               (p i0)

-- --     rotLoop'-filler2 : ∀ {ℓ} {A : Type ℓ} {x : A} (p : x ≡ x) → I → I → I → A
-- --     rotLoop'-filler2 p k i j =
-- --       hfill (λ k → λ { (i = i0) → {!!}
-- --                  ; (i = i1) → {!p k!}
-- --                  ; (j = i0) → p (i ∨ ~ k)
-- --                  ; (j = i1) → p (i ∧ k)})
-- --               (inS (p i0))
-- --               k

-- --     rotLoop'-filler : ∀ {ℓ} {A : Type ℓ} {x : A} (p : x ≡ x) → I → I → I → A
-- --     rotLoop'-filler p k i j =
-- --       hfill (λ k → λ { (i = i0) → p (j ∨ ~ k)
-- --                  ; (i = i1) → p (j ∧ k)
-- --                  ; (j = i0) → p (i ∨ ~ k)
-- --                  ; (j = i1) → p (i ∧ k)})
-- --               (inS (p i0))
-- --               k

-- --     S¹-ind : ∀ {ℓ} {A : S¹ → S¹ → Type ℓ} (f g : (a b : S¹) → A a b)
-- --           → (b : f base base ≡ g base base)
-- --           → (l : PathP (λ i → f (loop i) base ≡ g (loop i) base) b b)
-- --           → (r : PathP (λ i → f base (loop i) ≡ g base (loop i)) b b)
-- --           → (x y : S¹) → f x y ≡ g x y
-- --     S¹-ind f g b l r x y = {!!}
-- --     help : ∀ {ℓ} {A : Type ℓ} {x : A} (p : x ≡ x)
-- --          → refl ≡ p
-- --          → (q : p ≡ p)
-- --          → Σ[ b ∈ p ∙ p ≡ p ]
-- --              Σ[ l ∈ PathP (λ i → b i ≡ b i) (cong (p ∙_) q) q ]
-- --                Σ[ r ∈ PathP (λ i → b i ≡ b i) (cong (_∙ p) q) q ]
-- --                  (Cube (λ k j → l k j) (λ k j → l k j)
-- --                        (λ i j → q i ∙ q j) (λ i j → rotLoop' q i j)
-- --                        (λ k j → r j k) (λ k j → r j k))
-- --     help {x = x} p =
-- --       J (λ p _ → (q : p ≡ p)
-- --          → Σ[ b ∈ p ∙ p ≡ p ]
-- --              Σ[ l ∈ PathP (λ i → b i ≡ b i) (cong (p ∙_) q) q ]
-- --                Σ[ r ∈ PathP (λ i → b i ≡ b i) (cong (_∙ p) q) q ]
-- --                  (Cube (λ k j → l k j) (λ k j → l k j)
-- --                        (λ i j → q i ∙ q j) (λ i j → rotLoop' q i j)
-- --                        (λ k j → r j k) (λ k j → r j k)))
-- --           λ q → (sym (rUnit refl)) , ((λ i j → lUnit (q j) (~ i)) , (((λ i j → rUnit (q j) (~ i)))
-- --             , h q {!!}))
-- --       where
-- --       fill1 : (q : refl {x = x} ≡ refl) -- i j r
-- --         → Cube (λ j r s → q j s) (λ j r s → q j s)
-- --                 (λ i r → q i) (λ i r → q i)
-- --                 (rotLoop' q) (rotLoop' q)
-- --       fill1 = {!!}

-- --       h : (q : refl {x = x} ≡ refl) → (rotLoop' q ≡ flipSquare (rotLoop' q))
-- --         →  Cube (λ k j → lUnit (q j) (~ k)) (λ k j → lUnit (q j) (~ k))
-- --                 (λ i j → q i ∙ q j) (λ i j → rotLoop' q i j)
-- --                 (λ k j → rUnit (q k) (~ j)) (λ k j → rUnit (q k) (~ j))
-- --       h q fl i k j s =
-- --         hcomp (λ r → λ { (i = i0) → lUnit (q (j ∨ ~ r)) (~ k) s -- lUnit-filler (q j) r (~ k) s
-- --                         ; (i = i1) → lUnit (q (j ∧ r)) (~ k) s -- lUnit-filler (q j) r (~ k) s
-- --                         ; (j = i0) → {!rUnit (q (i ∨ ~ r)) (~ k) s!} -- rUnit (q i) (~ k ∧ r) s
-- --                         ; (j = i1) → {!!} -- rUnit (q i) (~ k ∧ r) s
-- --                         ; (k = i0) → {!!} -- compPath-filler (q i) (q j) r s
-- --                         ; (k = i1) → rotLoop'-filler q r i j s -- rotLoop' q i j s
-- --                         ; (s = i0) → {!!} -- x
-- --                         ; (s = i1) → {!!} }) -- q j (k ∨ r)})
-- --               (
-- --          hcomp (λ r → λ { (i = i0) → {!!}
-- --                         ; (i = i1) → {!!}
-- --                         ; (j = i0) → {!!}
-- --                         ; (j = i1) → {!!}
-- --                         ; (k = i0) → {!!}
-- --                         ; (k = i1) → {!lUnit (q (j ∨ ~ r)) (~ k) s -- rotLoop'-filler q r i0 j s!} -- rotLoop'-filler q r i j s -- rotLoop' q j i s -- rotLoop' q i j s
-- --                         ; (s = i0) → {!!}
-- --                         ; (s = i1) → {!!}}) -- q j k})
-- --               (hcomp (λ r → λ { (i = i0) → {!!} -- q (j ∨ ~ r) (k ∧ s)
-- --                         ; (i = i1) → {!!} -- q (j ∧ r) (k ∧ s)
-- --                         ; (j = i0) → {!q (~ r ∨ i) (~ k ∨ s)!}
-- --                         ; (j = i1) → {!!}
-- --                         ; (k = i0) → {!!}
-- --                         ; (k = i1) → {!!}
-- --                         ; (s = i0) → {!!}
-- --                         ; (s = i1) → {!!}})
-- --                      {!!}))
-- --       {-
-- -- lUnit-filler : {x y : A} (p : x ≡ y) → I → I → I → A
-- -- lUnit-filler {x = x} p j k i =
-- --   hfill (λ j → λ { (i = i0) → x
-- --                   ; (i = i1) → p (~ k ∨ j )
-- --                   ; (k = i0) → p i
-- --                -- ; (k = i1) → compPath-filler refl p j i
-- --                   }) (inS (p (~ k ∧ i ))) j

-- -- i = i0 ⊢ lUnit (q j) (~ k)
-- -- i = i1 ⊢ lUnit (q j) (~ k)
-- -- k = i0 ⊢ q i ∙ q j
-- -- k = i1 ⊢ rotLoop' q i j
-- -- j = i0 ⊢ rUnit (q i) (~ k)
-- -- j = i1 ⊢ rUnit (q i) (~ k)
-- -- -}
-- --       {-
-- --       hcomp (λ k → λ { (i = i0) → p (j ∨ ~ k)
-- --                  ; (i = i1) → p (j ∧ k)
-- --                  ; (j = i0) → p (i ∨ ~ k)
-- --                  ; (j = i1) → p (i ∧ k)})
-- --               (p i0)


-- --       i = i0 ⊢ lUnit (q j) (~ k)
-- -- i = i1 ⊢ lUnit (q j) (~ k)
-- -- j = i0 ⊢ rUnit (q i) (~ k)
-- -- j = i1 ⊢ rUnit (q i) (~ k)
-- -- k = i0 ⊢ q i ∙ q j
-- -- k = i1 ⊢ rotLoop' q i j
-- --       -}



-- --     rotLoop'-funct : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ} {x : A} (p : x ≡ x) (f : A → B)
-- --       → rotLoop' (cong f p) ≡ λ i j → f (rotLoop' p i j)
-- --     rotLoop'-funct p f k i j = {!!}

-- --     inst-help = help (σ (S₊∙ (suc zero)) base) (sym (rCancel (merid base))) (cong (σ (S₊∙ (suc zero))) loop)

-- --     E : typ ((Ω^ 2) (S₊∙ 2))
-- --     E i = (sym (rCancel (merid base)) ∙∙ (λ i → (merid (loop i) ∙ sym (merid base))) ∙∙ rCancel (merid base)) i

-- --     -- S¹ × S¹ → ΩS²

-- --     σ' : S¹ → typ (Ω (S₊∙ 2))
-- --     σ' base = refl
-- --     σ' (loop i) = E i

-- --     negi : {!S¹ → S¹!}
-- --     negi = {!!}

-- --     a+a : (a : S¹) → σ' (a * a) ≡ refl
-- --     a+a base = refl
-- --     a+a (loop i) j =
-- --       hcomp (λ r → λ {(i = i0) → σ' (loop (~ r))
-- --                      ; (i = i1) → σ' (loop (r ∨ j))
-- --                      ; (j = i0) → σ' (rotLoop'-filler loop r i i)
-- --                      ; (j = i1) → σ' (loop (~ r ∧ ~ i))})
-- --             {!i₁ = i0 ⊢ lCancel (E i) j
-- -- i₁ = i1 ⊢ lCancel (E i) j
-- -- i = i0 ⊢ lUnit (E i₁) (~ j)
-- -- i = i1 ⊢ lUnit (E i₁) (~ j)
-- -- j = i0 ⊢ sym (σ' (loop i)) ∙ σ' (loop i * loop i₁)
-- -- j = i1 ⊢ σ' (loop i₁)!}

-- --     lUnit' : ∀ {ℓ} {A : Type ℓ} {x y : A} → (p : x ≡ y) → p ≡ refl ∙ p
-- --     lUnit' = λ p → compPath-filler' refl p

-- --     ff : I → I → I → snd (S₊∙ 2) ≡ snd (S₊∙ 2)
-- --     ff r i j =
-- --       hfill (λ r → λ {(i = i0) → lUnit' (E (~ r)) (~ j) -- rUnit refl (~ r) j s -- compPath-filler' (E r) refl (~ j) s
-- --                      ; (i = i1) → rUnit (E (~ r)) (~ j) -- rUnit refl (~ r) j s -- compPath-filler' {!!} {!!} (~ j) s
-- --                      ; (j = i0) → E (~ i ∨ ~ r) ∙ E (i ∨ ~ r)
-- --                      ; (j = i1) → E (~ r)}) -- north
-- --              (inS (rUnit refl (~ j))) --  (compPath-filler' refl (~ j)))
-- --              r

-- --     σ'aa : (a b : S¹) → (σ' (invLooper b) ∙ σ' (b * a)) ≡ σ' a
-- --     σ'aa a base = sym (lUnit' _) -- sym (compPath-filler' refl _)
-- --     σ'aa base (loop i) j =
-- --       ff i1 i j
-- --     σ'aa (loop i) (loop j)  k s =
-- --       hcomp (λ r → λ {(i = i0) → PP r j k s -- ff r j k
-- --                      ; (i = i1) → PP r j k s -- ff r j k
-- --                      ; (j = i0) → lUnit' (σ' (loop i)) (r ∧ ~ k) s
-- --                      ; (j = i1) → lUnit' (σ' (loop i)) (r ∧ ~ k) s
-- --                      ; (k = i0) → compPath-filler' (σ' (loop (~ j))) (σ' (loop j * loop i)) r s -- 
-- --                      ; (k = i1) → E i s -- E i s
-- --                      ; (s = i0) → σ' (loop (~ j)) (~ r ∧ ~ k) -- E (~ j) (~ r ∧ ~ k) -- E (~ j) (~ r)
-- --                      ; (s = i1) → north})
-- --         (hcomp (λ r → λ {(i = i0) → {!!}
-- --                      ; (i = i1) → {!!}
-- --                      ; (j = i0) → {!!}
-- --                      ; (j = i1) → {!!}
-- --                      ; (k = i0) → {!!}
-- --                      ; (k = i1) → {!!}
-- --                      ; (s = i0) → {!!}
-- --                      ; (s = i1) → {!!}})
-- --                {!!})
-- --     {-
-- -- Goal: snd (S₊∙ 2) ≡ snd (S₊∙ 2)
-- -- ———— Boundary ——————————————————————————————————————————————
-- -- i = i0 ⊢ ff i1 j k
-- -- i = i1 ⊢ ff i1 j k
-- -- j = i0 ⊢ lUnit (E i) (~ k)
-- -- j = i1 ⊢ lUnit (E i) (~ k)
-- -- k = i0 ⊢ σ' (invLooper (loop j)) ∙ σ' (loop j * loop i)
-- -- k = i1 ⊢ E i-}
-- --       where -- j k s
-- --       PP3 : Cube (λ j s → north) (λ j s → north)
-- --                  (λ j₂ s₂ → E j₂ s₂) (λ j s → north)
-- --                  (λ j₂ k₂ → E (~ j₂) (~ k₂)) (λ j s → north)
-- --       PP3 j k s =
-- --         hcomp (λ r → λ {(j = i0) → E r (~ k)
-- --                        ; (j = i1) → E r (s ∧ ~ k) -- E (k ∨ r) (s)
-- --                        ; (k = i0) → E (j ∧ r) s
-- --                        ; (k = i1) → north
-- --                        ; (s = i0) → E (~ j ∧ r) (~ k)
-- --                        ; (s = i1) → E r (~ k)})
-- --                north

-- --       PP :
-- --         PathP (λ r → Cube (λ k s → lUnit' (σ' base) (r ∧ ~ k) s) (λ k s → lUnit' (σ' base) (r ∧ ~ k) s)
-- --                            (λ j s → compPath-filler' (σ' (loop (~ j))) (σ' (loop j)) r s)
-- --                            (λ j s → north)
-- --                            (λ j k → σ' (loop (~ j)) (~ r ∧ ~ k))
-- --                            λ j k → north)
-- --                  PP3
-- --               λ j k s → ff i1 j k s
-- --       PP =
-- --         {!i = i0 ⊢ ff i1 j k
-- -- i = i1 ⊢ ff i1 j k
-- -- j = i0 ⊢ lUnit (E i) (~ k)
-- -- j = i1 ⊢ lUnit (E i) (~ k)
-- -- k = i0 ⊢ σ' (invLooper (loop j)) ∙ σ' (loop j * loop i)
-- -- k = i1 ⊢ E i!}

-- --       help2 : (a : S¹) → PathP (λ i →  cong₂ _∙_ (cong σ' (sym loop)) (cong σ' (rotLoop a)) i ≡ σ' a)
-- --                    (sym (lUnit (σ' a))) (sym (lUnit (σ' a)))  -- (σ' a) 
-- --       help2 a = flipSquare (({!congFunct σ' (cong (_* a) loop)!}
-- --                          ∙ {!!})
-- --                          ◁ {!!})

-- --     bazonga : (a b : S¹) → (σ' a ∙∙ refl ∙∙ (σ' b))
-- --                     ≡ σ' (a * b)
-- --     bazonga base base = sym (rUnit refl)
-- --     bazonga base (loop i) = sym (lUnit (E i))
-- --     bazonga (loop i) base j k = {!doubleCompPath-filler (E i) refl refl (~ j)!}
-- --     bazonga (loop i) (loop i₁) = {!!}

-- --     σp : (a b : S¹) → (σ' a ∙ (σ' b))
-- --                     ≡ σ' (a * b)
-- --     σp base base = sym (rUnit refl) -- inst-help .fst
-- --     σp base (loop j) = sym (lUnit (E j)) -- inst-help .snd .fst j
-- --     σp (loop i) base =  (sym (rUnit (E i))) -- inst-help .snd .snd .fst i
-- --     σp (loop i) (loop j) k s =
-- --       hcomp (λ r → λ { (i = i0) → lUnit-filler (E j) r (~ k) s
-- --                         ; (i = i1) → lUnit-filler (E j) r (~ k) s
-- --                         ; (j = i0) → rUnit (E i) (~ k ∧ r) s
-- --                         ; (j = i1) → rUnit (E i) (~ k ∧ r) s
-- --                         ; (k = i0) → compPath-filler (E i) (E j) r s
-- --                         ; (k = i1) → σ' (loop i * loop j) s
-- --                         ; (s = i0) → north
-- --                         ; (s = i1) → E j (k ∨ r)})
-- --             (hcomp (λ r → λ { (i = i0) → σ' (loop j) (k ∧ (s ∨ ~ r)) -- σ' (loop j) (k ∧ (s ∨ ~ r)) -- σ' (loop j) ((k ∨ ~ r) ∧ s) -- σ' (loop j) (k ∧ s)
-- --                         ; (i = i1) → σ' (loop j) (k ∧ (s ∨ ~ r)) -- σ' (loop j) (s ∧ (k ∨ ~ r)) -- σ' (loop j) (k ∧ (s ∨ ~ r)) -- σ' (loop j) ((k ∨ ~ r) ∧ s) -- σ' (loop j) ((k) ∧ s)
-- --                         ; (j = i0) → {!σ' (loop i) s!} -- σ' (loop i) s -- σ' (loop i) (s ∧ r) -- σ' (loop i) s
-- --                         ; (j = i1) → {!!} -- σ' (loop i) s -- σ' (loop i) (s ∧ r)
-- --                         ; (k = i0) → {!!} -- σ' (loop i) s
-- --                         ; (k = i1) → {!!} -- σ' (loop i * loop j) (s ∨ ~ r) -- σ' (loop i * loop j) (s ∧ r) -- σ' (loop i * loop j) s -- σ' (loop i * loop j) s -- rotLoop' q i j s
-- --                         ; (s = i0) → σ' (loop j) (k ∧ ~ r) -- σ' base s -- σ' base s -- north
-- --                         ; (s = i1) → E j k}) --  σ' (loop j) k})
-- --                    {!σ' ? (k ∧ s)!})
-- --      where
-- --      ss : {!!}
-- --      ss = {!!}
-- --     {-
-- -- i = i0 ⊢ σp base (loop j) k s
-- -- i = i1 ⊢ σp base (loop j) k s
-- -- j = i0 ⊢ σp (loop i) base k s
-- -- j = i1 ⊢ σp (loop i) base k s
-- -- k = i0 ⊢ (σ' (loop i) ∙ σ' (loop j)) s
-- -- k = i1 ⊢ σ' (loop i * loop j) s
-- -- s = i0 ⊢ snd (S₊∙ 2)
-- -- s = i1 ⊢ snd (S₊∙ 2) -}


-- --     lem : (a b : S¹) → (σ (S₊∙ 1) (a * b) ∙ sym (σ (S₊∙ 1) b)) ∙ (sym (σ (S₊∙ 1) a ∙ σ (S₊∙ 1) (a * b)))
-- --                       ≡ {!!}
-- --     lem a b = {!i = i0 ⊢ inst-help .snd .fst j k
-- -- i = i1 ⊢ inst-help .snd .fst j k
-- -- j = i0 ⊢ inst-help .snd .snd .fst i k
-- -- j = i1 ⊢ inst-help .snd .snd .fst i k
-- -- k = i0 ⊢ σ (S₊∙ 1) (loop i) ∙ σ (S₊∙ 1) (loop j)
-- -- k = i1 ⊢ σ (S₊∙ 1)
-- --          (hcomp
-- --           (λ { k₁ (j = i0) → loop (i ∨ ~ k₁)
-- --              ; k₁ (j = i1) → loop (i ∧ k₁)
-- --              ; k₁ (i = i0) → loop (j ∨ ~ k₁)
-- --              ; k₁ (i = i1) → loop (j ∧ k₁)
-- --              })
-- --           base)!}

-- --     h : (a b : S¹) → cong (fst HopF2') (push a b)
-- --                    ≡ ((cong (fst HopF') (push a b ∙ sym (push base b))
-- --                    ∙∙ refl ∙ refl
-- --                    ∙∙ cong (fst HopF') (push base base ∙∙ sym (push a base) ∙∙ push a b)))
-- --     h a b = cong-∙∙ fold⋁ ((λ i → inr (σ (S₊∙ 1) b i))) (sym (push tt)) (λ i → inl (σ (S₊∙ 1) a i))
-- --           ∙ (λ _ → σ (S₊∙ 1) b ∙∙ refl ∙∙ σ (S₊∙ 1) a)
-- --           ∙ ({!!}
-- --           ∙∙ {!sym (σ (S₊∙ 1)  (a * base))!}
-- --           ∙∙ {!σ (S₊∙ 1) base!})
-- --           ∙ (λ i → (σ (S₊∙ 1) (a * b) ∙ sym (σ (S₊∙ 1) b))
-- --                  ∙∙ refl
-- --                  ∙∙ (rCancel (merid base) (~ i) ∙∙ sym (σ (S₊∙ 1)  (rUnitS¹ a (~ i))) ∙∙ σ (S₊∙ 1) (a * b)))
-- --           ∙ λ i → cong-∙ HopfM (push a b) (sym (push base b)) (~ i)
-- --                 ∙∙ rUnit refl i
-- --                 ∙∙ cong-∙∙ HopfM (push base base) (sym (push a base)) (push a b) (~ i)
  
-- --   id1 : joinify HopF ≡ HopF'
-- --   id1 = ΣPathP (funExt (λ x → cong HopfM (S3→joinS¹S¹→S³ x)) , flipSquare (cong (cong HopfM) (rCancel (push base base))))

-- --   id2 : joinify HopF2 ≡ HopF2'
-- --   id2 = ΣPathP (funExt (λ x → cong (fold⋁ ∘ ∨map) (S3→joinS¹S¹→S³ x)) , flipSquare ((cong (cong (fold⋁ ∘ ∨map)) (rCancel (push base base)))))

-- --   l : cong (λ x → HopfM (S3→joinS¹S¹ x)) (merid north) ≡ refl
-- --   l = rCancel (merid base)

-- --   main : {!rUnit!}
-- --   main = {!!}

-- --   help : (a : S₊ 2) → cong (fst HopF2) (merid a) ≡ cong (fst (∙Π HopF HopF)) (merid a)
-- --   help a = {!cong (λ x → fold⋁ (∨map (S3→joinS¹S¹ x))) (merid a)!}
-- --         ∙∙ {!!}
-- --         ∙∙ {!!}
-- --         ∙∙ cong (λ x → x ∙ x) (rUnit (cong (fst HopF) (merid a))
-- --                          ∙ cong (cong (fst HopF) (merid a) ∙_) (cong sym (sym l))
-- --                          ∙ sym (cong-∙ (fst HopF) (merid a) (sym (merid north))))
-- --         ∙∙ λ i → rUnit (cong (fst HopF) (merid a ∙ sym (merid (ptSn 2)))) i
-- --          ∙ rUnit (cong (fst HopF) (merid a ∙ sym (merid (ptSn 2)))) i
