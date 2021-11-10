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
open import Cubical.Functions.Morphism

open import Cubical.HITs.SetTruncation
  renaming (rec to sRec ; rec2 to sRec2
          ; elim to sElim ; elim2 to sElim2 ; elim3 to sElim3
          ; map to sMap)
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp renaming (toSusp to σ)
open import Cubical.HITs.S1

open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Bool

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
Ωⁿ⁺¹(Sⁿ →∙ A) ----------------> Ω (Sⁿ →∙ A) -----------> (Sⁿ⁺¹ →∙ A)
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
