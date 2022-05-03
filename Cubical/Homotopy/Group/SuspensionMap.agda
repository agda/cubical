{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Homotopy.Group.SuspensionMap where

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
open import Cubical.HITs.Susp renaming (toSusp to σ ; toSuspPointed to σ∙)
open import Cubical.HITs.S1

open import Cubical.Data.Bool hiding (_≟_)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order

open import Cubical.Algebra.Group
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid


open import Cubical.HITs.PropositionalTruncation
  renaming (rec to pRec ; rec2 to pRec2 ; elim to pElim)
open import Cubical.HITs.SetTruncation
  renaming (rec to sRec ; rec2 to sRec2 ; elim to sElim
          ; elim2 to sElim2 ; elim3 to sElim3 ; map to sMap)
open import Cubical.HITs.Truncation
  renaming (rec to trRec)

open Iso
open IsGroup
open IsSemigroup
open IsMonoid
open GroupStr

{-
This file concerns the suspension maps
suspMapΩ : πₙA → πₙ₊₁ΣA and
suspMap : π'ₙA → π'ₙ₊₁ΣA
For instance, we want to transport freudenthal
for suspMapΩ to suspMap by establishing a dependent
path between the two functions.

This gives, in particular, surjectivity of
πₙ₊₁(Sⁿ) → πₙ₊₂(Sⁿ⁺¹) for n ≥ 2.
-}

-- Definition of the suspension functions
suspMap : ∀ {ℓ} {A : Pointed ℓ}(n : ℕ)
        → S₊∙ (suc n) →∙ A
        → S₊∙ (suc (suc n)) →∙ Susp∙ (typ A)
fst (suspMap n f) north = north
fst (suspMap n f) south = north
fst (suspMap {A = A} n f) (merid a i) =
  (merid (fst f a) ∙ sym (merid (pt A))) i
snd (suspMap n f) = refl

suspMapΩ∙ : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
        → ((Ω^ n) A)
        →∙ ((Ω^ (suc n)) (Susp∙ (typ A)))
fst (suspMapΩ∙ {A = A} zero) a = merid a ∙ sym (merid (pt A))
snd (suspMapΩ∙ {A = A} zero) = rCancel (merid (pt A))
suspMapΩ∙ {A = A} (suc n) = Ω→ (suspMapΩ∙ {A = A} n)

suspMapΩ : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
         → typ ((Ω^ n) A) → typ ((Ω^ (suc n)) (Susp∙ (typ A)))
suspMapΩ {A = A} n = suspMapΩ∙ {A = A} n .fst


suspMapπ' : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ}
  → π' (suc n) A
  → π' (suc (suc n)) (Susp∙ (typ A))
suspMapπ' n = sMap (suspMap n)

suspMapπ : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
        → π n A → π (suc n) (Susp∙ (typ A))
suspMapπ n = sMap (suspMapΩ n)

{-          suspMapΩ
 Ωⁿ A  --------------------> Ω¹⁺ⁿ (Susp A)
 |                           |
 | =                         | ≃ flipΩ
 |          Ωⁿ→ σ           v
Ωⁿ A -------------------> Ωⁿ (Ω (Susp A))
 |                           |
 |                           |
 | ≃ Ω→SphereMap            | ≃ Ω→SphereMap
 |                           |
 v           post∘∙ . σ      v
 (Sⁿ →∙ A) -------------- > (Sⁿ →∙ Ω (Susp A))
 |                           |
 | =                         | ≃ botᵣ
 |                           |
 v            suspMap        v
 (Sⁿ →∙ A) -------------- > (Sⁿ⁺¹→∙ Susp A)
 -}

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

----- Top square filler -----
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

----- Middle square filler -----
module _ {ℓ ℓ'} (A : Pointed ℓ) (B : Pointed ℓ')
  (homogB : isHomogeneous B) (f : A →∙ B)  where
  nat = isNaturalΩSphereMap A B homogB f
  mutual
    isNatural-Ω→SphereMap : ∀ n p → f ∘∙ Ω→SphereMap n p
                                   ≡ Ω→SphereMap n (Ω^→ n f .fst p)
    isNatural-Ω→SphereMap 0 p =
      →∙Homogeneous≡ homogB (funExt λ {true → f .snd; false → refl})
    isNatural-Ω→SphereMap (n@(suc n')) p =
      cong (f ∘∙_) (Ω→SphereMap-split n' p)
      ∙ nat n' (Ω→SphereMapSplit₁ n' p)
      ∙ cong (ΩSphereMap n') inner
      ∙ sym (Ω→SphereMap-split n' (Ω^→ n f .fst p))
      where
      inner : Ω→ (post∘∙ (S₊∙ n') f) .fst (Ω→ (Ω→SphereMap∙ n') .fst p)
            ≡ Ω→ (Ω→SphereMap∙ n') .fst (Ω^→ (suc n') f .fst p)
      inner =
        sym (Ω→∘ (post∘∙ (S₊∙ n') f) (Ω→SphereMap∙ n') p)
        ∙ cong (λ g∙ → Ω→ g∙ .fst p) (isNatural-Ω→SphereMap∙ n')
        ∙ Ω→∘ (Ω→SphereMap∙ n') (Ω^→ n' f) p

    isNatural-Ω→SphereMap∙ : ∀ n
      → post∘∙ (S₊∙ n) f ∘∙ (Ω→SphereMap∙ n)
      ≡ (Ω→SphereMap∙ n {A = B} ∘∙ Ω^→ n f)
    isNatural-Ω→SphereMap∙ n =
      →∙Homogeneous≡ (isHomogeneous→∙ homogB)
        (funExt (isNatural-Ω→SphereMap n))

mid□ : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
         → (p : typ ((Ω^ (suc n)) A))
        → fst (post∘∙ (S₊∙ (suc n)) (σ∙ A)) (Ω→SphereMap (suc n) p)
        ≡ Ω→SphereMap (suc n) (fst (Ω^→ (suc n) (σ∙ A)) p)
mid□ {A = A} n p =
  funExt⁻
    (cong fst
      (isNatural-Ω→SphereMap∙
        A (Ω (Susp∙ (typ A)))
        (isHomogeneousPath _ _)
        (σ∙ A) (suc n))) p

----- Bottom square filler -----
bot□ : ∀ {ℓ} {A : Pointed ℓ}  (n : ℕ) (f : (S₊∙ (suc n) →∙ A))
      → suspMap n f
       ≡ botᵣ {A = A} (suc n) (post∘∙ (S₊∙ (suc n)) (σ∙ A) .fst f)
bot□ {A = A} n f =
  ΣPathP ((funExt (λ { north → refl
                     ; south → refl
                     ; (merid a i) → refl}))
         , refl)

-- We prove that botᵣ is an equivalence
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

-- Right hand composite iso
IsoΩSphereMapᵣ : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
  → Iso (typ ((Ω^ (suc n)) (Susp∙ (typ A)))) ((S₊∙ (suc n) →∙ Susp∙ (typ A)))
IsoΩSphereMapᵣ {A = A} n =
  compIso (flipΩIso n)
    (compIso (IsoΩSphereMap n) (botᵣIso {A = A} n))

-- The dependent path between the two suspension functions
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
            (cong (Ω→SphereMap (suc n) {A = Ω (Susp∙ (typ A)) })
                  ((sym (funExt⁻ (cong fst (top□ {A = A} n))
                     (invEq (Ω→SphereMap (suc n)
                           , isEquiv-Ω→SphereMap (suc n)) p))))
           ∙ (sym (mid□ n (invEq (Ω→SphereMap (suc n)
                                , isEquiv-Ω→SphereMap (suc n)) p))
             ∙ cong (σ∙ (fst A , snd A) ∘∙_)
                    (secEq (Ω→SphereMap (suc n)
                          , isEquiv-Ω→SphereMap (suc n)) p)))
    ∙∙ sym (bot□ n p)))

-- Connectedness of suspFunΩ (Freudenthal)
suspMapΩ-connected : ∀ {ℓ} (n : HLevel) (m : ℕ) {A : Pointed ℓ}
     (connA : isConnected (suc (suc n)) (typ A))
  → isConnectedFun ((suc n + suc n) ∸ m) (suspMapΩ {A = A} m)
suspMapΩ-connected n zero {A = A} connA = isConnectedσ n connA
suspMapΩ-connected n (suc m) {A = A} connA with ((n + suc n) ≟ m)
... | (lt p) = subst (λ x → isConnectedFun x (suspMapΩ {A = A} (suc m)))
                     (sym (n∸m≡0 _ m p))
                     λ b → tt* , (λ {tt* → refl})
... | (eq q) = subst (λ x → isConnectedFun x (suspMapΩ {A = A} (suc m)))
                     (sym (n∸n≡0 m) ∙ cong (_∸ m) (sym q))
                     λ b → tt* , (λ {tt* → refl})
... | (gt p) = isConnectedCong' (n + suc n ∸ m) (suspMapΩ {A = A} m)
    (subst (λ x → isConnectedFun x (suspMapΩ {A = A} m))
           (sym (suc∸-fst (n + suc n) m p))
           (suspMapΩ-connected n m connA))
    (snd (suspMapΩ∙ m))

-- We prove that the right iso is structure preserving
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

hom-botᵣ : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
  → (f g : S₊∙ (suc n) →∙ Ω (Susp∙ (typ A)))
  → botᵣ {A = A} (suc n) (∙Π f g)
  ≡ ∙Π (botᵣ {A = A} (suc n) f) (botᵣ {A = A} (suc n) g)
hom-botᵣ {A = A} n f g =
  morphLemmas.isMorphInv ∙Π ∙Π (botᵣ⁻ {A = A} (suc n))
    (hom-botᵣ⁻' {A = A} n)
    (botᵣ {A = A} (suc n))
    (leftInv (botᵣIso {A = A} (suc n)))
    (rightInv (botᵣIso {A = A} (suc n)))
    f g

isHom-IsoΩSphereMapᵣ : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
                    (p q : typ ((Ω^ (2 + n)) (Susp∙ (typ A))))
                 → Iso.fun (IsoΩSphereMapᵣ (suc n)) (p ∙ q)
                  ≡ ∙Π (Iso.fun (IsoΩSphereMapᵣ (suc n)) p)
                       (Iso.fun (IsoΩSphereMapᵣ (suc n)) q)
isHom-IsoΩSphereMapᵣ {A = A} n p q =
     cong (botᵣ {A = A} (suc n))
       (cong (Ω→SphereMap (suc n) {A = Ω (Susp∙ (typ A))})
         (flipΩIsopres· n p q)
     ∙ isHom-Ω→SphereMap n (fun (flipΩIso (suc n)) p)
                    (fun (flipΩIso (suc n)) q))
     ∙ hom-botᵣ n _ _

suspMapΩ→hom : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) (p q : typ ((Ω^ (suc n)) A))
  → suspMapΩ (suc n) (p ∙ q)
   ≡ suspMapΩ (suc n) p ∙ suspMapΩ (suc n) q
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
  transportLem : ∀ {ℓ} {A B : Type ℓ}
                   (_+A_ : A → A → A) (_+B_ : B → B → B)
                 → (e : Iso A B)
                 → ((x y : A) → fun e (x +A y) ≡ fun e x +B fun e y)
                 → PathP (λ i → isoToPath e i → isoToPath e i → isoToPath e i)
                         _+A_ _+B_
  transportLem _+A_ _+B_ e hom =
    toPathP (funExt (λ p → funExt λ q →
         (λ i → transportRefl
                  (fun e (inv e (transportRefl p i)
                       +A inv e (transportRefl q i))) i)
      ∙∙ hom (inv e p) (inv e q)
      ∙∙ cong₂ _+B_ (rightInv e p) (rightInv e q)))

  pₗ : ∀ {ℓ} (A : Pointed ℓ) (n : ℕ)
    → typ (Ω ((Ω^ n) A)) ≡ (S₊∙ (suc n) →∙ A)
  pₗ A n = isoToPath (IsoΩSphereMap {A = A} (suc n))

  pᵣ : ∀ {ℓ} (A : Pointed ℓ) (n : ℕ)
    → typ ((Ω^ (2 + n)) (Susp∙ (typ A)))
     ≡ (S₊∙ (suc (suc n)) →∙ Susp∙ (typ A))
  pᵣ A n = isoToPath (IsoΩSphereMapᵣ {A = A} (suc n))

∙Π→∙ : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
     → PathP (λ i → pₗ A n i → pₗ A n i → pₗ A n i) _∙_ ∙Π
∙Π→∙ {A = A} n =
  transportLem _∙_ ∙Π (IsoΩSphereMap {A = A} (suc n)) (isHom-Ω→SphereMap n)

∙Π→∙ᵣ : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
     → PathP (λ i → pᵣ A n i → pᵣ A n i → pᵣ A n i) _∙_ ∙Π
∙Π→∙ᵣ {A = A} n =
  transportLem _∙_ ∙Π (IsoΩSphereMapᵣ {A = A} (suc n)) (isHom-IsoΩSphereMapᵣ n)

isHom-suspMap : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) (f g : S₊∙ (suc n) →∙ A)
           → suspMap n (∙Π f g)
           ≡ ∙Π (suspMap n f) (suspMap n g)
isHom-suspMap {A = A} n =
   transport (λ i → (f g : isoToPath (IsoΩSphereMap {A = A} (suc n)) i)
                 → Ωσ→suspMap n i (∙Π→∙ n i f g)
                 ≡ ∙Π→∙ᵣ n i (Ωσ→suspMap n i f) (Ωσ→suspMap n i g))
             (suspMapΩ→hom n)

suspMapπHom : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
            → GroupHom (πGr n A) (πGr (suc n) (Susp∙ (typ A)))
fst (suspMapπHom {A = A} n) = suspMapπ (suc n)
snd (suspMapπHom {A = A} n) =
  makeIsGroupHom
    (sElim2 (λ _ _ → isSetPathImplicit)
      λ p q → cong ∣_∣₂ (suspMapΩ→hom n p q))

suspMapπ'Hom : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
  → GroupHom (π'Gr n A) (π'Gr (suc n) (Susp∙ (typ A)))
fst (suspMapπ'Hom {A = A} n) = suspMapπ' n
snd (suspMapπ'Hom {A = A} n) =
  makeIsGroupHom (sElim2 (λ _ _ → isSetPathImplicit)
    λ f g → cong ∣_∣₂ (isHom-suspMap n f g))

πGr≅π'Grᵣ : ∀ {ℓ} (n : ℕ) (A : Pointed ℓ)
          → GroupIso (πGr (suc n) (Susp∙ (typ A)))
                      (π'Gr (suc n) (Susp∙ (typ A)))
fst (πGr≅π'Grᵣ n A) = setTruncIso (IsoΩSphereMapᵣ (suc n))
snd (πGr≅π'Grᵣ n A) =
  makeIsGroupHom (sElim2 (λ _ _ → isSetPathImplicit)
    λ f g → cong ∣_∣₂ (isHom-IsoΩSphereMapᵣ n f g))

private
  isConnectedPres : ∀ {ℓ} {A : Pointed ℓ} (con n : ℕ)
                  → isConnectedFun con (suspMapΩ∙ {A = A} (suc n) .fst)
                  → isConnectedFun con (suspMap {A = A} n)
  isConnectedPres {A = A} con n hyp =
    transport (λ i → isConnectedFun con (Ωσ→suspMap {A = A} n i)) hyp

isConnectedSuspMap : (n m : ℕ)
  → isConnectedFun ((m + suc m) ∸ n) (suspMap {A = S₊∙ (suc m)} n)
isConnectedSuspMap n m =
  isConnectedPres _ _ (suspMapΩ-connected m (suc n) (sphereConnected (suc m)))

isSurjectiveSuspMap : (n : ℕ)
  → isSurjective (suspMapπ'Hom {A = S₊∙ (2 + n)} (2 + n))
isSurjectiveSuspMap n =
  sElim (λ _ → isProp→isSet squash)
    λ f →
      trRec
        ((subst (λ x → isOfHLevel x (isInIm (suspMapπ'Hom (2 + n)) ∣ f ∣₂))
                      (sym (snd (lem n n)))
                      (isProp→isOfHLevelSuc {A = isInIm (suspMapπ'Hom (2 + n)) ∣ f ∣₂}
                      (fst (lem n n)) squash)))
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
