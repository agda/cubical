{-# OPTIONS --lossy-unification #-}
{-
This file contains:
1. An iso πₙ'(Sⁿ) ≅ ℤ, where πₙ'(Sⁿ) = ∥ Sⁿ →∙ Sⁿ ∥₀
2. A proof that idfun∙ : Sⁿ →∙ Sⁿ is the generator of πₙ'(Sⁿ)
3. An explicit construction of iso Hⁿ(Sⁿ,ℤ) ≅ πₙ'(Sⁿ)
4. Description of multiplication on πₙ'(Sⁿ) (function composition)
-}
module Cubical.Homotopy.Group.PinSn where

open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Group.SuspensionMap
open import Cubical.Homotopy.Connected

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.S1 renaming (_·_ to _*_)
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp

open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Int renaming (_+_ to _+ℤ_)

open import Cubical.ZCohomology.Properties

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Instances.Int
open import Cubical.Algebra.Group.ZAction
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Groups.Sn

open Iso

-- The goal is to prove that πₙSⁿ ≅ ℤ. This is of course trivial, given
-- that ΩⁿK(ℤ,n) ≅ ℤ is already proved. However, we would like to do
-- this for πₙSⁿ defined via (Sⁿ →∙ Sⁿ) and prove that the generator
-- of this group is idfun∙ : Sⁿ → Sⁿ.

private
  suspMapS^ : (n : ℕ) → (S₊∙ (suc n) →∙ S₊∙ (suc n))
                        → S₊∙ (2 + n) →∙ S₊∙ (2 + n)
  suspMapS^ n = suspMap {A = S₊∙ (suc n)} n

is2ConnectedSuspMap : (n : ℕ) → isConnectedFun 2 (suspMapS^ (suc n))
is2ConnectedSuspMap n =
  isConnectedFunSubtr 2 n _
    (subst (λ x → isConnectedFun x (suspMapS^ (suc n)))
                   (subtrLem n (suc (suc n)) ∙ +-comm 2 n)
      (isConnectedSuspMap (suc n) (suc n)))
  where
  subtrLem : (n m : ℕ) → (n + m ∸ n) ≡ m
  subtrLem zero m = refl
  subtrLem (suc n) m = subtrLem n m

-- From the connectedness of the suspension map,
--  we get an iso πₙSⁿ ≅ πₙ₊₁(Sⁿ⁺¹) for n ≥ 2.
SphereSuspIso : (n : ℕ)
  → Iso (π' (2 + n) (S₊∙ (2 + n))) (π' (3 + n) (S₊∙ (3 + n)))
SphereSuspIso n =
  compIso setTruncTrunc2Iso
   (compIso
     (connectedTruncIso 2
       (suspMap {A = S₊∙ (suc (suc n))} (suc n)) (is2ConnectedSuspMap n))
     (invIso (setTruncTrunc2Iso)))

SphereSuspGrIso : (n : ℕ)
  → GroupIso (π'Gr (suc n) (S₊∙ (2 + n))) (π'Gr (2 + n) (S₊∙ (3 + n)))
fst (SphereSuspGrIso n) = SphereSuspIso n
snd (SphereSuspGrIso n) =
  makeIsGroupHom (ST.elim2 (λ _ _ → isSetPathImplicit)
    λ f g → IsGroupHom.pres· (suspMapπ'Hom (suc n) .snd) ∣ f ∣₂ ∣ g ∣₂)

private
  stLoop₁ : π 2 (S₊∙ 2)
  stLoop₁ = ∣ sym (rCancel (merid base))
          ∙∙ (λ i → merid (loop i) ∙ sym (merid base))
          ∙∙ rCancel (merid base) ∣₂

  stLoop₁flip : π 2 (S₊∙ 2)
  stLoop₁flip = ST.map flipSquare stLoop₁

flipSquareIso : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
  → GroupIso (πGr (suc n) A) (πGr (suc n) A)
fun (fst (flipSquareIso n)) = ST.map flipSquare
inv (fst (flipSquareIso n)) = ST.map flipSquare
rightInv (fst (flipSquareIso n)) =
  ST.elim (λ _ → isSetPathImplicit) λ _ → refl
leftInv (fst (flipSquareIso n)) =
  ST.elim (λ _ → isSetPathImplicit) λ _ → refl
snd (flipSquareIso n) =
  makeIsGroupHom
    (ST.elim2 (λ _ _ → isSetPathImplicit)
      λ f g → cong ∣_∣₂
        ((sym (sym≡flipSquare (f ∙ g))
      ∙∙ symDistr f g
      ∙∙ cong₂ _∙_ (sym≡flipSquare g) (sym≡flipSquare f)
       ∙ EH n (flipSquare g) (flipSquare f))))

-- We now want to prove π₁S¹≅π₂S². This will be done by passing through
-- The loop space defintion of the groups
π'₂S²≅π₂S² : GroupIso (π'Gr 1 (S₊∙ 2)) (πGr 1 (S₊∙ 2))
π'₂S²≅π₂S² = π'Gr≅πGr 1 (S₊∙ 2)

{- We now define the iso π₂S² ≅ π₁S¹ -}
π₂S²≅π₁S¹ : GroupIso (πGr 1 (S₊∙ 2)) (πGr 0 (S₊∙ 1))
fst π₂S²≅π₁S¹ =
  compIso setTruncTrunc2Iso
   (compIso
    (compIso (invIso (PathIdTruncIso 2))
     (compIso (congIso (invIso (PathIdTruncIso 3)))
      (compIso
        (congIso (invIso (Iso-Kn-ΩKn+1 1)))
        (PathIdTruncIso 2))))
    (invIso setTruncTrunc2Iso))
snd π₂S²≅π₁S¹ =
  makeIsGroupHom
    (ST.elim2 (λ _ _ → isSetPathImplicit)
      λ f g →
        cong (inv setTruncTrunc2Iso)
          (cong (fun (PathIdTruncIso 2))
            (cong (cong (ΩKn+1→Kn 1))
              (cong (cong (inv (PathIdTruncIso 3)))
                (cong (inv (PathIdTruncIso 2))
                  (refl {x = ∣ f ∙ g ∣})
               ∙ cong-∙ ∣_∣ₕ f g)
             ∙ cong-∙ (inv (PathIdTruncIso 3)) (cong ∣_∣ₕ f) (cong ∣_∣ₕ g))
           ∙ cong-∙ (ΩKn+1→Kn 1)
              (cong (inv (PathIdTruncIso 3)) (cong ∣_∣ₕ f))
              (cong (inv (PathIdTruncIso 3)) (cong ∣_∣ₕ g)))
         ∙ PathIdTruncIsoFunct 1
            (cong (ΩKn+1→Kn 1) (λ i → inv (PathIdTruncIso 3) ∣ f i ∣ₕ))
            (cong (ΩKn+1→Kn 1) (λ i → inv (PathIdTruncIso 3) ∣ g i ∣ₕ)))
         ∙ setTruncTrunc2IsoFunct
            ((fun (PathIdTruncIso 2))
             (cong (ΩKn+1→Kn 1) (λ i → inv (PathIdTruncIso 3) ∣ f i ∣ₕ)))
            ((fun (PathIdTruncIso 2))
             (cong (ΩKn+1→Kn 1) (λ i → inv (PathIdTruncIso 3) ∣ g i ∣ₕ))))
  where
  setTruncTrunc2IsoFunct : ∀ {ℓ} {A : Type ℓ} {x : A}
    (p q : hLevelTrunc 2 (x ≡ x))
    → inv setTruncTrunc2Iso
         (TR.map2 _∙_ p q)
       ≡ ·π 0 (inv setTruncTrunc2Iso p) (inv setTruncTrunc2Iso q)
  setTruncTrunc2IsoFunct =
    TR.elim2 (λ  _ _ → isSetPathImplicit) λ _ _ → refl

π₂'S²≅π₁'S¹ : GroupIso (π'Gr 1 (S₊∙ 2)) (π'Gr 0 (S₊∙ 1))
π₂'S²≅π₁'S¹ =
  compGroupIso (π'Gr≅πGr 1 (S₊∙ 2))
    (compGroupIso (flipSquareIso 0)
      (compGroupIso π₂S²≅π₁S¹
        (invGroupIso (π'Gr≅πGr 0 (S₊∙ 1)))))

-- We get our iso
πₙ'Sⁿ≅ℤ : (n : ℕ) → GroupIso (π'Gr n (S₊∙ (suc n))) ℤGroup
πₙ'Sⁿ≅ℤ zero =
  compGroupIso (π'Gr≅πGr zero (S₊∙ 1))
    ((compIso (setTruncIdempotentIso (isGroupoidS¹ _ _)) ΩS¹Isoℤ)
      , makeIsGroupHom (ST.elim2 (λ _ _ → isProp→isSet (isSetℤ _ _))
           winding-hom))
πₙ'Sⁿ≅ℤ (suc zero) = compGroupIso π₂'S²≅π₁'S¹ (πₙ'Sⁿ≅ℤ zero)
πₙ'Sⁿ≅ℤ (suc (suc n)) =
  compGroupIso (invGroupIso (SphereSuspGrIso n)) (πₙ'Sⁿ≅ℤ (suc n))

-- Same thing for the loop space definition
πₙSⁿ≅ℤ : (n : ℕ) → GroupIso (πGr n (S₊∙ (suc n))) ℤGroup
πₙSⁿ≅ℤ n =
  compGroupIso (invGroupIso (π'Gr≅πGr n (S₊∙ (suc n)))) (πₙ'Sⁿ≅ℤ n)

-- The goal now is to show that πₙ'Sⁿ≅ℤ takes idfun∙ : Sⁿ → Sⁿ to 1.
-- For this, we need a bunch of identities:
private
  Isoπ₁S¹ℤ = (compIso (setTruncIdempotentIso (isGroupoidS¹ _ _)) ΩS¹Isoℤ)

  π'₂S²≅π₂S²⁻-stLoop' : inv (fst (π'₂S²≅π₂S²)) stLoop₁flip ≡ ∣ idfun∙ _ ∣₂
  π'₂S²≅π₂S²⁻-stLoop' =
    cong ∣_∣₂ (ΣPathP ((funExt
      (λ { north → refl
         ; south → merid base
         ; (merid base i) j →
           hcomp (λ k
             → λ {(i = i0) → north
                 ; (i = i1) → merid base (j ∧ k)
                 ; (j = i0) → rUnit (λ _ → north) k i
                 ; (j = i1) → merid base (i ∧ k)})
                 north
         ; (merid (loop k) i) j
                  → hcomp (λ r
                    → λ {(i = i0) → north
                        ; (i = i1) → merid base (j ∧ r)
                        ; (j = i0) →
                          rUnit (funExt⁻ (cong fst (cong (Ω→SphereMap 1)
                              (flipSquare (sym (rCancel (merid base))
                            ∙∙ (λ i₁ → merid (loop i₁)
                             ∙ sym (merid base))
                            ∙∙ rCancel (merid base))))) (loop k)) r i
                        ; (j = i1) → lem₂ r i k})
                 (((sym (rCancel (merid base)) ∙∙
                    (λ i₁ → merid (loop i₁) ∙ sym (merid base)) ∙∙
                    rCancel (merid base))) k i)})) , refl))
    where
    genBot+side : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y)
                → Cube {A = A} (λ j r → x) (λ j r → p (~ j ∨ r))
                                (λ i r → p i) (λ i r → p (i ∧ r))
                                (λ i j → p (i ∧ ~ j)) (λ i j → p i)
                 × Cube {A = A} (λ j r → p (~ j ∨ r)) (λ j r → p (r ∧ j))
                                (λ k r → p (~ k)) (λ k r → p r)
                                (λ k j → p (~ k ∧ ~ j)) λ k j → p (j ∨ ~ k)
    genBot+side {A = A} {x = x} =
      J (λ y p → Cube {A = A} (λ j r → x) (λ j r → p (~ j ∨ r))
                                (λ i r → p i) (λ i r → p (i ∧ r))
                                (λ i j → p (i ∧ ~ j)) (λ i j → p i)
                 × Cube {A = A} (λ j r → p (~ j ∨ r)) (λ j r → p (r ∧ j))
                                (λ k r → p (~ k)) (λ k r → p r)
                                (λ k j → p (~ k ∧ ~ j)) λ k j → p (j ∨ ~ k))
         (refl , refl)

    lem₁ : I → I → I → S₊ 2
    lem₁ j i r =
      hcomp (λ k → λ {(i = i0) → north
                     ; (i = i1) → genBot+side (merid base) .snd k j r
                     ; (j = i0) → compPath-filler
                                    (merid base) (sym (merid base)) k i
                     ; (j = i1) → merid base (i ∧ r)
                     ; (r = i0) → rCancel-filler (merid base) k j i
                     ; (r = i1) → compPath-filler
                                   (merid base) (sym (merid base)) (~ j ∧ k) i})
            (genBot+side (merid base) .fst i j r)

    lem₂ : I → I → I → S₊ 2
    lem₂ r i k =
      hcomp (λ j → λ {(i = i0) → north
                     ; (i = i1) → merid base (r ∧ j)
                     ; (r = i0) → doubleCompPath-filler
                                    (sym (rCancel (merid base)))
                                    (λ i₁ → merid (loop i₁) ∙ sym (merid base))
                                    (rCancel (merid base)) j k i
                     ; (r = i1) → compPath-filler
                                   (merid (loop k)) (sym (merid base)) (~ j) i
                     ; (k = i0) → lem₁ j i r
                     ; (k = i1) → lem₁ j i r})
            ((merid (loop k) ∙ sym (merid base)) i)

  π₂S²≅π₁S¹-stLoop : fun (fst π₂S²≅π₁S¹) stLoop₁ ≡ ∣ loop ∣₂
  π₂S²≅π₁S¹-stLoop =
      sym (leftInv Isoπ₁S¹ℤ
          (fun (fst π₂S²≅π₁S¹) stLoop₁))
   ∙∙ cong (inv Isoπ₁S¹ℤ) compute
   ∙∙ leftInv (compIso (setTruncIdempotentIso (isGroupoidS¹ _ _)) ΩS¹Isoℤ)
              ∣ loop ∣₂
    where
    compute : fun Isoπ₁S¹ℤ (fun (fst π₂S²≅π₁S¹) stLoop₁)
            ≡ fun Isoπ₁S¹ℤ ∣ loop ∣₂
    compute = refl

  π₂'S²≅π₁'S¹≡ : fun (fst π₂'S²≅π₁'S¹) ∣ idfun∙ _ ∣₂ ≡ ∣ idfun∙ _ ∣₂
  π₂'S²≅π₁'S¹≡ =
    lem₁ ∣ idfun∙ _ ∣₂ stLoop₁
      (sym π'₂S²≅π₂S²⁻-stLoop')
      (cong (inv (fst (π'Gr≅πGr zero (S₊∙ 1)))) π₂S²≅π₁S¹-stLoop
     ∙ lem₂)
    where
    lem₁ : (x : _) (y : π 2 (S₊∙ 2))
       → (x ≡ inv (fst π'₂S²≅π₂S²) (fun (fst (flipSquareIso 0)) y))
       → inv (fst (π'Gr≅πGr zero (S₊∙ 1))) (fun (fst π₂S²≅π₁S¹) y)
          ≡ ∣ idfun∙ _ ∣₂
       → fun (fst π₂'S²≅π₁'S¹) x ≡ ∣ idfun∙ _ ∣₂
    lem₁ x y p q =
         cong (fun (fst π₂'S²≅π₁'S¹)) p
      ∙∙ (λ i → inv (fst (π'Gr≅πGr zero (S₊∙ (suc zero)))) (fun (fst π₂S²≅π₁S¹)
          (fun (fst (flipSquareIso zero))
            (rightInv
              (fst (π'Gr≅πGr (suc zero) (S₊∙ (suc (suc zero)))))
              (inv (fst (flipSquareIso zero)) y) i)
          )))
      ∙∙ cong (inv (fst (π'Gr≅πGr zero (S₊∙ (suc zero)))))
              (cong (fun (fst π₂S²≅π₁S¹))
                (rightInv (fst (flipSquareIso zero)) y))
       ∙ q

    lem₂ : inv (fst (π'Gr≅πGr zero (S₊∙ 1))) ∣ loop ∣₂ ≡ ∣ idfun∙ _ ∣₂
    lem₂ =
      cong ∣_∣₂ (ΣPathP (funExt (λ { base → refl ; (loop i) → refl}) , refl))

  suspPresIdfun : (n : ℕ) → suspMap n (idfun∙ (S₊∙ (suc n))) ≡ idfun∙ _
  suspPresIdfun n =
    ΣPathP ((funExt
      (λ { north → refl
         ; south → merid (ptSn (suc n))
         ; (merid a i) j
           → compPath-filler (merid a) (sym (merid (ptSn (suc n)))) (~ j) i}))
        , refl)

  suspPresIdfun2 : (n : ℕ)
    → fun (fst (invGroupIso (SphereSuspGrIso n)))
        ∣ idfun∙ (S₊∙ (suc (suc (suc n)))) ∣₂
    ≡ ∣ idfun∙ _ ∣₂
  suspPresIdfun2 n =
      sym (cong (fun (fst (invGroupIso (SphereSuspGrIso n))))
          (cong ∣_∣₂ (suspPresIdfun (suc n))))
    ∙ leftInv (SphereSuspIso n) ∣ idfun∙ _ ∣₂

-- We finally have our results
πₙ'Sⁿ≅ℤ-idfun∙ : (n : ℕ)
  → fun (fst (πₙ'Sⁿ≅ℤ n)) ∣ idfun∙ _ ∣₂ ≡ (pos (suc zero))
πₙ'Sⁿ≅ℤ-idfun∙ zero = refl
πₙ'Sⁿ≅ℤ-idfun∙ (suc zero) = speedUp ∣ idfun∙ _ ∣₂ π₂'S²≅π₁'S¹≡
  where
  speedUp : (x : _) -- stated like this for faster type checking
     → fun (fst π₂'S²≅π₁'S¹) x ≡ ∣ idfun∙ _ ∣₂
     → fun (fst (πₙ'Sⁿ≅ℤ (suc zero))) x ≡ pos (suc zero)
  speedUp x p = cong (fun (fst (πₙ'Sⁿ≅ℤ zero))) p
πₙ'Sⁿ≅ℤ-idfun∙ (suc (suc n)) =
  cong (fun (fst (πₙ'Sⁿ≅ℤ (suc n)))) (suspPresIdfun2 n)
  ∙ πₙ'Sⁿ≅ℤ-idfun∙ (suc n)

πₙ'Sⁿ-gen-by-idfun : (n : ℕ) → gen₁-by (π'Gr n (S₊∙ (suc n))) ∣ idfun∙ _ ∣₂
πₙ'Sⁿ-gen-by-idfun n =
  subst (gen₁-by (π'Gr n (S₊∙ (suc n))))
        (sym (cong (inv (fst (πₙ'Sⁿ≅ℤ n))) (πₙ'Sⁿ≅ℤ-idfun∙ n))
        ∙ leftInv (fst (πₙ'Sⁿ≅ℤ n)) ∣ idfun∙ _ ∣₂)
        (Iso-pres-gen₁ ℤGroup (π'Gr n (S₊∙ (suc n)))
          (pos (suc zero))
          (λ h → h , (sym (·Comm h (pos 1)) ∙ ℤ·≡· h (pos 1)))
          (invGroupIso (πₙ'Sⁿ≅ℤ n)))

-- Isomorphism πₙ(Sⁿ) ≅ Hⁿ(Sⁿ,ℤ)
private
  makePted : (n : ℕ) (fn : S₊ (2 + n)) → ∥ fn ≡ north ∥₂
  makePted n fn =
    TR.rec (isOfHLevelPlus' 2 squash₂) ∣_∣₂
        (isConnectedPathSⁿ (suc n) fn north .fst)
  makePted-eq : (n : ℕ) (fn : S₊ (2 + n)) (p : fn ≡ north) → makePted n fn ≡ ∣ p ∣₂
  makePted-eq n fn p j =
    TR.rec (isOfHLevelPlus' 2 squash₂) ∣_∣₂ (isConnectedPathSⁿ (suc n) fn north .snd ∣ p ∣ j)

-- Forgetting pointedness gives iso
πₙSⁿ-unpoint : (n : ℕ) → (π'Gr n (S₊∙ (suc n)) .fst) → ∥ (S₊ (suc n) → S₊ (suc n)) ∥₂
πₙSⁿ-unpoint n = ST.map fst

isIso-πₙSⁿ-unpointIso : (n : ℕ) → isIso (πₙSⁿ-unpoint n)
fst (isIso-πₙSⁿ-unpointIso zero) =
  ST.map λ f → (λ x → f x * (invLooper (f base)))
                , sym (rCancelS¹ (f base))
fst (snd (isIso-πₙSⁿ-unpointIso zero)) =
  ST.elim (λ _ → isSetPathImplicit)
      λ f → PT.rec (squash₂ _ _)
      (λ q → cong ∣_∣₂ (funExt λ x → cong (f x *_)
        (cong invLooper (sym q)) ∙ rUnitS¹ (f x)))
      (isConnectedS¹ (f base))
snd (snd (isIso-πₙSⁿ-unpointIso zero)) =
  ST.elim (λ _ → isSetPathImplicit)
    λ f → cong ∣_∣₂
      (ΣPathP ((funExt
        (λ r → cong (fst f r *_) (cong invLooper (snd f))
                                ∙ rUnitS¹ (fst f r)))
    , help _ (sym (snd f))))
  where
  help : (x : _) (p : base ≡ x)
    → PathP (λ i → ((λ j → x * invLooper (p (~ j))) ∙ rUnitS¹ x) i ≡ base)
             (sym (rCancelS¹ x)) (sym p)
  help = J> λ i j → rCancel (λ _ → base) j i
fst (isIso-πₙSⁿ-unpointIso (suc n)) =
  ST.rec squash₂ λ f → ST.map (λ p → f , p) (makePted n (f north))
fst (snd (isIso-πₙSⁿ-unpointIso (suc n))) =
  ST.elim (λ _ → isSetPathImplicit)
    λ f → ST.rec isSetPathImplicit
      (λ p j → πₙSⁿ-unpoint (suc n)
        (ST.map (λ p₁ → f , p₁) (makePted-eq n (f north) p j)))
           (makePted n (f north))
snd (snd (isIso-πₙSⁿ-unpointIso (suc n))) =
  ST.elim (λ _ → isSetPathImplicit)
      λ f i → ST.map (λ p → fst f , p) (makePted-eq n _ (snd f) i)

πₙSⁿ-unpointIso : (n : ℕ) → Iso ∥ (S₊∙ (suc n) →∙ S₊∙ (suc n)) ∥₂ ∥ (S₊ (suc n) → S₊ (suc n)) ∥₂
Iso.fun (πₙSⁿ-unpointIso n) = πₙSⁿ-unpoint n
Iso.inv (πₙSⁿ-unpointIso n) = isIso-πₙSⁿ-unpointIso n .fst
Iso.rightInv (πₙSⁿ-unpointIso n) = isIso-πₙSⁿ-unpointIso n .snd .fst
Iso.leftInv (πₙSⁿ-unpointIso n) = isIso-πₙSⁿ-unpointIso n .snd .snd



-- πₙ(Sⁿ) → Hⁿ(Sⁿ,ℤ)
πₙSⁿ→HⁿSⁿ-fun : (n : ℕ) → π'Gr n (S₊∙ (suc n)) .fst → coHom (suc n) (S₊ (suc n))
πₙSⁿ→HⁿSⁿ-fun n = ST.map λ f x → ∣ fst f x ∣

-- to prove it's a homomorphism, we need the following
module suspensionLemmas (n : ℕ) where
  Susp⊣Ω-Sn← : ((f : S₊ (suc n) → Ω (S₊∙ (suc (suc n))) .fst)
              → S₊ (suc (suc n)) → S₊ (suc (suc n)))
  Susp⊣Ω-Sn← f north = north
  Susp⊣Ω-Sn← f south = north
  Susp⊣Ω-Sn← f (merid a i) = f a i

  Susp⊣Ω-Sn←-σ : (f : S₊∙ (suc n) →∙ Ω (S₊∙ (suc (suc n))))
    → (x : _)
    → cong (Susp⊣Ω-Sn← (fst f)) (σSn (suc n) x) ≡ fst f x
  Susp⊣Ω-Sn←-σ f x =
      cong-∙ (Susp⊣Ω-Sn← (fst f)) (merid x) (sym (merid _))
    ∙ cong (λ z → fst f x ∙ sym z) (snd f)
    ∙ sym (rUnit _)

  Susp⊣Ω-Sn←≡ : (f : _) → ∥ Σ[ g ∈ (S₊∙ (suc n) →∙ Ω (S₊∙ (suc (suc n)))) ] f
                            ≡ Susp⊣Ω-Sn← (fst g) ∥₂
  Susp⊣Ω-Sn←≡ f =
    ST.map
      (λ p → ((λ x → (sym p ∙ cong f (merid x)
                    ∙ (cong f (sym (merid (ptSn _))) ∙ p)))
              , (cong (sym p ∙_)
                  (assoc _ _ _ ∙ cong (_∙ p) (rCancel (cong f (merid (ptSn _))))
                               ∙ sym (lUnit p))
               ∙ lCancel p))
            , funExt (
            λ { north → p
              ; south → cong f (sym (merid (ptSn _))) ∙ p
              ; (merid a i) j → compPath-filler' (sym p)
                                 (compPath-filler (cong f (merid a))
                                   (cong f (sym (merid (ptSn _))) ∙ p) j) j i}))
      (makePted n (f north))

  Susp⊣Ω-Sn←≡∙ : (f : (S₊∙ (2 + n)) →∙ S₊∙ (2 + n))
    → ∃[ g ∈ _ ] f ≡ (Susp⊣Ω-Sn← (fst g) , refl)
  Susp⊣Ω-Sn←≡∙ f =
    ST.rec (isProp→isSet squash₁)
      (uncurry (λ g q → TR.rec (isProp→isOfHLevelSuc n squash₁)
        (λ r → ∣ g , ΣPathP (q , (sym r ◁ (λ i j → q (i ∨ j) north))) ∣₁)
        (isConnectedPath _
          (isConnectedPathSⁿ (suc n) (fst f north) north)
          (funExt⁻ q north) (snd f) .fst )))
      (Susp⊣Ω-Sn←≡ (fst f))

-- homomorphism πₙ(Sⁿ) → Hⁿ(Sⁿ,ℤ)
πₙSⁿ→HⁿSⁿ : (n : ℕ)
  → GroupHom (π'Gr n (S₊∙ (suc n))) (coHomGr (suc n) (S₊ (suc n)))
fst (πₙSⁿ→HⁿSⁿ n) = πₙSⁿ→HⁿSⁿ-fun n
snd (πₙSⁿ→HⁿSⁿ zero) =
  makeIsGroupHom
    (ST.elim2 (λ _ _ → isSetPathImplicit)
      λ f g → subst2 P (sym (S¹-fun-charac f .snd)) (sym (S¹-fun-charac g .snd))
                (main (S¹-fun-charac f .fst) (S¹-fun-charac g .fst)))
    where
    mkfun : fst (Ω (S₊∙ 1)) → S¹ → S¹
    mkfun p base = base
    mkfun p (loop i) = p i

    main : (a b : Ω (S₊∙ 1) .fst)
      → πₙSⁿ→HⁿSⁿ-fun zero (·π' zero ∣ mkfun a , refl ∣₂ ∣ mkfun b , refl ∣₂)
       ≡ πₙSⁿ→HⁿSⁿ-fun zero ∣ mkfun a , refl ∣₂
       +ₕ πₙSⁿ→HⁿSⁿ-fun zero ∣ mkfun b , refl ∣₂
    main a b = cong ∣_∣₂ (funExt
      λ { base → refl
       ; (loop i) j → ((λ i j → ∣ (rUnit a (~ i) ∙ rUnit b (~ i)) j ∣ₕ)
                    ∙∙ cong-∙ ∣_∣ₕ a b
                    ∙∙ ∙≡+₁ (cong ∣_∣ₕ a) (cong ∣_∣ₕ b)) j i})

    S¹-fun-charac : (f : S₊∙ 1 →∙ S₊∙ 1)
      → Σ[ g ∈ Ω (S₊∙ 1) .fst ] f ≡ (mkfun g , refl)
    S¹-fun-charac (f , p) = (sym p ∙∙ cong f loop ∙∙ p)
      , ΣPathP ((funExt (
      λ { base → p
       ; (loop i) j → doubleCompPath-filler (sym p) (cong f loop) p j i}))
      , λ i j → p (i ∨ j))

    P : (f g : _) → Type
    P f g = πₙSⁿ→HⁿSⁿ-fun zero (·π' zero ∣ f ∣₂ ∣ g ∣₂)
          ≡ (πₙSⁿ→HⁿSⁿ-fun zero ∣ f ∣₂) +ₕ (πₙSⁿ→HⁿSⁿ-fun zero ∣ g ∣₂)

snd (πₙSⁿ→HⁿSⁿ (suc n)) = makeIsGroupHom isGrHom
  where
  open suspensionLemmas n
  isGrHom : (f g : _)
    → πₙSⁿ→HⁿSⁿ-fun (suc n) (·π' _ f g)
     ≡ πₙSⁿ→HⁿSⁿ-fun (suc n) f +ₕ πₙSⁿ→HⁿSⁿ-fun (suc n) g
  isGrHom =
    ST.elim2 (λ _ _ → isSetPathImplicit)
     λ f g → PT.rec2 (squash₂ _ _)
      (uncurry (λ g' gp → uncurry λ h hp
        → (λ i → πₙSⁿ→HⁿSⁿ-fun (suc n) (·π' (suc n) ∣ gp i ∣₂ ∣ hp i ∣₂) )
        ∙∙ cong ∣_∣₂ (funExt
          (λ { north → refl
             ; south → refl
             ; (merid a i) j
             → hcomp (λ k →
             λ {(i = i0) → 0ₖ (2 + n)
              ; (i = i1) → 0ₖ (2 + n)
              ; (j = i0) → ∣ (rUnit (Susp⊣Ω-Sn←-σ g' a (~ k)) k
                            ∙ rUnit (Susp⊣Ω-Sn←-σ h a (~ k)) k) i ∣ₕ
              ; (j = i1) → ∙≡+₂ _ (cong ∣_∣ₕ (g' .fst a)) (cong ∣_∣ₕ (h .fst a)) k i})
           (cong-∙ ∣_∣ₕ (g' .fst a) (h .fst a) j i)}))
        ∙∙ λ i → πₙSⁿ→HⁿSⁿ-fun (suc n) ∣ gp (~ i) ∣₂
               +ₕ πₙSⁿ→HⁿSⁿ-fun (suc n) ∣ hp (~ i) ∣₂))
       (Susp⊣Ω-Sn←≡∙ f) (Susp⊣Ω-Sn←≡∙ g)

-- isomorphism πₙ(Sⁿ) ≅ Hⁿ(Sⁿ,ℤ)
πₙSⁿ≅HⁿSⁿ : (n : ℕ)
  → GroupEquiv (π'Gr n (S₊∙ (suc n))) (coHomGr (suc n) (S₊ (suc n)))
fst (fst (πₙSⁿ≅HⁿSⁿ n)) = fst (πₙSⁿ→HⁿSⁿ n)
snd (fst (πₙSⁿ≅HⁿSⁿ zero)) =
  subst isEquiv (sym funid) (isoToIsEquiv (compIso is1 is2))
  where
  is1 : Iso (π' 1 (S₊∙ 1)) ∥ (S¹ → S¹) ∥₂
  is1 = πₙSⁿ-unpointIso 0

  is2 : Iso ∥ (S¹ → S¹) ∥₂ (coHom 1 S¹)
  is2 = setTruncIso (codomainIso (invIso (truncIdempotentIso 3 isGroupoidS¹)))

  funid : πₙSⁿ→HⁿSⁿ-fun zero ≡ Iso.fun is2 ∘ Iso.fun is1
  funid = funExt (ST.elim (λ _ → isSetPathImplicit) λ _ → refl)
snd (fst (πₙSⁿ≅HⁿSⁿ (suc n))) =
  gen∈Im→isEquiv _
    (GroupIso→GroupEquiv (invGroupIso (πₙ'Sⁿ≅ℤ (suc n)))) _
     (GroupIso→GroupEquiv (invGroupIso (Hⁿ-Sⁿ≅ℤ (suc n))))
     ∣ ∣_∣ₕ ∣₂
     (sym (HⁿSⁿ-gen (suc n)))
     (πₙSⁿ→HⁿSⁿ (suc n))
     ∣ ∣ idfun∙ _ ∣₂ , refl ∣₁
snd (πₙSⁿ≅HⁿSⁿ n) = snd (πₙSⁿ→HⁿSⁿ n)

-- the multiplications
module _ (n : ℕ) where
  multSⁿ↬ : (f g : ∥ (S₊ (suc n) → S₊ (suc n)) ∥₂)
   → ∥ (S₊ (suc n) → S₊ (suc n)) ∥₂
  multSⁿ↬ = ST.rec2 squash₂ λ f g → ∣ f ∘ g ∣₂

  multπₙ : (f g : π'Gr n (S₊∙ (suc n)) .fst) → π'Gr n (S₊∙ (suc n)) .fst
  multπₙ = ST.rec2 squash₂ λ f g → ∣ f ∘∙ g ∣₂

-- preservation of multiplication under relevant isos
multπₙ-pres : (n : ℕ) (f g : π'Gr n (S₊∙ (suc n)) .fst)
  → Iso.fun (πₙSⁿ-unpointIso n) (multπₙ n f g)
   ≡ multSⁿ↬ n (Iso.fun (πₙSⁿ-unpointIso n) f) (Iso.fun (πₙSⁿ-unpointIso n) g)
multπₙ-pres n = ST.elim2 (λ _ _ → isSetPathImplicit) λ f g → refl

multπₙ-pres' : (n : ℕ) (f g : ∥ (S₊ (suc n) → S₊ (suc n)) ∥₂)
  → Iso.inv (πₙSⁿ-unpointIso n) (multSⁿ↬ n f g)
   ≡ multπₙ n (Iso.inv (πₙSⁿ-unpointIso n) f) (Iso.inv (πₙSⁿ-unpointIso n) g)
multπₙ-pres' n f g =
    (λ i → isIso-πₙSⁿ-unpointIso n .fst
             (multSⁿ↬ n (Iso.rightInv (πₙSⁿ-unpointIso n) f (~ i))
                         (Iso.rightInv (πₙSⁿ-unpointIso n) g (~ i))))
  ∙∙ sym (cong (Iso.inv (πₙSⁿ-unpointIso n))
       (multπₙ-pres n (Iso.inv (πₙSⁿ-unpointIso n) f) (Iso.inv (πₙSⁿ-unpointIso n) g)))
  ∙∙ Iso.leftInv (πₙSⁿ-unpointIso n) _

multHⁿSⁿ-pres : (n : ℕ) (f g : π'Gr n (S₊∙ (suc n)) .fst)
  → πₙSⁿ→HⁿSⁿ-fun n (multπₙ n f g)
   ≡ multHⁿSⁿ n (πₙSⁿ→HⁿSⁿ-fun n f) (πₙSⁿ→HⁿSⁿ-fun n g)
multHⁿSⁿ-pres n = ST.elim2 (λ _ _ → isSetPathImplicit) λ f g → refl
